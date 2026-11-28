import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36314.Model
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


end PEqualNP.Outside.L_meta_36314.Model

namespace PEqualNP.Outside.L_meta_36314
open PEqualNP.Outside.L_meta_36314.Model
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

def SBf (j : Nat) : Nat := [7, 7, 7, 5, 7, 7].getD j 0

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

end PEqualNP.Outside.L_meta_36314

namespace PEqualNP.Outside.L_meta_36314
open PEqualNP.Outside.L_meta_36314.Model
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
end PEqualNP.Outside.L_meta_36314
namespace PEqualNP.Outside.L_meta_36314
open PEqualNP.Outside.L_meta_36314.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x30007802400000460098034000000000a801418000004112436980003c084000001580009c0010011080325c0001c0148350000000001280382c60500a800700000003e58e800000000004400d0050020000000012000000000002000608002000c103ff43fe43de43fd43dd43fc43ff42fe42fd42fc42ff32fe32de32fd32fc32dc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x885e626a2a78123cb20e7c366c1aa608665aa276005c9a9414a096aa6064004280320026388e3ea448409c04ae300c1e345224981c000000000000004eb000000000029000005046867e180000564c00749e542e684472a858167a0682106e2c843a8c0a7020288a22ac4a92001460107000408d5a00100140468200142071c5c10d22689801606baa921d794a43b7a92876c5250f3ea8a1f3d4943ae29287cc5250e98a4a1d794c43af29e855d53d0b3a87a15d94742baa8e855f5350ab8a6a16750d42af298855d5310abea9195755232af294653e540ca7aa81957d5032cf2a0655d540cb3aa8194755032af29065ce520cb9e84197310832af29e835d53d073a87a0db94b41b6a96839d43506bca620d754c41b7a92636c524c67ca818cf550319f2a4433d54886bca710d754e21e6194435f53486b8a690f30c821af29e815d53d033a87205794c40aea98819d43102dca4205b54840bb2888175511027ca9984f55330b7294616d528c39865905794e20aea9c413f5448278a89057d4d20ae29a41cc32482eea2905d145209faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x14000028730782a8089a0004063085a612c2a0600000b923a40081400030810e8c6250f42c550d51d0a1d6595032c3189540cb0d54d0832b1987420ca4d6510832a318943d070d4354b41a3189435064c6254c41a3590328870e540ca2187590534868d640c8219318953d028c6250e40a3189431030d4354840c550d511028d640cb2087592538828d640c920c315032483443214520
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x62480a0428239286a8e858155261d083281aed2a06510d047250d5110206bb0a819241415d03214520
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
  | 4 => packedAt s1K4 (2640+((h/30+packedAt s1K4 (2430+(h % 30)*7) 7) % 109)*8) 8
  | 3 => packedAt s1K3 (998+((h/8+packedAt s1K3 (950+(h % 8)*6) 6) % 34)*6) 6
  | 2 => packedAt s1K2 (300+((h/2+packedAt s1K2 (294+(h % 2)*3) 3) % 8)*4) 4
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x1fffffe07fffff03ffff07ffff07fffcf1f1ff
  | 2 => 0xe07f07ff83fffffc1e0ff8781ff87fff4e4e3f
  | 3 => 0xff8007fffc0fc3ffe00fff801fff87038f8fcc
  | 4 => 0x7fffff003fffff000001ffff803f00ff0
  | 5 => 0xfffff800000003ffffffffffe0000003fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x420a00230020800062110088c50089281090d5
  | 2 => 0x89144a441945212c0c8648510a4852d146462a
  | 3 => 0x4526948928ea0655a10b95025395041a8b8b4c
  | 4 => 0x9658e7125283ab9ad7a0c4449ce66063f00db0
  | 5 => 0x1860c61c630c33e319cce66700c44083ed6000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaafaaafaa0a0a0faaafaaafaa0a0a0faaafaaafaa0a0a0faaafaaafaa0a0a0faaafaaafaa0a0a0faaafaaafaa0a0a0faaafaaafaa0a0a0faaafaaafaa0a0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36314
namespace PEqualNP.Outside.L_meta_36314
open PEqualNP.Outside.L_meta_36314.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x90c00b800000296188c00f0040e803c00c00340101100002241a38a014c492a726090a2066ca993e2ce000e2050600e58000818419b000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x38440002b00681183ebd1b0320000d00cc03a3c384014a293aa0aec3202c4d6b236400044cd403c0685cb60ea00247aa4a1c7c758ae223059258240000055fb42e01b8f02080008300501000e3c08106142808408322b7a92876c5250eeea2a1dd14543bda8287785050edca421db54843bda8285785050abca6215754c42bba8a6574514ca7ca8194f55032af29e835d53d06dca5a0db54b41b7294836d52906f4a120de54241b7a92636c524c67ca818cf55031b7290636d520c6f4a018de54031afa9a435c53486f4a010de54021b7a92816c52502bca6205754c40b7290816d52102eca2205d544409f2a6613d54cc2dca5985b54b30b7294616d528c2eca3185d546309faa2413c54482eca2105d544209faa2213c54442bea6885714d10b7a92216c52442dca4085b54810
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 40
  | 4 => 64
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (i*5) 5
  | 5 => packedAt s2K5 (i*16) 16
  | 4 => packedAt s2K4 (i*27) 27
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (6+((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s2K5 (718+((h/13+packedAt s2K5 (640+(h % 13)*6) 6) % 53)*7) 7
  | 4 => packedAt s2K4 (1875+((h/21+packedAt s2K4 (1728+(h % 21)*7) 7) % 77)*7) 7
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffffe03ff8307fc3fe0fffff83fe0138fe7c
  | 1 => 0xf01f83ffc1ffff83fc3ff0780ffc1ffecf338f
  | 3 => 0xffe003fffe003ffc003fff800fffe0030fc3f0
  | 4 => 0x3ffffffffffffc000000ffffffff003ff
  | 5 => 0xfffffc0000003ffffffffffff0000003fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x614510238411500cc04642a8e590aa2818563c
  | 1 => 0x24c214448ca11281441a523122948c984b3285
  | 3 => 0xc28b5a891875b5b4222d6b224b5ac8530dc3d0
  | 4 => 0x8b1463122144295aaa8108048c631163b0016a
  | 5 => 0xc18421c31862e6333318c4700420183e6a800
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaaeecc0000eeeeeeaaeecc0000eeeeeeaaeecc0000eeeeeeaaeecc0000eeeeeeaaeecc0000eeeeeeaaeecc0000eeeeeeaaeecc0000eeeeeeaaeecc0000, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36314
namespace PEqualNP.Outside.L_meta_36314
open PEqualNP.Outside.L_meta_36314.Model
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
  | 0 => 0x1ffffc0ff0f87c3fc3f87fff87f0383e99f793
  | 1 => 0xe0787ff0ffff87c3fc3f8703f87fffc166c9fc
  | 2 => 0xff807fff00fffffc003ff803ff803fff870e1f
  | 4 => 0x7fffff0007ffffc00003ffffc001f80fe0
  | 5 => 0xffff8000000007fffffffffc00000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x4310046201108004c04809198091888c085391
  | 1 => 0x490088a240400881441882288824928422c0b4
  | 2 => 0x842551042aa445582225504255022531850c0a
  | 4 => 0x96566248a835566eaa844093664b0119d80f40
  | 5 => 0x1864438cccc667b3333664e0440c0621f7a000
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeaecece0e0eeeeeaeaecece0e0eeeeeaeaecece0e0eeeeeaeaecece0e0eeeeeaeaecece0e0eeeeeaeaecece0e0eeeeeaeaecece0e0eeeeeaeaecece0e0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36314
namespace PEqualNP.Outside.L_meta_36314
open PEqualNP.Outside.L_meta_36314.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x70050015804a005002a14c00200001200004003a110230c0ccad383462c3624ba1007879a52500074e08000447cb0b544c08048453001000000523800403ca3c0ff43df43fe43fd43fc43dc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30df30fe30fd30dd30fc30ff20fe20fd20fc20ff10f710fe10fd10f510fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x1257c680028e864014c000000f18000195d09184400ac0000b4d81499449530ec5c900054b0c8f84030107c2000000000dd580000000034013514d560800000a4013c000085508d1c00fd68bd0c0000014000506000a00000000000000048e4000c00240000000038000000d070000000000000012d04cd280170002c000000011148006c01380000004c0000009c000058001d640988c08974b96d852078a9007579543c000000f4c404e006120400280c0202000400060c0000001002000400060a060202000000200402135d50d0ebca721d795043cf2a0875d5010f3887a15794e42aea9c855f5350ab8a6a16710d42bba8a85745150af6a0a15e141429f2a4653d548caeea2995d14532af29c835d53906f4a120de54241afa9a835c53506f4a018de54031afa9a435c534867ca810cf55021af298435d53086f4a010de54021af29c815d539033887205d94640baa8c815f53502b8a6a05794c40aea98819c43102dca4205b54840bb288817551102bca9985715330aea9c6176518c2eaa3184fd51309e2a2619f544c2bca8985715130ce2a2611c544c3b6a0985794c30bb2886175510c2bca7105754e20bb28c4175518827ca8104f55020af298415d53082eca2105d54420eba1e21d443c43ae6188754c310af29c215d53842eaa308764c210ec98221d743443a886887cd4110f9a0221f040443ae60887c8c110ea98221f130443a260887c88110f8902215e53042baa6085d94410
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x40140003d30464090112803071480922ce00034300c0002811b1843141429c580514cb0c435484087992544c21c6454e20a519130c4298644c210a619130442d16010d10b458c40443904310110b858840442d1638c110a519130442b0644c110e4d9130442d2644c110b41913044390644c110a419130442d16388110
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x4002006804358840442493a4c898221241d16388110
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 99
  | 3 => 21
  | 2 => 3
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
  | 4 => packedAt s4K4 (2937+((h/33+packedAt s4K4 (2673+(h % 33)*8) 8) % 172)*8) 8
  | 3 => packedAt s4K3 (833+((h/7+packedAt s4K3 (798+(h % 7)*5) 5) % 28)*6) 6
  | 2 => packedAt s4K2 (150+((h/1+packedAt s4K2 (147+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xf83ffff81ffc3e0f1f0fe3fffe1fe07c467e73
  | 1 => 0xffc0f87fe0ffc3f01ff0fc781fe1ff8079b39c
  | 2 => 0xffff007fffffffffe000ff801fffffff81c3ff
  | 3 => 0x7fff0003ffffff00001ffe0003fe03e0
  | 5 => 0xffffff80000003ffffffffffe0000003fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x48861408c2095201034520a8c7132118421631
  | 1 => 0x51922491465116500d5464314b314b0858b294
  | 2 => 0x2208412208a000a6200089021044946181414a
  | 3 => 0x472cb64494399b3b566600249d990632ee03e0
  | 5 => 0x8430c00718c221cc9888d2470000184335e800
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xfeeafeeae0e0e0e0feeafeeae0e0e0e0feeafeeae0e0e0e0feeafeeae0e0e0e0feeafeeae0e0e0e0feeafeeae0e0e0e0feeafeeae0e0e0e0feeafeeae0e0e0e0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36314
namespace PEqualNP.Outside.L_meta_36314
open PEqualNP.Outside.L_meta_36314.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x13000002c12a43165600ca7081401848350032a21107008d4002050f253a701011ca8012343002d3e4400a003cda62e845820490c80202001c52411c5ff43df43fe43fd43fc43dc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31df31fe31fd31dd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fa10fd10f910fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x4a60c0462212c2904e6c6ea856b8b40074009a7834c44c1e7e5a80a064a4bc000096662c10929e4252067c3068388c0000a6943c5e9c2e00aabab270880086b6500c580082000000b08e0a000498001cae5c3e1a627a00162428008440021400268a720e00a200084418362a3276200054beac003a486a0a00187021402c0608b0a88740010034481022c000001c0000625588015d51d0ebca721d795043cf2a0875d5110f3887a15794e42aea9c855f5350ab8a6a16710d42bba8a85745150af6a0a15e141429f2a4653d548caf6a0995e14132af29c835d53907388720de94241bca84835f53506b8a6a0d794c41aea98839c43106dca420db54841bd280837950106bca998d715331aea9c637a508c6f2a118cfd51319e2a2639f544c6bca898d715131ce2a2631c544c7aea298d794c31bd2806379500c6bca710d754e21bd2844379508867ca810cf55021af298435d53086f4a010de54021af29c815d53902eca3205d54640afa9a815c53502eca2185d54430afa9a415c534827ca8104f55020af298415d53082eca2105d54420af29e215d53c43aa638876d0e10ec21c217951843b66308764c610ea98a21db43443b086887cd4510f9a0a21f041443b662887c8c510ec98a21f131443a262887c88510f890a215e53042baa6085e94010
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x6807a400210058061c4a250000080001020e300026028286002001001171443145429c584504cb0c435484187992544c61c6454e21a519131c4298644c610a519131442d16110d10b458c41443904310510b858841442d1638c510a619131442b0644c510e4d9131442d2644c510b41913144390644c510a419131442d16388510
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x10806804358841442493a4c898a21241d16388510
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 99
  | 3 => 21
  | 2 => 3
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (i*5) 5
  | 5 => packedAt s5K5 (i*16) 16
  | 4 => packedAt s5K4 (i*27) 27
  | 3 => packedAt s5K3 (i*38) 38
  | 2 => packedAt s5K2 (i*49) 49
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (6+((h/1+packedAt s5K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s5K5 (826+((h/15+packedAt s5K5 (736+(h % 15)*6) 6) % 56)*7) 7
  | 4 => packedAt s5K4 (2904+((h/33+packedAt s5K4 (2673+(h % 33)*7) 7) % 119)*8) 8
  | 3 => packedAt s5K3 (840+((h/7+packedAt s5K3 (798+(h % 7)*6) 6) % 33)*6) 6
  | 2 => packedAt s5K2 (150+((h/1+packedAt s5K2 (147+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf81ff8783ffc3e1f1f0fe3f81e1fe0fc4ef273
  | 1 => 0xffe0ffffc0ffc3e01ff0fc7fffe1ff00713f9c
  | 2 => 0xffff007fffffffffe000ff801fffffff81c3ff
  | 3 => 0x7fff0003ffffff00001ffe0003fe03e0
  | 4 => 0xffffff80000003ffffffffffe0000003fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x4a4614898a4952050b4560a947132258467231
  | 1 => 0x50c224108611162005542430cb314608501694
  | 2 => 0x2108412210a000ca20008902104498a181814a
  | 3 => 0x459cb64524399b73566600249d990c32fa03e0
  | 4 => 0x8610c00638c2219c9888d247000010c32de800
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfeece0e0feece0e0feece0e0feece0e0feece0e0feece0e0feece0e0feece0e0feece0e0feece0e0feece0e0feece0e0feece0e0feece0e0feece0e0feece0e0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36314
namespace PEqualNP.Outside.L_meta_36314
open PEqualNP.Outside.L_meta_36314.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c38182140400004085000238085000000102ffd5009fe54007f55009fc5402ffd4c01fe53007f54c0bfc53027fd0c01fe43007f50c09fc4302ffd4807fe52007f54807fc52027fd0807fe42007f50807fc42007fcc807fe32007f4c807fc3202ffd4405fe51007f54405fc51027fd0405fe41007f50405fc41007fcc405fe31007f4c405fc3101ffc8405fe21007f48405fc2102ffd4003fe50007f54003fc50027fd0003fe40007f50003fc40007fcc003fe30007f4c003fc3001ffc8003fe20007f48003fc20017fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x826001ff0c13000fb86098007f8304c003ff9026001ff8813000ff84098007ff104c003ff0826001fe8413000ff82098003ff65480017fb2a400bff9952002dfcca90003fd65480017eb2a400bff1952002df8ca90003ff64480017fb22400aff99120025fcc890003fd64480017eb22400aff19120025f8c89002fff5448015ff2a24000ff55120057f8a890003ff63480017fb1a4000ff98d20005fcc690003fd63480017eb1a4000ff18d20005f8c69002fff5348001ff29a4000ff54d2005ff8a69002bff4348001ff21a4000ff50d20057f88690006ff6248007ffa924003ff9492001fdca49000ffd5248001f6a924003ff1492001ffe849000ffe4248007fea124003ff1092001ffe649000ffe3248007fe9924003ff0c920007fec290002ff6148013ff30a4002bf98520007fac290027fc61480057e30a400bffd452004ffca290003fd5148013fe28a400affd052004ffc8290003fd4148013fe20a4000ffcc52004ffc6290003fd3148013fe18a4003ffc852001ffc429000ffd2148007fe10a4001bfd812000ffea090007fe5048003fea824001ff1412000ffe8090007fe4048003fea024001ff1012000ffe6090007fe3048003fe9824001ff0c12000ffe409000ffb2048003ff1024001fb8812000ff84090007ec2048003fc1024001ffc412000ffc2090007fa1048003fe0824000ffd9510005feca8801bfe654400b7f32a2000ff59510005faca8801bfc654400b7e32a2000ffd9110005fec88801ffe64440097f3222000ff59110005fac88801ffc64440097e3222006ffd511003ffca888003fd544400ffe2a22000ffd8d10005fec688003fe63440017f31a2000ff58d10005fac688003fc63440017e31a2006ffd4d10007fca688003fd534400dfe29a2007ffd0d10007fc8688003fd434400ffe21a2000ffd8910005fec488023fe62440077f3122000ff58910005fac488023fc62440077e3122006ffd4910047fca488003fd5244011fe2922007ffd0910047fc8488003fd4244011fe2122000ffcc910047fc6488003fd3244011fe1922001bfd8510017fea28800bfe5144005fb28a2002ff54510007eaa28800bfc5144005ffa0a2007fdd0510017fc828800bfd4144005fe20a2002fd10510017fe628800bfe3144005fb18a2002ff4c510007ea628800bfc3144005ff90a2002ff88510017ec428800bfd2144001fa90a2002ff0851000dfec088007ff504400dfda822001ff9411000ffaa088007fc5044003fc2822001ffd011000ffc8088007fa4044003fea022000fe5011000ff88088007ff3044003ff1822001fe8c11000ffa6088003f93044003fe1822001ffc811000ffc4088007fa2044003fe9022000fe4811000ff84088007ff1044005fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x3fd315002bfe18a8016ffc85400affc42a0003fd215002bfe10a8001bfd814000ffea0a0007fe5050003fea828001ff1414000ffe80a0013fb4050003ff2028001ef9014000ff880a0007bc4050003fc2028001ff8c14000ff860a0007ff2050003ff1028001ff0814000ffe20a0007fe1050003fd0828001ff04140097fecb98002ff65cc029ff32e6005bf99730007facb98002fd65cc025fe32e6005bf19730097fec998002ff64cc027ff3266004bf99330007fac998002fd64cc025fe3266004bf193300a7fea99804ffe54cc001feaa66013ff1533000dfcc798053ff53cc025ff29e6000f794f30007faa798003dd53cc025fe29e6013ffd0f3009fbe879804bfe43cc001fea1e6012ff10f3009fb8879804bff62cc023ff3166003bf98b30007fac598002fd62cc025fe3166003bf18b300a7fea598047fe52cc001fea966011ff14b3009ffe8598047fe42cc001fea166011ff10b30097fe6598003df32cc023ff1966000ff4cb30007ba659804bfc32cc025ffb0e6010ff98730015fcc398003fd61cc0017eb0e6012ff18730015f8c398053ff51cc021ff28e6000ff54730087f8a39804fff41cc021ff20e6000ff50730087f8839804bff31cc001ef98e6010ff8c730007fa6398003dd31cc025fe18e6011ffc8730087fc4398003fd21cc021fe10e6001bf5833000ffea198007fe50cc003fea866001ff1433000ffe8198007fe40cc003fea066001ff1033000ffc6198007de30cc003fd1866001ff0c33000fb86198007ff20cc003ff1066001ff0833000ffe2198007fe10cc003fe0866000ffd9530005feca980037f654c0013fb2a600fff9953002dfcca98003fd654c0017eb2a600fff1953002df8ca980037c654c00b3e32a6000ffd9130005fec89803bfe644c0097f3226000ff59130005fac89803bfc644c0097e322600fffd5130077fca898003fd544c01dfe2a26001bfd8d3007ffea698003fe534c001ef29a6000ff54d30007baa69803ffc534c01dffa1a600ef7d0d30007fc8698003fd434c01dfe21a600ef710d30007fec498002ff624c01bff3126003bf98930007fac498037fc624c0077e312600fffd493006ffca498003fd524c01bfe292600effd093006ffc8498003fd424c01bfe2126000ffcc930007be6498037fe324c001fe9926000f74c93006ff86498003ff614c0017fb0a600cff98530015fcc298003fd614c019fe30a6002bf1853007ffea298033fe514c001fea8a600cff14530077fe8298033fe414c001fea0a600cff10530007fe6298003df314c019ff18a6000ff4c530007ba6298033fc314c01bff90a600cff88530007fa4298033fc214c0037fb026001ffd413000ffca098007fd504c003fe2826001ffd013000ffc8098007fd404c003fe2026001ffcc130007f66098007fe304c003ef1
  | 2 => 0x210effea690803fe5348401fea9a421dff14d210e7fe8690803fe4348401fea1a421cff10d21015fec49080fff5248407ff2924203ff5492101ff8a49080fff4248407ff2124203fb9092101ffa8490803ed4248407fe2124203ffcc92101ffc649080ffd3248407fe1924202bfd8521017fea29080bfe5148405fea8a4202ff14521017fe829080bfe4148405fea0a4202ff10521017fe629080bfe3148405fe98a4202ff0c521017fe429080ff72148405ff10a4202fb88521017f8429080bec2148405fa10a4200ffd8121005fec09086ffe60484037f3024200ff581210dff8c090806fc604843bffa82421bff941210dff8a090873ff4048437ff202421bff101210dffc609086ffc3048407ff9024203ff8812101ff8409080bff1048405fb8824202ff84121017f82090806ff6554001ffb22a000bfd91500d7fcc8a8012fe6454001feb22a01aff19150025f8c8a8017ff545400bff2a2a005ff5515002ff8a8a8003ff63540017fb1aa000ff98d50007fac6a8003fc63540017e31aa005ffd4d5002ffca6a8017fd535400bfe29aa01affd0d50007fc86a8003fd4354035fe21aa000ffd8950005fec4a8067fe62540077f312a000ff589500cff8c4a800efc625400bffa92a005dfd495002ffca4a8017fd5254001bea92a005ff149500d7fe84a8067fe4254001fea12a019ff10950007fe64a8067fe3254001fe992a019ff0c950007fec2a8002ff6154031ff30aa002bf98550007fac2a8063fc61540057e30aa005ffd455002ffca2a8017fd515400bfe28aa01affd05500c7fc82a8003fd4154031fe20aa000ffcc5500c7fc62a8003fd3154031fe18aa019ffc85500c7fc42a8003fd2154031fe10aa001bfd815000ffea0a8017fb5054003ff282a001df9415000ff8a0a80077c5054003fc282a001ffd015000ffc80a8007fc4054003ff182a001ff0c15000ffe40a8007fe2054003fe102a001ffc415000ffc20a8007fc1054001ffb2a8000bfd95400bffccaa0016fe6550001feb2a8000bf595400bff8caa0016fc65500037fb228004ffd5140027fca8a0013be5450009feaa28000ef55140027f8a8a0003ff63500017fb1a8000ff98d40007fac6a0003fc63500017e31a8017ffd4d40007fca6a0003fd535002ffe29a8004ffd0d40027fc86a0013fd4350009fe21a8000ffd8940005fec4a005bfe62500077f3128000ff589400b7f8c4a000efc625002fffa928016ff94940007faa4a005bfc5250009ffa128004efd0940027fc84a0013fd4250001dea128004ff10940007fe64a005bfe3250001fe9928016ff0c940007fec2a0002ff615002bff30a8002bf98540007fac2a0057fc61500057e30a8017ffd45400affca2a0003fd515002bfe28a8004ffd0540027fc82a0013fd4150009fe20a8000ffcc5400affc62a000
  | 3 => 0xf8828202ff84141017f820a084bff65cc4017fb2e6225ff9973102dfccb98803fd65cc4017eb2e6212ff1973102df8cb9884bff64cc4017fb266224ff99331025fcc998803fd64cc4017eb266212ff19331025f8c998897ff54cc449ff2a66200ff55331127f8a99880afe63cc44bffa9e6225f7d4f31097fca798803fd53cc425fe29e6225f714f31127fe879884bfe43cc401ef21e6200ff50f31007ba879884bfc43cc425ffb166223ff98b3101dfcc598803fd62cc4017eb166212ff18b3101df8c598897ff52cc447ff2966200ff54b3111ff8a598893ff42cc447ff2166200ff50b3111ff8859884bff32cc401ef9966223ff8cb31007fa6598803dd32cc425fe1966202bf58731017fea39880bfe51cc405fea8e6202ff14731017fe839880bfe41cc405fea0e6202ff10731017fc639880bde31cc405fb18e6202ff0c731017b8639880bff21cc405ff10e6202ff08731097fec19888bfe60cc4037f3066200ff58331005fac19884bfc60cc4037e3066225ffd4331117fca19888bfc50cc449ffa066222ff90331117f8819888bfe30cc425fe1866223ffc8331117fc419888bfc20cc405ff8866202ff84331017f82198803ff654c4017fb2a6221ff9953102dfcca98803fd654c4017eb2a6221ff1953102df8ca98803ff644c4017fb226200efd91310057ec898883fe644c4097f3226200ff59131005fac898883fc644c4097e3226200ef1913102578c898887ff544c441ff2a26200ff55131107f8a89880aff634c443ffa9a6221f7d4d31007fca698803fd534c443fe29a6221f714d31107fe8698803fe434c401ef21a6200ff50d31007ba8698883fc434c401ffb126200bfd89310fffcc49880efe624c401feb12621fff1893101df8c498887ff524c43fff2926200ff549310fff8a498883ff424c43fff2126200ff509310fff88498803ff324c401ef992621fff8c931007fa6498803dd324c43ffe1926202bfd8531017fea29880bfe514c405fea8a6202ff14531017fe829880bfe414c405fea0a6202ff10531017fe6298803f7314c405ff18a6202f78c531017f8629880bdc314c405fa18a6202ffc8531017fc429880bfc214c401ffb026200bfd81310f7fcc098806fe604c401feb02621eff1813100df8c098887ff504c43dff282621eff14131107fe809887bfe404c43dfe202621eff8c1310f7f8609887fff204c43dff102621eff08131017fe209880bf7104c405ff0826202ff04131007feca90802ff654843bff32a4205bf99521007faca90802fd654843bfe32a4205bf19521007fec890802ff6448439ff3224204bf99121007fac890802fd6448439fe3224204bf191210effea890873fe5448401feaa2421cff15121007fec690802ff6348401ff31a4200bf98d21007fac690802fd6348401fe31a4200bf18d
  | 4 => 0xffc524c807ffa126403ff9093201ffa849900ffc424c807ff9926400fbcc93201ffc649900fde324c807fe1926403f70c93201fd86499003ff614c8017fb0a642dff98532015fcc299003fd614c85bfe30a6402bf1853217ffea2990b7fe514c85bfe28a642effd053216ffc82990b7fc414c85bff18a642dff0c53201ffe429900ffe214c807fe10a6400ffd8132005fec0990b3fe604c8037f3026400ff58132167f8c099006fc604c85fffa82642cff94132167f8a0990bbff404c859ff202642cff10132167fc60990b3fc304c807ff9026403ff8813201ff840990b7ff104c859ff082642cff04132015fecaa8803ff64544017fb22a22bff99151025fcc8a8803fd6454457fe322a204bf1915102ffea8a88177f545440bff2a2a205ff55151006faa8a8817fc5454401ffb1aa200bfd8d51007fcc6a8803fd6354401fe31aa200bf18d5102ffea6a8817fe535440bfea9aa205ff14d5115ffe86a8803fe4354401fea1aa22bff10d51007fec4a8802ff6254455ff312a203bf98951007fac4a88abfc62544077e312a205ffd495102efea4a8817fe525440bfea92a200df5495102ff8a4a88afff4254455ff212a200ff50951157f884a8803ff3254455ff192a200ff4c951157f864a880aff6154405ffa8aa205fdd4551017fca2a880b7e5154405fe28aa202df14551017e8a2a880bff4154405ff20aa202ff10551017fc62a880bfc3154405ff90aa202ff88551017f842a8803ff60544017fb02a229ff9815100dfcc0a8803fd6054453fe302a201bf1815102ffea0a8817fe505440bfe282a22bffd015114ffc80a88a7fc4054453ff182a229ff0c151157fe40a88a7fe2054453fe102a202ffc4151017ee20a880bfe1054405fe082a200ffd9541005fecaa08a3fe655040b7f32a8200ff59541005facaa08a3fc655040b7e32a8202bfd9141027fea8a0813fe5450409feaa28204ff15141007fec6a0802ff6350401ff31a8200ff58d41007f8c6a0802fc6350451ffa9a8200ff94d41007faa6a08a3fc5350409ffa1a8204ff90d41027fa86a0813fc4350401ffb128200bfd894113ffcc4a080efe6250401feb128227ff1894101df8c4a08a3ff525044fff2928200ff5494113ff8a4a0813ff4250409dfa128204ff90941027fa84a0803bd4250409fe2128200ffcc94113ffc64a0803fd325044ffe1928202bfd8541017fea2a080bfe5150405fea8a8202ff14541017fe82a0813f74150405ff20a8202ef90541017f882a080bbc4150405fa20a8202ff8c541017f862a080bff2150405ff10a8202ff08541007fec0a0802ff605044dff3028201bf98141007fac0a089bfc60504037e3028228ffd4141137fca0a089bfc5050409ffa028204ff90141027f880a089bfe305044dfe1828227ffc8141137fc40a089bfc2050405f
  | 5 => 0x8152007fac0a90dffc60548037e302a405ffd415202efea0a9017fe505480bfe282a439ffd01521bffc80a90dffc405486fff182a437ff0c15201ffe40a900fef2054807ff102a403ff081521c7fe20a90dffe105486ffe082a400ffd9542005fecaa10dbfe655080b7f32a8400ff59542005facaa10dbfc655080b7e32a8403bfd9142027fea8a1013fe5450809df2a28404ff551420077aa8a1013fc5450801ffb1a8400bfd8d42007fcc6a1003fd6350801fe31a8400bf18d421b7fea6a1003fe5350801fea9a8436ff14d42027fe86a1013fe4350801df21a8404ff50d42027f886a1013bc43508077fb128403ffd494201ffca4a100ffd5250807fe2928403ffd0942027de84a100ffe4250807df2128403ff1094201f7884a100fec4250807ff1928403ff0c942007fec2a1002ff615086bff30a8402bf98542007fac2a10d7fc61508057e30a8436ffd45421affca2a10d7fc5150809ffa0a8404efd0542027fc82a1013fc415086bff18a8435ff0c54201ffe42a100fef2150807ff10a8403ff08542007fec0a1002ff6050869ff3028401bf98142007fac0a10d3fc60508037e3028436ffd41421a7fca0a10d3fc5050809ffa028404efd0142027fc80a1013fc4050869ff1828434ff0c14201ffe40a100ffe2050807fe1028435ffc41421a7fc20a10d3fc1050825ffb2e6400bfd973219ffccb99016fe65cc801feb2e6400bf59732097f8cb99016fc65cc825ffb266400bfd9332197fcc999012fe64cc801feb266400bf59332097f8c999012fc64cc867ffaa66432ff95332007faa9990cbfc54cc8077f31e6433ffd4f32097fca799003fd53cc825fe29e6432ffd0f32097fc8799003fd43cc825fe21e6403bf58b3201ffea59900ffe52cc807fea966403ff14b3201ffe859900ffe42cc807fea166403ff10b3201ffc659900fde32cc807f71966403ff0cb3201fb8659904bff61cc863ff30e6402bf98732007fac399002fd61cc825fe30e6402bf1873219ffea3990c7fe51cc863fe28e6432ffd073218ffc83990c7fc41cc863ff18e6412ff0c73201ffe439900ffe21cc807fe10e6412ffd8332187fcc199006fe60cc801feb066400bf58332097f8c199006fc60cc867ffa866430ff94332187f8a1990cbff40cc861ff2066430ff10332187fc619904bfc30cc807ff9066403ff8833201ff841990c7ff10cc861ff0866430ff04332007feca99002ff654c85fff32a6405bf99532007faca99002fd654c85ffe32a6405bf19532007fec899002ff644c85dff3226404bf99132007fac899002fd644c85dfe3226404bf1913217ffea8990bbfe544c801feaa2642eff1513201dfec6990bfff534c801ff29a6400ff54d3217ff8a6990bbff434c801ff21a6400ff50d32177f8869900eff624c807ffa926403ff9493201ffaa499
  | 6 => 0x17eb2c8612ff1964302df8cb21812fd6490c09ffaa48604ff95243027faa921813fc5490c097f31c8641ffd4e43097fca721803fd5390c25fe29c8604ffd0e430277e8721813df4390c25fe21c8604f710e43097fec521903fe6290c077f3148600ff58a43005fac52184bfc6290c077e3148641ffd4a43207fca521903fc5290c09ffa148604efd0a43027fc8521813fc4290c81ff1948612ff0ca43097fec3218fffe6190c057f30c8600ff58643005fac32184bfc6190c057e30c8641ffd46431fffca3218fffc5190c09ffa0c8604ff906431ff7c8321813fc4190c09de20c863fff8c643097f86321903ff2190c7fff10c863fff08643097fec1218fbfe6090c037f3048600ff58243005fac12184bfc6090c037e3048641ffd42431f7fca1218fbfc5090c09ffa048604ff90243027f881218fbfe3090c25fe1848640ffc82431f7fc41218fbfc2090c7fff884863eff842431f7f82121803ff6550c017fb2a863dff9954302dfccaa1803fd6550c017eb2a863dff1954302df8caa1812ff6450c09ffaa28604ff951430277ca8a1813fd5450c01deaa28604ff15143025fec6a18f7ff5350c01ff29a8600ff54d431eff8a6a1813ff4350c09efa1a8604ff90d430077c86a1813fc4350c09de21a8604f710d43007fec4a1802ff6250c79ff3128603bf98943007fac4a18f3fc6250c077e312863dffd49431e7fca4a18f3fc5250c09ffa128604ff90943027f884a18f3fe3250c79fe1928600ffd8543005fec2a18effe6150c057f30a8600ff585431dff8c2a180afc6150c7bffa8a863bff945431dff8a2a1813ff4150c09ff20a8604ff105431dffc62a18effc3150c79ff90a863bff885431dff842a1803ff6050c017fb02863aff9814300dfcc0a1803fd6050c75fe3028601bf181431effea0a18ebfe5050c75fe2828604ffd0143027fc80a1813fc4050c75ff182863aff0c1431e7fe40a18ebfe2050c75fe102863bffc41431d7fc20a18ebfc1050c077fb2aa400ffd9152005fec8a90e7fe64548097f322a400ff591521cff8c8a9012fc645480bffaa2a405dfd515202ffca8a9017fd5454801beaa2a405ff15152007fec6a9002ff6354801ff31aa400ff58d52007f8c6a9002fc635480bffa9aa405ff94d52006fca6a9017fd535480bfe29aa405df14d521cffe86a9003fe4354801fea1aa439ff10d5201dfec4a900fff525480bf7a92a403ff9495201efca4a900ffc5254807be292a403fb1495201ffe84a900ffe4254807fe212a403ff8c95201ff864a9003ff61548017fb0aa438ff98552015fcc2a9003fd6154871fe30aa402bf1855202ffea2a90177f515480bff28aa405ff145521cffe82a90e3fe4154871fe20aa438ff8c5521c7f862a900fff2154807ff10aa403ff08552007fec0a9002ff605486fff302a401bf9
  | 7 => 0xaa133fe62550077f312a800ff58954267f8c4aa00efc625500bffa92a805dfd495402ffca4aa017fc5255009ffa12a804efd0954027fc84aa013fc4255099ff192a84cff0c954007fec2aa002ff6155097ff30aa802bf98554007fac2aa12ffc61550057e30aa805ffd455402efea2aa017fe515500bfe28aa804ffd0554027fc82aa12fbe4155009fe20aa804ef1055425ffc62aa12ffc3155099ff90aa84bff8855425ff842aa003ff60550017fb02a84aff9815400dfcc0aa003fd6055095fe302a801bf1815402ffea0aa017fe5055095bf282a805ff1415402ef8a0aa013ff4055009dfa02a804ff90154027f880aa12bfe3055095fe182a84cffc8154257fc40aa12bfc2055097ff882a84aff84154257f820aa016fd6594c25ffb24a649ff99253025fcc929803fd6494c017eb24a612ff19253025f8c929817ff5494c0bff2a4a605ff5525302ff8a929816fe6394c0bffa9ca605dfd4e5302fbea7298175f5394c25fe29ca605f714e5324ffe872984bfc4394c25ffb14a648ff98a5301dfcc529803fd6294c017eb14a612ff18a5301df8c529817ff5294c0bbfa94a605ff94a5302ff8a529927ff4294c91ff214a648ff10a53247fc652984bfc3294c25ffb0ca647ff98653015fcc329803fd6194c017eb0ca612ff18653015f8c329817ff5194c0bff28ca605ff1465324ffe832991ffe4194c8ffe20ca647ff8c653097f86329923ff2194c8fff10ca647ff08653097fec12991bfe6094c037f304a600ff58253005fac12984bfc6094c037e304a605ffd425302ffca12991b7e5094c0bfe284a605df1425324ffe812991bfe4094c8dfe204a646ff8c253097f86129923ff2094c8dff104a646ff0825323ffe212991bfe1094c8dfe084a605bfd9553007fec8a9802ff6454c8bff322a604bf99153007fac8a9917fc6454c097e322a605ffd515302efea8a9817fe5454c0bfeaa2a600df5515302ff8a8a9816ff6354c0bffa9aa605f7d4d5302ffca6a98037e5354c0bfe29aa605df14d5302fb8a6a9917ff4354c8bfe21aa600ffd8953005fec4a9913fe6254c077f312a600ff58953227f8c4a980efc6254c0bffa92a605ff9495302ff8a4a9917ff4254c89ff212a644ff10953227fc64a9913fc3254c01ffb0aa600bfd855321ffcc2a980afe6154c01feb0aa643ff18553015f8c2a9817ff5154c0bff28aa605ff1455322ffe82a990ffe4154c87fe20aa643ff8c55321ff862a9913ff2154c87ff10aa643ff08553007fec0a9802ff6054c85ff302a601bf98153007fac0a990bfc6054c037e302a605ffd415302ffca0a9817fc5054c8bffa02a642ff90153217f880a990bfe3054c85fe182a644ffc8153217fc40a990bfc2054c87ff882a642ff84153217f820a984bff6590c017fb2c8641ff9964302dfccb21803fd6590c0
  | 8 => 0x800800400000800400000800000001800003800001000401000000000400401400401400003802000401000800000000000000000400000004400800c00000000000400001c00001000c00400800000002000000000801000000c01000400000402c01000000400800000400000000801000000400003001000400000c01000000c01400400000000800000403000400800400401000000400002800000801000401c00000000400000002c00400000000000000400800001001000000000000800000c00400000800000c00800000401800400000401400c01400001400000800801001000000800400000400401000000000000800001400000000000000400000400004800800802400000000000000000800000000c01400400000800400001800400400400800802000000000000000400400000000400000000402c00400002000000000000400800400000c00000400001400800c00000400800400000000000000800000000c00800400401800800000000000000800000000000401000000000400800005000000000000000000c00002400000000000c00000400000400400800001400800c00000000001400400001000000000400c00000400000001800401800800400400000000c01000802400000801c00000c00003c00c01800000000000c00400800c00400401400401001000404801000400000000000000400800401400400000800400000003405000c01800000000400800c00400400400000800000800400000400000400000000400000400400002400400001400000800400800001000000400401c00002000801000c00400003000000c00000000c02000800000000000000000400401000000800800c00400800000c00000000400c02c03800400800000400800401000000400000c00801000000000000000000000000000000400400000400400000000000000400000c00400400000800000c00000000000800401000000400000001800400800401400000400800000000000000000400000000000000000000400000000000400001800002c00001800c00400000400000000400000401400c00802801000000000000400000401000400800000800000000404c00400000400000000000400000001400000400400c01000400002400400400001400000800800000402800001800000000801400800000000400000000800c00802800000001800000400c01400401800000000c004000097fb2aa804bfd9154027fea8aa017bf5455009ff2a2a804df95154027f8a8aa0137c5455009de2a2a800ffd8d54005fec6aa003df63550016fb1aa800ff98d54007fac6aa003fc63550017e31aa800f718d54005b8c6aa017ff535500bbfa9aa805ff14d54027fe86aa013bf4355009fe21aa800ffd8954005fec4
  | 9 => 0x1f70000001d28002b40ee00000006e0000000000000003060002db8000000000530000002282c815d2e8a8593b80000003c0000000000001740000001b200029580003925512600036c9b326db6f219800000122b768000000001adaaf800357a2380000000000a00000000008b80027400009480037900000000011f8000000000000bb1deaf731180000019c2fe904b7b8000000288000002ca8003643820858002e197b8000349650f707fb0215f8003650001d80000000000002b010f97386f80000006a0000002c18000003428000002ec8000003629158000002ed96f8472c9a5009610825480000037cb740000000000000002cd00000000000028a9cb31623a0000c69643582580000000000f100000025da8981f1a99ce067868b0d3172ada6100000000000004d800000360b28245192b4382220a8c131529dae2000000232a460001e80000000000000000000000000000002e980000026a07831100000000012caca00000000023780000000017f82c28b22333b94a0b0800168000000000000359b7700011500032d35f35c8000000b780000000000023a9b180034eb2e0d89b280000036e11a00000004f8e80d50328f0b301998c32ff8cd2e38002e79278000003200000001cd8d000000018f0000f419b0000000001fa80006680004a21e1ae0df1eeaf60e396004e9970000000000000000000000000000db8000001438000000000000000000dcb7080000000024419794700000000023c35c2a2a400e28000ef28300000031a00029680000000007e8000001dc2988000000b69b534902b32aaf8a4e23900000000000000037e8002e620c80000029327300000007b8a48000000000d120b0000000000000000aca628001a480000030100000000035883400000000000000000000000016c80000003580015589a80000018480014d9c3b0725188098700013300000012923e8002e280000000005f15c00031880000000016a0000000000000000000000000003360000002570000000000002a897a8d282f8000c88000000000d90001128000000000e60000068000001b000000000004000000021417f326188291a3b0000000000000000001ab0000000648000000001070000000000000001e000009200000012a8000000000002a7afd00000000000000005c0000001401540000000000000000000000000001708000000001988000000002358000003108ea8f02a180036219d31b8d69ff000274800000000070b1da3309c81fa70b2caab9382cd9a111f0bcad51a616da9a1f31b48fda94266b660f3271aa70000000000000001f42f38001b700026f80003dab92129d4ab2a4aad91510000000000550000000002298000001d7ab880012f0002eeadf0d18000000000000002c400027535280000000024eb12800
  | 10 => 0x70661b8000276acb18a000000000000124af980000000005b8000000002c22083399828001e700009e1cb8779eb2350000000000002bf80030f1231958000000000000002670000000000000000000000001f78000002208001c0a008000000798e88001d08000b700000000000025320634e00020e1af8000dd8001e38000002a6aac9271728441991ed8000000d400000db038df80034c25f80000001eb568000000000000268000000b10001951fb0dc0000001360250000000000000010001e980002a0000001539df9078000000d700000036901700003200020e8000000001488000002048002f4812259b3a99100037b0000001588da26591cad88000131c6ad980000000030b0002f1a7d0001c0342316a5ca4d80000000000014f000255aa91e600000000005980000022d8000000fc36b0ec0000000002c78000000000002540000000c78000000000000000000000090000000020000000000001b79ff800000222000000000249000000000000000281800109000142800000000000268a6e0000001480000000000a780000000027c85c82c80000012b80019c800121b6e80014b80034608f00012800018d34d052afb13c800088a278a80f8b7200000000033080005699a099b50a2a93891c10e8000002f680000580800e00013a1da0000000002840000003192998f180000000004c80000033c8000000001aa80001c80000000019480033d8000000000001ca0000000000000001e180000000000000000037e0f900000024f8000000640850a90e180000000012c0000000000000000000000882870fe90616b8000000e7800221000000000284ab18991a08c48201fc3310000cd8002c580080000b800000123a34ad400000000000000000000007f111b752c6abcb2c0af8000000000000002b6829000000011ac49298001d60ed00019d80000000000003080024180000000000000000000012e1320002690000000000000003100000000001e58032b38000000000000003328000002d1800204140b37a920000001d3a7980034a00000000000000000027f00000010b8000e72d0801952186b450968e400000000000000000000000010da609028000000002170000000001cf0000000002cf80010a00034c8000000000000000001b11c600014537c0000000158000000000001308001bd0000000002070001c88002cc0000001c5380187a9f34709815eb351fa238060a42aa530914aa310000000001fe0002c308e19200000000000003e32ea1326480002580000000027100000000032780000000000000000012d2db00000025e0000000000000000ac3798000001198001830000820bf9dc80000000000000031826d1930a389b8ae8002eab31ad60002188000000000000000000000000000000000000aa1578938000
  | 11 => 0x1370000000000ed8000000000000000001a8aeb0000003220000000000000000000000000000000218000000000be0002790000002f20000003703828000001f880025e93b0000001698000000000000000e12d70c58000000000002e91fd93d2c392fabe007189a368e48a42cf101b3e0000002f8000119139b272aa0d21549c91c10deaa48002d32dd94c33f334249800058000317a2c00000000034fb818000001779a82c028eb3d02f1bc1e42ae80008b1db0e50002890000000001e09d2000000000000000000000266000000000000000304b6329a80018600020780002780011d35fa8a29ba0192000000000037d10880c80010400024f0000000000000148000000001182b614680000000008d2b80000000001d8ae80001288c403800004281b2da1133480a11148959be85200025aa271c432305780022b8ba81e00028f0000001d180000000037899b83880021027b00000005b00000022f04920c0e20000000000000001cd00000014e000000000000000240800354a4315b04580000021b000000000000150aea00004680017c80000021c0000002be8000000ea00032f07319e0d60c2084b0d8000cc0000a8b520a596208ca619258000000ba1490002908002950000000698000000001d50002af2d489188a8000000b600002380000007a83fb6883980030181daa3a10800156a7b9691de0bd0760000fa00000023200013f00000018900aaa09a78770000000000000001720002f12b080014200002300000017500023722293934080000010580013480018b0000000b48000000d98000b39e22578002a5a028000000000001942d100018fa938002488432c605e0c607035e86a8f483c962a122bab0c1bf0002160001fe84f2ad07e0000558000000000000000000000000000000000000000000500000000002248000000000000000000a30001cc00034b00000000000000004e28f8000000000000000001768000000000001d68001c2000141b5381a80000000000006d80000000016380010f3250001f991d86c0db0738a6307a02053b1fb14345a28b0ea87a5b2a110084100000000021490c9e48000f38001d4205b658818003561cab48a72b2a28d8000b29f000005a18e24c280a2e36797880035b0000001a41ec0000001f10000e08001bb36d036b229c7aee3648000002c88000002fe00000000000000000000028603a2e0af02f2ae521126a80000000008600000000000000005e959800000071aed0e30d480000000000ea760000fb00000028e0003448002260001e50000b00001939ab89024680000019629800016f0001908002f582db298000000001a38000a02478ada3d8000002d20000000480002dc99f800371a6b000000286980a4586b0000000001100000002f433880000000000015d80000000000002
  | 12 => 0x770650000e0000081000000000000213849aa803f30680021d80000000000021b80000000000f92693ea7c0000460000000002ce1528001020000002678000000000001f600000000012d80001b80000020531a93c00000000017c0000b223e0000001df28280035a09d8000003321572338c1b3e878a77b209bc8000002c10001f488c1ef32180000000000006f07b2b31ac80000000000000000000026400016e0000000000000000000768000000002fc8000000000b5ae405600000000022a0be800000065aab0000000001170000001b400000000024a0001db8000000000000c70301e10000000000000000000fb8000350198a200017a00009d000000377977000000000363913a9e9d000035d1a70000002201a223caf53710003618160002528000000003610000d593f80000f1a51858003001ed0878600002ec2308000000002e68000000000000000000000002f90003412ac0000000000002fb80000000000000022405880000000022c8000000000000000000000000000000000000000001c800010b0000b9000000000000000256000171979000000244b7300000023f0000000000000930000002520001f184b95a00000021f03b00017e8000cf00000016a8002a41519f2851b7f9e88000112269b62b58d32da8000000000000001f096580000035100018208d9d58000000eb800353167ac7000000000033029b030000000001328000000000002d596180000000000000036b80000000000022180034332b1b380000000000007d0191f380000000000033800030c8c900000000000000035e0000000ab80008415a8000cc83a8000000000000000f22822590000001888000000da8002e70000d788f8001a69fd0000eb00000005100024b34400000022590e0ca0fc8002a980032100004080018a8000000000000000bd8e680000035000009880000000019f0000000000000002e10cb0000000000000000000000000000000001c982bb1e91e15c80000016080000000023f8000001b094b0000360000000000000000000b400000006398e80020a1c280016e80008300000027e00000000000000000000000000013e2df95507135900014d2bd2d28003668000000000000793758f7a030001b58000000000000001632340000003400000000620000000000000002e30af2990000000002ef17300000000032b80001500000000000015f0000000000001f58000000000000000000000178088000000000000109a280006332f9f917d00000000017800000001280000000002a8000000000001668d800000023b8b180000010300024737a00000009780000033700000000000015bab10b30000000000000000000000002bb8000001338000002fd8040000002aa8338000000000000000001bd80012500000000000036a
  | 13 => 0x88b502e21d3288000618000000000001002179759d98098000f60000001c3374b2d80000000000026035400000031480000029f8003808000003158000000000000000628001f500000000035a8000ce8001ba80000007ca389688000000000b98000000000000000970002090a500000000030416b00015e06b80000000024200007a0002e480000017e00010c0000000c39660bc0001a180030a0000001a900000000001800000000000000011200000018b80000020d00031300019a9ae80000016726b80021900009f80000025a0000062b4b6980000000034b99684c02136fa1f9eaa3d0000003088000000f680000000000000012a19813000000000000000000032380000000000000000031c1358838000000ab2f7b0ba9630f800000174a3633480000000000000000000021a00000000015309c0000000000000002d780002831d3392720ad00030507da2518c00011880001000000c36700034180000000000002080000000014334f0000001580000002511c7000000061000000000231b0580033a0048002ef80001d0000000000000000000000001800000f980000031f0000000000001240d3a7580000030e12e8001e68000000000000001f2146043800000000216a8000009500000018d97b191920b330000002d000000002d0000000000002ae00000000000000036c00000019e80030289424d0680690000000000000800078248e5a438000000000001d930aa97b2902e96d29e00008a00000000000000025d0000318001498002de80013780017100033b0740001311478e980000000014594f9819108000001af0001a32a334d8d080000000033c1168003359900cf84529727a00000014127f8ee91ab478002e00000002b780000029128b8000000002630f58c280d2839ad00000005a80000000022e9f68000001cf800074b6800000000001c0000000000000001d300000026e80000000006700000004a80027000000018ca1e8000000000000000003600000000002f08000000000000000c98001700758000000000000000000310000000000000001500000000000dd10500028c000000000000091000000000000351aa60b880000020bad6a63b0805d800054a3992b26f0ca8570000000bb80000000034980024800000036d81a07c29c0000000000000000000000000000000001842588000000cba00000000000000003a9d29280000000000001691b2a026c20d9319eb80000000000029b0000002620000000000000000000002dc00025b8002bc2f31dd000000000000336a69a650ce1e2aa200027e8002680000000000000ef80024c80003d0000001760000000fab5b8000000000f52d3a78000000000144326ade0000000000000261368000f80fd00000026cb570000000000000478002c089b21cae58002
  | 14 => 0x333b73a8525f2fc2c52cb80000000000000000000000000000000014c80028c80000000000000000000000000000000022d2c29ec8050000000591163199810909a006c91e887215044814378041a1a80000027d8000000ff0540c08002b9a291220de2b200000000000000000000014490d25c0000000508001ce8003008000001d70000000001611098000000000001110002dd28d0001b982410ab468000000001da8000000000000000000000000000000000001c180000000000000008e9649e90001560750721c480b00028805d037a182bb20f8000000868ff9c5a56a948002bf0000001b9000000372b7a8fe0000a6a2b0000b814e83e9a58000828003258c0313b7f0000002812cc80005f80023000000000000009ea088001b68c50002fa0ae0003812b704d00000013a802b5500000036a9ba0000000002888000000000000000000a98000002eb800273889b24000018aceb4a8aa97db1c8000000000000001ee000000206a5080000000010690108900024babda539341e7b5dafa80004237609a0929fcac921596c00031b0000000000000000000000002d81140002b500022f8000000000000f280029000009f1bb8001ac06ea9c9bf80011b800000000355800000000000135000000000000000022a0f0002ba0000000000000001cca7a8000000000000000000370000000000000000000000002039178139ef8000728000000001ea1038000003120000001838001fb800278a412098a70001798a19dd8e937d80013db248bf31e0a09e31f812104b1850a28000000001d10000c80001b88000000000eca011be0000001aa03b959309b3faff06d21184
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x3505451014ff0505451014ff2405451014ff2305451014ff2205451000df4764c5100f6f4764c51000cf4764c510005f7754c510005f5754c510007b7744c51003df6744c51003df4744c510007b4744c51003db4744c510015f7734c510017d7734c510007d7634c510096f6634c510096f4634c510007d4634c510287d7534c510287d4534c510007d6434c510007d5434c510005f7724c510007d7324c510007d5324c510007f3704c51000df6704c51000df4704c5100f7f0704c510016f7604c510017f3604c510287f3504c5100f7f0504c5100f7f2404c5100f7d7304c5100f7f2304c5100f7d5304c5100f7f2204c51000df4764851001ef4764851000cf47648510005f77548510005f5754851003df6744851003df47448510005f77348510005f57348510015f77248510017e77248510007e7624851001ef6624851001ef46248510047e46248510047e64248510007e54248510007f3704851000df6704851000df470485100dff07048510016f76048510017f3604851027ff350485100dff050485100dff240485100dff230485100dff22048510015f87650110026f87650110014f87650110035fa7550110035f8755011000dfb745011000fbb7450110007bb6450110026fa6450110026f8645011003fb8645011003fba5450110007b95450110005fb7350110005fb725011003fbb4250110007b94250110007f37150110015fa7150110015f871501100aff0715011000efb615011000ff361501100aff25150110007f1515011003ff341501100aff041501100aff23150110007f131501100aff22150110007f12150110015f8764c110066f8764c110014f8764c1100077b754c110035fa754c110035f8754c11000778754c11003578754c110005fb744c110005f9744c11000dfb734c11000fdb734c110007db634c110096fa634c110096f8634c110007d8634c110007da534c110007d9534c110277db434c110277d8434c110005fb724c110007db324c110007d9324c110007f3714c110015fa714c110015f8714c110067f0714c11000efb614c11000ff3614c110067f2514c110007f1514c110277f3414c110067f0414c110067db314c110067f2314c110067d9314c110007f1314c110007d1314c110067f2214c110007f1214c110015f8764811001ef87648110014f87648110035fa7548110035f87548110005fb7448110005f97448110005fb7348110005f9734811000dfb724811000feb7248110007eb624811001efa624811001ef86248110047e86248110047ea5248110007e95248110007f37148110015fa7148110015f8714811004ff0714811000efb614811000ff3614811004ff25148110007f1514811026ff3414811004ff0414811004ff23148110007f1314811004ff22148110047f12148110
  | 1 => 0x8d10096f63118d102b6dd3118d10014ff7018d1000cfe7018d10014fd7018d10096f97018d1000cfc7018d10096df3018d10096fa3018d102aedd3018d10094ff7694d10004fe7694d10004fd7694d10094fc7694d100067f6594d1002e7c6594d100375f5394d10015f67194d10005f57194d1000dfa7094d10005f97094d10237785094d10004ff7654d10004fe7654d10004fd7654d10004fc7654d10015f67154d10005fb7054d1000df87054d10094ff7690d10004fe7690d10004fd7690d10094fc7690d10006bf6490d10026bc6490d10015f67190d10005f57190d101ffb44190d1000dfa7090d10005f97090d10004ff7650d10004fe7650d10004fd7650d10004fc7650d10005f77150d10015f47150d1000dfa7050d1001cfe76d8910046ee62d891002cfe75d8910004fd75d891002cfc75d8910024fe74d8910004fd74d8910024fc74d8910094fe73d8910004fd73d89100dcfd72d8910046ec32d891000cff71d8910014fe71d891000cfd71d8910014fc71d89102a6ef21d89102a6ed21d8910014ff70d891000cfe70d8910014fd70d891000cfc70d8910296ef20d8910296ed20d891001cff76589100057f75589100357c7558910005bf745891003dbc7458910005df7358910005dc7358910046ec625891028df7715891029dfb7058910004ff75589100067f75589100047f755891002cfe755891002cfc75589100067c755891002c7c7558910004ff7458910006bf7458910004bf7458910024fe7458910024fc7458910006bc7458910024bc7458910004ff7358910006df7358910004df7358910094fc7358910006dc7358910004dc7358910294ff7258910006ef725891028cff7158910006f771589100dcff7058910006fb7058910004ff7654910004fe7654910004fd7654910004fc765491002e7e65549100067d6554910015f67154910005fb705491000df870549100377b5054910004ff7650910004fe7650910004fd7650910004fc7650910026be6450910006bd6450910005f77150910015f4715091003fb7415091000dfa7050910094ff76cc910004fe76cc910004fd76cc910094fc76cc910096de63cc910006dd63cc910006ef62cc91001eec62cc910015f671cc910005f571cc91000dfa70cc910005f970cc910004ff764c910004fe764c910004fd764c910004fc764c910006de634c910006dd634c910015f6714c91000dfa704c91000df4765451002ef4765451000cf47654510015f7755451001777755451000777655451002ef6655451002ef4655451003774655451003df6745451003df47454510037775454510007755454510005f77354510005f77254510037775254510007755254510007f3705451000df6705451000df4705451014ff07054510016f76054510017f36054510037f
  | 2 => 0x2ecff7159510006f7715951014cff7059510006fb7059510036fb505951014ef85059510024fe76d911003ebe64d9110015f671d911000df571d911003fb741d911002cfe75d9110004fd75d911002cfc75d9110134fd74d911003ebe54d9110094fe73d9110004fd73d911003ebc43d911001cfe72d9110004fd72d911001cfc72d9110006be42d911003ebc42d911000cff71d9110014fe71d911000cfd71d91102d6f571d911000cf571d9110014fc71d91102e6bf41d911003ef741d91102e6bd41d91102e6f441d9110014ff70d911000cfe70d9110014fd70d911000cfc70d91102d6bf40d91102d6bd40d9110024ff765911003ebc64591102cdf771591102ddfb7059110004ff755911002cfe755911002cfc75591102d4ff7459110006bf7459110004ff7359110094fc7359110004ff725911001cfe725911001cfc725911003ebf42591102ccff7159110006f7715911003ef741591100aef44159110134ff7059110006fb7059110004ff7655110004fe7655110004fd7655110004fc76551100067f655511002e7c6555110006bf6455110026bc6455110005df7355110005dc7355110005f77155110015f4715511025fb44155110005fb705511000df8705511025778505511002cfe75d8d10004fd75d8d1002cfc75d8d10024fe74d8d10004fd74d8d10024fc74d8d1001cfe72d8d10004fd72d8d1001cfc72d8d10006de32d8d10006dc32d8d1000cff71d8d1000cfd71d8d102c6df31d8d102c6dd31d8d10014ff70d8d10014fd70d8d102bedf30d8d102bedd30d8d100f4fd7698d10006df6398d100f5f57198d10065f97098d1002cfe7598d10004fd7598d10094fc7598d10024fe7498d10004fd7498d10094fc7498d10094fe7398d1001cfe7298d10004fd7298d1001cfc7298d100f4fd7198d10096f57198d10096f63198d10114fd7098d10096f97098d10096fa3098d100057f7558d100357c7558d10005bf7458d1003dbc7458d10005ef7258d10045ec7258d10115f77158d10085fb7058d10004ff7558d100067f7558d100047f7558d1002cfe7558d1002cfc7558d100067c7558d1002c7c7558d10004ff7458d10006bf7458d10004bf7458d10024fe7458d10024fc7458d10006bc7458d10024bc7458d10006df7358d10004ff7258d10006ef7258d10004ef7258d1001cfe7258d1001cfc7258d10006ec7258d1001cec7258d10114ff7158d10006f77158d100f4ff7058d10006fb7058d102bcfe7618d10006dd6318d1002cfe7518d10004fd7518d10094fc7518d10024fe7418d10004fd7418d10094fc7418d10094fe7318d10096de7318d1001cfe7218d10004fd7218d1001cfc7218d10006de3218d10096dc3218d1000cff7118d10014fe7118d1000cfd7118d10096f57118d10014fc7118d10096df311
  | 3 => 0xc7158d20164ff7058d20006fb7058d20166fa1058d2032cfe7618d20006dd6318d2002cfe7518d20004fd7518d20094fc7518d20024fe7418d20004fd7418d20094fc7418d20094fe7318d20096de7318d20006df5318d20096dc5318d2000cff7218d2001cfe7218d2000cfd7218d2001cfc7218d20096df3218d20326dd3218d20014fe7118d20004fd7118d20014fc7118d20006de3118d20096dc3118d2001cff7018d2001cfd7018d20096df3018d2031edd3018d20094ff7694d20004fe7694d20004fd7694d20094fc7694d200067f6594d2002e7c6594d2005f5f5394d20004ff7654d20004fe7654d20004fd7654d20004fc7654d20094ff7690d20004fe7690d20004fd7690d20094fc7690d20006df6390d20096dc6390d20004ff7650d20004fe7650d20004fd7650d20004fc7650d20006df6350d20006dc6350d2000dec765492002eec765492000cec765492001def755492001f6f75549200076f655492002eee655492002eec655492005f6c655492005f6f54549200076d54549200076e535492005f6c535492005f6f5154920007eb705492000dee705492000dec70549201bfe8705492001eef605492001feb60549201bf6f50549201bf6d50549201bfea1054920014fe76d852004ef661d852002cfe75d8520004fd75d852002cfc75d8520024fe74d8520004fd74d8520024fc74d8520094fe73d8520004fd73d852000cfd72d8520014fc72d852004ef621d8520316f521d852000cfe70d852001cfd70d852000cfc70d852028ef710d85200057f755852005d7c7558520005bf7458520055bc7458520005df7358520005dc735852004ef4615852030dfb7058520004ff7654520004fe7654520004fc76545200076d5254520004ff7650520004fe7650520004fc7650520004fe76cc520004fd76cc520094fc76cc520096de63cc520006dd63cc520004ff764c520004fe764c520004fc764c520005bf744c520055bc744c520006de634c520006dd634c52002cfe76d95100367e65d951000dfa70d9510015f970d95100377b50d951014cfd75d9510024fe74d9510004fd74d9510024fc74d95100367f54d9510094fe73d9510004fd73d95100367c53d951001cfe72d9510004fd72d951001cfc72d95100067e52d95100367c52d951000cff71d9510014fe71d951000cfd71d9510014fc71d95103067f51d95103067d51d9510014ff70d951000cfe70d9510014fd70d9510306f970d9510014f970d951000cfc70d95102f67f50d9510036fb50d95102f67d50d95102f6f850d951002cff76595100367c65595102edf771595102fdfb70595102f4ff75595100067f7559510004ff7459510024fe7459510024fc7459510004ff7359510094fc7359510004ff725951001cfe725951001cfc72595100367f5259510
  | 4 => 0xc130007d953cc13037fdb43cc130097d843cc130097db32cc130007d932cc130005f971cc130097db31cc130007d931cc13002cfe76d952005e7e65d95201bcfd75d9520024fe74d9520004fd74d9520024fc74d952005e7f54d9520094fe73d9520004fd73d952005e7c53d952000cff72d952001cfe72d952000cfd72d952001cfc72d95203767f52d95203767d52d9520014fe71d9520004fd71d9520014fc71d95200067e51d952005e7c51d952001cff70d952001cfd70d95203667f50d95203667d50d952002cff765952005e7c6559520005df7359520005dc735952035def725952036dfb7059520364ff75595200067f7559520004ff7459520024fe7459520024fc7459520004ff7359520006df7359520004df7359520094fc7359520006dc7359520004dc735952035cff7259520006ef7259520004ff7159520014fe7159520014fc71595201bcff7059520006fb7059520024fe76d9120056be64d912002cfe75d9120004fd75d912002cfc75d91201a4fd74d9120094fe73d9120004fd73d912000cff72d912001cfe72d912000cfd72d912001cfc72d9120356bf42d9120356bd42d9120014fe71d9120004fd71d9120014fc71d9120006be41d9120056bc41d912001cff70d912001cfd70d9120346bf40d9120346bd40d9120346fa10d9120024ff7659120056bc645912033def725912034dfb7059120004ff755912002cfe755912002cfc7559120344ff7459120006bf7459120056be5459120004ff7359120094fc735912033cff7259120006ef7259120004ff7159120014fe7159120014fc71591201a4ff7059120006fb70591201a6fa1059120004ff7655120004fe7655120004fd7655120004fc76551200067f655512002e7c6555120026be6455120006bd6455120005df7355120005dc735512002cfe75d8d20004fd75d8d2002cfc75d8d20024fe74d8d20004fd74d8d20024fc74d8d20006df53d8d20006dc53d8d2000cff72d8d2000cfd72d8d20336df32d8d20336dd32d8d20014fe71d8d20004fd71d8d20014fc71d8d20006de31d8d20006dc31d8d2001cff70d8d2001cfd70d8d2032edf30d8d2032edd30d8d2032efa10d8d20164fd7698d20006df6398d20165ed7298d2006df97098d2002cfe7598d20004fd7598d20094fc7598d20024fe7498d20004fd7498d20094fc7498d20094fe7398d20164fd7298d20096ed7298d20014fe7198d20004fd7198d20014fc7198d20184fd7098d20096f97098d200057f7558d2005d7c7558d20185ef7258d2008dfb7058d20004ff7558d200067f7558d200047f7558d2002cfe7558d2002cfc7558d200067c7558d2002c7c7558d20004ff7458d20024fe7458d20024fc7458d20006df7358d20184ff7258d20006ef7258d20004ff7158d20014fe7158d20014f
  | 5 => 0x5dd75cc9300075f65cc9300075c65cc930075de74cc930075dc74cc930165dd72cc93001ede62cc93001edc62cc930005dd71cc93000dde70cc93000ddc70cc930096df60cc930187da10cc93000cfc764c9300067f654c93017e7c654c930006ef624c93001eec624c930005fb704c93000df8704c93000ddc764c93001edc764c93000cdc764c930005df754c930005dd754c9300075f654c9300075c654c930075de744c930075dc744c930185df724c930007cf724c930007cf624c93001ede624c93001edc624c93006fcc624c930005df714c930007db704c93000dde704c93000ddc704c930167d8704c930166df604c930167da104c930014fe76d85300067f65d85300067c65d8530066f661d853002cfe75d8530004fd75d853002cfc75d8530024fe74d8530004fd74d8530024fc74d853000cfd73d8530014fc73d853001cfe72d8530004fd72d853001cfc72d8530006df32d8530006dd32d8530066f631d8530116f710d85300057f755853007d7c75585300067f65585300067c6558530005bf7458530075bc7458530005ef725853006dec7258530066f46158530004ff7654530004fe7654530004fc76545300067f655453002e7c6554530004ff7650530004fe7650530004fc76505300067f65505301467c6550530005df7350530005dc73505302acfe76cc5300067f65cc53012e7c65cc53000df870cc530097d830cc5302adde76cc5302c6de76cc530005df75cc530005dd75cc5300075f65cc53012ede65cc53012edc65cc5300075c65cc53012e5c65cc530075de74cc530075dc74cc530006df64cc530006dd64cc530005dd72cc530006df62cc5300f5dd71cc530016de61cc530016dc61cc530097db70cc53000dde70cc53000ddc70cc530097d870cc530096df60cc530117da10cc53000cfc764c5300067f654c53010e7c654c530005bf744c530075bc744c530006f7614c530016f4614c530067d4314c530005fb704c53000df8704c5300f7d8304c53000ddc764c530016dc764c53000cdc764c530005df754c530005dd754c5300075f654c53010ede654c53010edc654c5300075c654c53010e5c654c5300079f744c530075de744c530075dc744c5300079c744c5300759c744c530006df644c530006dd644c530005df724c530006df624c530115df714c530007d7714c530007d7614c530016de614c530016dc614c530067d4614c530007db704c53000dde704c53000ddc704c5300f7d8704c5300f6df604c5300f7d7104c5300f7da104c530004ff7648530004fe7648530004fc76485300067f65485300ee7c6548530005de7348530005dd734853000dfa76cc13000efa76cc13000cfa76cc1300077b65cc1300077865cc13000dfa73cc13000fda73cc13000efb63cc13000fdb63cc130097da53c
  | 6 => 0xc72d9130076bf42d9130014fe71d9130004fd71d9130014fc71d9130006be41d9130076bc41d9130094ff70d91301f4fd70d91301f6bf40d91301f6bd40d91301f6fa10d91300057f755913007d7c75591300067f65591300067c6559130076bc6459130385df7359130004ff75591300067f75591300047f755913002cfe755913002cfc75591300067c755913002c7c75591301f4ff7459130006bf7459130076be5459130384ff7359130006df7359130076df4359130076dc4359130004ff725913001cfe725913001cfc7259130004ff7159130014fe7159130014fc71591301d4ff7059130006fb70591301d6fa1059130004ff7655130004fe7655130004fd7655130004fc76551300067f655513002e7c6555130026be6455130006bd6455130005df7355130005dc73551300779f435513039cfe7694d302367f6594d3002e7c6594d3007f5f5394d3039dde7694d30396de7694d30215dd7594d302375f6594d3002ede6594d3002edc6594d3007f5c6594d3002e5c6594d30075de7494d30075dc7494d30005dd7294d3007f5f5294d30005dd7194d3000dde7094d3000ddc7094d30096df6094d302375e5094d302375c5094d30237da1094d3002cff7654d3000cfe7654d30214fd7654d3000cfc7654d300067f6554d3002e7c6554d30005fb7054d3000df87054d3000ddc7654d3002edc7654d3000cdc7654d30235df7554d300075f7554d300075f6554d3002ede6554d3002edc6554d3007f5c6554d30075de7454d30075dc7454d3007f5f5454d300075d5454d30005df7254d30005df7154d30007db7054d3000dde7054d3000ddc7054d30217d87054d30216df6054d30217da1054d3038cfe7690d300067f6590d3020e7c6590d3038dde7390d30097d83090d30024ff7650d3000cfe7650d301d4fd7650d3000cfc7650d300067f6550d301ee7c6550d30006bf6450d30026bc6450d30385df7350d30005fb7050d3000df87050d301d7d83050d3001cfe76d89300067f65d89300067c65d893006eee62d893002cfe75d8930004fd75d893002cfc75d8930024fe74d8930004fd74d8930024fc74d893000cfd73d893001cfc73d893006eee42d893006eee32d8930014fe71d8930004fd71d8930014fc71d8930006ee21d893006eec21d8930186ef20d8930186fa10d89300057f755893007d7c75589300067f65589300067c655893006eec6258930004ff7654930004fe7654930004fc76549300067f655493002e7c65549300075e5354930004ff7650930004fe7650930004fc76509300067f65509301b67c6550930006bf6450930026bc6450930005df7350930005dc73509300779c4350930006ef625093001eec625093031cfe76cc9300067f65cc93019e7c65cc93031dde76cc930336de76cc930005df75cc930
  | 7 => 0xc7300079f744c73009dde744c73009ddc744c7300079c744c73009d9c744c730006df644c730006dd644c730005df724c730006dd624c730097d7714c730097d7614c730016de614c730016dc614c730097d4614c73000dde704c73000ddc704c7300f7d7104c730004ff7648730004fd7648730094fc7648730095de7348730005dd734873002cfe76d953007e7e65d9530024fe74d9530004fd74d9530024fc74d953007e7f54d95300067e54d953007e7c54d9530094fe73d953000cfd73d9530094fc73d953007e7f53d953001cfe72d9530004fd72d953001cfc72d953007e7f52d95300067e52d953007e7c52d9530014fe71d9530004fd71d9530014fc71d953007e7f51d95300067e51d953007e7c51d9530094ff70d9530234fd70d95302367f50d95302367d50d953039d7e76d953002c7e76d95300067e64d95300067c64d95302375f73d95300075f43d95300075c43d95300067e62d95300067c62d95300067e61d95300067c61d95302375e30d95302375c30d95302377830d95302377a10d95300067f74d95300067e74d95300067d74d95300067c74d95302367f73d953007e7e73d95302367d73d95300067f43d95300067c43d95300067f72d95300067e72d95300067d72d95300067c72d95300067f42d95300067e42d95300067c42d95300067e32d95300067c32d95300067f71d95300067e71d95300067d71d95300067c71d95300067f41d95300067e41d95300067c41d95300067e31d95300067c31d95300067f21d95300067e21d95300067c21d95302367f70d95302367e70d95302367d70d95302367c70d95302367f40d95302367e40d95302367d40d95302367c40d95302367f30d95302367e30d95302367c30d95302367f20d95302367e20d95302367d20d95302367c20d95302367f10d95302367e10d95302367d10d95302367c10d953007e7c65595303a5df7359530234ff75595300067f7559530004ff7459530024fe7459530024fc74595303a4ff7359530006df7359530004ff725953001cfe725953001cfc7259530004ff7159530014fe7159530014fc7159530214ff7059530006fb70595302357e761953007e7e76195302347e761953007f3e741953007f3d74195300067e64195300067c641953039f5d731953039e7f63195300075f43195300075c43195300067e62195300067c62195300067e61195300067c611953039e7f601953039f5e301953039f5c301953039f78301953039f7a1019530024fe76d91300067f65d91300067c65d9130076be64d913000ddd73d91300779f43d913002cfe75d9130004fd75d913002cfc75d9130094fe73d913000cfd73d91301f6dd73d913000cdd73d9130094fc73d9130076bf43d9130076df43d9130076dc43d913001cfe72d9130004fd72d913001cf
  | 8 => 0x14fc71593301d6bf40593301d6bd4059330004ff7655330094fe7655330004fd7655330094fc765533002e7e65553300067d6555330026be6455330006bd6455330005df7355330095dc735533009f9f435533000ddd7694f30096dd7694f3000cdd7694f3002ede6594f300975e6594f3002e5e6594f300975d6594f30096dc6594f3009dde7494f30095dc7494f30005dd7294f300a75f5294f30005dd7194f3000dde7094f30097da7094f30097d97094f3000ddc7094f302375e5094f302375c5094f303a4ff7654f30217da3054f303a5df7654f303aedf7654f300975f7554f3002ede6554f3002edc6554f3009dde7454f3009ddc7454f300a75f5454f300075d5454f30005df7254f30005df7154f3000dde7054f3000ddc7054f30384ff7650f30385df7350f3001cff7658b30096ec6258b30004ff7558b3002cfe7558b3002cfc7558b30004ff7458b30024fe7458b30024fc7458b3001cfd7358b3000cfc7358b30096ef3258b30096ec3258b30004ff7158b30014fe7158b30014fc7158b30166ef2058b30004ff7654b30004fd7654b30094fc7654b300067f6554b3002e7c6554b300075e5354b30005fb7054b3000df87054b30004ff7650b30004fd7650b30094fc7650b30006bf6450b30026bc6450b30005df7350b30095dc7350b3009f9c4350b3000ddd76ccb3001edd76ccb3000cdd76ccb30095df75ccb30005dd75ccb3009dde74ccb30095dc74ccb3001ede62ccb30097ce62ccb30097cd62ccb3001edc62ccb30005dd71ccb3000dde70ccb30097da70ccb30097d970ccb3000ddc70ccb3032cff764cb3032ddf764cb30326df764cb30005df754cb30005dd754cb3009dde744cb3009ddc744cb30097cf724cb3001ede624cb3001edc624cb30005df714cb3000dde704cb3000ddc704cb30014ff7658730096f46158730004ff755873002cfe755873002cfc7558730004ff7458730024fe7458730024fc7458730014fd735873000cfc7358730004ff725873001cfe725873001cfc7258730006df3258730006dd3258730096f73158730096f431587300f6fa30587300f6f71058730004ff7654730004fd7654730094fc7654730004ff7650730004fd7650730094fc7650730005df7350730095dc735073000ddd76cc730016dd76cc73000cdd76cc730095df75cc730005dd75cc73012ede65cc730096dc65cc73009dde74cc730095dc74cc730096df64cc730006dd64cc730005dd72cc730006dd62cc730016de61cc730097d661cc730097d561cc730016dc61cc73000dde70cc730097da70cc730097d970cc73000ddc70cc7302bcff764c730005bf744c73009dbc744c730016f4614c730097d4314c7300f7da304c7302bddf764c7302b6df764c730005df754c730005dd754c73010ede654c73010edc654
  | 9 => 0xd5454d4001cfe76d89400b6ee62d894002cfe75d8940004fd75d894002cfc75d894000cfd74d894001cfc74d89403cebe54d8940006bd54d8940094fe73d8940004fd73d89400b6ee42d89403ceed42d8940014fe71d8940004fd71d8940014fc71d8940024fd70d894033eef20d894033efa10d89400b6ec62589403c5fb7058940004ff7654940004fe7654940004fc765494002e7e65549400067d6554940025be74549400073d545494000dbc765094001ebc765094000cbc7650940005bf7550940005bd7550940006bf6550940006bd6550940006bc6350940025bf7250940027af7250940007af625094001ebe625094001ebc62509400b7ac625094001eac62509400b7af2150940007bb705094000dbe705094000dbc70509401a7b87050940026bf6050940027bb60509401a7ba1050940004fe76cc940004fd76cc940094fc76cc940004ff764c940004fe764c940004fc764c940014fe76d85400aef661d854002cfe75d8540004fd75d854002cfc75d854000cfd74d8540014fc74d8540094fe73d8540004fd73d854001cfe72d8540004fd72d854001cfc72d85403bebf42d8540006bd42d85400aef641d85403bef541d8540024fd70d85402cef710d85400aef461585403b5fb7058540004ff7654540004fe7654540004fc76545400073d5454540004fe76cc540004fd76cc540094fc76cc540004ff764c540004fe764c540004fc764c540005bf744c540025bc744c540004ff7648540004fe7648540004fc7648540007ad4248540214fd75d9730024fe74d9730004fd74d9730094fc74d9730094fe73d9730096de73d973001cfe72d9730004fd72d973001cfc72d97300a67f52d9730014fe71d9730004fd71d9730014fc71d9730096f970d97302367e50d97302367c50d973002cff76597300967c65597300967f7559730004ff7459730024fe7459730024fc74597300a67f545973002cff735973000cfe735973002cfd735973000cfc73597300967e53597300967c5359730004ff725973001cfe725973001cfc7259730004ff7159730014fe7159730014fc71597302167f50597302167d505973002cfe75d9330004fd75d9330094fc75d93301d4fd74d9330094fe73d9330096de73d933009edf43d9330096dc43d933001cfe72d9330004fd72d933001cfc72d933009ebf42d9330014fe71d9330004fd71d9330014fc71d9330096f970d9330024ff7659330096bc645933000ddc73593300979c4359330004ff755933002cfe755933002cfc7559330096bf745933009ebe5459330024ff735933000cfe7359330024fd735933000cfc73593301d6dc735933000cdc735933009edf4359330096be4359330096bc435933009edc4359330004ff725933001cfe725933001cfc7259330004ff7159330014fe7159330
  | 10 => 0xc950014fe76d85500c6f661d855000cfd75d8550014fc75d8550024fe74d8550004fd74d8550024fc74d8550094fe73d8550004fd73d855001cfe72d8550004fd72d855001cfc72d855040e7f52d85500067d52d85500c6f651d855040ef551d855002cfd70d855040efb50d85502eef850d85502eef710d85500c6f46158550405fb7058550004ff7650550004fe7650550004fc7650550004fe76cc550004fd76cc550094fc76cc550006df63cc550096dc63cc550004ff764c550004fe764c550004fc764c550005bf744c5500d5bc744c550006df634c550006dc634c550004ff7648550004fe7648550004fc764855002cfe76d95400be7e65d9540254fd75d954000cff74d9540024fe74d954000cfd74d9540024fc74d95403fe7f54d95403fe7d54d9540094fe73d9540004fd73d95400be7c53d954001cfe72d9540004fd72d954001cfc72d95403febf42d9540014fe71d9540004fd71d9540014fc71d9540024ff70d9540024fd70d95403ee7f50d95403ee7d50d954002cff76595400be7c65595403e5bf7459540005df7359540005dc73595403f5fb70595403ecff75595400067f75595403e4ff7459540006bf7459540004ff7359540006df7359540004df7359540094fc7359540006dc7359540004dc7359540004ff725954001cfe725954001cfc72595400be7f52595400d6bf4259540004ff7159540014fe7159540014fc7159540254ff7059540006fb70595402567e50595402567c505954000dbc765514002ebc765514000cbc7655140025bf75551400273f75551400073f655514002ebe655514002ebc65551400bf3c65551400079f73551400079c73551400bf3f5355140005bf72551400bf3f525514025ebe615514025ebc61551400bf3f5155140007bb705514000dbe705514000dbc7055140257b87055140026bf6055140027bb60551402573e50551402573c5055140257ba105514002cfe75d8d40004fd75d8d4002cfc75d8d4000cfd74d8d403debe54d8d40006bd54d8d40006df53d8d40006dc53d8d403dede43d8d403dedd43d8d4001cfe72d8d40004fd72d8d4001cfc72d8d40014fe71d8d40004fd71d8d40014fc71d8d40024fd70d8d40386df30d8d40386fa10d8d40006df6398d40075f97098d400057f7558d400bd7c7558d4009dfb7058d40006dd6318d4002cfe7518d40004fd7518d40094fc7518d4000cfd7418d40006df5318d40096dc5318d40096de4318d403d6dd4318d4001cfe7218d40004fd7218d4001cfc7218d403d6bf4218d40014fe7118d40004fd7118d40014fc7118d40094ff7018d40024fd7018d40096df3018d4038edd3018d40004fe7694d40004fd7694d40094fc7694d400067f6594d4002e7c6594d400bf5f5394d40004ff7654d40004fe7654d40004fc7654d400073
  | 11 => 0x4fe7650d21004fd7650d21004fc7650d21015ec7650921026ec7650921014ec765092101def745092101faf7450921007af6450921026ee6450921026ec64509210e7ac64509210e7ae5450921007ad5450921007ae43509210e7ac4350921007e77150921015ee7150921015ec71509211afe4715092101eef615092101fe761509211afaf41509211afad41509210e7af40509211afe7105092100cfe76d81210defa60d812102cfe75d8121004fd75d812102cfc75d8121024fe74d8121004fd74d8121024fc74d8121094fe73d8121004fd73d8121014fd72d812100cfc72d812101cfd71d812100cfc71d81210defa20d81210defa10d81210057f75581210ed7c7558121005bf74581210e5bc7458121005df7358121005dc73581210def86058121024fe76d91500d6be64d915000cfd75d9150024fc75d91500d6be54d915042ebd54d9150094fe73d9150004fd73d915001cfe72d9150004fd72d915001cfc72d915042e7f52d9150014fe71d9150004fd71d9150014fc71d915002cfd70d91503e67e50d91503e67c50d91503e6bf40d91500d6bc6459150005df7359150005dc7359150425fb705915000cfd75d8d50024fe74d8d50004fd74d8d50024fc74d8d50396de53d8d50396dd53d8d50006df43d8d50006dc43d8d5001cfe72d8d50004fd72d8d5001cfc72d8d50006de32d8d50006dc32d8d50014fe71d8d50004fd71d8d50014fc71d8d5002cfd70d8d503a6df30d8d50006df6398d5007df97098d500a5fb7058d50006dd6318d5000cfd7518d50024fe7418d50004fd7418d50094fc7418d50096de5318d503aedd5318d50006df4318d50096dc4318d5001cfe7218d50004fd7218d5001cfc7218d503ae7f5218d50006de3218d50096dc3218d50014fe7118d50004fd7118d50014fc7118d50094ff7018d5002cfd7018d5039e7e5018d5039e7c5018d50096df3018d5039edd3018d50004fe7690d50004fd7690d50094fc7690d50004ff7650d50004fe7650d50004fc7650d5001cfe76d89500ceee62d895000cfd75d895001cfc75d8950024fe74d8950004fd74d8950024fc74d8950094fe73d8950004fd73d89500ceee52d895041eed52d8950014fe71d8950004fd71d8950014fc71d895002cfd70d895035eef20d8950005df7358950005dc73589500ceec6258950415fb705895000d7c765495001e7c765495000c7c76549500067f64549500067c635495002d7f725495002f6f72549500076f625495001e7e625495001e7c62549500cf6c62549500077b705495000d7e705495000d7c70549501bf78705495002e7f605495002f7b60549501bf6f2054950004ff7650950004fe7650950004fc7650950026be6450950004fe76cc950004fd76cc950094fc76cc950004ff764c950004fe764c950004fc764
  | 12 => 0xf7159521006f77159521004ff705952100cfe705952100cfc70595211c6f71059521024fe76d91210e6be64d912102cfe75d9121004fd75d912102cfc75d91211acfd74d91210e6be54d9121094fe73d9121004fd73d91210e6bc43d9121014ff72d9121014fd72d912146ebf42d912146ebd42d912101cff71d912101cfd71d912145ebf41d912145ebd41d912100cfe70d9121004fd70d912100cfc70d9121006be40d91210e6bc40d9121024ff76591210e6bc6459121005df7359121005dc7359121455ef7259121465f77159121004ff755912102cfe755912102cfc755912145cff7459121006bf7459121004ff7359121006df7359121004df7359121094fc7359121006dc7359121004dc7359121454ff7259121006ef72591211acff7159121006f77159121004ff705912100cfe705912100cfc7059121004ff7655121004fe7655121004fd7655121004fc765512102e7e65551210067d6555121006bf6455121026bc6455121005df7355121005dc735512102cfe75d8d21004fd75d8d2102cfc75d8d21024fe74d8d21004fd74d8d21024fc74d8d21006df43d8d21006dc43d8d21014ff72d8d21014fd72d8d2144edf32d8d2144edd32d8d2101cff71d8d2101cfd71d8d21446df31d8d21446dd31d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21006de30d8d21006dc30d8d21446f710d8d2116cfd7698d21006df6398d2116ded7298d210fdf57198d2102cfe7598d21004fd7598d21094fc7598d21024fe7498d21004fd7498d21094fc7498d21094fe7398d2116cfd7298d21096ed7298d2118cfd7198d21096f57198d2100cfe7098d21004fd7098d2100cfc7098d21005bf7458d210e5bc7458d2118def7258d2111df77158d21004ff7558d2102cfe7558d2102cfc7558d21004ff7458d21006bf7458d21004bf7458d21024fe7458d21024fc7458d21006bc7458d21024bc7458d21006df7358d2118cff7258d21006ef7258d2116cff7158d21006f77158d21004ff7058d2100cfe7058d2100cfc7058d2116ef71058d21444fe7618d21006dd6318d2102cfe7518d21004fd7518d21094fc7518d21024fe7418d21004fd7418d21094fc7418d21094fe7318d21096de7318d21006df4318d21096dc4318d21014ff7218d21014fd7218d21096df3218d2143edd3218d2101cff7118d2101cfd7118d21096df3118d21436dd3118d2100cfe7018d21004fd7018d2100cfc7018d21006de3018d21096dc3018d21094ff7694d21004fe7694d21004fd7694d21094fc7694d21006df6394d21096dc6394d210ef5f5394d21004ff7654d21004fe7654d21004fd7654d21004fc7654d21006df6354d21006dc6354d21094ff7690d21004fe7690d21004fd7690d21094fc7690d21006bf6490d21026bc6490d21004ff7650d21
  | 13 => 0xd311dedf6150d31005df7050d311dfd71050d3101cfe76d8931006bf64d8931006bc64d89310feee62d893102cfe75d8931004fd75d893102cfc75d8931024fe74d8931004fd74d8931024fc74d8931014fd73d89310feee52d89310feee32d893118eef21d893100cfe70d8931004fd70d893100cfc70d8931006ee20d89310feec20d893118ef710d8931005bf7458931105bc7458931006bf6458931006bc64589310feec6258931004ff7654931004fe7654931004fc76549310067f655493102e7c6554931006bf64549311cebc6454931005df7354931005dc735493110f5c5354931006ef625493101eec6254931004ff7650931004fe7650931004fc7650931006bf6450931026bc64509310079e4350931434fe76cc931006bf64cc931196bc64cc931435de76cc93144ede76cc93110dde75cc93110ddc75cc931005df74cc931005dd74cc9310079f64cc9310079c64cc93116ddd72cc93101ede62cc93101edc62cc931015de71cc931015dc71cc931096df61cc931005dd70cc93118fd710cc931014fc764c931006bf644c931176bc644c931006ef624c93101eec624c931005f7714c931015f4714c931015dc764c93101edc764c931014dc764c93110dde754c93110ddc754c931005df744c931005dd744c9310079f644c9310079c644c93118ddf724c931007cf724c931007cf624c93101ede624c93101edc624c9310ffcc624c931007d7714c931015de714c931015dc714c93116fd4714c93116edf614c931005df704c93116fd7104c931007b764cc531007b464cc531015f673cc531017d673cc531016f763cc531017d763cc531497d753cc531097d453cc531097d643cc531007d543cc531097d732cc531007d532cc531005f570cc53100cfe76d8131006bf64d8131006bc64d81310f6fa60d813102cfe75d8131004fd75d813102cfc75d8131024fe74d8131004fd74d8131024fc74d8131014fd73d813101cfe72d8131004fd72d813101cfc72d8131006df32d8131006dd32d81310f6fa30d81310f6fa10d81310057f755813110d7c7558131005bf7458131105bc7458131006bf6458131006bc6458131005ef72581310fdec72581310f6f8605813102cfe76d95210ee7e65d95211c4fd75d9521024fe74d9521004fd74d9521024fc74d9521094fe73d9521004fd73d9521014ff72d9521014fd72d952148e7f52d952148e7d52d952101cff71d952101cfd71d952147e7f51d952147e7d51d952100cfe70d9521004fd70d952100cfc70d95210067e50d95210ee7c50d952147ef710d952102cff76595210ee7c6559521475ef7259521485f7715952147cff75595210067f7559521004ff7459521024fe7459521024fc74595210ee7f5459521004ff7359521094fc7359521474ff7259521006ef72595211c4f
  | 14 => 0x1ff9c31d91311ffb431d9131006be60d9131006bc60d91311ffb710d9131006bf75d9131006be75d9131006bd75d9131006bc75d91311febf73d9131106be73d91311febd73d9131006bf53d9131006bc53d9131006bf72d9131006be72d9131006bd72d9131006bc72d9131006bf52d9131006be52d9131006bc52d9131006be32d9131006bc32d91311febf71d91311febe71d91311febd71d91311febc71d91311febf51d91311febe51d91311febd51d91311febc51d91311febf31d91311febe31d91311febc31d91311febf21d91311febe21d91311febd21d91311febc21d9131006bf70d9131006be70d9131006bd70d9131006bc70d9131006bf50d9131006be50d9131006bc50d9131006be30d9131006bc30d9131006bf20d9131006be20d9131006bc20d91311febf10d91311febe10d91311febd10d91311febc10d9131106bc64591314bddf7359131004ff755913102cfe755913102cfc75591311fcff7459131006bf74591314bcff7359131006df7359131004ff725913101cfe725913101cfc72591311dcff7159131006f77159131004ff705913100cfe705913100cfc70591311fdbe7619131106be76191311fcbe76191311073e75191311073d7519131006bf6519131006be6519131006bd6519131006bc65191314a79d73191314a6bf63191310079f53191310079c5319131006be6219131006bc62191314a6bf61191314a79e31191314a79c31191314a7b43119131006be6019131006bc60191314a7b71019131004ff7655131004fe7655131004fd7655131004fc765513102e7e65551310067d6555131006bf6455131026bc6455131005df7355131005dc735513110f5f53551314b4fe7694d31006bf6494d3124ebc6494d314b5de7394d3110f5f5394d31097d43194d3102cff7654d31014fe7654d3121cfd7654d31014fc7654d310067f6554d3102e7c6554d31006bf6454d3122ebc6454d314addf7354d31005f77154d31015f47154d3121fd43154d314a4fe7690d311febf6490d31026bc6490d314a5de7690d3149ede7690d3110dde7590d3110ddc7590d311dddd7490d311ff9f6490d31026de6490d31026dc6490d311079c6490d310269c6490d31005dd7290d311079f4290d31015de7190d31015dc7190d31096df6190d311ff9e4190d311ff9c4190d31005dd7090d311ffd71090d31024ff7650d31014fe7650d311dcfd7650d31014fc7650d31006bf6450d31026bc6450d31005f77150d31015f47150d31015dc7650d31026dc7650d31014dc7650d3110dde7550d3110ddc7550d311fddf7450d310079f7450d310079f6450d31026de6450d31026dc6450d311079c6450d310269c6450d311079e5450d310079d5450d31005df7250d31007d77150d31015de7150d31015dc7150d311dfd4715
  | 15 => 0xf7658b31096ec6258b31004ff7558b3102cfe7558b3102cfc7558b31004ff7458b31024fe7458b31024fc7458b31014fc7358b31096ef3258b31096ec3258b3116eef2158b31004ff7058b3100cfe7058b3100cfc7058b31004ff7654b31004fd7654b31094fc7654b310067f6554b3102e7c6554b31005df7354b31095dc7354b3112f5c5354b31004ff7650b31004fd7650b31094fc7650b31006bf6450b31026bc6450b310079e4350b31005f77150b31015f47150b31015dd76ccb3101edd76ccb31014dd76ccb3112dde75ccb31095dc75ccb31095df74ccb31005dd74ccb3101ede62ccb31097ce62ccb31097cd62ccb3101edc62ccb31015de71ccb31097d671ccb31097d571ccb31015dc71ccb31005dd70ccb31444ff764cb31445df764cb3143edf764cb3112dde754cb3112ddc754cb31005df744cb31005dd744cb31097cf724cb3101ede624cb3101edc624cb31015de714cb31015dc714cb31005df704cb3100cff7658331096f86058331004ff755833102cfe755833102cfc7558331004ff7458331024fe7458331024fc7458331014fc7358331004ff725833101cfe725833101cfc7258331006df3258331006dd3258331066f63158331096fb3058331096f83058331116fa105833102cfe76d953110e7e65d9531015dd73d953110f5f53d9531024fe74d9531004fd74d9531024fc74d9531014fd73d953123edd73d9531014dd73d953110e7f53d953110edf53d953110e5f53d953110edc53d953101cfe72d9531004fd72d953101cfc72d953110e7f52d9531094ff71d953123cfd71d953123e7f51d953123e7d51d953100cfe70d9531004fd70d953100cfc70d95310067e50d953110e7c50d953123ef710d953110e7c6559531005bf7459531105bc74595314addf735953123cff75595310067f7559531004ff7459531006bf7459531004bf7459531024fe7459531024fc7459531006bc7459531024bc745953110e7f54595314acff7359531006df735953110edf535953110edc5359531004ff725953101cfe725953101cfc725953121cff7159531006f77159531004ff705953100cfe705953100cfc705953121ef71059531024fe76d9131106be64d913102cfe75d9131004fd75d913102cfc75d9131006bf54d9131106be54d9131106bc54d9131014fd73d9131106bf43d913101cfe72d9131004fd72d913101cfc72d9131106bf42d9131006be42d9131106bc42d9131094ff71d91311fcfd71d91311febf41d91311febd41d913100cfe70d9131004fd70d913100cfc70d9131106bf40d9131006be40d9131106bc40d91314a5be76d9131024be76d9131006bf65d9131006be65d9131006bd65d9131006bc65d91311ff9f73d91310079f53d91310079c53d9131006be62d9131006bc62d91311ff9e31d9131
  | 16 => 0x4941004fc765494102e7e65549410067d6554941015bc765094101ebc7650941014bc7650941006bf6550941006bd6550941006bc6350941025bf7250941027af7250941007af625094101ebe625094101ebc625094113fac6250941007b77150941015be7150941015bc71509411afb47150941026bf6150941027b761509411afaf2150941004fe76cc941004fd76cc941094fc76cc941004ff764c941004fe764c941004fc764c94100cfe76d8141136fa60d814102cfe75d8141004fd75d814102cfc75d8141014fd74d814100cfc74d8141094fe73d8141004fd73d814101cfe72d8141004fd72d814101cfc72d81413b6bf42d8141006bd42d8141024fd71d81413b6f741d81412def441d8141136fa40d8141136fa10d8141136f8605814121cfd75d9731024fe74d9731004fd74d9731094fc74d9731094fe73d9731096de73d973112edf53d9731096dc53d973101cfe72d9731004fd72d973101cfc72d973112e7f52d9731096f571d973100cfe70d9731004fd70d973100cfc70d973102cff76597310967c6559731015dc73597310975c53597310967f7559731004ff7459731024fe7459731024fc745973112e7f5459731014fe7359731014fc735973121edc7359731014dc735973112edf53597310967e53597310967c535973112edc5359731004ff725973101cfe725973101cfc725973121e7f515973121e7d5159731004ff705973100cfe705973100cfc705973102cfe75d9331004fd75d9331094fc75d93311dcfd74d9331094fe73d9331096de73d933101cfe72d9331004fd72d933101cfc72d9331126bf42d9331096f571d93311febe41d93311febc41d933100cfe70d9331004fd70d933100cfc70d9331024ff7659331096bc6459331004ff755933102cfe755933102cfc7559331096bf7459331126be5459331014fe7359331014fc7359331096be4359331096bc4359331004ff725933101cfe725933101cfc72593311debf41593311debd4159331004ff705933100cfe705933100cfc7059331004ff7655331094fe7655331004fd7655331094fc765533102e7e65553310067d6555331026be6455331006bd6455331005df7355331095dc735533112f5f53553314acff7654f314addf7354f3121fd63154f31015dd7690f31096dd7690f31014dd7690f3112dde7590f31095dc7590f31026de6490f310979e6490f310979d6490f31096dc6490f31005dd7290f311279f4290f31015de7190f31097d67190f31097d57190f31015dc7190f311ff9e4190f311ff9c4190f31005dd7090f314bcff7650f314bddf7650f314c6df7650f3112dde7550f3112ddc7550f310979f7450f31026de6450f31026dc6450f311279e5450f310079d5450f31005df7250f31015de7150f31015dc7150f31005df7050f3101cf
  | 17 => 0x57f74549510067f64549510067c635495102d7f725495102f6f72549510076f625495101e7e625495101e7c62549511576c62549510077771549510157e71549510157c71549511c774715495102e7f615495102f7761549511576f20549511c7771054951004ff7650951004fe7650951004fc765095102d7e75509510057d7550951026be64509510073d5450951004fe76cc951004fd76cc951094fc76cc951004ff764c951004fe764c951004fc764c95100cfe76d815114efa60d8151014fd75d815100cfc75d8151024fe74d8151004fd74d8151024fc74d8151094fe73d8151004fd73d815101cfe72d8151004fd72d815101cfc72d81514067f52d81510067d52d815102cfd71d815114efa50d815114efa10d815114ef8605815102cfe76d95411467e65d954125cfd75d9541014ff74d9541014fd74d95414f67f54d95414f67d54d9541094fe73d9541004fd73d954101cfe72d9541004fd72d954101cfc72d95414f6bf42d9541024ff71d9541024fd71d95414e67f51d95414e67d51d95414e6be41d95414e6bc41d954100cfe70d9541004fd70d954100cfc70d954102cff76595411467c65595414ddbf7459541005df7359541005dc73595414edf771595414e4ff75595410067f75595414dcff7459541006bf7459541004ff7359541006df7359541004df7359541094fc7359541006dc7359541004dc7359541004ff725954101cfe725954101cfc72595411467f525954115ebf425954125cff7159541006f7715954125ebe415954125ebc4159541004ff705954100cfe705954100cfc705954102cfe75d8d41004fd75d8d4102cfc75d8d41014fd74d8d41006df53d8d41006dc53d8d4149ede43d8d4149edd43d8d4101cfe72d8d41004fd72d8d4101cfc72d8d41006de32d8d41006dc32d8d41024fd71d8d414bedf31d8d4100cfe70d8d41004fd70d8d4100cfc70d8d41006df6398d41105f57198d41125f77158d41006dd6318d4102cfe7518d41004fd7518d41094fc7518d41014fd7418d41006df5318d41096dc5318d41096de4318d414c6dd4318d4101cfe7218d41004fd7218d4101cfc7218d414c6bf4218d41006de3218d41096dc3218d41094ff7118d41024fd7118d414a6be4118d414a6bc4118d41096df3118d414a6dd3118d4100cfe7018d41004fd7018d4100cfc7018d41004fe7694d41004fd7694d41094fc7694d411475f5394d41004ff7654d41004fe7654d41004fc7654d4101cfe76d894113eee62d894102cfe75d8941004fd75d894102cfc75d8941014fd74d8941094fe73d8941004fd73d894113eee42d89414d6ed42d8941024fd71d8941456ef21d894100cfe70d8941004fd70d894100cfc70d8941005df7358941005dc735894113eec62589414cdf77158941004ff7654941004fe765
  | 18 => 0xf6450d32026bc6450d321779c4350d32005ef7250d3201dec7250d321e7cc3250d3201dee73cc93201fce73cc93201eef63cc93201fcf63cc932014fe76d853216ef661d853202cfe75d8532004fd75d853202cfc75d8532024fe74d8532004fd74d8532024fc74d853201cfd73d8532006f741d853216ef441d853216ef631d853216ef621d853200cfe70d8532004fd70d853200cfc70d8532005bf7458532175bc745853216ef4615853200cfe76d8132166fa60d813202cfe75d8132004fd75d813202cfc75d8132024fe74d8132004fd74d8132024fc74d813201cfd73d8132014fe71d8132004fd71d8132014fc71d8132006fb50d8132166f850d8132166fa30d8132166fa20d81320057f755813217d7c7558132166f86058132024fe76d915115ebe64d9151014fd75d915115ebe54d9151526bd54d9151094fe73d9151004fd73d915115ebc43d915101cfe72d9151004fd72d915101cfc72d91515267f52d915102cfd71d91514debf41d915100cfe70d9151004fd70d915100cfc70d915115ebc6459151005df7359151005dc735915151df771591510157c76551510267c76551510147c765515102d7f745515102f3f74551510073f64551510267e64551510267c645515115f3c64551510075f73551510075c735515115f3f43551510057f725515115f3f42551510077771551510157e71551510157c715515125f74715515102e7f615515102f77615515125f3e415515125f3c41551512567e60551512567c605515115f3f405515125f771055151014fd75d8d51024fe74d8d51004fd74d8d51024fc74d8d515167f54d8d510067d54d8d51516de53d8d51516dd53d8d51006df43d8d51006dc43d8d5101cfe72d8d51004fd72d8d5101cfc72d8d5102cfd71d8d514aedf31d8d5100cfe70d8d51004fd70d8d5100cfc70d8d514aef710d8d51006df6398d5110df57198d51005bf7458d5115dbc7458d5112df77158d51006dd6318d51014fd7518d51024fe7418d51004fd7418d51094fc7418d51096de5318d5150edd5318d51006df4318d51096dc4318d5101cfe7218d51004fd7218d5101cfc7218d5150e7f5218d51094ff7118d5102cfd7118d51096df3118d514b6dd3118d5100cfe7018d51004fd7018d5100cfc7018d51004fe7690d51004fd7690d51094fc7690d51006bf6490d51026bc6490d51004ff7650d51004fe7650d51004fc7650d510073d5450d5101cfe76d8951156ee62d8951014fd75d8951024fe74d8951004fd74d8951024fc74d89515067f54d89510067d54d8951094fe73d8951004fd73d8951156ee52d8951506ed52d895102cfd71d8951476ef21d895100cfe70d8951004fd70d895100cfc70d8951476f710d8951156ec62589514fdf771589510157c765495101e7c76549510147c7654951
  | 19 => 0x9332014fc7159332004ff705933200cfe705933200cfc7059332004ff7655332094fe7655332004fd7655332094fc765533202e7e65553320067d6555332026be6455332006bd6455332005df7355332095dc7355332544ff7654f32227ce3254f3253cff7650f320979c4350f32014ff7658732096f46158732004ff755873202cfe755873202cfc7558732004ff7458732024fe7458732024fc745873201cfc7358732096f73158732096f4315873218ef62158732004ff705873200cfe705873200cfc705873218ef7105873200cff7658332096f86058332004ff755833202cfe755833202cfc7558332004ff7458332024fe7458332024fc745833201cfc7358332004ff7158332014fe7158332014fc7158332096fb3058332096f83058332186fa2058332186fa105833202cfe76d953217e7e65d9532024fe74d9532004fd74d9532024fc74d953201cfd73d953217e7f53d9532094ff72d9532244fd72d95322467f52d95322467d52d9532014fe71d9532004fd71d9532014fc71d953200cfe70d9532004fd70d953200cfc70d95320067e50d953217e7c50d953217e7c6559532545df7359532005fb7059532165f87059532244ff75595320067f7559532004ff7459532024fe7459532024fc745953217e7f5459532544ff7359532006df735953217e7c5359532224ff7259532006ef7259532004ff7159532014fe7159532014fc7159532004ff7059532006fb7059532004fb705953200cfe705953200cfc7059532006f8705953200cf87059532024fe76d9132176be64d913202cfe75d9132004fd75d913202cfc75d913201cfd73d9132176bf43d9132094ff72d9132204fd72d9132206bf42d9132206bd42d9132014fe71d9132004fd71d9132014fc71d9132006be41d9132176bc41d913200cfe70d9132004fd70d913200cfc70d9132176bc645913253ddf7359132005f7715913216df47159132004ff755913202cfe755913202cfc7559132204ff7459132006bf7459132176be545913253cff7359132006df7359132176bc43591321e4ff7259132006ef7259132004ff7159132006f77159132004f77159132014fe7159132014fc7159132006f47159132014f47159132004ff705913200cfe705913200cfc7059132004ff7655132004fe7655132004fd7655132004fc765513202e7e65551320067d6555132026be6455132006bd6455132005df7355132005dc7355132534fe7694d3202e7e6594d320067d6594d3217f5f5394d32097cc3294d3202cff7654d3201cfe7654d32224fd7654d3201cfc7654d320067f6554d3202e7c6554d32005ef7254d3201dec7254d32227cc3254d3252cfe7690d32026be6490d32006bd6490d32097cc3290d32024ff7650d3201cfe7650d321e4fd7650d3201cfc7650d32006b
  | 20 => 0x556dd43d8d42556bc43d8d42024fd72d8d4253edf32d8d42014fe71d8d42004fd71d8d42014fc71d8d42006de31d8d42006dc31d8d4200cfe70d8d42004fd70d8d4200cfc70d8d42006df6398d42175ed7298d42195ef7258d42005f77158d421adf47158d42006dd6318d4202cfe7518d42004fd7518d42094fc7518d4201cfd7418d42006df5318d42096dc5318d42096de4318d4254edd4318d42094ff7218d42024fd7218d42096df3218d4252edd3218d42014fe7118d42004fd7118d42014fc7118d42006de3118d42096dc3118d4200cfe7018d42004fd7018d4200cfc7018d42004fe7694d42004fd7694d42094fc7694d42025bc7494d421b75f5394d42004ff7654d42004fe7654d42004fc7654d42005bf7454d42025bc7454d420073d5454d4201dbe7690d42206be7690d4201cbe7690d42005bf7590d42005bd7590d42025be7390d420279e7390d42006bf6390d420079f6390d420079c6390d4201dbe7290d42207ae7290d4201dae7290d42007ad7290d4201dbc7290d42026bf6290d42027af6290d42005bd7190d421febe6190d421febc6190d42207af2190d42005bd7090d42014fe76d85421aef661d854202cfe75d8542004fd75d854202cfc75d854201cfd74d8542094fe73d8542004fd73d8542024fd72d8542006f751d85421aef451d85421aef641d85421aef431d85421aef621d854200cfe70d8542004fd70d854200cfc70d85421aef710d8542005df7358542005dc73585421aef4615854200cfe76d81421a6fa60d814202cfe75d8142004fd75d814202cfc75d814201cfd74d81423c6be54d8142006bd54d8142094fe73d8142004fd73d8142024fd72d8142014fe71d8142004fd71d8142014fc71d8142006fb50d81421a6f850d81421a6fa40d81421a6fa20d81421a6f86058142224fd75d9732024fe74d9732004fd74d9732094fc74d9732094fe73d9732096de73d9732096ed72d9732014fe71d9732004fd71d9732014fc71d973200cfe70d9732004fd70d973200cfc70d973202cff76597320967c65597320967f7559732004ff7459732024fe7459732024fc745973219e7f545973201cfe735973201cfc73597320967e53597320967c53597322267f52597322267d5259732004ff7159732014fe7159732014fc7159732004ff705973200cfe705973200cfc705973202cfe75d9332004fd75d9332094fc75d93321e4fd74d9332094fe73d9332096de73d9332096ed72d9332014fe71d9332004fd71d9332014fc71d933200cfe70d9332004fd70d933200cfc70d9332024ff7659332096bc6459332004ff755933202cfe755933202cfc7559332096bf7459332196be545933201cfe735933201cfc7359332096be4359332096bc43593321e6bf42593321e6bd4259332004ff7159332014fe715
  | 21 => 0xc3018d5201d7e7694d522467e7694d5201c7e7694d520057d7494d5202d7e7394d5202f5e7394d520067f6394d520075f6394d520065f6394d520075c6394d5201d7e7294d522476e7294d520076d7294d5201d7c7294d5202e7f6294d5202f6f6294d520057d7194d520057d7094d522367e6094d522367c6094d522476f2094d52004fe7690d52004fd7690d52094fc7690d520057f7590d5202d7c7590d52004ff7650d52004fe7650d52004fc7650d520057f7550d5202d7c7550d520073d5450d52014fe76d85521c6f661d855201cfd75d8552024fe74d8552004fd74d8552024fc74d85524fe7f54d85520067d54d8552094fe73d8552004fd73d855202cfd72d85521c6f651d8552006f741d85521c6f441d85521c6f621d855200cfe70d8552004fd70d855200cfc70d85521c6f4615855200cfe76d81521befa60d815201cfd75d8152024fe74d8152004fd74d8152024fc74d8152094fe73d8152004fd73d815202cfd72d8152014fe71d8152004fd71d8152014fc71d81521befa50d8152006fb40d81521bef840d81521bef830d81521befa20d81521befa10d8152005df7358152005dc73581521bef8605815202cfe76d95421b67e65d9542264fd75d954201cff74d954201cfd74d954257e7f54d954257e7d54d9542094fe73d9542004fd73d9542024ff72d9542024fd72d954256e7f52d954256e7d52d9542014fe71d9542004fd71d9542014fc71d954200cfe70d9542004fd70d954200cfc70d954257ebf40d954202cff76595421b67c6559542565bf7459542005df7359542005dc7359542575ef7259542005f771595421adf47159542005fb70595421a5f8705954256cff75595420067f7559542564ff7459542006bf7459542004ff7359542006df7359542004df7359542094fc7359542006dc7359542004dc7359542264ff7259542006ef7259542004ff7159542006f77159542004f77159542014fe7159542014fc7159542006f47159542014f471595421b67f5159542004ff7059542006fb7059542004fb705954200cfe705954200cfc7059542006f8705954200cf870595421cebf405954201dbc765514202ebc765514201cbc7655142025bf75551420273f75551420073f655514202ebe655514202ebc65551421b73c65551420079f7355142005bc73551420079c73551420059c73551421b73f5355142007af725514201dbe725514201dbc7255142267ac7255142026bf6255142027af62551422673f52551422673d5255142005bf715514225ebe615514225ebc61551421b73f5155142267af2155142005bf705514255f3e50551421b73c505514202cfe75d8d42004fd75d8d4202cfc75d8d4201cfd74d8d4253ebd74d8d42556be54d8d42006bd54d8d42006df53d8d42006dc53d8d42556de43d8d42
  | 22 => 0x4d430073d5454d4322f9c4354d43095bf7590d43005bd7590d43095be7390d430979e7390d43096bf6390d430279f6390d431febe6190d431febc6190d4301cfe76d89431e6ee62d894302cfe75d8943004fd75d894302cfc75d8943196be54d8943006bd54d8943024fd73d8943006be43d8943196bc43d89431e6ee42d89431e6ee32d8943014fe71d8943004fd71d8943014fc71d894300cfe70d8943004fd70d894300cfc70d89431e6ec6258943005f771589431ddf47158943014fe76d85431def661d854302cfe75d8543004fd75d854302cfc75d8543024fd73d854301cfe72d8543004fd72d854301cfc72d85431def641d85431def631d8543006f721d85431def421d854300cfe70d8543004fd70d854300cfc70d85431def710d85431def4615854300cfe76d81431d6fa60d814302cfe75d8143004fd75d814302cfc75d814309ebe54d8143006bd54d8143024fd73d814309edf43d814309edc43d814301cfe72d8143004fd72d814301cfc72d8143014fe71d8143004fd71d8143014fc71d81431d6fa40d81431d6fa30d81430057f75581431ed7c75581431d6f86058143024fe76d91521cebe64d915201cfd75d91521cebe54d91525a6bd54d9152094fe73d9152004fd73d915202cfd72d9152566bf42d9152014fe71d9152004fd71d9152014fc71d91525a67f51d915200cfe70d9152004fd70d915200cfc70d91521cebc6459152005df7359152005dc735915259def7259152005f771591521c5f47159152005fb70591521bdf8705915201d7c76551520267c765515201c7c765515202d7f745515202f3f74551520073f64551520267e64551520267c64551521cf3c64551520075f73551520057c73551520075c73551520055c73551521cf3f43551520076f725515201d7e725515201d7c72551522676c725515202e7f625515202f6f62551522673f42551520057f71551525973e41551521cf3c41551520057f70551522567e60551522567c60551521cf3f40551522676f205515201cfd75d8d525467d75d8d52024fe74d8d52004fd74d8d52024fc74d8d5258e7f54d8d520067d54d8d5258ede53d8d5258edd53d8d5258e7c53d8d52006df43d8d52006dc43d8d5202cfd72d8d52546df32d8d52014fe71d8d52004fd71d8d52014fc71d8d5200cfe70d8d52004fd70d8d5200cfc70d8d52006de30d8d52006dc30d8d52006df6398d5217ded7298d5219def7258d52005fb7058d521bdf87058d52006dd6318d5201cfd7518d52024fe7418d52004fd7418d52094fc7418d52096de5318d52586dd5318d52006df4318d52096dc4318d52094ff7218d5202cfd7218d52096df3218d52536dd3218d52014fe7118d52004fd7118d52014fc7118d5200cfe7018d52004fd7018d5200cfc7018d52006de3018d52096d
  | 23 => 0x1cfc72d964320e7f52d964324ebf42d9643014fe71d9643004fd71d9643014fc71d9643006be41d964324ebc41d964300cfe70d9643004fd70d964300cfc70d96430067e50d964320e7c50d964302cff76596430967c65596430967f755964322e7f545964322e7d5459643094fe7359643094fc73596430967e53596430967c535964322ebf4359643004ff725964301cfe725964301cfc725964322ebf4259643004ff7159643014fe7159643014fc7159643006be415964322ebc4159643004ff705964300cfe705964300cfc70596435bcff7654e430967f6554e430967c6554e4322f9f4354e4301cff7658a43096ec6258a43004ff7558a4302cfe7558a4302cfc7558a43094fc7358a43206ee4258a43096ef3258a43096ec3258a43004ff7158a43014fe7158a43014fc7158a43004ff7058a4300cfe7058a4300cfc7058a43014ff7658643025bc7458643096f461586431ffb64158643004ff755864302cfe755864302cfc7558643094fc7358643004ff725864301cfe725864301cfc7258643106bf42586431febe41586431fef641586431febc4158643096f73158643096f43158643004ff705864300cfe705864300cfc70586431fef7105864300cff76582430057f755824320d7c7558243096f86058243004ff75582430067f75582430047f755824302cfe755824302cfc75582430067c755824302c7c7558243094fc7358243076df4358243076dc4358243004ff725824301cfe725824301cfc7258243076bf4258243004ff7158243014fe7158243014fc71582431f6fa4058243096fb3058243096f830582431f6fa105824302cfe76d95431ee7e65d9543094ff74d954324cfd74d954324e7f54d954324e7d54d9543024fd73d95431ee7f53d954301cfe72d9543004fd72d954301cfc72d95431ee7f52d9543014fe71d9543004fd71d9543014fc71d954300cfe70d9543004fd70d954300cfc70d95430067e50d95431ee7c50d95431ee7c65595435bddf735954324cff75595430067f755954322cff7459543006bf74595435bcff7359543006df73595435bcdf7359543004ff725954301cfe725954301cfc7259543004ff7159543014fe7159543014fc7159543004ff705954300cfe705954300cfc70595431edbc765514302ebc765514302cbc7655143025bf75551430273f75551430073f655514302ebe655514302ebc65551431ef3c65551430079f7355143095bc73551430079c7355143026bf63551430279f63551431ef3f53551431ef3f525514325ebe615514325ebc61551431ef3f51551435b73e50551431ef3c50551435acfe7694d43095bc7494d431ef5f5394d430979c4394d4302cff7654d43024fe7654d4322cfd7654d43024fc7654d430067f6554d4302e7c6554d43005bf7454d43025bc745
  | 24 => 0xc7158a53004ff7058a5300cfe7058a5300cfc7058a53014ff7658653005bf745865324dbc745865310f5f5358653096f46158653004ff7458653006bf7458653004bf7458653024fe7458653024fc7458653006bc7458653024bc7458653094fc735865310edf535865310edc5358653004ff725865301cfe725865301cfc725865310e7f525865323ef65158653096f73158653096f43158653004ff705865300cfe705865300cfc705865323ef7105865300cff765825302d7c755825307f5f5358253096f860582532377a5058253004ff7458253024fe7458253024fc7458253094fc7358253004ff725825301cfe725825301cfc725825307e7f5258253004ff7158253014fe7158253014fc71582532367e5058253236fa50582532367a50582532367c5058253096fb3058253096f83058253236fa1058253024fe76d915322ebe64d915322ebe54d915320ebd54d915302cfd73d915322ebf43d915301cfe72d9153004fd72d915301cfc72d915322ebf42d9153014fe71d9153004fd71d9153014fc71d9153006be41d915322ebc41d915300cfe70d9153004fd70d915300cfc70d915322ebc64591535cddf735915322d7c76551530267c76551530247c765515302d7f745515302f3f74551530073f64551530267e64551530267c645515322f3c64551530075f73551530957c73551530075c735515302e7f635515302f5f635515322f3f435515322f3f42551535c73e415515322f3c41551532567e60551532567c605515322f3f40551530057d7494d530957e7394d530975e7394d530967f6394d5302f5f6394d5302e5f6394d532367e6094d532367c6094d5301cfe76d8953226ee62d8953024fe74d8953004fd74d8953024fc74d895319e7f54d89530067d54d895302cfd73d89530067e53d895319e7c53d8953226ee52d8953226ee32d8953014fe71d8953004fd71d8953014fc71d895300cfe70d8953004fd70d895300cfc70d8953226ec6258953005fb7058953215f87058953014fe76d855321ef661d8553024fe74d8553004fd74d8553024fc74d855312e7f54d85530067d54d855302cfd73d855312edf53d855312edc53d855301cfe72d8553004fd72d855301cfc72d855321ef651d855321ef631d855300cfe70d8553004fd70d855300cfc70d8553005bf745855322dbc745855321ef4615855300cfe76d8153216fa60d8153024fe74d8153004fd74d8153024fc74d815302cfd73d815301cfe72d8153004fd72d815301cfc72d8153014fe71d8153004fd71d8153014fc71d8153216fa50d8153216fa30d8153006fb20d8153216f820d8153216fa10d8153216f8605815322cfd75d9643096bd74d9643094fe73d9643096de73d96435acde73d96430967f53d9643096bf43d964301cfe72d9643004fd72d9643
  | 25 => 0x8d545d6dc5218d545aedf4218d545ae9f4218d545aede4218d545aedd4218d545aedc4218d54096df7118d54006de7118d54006dd7118d54096dc7118d545d6df5118d545d6de5118d545d6dd5118d545d6dc5118d545aedf4118d545aede4118d540069e4118d545aedd4118d545aedc4118d545ae9c4118d54006df2118d54006de2118d54006dc2118d54096df7018d54006de7018d54006dd7018d54096dc7018d545d6df5018d545d6de5018d540065e5018d545d6dd5018d545d6dc5018d545d65c5018d545aedf4018d545aede4018d545aedd4018d545aedc4018d54006df2018d54006de2018d54006dc2018d54006df1018d54006de1018d54006dc1018d5401cfe76d8954006df63d8954006dc63d8954266ee62d8954024fd75d895402cfd74d8954094fe73d8954004fd73d8954266ee52d8954266ee42d8954014fe71d8954004fd71d8954014fc71d895459e7f51d895400cfe70d8954004fd70d895400cfc70d8954576bf40d8954005df7358954005dc7358954006df6358954006dc6358954266ec6258954005f7715895425df47158954005fb7058954255f87058954014fe76d8554025be74d855402dbd74d8554006df63d8554006dc63d855425ef661d855425fb641d8554024fd75d855402cfd74d855425ebd74d855402cbd74d8554094fe73d8554004fd73d855401cfe72d8554004fd72d855401cfc72d855451e7f52d85544eebf42d855425ef651d855425ebe41d855425ef641d855425ebc41d8554006f721d855425ef421d855400cfe70d8554004fd70d855400cfc70d855425ef710d8554005df7358554005dc7358554006df6358554006dc635855425ef4615855400cfe76d815402d7e75d81540257d75d8154006df63d8154006dc63d8154256fa60d81542577a50d8154024fd75d81542567d75d81540247d75d815402cfd74d8154094fe73d8154004fd73d815401cfe72d8154004fd72d815401cfc72d81544267f52d81543f6bf42d8154014fe71d8154004fd71d8154014fc71d81542567e50d8154256fa50d81542567c50d8154256fa40d8154006fb20d8154256f820d8154256fa10d8154005df7358154005dc7358154006df6358154006dc6358154256f86058154024ff7659253096bc64592531ef5f535925324ebe54592531eebd5459253094fe7359253094fc73592531ee7f5359253096be4359253096bc4359253004ff725925301cfe725925301cfc72592531ee7f5259253004ff7159253014fe7159253014fc7159253004ff705925300cfe705925300cfc70592530067e50592531ee7c505925301cff7658a5317f5f5358a53096ec6258a53004ff7458a53024fe7458a53024fc7458a53094fc7358a53246ee5258a53096ef3258a53096ec3258a53004ff7158a53014fe7158a53014f
  | 26 => 0x6de32d8d54006dc32d8d54014fe71d8d54004fd71d8d54014fc71d8d54006de31d8d54006dc31d8d5400cfe70d8d54004fd70d8d5400cfc70d8d54006de30d8d54006dc30d8d545bf5f75d8d545bf5c75d8d545cf9f74d8d545bf9c74d8d545cf9f54d8d545bf5e54d8d545bf5c54d8d545bf9c54d8d54006de62d8d54006dc62d8d545cf5f52d8d545bf9f42d8d54006de61d8d54006dc61d8d545cf5f51d8d540079e41d8d545bf9c41d8d54006de60d8d54006dc60d8d540075e50d8d545cf5c50d8d545bf9f40d8d545bedf75d8d545cede75d8d545bedd75d8d545bedc75d8d545bedf74d8d545bede74d8d545bedd74d8d545bedc74d8d545bedf54d8d545bede54d8d545bedc54d8d54006df72d8d54006de72d8d54006dd72d8d54006dc72d8d545cedf52d8d545cede52d8d545cedd52d8d545cedc52d8d545bedf42d8d545bede42d8d545bedd42d8d545bedc42d8d54006df71d8d54006de71d8d54006dd71d8d54006dc71d8d545cedf51d8d545cede51d8d545cedd51d8d545cedc51d8d545bedf41d8d545bede41d8d545bedd41d8d545bedc41d8d54006df21d8d54006de21d8d54006dc21d8d54006df70d8d54006de70d8d54006dd70d8d54006dc70d8d545cedf50d8d545cede50d8d545cedd50d8d545cedc50d8d545bedf40d8d545bede40d8d545bedd40d8d545bedc40d8d54006df20d8d54006de20d8d54006dc20d8d54006df10d8d54006de10d8d54006dc10d8d54006df6398d54006dd6318d54024fd7518d540967d7518d5402cfd7418d54096bd7418d540967f5318d54096de5318d545d6dd5318d54096bf4318d54096de4318d545aedd4318d5401cfe7218d54004fd7218d5401cfc7218d545d67f5218d545aebf4218d54006de3218d54096dc3218d54014fe7118d54004fd7118d54014fc7118d54006be4118d545aebc4118d54006de3118d54096dc3118d5400cfe7018d54004fd7018d5400cfc7018d540067e5018d545d67c5018d54006de3018d54096dc3018d545bdde7618d54006de7618d545d75e7518d545af5d7518d545af9e7418d545d79d7418d545d79f5418d545af5e5418d545af5c5418d545af9c5418d54006de6218d54006dc6218d545d75f5218d545af9f4218d54006de6118d54006dc6118d545d75f5118d540079e4118d545af9c4118d54006de6018d54006dc6018d540075e5018d545d75c5018d545af9f4018d54096df7518d545d6de7518d545d65e7518d545aedd7518d545ae5d7518d54096dc7518d54096df7418d545aede7418d545ae9e7418d545aedd7418d545d69d7418d54096dc7418d545aedf5418d545aede5418d545aedd5418d545aedc5418d54096df7218d54006de7218d54006dd7218d54096dc7218d545d6df5218d545d65f5218d545d6de5218d545d6dd521
  | 27 => 0x8070000003002004c006000006800c01400f000800001802f002800c004000000000000400002f001c0000080088018004000006801401600300d800400a002000000400600d0068000004001009800c032017001808000a0030088000002043000005c004000008000400600900480480460010010004000001000000005600900b000802804a00000180fa00b003801c07e017000809000000b000000001e00c00f802000a004003002800800100201300000040090000002002000000c05e0040068018008008031802800000b0018000004002003806001c001000805c01e0100018000002000004800400800400000400080010030064008042000000000a00000a801400400b00000000c200e006800000e01d001005400000400300240000000000008004002000802400000000f800c02e011003804000a006002006000c002002004001e002004002800e005000005c032001000002400a007000000000c000031000001a00001b003400601a000800000000f00200000cc030002800403000500280000360030060064008006003000001802900000040280000000188002004002802402000b010000c002008000002c0120030020000064006003801000c000004800003a007002000800a010001000400001400080000020000000000044051003000c01c0080028000044000006000000000a0000000018004004009801200c0000034040003006000c000000002002000000f001802c03a00b000808400000a002000800600700100ac012001000005c0060050008000002002021000400000300100041960020000014000002000007400000701780480040120038024008004005000000006200300cc018001012002003000200180000060010008000000001006002001a021008800800600e0078020008000000000000200000000400120040060000000004000800000201e001003c0320210168004000000000800000000200f00bc02400f0038018000000000004800400500200280260070008020014004000000800c000002000401600200f00000180030138000004001001000c01601000000180160020008004028000000000800e0000008038020007000000000400a001801c01a000000800000e00000a801407801000200b000e027000001000c00101d800801a000000800405000600000440140000000020000000001804c02600200f8008000000001002000200000b00a800000000200000140000000004010001000000c00a0050058034002004001802400a004000002400600d000011000000300000140000000000028044002000004c000001009000402c007001000800000200500dc002000024fd75d8d5402cfd74d8d545cede53d8d545bede43d8d5401cfe72d8d54004fd72d8d5401cfc72d8d54
  | 28 => 0x1c00a009001000800c01d003000004000100f001400400800100700040030000028008003005005801c025000000400a000000800400000700000780220120000004004000001000c0180010068004002000000005c0000060000000002001005800002c000000802c00000000e800000c007003001802400000000cc01400000000d0000000002000801800c0008014024012012001c01800e01b8004000005003008c02001500000e401e001001001c00e001000800c00c016000001c00c00501c800802201e003802c01c00200c000c004019000000c002000008800c000000000803c0380030008000000001021000400e00000500000000000078000000002002806400a0020000030006002000000007a0000038000006003036817001e00500000380000000018020000000008800000a000001001403200000380300360130040000012002002001c02a05e0008000000003000803c09a0100220020000002001000000200100580180060070008004008003000001400a03800300600100040028018040023000002c006002002800400a0080030098018000001001000001b000009c00202101800f805200a0020000012002000000800801700100d8028001000002000a004000000000401300080880080000008000008017003800001a0070180054002000003000800000d002000c044000003002c002002000800401200b00580d403a009023001c016003000801800400500a000c00004a000001800c00a002801800800801d800806a03000300780100020008000020006000004000000500b8084008001001000c0060000008030002000003002400601a003000c00000e000004004000000b002003a003001800000400f0010004006006000000000c00700080b0010001001000400a00000c8004004001005808c004016000004001401301f0000018000003002c000000008005c000000003000001002400d80000080020010004000007001000801e00000180c000a0000140038032008002801803200e02c000003c00000100080000050000008000006001800805800000b807c02600200f8078000006006801800200e00380b8018001002804c00a0030020020000000000802c00401e000000000000000000000000080030000006000002000402400001080880080000088004002011001002400c00300a006c02a00000000200000110050004000026003007400200100200040140000000010000004004000400a000005801c00e0010020000020001000004c00400100100b002c003000000401c000002006003c001000003c0060010018000000000005001000803900d0020002009000808c01004d000800000a0020008008006000003801400200000d8014004007004803400a00f0010000000000004806402c00
  | 29 => 0x7a080005a1000000000722530f704bd89da0000506771146400021ca000191c0aa8a2a00022784ea916e099066400001502d805e400003580a9800089907986509f5e00000421441cc80000e0e21a000000000000aa030400000008118d6a0001d5809d9be20001458000225a666049a7910aa40001b763f419868bc8fde72c9e6489d0cf071b8b0a6c49dda676058045f0626000062c2b6000075f800061494d022992728e50a9e7d39aa20119f7e673804a00005c800000002b2000062f9908000000000023c468782920000000000112a1f79652012090227094d6900912408c21906441da8860000080311a81808f0c000199c7cf1a44161048616f8e120000da06d418a6856030670f21d2668073c10680008f19fec1be1de2702956c5bb9f507d9207668310867748bf678318f61fc1b4c4c5874078607a4627000076e9db61910c2e00011e41700c120001ad445c01a80688000391950c5b50000000123e7a106565e292a447b0f9613a1b9c7b11f1e58295f618113c85e3914808685bc0000000000000062b860e00018304798cca0000ca811a9b2026800005d283be0001d8e8eb17401a223b0000107e7498556371000077000005050dd0792800000022f628b089a341800074c80006249bf26301f1400012dc46ea35e26b85d8033025e2399ade82b82483a395163a90d6c26386b421817322640dfc154996c3088ce08eca1e029fa15e0001d925350142073803a09d0020000000003005000000800f001803000000102e806000000100200200120240008008084008000000c0160030008018020000000002c014000003001c022003000800c024009012000400803c0000008000000000000400800a003800c004022026800000000d002804c090000003800000c000000800000000400680940360050000040024018001802c006000000000400200400000040100000030004012000004000c006004002800000204e000000c0500000058038004001000000800001100f800001c001001000800a000000800000a0000018010008020000000000001201f800000600d004000c010007001002400003c002801c0000000010000022005000805801c00600280b800a00b00000040080200038004010003000803002800f00580100000000000018006000000003001000c004003c00c001000800001c0020028010000014000000800003b002000c000003013800c0040260260008002000005801800e004000800000e00800b001c000000002000c002000008000800401a0090000068008000801805c008000802c00800f0030020014003007800006201c00e00b801201200100080260040018024000001004002800c0000010004002009005006400601d0000000020003003001400c0000000014044000001000c03801a00680
  | 30 => 0xfa3e64e3800060fa21031d22d2000010860d039e7491c8669f81ca30d1fe000023760caa39079e18e20450770000040457ca3544c9800087380008fd90425048fc8000104c000180200000000001d8278594f80000750000000062297704eb050248a8b3243e031e7fe8be05a6973c2f489545bd956255599504a996e45b61f7c0e9037278c0c5c58d80944c08924491090e47396a419b9bfc2519bc8774095c6b2045619d895a06e9ebc5609c962c4068c3e484468ae99746f4938c334828c75b163e6e49d6e3398e6063f8cdc3f184520930bee3eb201e67790c43881f5654e0cf28b70e6e5e083fc8d285c41cf92f00df89c416d231a7ca20984579b003ac906247d07cc808085a4a205ae04d213e568a3263d287282831f4821298c270ca2fe5d09ca2513091e3b708bc2909bd06a620f63d40ef62da079478718f80d100b22cb86680000f84704800040fa2cc2ec11dc2d38a7431f0e3e09e1e3a14e21247d681d83cc80001ba1e8600020386cd190668001a680122b647a18e047f1d1e6ac0ce88cf0000000014a2f40d5c63788881329602722800015199fa6919b2600007b20000642669222c03a9cd200008c409a0b728c31f9c3968000607870a7bc214052800082ed800062c814e2a5914482c970e50285f214d9ef20641ff26aa019c2231e3862797e67739cd010b81587fa864c66a00006e3800008996167c615de7e61e1e07300005a51f7a7960b1e0351f627e42144259a12041220e82e58d3a3aa9fc62858b8886287c873f0a18548105c2de16a848e99ee7468c2a48913a868f010c6b9130654e8f540c2931e86c8b5031b192462d9f4677e964645b16c60bd84a430f97d4681159a0d48fca7f10c1852702e63b2a1643a182462789d2a1a8800053f800017e1ab200000000c980006d88000000134a5920f900a50c0868a21a45aa86182af09dc7ef80004eb80e424e1f1a0001c8c000061a00007882849c4057e91286d280001f4064e27e003a09b02f03db800000004c233500000000a5400000001e78c5008a80000000c8e00013f833106f661c9c3012c00000000000104000015a8000157a2868c40000173945652522f0000186e346882e38400002281bec89280003638000000072680880004d00ef417a8000000000029300002db800058c079a7a9800060809b23a280006d18000000000015a03f4799800024a8af248300000001a9c5f30fa80000000000032412094be46997a82d8844420980000e307d611300004d08ede5ee006e2f096f853a800022a03700001f8a43000002208a4e00005280000000000000000009d400014fc26524043c0990466280000001da670006c42d50d1400002dc282023200008a471a8cae000087a55b93c686110de6ad1cc0000224c01000000001e7e36002fa58010d200006c6000000
  | 31 => 0x42c84407331f768849ff01c215a4724000082482c230915ae77b15f063105862ce8a068e0803225b954c67a22c64b69eee511a000607147e60e1dac8cb0e2e3b990f622709d655910566a1964c8020bb2720057e4e6118000023008d990e600002000001afe00000000000f4024200000ad8df88b81f0026c03b46ab8b4837da13a249911e65322da11b81a4071a3163000a706590d7c7140bba30388e42ac03106f1081c84785e67bd91b42a521180891d3e4ed231286f06f413319e24148cb8894a2ac27489f6000003e26685b66ae8eae69e19f400000008b987fc62a09361401b2e3b4a3185a89c4a7c48e1e6bc0c9071481406d999dc4501ec204d8c103d20e742e78000000127430280004b180005868000438800000000005ae13548190c8c58b1a967808000623947217095686bd8dca7171f3a14918ca01b1d00662000037095b23018dfa10f852a5101c980001e7a051863e22b1bb23621fa000020c41a707864879d3c3b586163ba800000000001a685a200000000000c5e000165a56319d25469ce40000000000201c402800064e817601d9a120fb0000000000078a000080b82b08e108365c812fe00008804fb000032a8bf86980ec0835915200395be23595281b080288db1ca825480001df125e6dc822e22780000000e660001f6047e87ea00007780001484730979c61b097e5e400000001800000000017c1b888aa15504d680000000c2c60ba1707e300003011edc26112c05f019d600000004c9000000000005d9800071901640a281ac39500304c882ea64f8000000124a00023b66be18c87a286da11988ee4a5875e8fe8cb27f514766d020d84480a7811ca0741348ae85e901d22dc000005a84640001bae000135849a129c68b0bce1698b260ef18ea59b82da395800000005148ed000006099fc6bea2d461195a876785a850b9d9c00000000a8028e11422aa412800042807ae000054255381fc6e0195e7c2877442521e68711ecc197095e03f21947c200f85169848549a2547a888541c697f465388443fc88cc442067c2b480002508d240000a9861822ea000000020f8000000075470922b239780003760e685a621060b00e708ee148e7b000000000e625bb0000000000013d0a8a0001d0a175907c000136000000000000000000205e00000003bb9dee85415408380fc42480c3607c0b18252992c1fb049443802426a01eaa2d617060000398000054a000178043080005748e267e09c8464780003c9800065600000000000390800064d056e000000076f809080c0d0260c80a40a78cde37923e800009d08ff80008838ffa3ef95ba00007d835d80001cc00001e117e88429ff655c14967cc20d059286de3679eb02600fd86bb00005d2000071e9076217816c42f970431506366f6186624c93e08ea08b04110d9089
  | 32 => 0xca15e65eb000080d00001501008322959410013f65f48000000000015e91aa00020583a117c800000008421d7836997f603691a261317e40000c02243078034d8c9237a07ee3e612be543808c08b1054371800000015b8000234649000000000e326571b600001cec0bb039a373152457513145e8800000018506959bc66f6808e00022f846d80006eb0d2275c1c1a5599d8876198ce05b80004dc171e4b08d4e89e99204b394a854614c24e4083a495228e47a8000478110a4361e1007f8a504448562634085c31e82ce665118c8cda2ec2401a1447f9442827817428a0d3c77784ec897913a04982846b718780cd89483f805a08a7899c7ac8a486859d0c34d09c03529cfa5520f465be9f8624d041800005fa0849dc64f00fce2f9917645e0e5034796cc14b081278f9f3660182b211f0b022ea116072e1e5c79788c2356151210b1f0e656823820600003ca16de4ff000065f065e0429ee87f6051620d239e18ca0c200003c63660b520001d806450f3a87891de81695fe2589b8421a95ac7b416206fa052e13601de21fa18e876189873aa2f4044882c82008421381e8c3c21d468791ba80d812f2363182c1b21d4a73807e48cc92cc7fd1c8e789a0e66039ba21461de85cb0e9459a9ee029a18544e9836440303400f2a04a51d1750312933a02f800000012086b10f7c15520ce45c8000000000069b00001e8859622d8e7e65b82342a811ae0f6800081f1624280210e03d105000021b452d88b2000058e7bd02a229490286b821c600016345039eae00016da34b03b20001b0a2da998431f800035412d66c78daa3f880001d1800046415a64ee853c00014ca42e8b0489ba34005f90b83290cd61bf800000023de1989bf65bf1f4c3830fc08d917f87d60422000236a32e84a658c9726000074e8c3a1ec0950b0c7ed1bde6c587e828c0cd857e000000017b28148c8669c8000891000086a80000000e582ea942625e00003691a9e6c51d545b4868e88e89fe058007e3f08e6a000000059007ca49f85886398ffc8699c785d1a25021393c4702185e00011c80001e800db9fce42a000045a21044519d2e1b588ce37b89b663c11267120db43c721f4446961285e02982f78e184060ed43ae9cce7a59b647da17602dd911806d9aa40e995063031c0434316f22ad076e33f86d84848a6668e12507d0869277222ee59c8e982ff21c804882662e114664fd0dac86c13da5e21196117207e83b108850d0d9a52f0ccc7488e7c8ad19688960156809222a73f83d0804010243381d656f22b8361001876b9d940000000176a40a0000000000001a0d1924624b0c3c287000062307c27e98d827be94f03c4182220802d44238e1a4ce1aa60d7800058600005f720ea6e59f446fd00007009b7a0000000000108a03c22308151d1c3ab08625ee8d440b280
  | 33 => 0xd687bb0df441c000022d1a5e620956a84693f27f204ba0d280888ca926c14d21467b6834840b99b600012c822e80003818fb803b8b1a4e18b9234a20440a68e8275a83206e28738475a0f881000c27399e0e26a149e7c4186284b16440f820322a206ea2ca96805939c0c3cb0a3e4e10f2414c0ef03db234244180006d583f0000071453112d883700008d3824a1ae1e147b49bcc39200000029b902c3939c63d000042da0a40cb9fde0fe000046c0dc886ea1da77e0000409800044fa0c800323a0000000000009aa1730f7e25d977e09710a226197fc00000000001aca34592c400021147ef069e1ca878e07b236e8dc1cf025614c82d71de40b792aa7b7903a23d1192143a30663b923219f99c082c01b20bf000000020600cc011a00000004ba1a5c21480000001a0842b04ea59b06983bb19660000f9a08214000000ade52480002a107b60ab011c2aaa3ca000000000000000171cb071b1c9400003fe000000030500000000a6236195d80000d381a500ec51109048ea947c8488ba288807525f3925c1c90c1e4ec9a641b4216e53c9aaa7e20dbe750000011fa3380000c261af9d3a1c316ba829990c000148c000000043c12220be00000000ab80f89d641aa9d020bf92387c80e0412d179216c804c4a694e80000000826800055e133c00000005a4000000000004ba8e807820000000000006500000001a5a2e40000481108c3cf80003928000585169e8d88de26e18000000231e00411423b9141079800002929cee26e80c000006ac24720a28140000000000079da3e47350b0641608be1771c207c11d50149828249e212a7759d481a097367e0000008886f01ed1a9076883964d20f3c8a981f80001f2c5b20000000000051a881a888800049f045e07a8aae1d689105c3088600022e2000179e29a988600016b012d98843fa9604459800038b0a8067994527d285ec2e99b0800014fa3188218000203c000122e5a99d68000145c21900000001a548b910bc5bf9c388819a2269e813e39ca3924e207fa3fd0ec229d91a425b17a61e80bd82b880000da8766429800056d8000000038858188f26510d6420899f6655074417786fc032049e22b9bea27915d643907e200023680001f740e88000539a148000031861a80001c41d7c000221c000000087f0cfc8cb849c0ad154400017940001be01cd19c424b87960000ba4617217e2b90f5641a057c00000008b29e240000cc803f9ed88b086e678c80000000700000000065c0000899a01472b100213e800089823026cf9cb647523dc54f0f665ab924c84f1a2453b121648382882cf90606df01e428f197637800d28a280001d2000087780000000a865980d5a71c191a00000005011ac00000132000075c0d71eea0001e9800000000000592683900e7cb8be2000072085f0a0e00000002
  | 34 => 0x84d04bc70ea1c243582d25e69eb823507ce3508d960360b4c0ee111c56d041e834a31c29901046e791c611220a02eb026e6ee1b4e86304425830aac0f10ae021d9aee30c9b6a0af19ae30e000034b88de8809ca000000001dc8b380988000732813a6658a5e039a2d67070aba06c084668c8af41dd9aac62e8e6482a142a5ad078215116e05f18f748e180002900ab683790ea070012a45d000077f88fa28b921c19603a81e494ba55f8c6e03a1a3a4e5a18618d12ec0001c5e30e80007771f9a71f1c9c16705604fb91d81371a9279499fe54c833a55c91348d117224569d364b8976a7810b401fd87c65db0bc81b48b1406690f28c28d7a4011bc2642903c12e109e1891d4204a143c86d9a5210e98fc56821f825807d252d1d4e27295f46b393be87d837655297983c605582fca2c43c813fe3ed123039d95003b307e079c88e05c521e861d9a621ee88d214710f459d1a680f013d2759834e18ba2be88123f81b8984203812844cd155c0589c343dea32802592b215c86b27eb8fa455806ba80f973a0c580002ef119e26f12b66d61e70000091427b0d40000196087f932c2b99e68707a15c8a600006f71a6e087924808a074268b96c05fc8000000000000014ac67082700001fb2165005200015c84ae800006b917e37586fa15c00008a8014c0b1226872f202a3b880004e9225c8a10afa000118a0001b3083f000017487f8000236086217c407084027450cf48f0021029c9f3880a16e83b196ea793a136877000000019d4000067a86f9b6c180000026d184e066000064b800000000001df9a180001c746050718000158634709a6772861e3738000034000000486407a20000342910463c8000000235a0000b8e802800035b92b00f79eb60001c4e7c302024620b126351c8834c800000000004d1237442696b660a8f1a00000000000000000084029180004100000160800000009282df1c460001000000237c0d31758000175e84b88dc84e08ec6f59c2c00000004da045a000128200000000db094e19988664078cc66c32240000183a29f08842058cfa86b000481c81885421f846fe097c88f1890136926a3100c42202142251b0ad47a812de6bd03800001fdc33ba38001a1acc0fe91562320066736836600004303f9800052200003e1942400010b043a11824f79700672000020c800008383d4341018c41c855c5c6115c646000000016ca34f800075100245b7048420000002829f2a01d208e6b5800033000008608ea67a41d521831a1c82d0ff8000064a4a3133e0000fd666e1c2a000000000007ac539054c6359a404e08000000053e4d997be6a309a2466921a8ab80008cc11c28e8a39c01e0bda20506f219e113854d1ff80160b4667c00003ec06140001ae65289a9a00019aa597891215d1bb64b8219a5068f448c201be0400
  | 35 => 0x1cf44be9a8215384ac00011227db932e26b03f28d48bc03a48c7853d165036e023a587216c5cf955275721605b417de33680003e222fc000059000008383fb0dfe89c072e3e714cc1c11eac1ce811019c04ce73886dc756840c1bb1930660835008d99b05339b480960c9e2e8135262f000054a811e132136c1ab8d625c71b5a00000363c5076816e80002e60ff649802b84530e36280894456603545349f925058e3a595235c2cc0000020a1283b804081a0167a55f0f786dc03b607b9fc28329fb05708f2210281862078e9010585d43ba0f124c48e28573a3d44d311da000224e61121b885d03ba07718a479b13d83891a948b20b34379a1d067a980c51b904622e1c16019185656203dc4b48b7e18183221c38806538880c14e9de025d11f84430e9a25910784ca13bc6c1205678b85b06a1171087305ca4d8990280680860329cc680196107c0842400b9a660c080002c019cc2d59b5c616093e24e8000471049009114aa10500007b908028750aa802719ac4fc11108920000362a22488a0f6031112563d8a288241993854c038624c0acc319021c3a79ef86dba100154000013400000001e9200000000000a443339ab879680005180dec4b5001681200ba18722348390bd45e1800060480000000c7057b968865a86126da2066736138a04f0fba2dd0a1e0799c548a49c685179be679d075820103ee7c88ca262a871e52e22725a0999a8a58a200551be41ee1cae38088c65a4a1ea3c1000031d800070386964f580005ac88d0735a3d850c9e405838c3035e15c4651982646f000020917ee00023480001b1c16e1abc7a915cc06e00006221fba73c80002c580000da238a00000000001cf67db1e545b387f400015364241ac2486219e664a1a226580008430000000000035495fc8230000000163c30696268139a4c58206e068809e844c221a2ba800010d000035182600681cc469c20b83ea84285e5800000019566041d100000000393803483f993256100000000e5240da1104998af878d800032703823ed800039e0000625085878d20846319b8c16682d870180000000000813040e1b51a26387033c4c61394000126e86a163a12a22d86af9b3a2ed0872131233a07809f07109d346c90ce20001752065978c00004784cd947078a927a3130f346cc8f9e6ffa29466321561c18ada2bc02be6cd8f4c8271ad887e82d627f18e4238977c49c1d982778000000211635f8000000205c3cd815a68095021f980004a822008b392bc30a1a2a72089fa77614c05fa841c236831217d18d87ae98fa30700f2000030e7640b9416b113625a15967e5a2180fa22768208d261db1db83f500b83a80ef8420a01620a82806bf00b0684150a66e92d059f8f5c83004aa4ee1e4c885901a88c966481e00ce27a88560ba0084779858a48f10fe61f8214
  | 36 => 0x8008d5e6330e888c10e2a77f071c6a38762018198e3058afe41e800034417784f2800005780002a418da048000000018241ea9ac633080002b28a565f299160000000248893c00003c84a2800000013780d888502fe80008b4037800000005b08b3c6c6237228c831a64a968c51a240c7fba1963559d625cb971600017d883c00007b211f27060c6a77c000000000006ea9e0a00000004d40fa6000000000f02d0013a2a22d2a15448d80003af87c052c0ad667e10ca00000503688d202a70a3443b8cac2f720682bb83e64318fe84a00dda7881f0607508f04321fe23820be40dd119456388964c003085a194b2000149a4c20e144f0811800023a453620260419da04f402e268193b6031827e7f580008701fe863b13a01388d9238c142c000000040b00007b50dde0001ca421c0a6c02a09e0000000000000002af8000246a3a64fe8c6809e800000023f474e144e5e809ce56c047600000005a7000000013108be977a163222e00000001399d18000136400000000000f2a8a7222679421522f29f1c34482ee1ff848802d8a82343913c50e8bea68d906c00011648ff0fdc7f31df200000008ef86ee000000083d00000a71e6e00000d614c962e8faa4084400000000000020c076a0000000818a1ee2b411027da80000000cb02d0925a55500005d680004dd0ec401ea1688c8800082d817c4a4000039302c825a9b9844b9990000905e5d51ee67ea0ff066c8dae00020880880a926678c46000194a3ac1776643800049897b4000181a0f30ef20151f3e0eb9c9a33aa0963e3888a76585985410f8c65887c422607223aa0000419952c358144a23616f446ca24600018b008112264090000644800006397aa7708fbc367152285c80005150874429158a00000006fe8fa21b3193665499b40000d1800000000000b5a000000000009980001f9e75313b023e00007cc876462e098214780000000b6c1e711a000020da7dca0d4416800072a91ac6e9000035c9c58792047078004604c1165c0e2864655e846201a95da130026a574220c7af800650a0bd605c09b8590a1925121c22352049640183ea7909e465a584ae32d14dc7a5047a18ea1f22891f705ab050804585ee000000081a9a4e45500001a99bbc61a1faa6cf000000003d2000000078487a80001fca4d580007d48e3c1228ed015982f4000000007200000002378742031c2b71b2a62d23d2000214e0001a6a7989590000134669402e425400002b094e0141000020f10d4000000028d989a47d80000000000570000005706ca2f1800021b9fd239000006ec0000000200e38d17ae4340eb81520b643e805aa1488b7a8eb97382c8930c5a818803c3864883c939a75e90326f010aa8a6a20a3d690342bf06a402b1ada3dd8a9a4b298a20001fb64a8a012250000007d02723a5850a8a9
  | 37 => 0x81b5e1781fa40000ddc0a5884800014804ab8000537880a8c91a340769d061b39bd410ca0188a002a41358efc7480fb26ba014847c208610f16be0a192ee2d9800014697f001784c65d8a33404919e002610cc0d09b2c72e915822402067e88bec3cb90643828ece407159c00e03d6690868600004264cc080e63a066c0268000124974e69f0df048b23ee43721d689892864d723e048188105cd1c145ed94a631206500070b8a70a0ebc7bf934e1a408aa50215ea07114ae12f8a8e7eb228c09420cc40a992642700ae52923c20000f5256019d08568c8211b0fda44b1fe46d4a3bc0001eca000229000000001c5942081b888e1dea0e211a0dd441a98960ce1d7227b80000df23e24dd8c720000000195086c65fa39a7b88bc4000185a4ca9e5665212b81b91ae22ff9514763140671c8000474a3c8000000009d02162ac873235d000000007a600000000000f647ff8000000087c000000005c93e237a92928fc97fa7558674000039200009c80000a6000010203138f8a61f00001c4a0ba522833e7e50bcc391155e6ed0a2600000000cca2b009f12b4822898c0ea83945d58b206dd00fa2fd0a8c4c381bc13c175c3c29bf080b06b000011860000c5a144801407a000078b12988af1cbe6370af685085e87de18a032809f429b98d25f817d0027904e00002f274b19e4000140c00000002ee078a4a384de1ad80005718f680000f7225c910e4728b2c32697723a70c606ef9e1a5141084038968e13f93dc65c800039e9c5a10d818445421267d7074a3f496786828a3a3081828281070228e0144550a2560a407be1b01038859a1985ef15762252320824221e57722387c597fe713025a4b9848e44580568e58000000151e0000eda6e69eb42b3800000008ea0000e8c113812e4df16580001c26029980450c000040c000061d0fae000203658a800000000007ee206c0001cde89f00005c2859e2249fc000004ee6e51db42eb8000285130a00020ac669a0943e511be5bc000064f1e9a00009d80001a4a000000000019f28e60dc060d9ba00001e9e77500004be00b40788b9a3c190fc1161e0654404e464a074c71822e8011000057899ec10801d068686300000f5e6f2a34c1ec1c625e10b80743a2c00ec12023ce15ca0099d286eea10223f91d069600a245aa3cc3f91a48093971275784a24800cec78f0a58094844a2a983c243e808087c00005d3183c6ba9dcc000030015d9940319868a7f686525f680aa70da28207c84f833909a4000000010a8f584e4800050e13ea0000000671955847b81aa3c787dc53d83e43b6048c5b112ac00017b000012423a89c667e399a2425800050601660000e165071a7400000008fc068488d9ab689b020a5f080001f695920fd9c2e18f18ac05e1c920831dbc39705a43d3862a1d5a31400000000f6052
  | 38 => 0x1d9a6e0918e7f423588671b7e11517e212812a8547000073e00dc4b9237a606124e55d137282a9768844938082f002c2e0884c75d89cc8821a764201fe617f060a0000328000000048299224bd14866c390b423a0cbe2c21e8e5cc1010228a14a7c908ca0229df482f93e65dba0ee458832c4bf000005e89928530000000000006d00001a8240670f80006d5213232d800038e00bc2e306203c5906e32f15e42c903ce4961d304528c8461280008f68aa20001014000000000000000000000067a1624de909885e97d607e9d7439b000000007d432509be3258db670417244f916281e40cf6320055a36a08786ca0ac01af00008dfa07a89080008fb238e84c16620000fcc57a1a8a8f391c000000008cfa35626797444369320000063840580000000f4281080002c714820cd172a0000000000000066f0ac600000004fa19ca4e886720000dbc00011cc3b2000046105fe00016762fa00000002388000119810195464f5166611d197836c9c5658e1ba619a8fee5c200c46a200de19690ec44c93ce2b1041229715aa7a7121488500001200f6a1e30000000010e000136a359a03a01f211c0168390727819225e943e255986434a99be5d91d600001702095824005a15ec1d809f2494a3d610e0c884e7856c18200a03e0812c1591daa171831428407f236e80706fb926473a171a0b30db07371436000165668f80004db8eb43cc030c1cb002017d909261e91b8761181600021ae184038451e937e0e70aec59a0b8654f800071f80007ff15e00000cf80000000000037a26200000001808316000085d9ed60b81af2000147800880007aa1ad2000000004c23ba0001f34507838e334238c18889182d117283bf9ec614316e2135119c7d980925a284f2242801e38890743551c447d5073625c1db25b990122629d0424590ae23d80005319db04f309e65261da46c89900000152e00003ac0d680004a7800000000006c080001260180230000000000000ab800018a0dd2296800029e8000000000000000004c71df656794620b19bce83e933253b84b22869d1245e8d30762921072d1dea4881234602800085a8f806ce1b784538c527298df200019da81c0c98000000023f000008f167003da4001aa17ec00014da6b404fc6c692281ef0d003ff86606c416d60e81efc66010228318b3615e1c76342197a288931a2d7a26a7c9927679a96223ad987047885d00628bbe7888152524013868c1b0620a1b4435c161e8f40f007d00d4c59f184038014025af223e6d092947b385e232981f674584f679f0bf000a8c565dd0000271823e00022de000000001880004d78efa44503562e702ba8680d94556a3506a
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8bf845cf624400917908b9ec48800333188735891002c3f43eeab1220048be87dd1624400187eebba2c4880030f1d774589100061fba8e8b122000c3c751d162440251bd0fb9ac48800317dd773589100062e3aee6b122000c9f74dcd6244001938e9b9ac48800317dd473589100062e3a8e6b122000c9f741cd6244001938e839ac488003331cf725891000c7d43ee0b12200087f855d9524400117f08bb2a4880122f21176549100046fc1aeca9220128dc835d952440070f90eb2aa48800a3ea1b70549100043fc2aeca12200587c855d9424400117f08bb2848800237e0d76509100946e41aeca1220038bc87591424400755904b2284880063da1b715091001c6f41ced99220008df8758f324400759904b1e64880063d21971cc9100147c432e1992200087f855d9324400b0f90abb264880022fe11764c9100245e422ec99220008df835d932440011df04bb2648800237a1e634c91001c6e43ac69922003acc8258d32440052e90eaa2a2880171d1d95454510014eac1eea98a2050d5753dd531440033e501baa62881435c143754c51000c7a432ea98a20079b4845d5314412936d0fba262880032d1db744c5100065a3b0e898a2007d947490d31440017a30121a628800a7521d434c51003eca3a28698a2000de220dc931440017a30199262880036c1d3704c51000cf9406ea90a204fd7050dd521440031e90cbaa4288003748c3734851000c7a432e690a20079b4845cd21440053c90ea124288002b9219424851000cdc43aa8a022004cb87655140440013e10ea8a8088003cc551515011003dd842262a022000fa14248540440e72f50fbaa60880031e1db754c1100063c3b0ea98220019d983dd130440053e503ba2608813b6c107744c1100147c432e89822006978855d1304400dab0eb29a6088002f4606534c11000cec43aa69822000de221dc930440017a30399260880035c1d7714c110036b83aaa29822001af0864c530440059e0ec98a60881435c1d5314c110275d8422629822012ed0634c530440037a10e98a608800b7421d314c11000de9432629822001bd0864c5304403dda10c98a608804bb4dd9314c110016e93b2629822002dd0764c53044019da0ec98a6088002f4e15314c110005e8c2a629822000f53754c530440a1ba4ea98a6088143741d5314c110007a83aa629822050d50754c53044001f270898a608813af4a11314c110275e8422629822000f90844c5304409d7210898a608800374dd1314c110006e8ba2629822000bd3824c53044001ba6e498a608813f5c1d5214c110005e8c1a4298220029f281dd1204409bb6083ba2408800a3e2197448110006e918ee690220028f8865cd204400d2f10ab9a40880067a21d524811000574432a49022000f6152545204409b7610898a4088003745cd3148110
  | 1 => 0x8ec3a2629800387194744c5300764e3a6c898a60028dc87591314c0434b90ab22629803b271d1644c5304972a32ee298a6000e5465d85314c001b30e9b8262980161fa1776485300043ec2eec90a60008de869cd214c0031b90cb9a429803a6721173485302363d3b6cb9826046e5b63d97304c00b8f4ec32e609804b74cc571cc13037dcc4226398260008bf845c7654800917908b8eca9000297a0e51d95200062e328e6b2a4000c5f751cd65480019b0e7b82ca9004a37a0e76551200046ec1cecaa240008df835d954480251b906bb2a8900023de0576551200147a40aecaa240008fb805d954480090fd0fb2aa8900162f21d64551200062fb28e6aa240bac5c651cd54480018baeba9ec690002b360b53d8d200054ec20a7b1a4000ad9808c763480015b30018ec6900161fa1f7558d200062e3aee6b1a4000c7875dc163480011bf0eb18c690002972156318d200946e41aea31a40008bf845c4634800917908b88c6900029760f6594d200043fc2aeca9a40008df835d953480011f700bb2a6900021fe157690d2002c3e42aed21a40128dc835da43480010ff0abb286900161f2157650d200047bc0aeca1a40028f4815d943480091bd0fb1a86900171b1d95454920005a641aa8a924005c6c7694d52480011bf06baec29004a3720d75d852000c7c402ebb0a40028de839db31480011bf0eb1e62900969721563cc5200245f424ec98a40008bd849d931480011bd0f31a629000a3721d634c52010d2e42ac698a4000a758194b654417b8eeebb8aca8804a37a0e76551100046ec1cecaa220008df835d954440251b906bb2a8880023be09765511001c76412ecaa2200487e87d95544400b17d0fb22a88800317d9473551105d62e328e6aa22000c9f641cd544416b938c839aa8882f36510473551105deac280e6aa220018f686dc554440018eecbb8aa88800a3ea1b705511002c3f43eeab1a20048be87dd1634400187eebba2c6880030f1d77458d100061fba8e8b1a2000c3c751d163440071dd0fb92c6880031bdd77258d10006363aee4b1a2000caf74dc96344001958e9b92c6880031bdd47258d10006363a8e4b1a2000caf741c96344001958e8392c68800333dcc7258d100046fc3ac631a2000acc8258c634400117f08bb4a6880122f2117694d100052ec1ecb29a20018f4865c653440018eecab8ca68801e6d2117194d100147c432e129a2000c7b655c253440010ff0abb2a6880022fe117654d100245e422eca9a20008ef825d953440071d904bb2a68800a3ea1b7054d100043fc2aed21a200587c855da43440031e90cb8c868800a3e2197090d10034bc42ae121a200087f855d9434400b0f90abb286880022fe117650d1000477c12eca1a20038ec825d943440031ed0db8a86880021fe1573d891002c3e42ae7b122000
  | 2 => 0x262d95302352ec1ee9b2a6000c3d741d3654c0010fd0e21eca9803e1f61c43d95300051f424e5b2a6000a3d849cb654c0014bd06396ca9811a9760c72d95300043f43885b2a600087d8710b654c08d0fd0f196ca980021f61e32d95300051f42465b2a6000a3d848cb654c00147f08b8eca980028f21171d95300052f418e3b2a6046a5d831c7654c08d4f50038eca980029e60071d95300043f43883b2a600087d87107654c0014bd0620eca980029760c41d95300053741083b2a6000a6d82107654c08d4f50020eca980029e60041d95302353d40063b2a600087e87087654c0010fb0e10eca980028fa1021d95300051ec2043b2a6000a5e83087654c0014bb0610eca9811a9ea0021d95300053cc0043b2a60c2c5f75dcd654c0014dd05320ca980029b60a64195300070e3268632a6073b5a80d0c654c0012bb0e218ca980028fa1262195300051ec24c432a60c1a5d83984654c0014f301308ca9811b175cf65d91300070fa1ecbb2260bac5e73197644c0e78bae632ec8980021fa1f65591300043f438cab2260c0c5f73195644c00b0fd0fbaac898003171d773591300043fc2aecaa260008df835d9544c0251b9063b2a89800327d0c76551300243f43ecaaa260058bc87591544c0031bd0db9aa89800317d9773551305ce2e32ee6aa26000c5f651cd544c1758b8ca39aa898087171957194d30074ce422e329a6046c7870d95534c00b8b8edbaaa69811b561c37554d302362e3b6caa9a600e95c87551534c0014b90caa2a698017171d95454d300043f43ecab12600087e87195624c17f8bee632ac49800e1fa1f65549300062e3b4a6a92600587e85dd9424c0010fb0bbb2849800e2fa1f645093000c6f436e6a126000c5c65dcd424c0018b8ca39a84980123ba1f62509300046f436eb99260bec5e76197324c0018f0cbb82649800637219754c93000cec402ea9926046c5c76d95324c001c98c5b2a64981cf171d8654c93039e3c380cbb0a60028dc835d7614c0010fd0fb2ac2980030f1d3655853000636396cab0a600087e87195614c001878e832ac2980031b1c865585300061fb2ee8b0a6000c3c65dd1614c0018decbb92c2980031b19772585300143f43ecaa8a600587e85dd9414c0010fb0bbb2829800637a1b73505300062e32ee6a0a60019da80dcd414c0018b8ca39a82980971719775cc53012c6e432eb98a6025a5e86d97314c01d1bb0fb2662980969721564cc5300061e3a6ca98a6000e5431d95314c00187ecbba262980030f197744c530006cc186e898a6021c5c65dd5314c0031b90cbaa629803a67211754c53010d2f436ca98a6046c5c76d95314c001a38e9b2a629800395187654c53039e2e3b0ca98a6000d1c74195314c01d33d0fba262980ff271db744c5300070e32ee898a6000d9870dd1314c12993
  | 3 => 0x1b22420587c855c3644840153d07206c8908032719073591210064fba0e6b224200cd473dc564484251bd073b2a8908023760e76551210046fc1aecaa242128dc835d954484011ef02bb2a8908023ee01765512100c7c402ecaa2420487c87595544840b17d0fb22a89080327d9073551215ae4e320e6aa24200a5d8510f63484015ab02186c6908122fa1f7458d210064e3a6e6b1a4200cb474dc563484011bf0eb18c690802a72116318d210946e41ae831a420087f855c0634840b0f90ab80c6908022fe117694d210245e422ed29a42128dc835da534840117f08bb2a6908122f2117654d210047dc02eca9a42018f8805d9534840b1bd0fb1aa6908022fe117650d210046fc1aeca1a42008f7815d94348409958ecaa28490802e320d54509210055743486a124204cac7690d42484011bf06ba6c09084a3720d74d812100c7a40ae9b024200a5d8510f63540014bb0b196c6a8002a7a1232d8d500046fc3ac631aa0c4a5f8558c63540014bb0b190c6a8002a7a123218d500043fc2aed21aa00387c855cf62540051b906bb662a80122fa12764c5500045ec24ec98aa0028de87d8d3154001938e9b1a62a800ab5a07634c5500064e3a0c698aa0048bc845c765500018b8ca39acaa030f0fdd774595400062fba8e6b2a8000c5f521cd655000193e8439acaa00031794073595400062e280e6b2a80b9c9c76dcd5450175938ec39aa8a0003175d753d8d400054ec26a7b1a8000e1d54d4f635000153b0829ec6a000237e1d6318d400052e42ac631a80128dc835d463500014bb07b2ca6a00021fe1573d894002c3e42ae7b1280038bc845cf62500070f90eb2aa4a00029720d655494000c5e432eaa1280038bc87595425000153906b2a84a000eab209655094001d57436c4a1280008df835d761500251b906baec2a000f2b1c942d85400061e3b2a8a8a80028de839db3150009179083b262a00062fa1b744c540006563b28490a80b78df835d954cc0031b906bb2a99804a1f21d65553300962e39acaaa660128bc8759154cc02733908b8ca79804a5721d5454f3000c6f41eeca96600387e87d9552cc0018beed29aa59811b561c25354b3000c6e41aeca1660008f7815d942cc0051e902bb2859800e2fa1f6450b3001d57416c8a1660008df865d532cc0033b100baa659800a3760f755873000c6f41eeca8e60018dc835d941cc0431bb0dbaa639808717997754c73009cce422ea98e601399e87dd131cc027938e9b22639804e3721d644c73009e4e3a2c898e60018de83dd921cc0011bf0cb9a439804e6721173487300061eba4a9b2a6000a5d8394b654c00117f08b8eca980122f21171d95300052ec1ca3b2a6000a6e82993654c0014db05326ca982e7179db43d9530235ad40687b2a600095e8710f654c00147d09316ca980028f61
  | 4 => 0x2cc4011f700bb2a5988063e2017654b3101c3f43ecaa9662028de83dd942cc40717d0fb22859880eaba0b6450b311feca38c86a1662008df865d132cc4053a902ba265988063760f74583310052ec1ca1b2a62048be87dd1654c5938beebb9aca98803271d373595310061ebaea9b22620087f855c3644c40b0f90ab86c898802aba0a65d913100556c14cbb22623fa9e86d4f644c56f93ceda9ec89880387d9753d91311fdcb40ea7b22620099e8714f644c40147d0b316c8988028f61662d91311fd4ec1eebb226200c3d751d7644c40117d0e29ec8988822f61c53d91310051f42ce5b226200a3d859cb644c40195ee5396c898802a7a0c72d91311fd4ec18e5b2262008be8714b644c40117b0e296c8988fe2fa1e32d91310045ec3c65b226200a3e858cb644c40147b0b196c8988028fe1570d91310051e42ae1b226200a9e831c3644c47f53b06386c8988feada0470d91310055ac08e1b2262008be87143644c40117b0e286c898802a7a0c50d91310054ec18a1b226200aae82143644c40155b04286c8988feada0450d91310055ac08a1b22623fab6810c3644c40117d0e106c8988022f61c20d91310051f42841b226200a3d85083644c40153d06106c898802a760c20d91311fd5b40841b226200ab581083644c40117b0f328c898802aba0a651913100556c14ca32262008bf87594644c59153f06b28c898ad6a720c65191314a54f436a63226200e1f65d4c644c401c38cba98c898a52e5a075319131004cec38a63226200a3e85988644c40147b0b310c898b1ea760e60191310055ac0cc032262008bf845d9544c4011bf06bb2a89880317d4c76551310243e43acaaa262058be87d91544c4051bd0db9aa898adf2719373551310064fb20e6aa262b5c9c641cd544c401c3ea7b24a69888717dcf6554d3110cae42ae121a620ec9c645c2434c47f968e3b228698a4ea7a1b7450d310264e3b6e8a1a623fd9471dd1434c40953d0db2286988ff271db6450d3110cce43aa8a1a6200a9c86551434c409938ecaa2869884f271937050d310045f43ec8b1262008be87191624c58d93ee6322c4988122fa1376549310045ec26eca92620387e87d95524c4051bd0db9aa49880317d9773549310064e326e6a926200c9c641cd524c40b1dd0fb12a49880e2fa1f645093101d57416c8a126200c9c7690d424c4011bd0dba66498b17279d864cc9310065a326e299262028dc865d1324c4053a902ba264988ff271db644c93100746316c89926294c9c76191324c425ba660b866298a532d1c464d813100c6e41ae9b02623f8bc86dd1604c40117d0fb22c0988030fdd764581310061e3aec8b026200cac72d91604c40117d0e322c0988030fdd464581310061e3a8c8b026200cac72191604c40195ec9b92c0988032b19372581310043fc2ae
  | 5 => 0x1003351cc715954200c7d43ee0b2a8400cdb73dc165508019b0e7b82caa10033cdc770595420067838ee0b2a8400cdb731c165508019b0e6382caa10033cdc4705954200678388e0b2a84b9c9c76dcd5450801b18e5b9aa8a12eb271d873551420064f430e6aa284cdc9d861cd545099ba3d0a39aa8a12d74761473551425ae4fb10e6aa284b5d8f621cd545099ba3ea439aa8a10034754873551420064f308e6aa28400c9c611cd5450801b1e4239aa8a100347940735514266e8e280e6aa28400d8c73dc95450897968c3b8aa8a100369c8771551420249ec2ee0aa28400a9c8355363508018baeba9ec6a1002a761353d8d420070eaa6a7b1a8400acd82d4f635080153b0829ec6a1002b660031d8d420046fc3ac631a8400ad48158c63508251b906ba8c6a100e2fa1b7454d4201cd7416e8a9a840493c87551535080717d0dbac86a12d667a0f7590d4201cd7416eb21a842e8bd87d8e435080735f0eb9486a100e6ba097190d420049fc2ae121a84008df835d761508251b906baec2a10023ee0175d854200c7c402ebb0a8400c7575d47615080156b09a8ec2a100335184735854202e1f3aaa9b0284abe3850553605080157309a86c0a100e3720d76553320943e43acaaa664128bc8759154cc80117f08b8eca990122f21171d95320052ec1ca1b2a64ccc5f75dcd654c8031f50fb82ca990031edd470595320066db98e0b2a640087f855c3644c80b0f90ab86c89900a3da1f71591320065bba0e2b226400cd7731c5644c8011bf06bb2a8990023de0576551320147a40aecaa264008fb805d9544c8031f100bb2a8990121f21d65551322553c402caaa264058bc87591544c89756902b22a89900e37a1b735513201ce7416e6aa264bac5e651cd544c96b93cc839aa89900e1fe1d6594d3258d2fc1acb29a6446a7880596534c80717f0eb2486990fead2056490d320047dc02ebb0a64018f8805d7614c8011ef02ba6c09900a3d20574d81320243e42ae1b22a200c9c641cd645456f8b8edb9aa8a8803551c773551515ae2e3b0e6aa2a200a5d85d0f6354401c3aa9a1ec6a88029761443d8d510046fc3ac631aa200a9c8458c635440117f08b9ec4a88122f21173d89510143e432eaa12a2008df835d360544251b906ba6c0a8b2f0fdd774595410064fba0e6b2a8200c5f521cd655040193e8439acaa08032790473595410064e208e6b2a8200c5d75d4f635040153b0829ec6a080297a1632d8d410046fc3ac631a82caa9f8458c63504251b906ba8c6a080297a163218d410054ec246431a82008bf845da53504070f90eb2aa4a08029720d655494101d36412caa9282038bc87595425040153906b2a84a080a3720d76553310943e43acaaa662128bc8759154cc425938e6b22a998896572157090f31094ce43aa8a1e62028dc835d95
  | 6 => 0x46ec384231aa8baa5e8508463550014bb0a108c6aa2d6a7a102118d540054ec204231aa800ada8008463550015b300108c6aa2ea972167018d5468d2fc2ae031aa800c5d755c063551a34bf0f280c6aa0029761e5018d546af0f3a4a031aa8bae1d7494063550014bb05280c6aa35787d0a5018d540070f20ca031aa8d5e1c419406355175cb501280c6aa2ea97a172018d540052ec2e4031aa8b5a9e84c80635500153b09900c6aa2ea972162018d540946f4384031aa8008dd8708063551754bd0a100c6aa002976142018d545ad4f4204031aa800a9d8408063550015ad02100c6aa002b56042018d545d52f42e2031aa800a5d85c4063551a9d2883880c6aa2d6a7a121018d540054ec242031aa8d3e585084063550251bd0e080c6aa0023761c1018d540046f43ec6b12a800cd471d8d62550019b0e1b1ac4aa00237a1c63589540066a388c6b12a800cd87018d62550019aec7b8ac4aa0033518f71589540066db1ee0b12a800cd863dc1625517393ae9b1ec2aa2d7279d063d85545d64eba0c7b0aa800a7585c8761550011bd0fb1ac2aa00237a1c63585546964fba0c6b0aa8b7c5d75d8f6055001cb4a1b1ec0aa2eb179d463d81545ae2eba8c7b02a8008de87d8d60550011bd0e31ac0aa34717dd463581540068fa9ee8b0ca6048be87dd16194c0187ea5ba2c32984a37a0f74582535be2e3b6e6aa2a612c5c761cd5454c0987ce8aa6c2a9ae637e0d74d81535ae4f39c83b2c86bac5e739436590c018f2e1286cb2184a37a0f755864302c3f43eeab048600c3f42dd56090c018f2e1286caa1b4317dd773595435ce4e3b6e6aa28612c9c761cd5450c0187ecbba2a6a184a4f21d5454d430951e432a8a9a8612b1c835515350d6f1bf06baec2a18170f9d554d81435be2e3b6e6aa2a400d4c72dcd545496b8b8ec39aa8a900317a18735515267e2ec30e6aa2a4cfd1e841cd5454975a3b0839aa8a92eb17d8873551525d6a7b10e6aa2a4cfd1f421cd5454801a3c8239aa8a933f4710473551520062f300e6aa2a400c5c601cd5454801a9e4039aa8a9003531cf725515202c9ec26e2aa2a44ac7860dc15454801ad641b82a8a90029720d54d8d520052ec2e87b1aa400e1d54d0f63548014bb0a21ec6a90029761630d8d520056ac0861b1aa4008df8758c63548015b100b18c6a904b2710d7418d5217c3ec3ec729aa42fa5d87d8e53548018bb0fb1ca6a90024fe117194d5201c3f436eb21aa4ba95e83dd643548072dd05bac86a900e1fa1b7550d5202c9e43aa8a1aa404c3e745536154965c6882aa6c2a90029d61741d85520046fc1ae9b02a4128dc835d360548011ef02ba6c0a900a3d20574d81520053cc2e81b02a400cd8601cd605499d87eebba2caa100a3da1f71595420066bb9ee2b2a8400cd473dc565508019aee638acaa
  | 7 => 0x400001000000000008100000040000700400400006016004028000000100a00500e0000100200c0200400902c01c0100200604c0400500e0100000402200c02003000018018030000000000d00202c0980300801c0001100a000000000220000180c0000041180100a0000180101a0000100000c000068090060000000105c000078030020080b80200000c000000000040000001003801000000008000010060140080900a01001001018000010000040000100000c004020010080000101400800403800006008000110000000000500200c078000200200380000c00400801004060018000000000200802200c00805002098058000000080280002801c0100000400801801004000020000020000500100803801804000000000000060000000900e00400003000078000010000000080200200000002000004010000000080100a00c000010010020000000000008c0000201403c03000000008000000000281380000603c0200800000c00802002018000040100100400000200404802000000038040040100581d0000040980a0040000000c00000a5d858cb63550014bb0b18ec6aa002b6a0031d8d540056cc0063b1aa800ad6810c363550015ab02186c6aa002b6a0261d8d540056cc04c3b1aa800ad68198363550015ab03306c6aa00333dca72d8d545cd2f428e5b1aa8b7a5d851cb635516f53d08396c6aa2e6a761072d8d545cd4ec26e3b1aa800ada809c763550015b30138ec6aa2e697a1471d8d545bd2ec28e3b1aa8008de8708763550011bb0e10ec6aa2e697a1421d8d540052ec2843b1aa8b7a9e84087635500153b0810ec6aa002b6a0021d8d540056cc0043b1aa8b7a5d85dc363550015ad03386c6aa002b560670d8d545bd4f420e1b1aa8b9a9d841c363550011bd0e106c6aa0023761c20d8d545cd2f42841b1aa800a5d85083635516f53d08106c6aa002a761020d8d540056b40841b1aa800ad58108363550011bd0e086c6aa0023761c10d8d540046fc3ac631aa812ccc325c863550014bb0b190c6aa002a76123218d540261ebac8231aa800a9d83904635500b87ae9280c6aa0029760e5018d540952e42cec31aa812a9c849d8635519f4bb0b310c6aa336a76126218d540056d404c231aa800ad9809846355001d28c3208c6aa002b5a066018d540056ac0cc031aa800e586094063551754bd0b390c6aa33e976167218d545ad4f424e431aa8cda9d849c86355025998e4b90c6aa2d6a72127118d546954fc22e231aa800c9d745c463551a553f0f208c6aa002a761e4118d546b70f3ac8231aa8b5e1d75904635500153b05208c6aa35b87d4a4118d545af4b40c8231aa8d6e1c5090463551754bd0b908c6aa002976172118d545ad4f4264231aa800a9d84c84635516b53909108c6aa04a37a1c2118d540
  | 8 => 0x11c1739269900d182580c02010004387f18d8c70cd0f90449f61590348860cc00016692180000018e0000000150291209958d49b28ba07389380000011e0ac80000000000000007c03188401100005c96405782797000e8000001210000028000001af8f38471a1000000000079a0910588a0000bf0001608a900016d1c697119e9809481600b287e0000f98a50288611e405180f95d1ae8c89fd00002d8b89490cb9cc00001216f83b80006c85e80000000000000016c16a9661b797a80004f9ba9e113b9f98cf1421d483d9e000a8c28000e40000000000001230558001ff0a60620890001e98000af1919730db15f9430c380006e1ef0f29150001560000000240000768c00000000001c700008395f0ea9de80314280b80001611a91a0001220fc8001188000c615d80019ca040001d611608c0220001f59bc0000000f10eb8000710d014484a89c8fe80001b0131011eb0a880000000008f8ef80005e02f9338099c80408b80ff9831580aa90c8950980bb8001f788b1db20b0d814f08d80004801f92880004a1d393300000010480000010c0000e18001638000fb94d81480000004780000000006418e98b8308329651038000000000f800f0ad9698001751910db8960b080015891718705da0189d00010b8fd9888001b70b90001c21d800000000003b1248a10e017c89b9d50508750708001db8002088cb16782701592011388980000000007b98a15c9e082688007d8000000000c302e9da80000200020e8002020001e209f0a40cf9c398c8000000000000001b107311b80000000001a8cd8000ab00000007a12d80002100000000013d8000001400b480009117700000001418c1088e49e502080017484f0001de08480007788e12980009a80005295e0018000000ee03f0c495c0c79469890000880000000d297800000006a9e70588e38468590a590e83700000000003e0b38000dc9d19881500c50001988001030001f201920006015b8000000001921bca058e98001fb82987d0000000e300006707c91d05701b8d79081f41628818001938001ed1380920808de98f0000000001858001009e189d8000000000000001e29c50908c58000d20000a70000001659878001090690000000000000001340000000000df1dd9ef9a39680d88002078000000490000001df00009f9d00000000f19a88000000000ed0d31ea1b99e58000378fa9419c09e31f68000000000000001c314e0091280000000000000000001598050000000000000551510000000d994984587f9a80bd8000820001a680000003a1b80e600000012c00000000018280012715200000080702a00000000004074000040000080100b004000098010000140101a008010000010020040001b00000c0400200e0040100000601401001004010010000000440100000000
  | 9 => 0x198001980000f08000fd0e58001548000000000631b08af8d580010a1309579a782288f00018b0000ac0000e88749fc80000018100014703886395580020097799280002c00000009312586696d87411f19492d00e03d0000bb1410000001c100000011d80000000010e00c8bd1708000000001370000380000f593e81d1dd00014b9b600000005a83c1068001aa9140000000da0001fe9540000001dc0000a80000b71f18f49ff83ea029bb1868059aa1800d692794a19b0d61d88000001ad07280000005d0629cf8000428001d711100013e1f30a68001a616b8f61999cc9239a21260001fe0000ca8000001f88568e900000005c0000001388000000a390a8581a08ec00000012f81d91f8f71741f38038001bb80000000a0b180014797980000014a90993482c80011b1bd80013299e0000888879131ee12e16881e0000000001379728001f814f8998a18001630da8ba8ae9d900001700013a1fa0990538540000001e81c40660001b31d78001c600020d1c29ce8d101c0828338c20549d40d50000000060958000700000000940000000928b31cd86f06e94c92c85219780018d00005600002380000000010f8000000b98ce02800000011189680002a8000b200000016180018408b94393b02b1350850b69761a292e84899c01881ca0e0100c916a1941e618fa0394419a1178000001250001e38301ee9159ca0df84c1968b79b39c903f9a913c0000000001f28000901148000410978000000dc1cb8c10ea09b0049b413215a8069509ca8001d59769ad8e29d09061c19f480000014080704420995287a9d31a01050178ab82482d184a060648a01bf9898450608e81a496f2048fc04d8250dd16900005100013004e1bd1ac19080004b82a0d39530bf80b1f11ec13d00008c86d1788000001758000fe17e9f70001168001359790a31a982f1a593989e9ce2050000360431b59ed81810b1bf12b8498e21950e78771450ce80000000800000011000017b00013a85b8000001cd02b8001108000720000001488e700008e88119708698509a1079538001a187b0000ff00000000000000000018615a0bc1670001610f21eb80005f00003319f0310000001af0000000000000000001020000000001c791900016483915b2068001e4a0700000016c8618040e51e90ed92aa031718001ab8e08000000000d70078dd8ca06f91286c0a48b60001070001228001550001c98a286505983c8321f080011e89c01f14b0f00fa0341cf14c16b0ef0000698679f91ab19601399a8c400000006b8970fb1ac9a70b005f99f9838358918c19be0ec97d04600012f0000000000000f305a00019d0000000e68b40718bc85320c8000000000000858001c88169c58b58001360000f68c08001b00001568400260761fb10d8c69ba0419df99320820a16218a84d
  | 10 => 0x1458de0000000c99da0500001180d09be8000a790d0118d91cb17f0cc80008a8658780be0b51120790758f79820001d281e8000421f006b04c80000001a10f00014611c9a316e9c480007e9e882e13f8001570000001369e781097f9ec9d68be9b500014e84b0681d986d8f89029a41dc8000e112907899d86897b8000001f50000001ea8a98d40001818ee80000009888d17213ca0a9198010350f41d119913197a1e680000000000000013f1fa8230009d21fd80005b0f50128948ad0a20000000000a09b91fc14d20b8aa03680015e80020d9b880004e9ae12b17d88703aa0100000020f0000088c812a00000013100d17c13900000000020c0000000000001c017e1b18000830000b100000000003996e06a1040000ae0000000eb00d89e19b9b49518001a50001240000218000000001b20000001019b68000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x280091034006164018d93307069f043c88b000071d0000a880e140092e2801e3200001000c004002874800030c01410401458905d57018d5400417660601cd545480109d9818473551420068355182d4f635080148d9210473595415ac2725c86551434c56b88c7620d545092100513648501cd655017505c972195454d300044766074195314c00181e87197744c53000487660651d1314c17584c7620d5454920284d42558090d314409d99074602434c5100064c21d5454540440a195075606534c110274e42518194d30440a195075e15314c110274e4251854c530441b155297dd5314c110007141db754c53044001b1084dd5314c110006c4210754c530441af39298e11314c110006a421b844c53044001d1075e11314c110007441d4844c5304409d99084dd1314c11028554255744c5304409d990845d1314c110274e42518348530440a1550955cd3148110
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x8500000c000912688905d57018d5400403b53438cbba26298002311a9210754c530440018894c0ebc226298220009446a475211314c110
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x4111baa6075e11314c110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x3
  | 4 => 0x5
  | 5 => 0x6
  | 6 => 0x94e
  | 7 => 0x94d
  | 8 => 0x94b
  | 9 => 0x98a
  | 10 => 0x98d
  | 11 => 0x98e
  | 12 => 0x9ca
  | 13 => 0x9cb
  | 14 => 0x9cd
  | 15 => 0x9ce
  | 16 => 0x168a
  | 17 => 0x168b
  | 18 => 0x4
  | 19 => 0x168d
  | 20 => 0x168e
  | 21 => 0xa0a
  | 22 => 0xa0b
  | 23 => 0xa0e
  | 24 => 0xa4a
  | 25 => 0xa4b
  | 26 => 0xa4d
  | 27 => 0xb09
  | 28 => 0xb0d
  | 29 => 0xb0e
  | 30 => 0xb49
  | 31 => 0xb4b
  | 32 => 0xb4d
  | 33 => 0xb4e
  | 34 => 0x16c9
  | 35 => 0x16cb
  | 36 => 0x16cd
  | 37 => 0x16ce
  | 38 => 0xb89
  | 39 => 0xb8b
  | 40 => 0xb8e
  | 41 => 0xbc9
  | 42 => 0xbcb
  | 43 => 0xbcd
  | 44 => 0xcc9
  | 45 => 0xcca
  | 46 => 0xccd
  | 47 => 0xcce
  | 48 => 0x1709
  | 49 => 0x170a
  | 50 => 0x170d
  | 51 => 0x170e
  | 52 => 0xd09
  | 53 => 0xd0a
  | 54 => 0xd0e
  | 55 => 0xd49
  | 56 => 0xd4a
  | 57 => 0xd4d
  | 58 => 0xe89
  | 59 => 0xe8a
  | 60 => 0xe8b
  | 61 => 0xe8e
  | 62 => 0x1789
  | 63 => 0x178a
  | 64 => 0x178b
  | 65 => 0x178e
  | 66 => 0xec9
  | 67 => 0xeca
  | 68 => 0xecb
  | 69 => 0xecd
  | 70 => 0x17c9
  | 71 => 0x17ca
  | 72 => 0x17cb
  | 73 => 0x17cd
  | 74 => 0x1049
  | 75 => 0x104a
  | 76 => 0x104b
  | 77 => 0x98955
  | 78 => 0x9c955
  | 79 => 0xb0956
  | 80 => 0xb4956
  | 81 => 0x1549
  | 82 => 0x1409
  | 83 => 0x150a
  | 84 => 0x128a
  | 85 => 0x249
  | 86 => 0xca
  | 87 => 0x1449
  | 88 => 0x12ca
  | 89 => 0x1849
  | 90 => 0x1489
  | 91 => 0x180a
  | 92 => 0x130a
  | 93 => 0x19c9
  | 94 => 0x14c9
  | 95 => 0x198a
  | 96 => 0x134a
  | 97 => 0x138b
  | 98 => 0x124b
  | 99 => 0x3c9
  | 100 => 0xcb
  | 101 => 0x15c9
  | 102 => 0x12cb
  | 103 => 0x1889
  | 104 => 0x1609
  | 105 => 0x180b
  | 106 => 0x130b
  | 107 => 0x1a09
  | 108 => 0x1649
  | 109 => 0x198b
  | 110 => 0x134b
  | 111 => 0x1689d5
  | 112 => 0x18c9
  | 113 => 0x589
  | 114 => 0x12ce
  | 115 => 0x5c9
  | 116 => 0x1a49
  | 117 => 0xce
  | 118 => 0x138d
  | 119 => 0x124d
  | 120 => 0x150d
  | 121 => 0x128d
  | 122 => 0xcd
  | 123 => 0x12cd
  | 124 => 0x1a89
  | 125 => 0x1949
  | 126 => 0x198d
  | 127 => 0x134d
  | 128 => 0x138e
  | 129 => 0x124e
  | 130 => 0x150e
  | 131 => 0x128e
  | 132 => 0x180e
  | 133 => 0x130e
  | 134 => 0x3ca
  | 135 => 0x24b
  | 136 => 0x15ca
  | 137 => 0x144b
  | 138 => 0x188a
  | 139 => 0x160a
  | 140 => 0x184b
  | 141 => 0x148b
  | 142 => 0x1a0a
  | 143 => 0x164a
  | 144 => 0x19cb
  | 145 => 0x14cb
  | 146 => 0x16cb56
  | 147 => 0x144d
  | 148 => 0x58a
  | 149 => 0x1a4a
  | 150 => 0x5ca
  | 151 => 0x18ca
  | 152 => 0x24d
  | 153 => 0x154d
  | 154 => 0x140d
  | 155 => 0x1a8a
  | 156 => 0x194a
  | 157 => 0x19cd
  | 158 => 0x14cd
  | 159 => 0x154e
  | 160 => 0x140e
  | 161 => 0x24e
  | 162 => 0x144e
  | 163 => 0x184e
  | 164 => 0x148e
  | 165 => 0x58b
  | 166 => 0x5cb
  | 167 => 0x18cb
  | 168 => 0x1a4b
  | 169 => 0x3cd
  | 170 => 0x15cd
  | 171 => 0x104d11
  | 172 => 0x1a8b
  | 173 => 0x194b
  | 174 => 0x1a0d
  | 175 => 0x164d
  | 176 => 0x3ce
  | 177 => 0x15ce
  | 178 => 0x104d52
  | 179 => 0x188e
  | 180 => 0x160e
  | 181 => 0x5cd
  | 182 => 0x104e91
  | 183 => 0x1a4d
  | 184 => 0x104ed2
  | 185 => 0x18ce
  | 186 => 0x58e
  | 187 => 0x58956
  | 188 => 0x5c955
  | 189 => 0x19d4d1
  | 190 => 0x5c3d1
  | 191 => 0x5d5d1
  | 192 => 0x5d8d1
  | 193 => 0x5cb51
  | 194 => 0x1a57d1
  | 195 => 0x1a9951
  | 196 => 0x5d7d1
  | 197 => 0x583d2
  | 198 => 0x595d2
  | 199 => 0x589d2
  | 200 => 0x59a52
  | 201 => 0x1a57d2
  | 202 => 0x59792
  | 203 => 0x1a9952
  | 204 => 0x1a57d3
  | 205 => 0x58d16
  | 206 => 0x1a9953
  | 207 => 0x5cd55
  | 208 => 0x1a57d5
  | 209 => 0x5d355
  | 210 => 0x59496
  | 211 => 0x124596
  | 212 => 0x1385d5
  | 213 => 0x1345d5
  | 214 => 0x148596
  | 215 => 0x9c592
  | 216 => 0xb45d1
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 1798
  | 6 => 4615
  | 5 => 1055
  | 4 => 33
  | 3 => 5
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
  | 8 => packedAt gbK8 (1700+((h/20+packedAt gbK8 (1560+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (73714+((h/599+packedAt gbK7 (66526+(h % 599)*12) 12) % 3820)*12) 12
  | 6 => packedAt gbK6 (241514+((h/1538+packedAt gbK6 (221520+(h % 1538)*13) 13) % 5539)*14) 14
  | 5 => packedAt gbK5 (66106+((h/351+packedAt gbK5 (62245+(h % 351)*11) 11) % 1532)*12) 12
  | 4 => packedAt gbK4 (2376+((h/11+packedAt gbK4 (2310+(h % 11)*6) 6) % 48)*7) 7
  | 3 => packedAt gbK3 (409+((h/1+packedAt gbK3 (405+(h % 1)*4) 4) % 10)*4) 4
  | 2 => packedAt gbK2 (93+((h/1+packedAt gbK2 (92+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x7fffc3e0f83fc3fc03c3fc07f14c467c4ef273
  | 1 => 0x87807c00ffc1fc3ffffc3ff802b079b0713f9c
  | 2 => 0xf8007fff0001ffc003fffffffcc381c381c3ff
  | 3 => 0x7ffffffe000003ffc0000f03fe03fe03e0
  | 4 => 0x7ffffffffffffc0000000ffc0003fffc00
  | 5 => 0xffff800000000000000000000ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0xa8740a0590ac05428e2641160044214467231
  | 1 => 0x830944002948441919662930201058b0501694
  | 2 => 0x5010194900012a80420892c684c1814181814a
  | 3 => 0x2226e72b5ac001093b32060cb02ee02fa03e0
  | 4 => 0x4044339cc631b322e00000830fec00032de800
  | 5 => 0x6478001804202203000003040ffb35e8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefeeafeece0e0feeefeeafeece0e0feeefeeafeece0e0feeefeeafeece0e0feeefeeafeece0e0feeefeeafeece0e0feeefeeafeece0e0feeefeeafeece0e0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36314
namespace PEqualNP.Outside.L_meta_36314
open PEqualNP.Outside.L_meta_36314.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs2_4_0 : Interval s2Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_32 : Interval s2Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 64 := (concat bs2_4_0 bs2_4_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 40 := (concat bs2_5_0 bs2_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 1 := bs2_6_0
theorem alls2 : ∀ k ≤ 6, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
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
theorem bs4_2_0 : Interval s4Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 3 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 21 := bs4_3_0
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
theorem bs4_4_96 : Interval s4Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 99 := (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 bs4_4_96))
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
theorem bs5_2_0 : Interval s5Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 3 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 21 := bs5_3_0
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
theorem bs5_4_96 : Interval s5Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 99 := (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 bs5_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 46 := (concat bs5_5_0 bs5_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 1 := bs5_6_0
theorem alls5 : ∀ k ≤ 6, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_2 i (by omega) hi
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
  · exact alls5_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 1 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 5 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 33 := (concat bgb_4_0 bgb_4_32)
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
theorem bgb_5_1024 : Interval gbAtlas 5 1024 31 := block_range (n:=31) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1055 := (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 bgb_5_224))) (concat (concat (concat bgb_5_256 bgb_5_288) (concat bgb_5_320 bgb_5_352)) (concat (concat bgb_5_384 bgb_5_416) (concat bgb_5_448 bgb_5_480)))) (concat (concat (concat (concat bgb_5_512 bgb_5_544) (concat bgb_5_576 bgb_5_608)) (concat (concat bgb_5_640 bgb_5_672) (concat bgb_5_704 bgb_5_736))) (concat (concat (concat bgb_5_768 bgb_5_800) (concat bgb_5_832 bgb_5_864)) (concat (concat bgb_5_896 bgb_5_928) (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024))))))
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
theorem bgb_6_4608 : Interval gbAtlas 6 4608 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 4615 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)))) (concat (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)) (concat (concat bgb_6_416 bgb_6_448) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))))) (concat (concat (concat (concat bgb_6_576 bgb_6_608) (concat bgb_6_640 bgb_6_672)) (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 (concat bgb_6_800 bgb_6_832)))) (concat (concat (concat bgb_6_864 bgb_6_896) (concat bgb_6_928 bgb_6_960)) (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120)))))) (concat (concat (concat (concat (concat bgb_6_1152 bgb_6_1184) (concat bgb_6_1216 bgb_6_1248)) (concat (concat bgb_6_1280 bgb_6_1312) (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408)))) (concat (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 bgb_6_1536)) (concat (concat bgb_6_1568 bgb_6_1600) (concat bgb_6_1632 (concat bgb_6_1664 bgb_6_1696))))) (concat (concat (concat (concat bgb_6_1728 bgb_6_1760) (concat bgb_6_1792 bgb_6_1824)) (concat (concat bgb_6_1856 bgb_6_1888) (concat bgb_6_1920 (concat bgb_6_1952 bgb_6_1984)))) (concat (concat (concat bgb_6_2016 bgb_6_2048) (concat bgb_6_2080 bgb_6_2112)) (concat (concat bgb_6_2144 bgb_6_2176) (concat bgb_6_2208 (concat bgb_6_2240 bgb_6_2272))))))) (concat (concat (concat (concat (concat (concat bgb_6_2304 bgb_6_2336) (concat bgb_6_2368 bgb_6_2400)) (concat (concat bgb_6_2432 bgb_6_2464) (concat bgb_6_2496 (concat bgb_6_2528 bgb_6_2560)))) (concat (concat (concat bgb_6_2592 bgb_6_2624) (concat bgb_6_2656 bgb_6_2688)) (concat (concat bgb_6_2720 bgb_6_2752) (concat bgb_6_2784 (concat bgb_6_2816 bgb_6_2848))))) (concat (concat (concat (concat bgb_6_2880 bgb_6_2912) (concat bgb_6_2944 bgb_6_2976)) (concat (concat bgb_6_3008 bgb_6_3040) (concat bgb_6_3072 (concat bgb_6_3104 bgb_6_3136)))) (concat (concat (concat bgb_6_3168 bgb_6_3200) (concat bgb_6_3232 bgb_6_3264)) (concat (concat bgb_6_3296 bgb_6_3328) (concat bgb_6_3360 (concat bgb_6_3392 bgb_6_3424)))))) (concat (concat (concat (concat (concat bgb_6_3456 bgb_6_3488) (concat bgb_6_3520 bgb_6_3552)) (concat (concat bgb_6_3584 bgb_6_3616) (concat bgb_6_3648 (concat bgb_6_3680 bgb_6_3712)))) (concat (concat (concat bgb_6_3744 bgb_6_3776) (concat bgb_6_3808 bgb_6_3840)) (concat (concat bgb_6_3872 bgb_6_3904) (concat bgb_6_3936 (concat bgb_6_3968 bgb_6_4000))))) (concat (concat (concat (concat bgb_6_4032 bgb_6_4064) (concat bgb_6_4096 bgb_6_4128)) (concat (concat bgb_6_4160 bgb_6_4192) (concat bgb_6_4224 (concat bgb_6_4256 bgb_6_4288)))) (concat (concat (concat bgb_6_4320 bgb_6_4352) (concat bgb_6_4384 (concat bgb_6_4416 bgb_6_4448))) (concat (concat bgb_6_4480 bgb_6_4512) (concat bgb_6_4544 (concat bgb_6_4576 bgb_6_4608))))))))
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
theorem bgb_7_1792 : Interval gbAtlas 7 1792 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1798 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat (concat bgb_7_96 bgb_7_128) (concat bgb_7_160 bgb_7_192))) (concat (concat bgb_7_224 (concat bgb_7_256 bgb_7_288)) (concat (concat bgb_7_320 bgb_7_352) (concat bgb_7_384 bgb_7_416)))) (concat (concat (concat bgb_7_448 (concat bgb_7_480 bgb_7_512)) (concat (concat bgb_7_544 bgb_7_576) (concat bgb_7_608 bgb_7_640))) (concat (concat bgb_7_672 (concat bgb_7_704 bgb_7_736)) (concat (concat bgb_7_768 bgb_7_800) (concat bgb_7_832 bgb_7_864))))) (concat (concat (concat (concat bgb_7_896 (concat bgb_7_928 bgb_7_960)) (concat (concat bgb_7_992 bgb_7_1024) (concat bgb_7_1056 bgb_7_1088))) (concat (concat bgb_7_1120 (concat bgb_7_1152 bgb_7_1184)) (concat (concat bgb_7_1216 bgb_7_1248) (concat bgb_7_1280 bgb_7_1312)))) (concat (concat (concat bgb_7_1344 (concat bgb_7_1376 bgb_7_1408)) (concat (concat bgb_7_1440 bgb_7_1472) (concat bgb_7_1504 bgb_7_1536))) (concat (concat (concat bgb_7_1568 bgb_7_1600) (concat bgb_7_1632 bgb_7_1664)) (concat (concat bgb_7_1696 bgb_7_1728) (concat bgb_7_1760 bgb_7_1792))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 24, 25),(inputs.getD 1 zero, 16, 18),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 34, 42),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefeeafeece0e0feeefeeafeece0e0feeefeeafeece0e0feeefeeafeece0e0feeefeeafeece0e0feeefeeafeece0e0feeefeeafeece0e0feeefeeafeece0e0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075690 * 2 ^ 32 + 4276936928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36314.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,1]⟩,⟨.and,[3,4]⟩,⟨.or,[5,7]⟩,⟨.and,[3,8]⟩,⟨.or,[2,4]⟩,⟨.and,[0,8]⟩,⟨.and,[6,10]⟩,⟨.or,[1,2]⟩,⟨.or,[9,12]⟩,⟨.and,[13,14]⟩,⟨.or,[11,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276936928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276936928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36314

open PEqualNP.Outside.L_meta_36314 in
theorem PEqualNP.Outside.L_meta_36314 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276936928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276936928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
