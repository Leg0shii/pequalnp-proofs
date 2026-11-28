import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_40297.Model
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
noncomputable def anyEq2 (m c d : Sig) (l : List Sig) : Bool :=
  @List.rec Sig (fun _ => Bool) false (fun v _ ih => eqF (masked d v) m || (eqF (masked d v) c || ih)) l
theorem anyEq2_eq (m c d : Sig) (l : List Sig) : anyEq2 m c d l = (anyEq m d l || anyEq c d l) := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change (eqF (masked d v) m || (eqF (masked d v) c || anyEq2 m c d vs)) =
      ((eqF (masked d v) m || anyEq m d vs) || (eqF (masked d v) c || anyEq c d vs))
    rw [ih]
    cases eqF (masked d v) m <;> cases eqF (masked d v) c <;> cases anyEq m d vs <;> cases anyEq c d vs <;> rfl
noncomputable def availF (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) : Bool :=
  eqF (masked d a) zero || eqF (masked d a) d ||
    cond u (anyEq2 (masked d a) (masked d (neg a)) d pool) (anyEq (masked d a) d pool)
theorem availF_eq (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :
    availF u d pool a = availableB u d pool a := by
  cases u
  · simp only [availF,cond_false,availableB,eqF_eq,anyEq_eq,Bool.false_and,Bool.or_false]
  · simp only [availF,cond_true,anyEq2_eq,availableB,eqF_eq,anyEq_eq,Bool.true_and,Bool.or_assoc]
noncomputable def memF (x : Sig) (l : List Sig) : Bool :=
  @List.rec Sig (fun _ => Bool) false (fun v _ ih => eqF x v || ih) l
theorem memF_eq (x : Sig) (l : List Sig) : memF x l = l.contains x := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change (eqF x v || memF x vs) = _
    rw [ih,eqF_eq,List.contains_cons]
noncomputable def subF (a b : List Sig) : Bool :=
  @List.rec Sig (fun _ => Bool) true (fun v _ ih => memF v b && ih) a
theorem subF_eq (a b : List Sig) : subF a b = a.all (fun x => b.contains x) := by
  induction a with
  | nil => rfl
  | cons v vs ih =>
    change (memF v b && subF vs b) = _
    rw [ih,memF_eq,List.all_cons]
noncomputable def sameWordsF (a b : List Sig) : Bool := subF a b && subF b a
theorem sameWordsF_eq (a b : List Sig) : sameWordsF a b = sameWords a b := by
  simp only [sameWordsF,sameWords,subF_eq]
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
    (links (keySet (choiceVal op::rest))).any (sameWordsF (choiceVal op::rest))

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,anyP_eq,sameWordsF_eq,Bool.or_eq_true,List.any_eq_true] at h
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
def M152 : Nat := 2^152-1
theorem not152 (x : Bits) : (~~~x).toNat = x.toNat ^^^ M152 := by
  rw [BitVec.not_def,BitVec.toNat_xor,BitVec.toNat_allOnes,Nat.xor_comm]
  rfl
def natBv (d x y : Nat) : Nat :=
  cond (Nat.beq d 0) (x &&& y) (cond (Nat.beq d 1) (x ||| y)
    (cond (Nat.beq d 2) (x &&& (y ^^^ M152)) ((x ^^^ M152) &&& y)))
theorem natBv_eq (d : Nat) (a b : Bits) : (bv d a b).toNat = natBv d a.toNat b.toNat := by
  match d with
  | 0 => simp [bv,natBv]
  | 1 => simp [bv,natBv]
  | 2 =>
    rw [show bv 2 a b = a &&& ~~~b from rfl,BitVec.toNat_and,not152]
    rfl
  | n+3 =>
    have e : bv (n+3) a b = ~~~a &&& b := by
      unfold bv
      rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]
    rw [e,BitVec.toNat_and,not152]
    rfl
def natCol (d : Bool) (x y : Nat) : Nat := cond d (x &&& (y ^^^ M152)) (x ^^^ y)
theorem natCol_eq (d : Bool) (s : Bits × Bits) : (column d s).toNat = natCol d s.1.toNat s.2.toNat := by
  cases d
  · rw [show column false s = s.1 ^^^ s.2 from rfl,BitVec.toNat_xor]
    rfl
  · rw [show column true s = s.1 &&& ~~~s.2 from rfl,BitVec.toNat_and,not152]
    rfl
def covFail (d : Bool) (t : Bits) (op : Nat) (a b : Decor) : Bool :=
  !(Nat.beq (t.toNat ||| natCol d (natBv op a.2.1.toNat b.2.1.toNat) (natBv op a.2.2.toNat b.2.2.toNat)) M152)
theorem covFail_eq (d : Bool) (t : Bits) (op : Nat) (a b : Decor) :
    covFail d t op a b = ((t ||| column d (dbin op a b).2) != BitVec.allOnes 152) := by
  have e : (t ||| column d (dbin op a b).2).toNat =
      t.toNat ||| natCol d (natBv op a.2.1.toNat b.2.1.toNat) (natBv op a.2.2.toNat b.2.2.toNat) := by
    rw [BitVec.toNat_or,natCol_eq]
    simp only [dbin,natBv_eq]
  unfold covFail
  rw [←e]
  generalize (t ||| column d (dbin op a b).2) = X
  by_cases h : X = BitVec.allOnes 152
  · subst h
    decide
  · have h3 : X.toNat ≠ M152 := fun q => h (BitVec.eq_of_toNat_eq (by rw [q,BitVec.toNat_allOnes]; rfl))
    have h4 : Nat.beq X.toNat M152 = false := by
      cases hb : Nat.beq X.toNat M152
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) h3
    rw [bne_iff_ne.mpr h,h4]
    rfl
noncomputable def allD (f : Decor → Bool) (l : List Decor) : Bool :=
  @List.rec Decor (fun _ => Bool) true (fun v _ ih => f v && ih) l
theorem allD_eq (f : Decor → Bool) (l : List Decor) : allD f l = l.all f := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change (f v && allD f vs) = _
    rw [ih,List.all_cons]
def opsAll (u : Bool) (f : Nat → Bool) : Bool := f 0 && (f 1 && cond u (f 2 && f 3) true)
theorem opsAll_eq (u : Bool) (f : Nat → Bool) : opsAll u f = (opsOf u).all f := by
  cases u <;> simp [opsAll,opsOf]
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
def quickPairN (c : NodeContext) (a b : Decor) (op : Nat) : Bool :=
  if Nat.blt c.1 c.2.1 then
    covFail (!c.2.2.2.1.2) (takeTwo c.2.2.2.1.1 (column (!c.2.2.2.1.2) a.2) (column (!c.2.2.2.1.2) b.2)) op a b
  else Nat.blt c.1 (c.2.1+1) &&
    (covFail (!c.2.2.2.1.2) (takeOne c.2.2.2.1.1 (column (!c.2.2.2.1.2) b.2)) op a b &&
     covFail (!c.2.2.2.1.2) (takeOne c.2.2.2.1.1 (column (!c.2.2.2.1.2) a.2)) op a b)
theorem quickPairN_eq (c : NodeContext) (a b : Decor) (op : Nat) :
    quickPairN c a b op = quickPair c a b op := by
  simp only [quickPairN,quickPair,covFail_eq]
noncomputable def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    allD (fun b => opsAll ctx.2.2.2.1.2 (fun op => quickPairN ctx a b op || testPair ctx a b op)) bs
noncomputable def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,allD_eq,opsAll_eq,quickPairN_eq,List.all_eq_true] at h
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


end PEqualNP.Outside.L_meta_40297.Model

namespace PEqualNP.Outside.L_meta_40297
open PEqualNP.Outside.L_meta_40297.Model
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

def SBf (j : Nat) : Nat := [8, 6, 5, 7, 8, 6].getD j 0

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

end PEqualNP.Outside.L_meta_40297

namespace PEqualNP.Outside.L_meta_40297
open PEqualNP.Outside.L_meta_40297.Model
def s0K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K6 : Nat → Nat
  | 0 => 0x400012400800c000004d0c92010023000002c0004fc41fd43fd40fc31fd10fd32fc32fe32fe31fd42fc10fe10fd21fd41fe42ff42bc40fc21fe30fe40ff31ff43fc30fe20ff10fc42fd20fe41dc31fe21de31ff40ff20fc40be40ff21fd31fc43ff30ff41fc20ff32fd30fe43
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x285bc53902f8a9195f94843f799465f7415077e83205f95320bfa9a217d54086fea0a1df54a20bf280417c53082faa221d754e10ee29a217d54442fca3a15fd5331ee994637e54107de8410df94840efa90637e52cc6fca4217dc4210efa84637c5350ad8a4884f55021afa9a437e50cc7bc63205f14c21efa1c637e520437c63205f94e42bf28465be42903bea6a0f70c410efa0863be52102fca1215f14931bfa92617d538877ca5205f94431bf2a44374514837c80905bd4910ef18843de520c7f040086f90840df18881bf52902fea299670c640be29281de430cb7e8621df54b30fc282837f51482fea2a15f94c20bea8e81bc40482f6a0a0df54843fb082217f54882fca6205f54420de18881de528c6fca9105f54d21bf288617e520cbbc6290df54e41ee21c63de510c6fca5205f94440bf28087f731842faa690778c932bf2a4635f53443bc8418f70c520df2a6617c53c82f8a7887dc8521f790041fa300c2f8a918f714831ef996617e5110fbc62205f94040bea9e215e510c6fca5a07b08620bea88813e54c82fea2a05fd4c20dea8881ec52443de8521774cb30dfaa2417d5090efca321ef94440be2a2657d53042f8a2a0678c440bf2a243bf425077c64205f15330be28285dc53507da4210fe50040dea1a83be51902fca6905f54f42af29841de314c3f240107754e10bea86857f524c7e863085f54241bfaa2617c5250efca6186f90330bf29083ee21882faa5a0778c831df200217c54c43bc63a05f94640ee19461dc428c6fca4885dd4530bf2a241be40083bc62185fd5221b7a9283bc51902f8a9905f94732bea98837d540cb7ea890df95321bea8687bc40cc37ea8985f94b41bf28441bc544437880105fd5010bf28c65de438cafaa1217d08610df990817d5310afaa3184fd5130bf28421be40c42f8a2985f94442be28a857e52cc3b863987ed0140bfaa043dc31082fca2086f95031f710841bc400437883205f54442aea9e857e540877aa32077d0631bf28683de31c86fca2107790e31eea1865bf42d06fea4885f54640de20621bc42106fca410f714d21ef28463dc53482fca8184f95021be282837d53087eea2986fd0a42ef190617d51842faa1196fcc640bf29e85d431842fca618f754f21fba8a41de318437a87a0efcca40ef18e41dc31c437c83206f90110bfa9c417d529077a85205fd4f10faa0883df528c7ee43085f95031afa9a83f7314c77863207bc8220bf29e81bc41102fea0997ed4121ef99063ee320caf8a8885fd5320ef21e617e54cc2fca320df54221de20441be411037e8720770ca31de202217e50d0af8a8985f94f219f2a0637d500c7be60185f55221de99481f820c437e62205f14d10bfaa2637f54c86fca8085f94630df204417e5410efca7087710431f7908433c54443bc8218dfd4f21
  | 1 => 0xe53486fca6216f90210bf296217c548c3baa418f790c31dfa0883de500c6faa8985f54831ee18e437c53486faa420f754231be28a877e50042f8a818fbc8621de206417c50487e8a2906f10210ee284637e50ccaf8a6a0df15020df204617e54c42f0a0a0efd0240ae29a417f544caf8a8087790c43beaa0215e53d0bb863a05f54743bf2a041df318c77ca810f70c720bfaa063bf53102faa898f74c030ef18a41be54c42faa0216f14440de29081dc318437e80204fd5121ee2a063bc53102eea2905fd4c21be2a663f731042faa9907d44010bfa82837f514c2fca3215f94e20be2a061dd530837c43205f94b439eaa665d6510c6faa7a0df15021bf28061ba50102fca91977d5031cf18c81df4350fdc40905f95042bf290637c540cb7ea8885f55030de204617f520427aa9907d14530dfa14817e51086baa7a0fec8010bfa9287fa10043baa518ef90140bea9c857e5010afca6885fd5231ef21a617c530437c42207ec8310de19081ef4250afca5086f50e40beaa621dc548c6faa8905f54830dfa1081fa40103b863187ec4210bf2a2615e53c87ba64195f55231fda0621f641107b86310fed0010dfa1a837f53483be64197bcc820deaa0637f52506faa9985b14930bf29e836f524c3f661184f553109eaa661de548c7b8a018df94343bf284877d53c82b8a6a0df94e41f621043f431042f8a898f78ca31efa10637e50c86fca520ef95332fa10821ef42886fca5195f15220beaa2657d549037ea7206f50c43beaa243de304c2faa921df94a43afa9a41bd40102faa4885f54041beaa483bd41902fca020ef4c640bea90217d53083bc63886f90a41dea18817c544837865205f55031f629261bf419077ea4205fd5110ba28a61bf4210afca888770c540bfa82857c53c86faa7a05f54840bf29843de31cc3ba6218ef50440be2a6657d53102fea6a14f15120ceaa063fb20883ba8618ef548409faa221bd53103bc62106f90841bea9463dd4310efaa718f78c410bf2a065bc52903ec4210cf55031eea0863d431042faa021df15321de988815e53d07baa818dfd4d41f7a92617d51cc3dea4885fd5030dea1885be32903ba8518df54732ef29841dc320c7bea690dfd4d40cea98813e54c43f260187794f42bea9c41bd54c82faa7085f55232f7210857e51c837aa810df94032bf28883de328c2fea790774c831ae29a437d5290f7e82206fd0e42ee19061df328cafea090dfd5230eea98817f534877e87a0ef50b41bfaa0653e54ccafca9997bd4941bfa9c215d53103de65105f54a10beaa485f721043bea6885f14143bea84637e548c37ca7205f94241aea98417d50ccafea710f78c620ee20c63be4350ef8a098f750d30ef20c637e53c83be6518df14e21bf29c81ef324cbd842105fd4940be29261de31443f681205f55020df21
  | 2 => 0x20080e8082c0334ac369f40201c11008f901d64088090800309c020080508019008000e8af82c02119cc0001203069008340080b058000000213407014000201b004000042e7080100c1e010000152b0003e0b80c38c001f00500dcf00000004000140d36805088000285b22000160002dc855a80f060040a00402c020024354401000360054f5782813cdd000001445a238060bc00254100005a0382009009028160ad87018000000f0180e0000f078743623c0080e0202701804014160d405014206e42f6e9092681858cfe1a8102cc07000000bc140300300c0009000000010001b760346902e0cc4f01631350c600002034070dc300a80267c00028190108b00004030000000205c054f008004070580c0583d0280e00000000e108038000a10002809426000f0000010ac09074c3bea9c65de314c7bca818dfd4131ee294637c53503bc63186f08440dea10813c544c3be6218df14532de99081dc31882fca998f70c510df28081bd21103f220085f55230eea10633e54cc2faa190f754f42f6190417d5190efea890df94f10bda8243bf43103bea690778c621de90c817d52d0f788520dfd4543fc206217c5284378a89077d0a31be28a417c52506fea8105fd5330bf29463dc31486fea6087ec4110eea80637e53107f0a090ef15130ae29a217d518837a872177d0c31de10c81de53d06faa510df54720de21c817d54c86fca318fd4c431fd10041de31502bca7085f94621beaa6637e544c77e42205f94e43ee18c81bd42507ba8718ef10c40af298817f54c4338622077cc930fb90c43dd548c7ee8320cf94040bea8065be53102f8a4085f94240dfa1885bd4210af8a9087ec8120bea8e857d54ccbdc4290df94c32ef29881df548c6fca110df55220be29221df308c2faa1a0cf94240dfa88817e510cafaa5a0df54331ee21863dc31087b862205f94743fda8283f7318c6d8a4a0ef90030ee992617e5290afaa790df54a30be29c417e53886fca3107750631f619441be439037885205f54e30bf28e817f54482fca1186f55330de202615e518c6faa2196f90130bf280637e528c37e8721f794f21bfa96217d510c2f8a5887b50842be29c21f521087da64195f94021de20061bd54ccb7884205f948309faa2417e541037e43205f15221cf29881bd53902fca9086f54a40de2a243dd53d06f0a090df54b10bf2a265f840042f8a6905fd5332beaa4217d53442faa598df54a40bf28e61bd54c43ba87197b14941bea8c857f548caf8a890f70c430dfa8c817c504cafaa3195f54021df2a6417d53903b88418f70c530eea1e617e508c7be8721fb10a21bfa9421be41506baa790dfd5210bf29887b840043bca7084f15121dea0883be431037c81907dc4010bf29821f6310c7da40106e10310efa8063fb304c3bc8518e795031bf290417
  | 3 => 0xf002004c0ac45f0090d08405008040080006413034a8028009101d0983c2ac05108160
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x54210a9e6314c409e594400423f64549109bd95210863e60953329798e544823d6414c109d185544c25e631532197194314831e6395021aed8121902776155132ec084400423e6494a10d314a304c23c65484408f5942110275650c41097d94311023d6414e218f994544c33754d4520cdd46404823f6548640e68c440042756508410d594431cc2b960c8440d390c524c25e6394241c7d50534823e6494d109718d518832c54149308f990538873b42141419e580530865d65d04319b18954442766194d208f992518c2f0604842197987534833854c4110c754e52103d03108010ae583411025f6355131e5952510c75a3114121ab98b519026c625403197984534825d63d4520a759332cc23d6414f108fd91508c63e65151208fd9153486756115020ec984400429d63c8440a759031cc2d663c8610c714e404823c60151109798f548423f6454221da148505063d6494410a7990528c67960d53318f592518c31f53101109d185534832f5414910e50c6408431d548c720d554431c832d5214840e60c440c429c64540319ed81534876452841109e181534865c6354740e6101300c29e63d0a40b5984548c6776154d209b189534425f65504319758e524431c548c510a7d8d519031f6555031cbd53524c3d031d0010d3d48314c2b9600c8408fd91510835543145308f994211023d65cca408f593504ca9d63d0842d9d48514c355510c740e654e501025f6550c438f992544c23e64150219ed81524425c6154f4297185531026d62d4f109758f5150a7a60951218f996404431f540c5218fd9150cc71c540c521ab988539032c6255021c7952510c65c6354021c754e421026d6215231d3d48314426e62d52109798e534831c53101109798c540427661d4f208f993528429c63546408f9925308395640c4109e98354c871c53d0d419dd85524423d64145329798e540876852d41418f19150cc67b6055121b6181434c23f6454d20b9185200825e63d4542cbd48404c23e60151108f996404c29d64d4231cb548421026f6255110c754c400826c6255130a798f511031e63953108f592528423e650c440d6d4c50486cc6250431c794d43d071d54d4031c7d4e40442ba60144408f593528423e6095031d50c6500423e64d4b109ed95200823e6494e10a718d211032f5210110d5d44314c36852c41109758e544426d650c8209bd89500c73754d45309798c5050a5d6314810c7d50314425f635464097596310834f5314941d5d8c514c29d64cc8329ed81544ca9d64cc930e5552510c65d63141428f990530865d6510c31ab58b4310a5e6315030cb153524c23d6494910a7590314c3954110431c7550320c79031100108f59352c429d658c440d6d4f50506b66114840dad4b50506ba60c8440ce508505063d6494c3097596430cb3854d4121
  | 1 => 0x4337541453097d95310c6ba6014640a7993520c63d64d4121a758f429023d64d4f1097996314865f63547409798f54c86786054442cb14a41506ba60d4840d518c514827561152329718d52906bb6050440d3148314c2d96014831d5144314823c6454810ce594400425e650c520a7593500c73b54141218f59052c42746155132d3d4a314c32d43149419d58653482786055131a7990520c6b86050441d5146304c33454d4520e68c440c425e6395320c755031c431c548c521cd144404c31c5414d109e98354cc74f5294a318f992530cb385414121cb9494290339541031097596430c66e6295110ea1012008357510c52097994534865d63d5020a7d91500c65c658c520c7150534831f548c5218f592534423d6494f21e658c4004395640c6108f994219026f6255130d598f514831f540c5209bd89534431c63550319718d51d0a9f6350440cd14440482b56114840cb153524429d6314840ae983519029c63544408f994404c3396510310b3189500c756431453097d8d511033451901309dd9510042746155120c7150314c26c62551319e181544873751101209d58753c833454145309798c548825e63d4b109e980530865f63551109dd85544c31c31940409758c540426e6294d10d60c7504874c5388120d614f505067b60551319798e520871f548c5108f596540c69c6454a31d5d4c514831e548c730c7592530823c6454d10a7d94311025f63540219b588540425d6395310c7592538423e641481097d9431082ba600c8409b98b54cc756518c630c7d4c404825d63951328f992544833754145209718d51c826e6294910b518d100431d54540318f592530cb3a6094040d354f320823e6414c109798e5088756510c430ec103100425e63d45209dd95411069e6095031b5d85420c71e540c421ae983529034c52cc930b358a430ca3e6494410d3d4c524423d650c440cb149425065e658c520a798c51102cf6254031d614c505071e650c440a7d8d419031c5490d308f594319033451901209b98b53c427b654401097994534825c6354420d5d85538435563d4520cbd50524c3645214530a718d419029e63d46409718d511023f6550c439798c52842776154032a7185531023c64549109e583540cb3b43141419798c54083b331100109798e54443d031c8010c7d5353486cf62506319758e509063d6595021d514c514831f54d4d209758f52c425c6114d10c755031cc31c54d4d21c754d411035453d4520d314c524425e650c521c714c404825d6315321e50c4408423e64949108f99053c4357510c540ce994400425d63951219dd95310c63e6494820aed81211032c5210130e5990310431e53940408fd95411073b6414141c7d4e40482b8604c840a7590528c75753d45208f982540867b6055110a718d411032c52901309bd9
  | 2 => 0x548c520b5984520c63d65cc840a7d96311027b654c030b3988548c67b6054442b5185300c25f63551208f980544871c548c530c794e408423e65901208f592538423e64d4f20ec0c4400429e64cc831ae181219025e650c510b3588548c71f5414d21b598631042d661d4a31d314f525067a6094d21a798c521026e6215010ae980529029c6354a408f99052c439a6310010c794e400823d6494d208fd91520425e639531097996314423c60550318f993504c71c5414d2197d8d5448757518c520a758f519025f635444297d8d51d0b1f5414d10ae99320043545384110c78c6501025f654c8329e58354c869f63544408f99053882ba6014c40b6980520c71e5350c40bc185200831e6494c20cb553420869e6414031d5d8c514829f6348440c7150314832f54d4910d9d4b514c23e6510120c7992538431e548c421a7593328cad561108318f593530865e63d50209d986544826d62951309bd8954487566194431ae982400431d5390c40d3149324c39a5394040c7553430c69e63d0440d68c7504871d5390210d314a314c23c645422197997324c31e63953209bd89511025c6355120d554431cc26d62d5331e658c40c429d63d0b41d3148314421d650c440a7593320c7983194040c7594311025d63d4a1097594311029d65950319758e544c65e63152218f596421071d531484097d8d52906b46150d419ed95401023e65cca40a758c5290355530c610c795031c429d6414031a798f521025f6354420b5987540c63d6494620ba181210869d6314440a7993508c63f6454d10e5990318432c521011097d8d5190a3e64946209e59420042bb604c440ab588511023e65101109758c548431e5450f30a798f211031d650c6408f195219031d548c730a798f219023d6414e209bd95200825d6315220a758f42102d66094431ce59350486e561108218f993530875b53d4121cd150514826e62951309b18951102ba6014840a7986311025f63548108f592520825e6394010ae983311023f65500409798453442b8604c4408f590530865e6314c209758e54c825e63d4a10c7d95531031e540c720a7d8d219031c54d4d20d5cc8514c29e63d06408f592534865d63d5210a7d91528c69e64d4031b6d81410c65c6354810b3189300c23d64d41319b588530423d6414f2097d96311036451881209798653d0a3d6508640a798f421031d53544408f191510831d540c421b6181410c63e6495110ae983539035b53141419758e500423e6414f20a7593520c65e63148108f99431902d661d48318f990540c71d53d4440d3949328c756510c720a7191508c7d03184010c7552520c7d1600c410c71535344355650c4108f191528c25e63d4540c7d50314c2d5650c6109b98b540c3b161100109d586544831d5310840ced8154c434f528c510cb14a404
  | 3 => 0xe4097d8d51c833b6414121ae19110042766115232c795031cc32c5488521c798e540c6d86050631a7993328c75853141219718d544869d6594c409758f51502796584010a718d219039a3194040c754f411031f548c530d350c524c34c528c5108fd91500cb2f52901109d986544c25e6514d10a7593328c7c431484218fd91528c6af6250440d3189530831d5494431b318d200823e64d4f1097d95300c394311001097d8d518831c548c520c758e540871e548c7109bd89544c63c6454d21ce904505069c6055031ce99350486ce62d4231cd153514c39a6310310cb150524423e64145329718d5110a3c6454231d614f504874c5314941d60c450486ba6194040ae99320c42ac6250640c758c544c23c6454a31b3d89410c63f64543329bd95320ca6e6215231f8084200425c63546408f19153482776155120e60c4400423d64d4f209798e52c42e9600c820ab58b519023f64543219e582534867461540328f590520433943141418f191500c63e64951219b58a544429d63d0640d3548320c6bb604c840cdd46404c33864141219758c528423e6494c308fd91528c2af62544409798e534427765484218f1815408796610c440c755031c825c6354642d3d4f525071e548c720b3588500c65d6394821c754e501023f6548440d5994310426f6254d209798c548425f6354a40a758f52102786055132b6d81418c67a60d503297596530833a5110010c7552310865e6394d21a7594311023e65cc84097d9631083b32110010d914b514c31d6494f21b598f210429d63d04409758e508865d65d0a318f19150c865f6354910d594431d03943190010cbd0c52506b960cc4409b994524437321141218f9945448754518c530b9189100425d639502197594310825e6394910a7590520c6d661d5231d3d4f524423e6494d20c758e54c823c6454232a758f511029e610c440b5984528c65d658c830ae181211035532145309d586544c2ac6448421c7550520c71c540c510f4980310425d658c440c7552320c6e86244010d5146314823e64d4132c7994319025d65d08319b58b540c355650c6109b594420863f6454031ab18951102d66115031a758f42506b965103109758e544837051c8120cbd4a529032c52d0941c794c408423f655084297986531025d63d5321a7990540c65c6354a40a798c5290396610c640c755231c423e60d5121b5185420c66d62d5210b3988500c71e5310020ae983531023e6515110c799253c863d6494c209798e54486766115020a758f4290a776154d109758c54886796095121c798e54cc2af625064097195434c36a21141218f993504863e6494f218f18154ccb4c53d4910c7d53534423e6494d21ae983511023f6454232c758e54c423f6454021d3548520c6ba6014e4097986530831d5310210a7d91508c71f
  | 4 => 0x14425008770000612c1300016020000480d1603e4085a00c2543023000030000100c0100c1006c04004020500100422248000880602000004060880501088010472bc2f000000000414c0000c0c024220206505c050040f000002c8030083518c2f00000000000ac0803800040ca0386a0080000032000000461131821010020340002c1913dc51f80105c02058a10683b05c041fc012e40003c2503007054010040b01c0000800030200040f018210300c0008a0100104c0504800000020000d048030900004406038050f00000804000090c049000000180102809004530040f8e82f00404034420000007005004020196d2b4300646300809018010045701403000000440800008000000b4170001f001d50004a00c460380300616005bb00c000bc0303c2001c0d010120640380018000000008a0ec010000600c040e0000180100402024000004b0280e850000fd31000dc028050680e0000202004034b714c1420c000000389404020074081b010010403d124091090600c41010500dc0009c0201402000020d80001802084080ec010004200400000c91381300c0c01c0a028030040e8901797997428c6ac625044097185530825e65d08319758e52c4354510c540b3189418c6cd62d4231c714e404433b54d4121b5984420c63c6454332a7986531025d6315020c7951430c6ae62144408f19150087d03110010cbd4a404c26d6294d10ab189411065c63551109718d524426e6214c10a7d8d529029d63c86408f191500cb375110130dad48505071d53900208f99742506ad6214
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x458e046808008540800600000020118702040038224103000048400000000e000020000681000000500000020024003040430392aec188810843870590514cb0caa2c029063641d1600c410d22c6b088008499760c4400420ebb4a620421381c1611082183aed2a063904e071580320820ebb4a620041a218c4048020d40c22024010499760c440c42c838ac620021a1190314842183aed2a06210cb1760c440042c939e4220021701c9600c410b40e4b0880084d070584420c712a92c229081491c54314941a28e2a9a822060d5318951102c8bb06220021a499031c8010930e0b26649860d6414b324c2c839ac220021075da650c440c1ac829062985307150c50506c83828220863a49d83110010b08e4a088218d93760c4400428a38aa6a8881521c143149308a8e2b18a0a159070590310424a38ac7a1283465cf4214141d10c4202601864952580520c70aa9ac229081a45d83110010c1aa8312a018d1574cc8514c20ebb0a818a612c1c5600c84083aeb31e4220592718c4400430ab2ac818821b00c46048421a30e0aa2a018c91760c44004348b22c0188218358c52d0941aa0e0a18a2986196558c40043483088098061261c1640c53083aed2a0638860d53189411024abb06220021345d83110010
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0xc3052c000000070001a08805506254031a0880590520c5308918799031c8010c81641c9600c410c81631c96110010c11651c56310010891869cf2110010a048158c52d0941a048154c6250440a048154c6254440a088059052cc930c11651c1640c410891879d83110010910815cf4214141910805d33214530
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 820
  | 4 => 894
  | 3 => 68
  | 2 => 15
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s0K7 (i*5) 5
  | 6 => packedAt s0K6 (i*16) 16
  | 5 => packedAt s0K5 (i*27) 27
  | 4 => packedAt s0K4 (i*38) 38
  | 3 => packedAt s0K3 (i*49) 49
  | 2 => packedAt s0K2 (i*60) 60
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 7 => 2*((h/1+packedAt s0K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/28+packedAt s0K6 (704+(h % 28)*6) 6) % 44)
  | 5 => 2*((h/273+packedAt s0K5 (22140+(h % 273)*10) 10) % 820)
  | 4 => 2*((h/340+packedAt s0K4 (33972+(h % 340)*10) 10) % 894)
  | 3 => 2*((h/64+packedAt s0K3 (3332+(h % 64)*7) 7) % 68)
  | 2 => 2*((h/19+packedAt s0K2 (900+(h % 19)*4) 4) % 15)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffff01ffffc0fffffffff80ffe3ffe3f
  | 2 => 0x1fffc07fffffffffff03ffc07fffffffc71fff
  | 3 => 0xe03fff80fffe03fffffc0fff81fff03ff9e3c7
  | 4 => 0xffc00000fffffc07fffff00001ffffc1fe03f8
  | 5 => 0xffffffff00000007fffffffffe000001fffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x224a450a211c4891402cb2d2a25886521a6e1b
  | 2 => 0x8909314522491228b01554854ab18a4c514ed
  | 3 => 0x5a230a2694483a44d55409ab1135a23969a346
  | 4 => 0x933a2c58e8912077669a603261c6cf11be03b0
  | 5 => 0x1c3c3060f0e1c387b8e38e3c78070c21f7d800
  | _ => 0
def s0Atlas : Atlas := ⟨7,rawDecor 62 s0Pos s0Neg, 0xfcc0ccc0f0c0c000fcc0ccc0f0c0c000fcc0ccc0f0c0c000fcc0ccc0f0c0c000fcc0ccc0f0c0c000fcc0ccc0f0c0c000fcc0ccc0f0c0c000fcc0ccc0f0c0c000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_40297
namespace PEqualNP.Outside.L_meta_40297
open PEqualNP.Outside.L_meta_40297.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x200500100ef20ec32ef32bc41ee21be40bf43ec21bd43ed20bc40be41
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x430402001401385050f488210d914520b328e65365190298a6904d14543
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 7
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*5) 5
  | 4 => packedAt s1K4 (i*16) 16
  | 3 => packedAt s1K3 (i*27) 27
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/18+packedAt s1K4 (192+(h % 18)*4) 4) % 12)
  | 3 => 2*((h/16+packedAt s1K3 (189+(h % 16)*3) 3) % 7)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfffffffe07fffffe07fffffffe03ffff1ffe3f
  | 2 => 0xf01ffffff80fe03ff83e07fffffc0f80e4ffcc
  | 3 => 0x1f81fffff0003fffc007e03ffff000f8e3f0
  | 4 => 0xffe001fffffffffffffff8003fffffffff03ff
  | 5 => 0xfffffe000000003fffffffffc0000000fffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x50c0842231224506014a4965461152a6096e15
  | 2 => 0x654918c450e4895a581682b99ad44b0a64b6cc
  | 3 => 0x4a922d68a241d5aeaac144cd2d5b6214b8e370
  | 4 => 0x831851910489183134a5901031a28c58d601aa
  | 5 => 0xc1c61e1c70e1e3dc739e71e01c30860ffd800
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaaa0a0faaa0000faaaa0a0faaa0000faaaa0a0faaa0000faaaa0a0faaa0000faaaa0a0faaa0000faaaa0a0faaa0000faaaa0a0faaa0000faaaa0a0faaa0000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_40297
namespace PEqualNP.Outside.L_meta_40297
open PEqualNP.Outside.L_meta_40297.Model
def s2K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xac42
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (i*5) 5
  | 3 => packedAt s2K3 (i*16) 16
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt s2K4 (5+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/1+packedAt s2K3 (16+(h % 1)*1) 1) % 1)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xe07fffffffffffc0fffff01fffffffff1f8fff
  | 1 => 0xfffffc0fe03fffff0781fffff03e07ffe4fe4f
  | 3 => 0xff81fff0003f03fff801ffe0ffc007c0f8f38c
  | 4 => 0x1ffffffc003fffffe0000fffff800ff03f0
  | 5 => 0xfffe0000000003ffffffffff00000000fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x29044482440840802912520914429452098495
  | 1 => 0x421888648952914b02a0a4b2623422ac643a4a
  | 3 => 0x852d5121d5a456d558513ac8be905706b8d38c
  | 4 => 0x1651a24919069b6694e40c90cb396208f60360
  | 5 => 0x1861c38e1e38e3b8e779cf1c0c218430dfec00
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 59 s2Pos s2Neg, 0xeeaacc88aaaa8888eeaacc88aaaa8888eeaacc88aaaa8888eeaacc88aaaa8888eeaacc88aaaa8888eeaacc88aaaa8888eeaacc88aaaa8888eeaacc88aaaa8888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_40297
namespace PEqualNP.Outside.L_meta_40297
open PEqualNP.Outside.L_meta_40297.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x2010034000f0801c41010032813c154044058028efe32ff42ff40fc32bc42fe43fc40ff10fd42fe31fd30ff43bd43fe41ff41fd32fc31fe21fc41ff21ff20fd31fe42fd20fc10fd41ff32fd10fc43fd43ff30fe10ff31fc21fc42fe30fc20bf43be42fd40fc30fe20fd21fe40
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0xa0e00102040c00082251870e0011000040111e5800300001001c2c18c0e08ac70201190040278a9195794c41af29c433e548875885905bd4943b7a92833d5404278a8994fd51209eaa6656c5250edca598cfd51109f2a0635d53886dca4084f95032af298215f534833ea6a1cf95043b7a92215e53d023aa6215714d209faa2435c534427ca9984f55330d6210433d54cc67ca8084f552439f2a4415d53106e8a2905d947329eaa0616c52506baa6084f95331afa9a219d43ccb5884906b10832b6a90617551ccb3a86994f15110b6a96639d43cc6eaa2184f94a4296292873f544cadaa4084f55031cea1c613f548ca78a8904f95030d6214436d529033aa6214f55032cea18619d434c67aa9106b94842aea9e815d5310a7ca5a1eb149439f2a6653d5390a7ca4216bd49439e2928776510c27aa910ddd4520d6216656e52902d8a4884f15121b7290615e5310b3ca6214f54c42
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x331900280000040009c00008000080000003003154354430a358c42cca8c6250d31c9108514830c6254c42c314c424828d6310920a3189438c28d6310a2187195434ca8d6310b20a358c420861d6395220a3189430c22c6255330c550d51cca1d6315121c910a51ccb0d4354830a318943cca2c6255031c350d52cc70e5310a218b594420ca8c6250f31
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x40000068239286a8e65035d8531092081aed2988510d047250d510c282b988428a41415cc4294732
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 90
  | 3 => 25
  | 2 => 6
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
  | 6 => 2*((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/28+packedAt s3K5 (704+(h % 28)*6) 6) % 44)
  | 4 => 2*((h/44+packedAt s3K4 (2430+(h % 44)*7) 7) % 90)
  | 3 => 2*((h/36+packedAt s3K3 (950+(h % 36)*5) 5) % 25)
  | 2 => 2*((h/9+packedAt s3K2 (294+(h % 9)*3) 3) % 6)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffff83fffffff03ffff83ffc1fffffcf1f1ff
  | 1 => 0xf07fffc0fe0ffffc1e0ffc3ffe1e07ff4e3e4f
  | 2 => 0xff81ffff000fc3ffe00fffc3ffe007038fcf8c
  | 4 => 0x1fffffff003fffff00003fffff803f00ff0
  | 5 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x2004088824020000a41280444022914810d095
  | 1 => 0x451891064894a12c0a852429921422b146264a
  | 2 => 0xa32d22921d2906556109ca82e540541a8b4b8c
  | 4 => 0xca51c4249181ab9a53a0622339996023e00d60
  | 5 => 0xc618738e1ce33e39dce7330311180c3fdb000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeaeae8e8eaea8888eaeae8e8eaea8888eaeae8e8eaea8888eaeae8e8eaea8888eaeae8e8eaea8888eaeae8e8eaea8888eaeae8e8eaea8888eaeae8e8eaea8888, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_40297
namespace PEqualNP.Outside.L_meta_40297
open PEqualNP.Outside.L_meta_40297.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0xc01470c00810000130042400411c008014d002000ff42fc20fd43fc21fd42fc40dc31ff43fc32fd30ff10fe43ff21fe30fd32ff40fc43fd31fe42fe31fc10ff30fe32fd21ff31dd30fd10fe10ff41fc41fd20fc31fd40de31fe21ff20fc42ff32fe41fd41df30fc30fe40fe20
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x637d53482faa2197bd0a42ee18e817d53c43baa7207dc4210ef18c437e50903f0a0a0d754f21de2a221dc434c378a890df94842f7a92877d53087bea418ef50c43efa0e61ee52042fca6215f94e20bf2a4437d500877e8320f710530be294217e54ccaf8a9905714530efa1661de548c7bc42986fd0441dfa1c877d52886faa7a15f54f21beaa665de414c3ea6218df55321bea9e837d518cbd88410cf55220fb20883df21cc2faa3105f54e31eea8063df30882faa688778c420eea9e837d51d0ff440107715231dfaa221ef21482fca68877d4930eea98817f53482f8a29877cc210ef29c21de31102dea4a0f750f30fd90021bf40102faa7a06f90b40bfa82653d54043d884906f90942f7a1065dd32cc2fca021df95210b6a9481dc31c87bc8518df94a30ee29e21df54cc2fea090df54b43bf28665ad4210bb8a2985f94840bf29887dd524c2fea8087754530efa10637e5290efca8085f15210ef98061f910043bea6a15fd4c21bda82833e54883b8a6a0f710130ef18a437e500c7bc8498778ca31efa08637c5050fb863105f55320ef18a637e52906fca4195f14d40ee18c217d538c2f8a4885f54420f7a1241fb40503aca218db14943bfa8287df4390efaa8995fd4d41eea1863dd214c2f8a498d794431bea90817e508c7bca5985fd4810be2a243dc310c3ba6418ef90c42ee98a617f54083ba87995fd5220bfaa4615e53902fea2995f94c21be2a6656c52507de65195f55021ee19463f6310c6f8a998fbc8020efa18657f53c82baa7187ed0310bea80857d53906fca218efd0a42af29e437e53902faa9207790e31bea9881ee21486faa5105b94a40bf2a6417e5410efaa9187794c42f7102417f52c42faa998f794730bf290617e53c86faa3215f94621f7a1043de434c2fca120df55330bf290877c514cafea810dfd4910bea9221de31087da4390770c930be2a661df30c82faa918f714a31be2a461ef21086dca40877cc110f610c417d5390af8a6107e14121bf288215d53882bca6215f55220bf28081de324c2fca3a1fb50842efaa0637e50cc77c80a05f54830ae29a21bc42502fca9107790f32bf29c83dd4310fbe6318dfd5320f7a92837e53483daa408770c730ef284637f50507ba83985f54e20bea84637c53507be61187ed0240bfa9c437d54042fea7085f15120ef18a817d52d06fca618f794930eea9841de31482fea898f7d0e31ef996617e544c7baa918fdc4010dfaa2437d51d0bb863907794f41eea90637d52cc3ec4210df14d10ee18a217f53503be6418f750130bfa92637d548caf8a990df14943ef18e217d540c7be8698770c630ef2a0637e51882faa920fb54a40ee982417e52443b84298778c530df21a87fb10842b8a690dbd4943be2a0637c504cbb8a5985f94a42f6292213c54442fca5a0df54332
  | 1 => 0xc31082baa118ef90841ef21e617f540c2fca5207794c10bea8e41dc31103be86a1f794c20eea1a61de31843bc65987b14943be28a41de420c6fca5a07750e31ee984417d54442f8a6905f94b30bea9487df414c2f8a2a15f94f10be2a4657e50086faa019774ca31bfaa2217e54082f8a090dfd5031ee98421de310c2faa8987714231bf298615e53842baa6085f95110beaa0657c54042f8a9107794a31bf29021f940103ee8320dfd5231af28e617e53102faa021df94f20bfaa4217d54083baa7106f95010bf29041bd41502fca418df15132bf280837d520c6f8a810df54610dfaa265fb50487de85905fd5332af28c63ed20082fca021774c030bea88877b50487baa6215f95121bea98217e53843bca8985f14930f790e415e53083bea2985754e40bf29c857e548c3de41105f95031f610841df328cbbc6418df54321bf28865f721486fca420f7d5231ef218637c54887b86418f708730b6292215f5350afca318f7cc120bf28e417f53c87ee6318df54740afa9a21dd40cc3baa118f7cc832f621443ed21482fea0a15f94030efa1e61ee320cbda4210df54732bf29687de500c7de85995f94c20eeaa661de31cc3f641105f55121fc206217e530cbf240107750530afa9e217c52042fca2185fd4540bf28443fb40042faa7207755130bf2a4657e528cbea200877cc930bf288437d544c7be6188778c720efa1c65df504c2fea6885f54241dfa18877e51906fea6a15f14543fda8283de31443b88719774c320bf28887f820c43de64995f94632ee98221de318c3bc8621dbd4910bfa9841be4390bb8a6a15f94242efa8463dc31502fca710dfd4f10be29843dc524c2fca990dfd4940efa18637f5150fbca218f7cc730ee18a417e50842fca321ef55010dea0e817d508cafca598d794c10eea0c63dd52cc2bca7a0dfd4a10beaa421dc430caf8a898f70c421ee2a661df328c6faa1a1770c530beaa621de304c3d8a4a0fe8c030f721085df52cc2fca8995f95310be2a0657e5390efca7a15f54242ee18e215c53c42f8a9885f54442be28283f541107b8a6885f54c41bf298217e53107bc81985fd5232efa0661ef42887de4310fecc230ee216617e52842f8a790df95231df212817d53486f8a7905f94321dea00817d51cc278a890df94440bf288837e53486f8a0a17b88620fd200817d5190efca9987794530eea1063df310c6bca7107710631bfa92615d53843f420085f54810bf29e83ed320cbbc62085f54a41be29c217850486baa6206f10c42de2a265dd434cafca3214fd5132bf28885bc41903ba859877d4f10be29821df53507ba60105f54221aea9e83bc42106f8a918df14f10bfaa443dd30043b863207755031bea8683de418c7b88718f710831bf2a2413e54043d884196f10a41bfa9287be41902faa7085f94220ee2a
  | 2 => 0x1800010001400e128162a0440683c1a01c0e8000012e000ac000000900047006038f4030320080001afa068e803806313240200235000268000025001808ab022000022f834050002400000000100bc0100e01814030c60403a0680e1a8960183c07800000040182e02802010160a8120027a0080e549720080b1d802030162100a5a1d4000200206a010120500001894000042b0080082c060080f006001000380c22010000141202200022008946c00010000058101f00e0100226838060001c8420181025006038b800808000c0000000082c040000101a000460180a020b45883e00058160200e816558100100c215b2018600f002010ea0187a0181c070029200000036128000405c2a07a00840018001120c0405a050060081c0006015002028800b004010c2000200100a0017a0a00a018021a83a0700200004040240190c098180e82c00022078180001601820050000180001000000b24e8000181e12040101722e8360003c088000edf54c42afa9a83dd30c427ea890df95040dea08837d54887b8a690f7d4d10bf28683dd53843ba6218df14e20ef980217f544c2faa2185f95331efaa261dd410c6f8a710df95041efa9463be41507f040087b88420ef29c41de520c67ea8887e4c030aea98417e51d037e81205f95042fc200217e51d0bec20885f54640beaa0617e51083b887985fd5331bf28c61dd53042f8a8986fd0540bea9e41df314c2baa6217754f21ee990657e508cafaa8907bd0942ee20e617d528c2f8a4a05fd5132bfaa6615c5350b7885a07710a31beaa4857f54483bc632076d4130bf28c81de21cc2fca1a1f794e40f7a9221dc520c6faa61077d4031bea94217c53487bc63a07750a31bf29621de41cc3baa398770c410ef2a661de404c2b8a6a0fd48421bea96217e500837aa9104f15132bea8881dc51cc2f8a8185f95021ee21261ee52903f660985f54a31ee218637e540cbf640905794c40dfa10857e500cafaa121fdd0541efa0261dc410c6fea2985f94010bfa8a41dc31886fea4a0df14d42bf290437c54082faa5207794f21be28a816d52043bea690ef90a41bf28487bd4210afaa198dfd4542ef98041df428c7bc86997710330ef208637f540cbf641885fd4131bf28e65f721887b86290df55243fd882217c52c437c82207790b30eea94637850506fca8185f15110bfaa2437d500c7be84985f54e32bf28461de324cabaa018df94730bfa98217f53486f8a098df54b40ee2a261dc32cc2bea690ef10e42f621641dd21cc3bca6206f95220ef90a617f54c42bca6187750930bea9c437d52cc7ba63985fd4e20bf294637d50d0fbea3985f54041ee992617d518c37e83a07dcc531ee280637d5210efca1a15f95130de208817e53d03bc6390df14941f6216657d52107be8318dfd5321ef18c41d
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x3208827b6054442c7950318825c6355120b5984540c75863d4121a719132cc31c5450d309758c52042cf6255031b6181410c71e54cc010b5185544c2e8604872097597430ca6d62d4c10cb95221882796584010d6d4f504865d6394342b658031c42db6048530d314f4250aad6490842c7153534871e5494e20a7590508c65d60d4d419758c52842b86050441cbd5042cca5d6394041d614c504863d659501097d8d52106af6550842a7191214c32f6550842b3988500c66f62551219bd8954cc2cd6215330ab191210865c6550d329b588540c6d9600c640c7d50314427a60d53218fd95401031c5490d32d394e520435a631412197580535065e63943419dd95210871f5414d10b398b51cc2cd62d4730b6580414c27765504419798e500869f644c8319ed81544865f658c6409758e52c43596014f109b58b548c66c6255031d354832cc25d6510a319798c548825f654c0309798c540c32f5410a219b189544c71c548c5219758f515025e6315021a318d4210a5d658c440d3548520c74d52149309759741cc34f5294a31f24c1200825e6394910b6980214c25c6154c429b594420ca5e63943429ed81544c75a31d4121a7191320c6ce6290130a7590500c74d5394a409798f540823e6515121975835350a5f658c4209798e54c42776544010c7950310438f635084297d8d5190a9d64d4a31b6980520c71c5450d32b318d4210a9e6414b30b658352cc23f64549108fd95411065f635532097d8d519032d541082197d9541cc26d6594810ab18941d029c6454530b6d81414c26f625513297185539026f6254d10b6582310427a6015031da14b505065d631494097d8153c865d6314121b6980414c26e6514910a7191520c72d5454810d3149304425d63d4520d394e529027b6544010cb94a419023f6454d20979865310b5963141419e98254486d960951309719521cc25e65108318fd91510826d6294341cb150524425d658c4209718d519035b53d4141d694d300c38e535084297596319025d63152109b58b548c2d661152318f5935388276611502097185531025d63d52109758f5150ad661d50319bd89540c757510c520b658351cc25d650c6409758e54442e862440109b189544c31c5414d21d3d4f525074f4314943cb55042c823f65508429b594420865d639482197994314425f6550a31c7550540c74e528c640b6d8121cc29c644873097d8d52d029f645493097581530425c63546209758e50042d9601503197594430ca5d63150219798e5010acf6250530a7d91520c65d6394021c754e4310b1d541513097d8d544826c62553109dd85544825d650c620a7990520c6db605453097997434c38e4310b328f997415025e63d481097d8d544c65d650c44097d954310e5c6355110b6d81418c63f6454d10c7551300423e6414c10
  | 1 => 0xc29f644c9309758f54c863d6590440ba181210865d6394241cb95152042ae6290140d6d4c505078d4210a319719541cc2ba6090940d314f524432d5410920a719152cc23e6414c21cb548421063c6454420b318943cc25f6550b308fd91520c65e63153219759721cc2cc6250c31975805350bd330440109798c53082ac62504419e580540865f6355121c755253042d96014b309798c505065c65509309bd95320ca5f63551328fd9152c42d46154930d394b300429c644c9309e58354cc6d7615493097996434cb4d528c640cb94b40902cc6250f32b658031042cf625513097195428c65d6315020ce1531044274615513097597414c25d6315220a7191524c25d6315320b5987520c75a3114121b6580318825c6355310d5944310c23f6550c43c7150314423e64d4810b598730c434e524ca31b658354cc25d6395221da884504865e6510b309b58a544433a4114141b6181418c78d4210b308fd9152cc27b60549109718d51d026e62d53318f590530871e544c0109798e5290757510c540c7952318826e62d50109b58b540431f54952318f593520425d658c430c714e4250a5c6354910c758c544ca5d65cc010b398b548c65f650c4109798f515025e6314940c7150534431d54cc2209b98a50d066c62551108f99253487d0314401097d8d524425e6315032a759052cc2746155120b5984528c65e6395110b358a40cc25f6354742c7551538838c43108329b988540c71f548c510d394d520425d650c41097d95300834e520c410c7951530425c6550d309798f54843566114f10dad4b50506d9609453097d95320ca5e6394041b5185304425f63551109b98b540827b654c03097195214c2cd62d523197597214c38d42108318f59052042d960d093097997304429e64140319758c544826d6215010c795153883545108530c7953308833b54d4121cb550420ca5f6550431b618121cc2d860507309e982534865d6014d218f59250c8754518c5309798f52842786054442a7191328c6786055131d5147214c25f6054f4197d9431882d9600c540d3548320c72e549481097d9530042ad6210c4297d96310429f644ca319798653882cc6255330b5d85544c25d63153218f19153442cd621403197d94319031d540c620b3988508c67a60150219798e548865d60d4d21cb153324ca5c6354420d614c505066d62d521097594424c31f54cc110d3548319031e548c4109b98a524427b60551109758f548829d64d47308f99053c831f54d4d10d60c450486d661d52319758253d065e650c521b3d89410c69f644cb30ba983424825e658c521a7993528c66e62153309759442cc25f650c440b6980540c67b6054d219758e529065d63d50109758e52442da6090930b6580520c6ac6250c43c7552538834c524c9308f992534426f6255131cb95
  | 2 => 0x62d53319ed95200825e6394b1097d96318825e6394241b5987528c66e62d5210cbd50524434f53149419758e500825e63150109e582544871d54cc0109b189534436852c4110c7d52314865d6510c31b3d8941cc23d6414e209798c54842796014c21d3148314425e6590130b6d81410c63c64549108f592524425d650c4209e594400432d5210b408f992500831c544c11097d95214c2786054d21d354a310425c654c110d354852cc27965080109b98b548c66f6548020e3508424c25e65c85309759631882cc6250d329719542cc25f6355021c7d50314874f528c510ce181540423e6495121a7191320cacc6250c4397d8d511025c6354642d598753c425e639401097d96311027960d53219b18954cc25c63550219798c544829f6454530a7d9121cc2af6050842b3d89438c74c53d49419b18951102cc6250d309758e544866e6294d10da54b200426e6214c1097d95424c25c6114d10d5144414c23e65151109758c54042746154d209dd85534832c52905419bd89544c25f6354442ae191100425d6594c208f592534425d63d48109798c504871d540c4108f994544ca5c6354b40d594431cc34f52cc110d5147414c25f6354720b3189418c65f654c431d354b300425e631481097d8d54c433b54141219798c540825e6394d21d31895310a5e6194c409e980530874f53d4910d3949300425e61d4d42ae1814150356619443197997314c31d544c2209758f548865c63548419798f514825e6394d109718d5110a5e6394020d658353c42ac63508429b98b530423e6495132b3189540c6cf6250f30ce153504865e6395121e354d4210b4d53948108f990540425c6550530c7152314423d6414c10b358c42ccb1c54d4d10b318941cc36860548109798f540425d639404297986530825c6354742ab1854210b8c6350842d394d5290359631412197d8d510825f6054c42b3189438c67b6550040b6582524c2cd6215031b3d89430c65e6510a3197996314431c548c9329799741cc23e64d4e20d618f505065e6194e409798f54c865e631414297997414c2756115020d5144314825d6590c31a7990508c65d63943219bd954210a3c6454d209b58a534432f54d4910c7d50534871e544c220975825310b4d520c4109dd85544c31c54cc110d354d529025d63141419718d54c82cd62901308f59253486d960147309718d544874f520c5109b58854cc23e64d4a10c7550430c65f6550831da148505065e63153209b596210835b5314121979845350acf6254530d394a310434c5314941ab19121482cc6254530c7d5130442d6611483197594420c63d64d4c109e983540cb2e5408620b3189410c67960150318f99250c869c635084297994424c26e65c8520c755043cc31d548c620b6181214c25d63951319798c53042db6054930b6181414
  | 3 => 0x3814008020040b0000800000000040003a0ac10011d007803000c4020000dc0801c87068041581f3b41f4880700410000000240003ca60143e0140c10c110201027c00024077ec2b0900014c0311800188020c16e008000e02200487018002b804064001646a050320443a02c0004807010ab030c206c1d028004580003c04190050080b0700d004020084e01c2901c0200048008030980507401028023fc160000606c4a154b600c010080f0141e008e5004290144d0181f00dfd04800058014843a0005e00c040a82500006014070180b0001d050af17800008130002200c870401900c2534c120a00507c0a010020d0000181c0400008cf00901a0100003104000030000005417029c607c66020181c818174040240e0cc00040040d00300047014010500103059004000086b00001038750043000409094080484807c48138050c805000120a40f0000307c00300003841506415000000000a0081001ad9600c520979945348799401013097185538825d6594c10ce150504865d63d50209798f540c35b63d41218f992544425d63942219bd8951102d96015330ce55340042db60551309bd95210865d65d0431c7551530425e6114d109dd95310c74c528c510b6580214c34c52cc110c715031486da60d0930b398a40cc2ac644c8329718d52c42ac6250540d6d8f505067860551218f990520425d63d4a108f593528425d63943419b58b540c25e6314a10c755054cc31e5494c10d60c7504863c645483197d8d52c434f5314910a7590520c6d4614c310cb1535244354510c5409758e5090aac6448720c7d53534866e6214810b3588508c72c5488521b3d89434c2cf62553308f19152c435853d412197d9521cc35a6314141a7d91214c2db605073097d81530425e639432197596310426f62553109758c5050a5f63546209e98054cca5e63d45428fd91534863c6454b30c7951438c66e62d503097d9431082d960909309718553082d661cc110cb5525204356518c630ae18141d034d524c0108f19153486ae648812097d95414c27960d5032ba181214831d548c410dad48505065d6094f21b3d89418c65e6394242b3988540c74f524c11097597300834d53548109e98354cc6ce62153308f993538865e6394821d394831902796094d21b658231c425e63942218f59053c825f6354740a799351cc23e64d4c109b98b548c26f6255110d614f505065d6395310b3189414c32e52106409798f548825c63544409e58054cca6e6295110d314c524432e43149438f990538829f6454b308f592500826d6214c1097195420c66e62150108f992524425c63547209b99742482cc62551309798f548863d64d4e2197994404c25e6514d109799721cc26d
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x3c900000f2c000004a0401400011402870c90000800060040000050160c0000000000c1aa8b10a818e0c64149324c2463b2a6a108543dd54210a31a18e8a90a49865051580214c306b22a42906385150614c110918ed29a842151471550544c2a238aa4292619498560d4f10a18e8a906418e0c54189434c2873a6a529463431c95410c31c1ca83128718d0c73548421062a38aca21261835915214b30a18e6a9085a050c72550540c706324a49946391148614c110ca0a2b00829850c74548520c62cb80caa1063431c95415130a18e8a90659860d65508420c687396a92a46392549600c640a18e8a90a59850c735504208706aa2c42a661431cd5410b20c92a4b00a418e1954580310429238aa821241235c06350842d20c818a200850c7255054cc324a92c018821865516015031a18eaa10859850e73d5042886863aa8421261831506250d32c32a8b00631050c735504248286392a821e61239c46350842a1aea218841950c75508420c706b2a8421661b01883144010
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x1a08825516015031909801d5421083180c875954210b30889801da5350842a0884549601483180c875954210831
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 801
  | 4 => 781
  | 3 => 56
  | 2 => 6
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
  | 7 => 2*((h/1+packedAt s4K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/28+packedAt s4K6 (704+(h % 28)*6) 6) % 44)
  | 5 => 2*((h/295+packedAt s4K5 (21627+(h % 295)*10) 10) % 801)
  | 4 => 2*((h/281+packedAt s4K4 (29678+(h % 281)*10) 10) % 781)
  | 3 => 2*((h/46+packedAt s4K3 (2744+(h % 46)*6) 6) % 56)
  | 2 => 2*((h/2+packedAt s4K2 (360+(h % 2)*3) 3) % 6)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfc0ffffe07ffffe07ff07c3fff83fffde07e3f
  | 1 => 0xfff03fffffffffff81ffffc0fffffffe3f8fff
  | 2 => 0xffffc07ff80fe0fffe007fff0ffc1e03c3f3cc
  | 3 => 0x7ffff000ffffff80000fffe003fc03f0
  | 5 => 0xffffff80000000fffffffffff0000003fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xa5210522312254601654141592a332a8e03615
  | 1 => 0x8448a044244800580a0a840250445500d88ea
  | 2 => 0x30a2934890e905aaaa084ea609e9181b42d34c
  | 3 => 0xa2cb2c712481d6f34d3d02348e739063f403b0
  | 5 => 0xc30c3061c70e18dc71ce7338c0420183bb6c00
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xece8ece8c888c888ece8ece8c888c888ece8ece8c888c888ece8ece8c888c888ece8ece8c888c888ece8ece8c888c888ece8ece8c888c888ece8ece8c888c888, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_40297
namespace PEqualNP.Outside.L_meta_40297
open PEqualNP.Outside.L_meta_40297.Model
def s5K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x4008dd30ed20dc32ef20de32df30
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x39260905654032
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 6
  | 3 => 2
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (i*5) 5
  | 4 => packedAt s5K4 (i*16) 16
  | 3 => packedAt s5K3 (i*27) 27
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s5K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/9+packedAt s5K4 (96+(h % 9)*3) 3) % 6)
  | 3 => 2*((h/7+packedAt s5K3 (54+(h % 7)*1) 1) % 2)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x83fffff81ffffc0f83ffe1ffffc1fffd1c7e3f
  | 1 => 0xfc0fe0fffffffff003c1fe1e07fffffe1393ff
  | 2 => 0xfff000ffe07e0ffffc01ffe007fe0f03e3e3cc
  | 3 => 0xffff800ffffffe000007fff003fc03f0
  | 4 => 0xffffff0000000ffffffffffff8000003fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x88414808c1044401904a20a231509929042615
  | 1 => 0x112291910a2908b041a0d21442a322d21190ea
  | 2 => 0x28a4ca2247505556940964c094d48c1962e34c
  | 3 => 0x72cb1cc4941d6e6b5aec10912739c863bc03b0
  | 4 => 0x430c108718618b8c63319919c0210082db5800
  | _ => 0
def s5Atlas : Atlas := ⟨5,rawDecor 31 s5Pos s5Neg, 0xfaeac888faeac888faeac888faeac888faeac888faeac888faeac888faeac888faeac888faeac888faeac888faeac888faeac888faeac888faeac888faeac888, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_40297
namespace PEqualNP.Outside.L_meta_40297
open PEqualNP.Outside.L_meta_40297.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x80141580142000b007042012b600031004dcc00c00007c218501ffd5007fd43007f4c407fd4200ffc8001fd5300ff08005fc3201ffd0403fd1000ff8c005fc4300ff84003fc5001ff10403fc40017f94c07fc54007f94403fd3000ff88007fe5400ff54003dd30007f08407ff43007f54801fe2101ff90805fe4300ffd4003fd4000ffc4001fd3200ff04003fc3001ff55007fd41007fd4c03fe40007f14401ff2101ff90407fc42007fd4405fc3100ff94005ff3201ffd0803ff30007f94803fd20007f48401fc52007f8c401ff52007f54405fc53017fcc403df30007f8c803ff40
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2641dff4c25111ffe809900bfc304c405fe192a600ffd4f2101df8c8a98abdd309480bfe30c6401bf9825119ff880a9817fc63148057fb126425ff842320dff8c6a8857ff408c409ff320420aff14052005fcc518883fe40d445dff994a402fb0c9320dff886a8813fe658c40bfe31e420eff50221017fe60990aafe62148157f32c4204ffcc651007faa49080bfd324c409fe31c420adf14c52027fe212889bff548c809fe314a20bff98121077faa11089ffd3014809fea08a22bff0815209ffaa09882bfe63d4463fe196a401bf18051025fec9108a3ff3114865fea1ea401bf9815313fda4029013fe314c433fea18a20aff15051187f881a90137f51944077f320a201bf1835305dfac09083bfc3088401bf292a404ff1923100dfcc09902bfe50d4813fe2864202ffccb531a7fec8a9803ff5348401fea90420affd51510fffca92888ffe204c8016fb1aa40aff54b51005fec6a88afff6054815f7a94a40affd4851027fcc110857fe208c409ffb00a22dffd9152197f885a904fff504c457fe082a42fff59252027e86318803fc6154c35ff302a234ff505530c7fc8628806fe608c45f7eb24a403bf191320a7fa8498813fd6394405fea1aa60aff99351007fa6510813fc621444bffa046428ff10c52097fca990806fc604c401ffa984204ff0c721027fc6310813fc6094467ff882a600ff18532137fe851908fdd304c83bff184a20aff14d52017fc61190677d54144037f304a400bf58a31017fc86a980bfc3154c09fe880a20aff95052055fcca99047fc43c8413f6906420aff58c5204ffa61908abfe6094815ff298a41aff841510fffe85288cbfd41d48017eb0ea402bf98c21007f8ca90813fc418c4097e31c422aff5025205ff8a0908137d5114415fea9ea40effd4221027f863a8813ff6214439feb22a202ff8c931057fea7a880bfc53d4c017eb16a205ffc8232057f8c5a880bdf304c409fe18a4204ff84251057f8a9a9003fe6254c01ff32a62009f19521187fa21a9013fe415442fff200a21cffd095108ffe639080b5e53d4c6bfe086a604ffc4321027feca1082bff5414829feaa26200af590510dffca6a886bfe3054415fe286a201bf18252057faa4288abfc3094815feb26a61ddf94251025fecb18802fd6394821fea14420bfb4812100dfcc110813fe41944077e326a605ff1825219ffa20a982ffd304840dfe2804204ff98e51187fc81a9003dc63484057f318a225ff882320effe612880bff328c46b7eb06a60abfd9351027f8621087bfe53944677eb02a60dbf59121015fac7190b3fc3254835ff982a202ffcc232077be6110803ff6154835ff902a22aff54252025fec698857dd308c401ff2926400ff99721005fac6108b7fc42548077f3226400ff94a31067fe6290803df538c801ff1944204ffc4121
  | 1 => 0x2fd64544013fb2a4202ff4c1321a7fcc8a9817fc658c80dfe200420eff8822113ffa2029003fd635441dff9844203bf9935215ff8c0a900bdc538c80dff280422fff90652047f8a81084bfd43c8401fea9a4217bf58051097f8a9908c3ef20d4809fe2884228ff0c452017fa6118803fd618c84dfeb246421ff0cb51015fecaa980afe6394455ff184a405ff10821177fca72904aff64c845fffa14a400ff54a51027fac710803ff52c840d7eb004220bf58351007faa4a889ffe401486bfe106a622ff10b51057fea6a880bff314c847ff882640adfd435106ffa829082bfe50d44077e3224204ffd8021057fac5a982bfc5314409ff884620bff18121025fec1288dbff41d4c01ffb1a4204ffd4451127fca899003fd654c809ee18a6202ff10d3202ffe4129017fc64c8415ffa9ca204ff1062106ff8a890847fe43c8405ff9926224bfd9132015fac718893fd644c81bfea1a4204bf18c510b7fca9188037c5294409feb20a200ff54c2101dfcc8a8813fd658c4075f3244204bf1853206ffec89082bfd64d4469feb22a60afd5445115ffa40a902afe658c415ffa98a404ff50421027f8202882bff61d4c015eb244204bf1923119ff840a982bfc5454c01ffa924202df94f53005f8c4a8897fc508c809ff310a22affd025201df8c929003fc654c8037e306a425ffc4232127fea89902bfd61d4c47ff0826404ff18a31047fa8610813f65114405fe18c6424bf59132057faa7a889efd6014855ff104a40cff90d21027fcc928827fe40c8415fea90a430ff0435202ff8c929013ff608c405fe29aa600ffd4821137fc8319003f5210841fff9944216ffd52310dffe62a88037f5294805ffa1ea617ff10051017fa611902bfc54d44097f3084222ff50751005fac710812fc6408409fe3284223ffd81320e7fca8a8803fe5288409ff32c420bff44121077ba6110817ff631484fff880a413ff18131017fe64990cffc1054c0bffb08a404ff0c551187f841a907bfc43944017f314a20aff14151007f8c4a8863fc321442bff9046207ff90c21027fec91080efc64548037e302a60aff94051017fe63190b7fe425485bff322a40bbfd8121005fac62882bff52d4459fe31aa404ffc4151017f8871902ffe404845ffe20ca402fdcc631027fc211882bfe61d48057e31ea221ff90f51027fa201086bfd305446dff216a604ff9942119ffec0a98b7fd6454833fe210a204ff1802109ffa8098803ff6254c4dff2a46400ff54b21127fc8299093fc414c815ffaa4a204ff0c65101df8c8a8802fd65c8405ff29c6205ff19721027fc8318803fc6254c05ff9846214ffd0531017fc60990d3fc4254c49ffa126402ff94d32107fa21a8893ff644c857fe202a42dffd0d52055fec1a9017ff60c840dff200420aff54c51017fc611885bff428c447ff9
  | 2 => 0x21025fec710873fc42544017fb2a620aff980520d6faa0a8877fc4094415feb20a416f7d0e31087fca910857fe408c427ff082620bfbc81210effca12882bfc5094805ff29c6410ffd5221007faa49908bff43d443ffe214a211ff14f21197fa85a9012fe618c4057f31aa400ffd8951017fc871900adc6348415ff308a402ff50e320a5fac898817fc321484bff3046430f7cc352027fec8108d3ff4154c69feaa2a62abf5825215fbe60a9013ef218845dfe21ca404ff4842115ff860a900aff614c46bfea06a60aff5435313ff880290abfd309480bfe308a40bff94121056fea9a905ffd2014417fe102422bff5415202ff88429003fd53544097e3184204ff58231025fec610802fd639440bffb2c6400ff98951027f8219082bfe5014809ffa884200ff54e51005faca99073fd41544037f306a404ff9805113efaa02900efe644c415fe326a60aff1485111ff8a09902bee5214805bf29aa604ff90531017fca69882bff52544097fb284205ff08021195fac9a9033fc5348465ffa0ea40aff55352057fec5a980bfe304c435feb02a22effcc652007faa518802ff635480bfe30ca402bf18d51157fe2129013ee2148409ff300422fff95252027fa832882bfc509444bfe8846432ffd0f52027fc21108cffd2054c117eb20420adfd405216ffaa8a9073ff645443ffea1ca200b7d8d2115dfac0a9013fc51c8415feb06a600bf58c52057f8a9288bb7c53948157fb06a204ff04121057fea0a904bfd41c840ffe2984219ff90851025fcc32904fff204c405ffa9c6205ff0cb21005fac7a900afc6314815fea98a40affd4a51015fcc729027fc40c8441fe106a21fdf55251027fac528897fe408c81dff1844204ff90621007fcc32900bde53d4c21ffa144200ff54a32057fcc5a8827fe50c8435fe882a20abf1953207ffca710806fc60d4419fe192421eff90e51106faa1a882bf7515440bffb00a401bf18251027f82010867ff4314401bf290a205ff10b21027fac42880bf7314c401feb0aa404ff44251057f8a7a884ffe204c415fe2a0a417ff08051027f821a880bfc438c453fea18a435ff483530d7fec0a8813fd649445bfea12a426ff99232077fe411080bff304c405ee1946200fdc8521017e8629882ffc404840bffb2e4203bf193520d7fc80a8803ff6548413ff306420affd4852025fec11880afc63d481dffa044223bfd8132027fa63108d3fe4254c01ff30a6400bf5942100dfcc0a882bff64d4c09fe32c6202bf18e52027fec528857fc508c409df324420afdd4651177fcc729013fc5148409ffb14620dff10921027f863188a3fe431480bfe31ca402f70c93216efea8a9006fe60d4c09deb24420cff18d2104ffa21908cbfe42d48157f32e422aff8425202ff86410877fe409446dfea16a604ff10531017be61a987
  | 3 => 0xe884a400ff54a2113ffc2029003ff654c401feb2a422fbfd9252017f8649908ffc404c815be280a200bf58a51007fac2a98b7fc6454827feb026205ff0823204ffa41908037e5294409feb2c4233ff501530aff88118893fc424c805ff986a623ff941321affc41a9802ff624c409ff28a4208ff55021027fe8210812fc6588401ff196a20abf19632025fecb1088bff41d44037e302640aff54051027faa210817fc52c844b7fb046426ff5063216ff882a9017ff6494835fe102a204ff14631017fea71909fef20148357fb02a22aff90252027fcc628813fd418c465beaa6a400ffd4e21017f860a9803fe524c42dfe214620bff48121176fca7290a7ff43148017eb2a6201bf18021057f8a6a880bff534c86dfe20ea613ffd0131017fa609888bfd43d4415ffa8aa220ff4835115fba60a9097fc108c809fe18a620affd4153025f8c91082bff50144077f326a213ff14131057faa9a88c3fd40d4815ffb1ea204ff94421007f8c49880bfc314c815fe29ca202f7cc15301dfcc81089ffc1014805fea9c6202ff54d320a7fac898813ff6494467feb02a633ff54153017fe6298803fc524840bff2164214ff99131167fe64a9093fc544c801ff30aa60dff99121097fcc990813ff641442b7eb046200ff986320b7f8a91881bfd2008415fe298a42bbf5965212ff88119093fd414c8013fb2a6419ff50851017fa87188c3fc30d4813feb064202bf98f51027fea32880bfd434c809ff31c4205ff08052027fec710817ff618c8017eb2c4200ffd4a3100dfcc09082bff63d4809fe082a200ff94952027f8c928817ff648c85dfe18ca405ff14821017de651903bfc5088409ffa08a212ffd0f2104dfec19080efe649444bff2846414ff9513109fba6098813fc3188409ffb24620dff909210bfbe6028813ff104c44d7eb246400ffd4932067fcc69082afc65c8415fea86a402ff10d311afba61a982bfd6114809fe084a202bfd8d5311ff8c099002fd618c84dfe2a46404bf98753007fc6428813ff3188415ffa9ca400ffc8521057f8a5a882b7f54144057e31e420eff4c22101dfcc91900bfe434c8277eb02620afbd4952007bec6a900afe63d4809fe8846200ff58d21057f8c9a882bff64d4815ffb0ea423ff44132057fea1a906bfc405440bff2104202ff90e3104fde4190883fc40d4415fe2a2a204ff94451057fea1a9837ff434840bfe3046400bfd85530dff864a882bfc60d4c01ffa8e420aff55051005f8c498813fd5114469fea12a614ffd5131027fe4210817ff63c84075f320a20abf994210f7f86528813ff1088405fe186a62bff501520d6fea0a883ffc4388401ffb126203bf99353007faa790873fd4354429ffa126223ff90132017faa719012fc658c4157e32a4200ffd4521117fc85a8823ff43084057f31c4205ff083
  | 4 => 0x827fd50c8405ff982a629bf590520e7faa8a8813fe648c4017f310a204bf98632107fa81a88affd6054801be32a420af7d4d53055f8ca98803fd53884017e312a630bf58352025fcc2290037f654c827ff3026206ff50021027fcc61080bff434c853fea10a400fdc8621016f8a7a9802ff6154841ef986a223ff981320eff84128803fd6254415ffaa2a42bff84152005fec79087ffd5494415ffa9ea413ff44131017fc869889aff648c809fea0c4200bf98b53057fcc629052ff644c415fe306a410ff152210dffc86a8817fc528c80dfe1804202bf98a32005feca9086ffe6354461ffa06a404ff8c521187fc41a9047fe63c8431ff990a20bff54121026fca2a880afc63484037f3064234ff105530effa41288abfc4094851bf298a417f74c05119ff8c0a98abfe5094815fea86a20abfd805212ffac11900bff438c8097f30ca20aff9485100dfcc029037fd6448401fe990420affd5353097fa859086bfd20544097e30aa600ffd4a2114ffe822902bfc5294415fe292a22dffd095202ff885290d3fc6454c15feaa0a406ff5402105ffea0908ab7d5094801ff32a4204ff8c42109dfec0988afff2054841fe186a209f7cc321027fec110817fe428c8037e3046404ff58c21097fac9908cbfc41d48097fb004213ff90131057fac5a8817fe32c84557fb04a423ff0813207ffc8710817fc60c8409fb1084206ffd402100df8c090857fc208c409ff320a203bf1913116ffc82a900afd63d4c0bff210a40affd4a52167fca6a90d7fe10d4c15feaa6a604ffd463111ff82099017ff6094801fe996a236ffd0b53025f8c2a9013fd108840bfe324642adfd4252005fecb90803fd5394815ff306a600ff59531017fc61a9802ff6348405fe29c6233f74c153057fec1a902bff64d4401feb1e4205ff1805206ffa8490813fc65884037f3046404ff18e51027fecb108dbfe41d4c57ff302a42fff5065213ffa402904bff41c8439ff212a212ff55321017fca7a983bfe40884357eb02a235ffd035305fbe60908bffd4394835ff282a20affd435119ffcc0a987fff4394405ffa1aa600ff54721057f8a929036ff6448415ffb16a21cbfd91510bffa8028813fc108c401ff1924231ffccb5200dfcc098803fd51484097fb00a20aff983510fffc8528812fc64144097fb24620abf99452187ba61a9023fd4208463ff21ea400bfd9632027f8c910813fe51c8415ff320a41aff18151037be6010802fd658c415feb0ea405ffd8e5215ffc40a9003de324c857ffa02a435ffc8353025fec110813fc6014439ffa1aa21fbf59251007bc6518812fc6508405ffa9a6202ff0ca310277ac8288afff305481bffa0a4204ffcc631007fa6428817fe3208415feb1ea203bf193210bff86028837fd5448445fea16a202fbcc932005fec4a8857fe508c455f
  | 5 => 0x972117ffcc92900afe6348405ff192640aff98352015f8c6a90d3fe5454c23ff9964204ff1052119ffc20a980bfe328c463ff98ea404ff904510d7f860a885f7e5014409fe0826224ff55132027fc42108b6fd6454817ffb02420aff583510d7faa0a888ffd604c809ffb1ca20aff59352187fe21a9013fc64084017eb10a220ff88351057fea6a903bfc20884077f3246220ffd035104dfcc410817fe52c8409fe3044220ffcc351005fac690826fd60c8463fe21ea42fffd0e52057fca9a905ffe3014413ee986420aff19352025f8c728813fd518c409ffa0c6229ff504520eff8612882bff5454c01ff32c6416ff55231027f8821082aff60d4c09ffa8c4200ff8c951017f8a719003fd3254461ff086a400ffd4a320cffe842882bfd63d4801feb2c640fff14e21027f8c6288777c50944457eb26a204ff58221007fec29909ffd40148577fb02a401bf18151137fa851900bfc534c815ff298a200ff4ca511a7fc82a9817fc428c819ff9924204ff9455113ff86029013fc108843bef984a202f7cca3202ff86529003ff654c8177eb144204ff58051057fcc3a9803fe624c401fe32a6200ff94921057fea0a8813fc41d4405fe192620bf74c121027fca31889bff418c829ffb226223ff48132027f8a29882bfd601482fff900a20aff14152017b865a9806fe6008409feb04a206f74c02109ffca09882bff54d4805ff29aa613ff10131017be6119017fc209480fff9904226ff5523216dfec8a902bed5214859ff31aa42cff0c552025fcc310887ff32d4413fe1864230ffcc35202ffca41082bfe64d4c2bfe9046234bf59153057fea128812ff64084077e320a40aff1875304ffa819082aff6414829fe2126234ffd0953007f8a499012ff64944037e304421af7cc1510bffe6028803fc528c417feb02420aff14353057faa02900bfd30d4c59ff98aa42bff4c152077fca11082bfe52d4417fe182420aff99352005fac22905fff4014457ff882a402ff0c7530e7fa84a889fdf30148157f328a217ff8805105ffa8090803fd3248427ffb02620fff0ca210a7f8c898803fd32c8409ff314a202bf99753167f886a903bfc4088465ff20ea40ebf58221107ba61a882bff5014815fe29ca433ffc8153025fcc3a9017fc328c801fea926205ffd8232057fca7a9003ff6354865ffa16a404bf19251057f8c7a880bfd534c409fe28c4230ff8c352007fac29900bfc43d4c337eb20a21fff50a51177fc8729003fd6354849ff2126436bf59353087f88510813fe31c8401ffa926233bfd81530b7fc8518827ff50c84017f316a214ff50531017fe87188b7fe5454867ff102a630ffc8352157f8212900bff31d4c017fb12a614ff15131027f88228813ff4194421fea1c4233ffd0153017fa8698897fd208c839ffa0aa204ff58c510fefea928
  | 6 => 0x17eb1ea20aff18b53057fcc5a982bff60d4c09ffb18422af7cc252007faa6a9037ff5448443fe21ea204ffc4351097fe859080bfc304c85ffea14a42dff50552007f8a49880bff328c809ff20e4204ff94621095fac990803fc61548013e32a6402f70c632027f882a8857fd408c4037e3064202f714d53027de4210813be6414447fea02640affd8351057fca9a883bfd2088409fe320a202bfd8d320e7f8c8a8827fe30c844fff100a40aff1515213ffe8029047fe53c8411ffaa04202ffd4d53007fec6a880afe631480bff2946402ff4ca3104ffe61908d2ff6454c15fe29ea405ffd8652027fec628897dd308c817ff0824204ff10651005fac79082bff525485ffeaa4a400ff58931007fcca9900bfd3054c077f3244202ff50f53056fea429003fc5288405fe21aa602ff0c231027f86228806fc6054805ff992a600dfd95210a7fc849882bfc54d4c157fb26a404ff90521005fac5a9803dc6354849ff3226404ff5942102ffe4190813ed2108415ffaa6a22cff90d52027fc20108bfff419482ffe980a220ff84351007fec2a988efd604c819ff29a4200bf59521085fac910803fd31c8417ff1824202ffd0d3106ffe849086afd6594457fe882a409ffd0321027fc82108a7fc411482bfea846204ffd9631007fca4a888ffd504c8157f32a621af74c151027fcc12882bfe63d484bffa846400bfd8532017fc87a9813ff311440bffb264200ff94a5106ff8c890802fd61d4c4fee980a41effcca5100df8c02901ffe530845bbeaa2a404bf98451057f8a0a9827fe20c8401ff30aa433ff94153037fc6010877dd3094421ff2144208ffd082105ffe4090803fe3294409ff880a223ffd41321affa21a982bfc60d4431fe218a225ff50232087fe8710803fd3148457ff202a405ff94852015fcc6a8813fd6008415ff29ea202ff8c1530affea1188c7fc31d48017fb2a6404dfd4451027fe4310813fc608c461fe906a430ff4c352127fa849902bfc50d48077f3224222ffd0b51057f8c7a9013fe41d4415ff2a0a20affd52521affc81a982fff3048455fe904a42aff58252147fe642902afe6294809ef18a6220ff8c35102ffe401080efc648c80bff214a42affcc25205ffe8090803fd6254c09fe988420bff881210d7fa80a880bff3154c09fe20e4202b718d5201dfcc8a9813fd648c45bffa0aa402ff0c23201df8c9a8896fd608c841ff906a203bf9905200dfcc0288037d52148037f302a42bff8c1521affe21a980efe64c8449ffa0a6413ff08131005fac329097fd508c80bffb20a406ffd0021006f8ca99017fc6414809ff10a4202f7cc132007fac3290c3ed20d483bfea04a203bf991520b7fa851881bfe2008401ffa8a6202df14d530effaa12881bff3008405ef9846203bf99252057fea828813fe1014405fe29a6200ff5
  | 7 => 0x80460102890901c5240700207c00006800322000368210060302280b79e01804001042318850222bc01813000000698040000120100001211e01c0300700a000ed8f50020280402600a0f4280291f800c00044006000008181aa77c0387d00484c0680b0000803e8050001800080500e0200707f5fe018090f80040480000700a0200703000a000000040100340480206e03c0481d00a000030150b8020090060c80f80701500a0200000d006020058413f60000021600e9700407a000028ba80c054060030150000ec003840000000a0000040080b80900a0002400f44209c0700107a0882c84109018c148070003280b8dfab89500480900c0041f803012188033852340100b80303e0740000203a1e80482b2f40200100c00e0000000e04e0800625c03801c290000000380f800018e680101b0ee0001f0270000000001701008404032406008100e30ec06814812004000000150000440002001402401033028018038db0040340000600c0e8078000020204a01c0022240011501c00800800058018080000080700201201400c01006008000000120000200100817d0810b82403a0a8000070040442d8010000083380f006010018110000000781805a0281181200a01c0880a00000c019381020040400c0a80000d0010000dc0d8000280881b85600c5bc0003313a00806c0a03e0000181e0740803300200e0000000302e06006002036194228210b403c2a00b1a82fc0080f0001100418a040000060000c215419cc50040740001700007c2d82e0102480005f00007c988062f89880003701c0c5d782902a0314784400e150020003f602406099000dac1780d00208c26860004008008180064901203100003006cd402c0004880100e02c060730180501b00601c0182a8a100c0340280417c0617e8090480341c2150660002180b01402c020200020000480300c010040000360300001228e00c0200700401802003fd6394867ff202a600ff5453115ffca0a901bfd3008435ffa02a20aff953530edfac128813df318c419fe21a4229ffd0852025fec82882b7c5214405f61946404ff9453114ffc822904bff54c843bff904a20aff18752017f865a989bfc418c839ff322a204ffc4021027fe6210806fe60d4409ff3244204ff98a31107fa61a8813ff418841bff2a24227ff8c052057fea1290d7fc40d4c35ff102a20abf99521007bec690806fc608c415ffa98a20abf99632087faa91082bfe50d4c11ff2a0422dff50d52027f8c61081ffc430846dfea0ea604ff58a31055fec9a980bdc438c409ffb04a236ff10b53057f8a028887ff31d4409ff3046200bf59632027fac91086fff3254449fe3226413ff481310effc4128813fd518843bffa04a20aff5835202ffe402909fff3014809feb204202bf98f2104ffc219085afd648c40
  | 8 => 0x94f88132640000081a00000800000026180228470100d0028000822541400200000805804082048000200ca0a40c
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc70d8d210576f7254852006df30d855207fcc324ca210567e7119521015dc73549320067c6419532026ee219885102cff74d8f211d6df608ca31005de7618d21006dc7359521006de70d8d520067f6554932054ff76d4a3102d7f7254852056be5059051006f641d85521cedf6218d21017ce728ca31054ff7654932006ef6294951054ff76d4c21004ff764c8510267c51596310067c50d9521006dd30d9521006dd634c8511d6dc31586320dedf3059531207cc52d8d52014fe7359421004ff7158b53006df6318552004ff7458652004ff7459421024ff7159421004ff7058c520057d759853201cfe7458b53005f7714c921056bd5059051206dc52d8d5202e7f64d4a5200cfe70d9532005f77154d5101cfc7458f21004fd768cb5108edc4358f210067e5059721245dd708c9321e76e6294a51006dc6398552006ef20588511767d72d9532025f67194951005dd7018d210dcfd76545311e67e51d97210567f74195210067e50d95311767e30d9532006ed6218931006f71058452006de50d8d21004fd7654e21004fe76d452102cfc74d9632004ff764cb5100cfe705875202f6e62d4a52006dd30588510277651d4531004fd70597210067c74d95320067e42d95210567c6594a21006dd10d8d52006df6354921006df3058652004fe764c9511467c32195320067f71d9532024fc7558f51024fc7558b51006be3059051004ff7058e52006dd50d8d210067f4119532026be7159221006dd30d8d51006dd74d8d520067f7559532004df70d8d521767f659493203f5e53d4c21006dd30586320067d6554c21024fd73d9531024fc7198a31066de63d8d2100cfc7058f5201cfe7459532205df70d4e320067d60195320067d41d95210f5dc7354a5101cfc7458b51004fd72d8553014fe7359521006be735905102cfc73d9721006dd70d8d210067f1019532006ef6214931005ec72545211767e73d9532024fe76d4921026de3158e21004fd71d8953027e7724842108edf3158f21004fd70596311df6c21195210067f50d9532004fd75d8f21056be5259051006de30d8d21004fd74d8931006ed6254a510567c701953221e7d6014a510567e6519531166de43d8d5202eee3218953006df3058a51006dc42d8d52004fd70596210567c655452102d7e72949520de7d535963102cff70d8f2125f5f3054852026bf3159221056bc5359051056bf50590511757f7554e52006dc41d8d5208ef631d8532166de63d8d52054ff725942100cfe7059621026bc10592212657d7054852006dc6518d21006df63949210067f6594931006bd7359051004ff7058f210f6df3058e510567e65547210267f755962114ebe6414a210567f7419532004fd7694a31006ed2018953004fe768c951005ef725855302e7e525972101cfe74594211fddf708ca31
  | 1 => 0x4a520067e74d95320067d3019521056bf5259051066dc6358d210067f755953102cff74189311465f30195320067f41d9521026bc5159221025f4714ca210567c5358c5200cfe70596310075d30d953221f6d2014a5120f5f3094851004fd74596310057c75585320067e4019521006ee20d89310067c658c92102cfc7258652054fe75d8532004fd7498b530067d65d47210567c65d4d21026f46198652024fc764ca21057775154a510067f65d45310067f32195211767f30d9532006bf705922100cfc7058e51006ed2058452006df3098b510067f65d493202cfc7258c21004fd70d9531006bf3059051004fd7614931054fc7558f210057e7598532006dd4358c210547e76d9532004ff74595320067d4019521006dd71d8d52006de54d8d5201cfe7459631004fd7458b51005ef7254521004fd745962100cfc70d9521006ed628c851016de634c851005dd73995210067d54588511a6be6454e211e57e71d4a5202cfc74988510067c32d9521006f771595210067c20d953201cfc74596210047f7558d21004fe7694931025f671d4921006ec42d8953065f57198931004fc764c951015dc7354a32006be2059221006bf73590510067d4319521026dc3158c5100cfe7058c52024fe7198a51004fe76d4d21006f410d8552016dc634c5210b5dc748ca3121f6f2014a51006ed2058851064ff7358d2102cfc73988510067f71d9521054fc764cb51005f77154e51006bc20590510567e7019521004ff7058753024fc7654e21166df31d8d520567d7219521004ff7459721004df735952100cfe7098b530076f2019521066df30d8d21016de6354c210067c40d9532004ff7259521016de618ca31004fd768ca510067e10195320567e6514a3101cfe74d8532006bf7259051014de76d8d2100cfe7058a510067c654c9211cfce2118d210567d7119532006dd6418d520c6df3258c510057f754c92102edc6358f2102cfc725963201cfc74588510067c71d9532006df30d8951006dd3058c51006df70d8d52004ff74596310067c60d9521016dc638c95121f5d3014a51006ed624c8510069d30592210067e50d953202ef576c8621006dc20d8d211667f5359632006ef205845224edd60d4e32004ff7458c210567d7614a51004ff735962102cff768c85102edf628c932166de53d8d520067d6214a51006dd72d8d521d6df6318532006dd3058753026bc7159051005ec7258d510067f64d9521006dc71d8d52026bd215905101cfe74d8553006dc10d8d52006dc40d8d21006df6358552004ff7159521006df7358851006dd6018d210267c5159421006bd6454e210075d301952101cfc7458d2101cfe74588511e67f10d9521006dd6354e521467e31195320067f2019521056bd5259051004fd7459721066f63158632004ff70d8953006d
  | 2 => 0x6df63c85210067d41195210047e76195211de7c511895102cff74189511767c53d9632006dd30d972102cfc7258e510567f54588510067d50d9532024fc7158e21026ee729885102edd73d9632167cc3254932004ff70d8553004fd705863202dde728c93202cfe72d9521006bd73592210065f30d95210067c60d9532007757194a51004fd70594210067f654c52100cfe7058f510567d701953202cfc725875323edd608c932006df75d8d21176ed3298b5301cfe7458b51026bd515922102cfe72d95311457e7354852014fc73d95210067e7619521024fe768c851006de6418d212657f7054852004ff70d8951006df3098851006dd305963200cfc70d89511467d3119532176dc6394921006be755922102eec42189510267e5159421014fc73d85520567c6594931004fd7459421026ec2198a51006ef6254951004fd7598a31004fd74d8d21006dc74d8d52006dd42d8d21004fd74d8d52006df43d8d2100cfe70d8d52024fc7159632004ff7458f2102cff70d9721004fe7654d211e67e21d9521004ff70d85320057c754ca2100cfe70d8953007d463c852100cfe7059531006ec62d49310067e10d9521004ff7059631016de6354e51056ef5298b51014fe7358652006df63d4521004ff70588510067c655853200cfe7058b5302eec2018931006de74d8d52007e55248421025f672c8521004fd7058c21054ff76d4d210075f5418d52004fd70d89530047f7654852004ff7258e51056df5358c51006de20d8d52004fe7614931004ff735875202dec725472101cfe74d953201cfc74d853202cff7498851006df6354d52014fe73d9521004fd7018951006df42d8d52004fd7458d2100cfe7058e5202edc3258c52166dc43d8d521bfd7304842100cfe7058851005df70d8d52004fe769492101cfc7458e5201cfc74d8953004fd7459531004fd7458f510067e70d9532006dd3058c21027e672c8621005ee72d4521026dc3158c210076d20195211e67e31d952107edc5358e211765c63949520067f7558d2102cfc7598b53004ff76548210277651d4521005ec724c5210567e6194a510f6de4358e51014fc7558b53006ef6298931005dd731493102ede3258c210057f754cb5102cfc7258f5100cfc7058e5202cff7418953006df63d49210ddf57199531004fd74d8953006dc54d8d21006dd64d8d21006dd3098b53026f676c8521026bc215922102cfc7498a510075f658c932026bf51590510075d5418d52006dd3059621004fd70595310576f5254e520067f40d95210067f60195320067c64195210067d54d952101cfc7458652025f67194a511de7c311952100cfc7058a31004fd70d89510067c54d95320067c30195210567d71195210def63158753004fd7459521004ff735865202fe65248421024fc7158b5328f6e20d
  | 3 => 0xd76d4d210067d54596320557c7014a51066df3058a3102e7c5259721004fd72d8d51006f56118552004fd74587531e67f6594a21005f571d4a21004ff7558a3100cfe7058e2118edc63d4921054ff7654a210057f7558d21006ec42d89510067e64d9521005df7359521024fe76d4c210dddc7358951006dd10d8d2123edf608c932006dd30d893108edf30d8532004fd71d8d5201cfc7459531174fe761953207edf3058e21006df3058b5127d7d74949521e57d7194851004fd74d85520567f609485102e7f65997210067c6019521006bc3059221024fd73d8931004fd7058f52006dd74d8d21005ef725472102eef2098a51065de76d8d21024fe76d4a3108cff764c821016de62d4e320067f6558d210567c7019521024ff7158c210567c6554932005f571949511d6de41d8d2102cff768ca5101cfe74d96320067f6419521014fc735942102fcc3294932014fe7358b510067c41d95320576f5294951006dd3098a511e67e6194851166df3058b5300cfe7098a51004ff7058b51056ef5298851005df7358552024fc76d4921014ff764ca21026f46198632006f641d8532176df30d95320067d60d952102cff7498a311de7f10195210067f74d953222f5f3094a510067c42d95320de7f5359631054ff76545211767f72d95320067d65d4c2101cfc74d8d21014fc7654932004ff7058f51006de64d8d52024fc7654a31006dc64d8d5201cfe74d8d51005df73548210057f754cb21006bf20592211d6dc658ca31004fd7459532066de43d8d21054fc76d4d21005ec7254e210067f4019532006dd638cb510067d201952101cfc74584521467e3019532024ff7358c21005ef7258d510067e60d9532056be75590512775d3094952004fd70595210573d6494851004ff70d8d52024fe71d9532026bf2159051056df5358f51014fc7558753026be51592210267e5159631026ee2158a31024fc7158e51014fc73d95310057f7558931054fd72d8d520f4fe76195310067f54d9521006ef205875202ef4215865203edf30189311d6dc41d8d2102eee3298b530067d70d952102cff74d9632004fd7058f210067d6519532166dc6354921004fd76545210557d76948511d6de31d8f21006dd3058f510567c6594932004fd76d4c211467c53189530067e64d9532004fd7458a51004fd769972101cfe7458753014ff7658f21006dd305875202edf7358f21006df30595210567e70195321efd530c86210567c7319532006dc42d8d21005df7354531006df60d8d210f6df30d95310067d42d95320dedc32d8d510f6de5358e51006df305972101cfc7458a311e76e21d952101cfe7418931006f56118532024fc7159421027e6215472100cfc7058752006bf7059051206dd65d4e32055ee72949520067e42195210267f755942100cfe7058f52
  | 4 => 0x47210075c6394952025f776484210067e71d9532006df6398552027e66248421005dd7018d520067f6554921005ef7254c21056df5358f52005f77154a510567c5198b51006de54d8d2102dec724c721136be648ca210075c658c932026bf31590511d7ce628ca31006dd3059631004fd70d89310067e30d95210067d50d9521056ef7258b53166dc30d8d520567e7119532006dd6418d2102edc6358e520567c65d45311de7e31195210067c74d952101cfe7458752176dc53d9632006dd3058f520067e63d952102cfe7258c2102cff70189310067c10d95320076f5294932024fc7158a511b6be64d4e21014fe7358851026bd105905107eed32d8931006dd3058f2101cfc74d8d52004fd70d953202ef46158652056ef5258b510075d3019532066df31d8d21024fc764c851006be725905102cfc7418953006f76198553006de65d8d21005df7354a5102cfc764c721006dd30d8553006bd7059221056be5359051026bc1059051004fd76d4a31014fe7359721004ff74596210067f4019521024fe7158c2107ddc7354a2100cfc7058f210567d76d4a52006dc75d8d21004ff7458f52014fd7558c5129e7d64d4a52006ed2098a51006df20d8d520067c53d9521025f4714c9210067f65149320067f6514931004ff7359521006ed42189310567c6514a21005f57194a510057c754c921004fd7098a51006df74d8d5210edc63d4521066de53d8d21005dd73d49321e76d6294a510567c65d493202cfc76d4521006dc74d8d21004ff764ca510067f659492102ede3258f21006dd6354e511775c32d95320067d651953100cfe7058753004ff70d8931026bc31592211d6dc10d8d2102ef7619865202edc3258c21006dd65d8d210067c201953202ede3258e52005ed72d4521006bd2059221146dc5318953006f410d853202cfc7418951126be644ca210067f4119521004fd7654f212957d70d4a52014fe7598b5301cfe74d8d5208cff7158d21026de3158c510567c74195320077765c852101cfc7458f52004fd7198b53006ed621895102f6c4254852004fd768c9510067f50d9521006bd648ca21056bc52590510067c3219521004fd74d9532006f56118553056dc5358c52006df75d8d52026ee7298a511dd7d7614a511fddd708ca310067d10d9532006bf3259221006bc7059051015dc7354a31006df6314921005f77154951006bd64d4e21007d77348421004ff7058f52004fd7058c51006ed20587520067c40195320065f65d8d21006bd30592210b5de748ca3100cfc7098a5100cfe705845202cff7498a51024fd72d8d210067d62948511d7d6718ca311d5dd718ca31006de60d8d21056ef5258b53006dd3058e520067e41d953228f5d30d4a52026ee7298a3102e7f6454852006ef42d8953004fd70d8532006bd644ca21004f
  | 5 => 0x557e729485101cfe7458a3110df7715953110edc3258f510067e6419532014fe7398a510067e20d95320067c54d95210075d54d8d52016de638ca51056bc7559051004ff7258c51026bf10592212157f74948510069d30590511476f3219532006df71d8d210567c731952101cfc7459421004fd7458f210567f72195320057c755893102cff768cb51005df7354a320067d4219532024fe7598b51056bd53590510067f30d9521004ff7059531024fc7158f521c7d530c85210267f75596310567f711953200cfc70d85521d6df72d8d21006dd30d8953006df6018d21024fe7614a31014fc7654531006be205905118edf3258f5226e7d6454852004ff7059621166dc31d8d521dd7c7154852056f751587530067f65d4921006bc50592210067d72d952102cfe72d9632006df42d8d21006dd64d8d5201cfe7458f21066dc43d8d210576e729485108edc63c8521004ff7458e211767e6394851006ef6298953004fd7058e51024fc7158e520067d74d95320067c6019532006df6354d21024fc7118931146df301895301cfe7458d21006f76198532006de20d8d21004fd74189311df6e21195210067d74d9521004ff715953202e7c655972107f5e53d4e21004ff7058c210057e76195210067f5059621006dd72d8d21004fd7098851004ff7058a5102eec5298b51166df32d8d520067f64d95320067e54d95320547e76d9521004fd7098b511767c43d953202eec62149311776c32d953201cfc7458f51006dd20d8d52086be725922126f6f425485202dec7254e52004ff7058a31004fd7058a31014fe73d89510067d505845201cfe74d89510065f30195210067c654c5211e57d7194a510067e74d9521004ff7058632054fd7318953004ff7058b5302cfc768c9510067c40d9521024fe76d4e21006f76198552004ff7159632004ff74d8d510557c754cb51066de7618d2101cfe74d8d210067d6019521004fd705875300cfe705942101cfe7498b51014fe76d8d21004fc7654931026bd7159221006dd3058d21005df735493210ef631d8553056f751584521767c73d9532206dc51d8d52004df73588510075f30d9521004ff7558f21004ff745963218edc3158f5201cfe7458c5200cfe70d95210067f545963202ef76198632056bf7559051024fe71d895300cfe70d8d51024fe71d9521146df3058c5200cfe7058e51026de3158c211de7e2119521014fc73584521767f31d95320567e651953207eee32d89310067e1019521005df735495100cfc70d9531006dd30594211767e43d9532015dc73549310567f505845208edf30d8f21006ef7259521006ef4218951014de76d8d520067e50d9521026df7358c511767f43d9532207cd72d4e3200cfe7058f21015dc7354531004fd70d8553026ee2158851004df70d8d2102dee72d
  | 6 => 0xc20d9521006ee2018931015de7314931006dd3018951006dd3098a3101cfe7459721026bc21590510067d65d4a2100cfc7058e210065f6518d21004fd70588511c7e520c8521005dd73d4531024fc7158c51014fe7359621004ff745953102edc3258f21004ff74d855300cfe70d96320575c5354d5100cfc701895102d7f7654852056ec5258b531e67f6094a5100cfc7018953004ef72595310067e4119532006bc7359221006dc70d8d520075f54d8d52025f47154a51026be7159051006de42d8d52165de76d8d52024fc71d9521004fd75d8d21004fd74d8d51004fd7058b53014fc76d45310077465c85211d6dc21d8d21024fe7198b5301cfc7458e51004ff7358b51006de6018d21005bd74986320567c65149310067c7558d21005f571d4921146dc63149210057f754c851026bc5159051006df4358c5200cfc70d8f21004ff7059632004ff74d95321467e4319532006dd41d8d5202cfc7398a510065c65d8d21014fc7359621004fd7614a31026bc7159221006ed62189530567f70195320067c41195321776f32d9532026bf71592210567f7319532006dd43d8d5202edc3258e520067d64d952102cff7358c520067f659953218def7259532054fc7558e21005ed72d47210573e6494851006dd30d8d52004ff70d9521006bc32592210067d54594211467f3019532014fc76d4932004ff74d8931026ec2158a51027b564c8621004ff70594210075f65d8d21024fe71d96321d6dc51d8d21006ef42d8951006de74d8d21004ff74d8d520067f50d972102ef72158452006be7059051054fe76d9532004ec725953102f6e42d4a520067c6558d210067e601953202eec5298851005ec72595310f67d53d9531006de40d8d52056df7358f51006df7359531015de728ca3102e7e5259632176dc6394952004ff7458d21004fd7458e21006df6418d52056dc5358c51014fe7318951006ee42d8931004fd764ca5102cfc7654f210067d71d9521014fe76549320067c42195320067e6419521004fd76d4f21007d47348421004fd7398a5102cff73d953202ef721586321e67c6394a51015de75d4e320057c754cb210067d50596210067f65d4521024fe7654e211de7e5118951054fe76d95310067d6554a2100cfc7058c21025f47154951176df30d96320065d30d95320067f65d8532004ff7558d210dedf30d8d51004ff7158f520067f65985320067c5359621026ec2198a310dcff73595310067d545963101cfc7458e210067d70d9532006be7359221004fd7058b511467f43195320067f42d9532054fe7518931025ee72c8521006dc7358851005ec7254d52006dd305953202fe720c8521006ef20d895302cff7098a51024fd71594210577661948511767d53d9532004fd7518931004ff73594210547c7558d211455c7354852
  | 7 => 0x8851014fe7358752016dc638c851024fe71d8d21004dd70d8d5202cfc72d8d211de7f6514a21004fd73d9521004fd7654a31006df41d8d5200cfe7059721004ff7558e21014fe76d8d52006dd75d8d210067c4019521166de72d8d52004fd74588510067e43d9521054fd71d8d51165df7018d520dedc6358d510067d2119521004ff70d8d21006df20d8d2100cfe7058b510c6df3058c51206de658ca311467e5358c520069f3059221004ff7458b510dedf3058753006dd40d8d5208eed3298a3118eee32d89530567e6554c21006dd6018d5202cfc74d8f21014fe76d8d510067f60d9521004fd73d97210075f3019521014fc7654d52004ff7458e52026be1059221006dd3059531005bd749853202cfe72d8d51026dc3158e5101cfe7458a51024fc7158c211e67c41d9521004ff74d853202ef4615863202eee72d8f2121f5f3014a51014fe7358a51006ef2058a51056ec5258b510567e7319532014ff7258c21004fd7058752004fe76195210057f754c821287cf5218d52005bd74986520557e7294a51014fc75d8d5101cfc7459521024fc71595321767c5358e520067c10195320067c42d95210067f5459421054fc7654521006dd638ca510067e73d952102f6f20548520057f754c951056f7515875200cfc70d96321767e53d9632014fe7654531006df30d952118edf6218d522357f7494a5102f6e52d4a3201cfe74586520067f5459631006df43d8d51004ff7458752206dd76d4e320567d741953200cfe70189510567c6554921004fd7058f51006df30584520567c741952102ef571d9721004fd764c851167cf3254a32006df7359521006bc7559221004ff74d95210067f65c8521006df73596320067c70d9521006de6518d21026be3159221026bd5159051066df3058632006f541d85520067e63195210567c651493202eef2018951004ff7058d210067f73d9521006dd3058a51015de73d493225f5d305485200cfe70988511d7cc21d8d21005df70d8d21004fd7058652006dd3058e5100cfc7059631024fe7198a3100cfc7058b5301cfc745953200cfe7098a31006f51058452006df10d8d521475c3219532024fc7654921024fe7694a31064fd71d8d21065dc73549210067d6554721004fd76949310576e7214a510067e3019521004fd7498b510067f6554531024ff7559421006df3058851014fd7258c211e67e5198b51006df6354521004ff70d9532006dd4358e5100cfc7058452165de7398552024fe715942100cfc70988510067d10195320567c65949210067d42d95212075e65d4e32004ff74d89510067f43d9521026f661185520067f65d8d21027b664c86210567e74195210067d50d972102eee7298b511467e5318953006dd6518d2102edf7358c52004ff7059721057775154e51005ef72595310067
  | 8 => 0x2cfc7398b51006bd3059051164fd76d4a32015dc73d4a3200cfe70586320067d505963100cfc7059532146dc4358c5200cfc7058d21006dd3098b5100cfc70d8d520067c6598532004ff7458f510f67f53d95311d7cd628ca31006dd30189310567c711953202cfe7259632024fe71596311767d43d9532004fd7018931006bd2059051006df30596210067f4219532006de40d8d21006df638c921005df7354a21006dd54d8d52066df32d8d2101cfc7458a5100cfe7058a31006df65d8d21006de10d8d5202cfc7258e52006dc64d8d21006dd70d8d521e67c10d9521006df63d4d210067f70d9532006dd40d8d21004ff725953102e7e52594211757e76195320567c65d4521176df3098b5300cfc70596320067e201953201cfe74d972116dbe749855200cfe705963203edf3058c211457c735485200cfc70d8553006bd705905102cfc7258632006ef20d8951024fd7318931206dc50d8d52004fd7458c52006dd20d8d2100cfe70d89310567e65d472125f6d20548521775f30d9532166de7618d520067c73d9521006dc6018d5201cfe7458632006bc3059051004fd75d8532005df7354a31206de658c932006dc63d8552026be2159221006bd644c8510075d65d4e320057c7558d210067d5458a51054fe7598a311767c30d95320067f5059421007d5718ca3101cfe7458c210067e60d952101cfe7458f521767c63949520067d6594a31146df3158c520067f765485200cfc7098a3102eef2098a310075f63949520567d7319521014fe7358452004fd7058452004ff73597210067d64d95320067f6514921004fd70595320057f754ca510067f5059631006dd30d895102eec42189530675e53d4d21006dd71d8d21056dc5358f51006df40d8d521467c4319532004fe76549310067f3019521006ed2058a51006dd634c72101cfc74d8d5102eee3298a3100cfc70d8532007cf20d8d21016dc6354d21006df634c92102cfc7259531004fe76d493102e7c659963202cff7694a310067d10d952117dbe7498652054fc76d4931006ef3218951026ef7258a511476c32195321767f73d95320067f20d95320067c65d853201cfc7458632004ff72596310067f6419532006dd3058452004ff7358851006dd30d85520075c73548520067c2019521026be5159051026df7358e210567c65d4921014fe76d4531007777548421026ee2198a5101cfe7458f5101cfe7498b53066dc30d8d2101cfe74d8931006dd30586520067e7619532006bf205905100cfe7058c21006bc73590511e67e41d9521004fd768c8511467f3119532056ef7258b51054ff7659632014ff764c721006ed2098a31004fd7018953006ed2018951026bd31592210567c52588511d6de51d8d21166dc535963202cff7498b51004fd7654d21005dd73d4a31056ef525
  | 9 => 0xf74d8d2102cfe72d8d21006de42d8d21005dd70d8d52004ff7458b53004ff70d9531006be5059221006bc5359221004fd7418951086bf725922117ebe6494a2101cfe7458e510057c754c821007e552c8621006dd41d8d210567c655453110edf3058f51026f762c852102ef421586320067d42195210067d64195211cfcc2118d21054ff765472102eee6294a51057766114a51004fd7458e510dedc63545210067e53d95210567d7219532006f541d85321efd730c862102cfc73189510dedc43d8d5102cfe7259421006bd6454a21004ff7058752056f451584520067c63d95210f6dc3258e51006bd5059221174fe76149320067f5458a5103eed321893101cfe7459521006de6018d52006be30592210067f4319521004ff7058e51004ff745885100cfe7059521135be7498632006df30d97210067d50594210067f75595211767d30d9532014fc764c521024fc7158a3100cfc7098b5102cff7098a31006de71d8d5200cfc70189311de7c6314a51004fd74d8f2102cfc76949310067d40d9532004ff7558c2102e7c6559632024fe7654c2100cfc7059521004fd7398b51006ec72595310067c65d8d21056ef5298b53006be70592211bfd53048421006ef32d8951164fd7699632054fe75d8d210567d73195320557c7558e52206df54d8d52017cf628c9320067c43d9521026bc3159051004fd7458b5302cff7614a3101cfc7458c211767e6394a5102fe652c86210557c754c851006ef7258d21004ff7158c52006bf7559221004fd7458c21006ed20d8951006df6018d520067e54d9521166df30596321767f32d9532007cd20d8d21006dd30d8d2101cfe74d8552025f47154d51026f6611853200cfe70d8f21004ff755863200cfe7018931004ff70d8552004ff7458452006de50d8d52006bd6494a21026ef7258a3101cfe7458452004fd74d972102cfc74d97210dedf31d8d510065c6518d2101cfc7458b53016dc638ca21024fc7158c522767d60949521cedc3118931004ff7058652004fd76d48210067f6518532166dc6358d521767e32d953202cff7498b53006bd72590510557f7114a510075f6518d21004df7359532006f610d8552014fe7398b510067e40d9532014ff7654e51016de638cb51006dd43d8d2100cfe7058d211767f53d9532004fd70d8f21024fe768ca5102fcc324c821065de7399521017d6618ca310067d20d9532027e42154521005f77154a21004fd7118953026ec219885120f5d309485100cfe70d8951014dc73595210067f31d95210065c658c932006f77159531005df735493102ef571d8f210dede53d8d51006bd648c851024fe7694951005cd72d4e321d6de71d8d21006bf3259051004fd73988510067f6599521004ff74d8552006df70d8d21056bf53590510075c65d8d210066d6294a51
  | 10 => 0x952101cfe74d8f21016dc634c921004fd74d95310567c6514921004fd70d8d52004ff7058e2102cfe72d8553004fd7058e21004ff74d953108edf3058f210567e65d4c210576f62949520567c51584520067d60d9532026bf10590510067d76948510067d6294a51006dd3058e21006bf3059221006de30d8d520065d30195320067f10d95321f6dd608ca31014fe73988511de7e4119521006bd64d4a21014fc735972102cfe7654f21015de73d4a3107cfe768c921024fc76d4e21174fd73d9532054fe76d952102e7f62949521d5de71d4e32056ec52588510067d1019521006dc60d8d21006df64d8d210077475484210067c50d95321e67e71d952122f5d3094a51054ff76d4e21004f7764842128f5f30d4a52014fc73d8951006dd30d9532056bc50590510067e70d9521006de75d8d21004fd7098a31006df7359532024fc71d8d21006df639495207cff7258d2100cfe7059532006ee624c851005dd72d4e32006df64d8d5201cfc74d893100cfc7059421054fc7558d2103ede4358c21026bd71590511775e5358e52006dc6358552006dd634ca21004fd70d8552006df71d8d52004ff70584520567c5398b5307edf30d89310ed7e7014a510557c754c95102eec32189511a5be7418553054fd73d8553166de75d8d520067e42d9532287cc5218d52006bc20592211d6df10d8d2100cfc7058f51004fd7058d2116ebe6454a21006dd3058b5300cfe70d8d21026bd2159221206df50d8d5200cfc7098b53005bd7498552004ff745875302ddf708c932056f77158753054ff7654531006dc50d8d210067f5018951026de3158e51024fc72597210067e4319521025f576c8621004fd73d8951006dd3059721006dc6318552006df6354d51027e762c852118cff7654a32026ec2158a31056f77158752006dd60d8d5208f5e53d4f2102e7c5259632005ef7254e21006ee6254a51056dc5358f52006dd305952101cfc74597210067c50d953100cfe70d972102cfc76149310067c505972102eee72d9721006ed20d89530067d41d9532006bf50592211767c31d9532004fd74d8553056df7358f5202eef209885102e7e625485201cfc745875201cfe74d89531de7c4119521025f47154e51006df3098a5102ef42158452054fe75d8931014ff7658e5202eee3218931064fd768ca2102ef77158452006dd30988510067e53596210065d30d9521014dc7358851026df7358e510067e20d952101cfc74587531767e5398b530067c4219521004fd75d89312157d7494851024ff73d95310bd7c7094851004dd70d8d210067f42d952122e7d6094a51005df735895100cfc70595310067f6019521056f451587531765e5358e52006ef72595310067f6554d2102d7d76d4a52006de41d8d52054ff76597210067c65c852108ddc7354b21004f
  | 11 => 0x5f7714ca210067f40d9532014ff7654e520067e40195321de7f6014a510067d54d95321467f32195321d6df638ca21004fd70d96321667d5359632016dc6354d52004fd7098b530567d7019521006dd30d8f21206df52d8d52054fc7558632006de70d8d21066de72d8d21004fd71d953200cfe7058c5120e7d6094851004ff7654a31024fc7654951007cd2018d21006dc20d8d52006df3059421014fe73d85520067f65995310067d2019532016dc6354d51026ee2158a5102cff7098b53005f7715492118edf3058f521d6dc71d8d211467d3019532006ef6298951056bd75590510067d5058652006bc72590511467d4319532006dc65d8d21006dd54d8d210567e6519521004fd72d9531026df7358c21017ce62d4e32015de73d45310075c6518d2102cfc7498a31024fc76d4c210567f7219521126be644c85100cfc70596210067f41d9532004ff7654d21166ee3258b53004fd70d952102f6c20d4a52006dc40d8d520067f31195210067d54d95311767c32d9532016de6354e520567f7319521054fd73d89531e76c21d952102cff7098b5103ede5358c21006df40d8d21006ef2058a31026ee2198a310dedf305963102eee4218931004ff7358a51004ff7458c520067f6554521026bf7159051005df7354921024fc7159621016dc638c92100cfc7058c52004fd74586320067d5459721026ef725885100cfc70586320567e6554a21054fe768cb51065dc735952102eee628c85101cfe7498a311465c32195321467d3219532006bd725922102cfc7498b51016dc63d4d21054fc7558c21006df6518d210557f7414a5110cff7159531004ff7058c51006dd628ca31006ef62d49311467c3019532006ec20d89310067f20195321475f3019532004fd7458e522775f309495210edf30d8553024fe7118931006bc32590510567c639485100cf676c852101cfe74596321de7c1019521026dc3158e21004ff7458e510057f7558532005de7618d5202fce728c932006dd3058b51006df30587520557f70d4a522357d7494a51024ff7358c511757e73d4a520067d65195210076f52949210bd7e7094851004ff70595320567e6594a31024fd7158c212257d7414a51006df41d8d2101cfc7459632004fd7318951004ff7458c510067f5058652006dd3058a3101cfc7458c51006df4358f5124edf60d4e32004fd74d85321e67c21d95210067d5018951004fd745865207edf3258e2102e7f7559721004fd7654c21006dd50d8d52165ed72995320557c754ca51005ef724c521004fd7058a51004ff7158e52176df3058e52006ed2098851024fe7118953006df74d8d21025f47154a210067d6419532006bc7059221004fd7498a51024fc7654c21165dc7358552007cf2018d21006dd63d4e2101cfe7458c51207ce72d4e320067e601
  | 12 => 0xd74587521767e63949520067f74d952102e7c5259421166dc3258b530175e75d4e320067f5459721006ed42d89310067d40195320069f30590510067d43d952101cfc74d895101cfc74d8553004ff7459521004ff70d8d51006dd30189530ed7e7094a51054fe75d8f21026bf51592210567e7319521004fd74596321e67c51d972101cfe7458e520066f20195211747e7619532004ff7258f510567f7119521006df63d8552054fc7558a31164fd765493200cfc7058b51004fd7458a311767d31d9532006df54d8d2102cfc72d952101cfe7498a511765f30d953218edf30d895301cfc7459631024fd75d8d51166df305953201cfc74d8552004fd71d9632004fd764cb51065df7018d21005dd70d8d21014fe73d953100cfc7059721005ef7254d520067f654c921255dd70d4e320067f42195210076f20d952100cfc7058a5102ede3258c52144fe7694932004ff764c951004fd7458f5200cfc7058652206df72d8d52026bd315905100cfe7018953054ff76d4f2102eee72d96320065d30195211e67f72d95210567c6554d2102ef66248421014fe76d493218cff7259532206df51d8d5203cff764cb211d7ce21d8d21004ff765493101cfe74189511c7d730c8521004ff7654e210067c30d95210075d30d95210067e201952100cfe70d85520057f754ca212767f60949521467e3219532004de7618d21006df634c521004ff7654f210067e10d953201cfe7418953086bc72592210067d6514a311767d73d95321767e31d9532066ed3258a3102cff70d9632066ee3258a311dd7d7114a5102e7c6599721006dc60d8d52004fd70d9721006dd3058c52026be1059051006bd75592211e67c71d95210067f20d9521006f610d853201cfe7498851006dc6418d2102eec5298b530567f5098b51006ed2058a31004fd74d963208df77158931026be215905102e7f659963200cfc70d95321cede3118931004ff70595210557c73d4a52026bf2159221207cf52d8d52006dd30d9531006dd60d8d21164ff73595320067c63195211d6dc31d8f21004ff7258753125be7498532136be648c851005ef7254e52066df3058d211e7767194a5102eee7298b53004fc7654d2100cfc70d8d510567e65d4a211767e5358e52004fd7498a31206dc54d8d52064fd764c5211467c3119532004fd76d4931006ef7259532004fd76d4e21014fc7358652006df4358f210567d74195210075f73548520065d65d4e32024fc71596310067c64d95321d6de21d8d2108cfd73d8f210267c5159621024fe71d8d520067c65185320067f60d9532006de10d8d2102dec7254c210067f70d9521056f45158752166df30d8d52004fd7458c5102cfc76d4f21026be3159051196be64d4a210067c4319521014fc7359521004fd7058c5200cfe70d9531006ec32d8951
  | 13 => 0x1900000602000600103509b00f0140022fa01201602a00401500b00038800000014f0000010230320000000240000000190090141ef00101f0ca00401800000204706705100a0d380f02c00214903800000200300901900001b00e00600300005d00e04d07200002d7f749495200cfc70d8931066dc53d8d210067c70d95320066d201952101cfc74d9531006df301895100cfe70d855302cfc7418931006bf7359221006de60d8d52005df7354b21025f471549210067f6558532006ec62549510567f701952101cfe74d9521006df50d8d21006be535922101cfe7458e21024fc7258f21007d763c852102cfc7259421026ec2158851014fc7358752176de5358e52004fd74d9521026ef62c8521005757194a511e67f65185521de7c211952102e7f7559632206dc658c93202f6e6254852066dc3258a3100cfc70d8d2108edf3098a310076d20d95210067d73d9521025f676c85210267e5159621025f77248421005ec7258553004fd705963200cfc70d8953006ed6294a510575c5354e52005dd739855201cfe74d95310067e40d9521056ef6294952004fd7058e52004fe7614921024fc764ca51014fc7358a5102cff701895300cfc7058c5110edc4358f51004fd70d8d51006df60d8d52206df65d4e32006df638c951146ed3218953006dc6018d21024fc764c921004ff74d8953004fd74d895100cfc7058753004ff7458a5102cff74d9721004ff7458632016de634c72102cfc7259631004fd745845200cfe70d853202eec6294951026f661185530dddc73549510567e74195320067d71d95321e67c31d952102ef7215865202cfe76d4f2100cfc70d972101cfe7459621006dd42d8d52006dd30d9632005ef724c72101cfe745953102f6e52d4b2102cff7098851004ff7654c2102cff7018951004ff7358452006bd6414a2100cfe705865200cfc7058851024fe72988510567c7119521004fd73d8552014fe73d9721006df6418d21006ef4218953286df5318953006df43d8d520067f32d95210dede63d8d510067f658c921054fd7259421004fd7418953004fd70d8d21016de63d4e21006de64d8d21014fc7358b510ed7c7094a511467e6314a51014ff764c5210067f65d4d21006df7358d21056df5358c52004ff7458a3101cfc74d95210067f54d953210edf3158f510067e421953202eef201895302cfc7498b53006f776484210067c64d9521006dd30d8532004fd7498851014fc735885102cfc7258c510067d4119532006de6418d52026bd1059221016de634ca2101cfc7458c520067d40d9521006dc6418d52005bd7418553024fc7654d5103ddc73548210067d20d9521025f671d4a21006f77158d210067d30d952101cfc74d9532006dd6354c210067f54d953129f6d42d4a5200cfe7098b510067d5098b51004f
  | 14 => 0x2900e01802800022e00b00c00200101100706400601500c1540a800301d00102401801f00801002300a0090270000002e50070010051b800101200800300000600100300b01100003901680400001504100100000300300002e0000600000000040090d300301e00100000300000e02600000b0bd0e600003300b00001d06a01b00002a00100d0a00350000020e00070050130ab16200000a00800000208800403100002f00100059606100600000600100001507c00000a00a01b0e800702401609505c02810d01100503302f00008706601303600000000500005c03900300704402000300000200000400000005f05b00704500202703c0901f600401700801500e01600a00400301b00100001a00b07900900a00f01a02b0030000020b70f400100e00c05100100800026432401800000003a01b03800001c11300000000a00200000000004100600200001301000700100000600f01900a00800900005401103601000000400400800300b0000090bd0000000010190690eb00600c00400f00000303600d00100000201b16604b01800b00800002100002701c0a600007401900561c04200a02501903c01700000d05a01000700a05300201600300800d0030000000770ec01104503500000102a15302f03d01301400302500407900a03d00201f00605c01201808201400000a00401600000900000e00300000401800000a00003601300817b1d500060200200b0020090080ef02b00301500202f07100700300d00602f01500803d0060040060550a608800404400401b00f02002e10c0000000000240000c00050000000284fb00a0080291cc0000d236502d00802900000302c0080332ce08108543400800b19a00000303900701903400301400401b00b00300201100000000001a00a00200100000200b00000901600c01d01203c00102400102f0000120000090010030000a300100600600100a00002100208100002f01200009000500e04a01100700100f16500000200000a01300000701201c07506900506000100001302a13100002801f00300000102d00001829200001f00800302b07a01201a04300000003800200e00001e00000013e0a900700105510d00200400000c00000100901f03400200108100500b0000140000040f300000101901100500600502900403900000404619a00500403201802900004900701103200c00300a0b500d00000700c00000201900000714600b02567200100f0000870470d20da0080f300b00c0120d300801d00e48003d06312e25600600a00000100100c00c00f00002000204a00f06b34e04501400001a00001400100000b00000000a00004003a06602f00115a01308600000101502f00a01a00b0030330fd00100002900019b00100e0bf07e00200000309c0030000200120400150054e
  | 15 => 0x2800000700e00001e00200702800200301d00100000200809300801f01400b04200504b0070040060000290010ea00400600200000800000f02300b00300a00300d00101800600800000307101300400000901012900300101e17900802401300110300a0005b400105401514311a00300e00201d0e80040040020670d500006624800900000000e0ac00b000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8dd8790363548158ecec32e429080237e0d74584520064f3a6c730aa400e4f3058a529443b0ff0e880ca90803a550441d8d520062e39acaa9442038f787507614c8014bd0ba1ec69080237e0d745953200537c2a40b14a200a9e841d7634840153906b92c9108b27360b7354a3200537410e1b2a4200a5e8398065484010fb0e080ca9900a1f21576d4d210543f42ee1b0a642ea5c83507654c80147908b00ca99003365c130d8f2102c76412e0b184240a5e8588363548018b8eab1a65108021fe1d64195210043fc2aeca9a4200a3f84580654c8150fd0f100ca9902a1f2157058c510054f41c40b244200a5e85d0763484010ff0eb28ca9900237a1c40d8d2100556c14a0b24420a87e87100654c83347b0bb9ac82880e2f21170988510247a40ae0b2a6400a3f854c164144814bd0a3a6c6a90023761e50d8d521462e318ea9924201cda704c365c84011bd0f206c69080297a0e40195210052f4184032a42008dd8799063484019b2e0986c6908063e20174584520066cb8261b1aa200a6c8255162144814bd0ba0ec6a90023721d30595210056741081b1a4200a5e85883634845dc9ec5b2c64991762fe1d20592210046fc1ae8b2a4200a5d8310065484514bd07080ca9900e3be1d42d893117536c10e1b2a6400a5d8588363484014bf06a10ca990021f61e60195320066db8260b2a622ea5e839c3654c80956d02282c9108029761620d8d520043fc2ae0b2a423ae5651d8f51484011bb0e086c6a9002b560664d8d522a4afc3acba9c6400a3e84043654c80b998c4b98a49880297a166018d210063bbb6ea908423a8de87883634840153b07382c91080335dd873484210053741081b2a64038bc845c162d4c0147b0b902c8288132d18574985320055ac0c40b244200a5d8390065484014bf06b06ca90802b360e201893102c76412e8b18a4028dc835c162144011bf06ba2c3a900297e0d65195210052e41ac1b2a42008de87903635480153b06102c910803279d0639855200c7c402e8b2a6200acd8298063548018b8cab80c69080e2f2117058a310047bc0ae0b1a4205ccc7258d31c84010fd0fa0eca908029761474d8d520066db8260b1ea200a9e8404363548b78dee432ac2990029760c101953201c5e422e0b1a4200a5d8510363484031b90e982ca988ba97e1d65d4e320053741021b2a643aacd821c3634840147908b06ca99002b3a0870d8d210043f43ecab1a4240d5751dcd52944011ef0eb08c2a98038794d64d4e210052e432a831aa428a5e83104654c8011bf06b82c4288032b9937254e210051fc22c1b2a640a87c855d1621440147908900ca9080297e1510d8d210062e986eca90a40087d87d0465484514bd06200ca990029b60840195320043fc3a21b2a6458a6e8208065484018bf0eb2ea71900237e1d6018d21
  | 1 => 0xb0f286c69080297a1440d8d2100557c12eab24420087d87883654840199e61b92ca98802b360a6418d210043fc2ae0b2a620aa3e85c81641440153f08906c6a90021fa1c42d95210052fc1a8232a64008ef875886254401cb0c0986ca9900e3de1d41d85520043ec3c4032a6402cd67618f21484bf53b07182c91080393d8f52949210062fb2ae031a4200a5d83903654840147d0bb9ac9108029761743d8d520543e42ae8b1a42008ef875886254c0147b0bb9ac9108063d21d105845200536c106032a4200a5e8308365484018beebb9aca90953930cb2019532005a6412a831aa400a5d8598063484018baea3aec69097aa7a0c30592210043ec3e87b2a423ce6762d97214840117f08b82c7288123721d4358e510543e42ae0b10a23c87e861d532484a98bee032c64990f21fa1e20d952100566c14a1b1aa45495e87dcd52148014eb02200ca90803365c130d963200c3e43aa0b2c6200a3c8448365484019b6e1386c6a900336dc13058f522052f42881b1aa4028dc835d951484031df0e906c4a88a29720d20195320055642241b12a200cdb704c1630845d4bd07106ca990031718c7558d210072dc026032a4200a5d85d8f53484014bb06386ca908029761442d8d210046f43a60b2a6400a5e8394365484014bb06106ca990029b20965195310066cb8261b2e4200a6e82040654c82f0ff0e886ca908029b209411952132f261924032a6400a5d83843654c801cd0c0906ca908021f61f43195210066cb86c1b1a420087f855c1618c8735990c900c6908ba1fa1c654c9210053dc02c832a420087d87d07654c8011bf0eb00c6a9007369c13098b510243e42aec996a254e4e72196324c8011bf0ea0ec6a9003365c130d8d5202c76412e0b2a6200a9d849c763548014f100b20ca908ba97e0130d95320146e41ae8b10a22887e87d953248415878eab226428802a760e70590510052f41cc832a4200a5f8559063548011ef02b82ca9917ea760e30590510061fbaac899442008de87cc162144011f700ba2ca9080637e1d30d8d211d74a20a83b1a4200ad583043614c8014bf06b20ca908038d50441d95320046f43a60b2a423b87e86dd532484798e8e3b2aa4908029ba0840195320066cb8261316a200a3e84040654c8014bb07106ca99003179d9301952130556412e0b24420097581dd532944010fd0e086ca9918aab20975592210061fbaac8990a20587e8794165c84010fb0e200ca90802a7a0e705905100c6fc3a61b2c6400c6c75dc963484010ff0ab82ca9910a8fe1572590510064eb26e6a94423ca768110365484514b906a08ca990021f61f41195320051fc22c032a4200ace8210363548014dd0b100c498802b5e056018d210255b408e0b20a200a5d83180654840117f08b82c5a99a29be0964195320052ec1c4032a6400
  | 2 => 0x510d8d210051fc224032a6400a78805936548401d90c0906c6908033318c7254521056363acc4990a200adb80590634845d8bcec980ca99003175c0658c9320045fc22e0b2a640087d87883654c8755ad02206c6908029da0440d95320053ac0881b2a423ba7681d0865484011bd0f286c6908023761e6418d520065ab26e29944240a5c8544363548014bd0b306c69090297a1442d8d520052e42ac831a423ca7681d41619485d0fd0f106ca991031719773549320247643ac4990a200a5d8314365484018d8cbb92629095297a1b658c9320045ec26e1b12a200e4c65c8063484014dd05080ca9080237a1f635855200e6d38261b1e420087d87108654c8051b9063b2a4988022fe117058b510045ec26e1b126200ccf301c9654c40717908b82c610802b5a0440d8d520255b40c40b244200a5e8599063484b7a98643aa65108031de197194a510072632a4031a42008df8759063548011bb0f206c6909529720f20195320052ec18c1b2a42008df835d165084011bf06ba2c32900297a0c40195210056641ac4312a20087f855c163484071bf0ea1ec69080237e0d705953200e6d38261b2c6404ad4814c163084018bca73b6a69080297a0e40d95210061eba4a9b2a640087d87d0765484014bf06aa2cb188028f21160195210062fbaec69924200a6d8210065484a98bce432c6499002aba0a50592210054fc22c031a423c977865c652944011bd0e206c6a90132d1c56454a2100667b18e498a422c8dd8718363548011bb0f086c6a90023761c6018d210054ec1ceab244254a5c824c0654c80717908b82c5a88123d205705942102c3e43aa8b2c640c8dd87083634840153f06b92c82880e2fa1370d89530066db8260b18a20087f87440654c86339f0cb96a7190038d50441195321452f41c4032a64018df874c3635440155f04b82c9108f29b21920d95210046ec3881b1aa4318df865cb538c8158b8eab1a642880237e1d6418d210046fc3ec031a42028de83dd3614c8010fb0f300ca9080237a1d30588510061fbaceab24422ec5f655c0635480b1d904ba2ca108029761442d8d5231e2e39aa8b10a2008de87cc165484011ef02b82ca90802b360a50d8d210066cb80c1b1a4200a5d83080654c8158d8cb396a2908063721d3058f510054fc2241b1a4203cb674507615480b9cca5bb242108bb171cf65549322a52f436c7292a43ba768110c65484014bd07326ca9080297a0c70d952100477c12e0b2a62018ec87481628c40147f08906ca990121fa1e53596210052ec2cc9b1a423cd66519cb51484798ecedb2e429080e2f2117098b530052ec2e87b1a4200a5f8559063484051bd0e300c69080335cc376484210062fb2ee6a9264028dc835d161948150fd0fa08ca908021f61e64195321452e41a8432a640287e87d9553484011b
  | 3 => 0x1b1a420087d8710b654841547d0a382c82880336dc13058e5100537416a8b14a200c5c75dcd63484018eae238eca990ba97a0c70d95320043ec388432a4200a5d8399065484011bd0e086c6a900e2f2117058a510054ec18e0b24420a87e87108654840b1bd0fa1ac7908028f61010d953200c6e43a60b1c4200ce77654921084010fd0e216ca99002a721120d8d520052fc1ac9b2a4200ace86c8063484051b906ba2c22919e9b60a601953217537436a529264008f78758461548014dd04200ca9080e2f21170588510052ec1ce1b2a42008bf8748164144014b906a08ca908a3179d930d95320043ec2ee1b0a643bc6f8758a52944019aa61bb242108031718f7558d210052ec2e83b1aa400a9e839c1648840187ae92a6ca9095297a195418d5200666398c4a92a200ccc631c9635440717908b82ca98802a761010d8d520052f41cc1b2a4200a7681100654c8abc9c42328c6908022fe117098b530052e4326032a4200a9f845806354809968e2b2265108023be1d621893100566c1021b1aa400a6e821c3654c80169904aa6c6a90021fa1c40d95210bc3e43aa0b0ca4008ef825c163484018b8cbb86c6908f29ba1b529492102c3e43aa8b2e4200ccf724c1654c4191bb0e306c6908e6b5205301893100c6e41ee0b1842018ec8748162944031f100ba2ca908028fe1572592210043f438cab1a42018ef874836254c0153b083aec6908029760e20195210062eb9ca7b2a42008de87943635480147b0a382c910866ad60470590510051fc22c1b2a4200e6b8048065484514bd06080ca990029ba0a30195212070faa4a9b1aa40087d87043654c8014bb06206ca908030f1d5644ca210052ec2cc831aa400e1f6455063548014db05080ca908021fa1c40d95320072dc0261b2a4200ad88059063484150fd0e210ca990023de1d61185320070faa4a9b1a4200a5d83943654840193ae831cc2a915b8721530590510062fb80ca31a4200a5f85580634840153d073aac9108ee1f21d50584521e43e43eca9924228a5f804c0654c80159d05286c6908029720d6519521175a741ea529264018dc874c1654c8014f700b26ca908029760e60195210052f41c2032a420a87c855c1618c8011bb013b0c6908029ba08301952100637ba8e4b2a62008dd8714363484014eb02218ca908ba97a0c10d953235537c2ac4312a600cdb704c1639480153d06102c91080297a166518d210043f43e83b2a6400a6e82943654c4014df0eb14a5288032d5937154a210056a40ac1b1aa400cd776dcd21084158b8cab9ea499002b360a30d8d2100637b28e4a8a42578df87507634840159d05286c6a900297a1442d8d210247a40ae0b184200a9e8394164884018b8ebb1a6490803365c06018d520053ac0e8432a420187c87541658840199ec6392a6a90029721
  | 4 => 0x2544014bb07200ca990a31798c754ca210043f43ecab0a6400a5f83480654c80155d04382c8288029ba1620d89312046f43c41b1aa400a6d82d96524c4594b90bb9acb190023761e6018d211452f4184032a6400c5f70d946348401cb6c0980ca99002a720d72590510052fc2a60b1ca4028dc835c165484014bd07100ca9082a1fa1e20195210156641ac5190a200a9f8458363484014bb06286ca988023761c40d8d2102c76412e8b2a6200a3c84480654c8154790a982c8288030f993754ca210045fc22e0b1ca404ab6811c164884014db04080ca990028fa1271d953200477c12eca9a4200a6d8510b6254c014bb07080ca90803934c16294a511d66a38ec6992420a87c855c163484014bd0c328c6908028f61271d95322d52f4186032a4200e9b804c1641440147b08080ca990063b21d20588511d46e43ec6a924200a5d83d08654c8014bd07086ca90803279937354a211e43f43ea0b0ca400a9e831c164144014bb06100ca9080237e0d7058d210052ec1881b2a6400cdb805c3634840159b07106c498802a7a0c20590510066631ee4a8a42008de87843634840117f08b82c6108063721d3058e510543e43a2032a640287d85dc36154c0157700b92c9108021f61e20195210066cb86c031a4200a5d85d0f635440153b07282c9108023761e20d8d520056ac0cc831a4200a6d85d8b524c4018beea39aca909928fe1570590510054fc1ae4b244200a5f8559363484014b90ab00c690803a6e0130592210062e32ae1b1a423acd676d8f21484010ff0eb28ca988022fe1170595210551e42ae0b20a2018df874c363c8477c6882a08ca908023760373595320066cb80c1b1aa400ccc73dc965484039b4e0986c6a90029761410d8d520054f424e3b1aa410ab5811c164884014bd06300ca9080a1f21570587530062fb2ee6a8a620a8de87d8d53484011bd0e106c6908ba97a0e40d95320046fc1ae0b2a4200a5f83504654840117f08b82c42880e2f2117059532007279864032a42008fb805d161148010fb0e206ca99003331c930595311752f41841b2a6400c9d74d8e6154801c9e60900ca908021fe157058c210052ec1c81b2a642e87f855d932144014db04206ca90802ae201725922100537c128232a420087f87580654c80187cc9baa6428802a72116018d2100c6e43a60b184200d57305c652944014bb0b306c690802a760c50592210052ec2e83b1a420087f87594654840147908b06ca9080297a0c40d95210061f3a0cb30a64028dc835d165484014790ab92c9108029b21562189310543f43e8232a6400a9c8448363484011bb01b9aca9082a8f21572590510052ec1cc1b2a4200e5b604c3654c80147908906ca990b23721b735855201c3fc3aa9b2a42028dc87cc162144018bee729acb108022fe117058a511d5664324
  | 5 => 0x90032b9907254e210543f43eeab1a4219a3d851c164144019b6e0982ca9900297e0d60195210051f428e0b244200a3d8588164144014b906b00ca9080317cc376548520066db8260b1e4200a5f83507654c8014bf06a0eca908029b60810d953200477c12e8b2a62008df835d1654c401c9a61900ca908f21fe1d65d47210046ec3c21b1a42008dd83dd361548030ff0ea86cb908023721d305885100556c10e0b20a204ae48148162144090f90eaa2ca108023be0974595322e45e43a40b244200e4d3048065484014e902b00ca9910393d8b63949522a7261908432a6400cdb704c16348401aaa60b8ca528802ad61010d85521dc3fc3acba944200a5d83840654c8158b8cab9cca9082a1fa1f431952100566c1841b126200a9d8388164144015af02b00c6a902a1fa1c101953200572c1021b0aa400a7581993654c81547d0bb9ac82880297e1560d8d2101e5b3a283b0a6400ccc73d8952544070ff0eaa6ca988029760c41195320061f320ea9944200a5f8558f538840155b04382c9108029760e64d95210066dc02e1b1aa400adb8059363484014bb07286ca99003171cf65549210052e41a83b2a4200ad58199063548010ff0eb00ca90803179d86518d2100c3e43aa0b284200ad58110363548150fd0e200ca9080297a0c50d95210052f418c1b2a4200a9e831c1648840b1d904bb2a6108bb96e0130d95320053bc0ac1b2a6400ab584043614c80b0f90ab82c3a902a972153058c5100636328e498a4205a6c8255165084018beec39aa429002b5a066418d5200c6e43a60b18a200a5d831c3654c8014b90ab26c6908029ba0840d95210053b40cc9b2a640a87e85dc3615480147f08900ca908029761474d8d210052f4366032a4200e6b6048065484015cb04086c299002b620164d8d210052ec1ca1b2a6240c5c65dcd52484051b906ba2ca108029760c50d95320052e41ac832a4200e4c65c8363484010ff0aba2ca9900a37a1f73588511752e41ac5290a200ab58114164884019b2e0300c6908029721930d95210052ec188032a6400c5f65dc363484010ff0eb20ca99002a72116018d520046ec3cca31a4200c5f30dd563484d34bd0a320c6a90023ee0174595310045fc22e0b2a6200a5f83551658c8a9a98643aa641082a1f2157058c520056ac0881b1a42008fb805d16348401c5f08900ca9080297a1474d8d210046f43841b1aa400aac844806254c014bd07386ca908a297a0f42195321646ec3841b1aa428a5e83900654c82d1b90ea0ec69095b171d53058d210072632a41b1a4200a5e8599363484014bb07106ca908030fd95749853200477c12e8b2a4200c3e74d96614c8010f90e886ca99003365c36018d520543e43a2032a42008dc8750763548031b90e982c7a902a37a1f4358f510054fc22c1b1aa40a87c851d93
  | 6 => 0x45ec26e1b12a600aac8448062544031b90e982c7290063721d3058c521752f41c21b2a6400a5f85443635485d8beeab1aa729003271cd6454a2100c6e43a60b1a42028dc87cc165484bd53d06182c8288023760373588510056741021b1aa400c5e73d9665484c356f02b92c910802b5e0560d8d520051ec2c40b2442008de8714363484014b90ab06c69082a8fa1620590510056b40cc9b1aa400a9d830816414401c5908900ca9080e2f2117058e511e5b340ea52924266e4c32d08654c80159b04206c6a9002b3e096418d520062fbaa60b1a42038be84dc3625440196ae9b0cc2990021f61e64195211d56a40a61b1e42008bf845c1628c42155d04382c9108028fa1620592210046f43c21b1aa40087d87100654c80717d09b86c4988022fe117058d210543e42ae0b1842018df874c363548014db05200ca90802976166018d522862e3a8e6b10a200a5d83043654c8051bd07ba6c2a90e637a1b73549210053bc0a4032a4200a7581990654c80196ae9b0cc2a900387e15305905100e7538241b12a600a5f855806354809968c2ba4c2a90029de0560195320066cb86c1b1aa4008de8718d615480199ee6392ca9894237a1f63549211d62fb1ceb30a643ba748148065484010fd0fa1eca90802a760e20592210543e438ca9924200a5e86cc365484071bf0ea1ec6a9002a721160d8d210054e422c1b1aa400a5e83883654845d4bd06206ca99002b360840d8d210055642241b12a600acf825806348401d9240106c6a900e2f21170595210073490041b2a6400a6d82103654c8010ff0aba2ca908029b61442d89510062eb98e7b2a4250ccf865cb538c8774ed02200ca9080336dc13058e210046fc3aca31a4200c5e76cc065484018beedb9aa4290022fe1170988510543e42ae8b18a455e4c2119463484014bb07086ca90903171d773588510ec3fc2ae0b08a4028de8718063548010ff0aba2c6908021f61c42d95320046ec3c41b1a4228e5b804c0654c8ad4bb07180ca908123721d6354c2100536c146032a4200c5f655c363484031dd0db9262908029760c20d952101c3fc3aa9b2a6402a5c83d97534841547d0a392c8288023761c6018d520061eba0e9b2a4240a5e8504363548731bf0eb1465188021f61c40d952100733c0a4032a4200a7581100654c8030ff0ea86ca9900237e0d76545210046fc1ae8b10a23ca6d821c3654840b4dd05282cb908021fa1c655853200c3fc3aa1b2a4200c77761d5210840117f08b80c4988039920520195210146e41ae8b0ea400a7481583654c8018beebb9ac6908030f195749853201c5e422e0b1ca40487c8759553084091b90ea1ac61080297a1b5418d521e71a20a83b2a421d87c8744365484015a902b00c6a9002a760c7059051005374148032a4200a7681990654c8014eb02206ca9
  | 7 => 0x30000c41200408048b01e004004200000d574000841c00005008342142b000740042c002660007c0063306c000c015000121d0050a8160900403407b284901c00b50050546a014100cc0101840000040180005421008001601c0600702c5d0000007c0801d060001004c020e9a001c00010010a0520540f06855000000002707400038ca09400032ae5740f01aa000000024000e8020401513c1d02000018021a97000c0102800094000000000414010380a4c600009794000043d01c17070080800204c01068020100304013170040045605c01094511381706c01020cb0008001408000220000702c8207408008000500201001014010282508c8b02c018484082400074090090500c0018d2c08001014060dc15008130246b1005700c2203c43000090046806c3200c0b004001400006820010000880003000320001b42402c00000003bc8d01800440811d40906c4a000010003d0040000001000001908c04812090021200c070030512d00000908030901800c071f850074720c8010100002c2322c0a21c2f00800000500001c02c000bc0b12c020017af54290040f00001000010b404018061280d0084a1301300006001b915c521280101c47184030000e0fc0008829f700226cb2038018becab9cca9080237e0d7458d211dd364324032a4200cdb704c1631480153d06282c91081237e1d63d4e2100c7c402e8b1a4200c5e76d9463484090f90eaa2cb188022f21d20590511762e31eea99242018dc874c163c84c78bcecaa6c6a90021fa1c50597210052ec2cc831a4200a9e83881641440147f08906ca9080317d9773549210052ec1ce1b2a6459a6d8288065484014eb0a086c2a90029720d64d95211e63b28ceda8a42038bc845c0624c4014bb0a206c6a90030f5d074d95320052fc2a60b1ca219a3d851c9641440b1bd0fa1ac6290023761e6018d520
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x2000a00040c0a984c3261c4219532006830c884480654c80184c732095458851006892108148065484a924c9260c4119532007030ca641d532884a924c922195418d52
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x4
  | 3 => 0x5
  | 4 => 0x2
  | 5 => 0x3
  | 6 => 0x209
  | 7 => 0x20c
  | 8 => 0x20d
  | 9 => 0x1549
  | 10 => 0x6
  | 11 => 0xb09
  | 12 => 0xb0c
  | 13 => 0xb0d
  | 14 => 0x1409
  | 15 => 0x140c
  | 16 => 0x140d
  | 17 => 0x154c
  | 18 => 0x154d
  | 19 => 0xb49
  | 20 => 0xb4d
  | 21 => 0x1449
  | 22 => 0x144d
  | 23 => 0x2c9
  | 24 => 0x2cc
  | 25 => 0x2cd
  | 26 => 0xbc9
  | 27 => 0xbcc
  | 28 => 0xbcd
  | 29 => 0x14c9
  | 30 => 0x14cc
  | 31 => 0x14cd
  | 32 => 0x19c9
  | 33 => 0x19cc
  | 34 => 0x19cd
  | 35 => 0xcc9
  | 36 => 0xccd
  | 37 => 0x15c9
  | 38 => 0x15cd
  | 39 => 0x449
  | 40 => 0x44c
  | 41 => 0x44d
  | 42 => 0x1649
  | 43 => 0xd49
  | 44 => 0xd4c
  | 45 => 0xd4d
  | 46 => 0x164c
  | 47 => 0x164d
  | 48 => 0x1a09
  | 49 => 0x1a0c
  | 50 => 0x1a0d
  | 51 => 0xec9
  | 52 => 0xecd
  | 53 => 0x1a49
  | 54 => 0x1a4d
  | 55 => 0xb0211
  | 56 => 0x154b11
  | 57 => 0x3ca
  | 58 => 0x15ca
  | 59 => 0x44a
  | 60 => 0x164a
  | 61 => 0x155411
  | 62 => 0x15d451
  | 63 => 0x1455d1
  | 64 => 0x15ce
  | 65 => 0x1642d1
  | 66 => 0x2d655
  | 67 => 0x454d1
  | 68 => 0x14c455
  | 69 => 0x1654d1
  | 70 => 0x14d655
  | 71 => 0x15ccd1
  | 72 => 0xcd5d1
  | 73 => 0x1a55d1
  | 74 => 0x15da51
  | 75 => 0xd4451
  | 76 => 0x44d51
  | 77 => 0xd4455
  | 78 => 0x164d51
  | 79 => 0xd5655
  | 80 => 0x3ce
  | 81 => 0x1a1651
  | 82 => 0x165a11
  | 83 => 0x1a1655
  | 84 => 0x5cb
  | 85 => 0x443d2
  | 86 => 0x9ce
  | 87 => 0x24d
  | 88 => 0x150e
  | 89 => 0x98e
  | 90 => 0x168e
  | 91 => 0x45414
  | 92 => 0x409
  | 93 => 0x1609
  | 94 => 0x168a
  | 95 => 0x9ca
  | 96 => 0x140095
  | 97 => 0x141555
  | 98 => 0x140455
  | 99 => 0x104c
  | 100 => 0x2d355
  | 101 => 0x98454
  | 102 => 0x188454
  | 103 => 0x44994
  | 104 => 0x45894
  | 105 => 0x1a8c
  | 106 => 0x45654
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 1619
  | 6 => 2372
  | 5 => 1002
  | 4 => 7
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
  | 9 => 2*((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 1)
  | 8 => 2*((h/34+packedAt gbK8 (1612+(h % 34)*6) 6) % 62)
  | 7 => 2*((h/546+packedAt gbK7 (59903+(h % 546)*11) 11) % 1619)
  | 6 => 2*((h/846+packedAt gbK6 (113856+(h % 846)*12) 12) % 2372)
  | 5 => 2*((h/369+packedAt gbK5 (59118+(h % 369)*10) 10) % 1002)
  | 4 => 2*((h/16+packedAt gbK4 (490+(h % 16)*3) 3) % 7)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xff81f00fffe07fffff03ffff033de07d1c7e3f
  | 1 => 0x3ffe000f01ff83e01fffffff1cd23f8e1393ff
  | 2 => 0xc1fffff001fffc001ffc0f00e0e3c3f3e3e3cc
  | 3 => 0x1fffffffe0000001ffff000ff03fc03fc03f0
  | 4 => 0x1ffffffffffffffe0000000fffc0003fffc00
  | 5 => 0xfe0000000000000000000000fffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x528030414a201428c522994a0104e035042615
  | 1 => 0x2516010620cc83410a4522b40c500d8a1190ea
  | 2 => 0x80aad6500971580253a88c0660a342d162e34c
  | 3 => 0x11cd6b6bec0411049cf3c818b703f403bc03b0
  | 4 => 0x21718d8cb19e639700410020def80002db5800
  | 5 => 0x38000e00c0184218008200c0fbffbb6c000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaece8faeac888feeaece8faeac888feeaece8faeac888feeaece8faeac888feeaece8faeac888feeaece8faeac888feeaece8faeac888feeaece8faeac888, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_40297
namespace PEqualNP.Outside.L_meta_40297
open PEqualNP.Outside.L_meta_40297.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 15 := block_range (n:=15) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 15 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 68 := block_range (n:=68) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 68 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_96 : Interval s0Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_192 : Interval s0Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_288 : Interval s0Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_384 : Interval s0Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_480 : Interval s0Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_576 : Interval s0Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_672 : Interval s0Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_768 : Interval s0Atlas 4 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_864 : Interval s0Atlas 4 864 30 := block_range (n:=30) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 894 := (concat (concat (concat bs0_4_0 bs0_4_96) (concat bs0_4_192 (concat bs0_4_288 bs0_4_384))) (concat (concat bs0_4_480 bs0_4_576) (concat bs0_4_672 (concat bs0_4_768 bs0_4_864))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_96 : Interval s0Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_192 : Interval s0Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_288 : Interval s0Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_384 : Interval s0Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_480 : Interval s0Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_576 : Interval s0Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_672 : Interval s0Atlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_768 : Interval s0Atlas 5 768 52 := block_range (n:=52) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 820 := (concat (concat (concat bs0_5_0 bs0_5_96) (concat bs0_5_192 bs0_5_288)) (concat (concat bs0_5_384 bs0_5_480) (concat bs0_5_576 (concat bs0_5_672 bs0_5_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 44 := bs0_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_7_0 : Interval s0Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_7 : Interval s0Atlas 7 0 1 := bs0_7_0
theorem alls0 : ∀ k ≤ 7, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
  · exact alls0_6 i (by omega) hi
  · exact alls0_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 7 := block_range (n:=7) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 7 := bs1_3_0
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
theorem bs2_3_0 : Interval s2Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 1 := bs2_3_0
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
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 6 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 25 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 90 := block_range (n:=90) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 90 := bs3_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 44 := bs3_5_0
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
theorem bs4_2_0 : Interval s4Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 6 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 56 := block_range (n:=56) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 56 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_96 : Interval s4Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_192 : Interval s4Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_288 : Interval s4Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_384 : Interval s4Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_480 : Interval s4Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_576 : Interval s4Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_672 : Interval s4Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_768 : Interval s4Atlas 4 768 13 := block_range (n:=13) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 781 := (concat (concat (concat bs4_4_0 bs4_4_96) (concat bs4_4_192 bs4_4_288)) (concat (concat bs4_4_384 bs4_4_480) (concat bs4_4_576 (concat bs4_4_672 bs4_4_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_96 : Interval s4Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_192 : Interval s4Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_288 : Interval s4Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_384 : Interval s4Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_480 : Interval s4Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_576 : Interval s4Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_672 : Interval s4Atlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_768 : Interval s4Atlas 5 768 33 := block_range (n:=33) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 801 := (concat (concat (concat bs4_5_0 bs4_5_96) (concat bs4_5_192 bs4_5_288)) (concat (concat bs4_5_384 bs4_5_480) (concat bs4_5_576 (concat bs4_5_672 bs4_5_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 44 := bs4_6_0
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
theorem bs5_3_0 : Interval s5Atlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 2 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 6 := bs5_4_0
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
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 7 := bgb_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_0 : Interval gbAtlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_96 : Interval gbAtlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_192 : Interval gbAtlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_288 : Interval gbAtlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_384 : Interval gbAtlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_480 : Interval gbAtlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_576 : Interval gbAtlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_672 : Interval gbAtlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_768 : Interval gbAtlas 5 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_864 : Interval gbAtlas 5 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_960 : Interval gbAtlas 5 960 42 := block_range (n:=42) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1002 := (concat (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 (concat bgb_5_288 bgb_5_384))) (concat (concat bgb_5_480 (concat bgb_5_576 bgb_5_672)) (concat bgb_5_768 (concat bgb_5_864 bgb_5_960))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_0 : Interval gbAtlas 6 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_96 : Interval gbAtlas 6 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_192 : Interval gbAtlas 6 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_288 : Interval gbAtlas 6 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_384 : Interval gbAtlas 6 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_480 : Interval gbAtlas 6 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_576 : Interval gbAtlas 6 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_672 : Interval gbAtlas 6 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_768 : Interval gbAtlas 6 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_864 : Interval gbAtlas 6 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_960 : Interval gbAtlas 6 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1056 : Interval gbAtlas 6 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1152 : Interval gbAtlas 6 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1248 : Interval gbAtlas 6 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1344 : Interval gbAtlas 6 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1440 : Interval gbAtlas 6 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1536 : Interval gbAtlas 6 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1632 : Interval gbAtlas 6 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1728 : Interval gbAtlas 6 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1824 : Interval gbAtlas 6 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1920 : Interval gbAtlas 6 1920 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2016 : Interval gbAtlas 6 2016 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2112 : Interval gbAtlas 6 2112 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2208 : Interval gbAtlas 6 2208 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2304 : Interval gbAtlas 6 2304 68 := block_range (n:=68) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2372 := (concat (concat (concat (concat bgb_6_0 (concat bgb_6_96 bgb_6_192)) (concat bgb_6_288 (concat bgb_6_384 bgb_6_480))) (concat (concat bgb_6_576 (concat bgb_6_672 bgb_6_768)) (concat bgb_6_864 (concat bgb_6_960 bgb_6_1056)))) (concat (concat (concat bgb_6_1152 (concat bgb_6_1248 bgb_6_1344)) (concat bgb_6_1440 (concat bgb_6_1536 bgb_6_1632))) (concat (concat bgb_6_1728 (concat bgb_6_1824 bgb_6_1920)) (concat (concat bgb_6_2016 bgb_6_2112) (concat bgb_6_2208 bgb_6_2304)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_96 : Interval gbAtlas 7 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_192 : Interval gbAtlas 7 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_288 : Interval gbAtlas 7 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_384 : Interval gbAtlas 7 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_480 : Interval gbAtlas 7 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_576 : Interval gbAtlas 7 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_672 : Interval gbAtlas 7 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_768 : Interval gbAtlas 7 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_864 : Interval gbAtlas 7 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_960 : Interval gbAtlas 7 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1056 : Interval gbAtlas 7 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1152 : Interval gbAtlas 7 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1248 : Interval gbAtlas 7 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1344 : Interval gbAtlas 7 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1440 : Interval gbAtlas 7 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1536 : Interval gbAtlas 7 1536 83 := block_range (n:=83) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1619 := (concat (concat (concat (concat bgb_7_0 bgb_7_96) (concat bgb_7_192 bgb_7_288)) (concat (concat bgb_7_384 bgb_7_480) (concat bgb_7_576 bgb_7_672))) (concat (concat (concat bgb_7_768 bgb_7_864) (concat bgb_7_960 bgb_7_1056)) (concat (concat bgb_7_1152 bgb_7_1248) (concat bgb_7_1344 (concat bgb_7_1440 bgb_7_1536)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 62 := block_range (n:=62) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 62 := bgb_8_0
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 8 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 2 zero, 24, 28),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 34, 42),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 18, 22),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 6 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaece8faeac888feeaece8faeac888feeaece8faeac888feeaece8faeac888feeaece8faeac888feeaece8faeac888feeaece8faeac888feeaece8faeac888
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276808936 * 2 ^ 32 + 4209690760) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_40297.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,1]⟩,⟨.and,[1,4]⟩,⟨.and,[5,6]⟩,⟨.or,[7,8]⟩,⟨.or,[2,8]⟩,⟨.and,[3,10]⟩,⟨.or,[1,4]⟩,⟨.or,[0,11]⟩,⟨.and,[2,9]⟩,⟨.and,[12,13]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4209690760) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808936 * 2 ^ 32 + 4209690760) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_40297

open PEqualNP.Outside.L_meta_40297 in
theorem PEqualNP.Outside.L_meta_40297 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4209690760) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808936 * 2 ^ 32 + 4209690760) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
