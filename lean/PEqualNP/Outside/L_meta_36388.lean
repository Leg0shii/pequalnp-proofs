import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36388.Model
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


end PEqualNP.Outside.L_meta_36388.Model

namespace PEqualNP.Outside.L_meta_36388
open PEqualNP.Outside.L_meta_36388.Model
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

def SBf (j : Nat) : Nat := [7, 7, 5, 8, 7, 7].getD j 0

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

end PEqualNP.Outside.L_meta_36388

namespace PEqualNP.Outside.L_meta_36388
open PEqualNP.Outside.L_meta_36388.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x15382959304750092430008168cc25006cf802ca878000051260e3869100a0224425c0000a0082d0c0001a28a56034e64f01003ac408408ac40000144ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32df32fe32fd32dd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x16801800054380084208c5c1088e4a84c48c5880144f8013000d8000000cd850cfcc00018440148013d614d39200094bc28415d58ad047d24046c6128a4014114a00164c96d340068710000e8640170001c2550b8015481751118011d7c9c00980c01780000d400b4e0d000012cb0005000f40000000008ec581508000000302c00740000f03c7834009000000000dc22080030020c200e000602000406000004080a02041004000000000a06021e00016e5210edaa421cf947429eaa4855e5390abaa7215dd4542ba28a85af5250b6ea2a14f14542da28a85345150a7ca8215794c42aea98859f42ccb3a85994f952329eaa4655d538cb5a85196b50932e7a92659f424cb9c84996750932e6a12658d424ca7ca8194f55032af298653d529073e6520e74ca419f28c833d521073e6420e74c8419f28883b6511067ca998cf55331b7296636d52cc67ea898cf151319f2a6433d54c86bca790d754f21da20e433f5488678a910f34ca219faa2433c544867ca810cf55021af298435d530879a6410ed10421bd280437950086eca3205d54640afa9a815c535027ea8984f151309f2a0613d540c2dca4185b54830bb2886175510c27ca9904f55320af29e415d53c839a6590734c9209f2a0413d54082bca6105754c20bb2884175510836883884f952109eaa4213f5444278a88857d4d10ae29a216f52442d8a4886d10510
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0xf4052023400094c045448418a1c03800c12c030000068062946150b32a9185428caa46150932a3592424ca946150932b1185424cb876150932a3185424cb846150932a1185424cb0d524c841c3d51328870d544c8218d59441087853210421d24c9500873041540219358853502346155320c355132c83245210510
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x204605654c8410878099082a8043411c5544cb20
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 99
  | 3 => 21
  | 2 => 3
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
  | 5 => packedAt s0K5 (826+((h/15+packedAt s0K5 (736+(h % 15)*6) 6) % 56)*7) 7
  | 4 => packedAt s0K4 (2937+((h/33+packedAt s0K4 (2673+(h % 33)*8) 8) % 143)*8) 8
  | 3 => packedAt s0K3 (833+((h/7+packedAt s0K3 (798+(h % 7)*5) 5) % 26)*6) 6
  | 2 => packedAt s0K2 (149+((h/1+packedAt s0K2 (147+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x3fff07ffffc3e0ff87f87fe1fffe07d19f3f3
  | 2 => 0xfc1fff81f0ffc3f0ff87f87fe1c0ff82e67d9c
  | 3 => 0xffe1fffe00ffffff0007ff8ffe00ffff078e1f
  | 4 => 0x1ffffff0003fffff8000fffff0003f80fe0
  | 5 => 0xfffe0000000003fffffffff000000003fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x4840111440204002280980920252212808b0b1
  | 2 => 0x1944230c814804505882882620864b08625594
  | 3 => 0x208944202a9222a50444550954089453050a0a
  | 4 => 0xb2958849281aab399550440d992c0613b00f40
  | 5 => 0xc3190e71cce333cee667664110301863dfe000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcfcfcc0fcccfc00fcfcfcc0fcccfc00fcfcfcc0fcccfc00fcfcfcc0fcccfc00fcfcfcc0fcccfc00fcfcfcc0fcccfc00fcfcfcc0fcccfc00fcfcfcc0fcccfc00, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36388
namespace PEqualNP.Outside.L_meta_36388
open PEqualNP.Outside.L_meta_36388.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x33601221586539a0040e1526800020e009011a2cb0a1c955983a500080000f804c8c000221000654154892ea111e18b47890c14e51c03c1105202080ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32df32fe32fd32dd32fc32ff41fe41fd41fc41ff31fe31de31fd31fc31dc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0xa4383652962e5e32a246c004c4bc5abe624a4ca08cac1aba6a8a3c9a56649c00004468a60000009200981e22aa8800300086948e28c2266e00001600008066b43a006c0020902c08100042484e7600580a18007e060c9e007440600ea85054b824143e3400b2027c82840078125cb6b02a00ae7a70721c2e0cb80062800200c4c802a10380000c0053008103023c1020200407016e5210edaa421cf55242af29c855d5390b5ea4a14f95042af298855d5310b3e85996750b32af28e653e548ca7aa9195754e32d6a1465ad424caeea2995d14532e7a92659f424cb9c84996750932e6a12658d424cbaea2995714532ea28a6554514ca7ca8194f55032af298655e53d06baa7a0db94b41b6a96835f53506b8a6a0d754a31cfa14639d428c6bca318d754831cfa10639d420c6bca218f5944319f2a6433d54c86bca790d754f21ea18e435f53886b8a710eb50a21afa9a435c534867ca810cf55021af298435d530875a8410f50c421bd280437950086bea6a05714d40af298815d53102dca4205b54840bb288817551102eca3185d546309faa2613c544c27ca9904f55320af29e415d53c835a85906b509209f2a0413d54082bca6105754c20bb288417551083a863885794e10aea9c213f5444278a88857d4d10ae29a216f52442d8a488750c510
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x258088002848c19c28068060040000000000e00001e0000002205049260030022c303254214532a3592424cb8542d4532c3508514cb854214532c5d08514cb464214532c5508514cb454214532c1508514cb0d5250831c3d4d428870d5350821955943108785420c421ca509500875031540218b588544c2546154f20c354d42c8344520c510
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x408605655083108780a1062a8043411c55350b20
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 99
  | 3 => 21
  | 2 => 3
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
  | 5 => packedAt s1K5 (826+((h/15+packedAt s1K5 (736+(h % 15)*6) 6) % 56)*7) 7
  | 4 => packedAt s1K4 (2904+((h/33+packedAt s1K4 (2673+(h % 33)*7) 7) % 119)*8) 8
  | 3 => packedAt s1K3 (840+((h/7+packedAt s1K3 (798+(h % 7)*6) 6) % 39)*6) 6
  | 2 => packedAt s1K2 (150+((h/1+packedAt s1K2 (147+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x7ffff81fffc3e0ff87f0ffff87fe07d19f3f3
  | 2 => 0xf81f0ffe0fffc3f0ff87f0e07f87ff82e6ccfc
  | 3 => 0xffe00ffff0ffffff0007ff007ff8ffff070f1f
  | 4 => 0xfffff0003fffff800007fff0003f80fe0
  | 5 => 0xfffff000000003ffffffffff80000003fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x10c2008c200840011809012318092118085171
  | 2 => 0x32441114645004506883104528824b0862c4b4
  | 3 => 0x4108aa2082a222a60444aa0845509463050a0a
  | 4 => 0xe596cc494a3aab3bb550881276640633b80fc0
  | 5 => 0x861888718cc333ccc666cc9c04401843d7a000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfafafaaafaa0fa00fafafaaafaa0fa00fafafaaafaa0fa00fafafaaafaa0fa00fafafaaafaa0fa00fafafaaafaa0fa00fafafaaafaa0fa00fafafaaafaa0fa00, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36388
namespace PEqualNP.Outside.L_meta_36388
open PEqualNP.Outside.L_meta_36388.Model
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
  | 0 => 0x1ffffc0ff0f87c3fc3f87fff87f0383e99f793
  | 1 => 0xe0787ff0ffff87c3fc3f8703f87fffc166c9fc
  | 3 => 0xff807fff00fffffc003ff803ff803fff870e1f
  | 4 => 0x7fffff0007ffffc00003ffffc001f80fe0
  | 5 => 0xffff8000000007fffffffffc00000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x4310046201108004c04809198091888c085391
  | 1 => 0x490088a240400881441882288824928422c0b4
  | 3 => 0x842551042aa445582225504255022531850c0a
  | 4 => 0x96566248a835566eaa844093664b0119d80f40
  | 5 => 0x1864438cccc667b3333664e0440c0621f7a000
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaaeeccee00eeeeeeaaeeccee00eeeeeeaaeeccee00eeeeeeaaeeccee00eeeeeeaaeeccee00eeeeeeaaeeccee00eeeeeeaaeeccee00eeeeeeaaeeccee00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36388
namespace PEqualNP.Outside.L_meta_36388
open PEqualNP.Outside.L_meta_36388.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x40e225c59e004c00c30587840000005248ce9a2001300000000d00500a12a011250418d83321d200389c01f14804831541c8153003042000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x8437e53086faa610df14c21bf29043ef32087d86410df94421fb98843f431087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d02fca5a05f54b40bf28e817d51d02faa9205f94e40bea9c817e52902faa5206f90a40de214817e51902faa3205f94240dfa0481fb40902fea6a05f14d40bfa9281ef52502dea4a05f14940f6292816c52502fea2a05f14540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea98817e52103dca4205b94840bea9081ed52102daa4206f90840de210817e51103eca2205d94440bea8881f551102eaa2205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30bf28e617d51cc3f681987e10330bfaa4617e548c2faa9185f15230bea9c617e528c3dca5185b94a30bea9461ed528c2daa5185f94630fb28c6176518c2faa3187d54630baa8c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130ef21a61dd434c2fea4985f14930bfa8a617c514c3f66098778c130bfaa0617e540c2faa8185f15030bf298617e520c2faa4185f94430bea88617e500c3f680187e10030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c83de65907b0cb20bf28e417d51c83de43907b48720fda0641f840c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5107bd0a20f6214417e51882faa3105f94220f790441fb20882fea8906fd51209faa2417e54482faa8905f15120de2a2413c54482fea6905f94d20bea9a417c53483dc84907b50920f799241ec32482fea2905f14520f790a41ed21483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20bf29041ef42083d884105f94420fb288417651082faa2107d54420baa88417e50083f680107e10020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43ee63887d0c710fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fda0421f840843f461087e4c210fd10421f920843ee21087ec4210bfaa2217e54442faa8885f15110bfa9a217e53442faa6885f14d10bfa92217e52442faa4885f14910fb20a21f541443ee62887d0c510fb10a21f521443f680887e10110fd18221f930443f440887e48110fd88221f610442fea8085f95010beaa0217c54042fea6085f94c10bea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0xf4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1fbd4943b7a92877c5250fd8a4a1db14943bfa8a87f75150eeea2a1df14543fa28a87745150efea0a1fed4143bda82877c5050ff0a0a1de14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0afca3a15f54742bf286857d50d0afaa9215f94e42bea9c857e5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a857c5350bde84a16f90942bfa8a857c5150afea0a17ed4142bda82857c5050bf0a0a15e14142bf2a0857e5310afaa6215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332f7a1665ec42ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbde6499778c932bfa8a65f7514caeea2995f14532fa28a6574514cafea0995f14132bfaa0657e540cafaa8195f15032bf298657e520cbde84197b10832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef50f41bf296837d52d06fca1a0df54341beaa4837e53906faa720df94a41f7294836e52906faa520fb54a41b6a94837e519077e8320fdd0641bf28483fa50906f4a120df54241fca84837950906fea6a0df14d41dfa1a83bd43506fea4a0df14941fba0a83be41506fea0a0df14141bf2a0837e53106faa620df94841bea90837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331bf296637d52cc7ee8398fd10731bf286637d50cc6fea918df95231beaa4637c548c6faa718df94a31bea9463de328c7b86518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131bfa9263ef524c6dea498df14931f6292636c524c7ee6298f78c531bfa82637c504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618df94831f7290636e520c6faa418fb54831b6a9063de320c7b86418df94431fba0863f4410c7be6218fd8c431ee98863f5310c6fca018fe94031bd280637d500c7f2a018de54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21f7a1643ec42c87dc6590fb4cb21fb98e43f431c86fca190df54321bfaa4437e54886faa910df15221bfa9c437e53886faa710df14e21bea9443ef32887d86510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a43df53486bea690df94d21bea9a437c53487b8a690d714d21f7a1243ec42487dc6490fb4c921fb90a43ee21486fea090df14121bfaa0437e54086faa810df15021bfa9
  | 2 => 0x4e00028a0002700000000000000000000000004ca000f78002de2381509208c2b00000000000000000000608b4880000228f80be00054c0b80039e544c300000055c000000000010780000091c000004b6000000000000010800005a320000000746900000024c000000000004506f9732e00001f8003d6000000001a40000008928e5010d8cb00000000000230000b08450000cc861d53bc17d0080000082c1283c3b012400000000038000003a0000fa82200000000000000000000002c8824dd0000007d00000000000000000000000000402a0758051db10e000001812f280c0000045609800000000000000000008ec0013c0e26c88787844633c000000009900000000052ce29602521e4408c30085e0b600032e0000000045c0000010d35e3f12c0000009700025a21c00041800000829068620003d4002600001600024900000000000000000000000fe6287c0000007c40007b3943f8000103ec4143b0002b28c000000000000000004a683889000000078000e922a0080012c156280f382c05c00000000000001292351920000000000063cd8005494660001cb00000007a0437e000001b80002c4ff80044a6b4660960121049918b2940dc0022c000000001c9000000bb1160de0000022600000000000486574a404b202680732440000180000000000114168132000000562120c40000000071c3602100000000000000000000000b81447b00000000000000000794000000000000016300098c000000003fcf0000000000be192000000d88000003b0058b5000000e19720001c000000000850d4a3923466cfe91f0000000023f00085800000338964e08682f60009b1d429200000000068000681a80000000006d03200000000000000d18000001204a9100006103a0000000000000000047000000462001269000008e9041ce4303c9031e428200000000000000000000007640006b0000000000002667c000000010000000080000a000000000120000000000c00000801002000018030000040000000000c00001004000000010040180000900000400003002008048020000000080000400400806000008008020040040000200400800009000000000030000000000200000001800000010000010000000000000000c0000000201400000000004008090040040000000000001800004008000020000000000100e014000030100000000000600c008000080080100000c000000000000080300000001800000000004008010000080000400001801800002000000000040140000100200400001000004020000000040000000a0000080200c00c0000500a000020020000000100000000000000000000000000000040200200200403801bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87d
  | 3 => 0x30000000000ee800000000000140000000a800000644000000000a0b880016c000000943680001180005e76800000000000000000002fc6b939000044e9000242000001ec06a0004c0160001cc840000004646e000000490000e500000000043288000000004ae4dc0000000000000000000000798fb000000001044a0000428e2432830eb88b31a4789a0d90004b8818000006ac0003203a650319a6000000718002a4000d5007000000000000000010982407c2dc0000033a00124000000000509bc2da000001800000005e8000000001013d0bc69c000c611e0012b0ba00000000000000000c7000000000ad80000000000000000000000001e86540025d2be0000000000035800000000000000002b0868ae0f7000000000003f05e80000000000000211000314000591ba8bc001e800031c000000000005c80000013c00000000000000a900006800199000000261bb246000001130000001b07519400000000482000000691b655800000000378e88000000003e22d00000000000000000000f015a000a18002ca000000002500000015e0fa000000000000000016e3840011100000053839084000000000000000000000000000000038000000000000000007200000029c0003b0008d0610000000000007e0000000010b000000330004a84ac210004400000012f3586e4000521fa8dc431fb2221850a80016800000122000020000e100092c530004c461cc4000000000000c40000010e8000008f4000d40000000d80000000000000000001330001508a800000000001190a5000000000000001680003d000244371e148a00000000000000000004784ec180000000009c0003cc3c4aa1dc204194001832407b4238670000600000026a7f8000533a6848001422fe2680013024e27474000236190e21f2000344001a53d200ccb0001a6288f99c636a15c4821f00029000027000000750000000000011d00000000088000000000002b4000000b048024c00000000518fb8290883ac0000037a870001660000000000c000000001fc4be4e8000001f2001260001760000000000000015800000000001fa00000127000154000000000000006720529a2bcfc80012e6b83d000000000001901b081cdb0000004fc6a80029e59c0001c39878c000fa21499c000000000000000000000000000000000000002ea300000000003046d000000128968003261752f18c000000001071363b428000000000000000000008314c4aa0005722400000000000000150db8ee0005d0df000254380000000000000009e466001108000000000000013e000e68b246c000000000000000019a0005f426800000001309c803e000000003448e00008d43c000001311467a9148e730a000001172aa788000774a21a85e0823801545c0013be0012797e00000000
  | 4 => 0x6240005b2ee90806a3e0005acd993e48c7b9139a1024000b10000005a85980000067800000000000000cd42e0e50108c400000928002663bc00000000000
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x553d026e62947409b58a51d036852d0140cb14a40503586054c40d394e521034d5394840d394d521034d5354840da181521032d5290840d594e51103555394440d994a51103655294440dc98251103565354440d554d51103665254440d9549511023f6550040ab189401027b6550040ba189401026e62d53309b58b54cc2d86050f30b658c40cc26e62d52309b58b548c27661d52309d587548c26e62152309b588548c27661152309d584548c3665294630d954a518c3726094630d9949518c36552546309bd89544c26c62551309dd85544c27461551309ed81544c25c6550d309b988514c26d62145309bd89540c26c62550309798c540c26e62150309b588540c27661150309d584540c2796510030ce550400c25f654c0309ed95300c2776154f209d18553c82e86050b20b318d21c82e96210320ea90840c825e63152209758c548827661152209d584548827661d4e209d587538823e64951209bd89544827b60551208f994544832d62151208f992534823d6494d208fd91534823c6454d209dd8553482746154d209b996424832c54909209b195424832c5450920ba181424826e65cc920cb15332482ea60cc920cb150324832c54c8520cb15121482cc6348520ce153204832c54881209d987540827561d50209798c540825d63150209b988540827661150209d584540826e62d4c209d987530827561d4c208f990530823d6414c209d98453082756114c209b597420826d6510820d9d0951083644254420dc54740082796510020ea10840083715110020d9547200837151880209bd9520082ac6448020d9545200827b6548020ae191200837151480209b98b54c426d62d53109bd8953c426c6254f108f99053c423d6414f109b98853c426d6214f108f99352c423d64d4b10b958a41c42b5640c710d554c31c42e5620c710b518d21c426f62552109b189548425e63152109758c548426e62152109b588548426e62d4e109b58b538425e63d4a109758f52843395410210b658c40842e96210210ba58a30842b8644821097d8d544425c63551109bd89544426c62551108fd91534423c6454d109bd89534426c6254d108fd91524423c645491097d8d524425c6354910b958a41442f260905109d195414427665cc510ad59031442e5620c510bc98031442746548510b518d214427a65d0110b658c40442e96210110bc98440442e9628c110bc9863044278654c1109e19520442b86448110f8485204426e62d50109b58b540427a60d50109798c540425d63150109b988540426d62150109d984540426e62d4c109b58b530427661d4c108f990530423d6414c109b988530426d6214c109e980530426d65948109b988520427661148109e980520436552c40109e596100436952840109dd95100436552440109ed9510043695244010
  | 1 => 0x700404000020000100000000000000000006000000140000400004000340000006008020000200001008020000500000000000000000000000020140000004004000040300000010030080e01c03000019b98a51d0e6d62947439e98251d0e7960947439b98a5090e6d62942439d9865090e756194243d9d4b5150f6452d4543d9d485150f645214543dad4b5050f6852d4143dcd475050f7051d4143dad485050f685214143dcd445050f7051141438fd954310e5f6550c439e98251d0a7960947429d9845050a756114142dad085050b3a4214142dc9845050b7161141429dd855310a746154c428fd954210ab860508429bd954210ae860508429e98354cca7960d53329d98650cca7561943329d987548ca7561d52329e983548ca7960d52329d986544ca7561951329bd89544ca7761551329d185544ca7b60551329e181544ca7a60145329e580514cb673214532d58c8514cb726014532dc580514ca7b60550329e181540ca7661150329d584540ca7a60150329e580540ca6d6510832cb550420cacd631083297d95320cad4614c8329bd95320cae4614c832ad18543d076a5294241da54a509076a5254241da549509066e62141419b588505066f6254c419b189531063f65504419dd95411066f62553319b18954cc67b60553319e18154cc66e62943319b58a50cc66e62d52319b58b548c67a60d52319e583548c66e62951319b58a544c66f62551319b189544c67761551319ed81544c6786055131d914b314c74c528c5319b98b540c66d62d50319e983540c67960d50318f596540c73461550318f990540c66e62150319b588540c67a60150319e580540c72e5494831cb552520c72e5454831cb551520c7646154831d354a320c73554d04319d594410c6d5631043197d95310c6cc624c4319dd95310c6e4624c431ce952500c7395494031da94a500c7695294031ce951500c7395454031da949500c76952540319ed8154c86786055321b918532c86e5620c721f18c831c867a60d52219e583548863e6414e218f590538867a6014e219e580538865e63951219758e544865f63551219718d544867b60551219e181544865e6394d219bd8953486776154d2197994534874d6214d219b997424874c53d0921b9987424874c53109219b996324874c538c9219b195324874c534c921b9185324875453c8521d314e214866e62d50219e983540867960d50219798c540865d63150219e980540867960150219e983530867960d4c218f990530863d6414c219b988530867a6014c219e580530866d65cc8219b5943208675650c421f10c8310866f6548421b318d21086776548421b518d210876b3254021da0c950087733154021dc0c5500876b2154021dc88550087692154021dc485500866f6254f409b18953d02776154f409d18
  | 2 => 0x65000ce1149624a000004f9706a00000252000000000089a9600000a406213800000000000000000000b824834002241d89e9921ca0800000003e12a589886c24c7e8007aaa4002e620000001ce6f9d8a88743a88cb22dc068d8002604d800240560000098b0c7b8505d09886a8c00304a980000000489f64e000b0000001f0000fa2ab2ec2000499d26e80000086310009212400000000000018a001c4000004e920000000000000000a4800000e47f000bc00000000000000000000000178000023c000000000000000402f6002ba00000c5800c48102c80e001fe000009c000000dc118fe940000000067800412cc0b0000a000002b87707200000000008b0001080000000000001f000001f23d878978000000000000002fa0000000000af80000000708009a01800000000003f000cca06090ac00000002e2000c07e0008e09c34800000000028035000000003b0002580000310470000005a00000000009baf44200000000b900c0e9400c0000ba841ba18968000000000000000000000000000130540014a2e800610000000000286b5a78b63002085800314ac8006b800002eecd000001307780000000b4000002f8841e00000001948ca000210006396ec38000000033a0a000009f0005a812b50da002ec2d800001320004a00000001ac00000a6800000000010a6000000306660000026a000086a81e000000028e87b2a0000000000000f06cb1ea510268a0c45956000000020251000000524180000000cd800ab8000000000236850bcbf800002a0000b4ac0c600000518007b19c0000000000c28005a00000000002cecc1d4000001b0c80000000000c60006400084800100004f0e03d23a7d1e2ad8009000008000ab23000208740889d8006f24e0d80000200533242c0000e29c8a19688a980007a5e2e82f9826925c6d31a000940000000048000000003c1a8003987e468002900000000ce80091a56c700000000009c6b68002a3260012e1702a0000075868000a200000000d69f8d000000768000000032800000005796000000479b6000002381400186002ca3a17e002f200000790000020ead000000de00000002c69d0c28108a2832c669ca3b80499a6c002aa8a9c86300000000000003c80000000000225f15c00000bf000330001111238800002c2002726e25491000af0002b80000000001e8000a6c0a3e000320297a700000028a000000000000000002340000068000002e00000019a167310c0722e598008c8600017226800002880000064950002dea7800c80000015a909524d10e0000100806000140000600c010000000c000080002400000050080100400000040000200000000000040000000000000000000403004020000600001008000000200001004000000001006000000040200000000050040001c0303
  | 3 => 0xf976aa2ea0007009a7a69942000000006400000001180016c4a00079800000005500000000002c40000000220442d25912cc881600000560005380
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x259205800001400b5401c610d2971432400004cf3800113004080018c38000a2014a1c15410832988e2b18841956170185520c662392c6208639114e61d09219c2e130e8490e44531853248670b80c299243d00c83154021a90e690aa010d507348550086b0b88c0a90814a1c95410030c50a830284904e17118142483142a4c199241385c660cc920c18a831a4290720425444008312322a2900418c1915148020a88e4a9863885287255040843503224290221701cd2148110
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x200800400600c40535c261d0921c40535c0614c921c20545c46050920c20545c660cc920c80641cd2148110
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 616
  | 4 => 414
  | 3 => 25
  | 2 => 5
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
  | 6 => packedAt s3K6 (718+((h/13+packedAt s3K6 (640+(h % 13)*6) 6) % 53)*7) 7
  | 5 => packedAt s3K5 (18887+((h/205+packedAt s3K5 (16632+(h % 205)*11) 11) % 1309)*11) 11
  | 4 => packedAt s3K4 (17112+((h/138+packedAt s3K4 (15732+(h % 138)*10) 10) % 798)*10) 10
  | 3 => packedAt s3K3 (1273+((h/8+packedAt s3K3 (1225+(h % 8)*6) 6) % 37)*6) 6
  | 2 => packedAt s3K2 (304+((h/1+packedAt s3K2 (300+(h % 1)*4) 4) % 11)*4) 4
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xf83ffffe03ff841f1e3fc3ffffc3fc0038fe7c
  | 1 => 0x7fc07e1ffc1fffe01fc7fc3c07fc3ff8cf338f
  | 2 => 0x7fff801fffe007ffe007ffc007ffc0070fc3f0
  | 4 => 0x8000001ffffffffffff8000007fffffff003ff
  | 5 => 0xffffffe0000007fffffffffff8000007fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x985148238412c030608d15472d1545018563c
  | 1 => 0x109308a448ca24a00a435518915519304b3285
  | 2 => 0x230a2cc89187356d20059991259990a30dc3d0
  | 4 => 0x62c51112214025654900002462222c5b0016a
  | 5 => 0x44306001c31843989926222380000306e6a800
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xfefeeaeaecec0000fefeeaeaecec0000fefeeaeaecec0000fefeeaeaecec0000fefeeaeaecec0000fefeeaeaecec0000fefeeaeaecec0000fefeeaeaecec0000, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36388
namespace PEqualNP.Outside.L_meta_36388
open PEqualNP.Outside.L_meta_36388.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x3210628360000042240000075629007c0104e3569a00003aa00007980a452940001216100011e14383004001180245c983382d30000000ab44540c18008381800c00001080c080ff43bf43fe43fd43bd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20ef20fe20fd20ed20fc20ff10f710fe10fd10f510fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x4b6d660f2a5e4468151f0028570a7038000023000e427136290c1b433c6319306e005b3a32072c2f5f465005005426186221481e116c0b2572522e27005d001c10134d0d594155000069743d02001a06516a17014a165322456f656700614c2b3e2431001d5a33490940030056582d3b003f086b000014600400374e475c39000000124f0000007364353420000c008b808000010000000981828a028181870700018005010185048200000182000000008c0000cf55243b7a92876c5250eeea2a1dd14543bda8287785050f3ea6a1ebd4943d629287b75150f68a2a1eed4143dc282873e5410eeca3215d54642bd28485795090a7ca9994f55332bba8a6574514ca7ca8194f55032bb2886575510caf4a0195e54032b7294836d52906f4a120de542419f2a6633d54cc6dea498db149319f2a0633d540c6dca418db54831bd2806379500c7ca4210de94021bca80436e52902daa5205d94640baa8c815e53102baa6205b94840b6a90817651102eaa2204f953309eaa6619d43cc2dca5185b54a30bb28c6175518c33a86984f950309eaa0616e520c2daa4185d94430baa8861af43c835a87905b54a20bb28c4175518827ea8904f15120d7aa241ac544835e86906b50d20f5a8241eb40483d080907a8c120f4982416e52082eca2105d54420dba1e21b543c43ce41887948310b7294216d52842eaa3087a482109faa2213c54443d240886dd5110da2a221b7434436a86887cd4110f9a0221f040443e460887c4c110f390221f220443ca40887c48110f0902216e52042daa4085d94410
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x80041a280622026a0e00000ca9c794096912188b8402c180003100109ca1485050f3051141439c580514ca696014931d8485500862c6550d20b258c40482e16110120b85863048389434c120ca15120442346550d10b458c40442e16210110b858a3044391434c110b858a20442b06448110e8d9120443a06448110e8d5120443a05448110e8d0d20443a14348110
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x32100a44ebb2240884a276d5120442503b28690221481d54348110
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
  | 5 => packedAt s4K5 (841+((h/15+packedAt s4K5 (736+(h % 15)*7) 7) % 67)*7) 7
  | 4 => packedAt s4K4 (3471+((h/39+packedAt s4K4 (3159+(h % 39)*8) 8) % 141)*8) 8
  | 3 => packedAt s4K3 (960+((h/8+packedAt s4K3 (912+(h % 8)*6) 6) % 34)*6) 6
  | 2 => packedAt s4K2 (199+((h/1+packedAt s4K2 (196+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xf87fffe07c3e1f0e38ff0ffff8783c1e18fe93
  | 1 => 0x7f83e1ff803fe1f03f1ff0f03f803fe06f331c
  | 2 => 0x7ffc01ffffc001ffc01fff003fffc0018fc3e0
  | 3 => 0x800001ffffffffffffe000003ffffffff003ff
  | 5 => 0xfffffe00000001ffffffffffc0000001fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xb0848230944a902082345519a28944c085691
  | 1 => 0x11388a4519988b30190d5462aaa119c42b3314
  | 2 => 0x2211cc8a310ccd5640166645333390888dc3a0
  | 3 => 0x442111040200088a24000080444221150004a
  | 5 => 0x4463001c623110ed3498888e00060311f6a800
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xfeeafeeafe00fe00feeafeeafe00fe00feeafeeafe00fe00feeafeeafe00fe00feeafeeafe00fe00feeafeeafe00fe00feeafeeafe00fe00feeafeeafe00fe00, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36388
namespace PEqualNP.Outside.L_meta_36388
open PEqualNP.Outside.L_meta_36388.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x1958a8f00368402d0020180000000000ad40034945804e0000000992182a3429222006000e0011f005832300807001e5ce290824980205009d44281c000002808400002010600001ff43bf43fe43fd43bd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21ef21fe21fd21ed21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fa10fd10f910fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x3b50085c0000000006261e196b640c112f600074000000007200005f2a006f520e65002e38000000004e00444a05453f37290a000000001a005710632500006c6a15002800035a0f21580001620000730002405e5b71234c312d333500176600004d1c20006d0043003047590427073d004b56135d53611f342c2b6748465524696e4f681b0d091249540b36003214183c511d3a422239703e1641008001040d8400000000028e0381090089800081000200808002800203000490858101038088804f55243b7a92876c5250eeea2a1dd14543bda8287785050f3ea6a1ebd4943d629287b75150f68a2a1eed4143dc282873e5410eeca3215d54642bd28485795090a7ca9994f55332bda826578504ca7ca8194f55032bb2886575510caf4a0195e54032b7294836d52906f4a120de54241af298835d53106dca420db54841bd2808379501067ca998cf55331cea1e636e528c6daa518de94231bca84639d434c67ca818cf55031b7290636d520c6f4a018de54031d7a1e43ad43c86daa510de94221bca84433f5448678a890ebd5121d62a243af434875a8690f9d4521f3a0a43e441487cc6290f94c521b7290437a50086f2a010db94a40b6a94817651902eaa3204f953309eaa6616f524c2d8a4984f950309eaa0616e520c2daa4185d94430baa88617651082eaa2107a48020b7296216d52c43ca43886ed0e10dca1c217951843d643087a486109faa2213c54443ca42886ed5110dc2a221bb434437286887cd4510f9a0a21f041443e462887c4c510f590a21f221443d242887c48510f090a216e52042daa4085e94010
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0xa8658051c02880011ab1e92e02261028801202608000000030e1811000811c0c91485150f3051141439c584504ca2c6550d21b158c41486e16010521b85823148785434c52199584524c3615148020c915121442386550d10b458c41442e16210510b858a3144391434c510b858a21442b06448510e8d9121443a06448510e8d5121443a05448510e8d0d21443a14348510
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x4c10000a44ebb2242884a276d5121442503b28690a21481d54348510
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 117
  | 3 => 24
  | 2 => 4
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
  | 5 => packedAt s5K5 (841+((h/15+packedAt s5K5 (736+(h % 15)*7) 7) % 67)*7) 7
  | 4 => packedAt s5K4 (3471+((h/39+packedAt s5K4 (3159+(h % 39)*8) 8) % 155)*8) 8
  | 3 => packedAt s5K3 (960+((h/8+packedAt s5K3 (912+(h % 8)*6) 6) % 34)*6) 6
  | 2 => packedAt s5K2 (199+((h/1+packedAt s5K2 (196+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf83fe1e0fc3e1f1e38ff0ff038783c3e39f293
  | 1 => 0x7fc3ffff003fe1e03f1ff0ffff803fc04e3f1c
  | 2 => 0x7ffc01ffffc001ffc01fff003fffc0018fc3e0
  | 3 => 0x800001ffffffffffffe000003ffffffff003ff
  | 4 => 0xfffffe00000001ffffffffffc0000001fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xb884a262954a906182b45529a28949c18f291
  | 1 => 0x1098884219888b2009055461aaa119840a1714
  | 2 => 0x2111cc8c510ccd6a40166645333391088f43a0
  | 3 => 0x422111080200090a24000080444222160004a
  | 4 => 0x46230018e23110dd3498888e00060231f5a800
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfeecfe00feecfe00feecfe00feecfe00feecfe00feecfe00feecfe00feecfe00feecfe00feecfe00feecfe00feecfe00feecfe00feecfe00feecfe00feecfe00, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36388
namespace PEqualNP.Outside.L_meta_36388
open PEqualNP.Outside.L_meta_36388.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xb004001a1af002100f5724000001300c5500600078000759224c5c03e000001f1c808800000000000000066e82273c0003f4a044a86cedb8036000005a01c2c68706190e8c0166a154b928000005e28a8206ac00624200180a000800006080040000084000c406000410002ffd5009fe54007f55009fc5401ffd4c077f5301ff94c07fd5301df54c07fc5301ffd0c07bf4301ff90c07fd4301ef50c07fc4302ffd4801fe52007f5480bfc52027fd0801fe42007f50809fc4201ffcc807fe3201ff4c807fc3202ffd4405fe51007f54405fc51027fd0405fe41007f50405fc4101ffcc405fe3101ff4c405fc31007fc8405fe21007f48405fc2102ffd4003fe50007f54003fc50027fd0003fe40007f50003fc4001ffcc003fe3001ff4c003fc30007fc8003fe20007f48003fc20017fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a4000df1952002cf8ca90003ff64480017fb22400bff99120025fcc890003fd64480017eb22400bff19120025f8c890033ff5448017ff2a24000ff5512005ff8a890027ff63480137fb1a4009ff98d2001dfcc690027fd63480137eb1a4009ff18d2001df8c690027ff5348013bfa9a4009ff94d2004ffaa6900277d5348013fe29a4009ffd0d2004f7e8690027fe4348013fea1a4009ef50d2004ff88690006ff6248019ffa924000ff94920007dca490003fd5248001f6a92400cff1492005ffe849002fef4248001ff2124000ff5092005ff8849002fec4248013ff9924009ff8c92004fdc6490027fd3248013f69924009ff0c920007fec290002ff6148015ff30a4002bf98520007fac29002bfc61480057e30a400cffd4520057fca290003fd5148015fe28a400bffd0520057fc8290003fd4148015fe20a4009ffcc520057fc6290027fd3148015fe18a4000ffc8520007de429002bfe2148001fe90a4000fb48520057f84290006ff6048003ffa824001ff9412000ffaa090007fc5048003ffa024001ff9012000ffa8090007fc4048003ff9824001ff8c12000ff46090007fd3048013fc9824001ff0c12000ffe4090003fb2048003ff1024001fb8812000ff84090007ec2048003fc1024001ffc412000ffc2090007fa1048003fe0824000ffd9510005feca8801ffe654400b7f32a2000ff59510005faca8801ffc654400b7e32a2000ffd9110005fec888023fe64440097f3222000ff59110005fac888023fc64440097e3222007ffd5110047fca888003fd5444011fe2a22006ffd8d10035fec68801bfe63440077f31a2006ff58d10035fac68801bfc63440077e31a2006ffd4d10036fea68801bfe534400dfea9a2006df54d10037f8a68801bff434400ddfa1a2006ff90d10037fa868801bbd434400dfe21a2000ffd8910005fec488003fe62440017f3122000ff58910005fac488003fc62440017e3122007ffd4910007fca488003fd524400ffe2922008ffd0910007fc8488003fd4244011fe2122006ffcc910037fc648801bfd324400dfe1922001bfd8510017fea28800bfe5144005fb28a2002ff54510007eaa28800bfc5144005ffa0a2008fdd0510017fc828800bfd4144005fe20a2002fd10510017fe628800bfe3144005fb18a2002ff4c510037ea628800bfc3144005ff90a2002ff88510017ec428800bfd2144001fa90a2002ff0851000dfec088007ff504400ffda822001ff9411000ffaa088007fc5044003fc2822001ffd011000ffc8088007fa4044003fea022000fe5011000ff88088007ff3044003ff1822001fe8c11000ffa608801bf93044003fe1822001ffc811000ffc4088007fa2044003fe9022000fe4811000ff84088007ff1044005fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x7ff3054003ff182a001ff4c15000ff860a8007fe2054003fe102a001ffc415000ffc20a8007fc1054001ffb2a8000bfd95400a7fccaa0016fe6550001feb2a8000bf595400a7f8caa0016fc65500037fb228004ffd5140027fca8a0013be5450009feaa28000ef55140027f8a8a004fff63500277fb1a8013ff98d4001dfcc6a004ffd63500277eb1a8013ff18d4001df8c6a004fff5350027bfa9a8013ff94d4009ffaa6a004f7d5350027fe29a8004ffd0d400277e86a0013fe4350009fea1a8013ef50d40027f886a0003ff62500017fb128000ff98940007fac4a0003fc62500017e3128014ffd4940007fca4a0003fd5250029fe2928004ffd0940027fc84a0013fd4250009fe2128013ffcc94009ffc64a004ffd3250027fe1928000ffd8540005fec2a004bfe61500057f30a8000ff58540097f8c2a000afc6150029ffa8a8012ff94540007faa2a004bfc5150009ffa0a8004ff90540027fa82a0013fc4150027ff98a8012ff8c54009ffa62a004bfc3150001ff90a8012ff88540007fa42a004bfc21500037fb028001ffd414000ffca0a0007fd5050003fe2828001ffd0140027f680a0007fe4050003df2028001ff1014000f7880a0007f84050003ff9828001ff8c14000ffa60a0007fc3050003ff1028001ff0814000ffe20a0007fe1050003fd0828001ff0414006ffecb90002ff65c8023ff32e4005bf99720007facb90002fd65c801bfe32e4005bf1972006ffec990002ff64c8021ff3264004bf99320007fac990002fd64c801bfe3264004bf1932008ffea990043fe54c8001feaa64010ff1532006ffec79003eff63c801fff31e4003bf98f2007ffac79003efd63c801bfe31e4003bf18f2007ffea79003f7f53c801fff29e400fff54f2007efaa79003ffc53c801fffa1e400fefd0f2007ffc879003ffd43c801fdea1e400fff10f2000dfcc590047ff52c801bff2964000fb94b20007faa590003ed52c801bfe2964010ffd0b20087de8590037fe42c8001fea16400dff10b20087d8859003fff32c801bff196400ffb8cb2007ffa659003fed32c801bfe196400dffd8720077fcc39000afe61c8001feb0e4000bf5872006ff8c39000afc61c8023ffa8e400eff94720007faa39003bfc51c8021ffa0e400eff90720007fa839003bfc41c801fff98e400eff8c72007ffa639003bfc31c801bff90e4000fbc8720077fc4390003fd21c8001f690e400dff0872000dfac190007ff50c8003ff2864001ff5432000ff8a190007ff40c8003ff2064001ff5032000ff88190007ff30c8003ff1864001ff4c32000ff86190007fe20c8003f71064001fe8832000ff84190007ec20c8003ff8864001ff8432000ff82190003ff65480017fb2a4000dfd9520004feca90033fe654800b7f32a4000ff59520005faca90033fc654800b7e3
  | 2 => 0x21017fa639080bfc31c8405ff10e4202fb88721017ec439080bfc21c8405f610e420dffd83210e7fcc190806fe60c8401feb064200bf5832106ff8c190806fc60c843fffa86421cff943210e7f8a19087bff40c8439ff206421cff103210effe6190873fe30c843bfe986421cff0c3210e7fc4190837fc20c8405ff8864202ff84321017f82190803ff65484017fb2a421bff9952102dfcca90803fd65484017eb2a421bff1952102df8ca90803ff64484017fb224200efd91210057ec89086bfe64484097f3224200ff59121005fac89086bfc64484097e3224200ef1912102578c89086fff5448435ff2a24200ff551210d7f8a890867ff63484337fb1a4219ff98d2101dfcc690867fd63484337eb1a4219ff18d2101df8c690867ff5348433bfa9a4219ff94d210cffaa6908677d5348433fe29a4219ffd0d210cf7e8690867fe4348433fea1a4219ef50d210cff8869080aff6248437ffa92421bfbd4921007fca490803fd5248437fe292421bfb149210d7fe8490803fe4248401f72124200ff50921007da849086bfc4248433ff9924219ff8c9210cfdc6490867fd3248433f69924219ff0c921015fec29080bff5148405ff28a4202ff54521017f8a29080bff4148405ff20a4202ff50521017f8829080bff3148405ff18a4202fd8c521017fa6290867f53148405fe18a4202ffc8521007ee429080bfe2148405f710a4202ff08521017d8429080bf42148401ffb024200bfd81210c7fcc090806fe6048401feb024218ff1812100df8c09086fff5048431ff2824218ff141210d7fe8090863fe4048431fe2024219ffcc1210c7fc6090867fd3048431fe1824218ff881210c7f8409080bff1048405fb8824202ff84121017f82090806ff6554001ffb22a000bfd91500bffcc8a8012fe6454001feb22a017ff19150025f8c8a8017ff545400bff2a2a005ff5515002ff8a8a805bff635402d7fb1aa016ff98d5001dfcc6a805bfd635402d7eb1aa016ff18d5001df8c6a8017ff535400bbfa9aa005ff94d5002ffaa6a805b7d535400bfe29aa016ffd0d500b77e86a805bfe435402dfea1aa016ef50d500b7f886a8003ff62540017fb12a000ff98950007fac4a8003fc62540017e312a005ffd495002ffca4a8017fd525400bfe292a017ffd0950007fc84a8003fd425402ffe212a016ffcc9500b7fc64a805bfd325402dfe192a000ffd8550005fec2a8057fe61540057f30aa000ff585500aff8c2a800afc615400bffa8aa005ff9455002ffaa2a8017fc515402fffa0aa015ff90550007fa82a8057fc415402dff98aa015ff8c5500b7fa62a8057fc3154001ff90aa015ff88550007fa42a8057fc21540037fb02a001ffd415002ff6a0a8007fe5054003bf282a001ff1415000ef8a0a8007f85054003ffa02a001ff9015000ff880a800
  | 3 => 0xea1aa224ef50d51127f886a8803ff62544017fb12a200ff98951007fac4a8803fc62544017e312a205ffd495102ffca4a8817fd525440bfe292a225ffd0951007fc84a8803fd425444bfe212a224ffcc951127fc64a8893fd3254449fe192a202bfd8551017fea2a8817f75154405ff28aa202df94551017f8a2a880b7c5154405fa28aa202ffd0551017fc82a880bfc4154405ff98aa202ff8c551017fa62a880bfc3154405ff10aa202ff08551007fec0a8802ff6054447ff302a201bf98151007fac0a888ffc60544037e302a205ffd415102ffca0a8817fc505444bffa02a223ff9015111ff880a8893ff3054447ff182a224ff4c15111ff860a888ffe2054447fe102a202ffc4151017ee20a880bfe1054405fe082a200ffd9541005fecaa088bfe655040b7f32a8200ff59541005facaa088bfc655040b7e32a8202bfd9141027fea8a0813fe5450409feaa28204ff1514110ffec6a0886ff6350443ff31a8203bf98d4110ffac6a0886fd6350443fe31a8203bf18d4110ffea6a08877f5350443ff29a8221ff54d4110efaa6a0887fc5350409ffa1a8204efd0d41027fc86a0813fd4350443dea1a8204ff10d41007fec4a0802ff6250401ff3128200ff58941007f8c4a0802fc6250445ffa928200ff94941007faa4a088bfc5250409ffa128204ff90941027fa84a0813fc4250443ff9928221ff8c94110ffa64a0887fc32504057fb0a8202ffd4541017fca2a080bfd5150405fe28a8202ffd0541027ee82a080bfe4150405df20a8202ff105410177882a080bf44150405ff98a8202ff8c541017fa62a080bfc3150405ff10a8202ff08541007fec0a0802ff6050441ff3028201bf98141007fac0a0883fc60504037e3028222ffd4141107fca0a0883fc5050409ffa028204ff90141027f880a0887ff3050441ff1828221ff4c141107f860a0883fe2050441fe1028202ffc4141017fc20a080bfc105041bffb2e4200bfd97210fffccb90816fe65c8401feb2e4200bf5972106ff8cb90816fc65c841bffb264200bfd93210f7fcc990812fe64c8401feb264200bf5932106ff8c990812fc64c843fffaa6421eff95321007faa99087bfc54c841bffb1e421dbfd8f210effcc79080efe63c843bfeb1e421dbf58f2106ff8c79080efc63c843bffa9e421ddfd4f210effca790877fd53c843bbea9e421dff14f210effe8790877bf43c843bff21e421dff50f210ef7a8790877fc43c84057f316421fffd4b210ffdea590837fe52c8401fea96420dff14b210ffd8a59087bff42c841bff2164200fb90b21007fa8590803ed42c841bfe216421dffccb2106ffc6590877ee32c843bfe996421dfb4cb2106ff8659080afd61c8405ffa8e4202ff94721017faa39080bfc51c8405ffa0e4202ff90721017fa839080bfc41c8405ff98e4202ff8c7
  | 4 => 0xbbfc4054861ff982a42eff8c152187fa60a90bbfc305485dff102a42eff0815217ffe20a90bbfe105485dfe082a40dffd9642005fecb210b7fe659080b7f32c8400ff59642005facb21037fc659080b7e32c8404bf59242027fea921013fe5490809feaa48404ff1524206ffec7210b2ff6390859ff31c8403bf98e42167fac7210b2fd639081bfe31c8403bf18e42167fea7210b37f5390859ff29c842cff54e42166faa7210b3fc5390809ffa1c8404efd0e42027fc8721013fd4390859dea1c8404ff10e42025fcc5210b7ff529081bff2948400ff54a4206ff8a521013ff4290809dfa148404fbd0a4206ff88521013ec4290859ff994840dff8ca42167fa6521037fc329081bffb0c842bff98642015fcc321003fd61908017eb0c840dff18642015f8c3210b7ff5190857ff28c842bff14642027fe8321013fe4190857df20c8404ff106420277883210b3ff3190857ff18c842cff4c64215ff863210affe219081bfe10c840dffd8242157fcc121006fe6090801feb048400bf5824206ff8c121006fc609085bffa84842aff94242157f8a121013ff4090809ff2048404ff10242167fe61210abfe3090859fe984842aff0c242157fc4121037fc2090857ff884842aff84242157f82121003ff65508017fb2a8429ff9954202dfccaa1003fd65508017eb2a8429ff1954202df8caa1012ff6450809ffaa28404ff95142027faa8a1013fc5450851ffb1a8428bfd8d42147fcc6a100efe6350851feb1a8428bf58d42147f8c6a100efc6350851ffa9a8428dfd4d42147fca6a10a3fd5350851bea9a8428ff14d42027fe86a1013bf4350809ff21a8404ff50d421477a86a1013fc43508097fb128429ffd4942007fca4a1003fd5250853fe2928404ffd0942027de84a1013fe4250801df2128404ff109420277884a1013ec4250851ff9928428ff8c942147fa64a10a3fc3250801ffb0a8400bfd854213ffcc2a100afe6150801feb0a8427ff18542015f8c2a10a7ff515084fff28a8427ff14542027fe82a1013fe4150809fe20a8428ffcc54213ffc62a10a3fd315084ffe18a8427ff8854213ff842a1003ff60508017fb028426ff9814200dfcc0a1003fd605084dfe3028401bf1814214ffea0a109bfe505084dfe2828404ffd0142027fc80a1013fc4050851ff9828426ff8c142147fa60a109bfc305084dff1028426ff0814213ffe20a109bfe105084dfe0828402bfd9551007fec8a8802ff645444bff322a204bf99151007fac8a8897fc64544097e322a205ffd515102efea8a8817fe545440bfeaa2a200df5515102ff8a8a8893ff63544497fb1aa224ff98d5101dfcc6a8893fd63544497eb1aa224ff18d5101df8c6a8817ff535440bbfa9aa205ff94d5102ffaa6a88937d535440bfe29aa224ffd0d511277e86a8893fe4354449f
  | 5 => 0xd54007fec4aa002ff6255001ff312a800ff58954007f8c4aa002fc625500bffa92a805ff14954027fe84aa013fc4255071ff992a838ff8c9541c7fa64aa0e3fc3255001ffb0aa800bfd85541bffcc2aa00afe6155001feb0aa837ff18554015f8c2aa017ff515500bbfa8aa805ff9455402ff8a2aa013ff4155009ff20aa804ff105541c7fe62aa0dffe3155071fe98aa837ff0c5541bffc42aa0dffc2155001ffb02a800bfd81541b7fcc0aa006fe6055001feb02a836ff1815400df8c0aa017ff505500bff282a805ff14154027fe80aa013bf4055009ff202a804ff101541c7fe60aa0dbfe3055071fe982a836ff0c1541b7fc40aa0dbfc205506fff882a836ff841541b7f820aa016fd659481bffb24a435ff99252025fcc929003fd64948017eb24a40dff19252025f8c929017ff549480bff2a4a405ff5525202ff8a929037ff63948697fb1ca434ff98e5201dfcc7290d3fd63948697eb1ca40dff18e5201df8c729017ff539480bbfa9ca405ff94e5202ffaa7290d37d539480bfe29ca434ffd0e521a77e87290d3fe4394869fea1ca434ef50e521a7f88729016fe629480bffa94a405dfd4a5202fdea529037fc529480bf6294a435ffd0a5206ff885290d3ff329481bff194a434ff4ca5206ff86529037ff6194867ff30ca402bf98652007fac329002fd619481bfe30ca402bf1865202ffea329017fe519480bfe28ca435ffd065219ffc83290cffc4194869ff98ca433ff8c6521a7fa63290cffc3194867ff10ca40dff0865206ffec1290cbfe60948037f304a400ff58252005fac129037fc60948037e304a405ffd425202ffca1290cb7e509480bfe284a405df142521affe81290cbfe4094865fe204a434ffcc252197fc61290d3fd3094865fe184a432ff8825206ff841290cfff1094865ff084a432ff0425202dfecaa9003ff64548017fb22a431ff99152025fcc8a9003fd6454863fe322a404bf1915202ffea8a9017fe545480bfeaa2a405ff15152187fec6a90c2ff6354861ff31aa403bf98d52187fac6a90c2fd6354861fe31aa403bf18d5202ffea6a90177f535480bff29aa405ff54d52186faa6a9017fc5354861ffa1aa430efd0d52187fc86a90c3fd4354861dea1aa430ff10d5202dfec4a9017ff525480bf7a92a405ff94952006fca4a9017fc525480bbe292a405fb1495218ffe84a90c7fc4254861ff992a430ff8c952187fa64a90c3fc3254801ffb0aa400bfd855217ffcc2a900afe6154801feb0aa42fff18552015f8c2a9017ff515480bff28aa405ff1455218ffe82a90bffe415485ffe20aa430ffcc55217ffc62a90c3fd315485ffe18aa42fff8855217ff842a9003ff60548017fb02a42eff9815200dfcc0a9003fd605485dfe302a401bf1815202ffea0a9017fe505480bfe282a431ffd0152177fc80a9
  | 6 => 0x8d4000650000d2800000090cb611e88706a800000000000000000000000065c000000000ea89d4000f4c89c00149c0013680000001bd4952680004640007f9200074f5802000026c00146c0000001e92b8ac42289c4000000001004000bec000000000c98a309900000000000005ed24c001054000000dd8470408108e09090000000001451394f0c0001240000004009e0000bdccc8001418000e14000bd40009ec000cb80000004c8000000340b54b9c0009ad0340000001d8000008000000001414000cb04a4000324fbc00000000000000400000000000000000000600400000a00200400200a00200600600600000000000000000800001600600000200000800200000402600000000000000a00200a00000001200200000200601a00200000000200a00200200200000200c00000000800000600201800000400c00000000600000200000400000200801800200000000000400200001400000000000400001800000000000400200000c00a01400800600200e00000000201200000001000001e00000000000400200800400000000000000400000001800c00800001400000000600600200600000000400c00000000600000000e00400000800001400600200e00600000200000000000000c00000000000400400000000a00000000200c00001000401601800000200000200c00600e00e00200400000400600400200400800000200000400600000400600000001c00001000000000000000200000000000000400000200200600200200000400600000000000000000000000200600e00600000600200200000001200600800000000a01a00e00a00400000200c00600800000000000200000400001000000200800400000200600000000000000002200000600201000000200000000a01000c00000000000401600400800600000000200200000000600200200400000000200200200000600600c00000200a00601000a00000400600000000000000000a00000000600600003600600400000000e00200c00e00200000200000a00002c01000000000600400400800a01600400200c00000000400400000200000e01600000c00200200000400000201200400400000200400202000002600000000000000200000600000400200600800404600400e00000004200400000000400000000200000200c00000000600000000600400400000000800600000201200001200000600000004bfd9554025fec8aa013ff545500bdfaa2a804ff95154026fca8aa013fc5455009be2a2a804ef151541c7fec6aa0e2ff6355071ff31aa803bf98d541c7fac6aa0e2fd6355071fe31aa803bf18d5402ffea6aa0177f535500bff29aa805ff54d541c6faa6aa017fc5355009ffa1aa804efd0d54027fc86aa013fd4355071dea1aa804ff1
  | 7 => 0x4000000e340001c80014f800039000000000000000047c0000000fc0000000009280000000000009dc0000010e4b4535c0015092743703c0448001194da412cd34c9435c5f0b69078ac83f400000000064c000000298668a9443c00111475915c33883c10c4b40009f02d8f9d4654bd0940e8000f48000850f64dcd31c0111584c106ca74000000000bb88b88f0fc0a7c0012446340000009bd3a40001a00000c40000008300001d4ee40d103c000000000614000d9c000000000000000f340000000000000000000013300012840000000000002a0a18f24000000000000000000000000a881f4f381a94b4984060000808dac35000130063c6fd138fe8000fa8f690dd21944400035943c7f0d885a4000000b48b90000001520000ce80012c54009f9144054e45518294fb493088caac00000060c7140003ecd3c000000d612ac000c7401c0f8f18000a49168000000838fc84ac0006e0000000000000c80000000f086f8081240000000000000000394001014ca0000bc40005f931061c00000121c0011712080013d07d0d154907a800011800019853454837400128cf2c0000007dcef4519190000efc0013bc0000000004e85e00005c44dce580000012e01f85cc000000000001499440000000000000000000568cf4ecd14c0000000000008bc000d98000000000000ce00000000008a89954e848c001008538000000864000000000d4058000000000122400000000000098c37c0000014c400000104c84400052ce806b11a8258014000000000c6d43434424839c7640412cc0000000006800000002180011a400000000000038882116c00000000000033c0005506081b84540009200009000000012700000000007c83b8000b74e60440000000598000000000000b2000000118c0000000000000000000013e539c0011a0eac000704b5ca040013f88b46a49090812b02b000000000000000000000000000003d0e8000001108238000aed0d0fd4000064000c4c000c3c9640000011f870c00125c9140000000013280000009402bc254149178af8d80db8000000000000bf50b400024c000000154000000000000000000000001370b787992990c0e50314c54000000000001454000000000dc01686c40000000002f14101cc8f526cc18500000000000001390000b14000000508e90b88000e9c00142d1b46c8884000000d0000137c00000097ce200004e42dc000004000848000001524ccc2a40000000014fc00085c000f74774000000000b0c000de06d800000000000000000028400000028d1fd21000150c4f8ded41c00122c698000c587b840c00056c1e000117400000000152cae42103fc0000000005e8180000140000f1c3cc55c87c0000003680000000001705144f10ac000000000000000000000000e6c6b8000ee00000000
  | 8 => 0x6f09b892d1f4000c100013e8070f8c8f8000000b50da0000840ff03e0d9110c0002b8c0d4380012f80000000000000000007e00000000012c80007540000000008d80000000000012c08e02e00002e80000000000002a8000000000fa101034cbe0a0057c1dd2bc000d587b4638000000750000354000000000000c04d20af086d48027000003414c0d4cd1314278a0d3c4610600fd02900011c0000001160000000000000000d1d0b8f200000484b00000007304cc001188f04c44fdc66d3c0748c5d00c59c4500000000000a4000001181258cbc3b02240008880011492940000000005b891084d0500014b87f5374cfd251320d78af4f6c00147c73c8a12dcae00007a12a0590150ec400021c13c4848180000001ad0bcb24000a644e0038ee8fb81ed0a8e8c58c0ad2d40000002c0000000000000000de51e000000102800023c0011d0a14e88d080000000000000000000000004a12d00000005d80000000011bc05d378000000000970404461364afcfe4c9cd6463111c0000013f55114f4c70030c8d1840011d92f50ec760158cc4478dc4000f14939530558a849e8a290d50c4c50de8bfd22846c5100dd3a06540014d4000dd52a8000384000a80e687cd0489d05643214e0d540000009792040000d8f507e800045d05c494001044000000000000e741d0000000000675380000000000c383a00001746b4000000000d10a6000130923400130c000000a780000000000004251e40a800000102400042c0000000c865820c0014acdf0c600006440010407940000011b8bc800000109c00000112ca6c5b4f54000000000d7c000f40ad0000858000000b34001140ec00b80000003d8c301100000012f0000dfc0001907bcd740010980013045780000000000002c80000000000010fc724950000000e480000000002080003d0e7d4cc00000000006c77095c000000c1c660524000b6478c000d50c402403ac475431354000d6c5d40007fc0000012313b8300f5ce3cb7c82c0011ec0000003f0000001198000000000000000000bbced85d115400030cc001c000000000079cc08000000b18db011c000a34778000000000000ed48940000000006cce3007c000000ae8000000b04000ca8a400000000005c85b000c1609a8144744ba50b1254364ebd058e9474cea00000010cc0000000001280000c0000ed00003300280000ccff8000001278000000a500000000000000004d00005bc000000948000dbc0000000006213dc6f4000ac06a0d2cb3c00136c000001388000000c2cb85398000104000000f3000000000000000108cf78000cc1488000f94cd8000000bd05880000013ecad82f80000000000006bc000a38000624000788ddc000000df8134a986d54280000000000000011dd0a00000011d46ace18095349484000000000718ab
  | 9 => 0xe540013240000000000005f4000000398000000000000000000000b8055400102d121404854a54000000954ef8690800378a5c1a40012d90d859462cb94a2ce640a0b304f4cac000000860000a1018c0000000000000910214e4000000000b2844ce9901804d0f82006d08c0000d70000185468fe150067c3040000000000000013cc6e40000013d50f052000000049c2151000000006700014600010600012ec0012e4000000000a9cad49593b4178cd4944000abc380000000000bf92a5350000d680000000013ac0ec8c8ba8000000000000000be800144907000000000000019411400145cd4c000000480468dc8309474d44a58aa4e280000002f4000868740204d0c0000000013440987000f400101c260eec96ccb4e1ce2d07d1b03f8001334b00ab1420000cec5dd4a400031c00000096000015c00000113d528418000000adcc900010c82200008e89e400069c00000013881000133c0012145acd8c3e86c12e80001fd0a40000000000005a00008e49749cc0003100000012205714783e4eb8f90a90000bb4f7000028068ceb13842d4000000000000000000e78804000b1cd48db40000001b4000d948c536075c000f889f400000027c6781200007ec9808dce00000000c35470000c24a0851c000000018000df4b7000123c4ec000000fc40445fc000000000e4d1ad4d0000fd88343bcdd110493400025c8d14ec000b58274000f005e44b8edc7900001f07814f0000000000000998ffc0003c8bf00006045a800000053c000438001288880000000000ea4000288bb000129c00138c26871ceb48ac2e4f10000000aa920ca706647a4084000000bac000a1c7394a03480000000bc000000000a44bc0068640f61038cf0a3c1640b00009d8fec4bd4b022cd047100000004a8000000000000000ca4f3c0000000000000000014c0414000708444000000b109c92380014a8d24000000b2c00000032d2fc0000005740000000000012640000001892b40010f4b8c00094c3d40009689a4000000000000cdc000b6c000c78b0800000089054c000000000000000130488b9800056081c000d5cf800004c4e5c0009b000000017cd1951c0000008a46dc2fc000434318e700013b0001118000000e040007d416c00148c0015149240011240000013e07b06e8000000fac430000000000000ab8000000000000000504c7d134aa1458e391c838c530000c687ace243280001000000f08249a0be450d08893c5c00500002d00000000010744284108b04d85848fcec900076862836d260f7c00140c3b40000007d80893a8b4c7c4000000000918e84a68ba02ec8980000000000000000011c4c487340b53d8e0d34133841c000334000a251642510302ac498000000a200004fc694c84078000001504024000000684544ff45280002c4
  | 10 => 0xa8d0651f036000072d1ccb39110a4d358d309fc0e472081429c0009c000112864809cf846ed06802c49000008c000000458000000fa4000fcc80c91d19d280904f44000c20000da8e1000099c0000000000000000000000000000000000000000000000008ecbcd32c0012493f0988fb00012903a40000000014d876c0002b41c42cc3c4bd8f98c28ce400077d1500000008cd3fd0e1318000000000000000000000acc000000000d840008281e4000000878c88b402440000000000000000013c84d4618874000cf942478472927c9b4000000c64000000264000ef0000000000058000001130f286880010840e01b14dc000000000234000e407e54c800000042000054000117c000d3819c3a8000c1534c3dc00023000144c7c14080000000
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xf6490910026bc6490910015f67190910005f5719091015fb4419091000dfa7090910005f97090910004ff7650910004fe7650910004fd7650910004fc7650910005f77150910015f4715091000dfa705091000df4765451002ef4765451000cf47654510015f7755451001777755451000777655451002ef6655451002ef4655451003f746554510045f67454510045f4745451003f775454510007755454510215f77354510215f5735451003f77535451020f75535451020fb7435451020fb54354510005f77254510007f3705451000df6705451000df4705451011ff07054510016f76054510017f3605451003ff3505451011ff0505451011ff2405451011ff2305451020ff1305451011ff2205451000df476485100c6f4764851000cf47648510005f77548510005f57548510007b77448510045f67448510045f47448510007b47448510045b47448510205f77348510205f573485101f6f763485101f6f563485101f77753485101f77553485101f7b743485101f7b54348510015f77248510017e77248510007e7624851006ef6624851006ef46248510007e462485101ffe752485101ffe45248510007e64248510007e542485101f7e632485101f7e53248510007f3704851000df6704851000df470485100c7f07048510016f76048510017f360485101fff350485100c7f050485100c7f240485100c7f230485101f7f130485100c7e720485100c7f220485100c7e52048510015f87650110026f87650110014f8765011003dfa755011003df8755011000dfb745011000fbb7450110007bb6450110026fa6450110026f86450110047b86450110047ba5450110007b954501101edfb73501101edf973501101e77b53501101e7795350110047bb43501101e7b94350110005fb7250110007f37150110015fa7150110015f87150110097f0715011000efb615011000ff36150110097f25150110007f15150110047f34150110097f04150110097f231501101e7f13150110097f22150110007f12150110015f87648110056f87648110014f876481100077b754811003dfa754811003df8754811000778754811003d787548110005fb7448110005f974481101ddfb73481101ddf973481101cefb63481101cef963481101cf7b53481101cf7953481101cfbb43481101cfb9434811000dfb724811000feb7248110007eb624811006efa624811006ef86248110007e86248110007ea5248110007e952481101d7eb42481101d7e842481101cfea32481101cfe93248110007f37148110015fa7148110015f87148110057f0714811000efb614811000ff36148110057f25148110007f151481101d7f34148110057f04148110057f231481101cff13148110057eb2148110057f22148110057e92148110007f12148110007e12148110
  | 1 => 0x9110004ff725911006cfc725911023cff7159110006f77159110046f74159110096f44159110104ff7059110006fb7059110004ff7655110004fe7655110004fd7655110004fc7655110005f77155110015f47155110005fb705511000df8705511002cfe75d8910004fd75d891002cfc75d8910024fe74d8910004fd74d8910024fc74d8910004ff73d891001cfe73d8910004fd73d891001cfc73d89100067f53d89100067d53d8910006bf43d8910006bd43d891000cff71d891000cfd71d8910236f631d8910006f531d8910236ef21d8910236ed21d8910014ff70d8910014fd70d891022efa30d8910006f930d891022eef20d891022eed20d89100c4fd7698910006ef62989100c5f57198910055f9709891002cfe7598910004fd759891006cfc7598910024fe7498910004fd749891006cfc749891006cff739891001cfe7398910004fd739891006cfc73989100067f53989100067d5398910006bf4398910006bd439891006cfe729891006eee3298910006ed32989100c4fd719891006ef5719891006ef621989100e4fd709891006ef9709891006efa20989100057f755891003d7c7558910005bf7458910045bc7458910005df7358910035dc73589100e5f77158910075fb7058910004ff75589100067f75589100047f755891002cfe755891002cfc75589100067c755891002c7c7558910004ff7458910006bf7458910004bf7458910024fe7458910024fc7458910006bc7458910024bc7458910004ff7358910006df7358910004df735891001cfe7358910004fd735891001cfc7358910006dc735891001cdc73589100067f53589100067d5358910006bf4358910006bd4358910006ef7258910006ee3258910006ed32589100e4ff7158910006f77158910056f63158910006f531589100c4ff7058910006fb70589100c6fa3058910006f9305891022cfe7618910006ed621891002cfe7518910004fd751891006cfc7518910024fe7418910004fd741891006cfc741891006cff731891001cfe7318910004fd731891006cfc73189100067f53189100067d5318910006bf4318910006bd431891006cfe721891006eee721891000cff7118910014fe711891000cfd711891006ef57118910014fc711891006eef211891006ef62118910226ed2118910014ff701891000cfe7018910014fd701891006ef9701891000cfc701891006eef201891006efa201891021eed201891006cff7694910004fe7694910004fd769491006cfc76949100067f659491002e7c6594910015f67194910005f5719491000dfa7094910005f97094910197785094910004ff7654910004fe7654910004fd7654910004fc7654910015f67154910005fb705491000df8705491006cff7690910004fe7690910004fd769091006cfc7690910006b
  | 2 => 0xe5ef7148520007e77148520007e76148520016ee6148520016ec6148520057e46148520057e63148520297e53148520007eb704852000dee704852000dec70485200c7e870485200c6ef60485200c7ea3048520297e930485200c7e710485200c7ea104852000dfa76c812000efa76c812000cfa76c81200077b65c81200077865c812006dfb73c812028df973c812027f7b53c812027f7953c812027fbb43c812027fb943c812000dfa72c812000fea72c812000efb62c812000feb62c812006fea52c8120007e952c8120287eb42c812006fe842c812006fea32c812027fe932c8120005f971c812006feb21c8120007e921c812002cfe76d951003e7e65d951000dfa70d9510015f970d951003f7b50d951011cfd75d9510024fe74d9510004fd74d9510024fc74d95100067e54d951003e7c54d9510004ff73d951001cfe73d9510004fd73d951001cfc73d951003e7f53d95100067d53d9510006bf43d9510006bd43d951006cfe72d9510004fd72d951003e7c52d951000cff71d9510014fe71d951000cfd71d9510014fc71d95102767f51d95102767d51d9510014ff70d951000cfe70d9510014fd70d9510276f970d9510014f970d951000cfc70d95102667f50d951003efb50d95102667d50d9510266f850d951002cff765951003e7c6559510005bf7459510045bc745951025df7715951026dfb7059510264ff75595100067f7559510004ff7459510006bf7459510004bf7459510024fe7459510024fc7459510006bc7459510024bc7459510004ff735951001cfe7359510004fd735951001cfc735951003e7f53595100067d5359510006bf4359510006bd4359510004ff725951006cfc725951025cff7159510006f7715951011cff7059510006fb705951003efb505951011ef85059510024fe76d9110046be64d9110015f671d911000df571d9110047b741d911002cfe75d9110004fd75d911002cfc75d9110104fd74d9110006bf54d9110046bc54d9110004ff73d911001cfe73d9110004fd73d911001cfc73d91100067f53d91100067d53d9110046bf43d9110006bd43d911006cfe72d9110004fd72d9110046bc42d911000cff71d9110014fe71d911000cfd71d9110246f571d911000cf571d9110014fc71d9110256bf41d9110046f741d9110256bd41d9110256f441d9110014ff70d911000cfe70d9110014fd70d911000cfc70d9110246bf40d9110246bd40d9110024ff76591100057f755911003d7c7559110046bc645911023df7715911024dfb7059110004ff75591100067f75591100047f755911002cfe755911002cfc75591100067c755911002c7c7559110244ff7459110006bf7459110004ff735911001cfe7359110004fd735911001cfc73591100067f53591100067d5359110046bf4359110006bd435
  | 3 => 0xc76549200067f655492002e7c6554920005fb705492000df8705492000dec765492002eec765492000cec7654920195ef75549200076f75549200076f655492002eee655492002eec65549200676c655492005dee745492005dec74549202cdef73549202cded73549200676f53549202c76d53549202c7af43549202c7ad4354920005ef7154920007eb705492000dee705492000dec7054920177e8705492000de87054920176ef6054920177ea30549202c7e93054920177ea10549202bcfe76909200067f659092016e7c65909202bdee729092006fe82090920024ff765092000cfe7650920134fd765092000cfc76509200067f655092014e7c6550920006bf6450920026bc64509202b5ef7250920005fb705092000df87050920137e82050920014fe76d85200067f65d85200067c65d8520056f661d852002cfe75d8520004fd75d852002cfc75d8520024fe74d8520004fd74d8520024fc74d8520004ff73d852001cfe73d8520004fd73d852001cfc73d85200067f53d85200067d53d8520006bf43d8520006bd43d852000cfd72d8520014fc72d8520006ee32d8520006ed32d8520056f621d852000cfe70d852000cfc70d85200e6fa30d8520006f930d85200e6f710d85200057f75585200657c75585200067f65585200067c6558520005bf745852005dbc7458520005df735852004ddc7358520056f46158520004ff7654520004fe7654520004fc76545200067f655452002e7c6554520004ff7650520004fe7650520004fc76505200067f65505201167c6550520005ef7250520005ec725052021cfe76c85200067f65c85200fe7c65c852000df870c852006fe820c852021dee76c8520236ee76c8520005ef75c8520005ed75c85200076f65c85200feee65c85200feec65c85200076c65c85200fe6c65c852005dee74c852005dec74c8520006ef64c8520006ed64c85202adef73c85202aded73c85202a6ef63c85202a6ed63c85202a76f53c85202a76d53c85202a7af43c85202a7ad43c85200c5ed71c8520016ee61c8520016ec61c852006feb70c852000dee70c852000dec70c852006fe870c852006eef60c85200e7ea30c85202a7e930c85200e7ea10c852000cfc76485200067f65485200de7c6548520005bf744852005dbc7448520006f76148520016f46148520057e42148520005fb704852000df870485200c7e8204852000dec7648520016ec764852000cec7648520005ef7548520005ed75485200076f65485200deee65485200deec65485200076c65485200de6c6548520007af744852005dee744852005dec7448520007ac744852005dac7448520006ef6448520006ed644852029def734852029ded7348520296ef6348520296ed63485202976f53485202976d5348520297af4348520297ad4348520
  | 4 => 0x95201967f30d95201967e30d95201967d30d95201967c30d95201967f20d95201967e20d95201967c20d95201967f10d95201967e10d95201967d10d95201967c10d95200667c65595202f5ef7259520194ff75595200067f7559520004ff7459520024fe7459520024fc7459520004ff735952001cfe7359520004fd735952001cfc73595200667f53595200067d5359520006bf4359520006bd43595202f4ff7259520006ef7259520004ff7159520014fe7159520014fc7159520174ff7059520006fb70595201957e76195200667e76195201947e76195200067e64195200067c64195200657f73195200057d73195200067f63195200067e63195200067d63195200067c63195200073f43195200073d43195202ef6d72195202ee7f62195200076f42195200076c42195200076e32195200076d32195200067e61195200067c61195202ee7f60195202ef7a30195200077930195202ef6e20195202ef6c20195202ef7820195202ef7a1019520024fe76d91200067f65d91200067c65d912005ebe64d912000ded72d912005faf42d912002cfe75d9120004fd75d912002cfc75d9120004ff73d912001cfe73d9120004fd73d912001cfc73d91200067f53d91200067d53d912005ebf43d9120006bd43d912006cfe72d912000cfd72d9120156ed72d912000ced72d912006cfc72d912005ebf42d912005eef42d912005eec42d9120014fe71d9120004fd71d9120014fc71d9120006be41d912005ebc41d912006cff70d9120154fd70d9120156bf40d9120156bd40d9120156fa10d91200057f75591200657c75591200067f65591200067c655912005ebc64591202b5ef7259120004ff75591200067f75591200047f755912002cfe755912002cfc75591200067c755912002c7c7559120154ff7459120006bf7459120004ff735912001cfe7359120004fd735912001cfc73591200067f53591200067d535912005ebf4359120006bd43591202b4ff7259120006ef725912005eef425912005eec4259120004ff7159120014fe7159120014fc7159120134ff7059120006fb7059120136fa1059120004ff7655120004fe7655120004fd7655120004fc76551200067f655512002e7c6555120005ef7255120005ec7255120005fb705512000df870551202ecfe76949201967f659492002e7c65949202edee76949202e6ee7694920175ed75949201976f659492002eee659492002eec65949200676c659492002e6c659492005dee749492005dec74949202ddef73949202dded73949200676f53949202d76d53949202d7af43949202d7ad4394920005ed719492000dee709492000dec709492006eef60949201976e50949201976c5094920197ea30949202d7e93094920197ea109492002cff765492000cfe7654920174fd765492000cf
  | 5 => 0x4fd765072006cfc7650720005ef725072006dec725072000ded76c8720016ed76c872000ced76c872006def75c8720005ed75c87200feee65c872006eec65c8720085ee74c872006dec74c872006eef64c8720006ed64c872006def73c8720315ed73c872006eef63c872030eed63c872030f6f53c872030f6d53c872030faf43c872030fad43c8720016ee61c872006fe661c872006fe561c8720016ec61c872000dee70c872006fea70c872006fe970c872000dec70c872022cff7648720005bf7448720085bc7448720016f4614872006fe421487200c7ea204872022def7648720226ef7648720005ef7548720005ed75487200deee65487200deec6548720007af7448720085ee7448720085ec7448720007ac7448720085ac7448720006ef6448720006ed6448720305ef7348720305ed73487202feef63487202feed63487202ff6f53487202ff6d53487202ffaf43487202ffad434872006fe7714872006fe76148720016ee6148720016ec614872006fe46148720077e631487202ffe5314872000dee704872000dec70487200c7e7104872002cfe76d95200667e65d9520024fe74d9520004fd74d9520024fc74d95200667f54d95200067e54d95200667c54d9520004ff73d952001cfe73d9520004fd73d952001cfc73d95200667f53d95200067e53d95200067d53d95200667c53d9520006bf43d9520006bd43d952006cfe72d952000cfd72d952006cfc72d95200667f52d9520014fe71d9520004fd71d9520014fc71d95200667f51d95200067e51d95200667c51d952006cff70d9520194fd70d95201967f50d95201967d50d95202ed7e76d952002c7e76d95200067e64d95200067c64d95200057f73d95200057d73d95200067f63d95200067e63d95200067d63d95200067c63d95200073f43d95200073d43d95201976f72d95200076f42d95200076c42d95200076e32d95200076d32d95200067e61d95200067c61d95201977a30d95200077930d95201976e20d95201976c20d95201977820d95201977a10d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200047f73d95200067e73d95200067d73d95200047d73d95200067c73d95200067f43d95200063f43d95200067e43d95200067d43d95200063d43d95200067c43d95201967f72d95200667e72d95201967d72d95200067f42d95200067c42d95200067f32d95200067e32d95200067d32d95200067c32d95200067f71d95200067e71d95200067d71d95200067c71d95200067f41d95200067e41d95200067c41d95200067f31d95200067e31d95200067d31d95200067c31d95200067e21d95200067c21d95201967f70d95201967e70d95201967d70d95201967c70d95201967f40d95201967e40d95201967d40d95201967c40d
  | 6 => 0xd74d972006cfc74d972006cff73d972001cfe73d9720004fd73d972006cfc73d972008e7f53d97200067d53d9720006bf43d9720006bd43d972006cfe72d972006eee72d9720014fe71d9720004fd71d9720014fc71d972006ef970d97201967e50d97201967c50d972002cff765972006e7c655972006e7f7559720004ff7459720024fe7459720024fc7459720004ff735972001cfe7359720004fd735972001cfc735972008e7f53597200067d5359720006bf4359720006bd435972002cff725972000cfe725972002cfd725972000cfc725972006e7e525972006e7c5259720004ff7159720014fe7159720014fc71597201767f50597201767d505972002cfe75d9320004fd75d932006cfc75d9320134fd74d932006cff73d932001cfe73d9320004fd73d932006cfc73d93200067f53d93200067d53d9320086bf43d9320006bd43d932006cfe72d932006eee72d9320086ef42d932006eec42d9320014fe71d9320004fd71d9320014fc71d932006ef970d9320024ff765932006ebc645932000dec725932006fac4259320004ff755932002cfe755932002cfc755932006ebf7459320004ff735932001cfe7359320004fd735932001cfc73593200067f53593200067d5359320086bf4359320006bd4359320024ff725932000cfe7259320024fd725932000cfc7259320136ec725932000cec7259320086ef425932006ebe425932006ebc4259320086ec4259320004ff7159320014fe7159320014fc7159320136bf4059320136bd4059320004ff765532006cfe7655320004fd765532006cfc7655320005ef725532006dec725532000ded7694b2006eed7694b2000ced7694b2002eee6594b2006f6e6594b2006f6d6594b2006eec6594b20085ee7494b2006dec7494b2006def7394b2033ded7394b2008f6f5394b203376d5394b20337af4394b20337ad4394b20005ed7194b2000dee7094b2006fea7094b2006fe97094b2000dec7094b201976e5094b201976c5094b202f4ff7654b202f5ef7654b2032eef7654b2006f6f7554b2002eee6554b2002eec6554b20085ee7454b20085ec7454b20325ef7354b20325ed7354b2008f6f5354b2031f6d5354b2031faf4354b2031fad4354b20005ef7154b2000dee7054b2000dec7054b202b4ff7650b202b5ef7250b20014ff765872006ef46158720004ff755872002cfe755872002cfc7558720004ff7458720024fe7458720024fc7458720004ff735872001cfe7358720004fd735872001cfc73587200067f53587200067d5358720006bf4358720006bd4358720014fd725872000cfc7258720006ee3258720006ed3258720076f63158720006f5315872006ef7215872006ef421587200c6fa20587200c6f71058720004ff7654720004fd765472006cfc7654720004ff7650720
  | 7 => 0x8550006ec624855002cfe76d95400a67e65d95401b4fd75d954000cff74d9540024fe74d954000cfd74d9540024fc74d954038e7f54d954038e7d54d9540004ff73d954001cfe73d9540004fd73d954001cfc73d95400a67f53d95400067d53d954038ebf43d9540006bd43d954006cfe72d9540004fd72d95400a67c52d9540014fe71d9540004fd71d9540014fc71d95400067e51d95400a67c51d9540024ff70d9540024fd70d954037e7f50d954037e7d50d954002cff76595400a67c6559540375bf7459540385fb705954037cff75595400067f7559540374ff7459540006bf7459540004ff735954001cfe7359540004fd735954001cfc73595400a67f53595400067d53595400bebf4359540006bd4359540004ff725954006cfc7259540004ff7159540014fe7159540014fc71595401b4ff7059540006fb705954000dbc765514002ebc765514000cbc7655140025bf75551400273f75551400073f655514002ebe655514002ebc65551400a73c655514036dbf735514036dbd7355140366bf6355140366bd63551400a73f53551403673d53551400a73f5155140007bb705514000dbe705514000dbc70551401b7b87055140026bf6055140027bb60551401b7ba105514002cfe75d8940004fd75d894002cfc75d894000cfd74d8940004ff73d894001cfe73d8940004fd73d894001cfc73d89400067f53d89400067d53d894035ebf43d8940006bd43d894035eee42d894035eed42d8940014fe71d8940004fd71d8940014fc71d8940024fd70d89402b6ef20d89402b6fa10d8940006ef629894005df970989400057f75589400a57c7558940085fb7058940006ed621894002cfe7518940004fd751894006cfc751894000cfd741894006cff731894001cfe7318940004fd731894006cfc73189400067f53189400067d5318940356bf4318940006bd431894006eee4218940356ed4218940014fe7118940004fd7118940014fc711894006cff7018940024fd701894006eef20189402beed2018940004fe7694940004fd769494006cfc76949400067f659494002e7c6594940004ff7654940004fe7654940004fc7654940014fe76d8540096f661d854002cfe75d8540004fd75d854002cfc75d854000cfd74d8540014fc74d8540004ff73d854001cfe73d8540004fd73d854001cfc73d85400067f53d85400067d53d854034ebf43d8540006bd43d854006cfe72d8540004fd72d8540096f641d854034ef541d8540024fd70d854023ef710d85400057f75585400a57c7558540096f46158540345fb7058540004ff7654540004fe7654540004fc76545400073d5454540004fe76c8540004fd76c854006cfc76c8540004ff7648540004fe7648540004fc7648540005bf7448540025bc7448540174fd75d9720024fe74d9720004f
  | 8 => 0x3b77553c85213b7b743c85213b7b543c8521015f672c8521017e672c8521016f762c8521017e762c85213bfe752c852106fe452c852106fe642c8521007e542c852106fe632c85213b7e532c8521005f570c852100cfe76d8121006bf64d8121006bc64d81210c6fa60d812102cfe75d8121004fd75d812102cfc75d8121024fe74d8121004fd74d8121024fc74d8121004ff73d812101cfe73d8121004fd73d812101cfc73d81210067f53d81210067d53d8121006bf43d8121006bd43d8121014fd72d8121006ee32d8121006ed32d812100cfc71d8121076f631d8121006f531d81210c6fa20d81210c6fa10d81210057f75581210dd7c7558121005bf74581210d5bc7458121006bf6458121006bc6458121005df73581210cddc73581210c6f86058121024fe76d91500bebe64d915000cfd75d9150024fc75d91500bebe54d91503aebd54d9150004ff73d915001cfe73d9150004fd73d915001cfc73d91503ae7f53d91500067d53d91500bebf43d9150006bd43d915006cfe72d9150004fd72d9150014fe71d9150004fd71d9150014fc71d9150006be41d91500bebc41d915002cfd70d9150376bf40d91500bebc64591503a5fb705915000cfd75d8950024fe74d8950004fd74d8950024fc74d8950004ff73d895001cfe73d8950004fd73d895001cfc73d89502e67f53d89500067d53d8950006bf43d8950006bd43d89502e6ee52d89502e6ed52d8950006ef32d8950006ec32d8950014fe71d8950004fd71d8950014fc71d895002cfd70d89502f6ef20d8950006ef6298950065f9709895008dfb7058950006ed621895000cfd7518950024fe7418950004fd741895006cfc741895006cff731895001cfe7318950004fd731895006cfc731895032e7f53189500067d5318950006bf4318950006bd431895006eee521895032eed5218950006ef321895006eec3218950014fe7118950004fd7118950014fc711895006cff701895002cfd70189502ee7e50189502ee7c501895006eef20189502eeed2018950004fe7690950004fd769095006cfc7690950004ff7650950004fe7650950004fc7650950014fe76d85500aef661d855000cfd75d8550014fc75d8550024fe74d8550004fd74d8550024fc74d8550004ff73d855001cfe73d8550004fd73d855001cfc73d855039e7f53d85500067d53d8550006bf43d8550006bd43d855006cfe72d8550004fd72d85500aef651d855039ef551d855002cfd70d855039efb50d855025ef850d855025ef710d8550005bf74585500bdbc74585500aef46158550395fb7058550004ff7650550004fe7650550004fc7650550004fe76c8550004fd76c855006cfc76c8550006ef62c855006eec62c8550004ff7648550004fe7648550004fc7648550005bf74485500bdbc7448550006ef624
  | 9 => 0xf31d912115ebe31d912115ebd31d912115ebc31d912115ebf21d912115ebe21d912115ebc21d9121006bf70d9121006be70d9121006bd70d9121006bc70d9121006bf50d9121006be50d9121006bc50d9121006bf30d9121006be30d9121006bd30d9121006bc30d9121006be20d9121006bc20d912115ebf10d912115ebe10d912115ebd10d912115ebc10d91210d6bc645912140def7259121004ff755912102cfe755912102cfc755912115cff7459121006bf7459121004ff735912101cfe7359121004fd735912101cfc73591210067f53591210067d53591210d6bf4359121006bd435912140cff7259121006ef725912113cff7159121006f77159121004ff705912100cfe705912100cfc705912115dbe76191210d6be761912115cbe7619121006bf6519121006be6519121006bd6519121006bc65191210d5bf7319121005bd7319121006bf6319121006be6319121006bd6319121006bc63191210073f53191210073d53191213f7ad72191213f6bf6219121007af5219121007ac5219121007ae3219121007ad32191213f6bf61191213f7b63119121007b531191213f7ae21191213f7ac21191213f7b42119121006be6019121006bc60191213f7b71019121004ff7655121004fe7655121004fd7655121004fc7655121006bf6455121026bc6455121005ef7255121005ec7255121005f77155121015f47155121404fe7694921006bf64949211aebc6494921405ee729492106fe4219492102cff7654921014fe765492117cfd7654921014fc76549210067f655492102e7c6554921006bf645492118ebc64549213fdef7254921005f77154921015f4715492117fe421549213f4fe769092115ebf6490921026bc64909213f5ee76909213eeee76909210ddee75909210ddec759092113ded749092115faf6490921026ee6490921026ec64909210d7ac6490921026ac64909213e5ef73909213e5ed73909213df6f53909213df6d53909210d7af43909213dfad4390921015ee7190921015ec719092106eef619092115fae419092115fac419092115fe631909213dfe53190921005ed709092115fe71090921024ff7650921014fe765092113cfd7650921014fc7650921006bf6450921026bc6450921005f77150921015f47150921015ec7650921026ec7650921014ec76509210ddee75509210ddec755092115def7450921007af7450921007af6450921026ee6450921026ec64509210d7ac64509213d5ef73509213d5ed73509213cf6f53509213cf6d53509210d7af43509213cfad4350921007e77150921015ee7150921015ec715092113fe47150921015e4715092113eef615092113fe631509213cfe53150921005ef705092113fe71050921007b764c8521007b464c852106df773c85213c5f573c85213b77753c8521
  | 10 => 0x8321024fc7458321004ff735832101cfe7358321004fd735832101cfc73583210067f53583210067d5358321006bf4358321006bd4358321014fc7258321006ee3258321006ed3258321056f621583210e6fa3058321006f9305832106efb205832106ef820583210e6fa105832102cfe76d95210de7e65d9521015ed72d95210df6f52d9521024fe74d9521004fd74d9521024fc74d9521004ff73d952101cfe73d9521004fd73d952101cfc73d95210de7f53d95210067d53d9521006bf43d9521006bd43d9521014fd72d952119eed72d9521014ed72d95210de7f52d95210deef52d95210deec52d952106cff71d952119cfd71d952119e7f51d952119e7d51d952100cfe70d9521004fd70d952100cfc70d95210067e50d95210de7c50d952119ef710d95210de7c6559521005bf74595210d5bc74595213fdef725952119cff75595210067f7559521004ff7459521006bf7459521004bf7459521024fe7459521024fc7459521006bc7459521024bc7459521004ff735952101cfe7359521004fd735952101cfc73595210de7f53595210067d5359521006bf4359521006bd43595213fcff7259521006ef72595210deef52595210deec525952117cff7159521006f77159521004ff705952100cfe705952100cfc705952117ef71059521024fe76d91210d6be64d912102cfe75d9121004fd75d912102cfc75d9121006bf54d91210d6be54d91210d6bc54d9121004ff73d912101cfe73d9121004fd73d912101cfc73d91210067f53d91210067d53d91210d6bf43d9121006be43d9121006bd43d91210d6bc43d9121014fd72d91210d6bf42d912106cff71d912115cfd71d912115ebf41d912115ebd41d912100cfe70d9121004fd70d912100cfc70d91210d6bf40d9121006be40d91210d6bc40d91213f5be76d9121024be76d9121006bf65d9121006be65d9121006bd65d9121006bc65d9121005bf73d9121005bd73d9121006bf63d9121006be63d9121006bd63d9121006bc63d91210073f53d91210073d53d912115faf72d9121007af52d9121007ac52d9121007ae32d9121007ad32d912115fb631d9121007b531d912115fae21d912115fac21d912115fb421d9121006be60d9121006bc60d912115fb710d9121006bf75d9121006be75d9121006bd75d9121006bc75d9121006bf73d9121004bf73d9121006be73d9121006bd73d9121004bd73d9121006bc73d9121006bf53d91210063f53d9121006be53d9121006bd53d91210063d53d9121006bc53d912115ebf72d91210d6be72d912115ebd72d9121006bf52d9121006bc52d9121006bf32d9121006be32d9121006bd32d9121006bc32d912115ebf71d912115ebe71d912115ebd71d912115ebc71d912115ebf51d912115ebe51d912115ebd51d912115ebc51d912115eb
  | 11 => 0xcfe76d8141106fa60d814102cfe75d8141004fd75d814102cfc75d8141014fd74d814100cfc74d8141004ff73d814101cfe73d8141004fd73d814101cfc73d81410067f53d81410067d53d8141346bf43d8141006bd43d814106cfe72d8141004fd72d8141024fd71d8141346f741d814124ef441d8141106fa40d8141106fa10d81410057f75581411157c7558141106f8605814117cfd75d9721024fe74d9721004fd74d972106cfc74d972106cff73d972101cfe73d9721004fd73d972106cfc73d97210fe7f53d97210067d53d9721006bf43d9721006bd43d972106cfe72d972106eee72d97210feef52d972106eec52d972106ef571d972100cfe70d9721004fd70d972100cfc70d972102cff765972106e7c6559721015ec725972106f6c525972106e7f7559721004ff7459721024fe7459721024fc7459721004ff735972101cfe7359721004fd735972101cfc73597210fe7f53597210067d5359721006bf4359721006bd4359721014fe7259721014fc725972117eec7259721014ec72597210feef525972106e7e525972106e7c52597210feec525972117e7f515972117e7d5159721004ff705972100cfe705972100cfc705972102cfe75d9321004fd75d932106cfc75d932113cfd74d932106cff73d932101cfe73d9321004fd73d932106cfc73d93210067f53d93210067d53d93210f6bf43d9321006bd43d932106cfe72d932106eee72d932106ef571d932115ebe41d932115ebc41d932100cfe70d9321004fd70d932100cfc70d9321024ff765932106ebc6459321004ff755932102cfe755932102cfc755932106ebf7459321004ff735932101cfe7359321004fd735932101cfc73593210067f53593210067d53593210f6bf4359321006bd4359321014fe7259321014fc725932106ebe425932106ebc425932113ebf415932113ebd4159321004ff705932100cfe705932100cfc7059321004ff765532106cfe7655321004fd765532106cfc7655321005ef725532106dec72553213fcff7654b213fdef7254b21015ed7690b2106eed7690b21014ed7690b210fdee7590b2106dec7590b21026ee6490b2106fae6490b2106fad6490b2106eec6490b2106def7390b21435ed7390b2142f6f5390b2142f6d5390b210f7af4390b2142fad4390b21015ee7190b2106fe67190b2106fe57190b21015ec7190b2115fae4190b2115fac4190b21005ed7090b2140cff7650b2140def7650b21426ef7650b210fdee7550b210fdec7550b2106faf7450b21026ee6450b21026ec6450b2141def7350b2141ded7350b214176f5350b214176d5350b210f7af4350b21417ad4350b21015ee7150b21015ec7150b21005ef7050b2100cff765832106ef86058321004ff755832102cfe755832102cfc7558321004ff7458321024fe745
  | 12 => 0xe52d8951466ed52d895102cfd71d89513feef21d895100cfe70d8951004fd70d895100cfc70d89513fef710d8951006ef62989510ddf57198951005bf745895112dbc74589510fdf77158951006ed6218951014fd7518951024fe7418951004fd741895106cfc741895106cff731895101cfe7318951004fd731895106cfc731895145e7f53189510067d5318951006bf4318951006bd431895106eee521895145eed521895106cff711895102cfd711895106eef2118951406ed211895100cfe7018951004fd701895100cfc7018951004fe7690951004fd769095106cfc7690951006bf6490951026bc6490951004ff7650951004fe7650951004fc765095100cfe76d815111efa60d8151014fd75d815100cfc75d8151024fe74d8151004fd74d8151024fc74d8151004ff73d815101cfe73d8151004fd73d815101cfc73d81513967f53d81510067d53d8151006bf43d8151006bd43d815106cfe72d8151004fd72d815102cfd71d815111efa50d815111efa10d8151005bf745815112dbc745815111ef8605815102cfe76d95411167e65d95411bcfd75d9541014ff74d9541014fd74d95414567f54d95414567d54d9541004ff73d954101cfe73d9541004fd73d954101cfc73d95411167f53d95410067d53d9541456bf43d9541006bd43d954106cfe72d9541004fd72d9541024ff71d9541024fd71d95414467f51d95414467d51d954100cfe70d9541004fd70d954100cfc70d95410067e50d95411167c50d954102cff76595411167c655954143dbf745954144df77159541444ff75595410067f755954143cff7459541006bf7459541004ff735954101cfe7359541004fd735954101cfc73595411167f53595410067d535954112ebf4359541006bd4359541004ff725954106cfc72595411bcff7159541006f77159541004ff705954100cfe705954100cfc705954102cfe75d8941004fd75d894102cfc75d8941014fd74d8941004ff73d894101cfe73d8941004fd73d894101cfc73d89410067f53d89410067d53d89413eebf43d8941006bd43d89413eeee42d89413eeed42d8941006ef32d8941006ec32d8941024fd71d894140eef21d894100cfe70d8941004fd70d894100cfc70d8941006ef62989410d5f571989410f5f77158941006ed621894102cfe7518941004fd751894106cfc7518941014fd741894106cff731894101cfe7318941004fd731894106cfc73189410067f53189410067d5318941426bf4318941006bd431894106eee4218941426ed4218941006ef321894106eec321894106cff7118941024fd71189413f6be41189413f6bc411894106eef21189413f6ed211894100cfe7018941004fd701894100cfc7018941004fe7694941004fd769494106cfc7694941004ff7654941004fe7654941004fc7654941
  | 13 => 0x954201cfe73d9542004fd73d954201cfc73d954214e7f53d95420067d53d95421aebf43d9542006bd43d9542024fd72d954214e7f52d9542014fe71d9542004fd71d9542014fc71d954200cfe70d9542004fd70d954200cfc70d95420067e50d954214e7c50d954214e7c65595424a5ef72595421acff75595420067f755954218cff7459542006bf7459542004ff735954201cfe7359542004fd735954201cfc735954214e7f53595420067d535954218ebf4359542006bd43595424a4ff7259542006ef7259542004ff7159542014fe7159542014fc7159542004ff705954200cfe705954200cfc705954249cfe769494214f6f529494206fac429494202cff7654942024fe765494218cfd7654942024fc76549420067f655494202e7c6554942005bf7454942025bc745494218fac425494206dbf7390942495bd739094248ebf639094248ebd639094248f3f539094248f3d539094206dbe729094206fae729094206ebf6290942027af629094215ebe619094215ebc6190942014fe76d854213ef661d854202cfe75d8542004fd75d854202cfc75d8542004ff73d854201cfe73d8542004fd73d854201cfc73d85420067f53d85420067d53d85420f6bf43d8542006bd43d8542024fd72d854213ef641d8542006f731d854213ef431d854213ef621d854200cfe70d8542004fd70d854200cfc70d854213ef710d854213ef4615854200cfe76d8142136fa60d814202cfe75d8142004fd75d814202cfc75d8142004ff73d814201cfe73d8142004fd73d814201cfc73d81420067f53d81420067d53d8142086bf43d8142006bd43d8142024fd72d8142086ef42d8142086ec42d8142014fe71d8142004fd71d8142014fc71d8142136fa40d8142136fa20d81420057f755814214d7c7558142136f86058142024fe76d915112ebe64d9151014fd75d915112ebe54d9151486bd54d9151004ff73d915101cfe73d9151004fd73d915101cfc73d91514867f53d91510067d53d915112ebf43d9151006bd43d915106cfe72d9151004fd72d915112ebc42d915102cfd71d915143ebf41d915100cfe70d9151004fd70d915100cfc70d9151006be40d915112ebc40d915112ebc645915147df771591510157c76551510267c76551510147c765515102d7f745515102f3f74551510073f64551510267e64551510267c645515112f3c64551514757f73551514757d735515146e7f635515146e7d635515112f3f435515146f3d43551510077771551510157e71551510157c71551511bf74715515102e7f615515102f77615515112f3f40551511bf771055151014fd75d8951024fe74d8951004fd74d8951024fc74d8951004ff73d895101cfe73d8951004fd73d895101cfc73d89514667f53d89510067d53d8951006bf43d8951006bd43d8951466e
  | 14 => 0x4ae7f63949524ae7d63949524af3f43949524af3d439495206d7e729495206f6e729495206e7f629495202f6f62949521967e60949521967c6094952014fe76d855217ef661d8552024fe74d8552004fd74d8552024fc74d8552004ff73d855201cfe73d8552004fd73d855201cfc73d85520fe7f53d85520067d53d8552006bf43d8552006bd43d855202cfd72d85520feef52d85520feec52d855217ef651d855217ef621d855200cfe70d8552004fd70d855200cfc70d8552005bf745855218dbc745855217ef4615855200cfe76d8152176fa60d8152024fe74d8152004fd74d8152024fc74d8152004ff73d815201cfe73d8152004fd73d815201cfc73d815208e7f53d81520067d53d8152006bf43d8152006bd43d815202cfd72d8152014fe71d8152004fd71d8152014fc71d8152176fa50d8152006fb30d8152176f830d8152176fa20d8152176fa10d8152176f8605815218cfd75d964206ebd74d964206cff73d964201cfe73d9642004fd73d964206cfc73d964216e7f53d96420067d53d96421aebf43d9642006bd43d964206cfe72d964206eee72d9642014fe71d964206ef671d9642014f671d9642004fd71d964206ef571d9642004f571d9642014fc71d964200cfe70d964206efa70d964200cfa70d9642004fd70d964206ef970d9642004f970d964200cfc70d964202cff765964206e7c655964206e7f755964218e7f545964218e7d5459642004ff735964201cfe7359642004fd735964201cfc735964216e7f53596420067d535964218ebf4359642006bd435964206cfe725964206cfc725964206e7e525964206e7c5259642004ff7159642014fe7159642014fc7159642004ff705964200cfe705964200cfc70596424a4ff7654a4218faf4254a42014ff7658642025bc745864206ef4615864215fb64158642004ff755864202cfe755864202cfc7558642004ff735864201cfe7358642004fd735864201cfc73586420067f53586420067d53586420d6bf4358642006bd435864206cfc7258642006f7515864215ef4515864215ebe415864215ef6415864215ebc415864215ef63158642006f5315864206ef7215864206ef42158642004ff705864200cfe705864200cfc705864215ef7105864200cff765824206ef86058242004ff755824202cfe755824202cfc7558242004ff735824201cfe7358242004fd735824201cfc73582420067f53582420067d535824205ebf4358242006bd435824206cfc725824205eef425824205eec4258242004ff7158242014fe7158242014fc7158242006fb5058242156f85058242156fa4058242156fa3058242006f9305824206efb205824206ef82058242156fa105824202cfe76d954214e7e65d954206cff74d95421acfd74d95421ae7f54d95421ae7d54d9542004ff73d
  | 15 => 0xe7318954004fd731895406cfc73189544c67f53189540067d531895449ebf4318954006bd431895406eee52189544c6ed521895406eee421895449eed4218954006ef321895406eec3218954014fe7118954004fd7118954014fc711895400cfe7018954004fd701895400cfc7018954014fe76d85541bef661d8554024fd75d855402cfd74d8554004ff73d855401cfe73d8554004fd73d855401cfc73d855447e7f53d85540067d53d855444ebf43d8554006bd43d855406cfe72d8554004fd72d85541bef651d85541bef641d8554006f731d85541bef431d85541bef621d855400cfe70d8554004fd70d855400cfc70d85541bef710d85541bef4615855400cfe76d81541b6fa60d8154024fd75d815402cfd74d8154004ff73d815401cfe73d8154004fd73d815401cfc73d81543a67f53d81540067d53d8154386bf43d8154006bd43d815406cfe72d8154004fd72d8154014fe71d8154004fd71d8154014fc71d81541b6fa50d81541b6fa40d8154006fb30d81541b6f830d81541b6fa20d81541b6fa10d81541b6f86058154024ff765925206ebc64592521aebe545925214ebd5459252004ff735925201cfe7359252004fd735925201cfc735925214e7f53592520067d53592521aebf4359252006bd435925206cfe725925206cfc725925206ebe425925206ebc4259252004ff7159252014fe7159252014fc7159252004ff705925200cfe705925200cfc7059252014ff765865206ef46158652004ff7458652024fe7458652024fc7458652004ff735865201cfe7358652004fd735865201cfc73586520de7f53586520067d5358652006bf4358652006bd435865206cfc72586520deef52586520deec525865219ef65158652006f7415865219ef4415865219ef63158652006f5315865206ef7215865206ef42158652004ff705865200cfe705865200cfc705865219ef7105865200cff765825202d7c755825206ef860582521977a5058252004ff7458252024fe7458252024fc7458252004ff735825201cfe7358252004fd735825201cfc73582520667f53582520067d5358252006bf4358252006bd435825206cfc7258252004ff7158252014fe7158252014fc71582521967e5058252196fa50582521967c5058252006fb4058252196f84058252196fa3058252006f9305825206efb205825206ef82058252196fa1058252024fe76d915218ebe64d915218ebe54d915216ebd54d9152004ff73d915201cfe73d9152004fd73d915201cfc73d915216e7f53d91520067d53d915218ebf43d9152006bd43d915202cfd72d915218ebf42d9152014fe71d9152004fd71d9152014fc71d9152006be41d915218ebc41d915200cfe70d9152004fd70d915200cfc70d915218ebc64591524bdef725915206d7f73949524b57d7394952
  | 16 => 0x600200200000300a00900f00300800e00500500800100000a00200200500602a00000101200000000700801202100000b00000300300100101901d00300300000200000100600400000100900100f00a00000900800001200f00000100000801400100300b00000000000400400c00002000c00300100000100400200200501200400200a01800000900000300100100100500000100600000601c00100600c00000200200200300000f01100100000300000a00a00800700000101700c00e00000000400000200200600100300700200000200000101700200100100100000000b00700301900b00000400400500400800000000a00200000800100400f00800600700000201000100401400200300300100700100001b00001202000502700000000600700d00000200c00700300701600601800400000b01200000b00e00000801900200000000200000700000f00400100200100700301a00000000000000000000000500900600000500100301a01500700000101d00100001400100c00102700001200001100700100400200100600000800100000103000600000d01e00000000000800800100700100200101000000000400d00f00500300000500100003005000000400101700900b00700500200400100000600000100800200000103700a00300300b00200c00200600000500000900701900801002100100000000100200800300600c01600300000c00800700200000901b00000100b00000200700500400200200000000300000000600700d00000200500100100100100400000000401e00100000000400000100100000100a00f02b00600000200100c00b00000200000b00600400000300000001c00000f00500501100400200000200900000001200401e00900700500000400000600000100000301500000100200000000200000d00200000700f00100000000300000b00900000700a00000400700601501500d00300300800800200001700200900400000500200000b00a00000200701700200200000700000400000001e00200e01000601600300000000200000000100000100900100900000001100d00000200400200a00000900000000300000800201200200000001300100800100800100000400000802400000001c000009000000017008001000000003000000024fd75d895402cfd74d8954004ff73d895401cfe73d8954004fd73d895401cfc73d89544be7f53d89540067d53d89544a6bf43d8954006bd43d89544beee52d89544a6ee42d8954006ef32d8954006ec32d8954014fe71d8954004fd71d8954014fc71d895400cfe70d8954004fd70d895400cfc70d8954006ef62989541bdf67198954005f571989541b5fa7098954005f97098954006ed6218954024fd751895402cfd741895406cff731895401cf
  | 17 => 0x43000102ca27000186c1181700000eb8908000293856133c00023b07b82486f70fc1f846aa988000028065600000000000003b01fe9f754980231bca2591925bb45c0b4c000000199800055a86450720c0ed200031c2274fa873b00028e800094e0df91f80008a15028ee8000154000085443206717f20f47403034810ec80146260000000b62aba24fa80810aa9d0e528f8f2c82052b0f383228902348df0ac200010481b505216f00005ccf6800000000000000003f292dca3033700017a94bc89a4e40000f842bf2aa14503d03bb32f027c7d24f83c91704e3600040405c417a000000268153c7b64ff2014d7257c2a89a3c66427b4730c84eaaa4e1c71a60a4827d48487002f6557202a234aca2eb27b0734000aa2189800064c45a4889d2cf4e00036ca288000000034085c00000049fa2505ca6643e3207c000952000000000093900012cc88664a1601574be408e498000097400000006ac0006e842e9abc00091600007705c00001ed9054000a75233a5049c608436629f05d44ed2ae00000f833f00005b00006f200000005b26420000ad043a0001140000946ab30c215d105a0c704f0000c7e5da1a413312dc0000000fbcd9e34f55400007387774890000a8a08a000000000000029800001460004e8800093200003520080003ee00000000009c60000340f7a00100500500900300000200500b01100100000102800400800100000100305801200100b00700101d00300200200e00200d00100000000000100300000c00000000000801700000001500200b01300100100a00301e00100700001600d00a00200002700201001e02000000500f00000a03500000000700000201100000102200200001100001d00500200000000200100200b00500200000000100100300300a00300100400000f00200100000b00000100300000100300000a00000700500100500000400001000400000000000a00300c00700300100500f00100300200a00201400900700000000300d00101d00a01b00800700200600100100700000700e01900200100900600c00500700100200000000500900400000100600e00f00600500100201500401c00000200000200200101500400900100000300101600000f02800300000000000e01200900800000600000200f00000001200c00100000001604700600000000104201500000200f00100000100100100100600401b00300000000600900000300c01600400200000700000100000000b00400400001000401f00200d00500700e02802100000200e00000001900900000100200400400a00000000601800602500801002300c00100600100b01300100501400000200200000400800900002a00100000f00500000400801003400000200400200601700000101d00900a00001600100900000200300801
  | 18 => 0x54e4be0890018f6644e5051cb13ca05f445a1202e400917b8eac6da7de07e031110c56c54aa5a50a65ca19c93fcab68f33d8999886034e17c1a5912a79710b0a781940b70e700000006bd00021ac0000002c2000042040c0b1aa600007b94d488187ac0b441984d84f241e000000000000052d994800006e1b600009140005121a90712000000000000076600000b80007f342a000065aab005fa97cda82b820d000474cac502429c47b20000000001088000000000147800049a0000000000000000075272f10c1c24ba800001c00014a22ac2ee000013a3713c589389c01a51a699e075072e27a9ee0b2ca901b90000126a743d58000db42040a79ebc01681121987812d00001b8145800072b000000015c97029a03310582e30f51a28b420003b9000155c2d00000000c6c2a8051000000041d0000d74a787084600000e6aa880000b8400020c0001bf800009400000000000000000000fd46ed04880000000000000000a3e0000000000f5c59e2520b602403a330727250ec41253fa6bc0007871bd000125e5a755901f433ea572e8177c6cc6940a395180000000000c64e6093253c86b4000a5041119f4be69f54ca91a80cc14b09926115725b93c621b47663151cb215851833034902e157a46e0c91e38a7c6441918a346fc08049304aca2a7543a315351d277f349948488c0b63b2975c008ac155610dd2de51128ca6cc76a8e245393f52e4862016299545624c14312b8e460f5341a15d0a205250faad01ce174546845c00000c444800094c74730b88d037c93d1a28cf0d9095f2948d2cc160101c1980000061000000009d82fa26b082d2c000028eaa14cb84653f89124ffa000000243d54676c217a35c000a942d5a8400ac458236a474166000553a3284c402d00022140001830000ef8000000000000149e0000001f8c00034a000000000000006d1f000009501e1000000061d4d2000000000008d17b44c850918a0630aa658916e8dd02260002b02a5c00000033026893dc000000000000000022800000006304a200009502673160d595847002108000e945e94768300b8615033980001965bd3a9248006c75c29799e8522a430d115313848ce31c90288501bc20b1ec004e9173241cc4bac26b4cd800000000000000012160000000304000000054800000018214b0e4117a5804801ff07d61c500005380000005589a99484608273a52c9d09aa0a68294a026e70001064d7e48e0000000000000000064cd8600000000000008db208800000022000026680000003a6918d12e01b5231394000000000282000000000007b0ff40280000cc4b3e000441a5ac0002320ec8544d563c90001a24e9000038a8000ce200000017bc0008353eb021c0009d932b00003826bb0000000a04092000105065826600017a150e3e74e9875c2c22472
  | 19 => 0x50610e502e6c0280148000000002220041ca2b749706980765ac014aa040002d235e179107020800014b8ea05a24e196381f48c11c11f7c9680000000cbc0006053018050f6e480241112c27c4701af8000d045230f284fcb362a326a9d4cfe89dd36288ccf548e8252a76c000000000046cd2000000000004286590001890c8c50400001e48f400002384610f20904ba2660b6c812468000000080b27088d8ef2a6a16b17780009dc51100000001f90000f480000001a3a4f01068df2868960e688bf4bf9ac800000041189fc31a6d21ee80000921254988eb021c0f20e31ccc54a01c321a0d0b9c38b14b9e61232a340949fed4da6132bc15f4df610507494b48ba5b029fa7c093a7ef36380003e82bb1840b0854404b3799e8cdc86580001d3948e8bb00000005866a25569648e649fb4b303d025a17828e15a10960002f0a09c0009b746e04b829879c00000000008f03bd04b00b2771000000119a619000262c17c0000000000de089c10525b04ac0000e11ff909c14818d80000008280001340cae00000003fc000964268a65c4ba00000028dc4da000319000136a6f138f80fc5820610000b68c746fc54603d94380000588ced37c7601458f44000000289000156a0003111bb000081b1b98000c1e030249a348e4e000000000147692a000000000000000000000000004a00000d3c17538389bc0002940000f94acc00011502c0b540003a180006844c106d87dc00032a29511a00000000000000cfe0000000000000a1100000012b800030c286d3be0000000af08b61420000ee40002c60000464a960003b98344bb642b00000000246a33b70e049d210150a00005143051b79fac00095112d11f404400000000000000001d200008ae4c00001080c5e6694689fa48029f31b395b82709550da800058e0000001b8000083c07c19ad14c14000000006b27cd3ec830c00000015580c88488840b5107000064e31598f0b880350d4a43052a2fd4a98d183280000e2097120a4892d980011981b448d0000cd400000000000009a31efa2b017255e1e0800000056940480786744b11158abc3fa0000001d30000a4515925c4000a7d0001258000577000000048a8da00029d87d891f02e800033600300010200000000690ac0b8e5c50000000000650000198c3b096a0000000d5c0000001f3905c86f4a11fd8000a8317681bc05e6b600000000001f531b80000004e63b40000bea00034b80000000000be8261292ab7262009479400025e269d18412f1dfaa8113099d1c900000001ed50b8001368000093169000059c05d118040e03739300000000001a81fdd1ee7cf1621f4510429f2bd02b0d6a3d84ea04d035408d1501b3833094627c83748ee13029b0334350a9120989114d26771079ae01a897d070255c4703a237c1adcf8e3f11c51748
  | 20 => 0x1b200000000002763f0000063c0009ef3e58000d9a4350a199240000003df00008a869c24383911dc000484000045c3c002c038c0000003598c8842467e08e00009562131b0119843c00055c01c50546994491eed5566de2c1298916877c42296d084a7ba40ca5f8f0c1390911d8cd424a9266953d328989137006400060d15990f001a855027117060e04a0001ac4c5a0000000000ed47c44ec24dc7687280f4a01d3c601f2ab0c38f985f12391d2492459119722b459a8f9222a16c28a70b0001ce0bc046426e8d503fc2983371c311c03d0194071c4227670ce131c00095b2eaa28c954785285aa6c3d67ec3ba8c2d4948be36e273896a36a26500000c452b375a5b491053a3a7a2c0d108cb2f8237455264101f00684a00ec32f8d44598a4841f26f4f126be47d93ec28c4b80bd1314c6287a29d9ef000075f00021b800000000017ac2ca0001b19c4000000000021a503a00000024845e21d53310edc3c686834e90880000750000dfc61800024b8f90feaa8223e12f47082a10000a705ce0000001fc0178a7246c00000002420001468c765500730c5850e0b523faabc4d8285110a9508c4a6325005b43ba43d4528e347320ef40d19307f268e363144d1e80d543ea8c4486a994968564cf646f3ac94c49e41882998a6ccd824f2e88d0d03081e3b801a475a23a46205682204b00dd29e05aa98c00000000000000000ba49dc4a70001efc9de04c0dc888ca723fa339000000000000020dc00061a1ad8000c960003cc8ad40000004f02564c1204300007c484603d000244c26e00017302246221e14fc9a008aa2b94f3a2e43e40003830d0538a30040525d4b4c000472a38c0e87d02db8b393cc9cc0000ec4f926d118210c8e085370002924b5001d42621c802e4bf158a2ac66837b00027dc49230d2e41a815521ae00013dc2ccabc2b81bb80000003369eb12900002fb0668e748f8430263c79e0e80dc0b285d8282563183077a9ea461918466c8c604b26c42ce9ff0861cd818a000000105c0000002cea0352f200050229dc7da000000000053260a38c23fd3c84cb13a0ab8eb48b72619430b9e881301210079a89b3c7868c89880334fa0bd5421874d82314d0a8e14c88ce0e4a2cb4540a392ac000509a3901c472413ba000fda6ea4b08f886ca00047e800099c9e825c8bd047600051c0000472451171179c0004af000058000058700026b00000002b526e800010a2cb8d108f200033a000000000000022305261e20159c3821e6e6281a9a00007f801504782080d32b6a6e13501d1353883556c000220037812a00000023c90f81cc10097e40003cc2b58a3ccb60002878ea84803f636d876c4e639d2c29e98efa23c1ca800151ca60429000085c000227a278a8e000000000067a28000024ec0006762298548000000308800072846c
  | 21 => 0x1000101d43c76f2911bd43761a70001f0c0229b604ca974a6a621126a1cc000448000000126c6d60001f20a4c000493a41847a30f21318a50b43c533404e95147d50000000b105710002a4c32000001c89d402c49538184443f63273a8a92c4b29540000778040a9c4551850bb2abb02293f13d62fc4be09c0f406d0529a13545866f364911cc8e2714e5a3f939e4f045718f49e256744386840f080e44ca594ee86ad20127780002df0ce963c4a8a3d000000000000045a8bc0e8a2523288dd939a03a3d1179473407b06f9c3c89aa9f2d9000094468609e00005ec0000002784aa4ac44af272800084121690a8c4062700021b0000544360a608a1c0f73c4163498c7da4941f98be8a204bb00004be6e20001a689307012148918bf048339f9cf474a3c31c307e80b62604f103b8ab414a42506391e255846796e01c27444c806f4ba60f92b213d074239b0a200000000004928da0d363f400000000004030002afc4045f7000257528e2e85149b4c00077b12b80000000002df1ad00001c9114872d2940dc43aa9b87c017c03998b89b80b221b03589a65401128000e321f0113259cbfc8f500022e854c0001fd800087400000017b057c4ad3299564c9a3af2fd80000007d3000000003000000000000000004fc20c44ca21c000209154a00000006b04f80004218bcc1024311a9035d47e5414388ae87f839329e841d13e4da4591a450ce35309526990c275d4fd0ee03cc9f60f78c907cc91b0d780007001d215515bc3604b23d2141c0006e3000216000036b02f25e93329e91f900004b68c80a480000006e94fe902c000a2d4d280012e67ff09a80002f20001d385f823e000213a041246a33000289400068b3f380000002c80001eb468000000000009226ff134a0e400000000023e80ae00038990d02ee00000000001509800001c848bc0a616e06007e66e549d20fc6121860ae89040003d50000c94e6e68400000000002632e00000c9e00026f000091878d38f0000000000050a81c0000002c98000bc400020780009a80000ad924032e09b38e2118b967f90ca8c480a059a3338054eb65081e9814439023045e0d6001e68c02022a43ac54e3ac16190a070a2c60f1c08c00006c08014aaa8000023587ee3b6000040c43e0002de271000049c0610a2063827e20005040005cd319849cf08a86459800009a8ea00028e400057f000121537e8143b0800000000018e800000000038b16e85ea0a446a0b2530c0c800000002ac00002e10e0d50a6f04108390cc85f2b119d4bb023739e003906c57523595ccc4aa8f00018a00008eb1ed00009e60004e0813c67c00015ea818c240000000f5d21a4094c981c8000000501a31c20078a457a648db011637e8790b520003a0800000000000016b400086500000006344e217d8b5d480000000000
  | 22 => 0x512281331c628c942c35e00029ac9be1c3000000039e00000029342b80003d915c800088e267a164d849ec4e38b786ee26a35480010380003e50c04df4847356136526686a002a124b5e945275860400073e00019140004a100026b544c4710432228a862c533294e052459820812341920ad00020944bca182fd1c0925861f4479f8871e4c84ac20195123e80d980011bc9830000c7865291e2e480000004180000000c0ca7e0b2185800029a0000e44d0e00000000007905a54b199e508479d118912804c19e37c8ef0e8067c2162b0d0ee10228502ed3e201314e80008085990000f854502511b08b90c8032032a9aa82100003c01440000000000000000099f34a80002d08152c1aaf8f3e87e28f094c506a302f30da43a00000ab90fcbfa40604e00009a44424eba8494cc0004c39b854a42033c100005202f2000000000000000000000006df0000e7c3a800700026c815600000006640000003020f7121c9240000d712864db53800000005282992a912ee40d21d80003b4000413023d1b24564838c7d0fe90111208882d6a2e48815280000000000000e3a000000158c6c40003f0000141e00000015d8c0224a0d90df43be92215201f8cb497b05501fd31474200009840007173e918543ce58b3b5a7f0a4a94f00000011ce58a0848e7800034c000000006821a1ad0b6c0000003952a4800061c000000148200049aaa1000075600000011de5ae45000000008b600000004d00000000fe153417f000074c00000028283180001281fa950872e0002e11f14d740004061fa112600000025300003104dc927934200049c122c00005400012040005dd48526f0b6a478207014c00000042e260400071a00005a40aa2cf532000000010d47b000000050600021c08be8d31f50f8cb208211ef0c285085a31778268000000482000045e722427800078c776261000100800030f123c0005942f180002469ab2d000f0abe79050027d10f0aaa49480009c893e000000014e9d60000000b7e83b0a9822000018a183025c000a58000204c00099c0000090e2255510d946c7a89781b726144960003ec15f82aa0ea12412ed3a4a7a31180012303fe00023b02bc59521f2700b02278020a8648ea00031a08d40007055068000f4276254b01801166cb12a9e4c63049a0781f5d16207025600007969da0001bd929a8a4004000022a6b00320000a900000000084000000000000000066151b00000000003c09f7000000025b0000216000000132427aa35000181c0001ff42f00000001f3031800036c549000000000000000002bc47c8fc22c88fc9d482b0c293605dc6d50000a04f36a1d3caa7c800070d03b235400063538a288c3f865d3d4145c0d852c4d71ea41da75e1cc1b5c0008322e300001fc0000c48000f823170af8000ddea011bc107c00089
  | 23 => 0x71200003ac1f647437a28542ec16e00011108a40fd34081690741b14ddaa2c6c8791018a2006ae2ff315275400022726b97314ce7295638000fb6794000000125600016a0c094127a5515258941698e1c405881e2000000062cef0ac014481090f6441098800070e22d2f729640007e413917f022847352d0b4501e7b5539800131a79e36e97fd4426a527f01ac00000000022209366700329fb832c00000003cd32c00000118f88363c40000000ca8000000240c0007573900dd420c0ce00024704f4a7b52e27b4d8827653095e4340aa63b6800000000000000000003354ad0be522a2b600000000ee000102a18d4d81b70001e0c0003ff0001fc8d1a12103d08b023a3491c28000000a1a23d9ce4efc1a43b21b2800000000028bcaf69d027d0000f3400006787d90e80000198000e5a00052212
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8bc845cd62440011bd0e39ac48800317dd473589100062e3a8e6b122000c9f741cd6244001938e839ac4880021fa1f535891002c3e43ea6b122000c3f74d4d624414f878e9a9ac48800317dcf535891001e2e39ea6b12200087e8754d62440010f90ea9ac4880030fdd153589105361e3a2a6b122000c5f7354d62440078b8e6a9ac4880022fa1f43589100245e43e86b122000c3f75d0d624414b878eba1ac48800327dcf435891001e4e39e86b1220008be8750d62440011790ea1ac4880030fdd543589105261e3aa86b122000c9f7350d6244007938e6a1ac4880038754d435891001e6639c64b1220038ec874c96244007998e6992c48800e3d21d31589100074aa1a62b1220018fa87dc162440071f10e982c4880039654d305891000477c3ac431220a3c7571d4c62441458f2e1a98c48800f179cd53189100062eb9aa631220a1c757154c62441418f2e0a98c48827f2d5c743189104f65cb86863122003c9e7350c624400193ae6a18c4880038754d43189104ee5ab8a86312209ccb97050c62440031e90cb8ca48800a3e21970949100043fc2aeca9220008bf845d9524400917908bb2a48800237e0d765491001c6e41aeca9220028fa86dc152440031e90cb8c848800a3e21970909100043fc2aeca12200587c855d9424400117f08bb2848800237e0d765091001c6e41aeca1220018f686dc542440052e90eaa2a28800a7960b754851000cf9406ea90a203fd7050dd521440031e90cbaa42880226d21175485103f4db43ee890a2000cb476dd12144001968ec3a24288023691d24248510005f0c048490a20029e48750921440015c90ca1242880036c1d3704851000cdc43aa8a0220009f0875454044001e62a8a8a8088022ec21121501102ecbd43eea9022000c7876dd520440018f0ec3aa40880067a60b7448110014f940ee8902203adb041dd120440051f10cba2408801e5e215744811003eb43aca49022000be18194920440033d10ea924088002ba2195248110006b83aee29022007d707554520440035e10c90a408800b3c1d921481101feb83aa42902203abb084485204401bdc0c490a4088006f821d2148110016f043a429022001be28648520440037c10c90a4088063b8219214811006f71bb2429022002de2764852044005bc0ec90a408802bb81d92148110005f1c2a429022000be1854852044001ec6ea90a40880ff789d521481101fef03aa429022000f6075485204407fac0ea90a4088003e8e1121481101d5f142242902203abe0844852044001f410890a40880eae82112148110006f1ba2429022000de17448520441377c70690a408826ef860d21481104d6f1b9a42902209ade1734852044133dc6c690a4088267b858d21481104cfb1a9a429022099f61534852044133f468690a4088267e850d2148110
  | 1 => 0x2a6986c2900021fa1f65585200061e3a6cab0a4000c5c73d9561480010fd0e32ac2900030f1d065585200062e398cab0a4000c3f65dd16148001878cbba2c29000317d9773585200062e32ee6b0a400287e87d95514800b0fd0bbb282900021f617765052000c77436e4a0a40019ea80dc9414803f8d8cbbae429007e3b21975c852000cf4402eb90a401fa6e86d9721480171db0fb26429007e9b21564c85200061e3a6ca90a4000e6421d95214800187ecbba242900030f1977448520006d4106e890a401bc6c65dd521480031d90cbaa429002e6b211754852000cf4402ea90a401ba6e86d9521480658d8edb2a42900034b1d365485200073230eca90a405dc6c761952148001a58e832a429002e6ba1f744852015e563b6e890a4000e2c65dd12148001b50e1ba242901fb2b1d8744852000716328e890a400bcac74d9121480051d90eb22429006e9b21564485200157240ac890a4077e6465dc52148001cc8cbb0a42900036a1d370485201963d3b6cb9024005c7a7619720480bd3d70ea96409003778c8571c8120285d4422439024000c3d7495365440014f3012a6ca8800a3e60373d951001c3fc3aa7b2a2000c5d7354f65441418f2e0a9eca8827b2e5c343d95100070ea9a87b2a209ccb97050f654400917d0fba2ca880022f60f74595100061fa9ee8b2a2000c3f751d165440070f90bb9aca880022fe1173595100245e422e6b2a20008ef825cd654401b1d904b9aca8800e1f21d53595100061fba2a6b2a20a6c3c7454d65440018bee6a9aca880022fa1f43595100245e43e86b2a20008be8750d65440011790ea1aca880038754d43595100061ebaea9b222000ab581d5364440031eb03b9ec88828f1d5c753d911050e3ab8aa7b2220038bf8750f644400193ae6a1ec8880038754d43d91104ee5ab8a87b22200587e87dd564440010fb07baac8880030fd0f75591100061e3aee8b2220038bc84dcd64440010ff0ab9ac8880161f215735911000477c12e6b22200d8ec825cd64440010fd0fa9ac8880161f21f53591100043f43aa6b22200087c8754d64440071790ea1ac8880030fdd543591105261e3aa86b222000c9f7350d6444001c3aa6a1ac8880363ba0a765511000476c14ecaa2200087f855d9544400117f08bb2a8880063da1b71551100147d436e0aa22000e1d5350f6244001d2a8698ec4880039654d30d89100070ea9a87312200587e87dd562440010fb07baac4880122fa1f74589100061fbaee8b122000c3c75dd1624400117b07ba2c4880030fdd474589100061e3a8e8b1220038de87dcd62440018beebb9ac488003171d773589100064fba6e6b122000c9c74dcd62440018bf0bb9ac4880031721773589100064fc26e6b122000c9c84dcd62440010ff0ab9ac4880161f21573589100045fc22e6b122004
  | 2 => 0xe43d95200062fb9c87b2a4000c5f7350f6548001c3f06a1eca900030fdcd43d95200070fb9a87b2a4000c1f7350f654800187ae6a1eca90003871cd43d95200043f43887b2a400087d8710f65480650fd0f996ca900021f61f32d95200051f42665b2a4000a3d84ccb65480010fd0e196ca900321f61c32d95200051f42065b2a4000a3d840cb65480014ed02196ca900029d60432d95201953d40065b2a4000a79800cb65480014dd0438eca900ca9b60871d95201953d400e3b2a4000a79801c765480010fd0e20eca900021f61c41d95200052f41883b2a4000a5d8310765480014dd0420eca900029b60841d95201953d40083b2a4000a798010765480010fd0f98eca900021f61f31d95200051f42663b2a4000a3d84cc76548001c3a8798eca900038750d31d95200043f43863b2a400087d870c7654800147d0818eca900028f61031d95200053741063b2a4000a6d820c765480654f50018eca900029e60031d95201953d40043b2a400087f855cd65480011df04b9aca900023ee01735952001c3e43aa6b2a4000c5f7354d654800193ee6a1aca9000f271cd43595200070ea9a86b2a4000a5e8399065480014bb07320ca900021fe1f63195200062eb9ec632a400087d8798c654800147d09318ca900028f61263195200043fc3ac632a40aca6f8258c65480014f700b18ca900161fa1c63195200043ec38c632a4000a3e8418c654800147b08318ca90003175cc63195200053b408c632a4000a758118c654815787ceda18ca902ab0f9d943195200068eb9a8632a4000e1f6350c6548001c38c6a18ca90176daa03421952054d374346432a4000d4d738c865480bb4d90c990ca902a29b60a61195200053cc04c232a4000a78864c06548001ab2e6980ca900cb1b5cb65d912000717a16cbb22405dc6d7219764480031db05b9ec89028f1b5cb53d912050e36b92a7b2240038bf8750f644800193ae6a1ec8900038754d43d91204ee56b9287b22400087e87d9564480010fd0e32ac8900161fa1f75591200043ec1eeab224000c3f43dd564480010ff0ab9ac8900161f21573591200047bc0ae6b2240028f4815cd64480010fd0fa9ac8900161f21f53591200043f43aa6b22400087c8754d64480071790ea1ac8900030fdd543591205261e3aa86b224000c9f7350d6448007938e6a1ac8900038754d43591200147b40cecaa240008f5819d954480010ff0abb2a8900121fa1f65551201963c386caaa240018ee86dc954480018deca392a8900363ea1b70551200de3632ae32924032c7870d95524800b8d8edbaaa4900cb5a1c37554920196363b6caa924032d6870d9552480033d101b8aa4900067aa1f70549202ee3c380cbb0a40028ec825d761480031f100baec29000327dcd43d852001e4e39a87b0a4000e1d5350f6148001cb
  | 3 => 0x5b12a0008ef87588625415d4df0ab10c4a80363b209731895001e4f39a86312a000c9d7350c6254001c3aa6a18c4a80029b61732189500045fc22e2312a0048bc845c46254001c3aa6a1ec2a800a3b20976c85500245f424ec90aa0008bd849d921540051dd0fb1242a800ab9a07624855001c3fc3aa7b2a8003c5e7354f65500018bae6a9ecaa000327dcd43d95400070ea9a87b2a8000a6e82947655015b87eebba2caa00023be09735954006c76412e6b2a80008f7815cd65500051e902b9acaa00023ee01735954001c3e43aa6b2a8000c5f7354d65500071790ea1acaa000327dcd43595400070ea9a86b2a8003c5e7354f62500018bae6a9ec4a00038754d43d894000477c3ac43128003c5e7354c62500018bae6a98c4a00038754d431894001e2f39aa7b0a8000c5d7354f615000193ee6a1ec2a00038754d43d85400061e3b2a8a8a80028ee829db2150009179083b242a00062fa1b744854001c3fc3aa7b2e4000c5d7354f65c8001c3aa6a1ecb900361f21d53597200062fb9aa6b2e4000e1d5350d65c800717f0ea1ec990003275cd43d93200070ea9a87b2640018ec825cd64c80011ef02b9ac99000a3d205735932051e36396a6b2640a1c6c7254d64c801b1790ea1ac99000327dcd43593200070ea9a86b26409dcac7250d64c80031d904bb2a99000a3b60b75587200062fb9aa6b0e4003c5c7354d61c8001c3aa6a1ac3900363d21d31587200074aa1a62b0e40018ee82dd951c80031d904bb2839006e3b61b75487200de3732eea90e40109ac845d521c802135d0fba243900432b1d364487200847643ac890e4002ae48159121c800187ae92a6ca900028fa1253d95200051ec24a7b2a4000c5d7394f65480014db0529eca900029e60253d952001c3fc3aa7b2a4000c5d7354f654800193ee6a1eca9000f271cd43d95200070f29a87b2a4000e1d5350f65480014bd07326ca900029760e64d95200062eb9ec7b2a4000a3e8498f654800147b0931eca900321f61c63d95200051f420c7b2a4000a3d8418f65480018bae631eca900029da0463d95200053ac08c7b2a40a5c3e76d0f654814987ceca1eca9000347dcd43d95200070fb1a87b2a4000e1c6350f65480656d501a16ca900ca9b21932d95200072631a65b2a4000d5b734c365480654db05ba6ca900029da0774d95200053ac0ee9b2a4000a7980dd365480014bd073a6ca900029760e74d95200061eba0e9b2a4000c5f30dcf65480018ba61b9eca900021f61e73d95200051f424e7b2a4000a3d849cf65480018bf06b9eca900028fa1073d95200051ec20e7b2a4000c5d731cf65480014dd0439eca900ca9b60873d95200053b408e7b2a4000a75811cf65480654f50039eca900029e60073d95200061fb9e87b2a4000c3d73d0f65480010fd0f21eca900021f61
  | 4 => 0x44840187ae7a9ec8908022fa1e53d91210045ec3ca7b224200c9f7394f6448401c3ea729ec89080327dcd53d91210070fc1aa7b224200c3f7354f6448401c3ee6a9ec89080307dcd53d91210061eb9aa7b224200e1c7354f644840117d0e29ec8908022f61c53d912115c5f43e65b2242008bd87ccb644840147d0b996c8908028f61732d91210045f43865b22421a8bd870cb644840147d0a196c8908028f61432d912115d5b40865b224200ab5810cb644840157500196c890802ae60032d912100557410e1b22422baad821c3644845756d02386c890802ad60470d91210045f438a1b2242008bd87143644840153d06286c890802a760c50d912100557410a1b224200aad82143644845756d02286c890802ad60450d91210045f43e61b2242008bd87cc3644840147d0b986c8908028f61730d91210070ea9e61b224200e1d534c3644840117d0e186c8908022f61c30d91210051f42861b224200a3d850c3644840155d04186c890802ab60830d912115d5b40861b224200ab5810c3644845756d02106c8908022fe11735912100477c12e6b2242008f7815cd64484018bee6a9ac89080f171cd535912101c5e43a86b224200c9f7350d6448401c3aa6a1ac8908022f61e65191210054f41cca3224200a9d83994644840117f0eb28c8908022fe1f63191210064eb9ec632242008bd8798c644840147d0b318c8908028f61663191210045fc3ac632242b3aaf8258c644840156f02b18c8908122fa1c63191210045ec38c63224200a3e8518c644840147b0a318c890803275cc63191210055d400c63224200ab98018c644856587ceda98c890ac70f9d953191210068eb9aa63224200e1f6354c6448401c38c6a98c8909faaba1b52191213f5d340ea432242b0aae868c86448401b1ae7190c8909faab21932191210055a432623224200d95734c4644855f55b05300c890802ad606601912100c7d404ecaa242008f9809d9544840117f08bb2a8908162fa1f645512115e5a38ec8aa242028ee86dc9544840195ec8392a8908363da1b715512105e56322e1212422bcb471d914248409958edba284908af691c7745092115e563b6c8a12422bda471d9142484053cd0fb8a849080a79207705092140cf3c3a8590a420dde3205c321484fd968e2326c0908063b20974d812100c7a40ae9b024200c5f7354f60484078b8e6a9ec0908038754d43d81210074aa1a63b02422b8bc86dd1604840117d0fb22c0908030fdd764581210061e3aec8b024200c9c73d91604840117d0e322c0908030fdd464581210061e3a8c8b024200c9c73191604840193ec9b9ac0908032719373581210062fb9aa7b22a0038bf8750f645400193ae6a1ec8a80038754d43d91500070ea9a87b12a000a6d85ccb62540014db0a196c4a8002b960432d895000574c006
  | 5 => 0x88023be1d621895101e4f39a86312a200c9d7350c6254401c3aa6a18c4a880317dcd53d815101e4f39a87b02a200c9d7350f6054401c3aa6a1ec0a880e1fe1d53d95410062eb9aa7b2a8200c9f7350f6550401c3aa6a1ecaa0ad70fdd7745954100477c12e6b2a820d8ec825cd65504011ef02b9acaa08023ee01735954100c7c402e6b2a820387c8754d65504018bee6a9acaa080e2f21d43595410064fb9a86b2a8200e1d5350d6550401c3aa6a1ec4a0802ab61032d894100572c0865b128200ae9800cb62504011df0eb10c4a0ad2abe11621894106c76412e63128203c5e7354c62504018bae6a98c4a08038754d431894100556c2664312820087f855c0625040b0f90ab80c4a08038754d43d814101c3fc3aa7b2e4200c5d7354f65c8401c3aa6a1ecb9080a3b20973597210047dc02e6b2e42018f8805cd65c841b0f90ea9acb9080317dcd535972150636392a6b2e429ecac72d0d65c8401c3aa6a1acb90a732b1c9435972101c5fc3a87b264200c9d7350f64c8401c3aa6a1ec9908362f21d43593210064fb9a86b264200e1d5350d64c84051d904bb2a9908063b60b74583210064fb9a86b064203c9c7350d60c8401c3aa6a1ac1908363e21d30583210072ca9a60b0642028ed82dcf65484070ff0ea9eca90803175cd53d952150636b92a7b2a429ecad72d0f6548401c3aa6a1eca90a732b5c943d95210245f43ee8b2a42008bd83dd1654840187ea7ba2ca908022fe1173595210245e422e6b2a42008fb805cd65484031f100b9aca9080e1f21d53595210061fba2a6b2a42a6c3c7454d65484018bee6a9aca9080f171cd53595210045f43e86b2a42048bc87d0d654840117d0ea1aca908022f21d43595210070ea9a86b2a4200c3d75d5364484018bee6a9ec89080f171cd53d91210051f42c87b224200a3d8590f6448401c3aa721ec89080e2fe1d43d91210064eb9a87b224200e1d5350f644840153d0732ec890802a760e65d91210064eb9ec7b224200a3e8598f644840147b0b31ec89086a2f61c63d91210051f428c7b224200a3d8518f644840193ae631ec890802aea0063d91210055cc00c7b2242a7c3e76d4f644854d87ceca9ec89080347dcd53d91210070fb1aa7b224200e1c6354f644845755d0da96c8908038bd9752d912115dd340ea5b22422baac864cb6448401d18c6996c89080365dcd31d912115d56c16ebb224200ab581dd7644840157501baec890802ae60375d91210054f41cebb224200a9d839d7644840187aea3aec89080327cc773d91210064e98ee7b2242008bd879cf644840147d0b39ec8908028f61673d91210064fc1ae7b224200a3e851cf644840147b0a39ec890802aba0873d912115d56c10e7b22422bab6811cf644840156b0239ec890802aea0073d91210055cc00e7b224200c3f73d4f6
  | 6 => 0x80100b0020000100b00c0000000500202002800006008000000000000200502a00c02801000074000180000080480000200000009002008020010000040000b0020000000400a00000003000078008000100300001a00600000804000030088000020500302c00c000060040400040900300000c0000301600c038000100380080a0460040000000000c000000000000080101e0000080003a00407013002044038070000000100000205000800008000010040020000181d0000040000500200c0000201000c0080102e0100180000001c0200100000e1d5350f62550014db0b996c4aa0029b61432d895400556c2065b12a800ae5810cb62550015d300196c4aa00339d89719895406e72312e3312a800ceb625c2625501b9d0c4b84c4aa0023be1d621895406c76412e6312a80dccc325cc6255001c3aa6a18c4aa0029b617321895400556c2664312a800c9f7350f6155001c3aa6a1ec2aa0029d61731d85540074aa1e63b0aa800c5f7354f6055001c3aa6a1ec0aa0029e61730d81540072ca9e61b02a800c5d7354d649481b1790ea1ac92900327dcd43592520070ea9a86b24a400e1d5350d619481b1e90e98ac329003a550d31586520147b40ee8b04a4008f581dd160948018bae6a9ac12900327dcd435825201e4e39a86b04a400e1d5350d60948014f30ba02c1290363e21d30582520072ca9a60b04a400c5f7354f645480717f0ea1ec8a9003275cd43d91520070ea9a87b22a400e1d5350f61548018bee6a9ec0a90038754d43d81520053cc2e61b02a400e5953cc360548070ff0ea9ecb21003175cd53d96425063b38aa7b2c84a1c7a7054f659080717f0ea1ecb21003275cd43d96420070ea9a87b2c849ccb67150f659093b974e0a1ecb210031dd4d71d96420063aa9ae3b2c8400cb7435c7659080196a86b8ecb210031ed4d70d96420063ca9ae1b2c8400cbb435c3659080197286b86cb210361f21d53596420062fb9aa6b2c8400c9d7350d6590801c3aa6a1acb210063ea0375586420047cc06eab0c8400c5f7354d61908078b8e6a9ac321003275cd43586420070ea9a86b0c8400ab584d45619081b1e90e98ac321003a550d31586420070ea9a86b04840d8f8874c16090801cb2a6982c12100e1fe1d53d95420062eb9aa7b2a8400c9f7350f6550801c3aa6a1ecaa10023be0973595420047bc0ae6b2a84028f4815cd65508011f700b9acaa10063e201735954201c3e43aa6b2a8400c5f7354d65508071790ea1acaa100327dcd43595420070ea9a86b2a8400c3f65dd1525080193ee6a1ec2a10038754d43d85420074aa1e63b0a8400e1d5350f60508018bee6a9ec8a880e2fe1d43d915101e4f39a87b22a200c9d7350f6454401c3aa6a1ec8a8802aba0a40d915101e4f39a87b12a200c9d7350f6254401c3aa6a1ec4a
  | 7 => 0xb92cb35ad045e8ba0da0013883845ac1c8c0bf56c6859b0000c0c0d499643f69440b9590000019636a244a40f80000ea26d92249442acd32aa80002280003f046bfc001995de34c039da7367c4000000004ec00206000e351d00000028cf19aa000001078006328dcd20004080005f000000170001564b80007508b000d2ca3a986ea81400000000b242207f0000000012e7388a9d110527c000000001f6000000005f6000051e40ec8441e91b000964c30005e8ae1408a1406805a215000000094af014e525270e2000b5c000000000000014a2fa834000003180000003a1f20011c000000000000006700018638a00c0f000000516534cb8001d0dac0030b1da2cc9086a2484ad3a0582dc464c428a08624c0021600000143b5c65c779c89d500077d4e0315d80002f8006aa000ca84847c4306e96563c69d76a522d26ecda99055ee613f0004b64400e2f25dc4bc5e2c1000295702f623e7ddd4bab21441912b423b200000000052c082b2df00000162350000a10cf0d174800000151000974a40a40040003a030000000000404569b0000006de0004b173000a54000006bc00000000000d9000137158000000004b013434aae620cf59294073e8d05904a06a0014100002699073a570c8d3d4c8006c0001c9a155f28317d2a500000030ade2e24c4db80063e000658193b6cc4001b0000bd4a2800000000378000f22040000058e000622f80ca001141a50e46b9002530004d1ce9bf0a03d19c916412214001a95220012d2a66f0b14003560560d8000684720000037d5d49c08ba3b58c15d581f54a80000000051c000003866e4d3000000000604002ce6423558ab7a6ae0017bb0d000e64e380000064cfe21d000d500027c000000ca07021c000003340001981f0000000bc0031a0000011e800000725998b010e00067099000a88d407e000000000000000000026a0000000000054262c000000c4d391e3830007115891c000d2079800000b30000000364f14a00015236000042000a2400395108000002552d640c000001380006519b000680000002aad699480016800103a43000badcb0881fee496c80062e000e90d453cc6d550004bc1f5c3a6e016000ba10b24600002b8f0120020580080100008c0080d00402c000170020200080700c0180380200600c0080101801001004000000098000000100700000400c0080c02a00c0101400200400006000008000140020001280000600c008000000000000000a0000d00000200c0000200a06c0100200000c0100d0100000000400000800801008000060000020080480d00000000800000000020000160100580300a00803805000000038020000080000400202402800000020028010080500580000400404807000000078000040000000100200001800000000158120000280080000002
  | 8 => 0x15d000000001e900000000000000000000a85e6a0c4f11d2f08b02e80000041c000006a4000000000008d4ae00e000d35138000000018c0670000003d88327e93d3d2c00000001388c0009cc00000000b997f2b2000a492318056e79400286000000001a60000019fb13000001bf800100a35440006d2cac0021950a000000ec0000010d20e3d48fd130004fe0d1210002a400110000000001301026b27e4299f828235ca71c0710e50550f112eca8bf2a7288668571856442bc002dd000000510006e2a6c000003a8320001c5590000d1800000000001ec0a42e4d98002b4151be158664dd83b8d249a00067b890000b4ce9cd162179bb9153de00086845000b284780055282da1a4c16eba16dadc25ad84ebba83acd610f16072ecbd18ba731a8ccb409871cad4abb6709ccec00000000e3174800000dd00019f06611d3b8004be00151b461a00000038b222af80000000000000000000054000d6000e10448002a8000c39b62fe6e000261000d7c0009d4f04e8e10002da000002a4122578002d3000000003280e2e00c7b2603000000039000e8134b6c3a64c8001dc2c4531d68fd0007287700153a119a015b1044f4bcad8096079b70140000014600061000092800000000000000008b95db3010c001b1a680000350a0c90541547931c444bf40000060a84d3d8db000000001122ce13000041000a3c000e5000911a50006022485d8160001e88405a000784002560420000000016a3e97e00000000035800254b08000003b098c72202034001a48000005d53e800000000820006d05b00030e4a0718000730005bcc1143000000d7800000000660ef0002356b0000003c08a2d10000004f9c3000af5cd0002e0380628001280011b0c024e4cc00230368738000000000018eb2d4e400000153120091239ee0000000019c0008c8000ab344c3d37900000914001770009e49c1ff5c8001259eb3e8000fd049438aac060c2182dccdd1f373c480d598a6cad1c1d94259ace8b324a3fca68131e06226f4808e35a8020002e52f6000f698e1ec000500954cc00000000000000000000000000000000000000000000ae8f101f52cb3cafae1612164001bc3cc001d19301b4dec003663649ac8f0e93a2c50279922582d80e8511be1f0e594b11c0481726d1c2b49bc8cd05870408963064001ad97c226645208c7430eb8003373987f4d8b0466a87c6f0d95b4e85c82f1000000e837e64e18d3b1896785e94f9ac000b8c003201f8db4df1762c2ad00027524c8bc9b1393d00a0003624481b02db5d1cce0911a295ce84183000012088078005580015f8ad020a810d89a1f000000316490d14fb00074c659a994f06e0015e0fe3ba001919833ce000002c374a43c5c020758b40c230a48085d890032120114ba1239ed456a9f218c00000370000cf8
  | 9 => 0x267186ae5710a6702828cc0eb0009880011a04a8200000070a1e0000001eeea8001281b8ab40016a0006e5401353901b8000f528cc
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x390029002202150c000000002a05030b0000002614081d310f2404181b003c2f2e0007401e13013a3041343d000e3e3600161c203f092d063533102c0d381f25111a123242443728002719172b000a433b23210104a42030600090121c4800c84280040c00a064401a158550f31d85545c7059c55350f6590973c1a7054d43d96420070554d435c76590801c195350d70d96425c7031c95350d65c8571c0d7254d43d952100607a1d5350d654840181c8754d4359521005866406354f644840141d95cc773d9121005866407354f644840181e8754f30d912101e0721d5350d644840181d855cc6319121006265cd8018c644840141f97d8d53191210050765c6354c64484016199018d531912100623a19738c86448401894865cd31191215cf031c95350d64c80016159118d43d95200050765330dcf6548001615911cd43d952000607a1d43cc7654800741c9754d4359520006076117318c654800185573604631952000507e5f6350c654800141d9718d4319520005856446350c654800184e865ce321952000616219734c06548173c0d7254d43d912000507a5d5350d644800141c9754d43591205c7065c15350f654400181e8754d43595105cf055c55350f644400141e9754d435911000607e1784dcd624400141e9754d43589100050725d5350d624400181e8754d43589100060721d5350d62440014949750d315891001e2521d434c562440014589754d305891001e1621d534c16244173c157154d43189105c7065c15350c62440759a07460242485100064c21d54545404407f9607560652481101fe581d78548520440032e09661521481101d4e825185485204416f56297dd52148110007181db754852044001b2084dd52148110006c821075485204416d3a298e112148110006a821b844852044001d2075e112148110007481d48448520440759a084dd121481100153825974485204407f560955d12148110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x4
  | 4 => 0x5
  | 5 => 0x6
  | 6 => 0x94c
  | 7 => 0x94e
  | 8 => 0x94d
  | 9 => 0x98c
  | 10 => 0x98a
  | 11 => 0x98d
  | 12 => 0x98e
  | 13 => 0x3
  | 14 => 0x150a
  | 15 => 0x150c
  | 16 => 0x150d
  | 17 => 0x150e
  | 18 => 0xa0a
  | 19 => 0xa0c
  | 20 => 0xa0e
  | 21 => 0xa4a
  | 22 => 0xa4c
  | 23 => 0xa4d
  | 24 => 0xb09
  | 25 => 0xb0c
  | 26 => 0xb0d
  | 27 => 0xb0e
  | 28 => 0x1549
  | 29 => 0x154c
  | 30 => 0x154d
  | 31 => 0x154e
  | 32 => 0xb89
  | 33 => 0xb8c
  | 34 => 0xb8e
  | 35 => 0xbc9
  | 36 => 0xbcc
  | 37 => 0xbcd
  | 38 => 0xd09
  | 39 => 0xd0a
  | 40 => 0xd0c
  | 41 => 0xd0e
  | 42 => 0x1609
  | 43 => 0x160a
  | 44 => 0x160c
  | 45 => 0x160e
  | 46 => 0xd49
  | 47 => 0xd4a
  | 48 => 0xd4c
  | 49 => 0xd4d
  | 50 => 0x1649
  | 51 => 0x164a
  | 52 => 0x164c
  | 53 => 0x164d
  | 54 => 0x1049
  | 55 => 0x104a
  | 56 => 0x104c
  | 57 => 0x98954
  | 58 => 0x98955
  | 59 => 0x94994
  | 60 => 0xa0954
  | 61 => 0x94a14
  | 62 => 0xb0954
  | 63 => 0xb0956
  | 64 => 0x94b14
  | 65 => 0xbc954
  | 66 => 0x94bd4
  | 67 => 0x209
  | 68 => 0x8a
  | 69 => 0x1409
  | 70 => 0x128a
  | 71 => 0x1849
  | 72 => 0x1489
  | 73 => 0x180a
  | 74 => 0x130a
  | 75 => 0x19c9
  | 76 => 0x14c9
  | 77 => 0x198a
  | 78 => 0x134a
  | 79 => 0x150994
  | 80 => 0x150995
  | 81 => 0x99514
  | 82 => 0xb0994
  | 83 => 0x98b14
  | 84 => 0x154994
  | 85 => 0x99554
  | 86 => 0x1889
  | 87 => 0x409
  | 88 => 0xd4994
  | 89 => 0x98d54
  | 90 => 0x164994
  | 91 => 0x99654
  | 92 => 0x128e
  | 93 => 0x449
  | 94 => 0x1a09
  | 95 => 0xb1514
  | 96 => 0x150b14
  | 97 => 0x155514
  | 98 => 0x151554
  | 99 => 0xd5514
  | 100 => 0x150d54
  | 101 => 0x8e
  | 102 => 0x165514
  | 103 => 0x151654
  | 104 => 0x138d
  | 105 => 0x124d
  | 106 => 0x8d
  | 107 => 0x128d
  | 108 => 0x104a14
  | 109 => 0xa1054
  | 110 => 0x1a89
  | 111 => 0x1949
  | 112 => 0x198d
  | 113 => 0x134d
  | 114 => 0x138e
  | 115 => 0x124e
  | 116 => 0x180e
  | 117 => 0x130e
  | 118 => 0x154b14
  | 119 => 0x154b16
  | 120 => 0xb1554
  | 121 => 0xd0b14
  | 122 => 0xb0d14
  | 123 => 0x160b14
  | 124 => 0xb1614
  | 125 => 0x140d
  | 126 => 0x40a
  | 127 => 0x1a0a
  | 128 => 0x44a
  | 129 => 0x188a
  | 130 => 0xd1554
  | 131 => 0x154d14
  | 132 => 0x20d
  | 133 => 0x161554
  | 134 => 0x155614
  | 135 => 0x1a8a
  | 136 => 0x194a
  | 137 => 0x19cd
  | 138 => 0x14cd
  | 139 => 0x20e
  | 140 => 0x140e
  | 141 => 0x104bd4
  | 142 => 0xbd054
  | 143 => 0x184e
  | 144 => 0x148e
  | 145 => 0x160d14
  | 146 => 0xd1614
  | 147 => 0x44d
  | 148 => 0x1a0d
  | 149 => 0x164d54
  | 150 => 0xd5654
  | 151 => 0x188e
  | 152 => 0x40e
  | 153 => 0xb09895c
  | 154 => 0xb09499c
  | 155 => 0x9894b1c
  | 156 => 0xe8a
  | 157 => 0xe89
  | 158 => 0x18ca
  | 159 => 0x18c9
  | 160 => 0xeca
  | 161 => 0xec9
  | 162 => 0x1a4a
  | 163 => 0x1a49
  | 164 => 0xe8e
  | 165 => 0x18ce
  | 166 => 0xecd
  | 167 => 0x1a4d
  | 168 => 0x44b11
  | 169 => 0x443d1
  | 170 => 0xe9651
  | 171 => 0x18d651
  | 172 => 0x45711
  | 173 => 0x1a9951
  | 174 => 0x45651
  | 175 => 0x40992
  | 176 => 0x403d2
  | 177 => 0xed612
  | 178 => 0x1a5612
  | 179 => 0x41712
  | 180 => 0x41612
  | 181 => 0x1a9952
  | 182 => 0x98412
  | 183 => 0xb0451
  | 184 => 0xece92
  | 185 => 0xece91
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 64
  | 7 => 1357
  | 6 => 2760
  | 5 => 943
  | 4 => 69
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
  | 8 => packedAt gbK8 (1811+((h/21+packedAt gbK8 (1664+(h % 21)*7) 7) % 101)*7) 7
  | 7 => packedAt gbK7 (55633+((h/452+packedAt gbK7 (50209+(h % 452)*12) 12) % 2383)*12) 12
  | 6 => packedAt gbK6 (143520+((h/920+packedAt gbK6 (132480+(h % 920)*12) 12) % 3644)*13) 13
  | 5 => packedAt gbK5 (59091+((h/314+packedAt gbK5 (55637+(h % 314)*11) 11) % 1369)*11) 11
  | 4 => packedAt gbK4 (4991+((h/23+packedAt gbK4 (4830+(h % 23)*7) 7) % 83)*8) 8
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffff8f0e1ff0ff00e1e03c0fc830c7e39f293
  | 1 => 0xf0f00f00fe1ff0ffffe003ff010c37984e3f1c
  | 2 => 0xff000fff001fff000ffffc000270c7e18fc3e0
  | 3 => 0xfffffe000000fffffffff80f801f003ff
  | 4 => 0xffffffffffff000000003ff0001fffc00
  | 5 => 0xfffff000000000000000000003fffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x4550e830602b4550a68a09423801042a18f291
  | 1 => 0x54612900220554646aa81196080415980a1714
  | 2 => 0x66424b51001666414cccb904103046e08f43a0
  | 3 => 0x4048a9540000201114228c380a80160004a
  | 4 => 0x886ecd998888b8000600863db0001f5a800
  | 5 => 0x888f00081100000c0001803083eefb54000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfefefeeafeecfe00fefefeeafeecfe00fefefeeafeecfe00fefefeeafeecfe00fefefeeafeecfe00fefefeeafeecfe00fefefeeafeecfe00fefefeeafeecfe00, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36388
namespace PEqualNP.Outside.L_meta_36388
open PEqualNP.Outside.L_meta_36388.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 3 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 21 := bs0_3_0
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
theorem bs0_4_96 : Interval s0Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 99 := (concat (concat bs0_4_0 bs0_4_32) (concat bs0_4_64 bs0_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 46 := (concat bs0_5_0 bs0_5_32)
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
theorem bs1_2_0 : Interval s1Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 3 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 21 := bs1_3_0
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
theorem bs1_4_96 : Interval s1Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 99 := (concat (concat bs1_4_0 bs1_4_32) (concat bs1_4_64 bs1_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_32 : Interval s1Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 46 := (concat bs1_5_0 bs1_5_32)
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
theorem bs3_2_0 : Interval s3Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 5 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 25 := bs3_3_0
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
theorem bs3_4_384 : Interval s3Atlas 4 384 30 := block_range (n:=30) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 414 := (concat (concat (concat bs3_4_0 (concat bs3_4_32 bs3_4_64)) (concat bs3_4_96 (concat bs3_4_128 bs3_4_160))) (concat (concat bs3_4_192 (concat bs3_4_224 bs3_4_256)) (concat (concat bs3_4_288 bs3_4_320) (concat bs3_4_352 bs3_4_384))))
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
theorem bs3_5_608 : Interval s3Atlas 5 608 8 := block_range (n:=8) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 616 := (concat (concat (concat (concat bs3_5_0 bs3_5_32) (concat bs3_5_64 (concat bs3_5_96 bs3_5_128))) (concat (concat bs3_5_160 bs3_5_192) (concat bs3_5_224 (concat bs3_5_256 bs3_5_288)))) (concat (concat (concat bs3_5_320 bs3_5_352) (concat bs3_5_384 (concat bs3_5_416 bs3_5_448))) (concat (concat bs3_5_480 bs3_5_512) (concat bs3_5_544 (concat bs3_5_576 bs3_5_608)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_32 : Interval s3Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 40 := (concat bs3_6_0 bs3_6_32)
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
theorem bs5_2_0 : Interval s5Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 4 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 24 := bs5_3_0
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
theorem bs5_4_96 : Interval s5Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 117 := (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 bs5_4_96))
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
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_64 : Interval gbAtlas 4 64 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 69 := (concat bgb_4_0 (concat bgb_4_32 bgb_4_64))
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
theorem bgb_5_928 : Interval gbAtlas 5 928 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 943 := (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat (concat bgb_5_96 bgb_5_128) (concat bgb_5_160 bgb_5_192))) (concat (concat (concat bgb_5_224 bgb_5_256) (concat bgb_5_288 bgb_5_320)) (concat (concat bgb_5_352 bgb_5_384) (concat bgb_5_416 bgb_5_448)))) (concat (concat (concat bgb_5_480 (concat bgb_5_512 bgb_5_544)) (concat (concat bgb_5_576 bgb_5_608) (concat bgb_5_640 bgb_5_672))) (concat (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 bgb_5_800)) (concat (concat bgb_5_832 bgb_5_864) (concat bgb_5_896 bgb_5_928)))))
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
theorem bgb_6_2752 : Interval gbAtlas 6 2752 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2760 := (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 bgb_6_192) (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)))) (concat (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 (concat bgb_6_416 bgb_6_448))) (concat (concat bgb_6_480 (concat bgb_6_512 bgb_6_544)) (concat bgb_6_576 (concat bgb_6_608 bgb_6_640))))) (concat (concat (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 (concat bgb_6_768 bgb_6_800))) (concat (concat bgb_6_832 (concat bgb_6_864 bgb_6_896)) (concat bgb_6_928 (concat bgb_6_960 bgb_6_992)))) (concat (concat (concat bgb_6_1024 bgb_6_1056) (concat bgb_6_1088 (concat bgb_6_1120 bgb_6_1152))) (concat (concat bgb_6_1184 (concat bgb_6_1216 bgb_6_1248)) (concat bgb_6_1280 (concat bgb_6_1312 bgb_6_1344)))))) (concat (concat (concat (concat (concat bgb_6_1376 bgb_6_1408) (concat bgb_6_1440 (concat bgb_6_1472 bgb_6_1504))) (concat (concat bgb_6_1536 (concat bgb_6_1568 bgb_6_1600)) (concat bgb_6_1632 (concat bgb_6_1664 bgb_6_1696)))) (concat (concat (concat bgb_6_1728 bgb_6_1760) (concat bgb_6_1792 (concat bgb_6_1824 bgb_6_1856))) (concat (concat bgb_6_1888 (concat bgb_6_1920 bgb_6_1952)) (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048))))) (concat (concat (concat (concat bgb_6_2080 bgb_6_2112) (concat bgb_6_2144 (concat bgb_6_2176 bgb_6_2208))) (concat (concat bgb_6_2240 (concat bgb_6_2272 bgb_6_2304)) (concat bgb_6_2336 (concat bgb_6_2368 bgb_6_2400)))) (concat (concat (concat bgb_6_2432 bgb_6_2464) (concat bgb_6_2496 (concat bgb_6_2528 bgb_6_2560))) (concat (concat bgb_6_2592 (concat bgb_6_2624 bgb_6_2656)) (concat bgb_6_2688 (concat bgb_6_2720 bgb_6_2752)))))))
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
theorem bgb_7_1344 : Interval gbAtlas 7 1344 13 := block_range (n:=13) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1357 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 bgb_7_192) (concat bgb_7_224 (concat bgb_7_256 bgb_7_288)))) (concat (concat (concat bgb_7_320 bgb_7_352) (concat bgb_7_384 (concat bgb_7_416 bgb_7_448))) (concat (concat bgb_7_480 (concat bgb_7_512 bgb_7_544)) (concat bgb_7_576 (concat bgb_7_608 bgb_7_640))))) (concat (concat (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 (concat bgb_7_768 bgb_7_800))) (concat (concat bgb_7_832 (concat bgb_7_864 bgb_7_896)) (concat bgb_7_928 (concat bgb_7_960 bgb_7_992)))) (concat (concat (concat bgb_7_1024 bgb_7_1056) (concat bgb_7_1088 (concat bgb_7_1120 bgb_7_1152))) (concat (concat bgb_7_1184 (concat bgb_7_1216 bgb_7_1248)) (concat bgb_7_1280 (concat bgb_7_1312 bgb_7_1344))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 7 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 20, 21),(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 17, 21),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfefefeeafeecfe00fefefeeafeecfe00fefefeeafeecfe00fefefeeafeecfe00fefefeeafeecfe00fefefeeafeecfe00fefefeeafeecfe00fefefeeafeecfe00
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4278124266 * 2 ^ 32 + 4276944384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36388.Model.Repr at out
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

def mono : List Gate := [⟨.and,[1,5]⟩,⟨.or,[3,5]⟩,⟨.or,[0,7]⟩,⟨.and,[2,8]⟩,⟨.or,[3,4]⟩,⟨.and,[2,6]⟩,⟨.or,[0,11]⟩,⟨.and,[7,12]⟩,⟨.or,[1,9]⟩,⟨.and,[10,14]⟩,⟨.or,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124266 * 2 ^ 32 + 4276944384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124266 * 2 ^ 32 + 4276944384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36388

open PEqualNP.Outside.L_meta_36388 in
theorem PEqualNP.Outside.L_meta_36388 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124266 * 2 ^ 32 + 4276944384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124266 * 2 ^ 32 + 4276944384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
