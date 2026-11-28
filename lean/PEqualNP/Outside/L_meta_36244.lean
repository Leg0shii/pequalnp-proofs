import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36244.Model
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


end PEqualNP.Outside.L_meta_36244.Model

namespace PEqualNP.Outside.L_meta_36244
open PEqualNP.Outside.L_meta_36244.Model
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

def SBf (j : Nat) : Nat := [5, 5, 6, 6, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36244

namespace PEqualNP.Outside.L_meta_36244
open PEqualNP.Outside.L_meta_36244.Model
def s0K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (i*5) 5
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (6+((h/1+packedAt s0K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x1ffe07fffff81c1fffff03fe0fffff007e73fc
  | 2 => 0xfffff81f81ffffe0f81ffffff0780fff93fccf
  | 3 => 0xe0ffffe001ffffff001ffc1fff800fffe38f0f
  | 4 => 0xfffffffe001fffffe0001ffffff001fc0ff0
  | 5 => 0xff00000000001fffffffffe000000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xc22231451041240529272126048a690c26315c
  | 2 => 0x444450c8229208a05a09464a9050a25490d4c5
  | 3 => 0x8aa8a2035525154b0512a9152d014ca9630b0a
  | 4 => 0x14d1049260365a729640c219ca658031d80ea0
  | 5 => 0x18e1c71c79c79f9ce79cf3818c4608c1ffe000
  | _ => 0
def s0Atlas : Atlas := ⟨4,rawDecor 62 s0Pos s0Neg, 0xfcccf0c0fcccf000fcccf0c0fcccf000fcccf0c0fcccf000fcccf0c0fcccf000fcccf0c0fcccf000fcccf0c0fcccf000fcccf0c0fcccf000fcccf0c0fcccf000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36244
namespace PEqualNP.Outside.L_meta_36244
open PEqualNP.Outside.L_meta_36244.Model
def s1K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (i*5) 5
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (6+((h/1+packedAt s1K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x1fffffe03ff81c1ffffe0fffff81ff007cfe7c
  | 2 => 0xe07e07ffc1ffffe0f81ff0f80ffe0fffb3338f
  | 3 => 0xff8007ffffffffff001fff000fffffffc3c3ff
  | 4 => 0x7fffe001fffffe000000ffff001fc03f0
  | 5 => 0xfffff80000001ffffffffffff0000001fffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xc30c40238410a40318a60128e390990c14563c
  | 2 => 0x4910ca448ca28ca06a8a90b124b28a54b13285
  | 3 => 0x842514891144114d04152a02494524a942c15a
  | 4 => 0x1659e7122876de76b6c188a48e79c831fc03e0
  | 5 => 0x1861861c31871b98c719ccc7006100c1eba800
  | _ => 0
def s1Atlas : Atlas := ⟨4,rawDecor 61 s1Pos s1Neg, 0xfaaafaaafa00f000faaafaaafa00f000faaafaaafa00f000faaafaaafa00f000faaafaaafa00f000faaafaaafa00f000faaafaaafa00f000faaafaaafa00f000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36244
namespace PEqualNP.Outside.L_meta_36244
open PEqualNP.Outside.L_meta_36244.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x8040a2600ee42ed42be40bc40ee20ec20
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x802d0a0a16a10020
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 6
  | 3 => 2
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
  | 4 => packedAt s2K4 (104+((h/2+packedAt s2K4 (96+(h % 2)*4) 4) % 10)*4) 4
  | 3 => packedAt s2K3 (56+((h/1+packedAt s2K3 (54+(h % 1)*2) 2) % 4)*2) 2
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffff01ffc1fc1ff07ffffffe0fe03c9ff3e7
  | 1 => 0x1f83ffe0fffffe0ff87c1e03ff0ffff64cc7f
  | 3 => 0xfe003ffff001ffff0007fe003fff003f870f87
  | 4 => 0x3ffffffe0ffffff800003fffffc3f80ff8
  | 5 => 0xffffc00000000fffffffffffc0000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x1450011c208220033008c223960122840951e3
  | 1 => 0x4c225224651084a0548351448a9049a924c42d
  | 3 => 0x28b6b448c3b54d6d0c45b5092daa0533870e86
  | 4 => 0xb14528910a206a56a9502012314c9602d80b50
  | 5 => 0xc18630e18c398f98ce66399c01881823f6a000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeeeaaaaeecc8800eeeeaaaaeecc8800eeeeaaaaeecc8800eeeeaaaaeecc8800eeeeaaaaeecc8800eeeeaaaaeecc8800eeeeaaaaeecc8800eeeeaaaaeecc8800, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36244
namespace PEqualNP.Outside.L_meta_36244
open PEqualNP.Outside.L_meta_36244.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x100aa184ee32ed32de31dc31ee21ec21
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x202c8a299710c421
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 6
  | 3 => 2
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
  | 4 => packedAt s3K4 (102+((h/2+packedAt s3K4 (96+(h % 2)*3) 3) % 8)*4) 4
  | 3 => packedAt s3K3 (56+((h/1+packedAt s3K3 (54+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x83fffff80fc1fc1ff0ffc3ffffc1e03d98fe67
  | 1 => 0xfc07e0ffffffffe0ff07fc1c07fffffe6733ff
  | 2 => 0xfff800fff001ffff0007ffe007fe003f87c387
  | 4 => 0xfffffe0ffffff8000007ffffc3f803f8
  | 5 => 0xffffff0000000ffffffffffff8000003fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x98514808e08a24033028c0a472d122a4885663
  | 1 => 0x9308111250080a051034408914249882330ad
  | 2 => 0x30a2daa243ad4d6d08a5aac125b5053385c386
  | 4 => 0x62c51cc48a286e56aab0228246399623d80350
  | 5 => 0x430610870c318b98ccc633138020180376a800
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeacccc8080eeeeeaeacccc8080eeeeeaeacccc8080eeeeeaeacccc8080eeeeeaeacccc8080eeeeeaeacccc8080eeeeeaeacccc8080eeeeeaeacccc8080, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36244
namespace PEqualNP.Outside.L_meta_36244
open PEqualNP.Outside.L_meta_36244.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x600000002c4800000813224844a25005d380007c0891c68008463c987183450000700003c6ca80000058000002003a000000000c8004002a12060180000020101000c08e001408eff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x2437c50486fea810df95021beaa0437c54086fea610df94c21bea98437c53086fca410fbcc821f6190437e51087ec8210fd50421fb98843f431087de4210fd88421f690843f521086fca010df54021bf29e817d53d02fca5a05f54b40bf28e817d51d02faa9205f94e40bea9c81bf439037a87205f94a40bea9481be429037885205f94640bea8c81be419037883205f94240dfa0481fb40902fea6a05f14d40bfa92817c52502fea2a07dd4540bba8a817c51503e8a2a05d14540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea9881bf431037a86205f94840f7290816e52102faa4207b54840b6a9081be421037884205f94440fb288817651102faa2207d54440baa8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330ef21e61dd43cc2fca5985f54b30bf28e61f651cc2eca3985f54730faa8e617551cc2fea9185f95230beaa4617c548c2faa7185f94a30bea9461de328c3b865185f94630bea8c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130ef21a61dd434c2fea4985f14930bfa8a617c514c3f66098778c130bfaa0617e540c2faa8185f15030bf298617e520c2faa418778c830ee190617e510c2faa2185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c82fca3905f54720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3105f94220fd18441f930883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20f721241ed42482fea2907dd4520bba8a417c51483e8a2905d14520fd18241f930483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20bf290417e51082faa2105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43f681887e10310bfaa4217e54842faa9085f15210bfa9c217e53842faa7085f14e10bfa94217e52842faa5085f14a10bea8c21f741843e883087d8c610fa98c21f721843e843085f94210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea6885f94d10bea9a217c53442fea4885f94910bea92217c52443ec82887d50510fd88221f610442fea8085f95010beaa0217c54042fea6085f94c10bea98217c53042fea4085f94810bea90217c52042fca2087dd0410fa20821f631043ea62087dc8410fa108217e50043f680087e10010fb88021fa10043ea20087e44010
  | 1 => 0xf4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf28887f65110eeca221df54443faa8887755110efca021df54043bf29e85de53d0abca7a15f54f42eea9e855d53d0b7e87a16f50f42bf28e85f651d0aeca3a15f54742faa8e857551d0afca1a15f54342beaa4857e5390afaa7215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42dfa1a85bd4350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e5310afaa6215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332bf28e657d51ccafca1995f54332bfaa4657e548cafaa9195f15232bea9c65de438cbba87195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbde6499778c932bfa8a65f7514caeea2995f14532fa28a6574514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf29865de430cbba86195f94832ef99065ee320cbba64197b4c832bf28865f6510caeca2195f54432faa886575510cafca0197e94032bd280657d500cbf2a0195e54032bf29e837d53d077e87a0ef50f41bf296837d52d06fca1a0df54341beaa4837e53906faa720df94a41bea94837e519077e8320fdd0641bf284837d50906fea6a0df14d41dfa1a83bd43506fea4a0df14941fba0a83be41506fea0a0fed4141bda82837c50507f0a0a0de14141bf2a0837e53107bca620d794c41bea9883dd53106baa620df94841bea90837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331ef21e63dd43cc6fca598df54b31bf286637d50cc6fea918df95231beaa4637c548c6faa718df94a31bea9463de328c7b86518df94631fb20c63f5418c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c7bc8698f750d31bfa9263ef524c6dea498df14931f6292636c524c7ec8298fd50531fb98a63de314c6fea098df14131bfaa0637e540c77ca818cf95031beaa063bd540c67aa818df15031bf298637e520c6faa418f78c831ee190637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21fb20e43f541c87ee6390fd0c721bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510fbcca21f6194437e51887ec6310fd4c621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a43df53486bea690df94d21bea9a437c53487b8a690d714d21fb18a43f531487ee4290fb88521bfa8
  | 2 => 0xa89a8003782d8a29941745a40001900000000000000090761f9000000b609348e348001ab31a000002054ce24800000000170000002081c80000000000000000000000000004040000000000000119a1a4181812213f3d49941699d26e0009c00000000000000000000a989b0002940017747a4940005d000394001520000000000020a60d099583c67106c1260009800010f01237800128000000001aa384000000003d2000ab123000000ae94943e41c000003ea0008a89e000194000210220000000000039c00000000228001ae2a2688f68000000a0ef0002020800000038a000000000005183d8002ca3252c96a3b40580013b10e0002a2561302901119e26690000000000000000711e83a85680000078030a4824000132000000000000db1e6000000000000000000039a75c0000046c000b7800444001319d43f4788d6a3820403cce0001ac1f827000000450680682889500005f00000000000000554220000c64a8000cb000538cb00000000000000000000000083fe79c9e8000943fd1413a0000004280000000000000000700209631040008800010c238001b80000d86e00001619cb70000000000017b000380000000000002a80000000000000308000f30900006fc000002949886c91f0d47a0000001da0f4c282b2522ec000000000000010900028c0387512800067000376000021b9000000248000d68b0540ae20c000552000fe8200019802a6943c90b07e0001d09a4a4668d303900092c6205a000764bf800000328030a9218630ee20e00000000000462074a10001ae000001d50000009900017206800173000000132120000004e199000000778003ac0000000000000000225316001019df000000000000007f4160343a61b4001640000007104700000000000206000001340000ec000000000000002f000000000001ea76c0023e000001180000000008e2463f0000000002da5c91d000386504ba0000000040140780800200000001006000000020020080100f00a0000000700a00000000000000010010020000380000600c0000300e000030000060000000700c048000000000000080000000000802004010000020040080080100c00004002000000000010060000080e00200005800004004010010000140180000201400806002034010000000000080100600c00000004018010010000100100000000c0000200001c0100000c00000808002000000010020180000000200c0000100200802800004000008000000080080300402400006004000010000080100080100400c0000000a00c008030040000000001a004008000060040400300200c0000100001c000010020000000000600c018000040340000000001803002bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87d
  | 3 => 0x3126002d800454350000b200068c002211421e8ec000000188000001f01400000045a0000011200000000000000795218b539e3dc13a570a23e4090004b03900000000097400084000000ca8003a200000168000000210000000000017d4928fc5625f44834c000002e24c40000035e00000000000234000000006a47b00021a00115a110e08343302e4b68806615903c444fa0c204a720ad80e1f49848b1b70000000991300000000000340684002234725d8002290000000000033e0002f0000007f0000000000003e8571d0704000000006c8000000000000000000063c00000234000000c62f20010800000050c000a0000000678640784bca41170000cc0020b2c413439a4a2a06c00004500000075a1e000000258e606e66c00232000000000000046b096000000000801c72607c8000000000000021d000001038b41dc6d4000c5080000b301c272748e31671aa000000000de99800000000120df0230dc22c790c816e0000016101a7240014b000000060913945c0f79b3278628a68fb36c738e809524e259009ec3ba2fc588c00006183c00049a3f0512062be1191a005000000be15a00027ccb9190007ac0007c1fc5700000036230c0000000029c00000000000c08000000000020932025c598003c8000190002ae368001f61329445f0772d60006880011272caa0000000000005300037c21a5e46a000001f11fa0c0d20cd00007c40000000000000694a073053035000374001f72560000091d2c00009700000031c278000000000023b310000da124000000c7187000000d400024206c0c0580e8158f70f10140012708845c8510b11e23046c7820a11e0c41f04c3fc64c000004b85f8000af34e6485c0030b22ac7085202e274001363c2644f9a371c6000a390a0000012988c0004b400000000000000c10005d4a797a430810580000000a51e24541e43917a1b0000000015e00000000014244000c106c49e1d8000002f07c0000e944e205261ba0002f41c13e0000012a9bd00090800000000000000002800005e0004388980008342e855208003f60010c94c210000000000000412d
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xd431034e5394840d354e521034e5354840d354d521032f4354840cb50d521032d5290840ae58042103565394440d554e51103665294440d954a51103565354440d554d51103665254440d954951103374354440cd50d51103706054440cd546411029d63104408fd9540102b461500409ed9540102f061500409d98754cc27561d5330c798e54cc27661153309d58454cc31e5450f30cd95251cc3355494730cd95151cc3355454730d590d51cc35543547309b988548c26d62152309d984548c2756115230b6580328c26f62551309b189544c27761551309d185544c27661151309d584544c25c6550d309798c540c26e62150309b588540c27661150309d584540c23e6494c308f592530c27761548309d185520c34d520c83097d95300c27b654c0309d98754c827561d53209798e54c825d63953209d98654c827561953208f99053c823d6414f209d98453c82756114f209798c548825d63152209d984548827561152209d987538827561d4e208f992538823d6494e209d98653882756194e208f992544825e63951209758e544827661951209d586544825f63551209718d544827761551209d185544823e6515120cb588544831f54d4d20c7153534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209dd8553482746154d2097994534831f5414d20c715053483596014d20cb152424826c6550920cdd53514833454d4520d5d4f514835453d4520cdd5051483345414520d5d4c51483545314520d614e3048278654c1209798c540825d63150209b988540827661150209d584540823e6414c208f59053082766114c209d584530827a6014c209bd95200827b65480209798c54c425d63153108f99053c423d6414f108f99352c423d64d4b109798f52c425d63d4b10bc18141c42f16110310ec90440c425e63152109758c548426e62152109b588548426e62d4e109b58b538423e6494e108f592538425e63d4a109758f52842d56310610d594d31842e4624c6108f992544427761551109ed81544425e63151109758c544423e6515110c798c544431d6315110cd584544423e6494d108f59253442756194d108fd91534423c6454d109bd89534426c6254d108f992524423d64949108fd91524423c645491097d8d524425c63549109dd8552442766590510cd15241442746550510cd15141442f06050510ce153104433454841109798c540425d63150109b988540426d62150109d984540423e6414c108f590530426e6214c109b588530425f63548109718d520423e64148108f590520425e63148109758c520427565d04109d59441042d563104109d59631042e4624c4109d59421043655208410bc58021042796510010ec104400427965840109dd9510042b464440109ed9510042b86444010
  | 1 => 0xb0001004040280c600d008302c00058000001018040a060704800010000c1600038380000010180201070280603010000004038102003058001201010000405000180e040202006000800400020280000079dd8550d0e7461543439dd855290e746154a438fd954310e5f6550c43cdd0d5110f564354443cd50d5110f554354443c794d43d0b565394742d554e51d0b565354742d554d51d0b374354742cd50d51d0a766114d429d5845350a3f65508429bd954210a7761540429d1855010a7661153329d58454cca7661952329d586548ca3f64542328f191508ca7761542329d185508ca5d63951329d986544ca7561951329dd85544ca7461551329ed81544ca786055132d9cc8514cb5632145329d987540ca7561d50329e983540ca7960d50328f596540cb1e63950328f990540ca7661150329d584540ca7a60150329e580540ca5d6590c32b358a430cb1e5450c3297d95320cad4614c8329bd95320cae4614c832cd952510cb355494432cd951510cb355454432d590d510cb554354432ce952500cb395494032dc946500cb715194032ce951500cb395454032dc945500cb715154032d690d500cb59435403297d8d529065c6354a41ced0c50507394314141dcd04505073a4114141c754f411075553904418fd95411071d5350441ae18141106776550441d554d41106f060504419e98354cc67960d5331b5584328c6f060506318fd91508c63c64542319b98a544c66d62951319bd89544c66c62551319ed81544c678605513197195434c74e4314931d350c524c7656114931d914a414c6746550531e550d414c7645250531bc181414c76452cc531d314a314c63d65950318f990540c65e63150319d984540c71d548c831c7550320c71d54cc431cd552310c65f654c431c7551310c6cc624c4319dd95310c735544c431b9189310c67a60d53219e58354c865e63953219758e54c863e6414f218f59053c867a6014f219e58053c87365450721bc18141c86b5640c7219798c548865d63152218f990538863d6414e21b958432887c4328c621b9189318865e63951219758e5448675619512197d8d544865c63551219ed81544867860551219798e534866f6254d219dd85534863e6414d218f590534865e6514d21c7990534871d6414d21d55845348676658c521d514e3148674654c521d514d31486e4624c521d514f214874c53885219798c540865d63150219e980540867960150218f990530863d6414c219d984530867a6014c219e580530866d650c8219d59641086f060504219d5973108675650c421ad59031087c4320c4219bd9521086cc63484219dd9521086d463484218fd91500863c64540219d98653902756194e4097d8d529025c6354a409dd8552902746154a40a758c419037051d0140cd14640502b960d0c40c794
  | 2 => 0xc209c00116948928f9b85c800b6000a51f07fada0000063000000000b8d41ea6e2f3204da7a3785cafa84b09ec758000e8587e0406d8004a800038009a80071800000006b04a00022ba0002aacac9020c2800b9800c70a00aab0448b43e0fcb430c4980088a04c60005aaba66ae4000a28da581e0ac3a94e3381c2321e000f4131f66e894bb15e3a32e398c4680965da487484e908da4d2bc739b2423382ba640100068aa2212ae7509e5e13214844062b4002203487285128002e23200000254481b4670689d0f0000001c05e3891ca02d23b9983e922cc0a41d20c15a1aa082c41a5c8b0d84b18eb3b1e6f00000304942187607e4614600200532fe0004800228cc8065a28cc41827b95a76b224e98459974b022a8280058af418268431601b25e81b2c788627e9565103e6296e699caa4a3aa40b6b1800000d6002305400c0422e54a38002f8001be0014a260a600000308e4968a8a5a0200076000002e8b04900050ab8052d67331a618bec0a726017e23a4a3b1d0552a4708fec0148821642690a009a84e0f64390289ac8000000000078328a2ae002a44a19de04ad42cb1209038ca92e5019eadb068d0f24f2a064b0e1521c9f05a95834700008416c000c60d800aa9ae000885f0cc068004011434000a2050372b23002800016000327a8468f216562127a104241a446800bb882710ca0798898a9c7200009af67d06e6580021994cda98a7aaccd000c58309d990440663827098170c988abaa24a99e64c2665e864ce9dc2e03c6c2dc90000b10008c8001f2cc7f000002a8bea7e00000939f26aa0e1080079000000001a800bca78c50004fa8ebc26cb780091a4ca6800bf0000215c2000000000478040200004100501044761100804060c02000000804808000702820021c00008082e0604022000501006020283c14030080c2001030080e0104880040a018282808000200a0416004020
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x42c019000c20101528034f5000021d36160170093914830050000011202e001311c56290c32c32a63028220e51531814110782a18a4a0a63a450c6050531cc0a43028298e0d54189310c712aa0c498863455ce5450721c64a83028390e1564584534868aba0a698a439114c624c521d0ac81906210cb071583431025838ac021081511c5520c830a2ae929a630864653189318430ab1ac22a221455cc5450510c60a830282885447354821042583a2c010821645cc4110010
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x2004008600e01431486050531a11839506050721a058414c624c521a058494c624c610a11831506050510
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
  | 5 => packedAt s4K5 (18887+((h/205+packedAt s4K5 (16632+(h % 205)*11) 11) % 1082)*11) 11
  | 4 => packedAt s4K4 (16974+((h/138+packedAt s4K4 (15732+(h % 138)*9) 9) % 497)*10) 10
  | 3 => packedAt s4K3 (1273+((h/8+packedAt s4K3 (1225+(h % 8)*6) 6) % 34)*6) 6
  | 2 => packedAt s4K2 (304+((h/1+packedAt s4K2 (300+(h % 1)*4) 4) % 9)*4) 4
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfffffc07e1ffc1e1fff87ffff0e03f8e3f33f
  | 1 => 0xf03f87ff801fffe01f0ff8f01ff003fc9ccc3f
  | 2 => 0xffc007ffffe0ffffe00fff001ffffc3f1f0fc7
  | 3 => 0x7ffffff07fffff000001fffffc7e00ff8
  | 5 => 0xfffff800000007ffffffffffe0000007fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x628500470422100603118111cb02284821531b
  | 1 => 0xa58a4c891d4c64e10d86c8a2559052948ccc2d
  | 2 => 0x411311122806812a200b120486249821170546
  | 3 => 0x8a2c66245110365556a0408918c96306e00ab0
  | 5 => 0xc3044386198c79998cc64ce00818207daa000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfaeafaeaf880f880faeafaeaf880f880faeafaeaf880f880faeafaeaf880f880faeafaeaf880f880faeafaeaf880f880faeafaeaf880f880faeafaeaf880f880, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36244
namespace PEqualNP.Outside.L_meta_36244
open PEqualNP.Outside.L_meta_36244.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x2437c54486fea690df94d21bea9a437c53487dc8490fb50921fb18a43f531487ee4290fb88521bfa82437c50486fea810df95021beaa0437c54086fea610df94c21bea98437c53086fca410fbcc821f6190437e51087de4210fd88421f690843f521086fca010df54021bf29e817d53d02fca5a05f54b40dfa1681bd42d02fca3a05f54740beaa4817e53902faa7205f94a40bea94817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c53502fea4a05f14940dfa1281bd42502fea2a07dd4540bba8a817c51503e8a2a05d14540fda0281be40502fca8205f94c40bea98817e52103dca4205b94840bea9081ed52102daa4205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330bf296617d52cc2fca3985f54730fd20661f940cc2fea9185f95230beaa4617c548c2faa7185f94a30bea9461de328c3b865185f94630bea8c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130bfa9261ef524c2dea4985f14930f6292616c524c2fea2985f14530fd98261de304c2fea8185f95030beaa0617c540c2fca6185f94830bea9061de320c3b864185f94430bea88617e500c3f480187e50030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c82fca3905f54720fd98641f830c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5107bcca20f6194417e51882faa3105f94220fd20441f940883f461107e4c220f790441fb20882fea8905f95120beaa2417c54482fea69077d4d20afa9a417e53482faa6905f14d20ee29a415c53483dc84907b50920bfa8a417c51483f480907e50120fd18241f930483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53082faa6105f14c20bf29041ef32083d864105f94420bea88417e50083f660107e0c020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fda0621f840c43f661887e0c310fd10621f920c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dd0610fa20c217e50843f481087e50210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea6885f94d10bea9a217c53442fea4885f94910bea92217c52443f480887e50110fd88221f610442fea8085f95010beaa0217c54042fea6085f94c10bea98217c53042fea4085f94810bea90217c52042fca2087dd0410fa208217e50043f680087e10010fd98021f830043f440087e48010fb88021fa10043ea20087e44010
  | 1 => 0xa50d0ef4a1a1df54343fca86877950d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42dfa1a85bd4350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e5310afaa6215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0217e94042bd280857d5010bf2a0215e54042bfaa6657e54ccafaa9995f15332f721665ed42ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbde6499778c932bfa8a657c514cafea0997ed4132bda82657c504cbf0a0995e14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf298657e520cbdc84197b50832ef99065ee320cbba64197b4c832bf28865f6510caeca2195f54432faa886575510cafca0197e94032bd280657d500cbf2a0195e54032bf29e837d53d06fca5a0df54b41bf286837d50d06faa920df94e41bea9c83be43907788720df94a41bea9483bf429077a8520df94641dfa0c83f741906fca120df54241bfa9a837c53506fea4a0df14941fba0a83be41506fea0a0fed4141bda82837c50507f0a0a0de14141bf2a0837e53107bca620d794c41bea9883dd53106baa620ef90c41de218837e52107dca420db94841bea9083ed52106daa420efd0841dea10837e511077e8220fd90441dea0883f541106fca020fe94041bd280837d50107f2a020de54041bfaa6637e54cc6faa998df15331ef21e63dd43cc6fca598df54b31bf286637d50cc6fea918df95231beaa4637c548c6faa718df94a31bea94637e518c7be6318fdcc631bf284637d508c6fea898efd51319faa2637e544c6faa898df15131de2a2633c544c7bc8698f750d31bfa9263ef524c6dea498df14931f6292636c524c7ee6298f78c531bfa8263fb504c6f6a098df14131fc2826378504c6fea818df95031beaa0637c540c6fca618df94831bea90637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c86faa790df14f21f721643ed42c86fca190fe94321bd286437d50c87f2a190de54321bfaa4437e54886faa910df15221bfa9c437e53886faa710df14e21bea9443ef32887d86510df94621fb18c43f531887de4310fdc8621bf284437d50886fea890df95121beaa
  | 2 => 0xc103481c4422e0002b1320300006747b13817c8a5228530006a07693a1245840da3b1cc038fca183b64d88f19a0004691f000000000e220d1084ac090d4078340eb18a1ac698789a03c03a0390000ce444b80d508e000af91d3ec0000000047e02c00000072968d52130008cd21800000000001c5000194c31fa424000001ed45a2b8cda4406c360041ca10c578828da1008305e9df066228ff0fd14a7006f1720d8760810024ae7ec4f96549437d0b1883e03a4e813139a750b619329c3d042921074554782660468f08782d32832c261044842ec631be04e4649c90606293d1c9da4ac5083510822c000610e3416430b520f3d800c0e08d0d0000ae2580b829c672324423fcc602b406110739154a6938419640e67bc5c9a51a20f4930643ea164210e101a1f0779a303c3c89920814291d0109919e258029710da13ce40554707c8eb80005e0000016936a40c001bc000000db9b94080002f95d2886fcef0870ee92c000001685283813e138000f99c611c0ec0a84e1828bccc2634282900603700081879a1913015ccc8613e87a83a0c83c486920a5904025075201140708000000dc3dd2f9e11262c8a00a32ae6e0d78b019a05c001ab468074598604ca6011d0b139816c511bb2e87704a9e84380012311b0121451589a0cc3281203426a2a05300f2764810fa100440451618716c4b87a90d344064b19d133c3f0ba92c3aa41ce71ad174978a097e462814000002904251b800000900db0bf0001bc758000fa450001e430a000000004a05248998308a6c8550002141fc0016843a6a4149cb03e5583c1890000006d9231226e88095221c0004b8c50000000023d0001886e8000002ac00000000000aa220446724a61f81c4540200062000b11a91f250000ad1774c0330770fa0fc8a8569ff1025cc4e94d220159110a90008943497c49a5d8a796f0084dc001921182e01919f0f6001261c72f0988e18900706d0000af302954d99e716e000001fc0001c4951e916a3807f14b3484f4001cf2fa000000230dc0102001060020080001c39000050240c04c0a0080303006044050b4110002800c000100401801004280041a0480502805000030241900000000000140601c06000150080507803128130841700c020100e058010d80c00000000460140300c030080c00c0007003000000000001c0203409004000000200c0304c0d00c010040800006048091000b008010100200c380f80f00c0300c000140200003080000283d030080100b004000000c01c040000b0180101009034000482203003000000380700c00010120140000c050180c1a8000080900c0400402000040500100c000140002c04000010000f008010a40e054030100700c050200201c0c14419bf29687ee52d0edca5a1df54b43f6a96876d52d0efca3a1df54743bf28687f
  | 3 => 0x25c0ec040001e31ae4d10a9e5094000478fb32a390b116e4220003a8001860000500008c5ec0008922400000000000000001241a4000000130000012da5242e5640021b04a0000002e2861782809e4125e930918000974f58000009443d0c44506081419126089c2482a178000bf9d235c65924a672da0004d9900005600000023865c91041116050131bd43c4f0001a70008292a0003a60f9130000003b0ad9ee0005802d2300c61490012731a000000002ce000000001b27c400816030120601b0192670001d928e6c4979dd0f210c969fd1ca0000000028a638b580718e5e4f30f826663d1b0211b8838a990b24a000d62240966842c18407e134b318b2a25183588206a3e4948d30ba9208b8003ee000000000004fc2a1
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x540867b6054c219e181530863e6414c218f59053086766114c219e98053086796014c218f992520863d64948219b594320874d530c8219bd95210867765484219bd89539026c6254e40ae58041903374214540cd50851503716014540dc14740503345190140cb54a411032d5210440cb54b401036952900408fd95401032d5250040ad185401027b6550040da54940102f061500409d98754cc27561d53309b98a54cc26d6295330ce95140cc2f061503309b988548c26d6215230b6580328c26e62951309b58a544c27960951309bd89544c26c62551309dd85544c27461551308f990524c23d6414930cb990524c32d6414930da580524c36852cc130d314a304c26e62150309b588540c27661150309d584540c23f64544308f191510c2796590030bc185400c25f654c030b3189300c27b654c030ba189300c27661d53209d58754c823e6414f208f59053c82766114f209d58453c82e9600ca208fd91518823c6454620bc18540883c8328c220ba189308825e63951209758e544825f63551209718d544827761551209d185544825e6394d209bd89534827b6054d209799453483596014d20d314e424826c6550920d314d424835853901209e19540483585350120ea50940482f061501209e9963048358538c1209e1953048358534c120ba189304835853c8120d314e204823d65950208f990540826e62150209e980540823e64d4c208f593530823e6414c208f59053082766114c209d584530827a6014c20cb553320826d650c820cb550320827965cc020ce5533008279650c020ce55030083c8320c020cb553200833954880209bd95200832d5448020b318d200827b6548020ce55120082d863480209798c54c425d63153109b98854c426d62153109b98b53c426d62d4f109798f52c425d63d4b108f99252c423d6494b10ba58840c42d86348310da94920c426e62152109b588548423e64d4e108f593538426e62d4e109b58b538423e6414a108f59052842f16010610ec10640842f061502108f992544427761551109ed81544426e62151109b588544423e6515110cb988544432d6215110ce580544423e6494d108f592534423f6454d108f191534426f6254d109b189534427b6054d108f992524423d64949109e582524423f64549108f191524425f63549109718d524427a6590110ce15240442786550110ce15140442f06150110ce153104433454841109798c540425d63150109b988540426d62150109e980540426f6254c109b189530423e6414c108f590530426e6214c109b588530423e64148108f590520425e63148109758c520427565104109e59740042796510010ba58840043b041100109e5943004359530c010bc58430042796588010b618d200427965840109dd9510042b464440109ed9510042b86444010
  | 1 => 0x40080400005000000000a00002008020040104400020020080000c00004060180002c07000050300300000008000280100404018010000000c000040301c0200402008000340200000000030040103801da94a50d0f695294343da94950d0f6952543439e9805250e7960149438fd954310e5f6550c439ed815110e786054443ae58343d0a7b60547429e18151d0a7b6054e429e1815390aae62d0d42ae5834350a3f65508429bd954210b3b4254042da9095010b394254042da5095010a7a60953329e58254cca3f64547328f19151cca7b60547329e18151cca7a60152329e580548ca6d62951329e982544ca7960951329dd85544ca7461551329ed81544ca786055132dacc8504cb5a32141329d987540ca7561d50329e983540ca7960d50328f596540cb2e62950328f990540ca7661150329d584540ca7a60150329e580540ca6d6590832b358e420cb2e545083297d95320cad8604c8329bd95320cae8604c832cd952510cb355494432cd951510cb355454432d9909510cb654254432ce952500cb395494032dc946500cb715194032ce951500cb395454032dc945500cb715154032da909500cb6942540329bd89539066c6254e419ed8153906786054e419e98252906796094a41dcd04505073a4114141c754e43106b56110c41d394e521074d5394841d394d521074d5354841c754f42106b561d0841c754d421072e52508418fd9541106b860504419dd9541106f06050441d694e50107595394041da94a50107695294041d694d50107595354041da94950107695254041ced09501073942540419e98354cc67960d53319b98a54cc66d62953319e98254cc67960953319b988548c66d62152319e980548c67960152318f992528c63d6494a319e982528c6796094a318f992544c66e62951319b58a544c67a60951319e582544c66f62551319b189544c67b60551319e181544c63e6515131c758c544c71c5490d3197195434c72f54d4931cb153524c72f5414931cb150524c7656114931ced53504c73854d4131dad4b504c76852d4131ced50504c7385414131dad48504c76852141319798c540c66e62150319b588540c67a60150319e580540c65f654c4319dd95310c67a60d53219e58354c872e62953219e98054c867960153218f99353c863d64d4f219e98353c867960d4f218f99053c863d6414f219e98053c86796014f21cb95142c873a5494321ce55250c873a5454321ce55150c876a4254321da50950c865e63152219758c548867a60152219e580548867a60d4e219e58353886e5610ca21b9189318865f63551219718d544867b60551219e181544867a60151219e580544863f6454d218f191534866f6254d219ed8153486786054d219b1954248674654c5219798c540865d63150219b988540867a60150219e58
  | 2 => 0x3220a9198c6f000bc8125400000008002f483070c4a58000006d9a099a6c0031444ac68b80000000002acc63088d10a000ba0000000000001da24a32588000017ec580000000361520018477000001e0271f800000000005d038002e4190000023e74800000000022cab8006b000cd8006400000000010002401c0d0000012a49000290000002c79800000003a00e848f2378063eb06318489d800ac8000c00048800002eca88002b260002eecd0229332241a887400051a2855acec9082888ec0000000018431948183a569763e28e0021a000105702ace9c00032c67ab85c99800000bd95400000002e25201446a9a528860000000000000001f32000286790000000000000002f0498ce0027caf800001041c9646e800ce0da000169b8f000000000001780089af815000002d6710001380000000000008e18a87a8c990004e9c87785c0012c258001ead40031040000000000292e0f1be001a60002ecb80000000000001b0000005000192000000000000000002ca7e88c148000030e0000065800001ce912b411a5aa59b8b4828392fc460b6000000023c4e0000000000000000005e878002b67a800a02560018000000003283700000000a48000011c00302bfaaa690002f0007b800348a2000b8000000000000000000000027a000680000026800000000000043aba000000000034000000d6b6080002de2a8f62a00000168000000016e8aa5e3123019800c70002ca00459b22103600130000ca00000002080c800001865e3327fa507c26a000007f0e676000000000000000000cc290be80000000c98fe9e0a67a000509a82f8007d800000e20004a3aa720032a00000000cc00000788005303eaf06ea52c08e840000000005a6384c25298579084c80060800539c62200000000000003b96600000001aa92000002c400000850981100c002e6882a6672dc00056b31440030aba16a000000015800218000000000066800001b000000890007d0009c110000002831e8700098a7ea11600000018ad0002040024a0017c0013c001a20029e7c80040aa4ba8004d80000000000000009e00000000765b08a3806a620425c2360000097000002b0729ae3020ec106080aa000134000f407a7490000aa000000000024e00000002e0a72da30800500003f000000004fa52090004a02690b0ca28b46d01a85ac80007400210009d67092000000002687300095282080b0000ae001ec35000479140000075000b0b1a1600023800000001f80000300000000080200001000000000300c000000000000000040000000c01018030200200002004010000000c01034040000401000004000040300005028010080100c0102406010030000100401018030000e0040000004008020040100
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x1802895cb40e31135508100500300001300050060f5871122000831030a183321c16390832960e0b088620cb07058742106a4382a619043895486150040cc2a430a80205297295140cc3192a0c2a06618a5916014930e10a6a128090650531854048350a10c2a02412a5d0624c120c90a63126090709540c83008306aa0c690041865506348020a52e929241886486394920c4314b12c02a2214a5c85450110c60a830a80886a16210440042a4392a6180212c1d1610c010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x62400800000000a21829506150330e00535086150120c097414c624c120c097418e5248310a21821506150110
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 616
  | 4 => 414
  | 3 => 25
  | 2 => 5
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
  | 5 => packedAt s5K5 (18682+((h/205+packedAt s5K5 (16632+(h % 205)*10) 10) % 740)*11) 11
  | 4 => packedAt s5K4 (17112+((h/138+packedAt s5K4 (15732+(h % 138)*10) 10) % 726)*10) 10
  | 3 => packedAt s5K3 (1273+((h/8+packedAt s5K3 (1225+(h % 8)*6) 6) % 34)*6) 6
  | 2 => packedAt s5K2 (304+((h/1+packedAt s5K2 (300+(h % 1)*4) 4) % 13)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf03f87c0fe1ffc3e1f1ff0f01f1e03fc3cc33f
  | 1 => 0xffffffff001fffc01fe1ffffffe003f8c7fc3f
  | 2 => 0xffc007ffffe0ffffe001ff001ffffc7f070fc7
  | 3 => 0x7ffffff07fffffe00001fffff87f80ff8
  | 4 => 0xfffff800000007ffffffffffe0000007fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x15854c4e252a540f0b12b8924b1228cc1cc31b
  | 1 => 0x228a00821c4420c005205121d5205110415c2d
  | 2 => 0x411355144906855320116a8486549865070546
  | 3 => 0xa2c2228901032a45644000918896202e80ab0
  | 4 => 0x8c304430e198c73998998cce00118047b6a000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeccf880feccf880feccf880feccf880feccf880feccf880feccf880feccf880feccf880feccf880feccf880feccf880feccf880feccf880feccf880feccf880, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36244
namespace PEqualNP.Outside.L_meta_36244
open PEqualNP.Outside.L_meta_36244.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c38182140400004085000238085000000100ffd5003fe5400ff55003fc54017fd4c05fe53017f54c05fc5300ffd0c03fe4300ff50c03fc43017fd4805fe52017f54805fc5200ffd0803fe4200ff50803fc42007fcc801fe32007f4c801fc32017fd4405fe51017f54405fc5100ffd0403fe4100ff50403fc41007fcc401fe31007f4c401fc31007fc8401fe21007f48401fc21017fd4005fe50017f54005fc5000ffd0003fe4000ff50003fc40007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x842003ff9421006ffaa10800ffc508400fffa042003ff9021003ff4810801ffd408400ffca042003ff10210007fe610800ffe3084001fe9842003ff0c210007fe410800ffe2084001fe9042003ff08210007fe2108003f71084001fd884200cffd9510065feca880037f65440013fb2a200cff99510015fcca88033fd65440197eb2a200cff19510015f8ca880337c65440053e32a200bffd911005dfec888003bf64440015fb22200bff9911000dfcc88802ffd64440177eb22200bff1911000df8c88802fbc64440035e322200bffd511005ffca88802ffd5444017fe2a22000ffd8d10005fec688003fe63440157f31a2000ff58d10005fac688003fc63440157e31a200cffd4d10067fca688033fd5344019fe29a200bffd0d1005ffc868802ffd4344017fe21a2000ffd8910005fec488003fe62440137f3122000ff58910005fac488003fc62440137e312200cffd4910067fca488033fd5244019fe292200bffd091005ffc848802ffd4244017fe2122000ffcc910007fc6488003fd3244001fe192200cffd4510067fca288033f65144019fea8a200cfd54510067f8a28802fff4144017ff20a200bff5051005ff88288003ff3144001ff18a2000ff4c510007f86288003ff2144001ff10a2000ff48510007f84288033ff5044019ff282200cff54110067f8a08802fff4044017ff202200bfe9011005ffa808802ff94044017fe2022000ffcc110007fc6088003fd3044001fe1822000ffc8110007fc4088003fd2044001fe1022000ffc4110007f62088003fe1044001fb0822003ffd9410035feca0801bfe65040057f3282006ff59410035faca0800ffc65040057e3282003ffd901002dfec808017fe64040037f3202005ff5901002dfac80800ffc64040037e3202005ffd501002ffca808017fd540400bfe2a02003ffd8c10005fec608003fe63040157f3182000ff58c10005fac60800ffc63040157e3182006ffd4c10037fca60801bfd530400dfe2982005ffd0c1002ffc8608017fd430400bfe2182003ffd8810005fec408003fe62040137f3102000ff58810005fac40800ffc62040137e3102006ffd4810037fca40801bfd520400dfe2902005ffd081002ffc8408017fd420400bfe2102000ffcc810007fc6408003fd3204001fe1902008bf98410037fea208013fe510400dfea882004ff1441002ffe8208013fe410400bfea082004ff10410007fe6208013fe3104001fe9882004ff0c410007fe4208013fe2104001fe9082004ff0841003dfcc00801bff5004007ff2802006ff5401001ff8a008017ff4004007ff2002005ff5001001ff88008003ff3004007ff1802000ff4c01001ff86008003ff2004007ff1002000ff4801001ff84008013ff1004001fb8802003ff84010007f42008003fd1004001fa8802000fe44010
  | 1 => 0xffd430801ffe2184009bf9882004ffea410027fe5208013fea904009ff1482004ffe8410027fe4208013fea104009ff1082004ffe6410027fe3208013fe9904009ff0c82001ffec210027fe61080017f3084009ff58420005fac21000ffc6108021ffa884010ff94420087faa210043fc510801fffa08400fff9042007ffa821003ffc4108001ff9884000ff8c420007fa6210003fc3108013ff9084009ff8842004ffa4210027fc21080237f3004010ffd402001ffca010043fd5008007fe280400fffd002001ffc801003ffd4008007fe2004000ffcc02001ffc6010003fd3008007fe1804009ffc802004fde401000ffe2008013fd1004009ff48020007da4010027f92008009ffb2e200ebfd9710077fccb8800afe65c401dfeb2e200ebf59710027f8cb8800afc65c4009ffb262008bfd9310047fcc988006fe64c4011feb262008bf59310027f8c988006fc64c4011ffaa62008ff95310047faa988023fc54c4009ffb1e2000bfd8f10007fcc78802afe63c4001feb1e2000bf58f10027f8c78802afc63c401dffa9e200eff94f10077faa78803bfc53c4011ffa1e2008ff90f10047fa8788023fc43c4009ffb162000bfd8b10007fcc588026fe62c4001feb162000bf58b10027f8c588026fc62c401dffa96200eff94b10077faa58803bfc52c4011ffa162008ff90b10047fa8588023fc42c4001ff9962000ff8cb10007fa6588003fc32c401dffa8e2004ff94710077eca38803bfd51c401dfaa8e2004ff14710047fe8388013fe41c4011fea0e2004ff10710007fe6388013fe31c4001fe98e2004ff0c710007fe4388013fe21c4001fe90e2004ff08710077fea18803bfe50c401dfea86200eff14310047fe8188023fe40c4011fea062008ff10310007fe6188003fe30c4001fe9862000ff0c310007fe4188003fe20c4001fe9062000ff0831001ffecb08036ff658401bff32c2002bf9961006ffacb08036fd6584007fe32c2002bf1961001ffec90801eff648400fff3242001bf9921003ffac90801efd6484007fe3242001bf1921003ffea90801ffe548400ffeaa42007ff1521001ffec708002ff6384001ff31c200abf98e10007fac708002fd6384007fe31c200abf18e1006ffea708037fe538401bfea9c200dff14e1003ffe870801ffe438400ffea1c2007ff10e1001ffec508002ff6284001ff3142009bf98a10007fac508002fd6284007fe3142009bf18a1006ffea508037fe528401bfea94200dff14a1003ffe850801ffe428400ffea142007ff10a10007fe6508003fe3284001fe9942000ff0ca1005dfac308037ff518401bff28c200dff5461006ff8a30801fff418400fff20c2007ff5061003ff88308003ff3184001ff18c2000ff4c610007f86308003ff2184001ff10c2000ff48610007f84308016fe608401bffa
  | 2 => 0x2001ff8cb1000afc6588007ffb244011bfd922008ffcc910006fe6488023feb244011bf5922001ff8c910006fc6488023ffaa44011ff9522008ffaa910047fc5488007ffb1c4000bfd8e20007fcc71002afe6388001feb1c4000bf58e2001ff8c71002afc6388029ffa9c4014ff94e200a7faa710053fc5388023ffa1c4011ff90e2008ffa8710047fc43880257eb144014ffd4a2004ffca510053fd5288013fe2944011ffd0a2004ffc8510047fd4288013fe2144000ffcca2004ffc6510003fd3288013fe1944003ffd8620007fcc310002fe6188001feb0c4000bf5862001ff8c310053ff5188029ff28c4014ff546200a7f8a310047ff4188023ff20c4011ff5062008ff88310003ff3188001ff18c4000ff4c620007f86310027ff2188001ff10c4000ff4862004ff84310026fe6088029ffa844003ff942200a7faa11000ffc5088023ffa044003ff9022008ffa811000ffc4088001ff9844003ff8c220007f46110003fd3088001fc9844003ff0c22004ffe4110003ef2088013fd9044013ffd952009dfeca900037f65480013fb2a4013ff99520015fcca9004ffd65480277eb2a4013ff19520015f8ca9004f7c65480053e32a4012ffd9120095fec89004bfe64480037f3224012ff59120095fac89004bfc64480037e3224012ffd5120097fca89004bfd5448025fe2a24000ffd8d20005fec690003df63480016fb1a4000ff98d20055fcc690003fd63480017eb1a4000ff18d20055f8c690003dc63480016e31a4013ffd4d2009ffca69004ffd5348027fe29a4012ffd0d20097fc869004bfd4348025fe21a4013ffd492004ffca49004fee5248027fea924013fb5492004ff8a49004bff4248013ff2124012fb90920097fa849004bed4248013fe2124000ffcc92004ffc6490003fd3248013fe1924000ffd8520005fec290003fe6148001feb0a4000ff18520005f8c29004fff5148027ff28a4013ff5452009ff8a29004bff4148025ff20a4012ff50520097f88290003ff3148001ff18a4000ff4c520007f86290027ff2148001ff10a4000ff4852004ff8429004fff5048027ff2824013ff5412009ff8a09004bff4048025ff2024012ff50120097f88090003ff3048001ff1824000fe8c120007fa6090003f93048001fe1824009ffc812004ff64090003fe2048001f71024003ffd942004dfeca10027fe65080057f3284009ff59420085faca1000ffc65080137e3284003ffd902004dfec810027fe64080037f3204009ef9902000d7cc810027fd640801f7eb204009ef590200057ac81000ffc64080137e320400fffd502007ffca81003ffd540801ffe2a04003ffd8c2004dfec610027fe63080157f3184009ff58c20005fac61000ffc63080137e3184010ffd4c20087fca610043fd5308021fe298400fffd0c2007ffc861003
  | 3 => 0xe292601affd09300d7fc849806bfd424c035fe212600affcc930007fc6498003fd324c015fe1926000ffd8530005fec298003fe614c001feb0a6000ff18530005f8c29806fff514c037ff28a601bff545300dff8a29806bff414c035ff20a601aff505300d7f8829802bff314c001ff18a6000ff4c530057f86298003ff214c001ff10a6000ff48530007f8429806fff504c037ff282601bff541300dff8a09806bff404c035ff202601aff501300d7f8809802bff304c015fd9826000ff8c130007bc609800fff650c0157fb28600aff99430015fcca1802bfd650c0317eb286003ff19430055f8ca1800fff640c0157fb20600aff9903000dfcc81802bfd640c02f7eb206003ff19030055f8c81805fff540c02fff2a06017ff550300bff8a81802afe630c015ffa98600aff94c30057faa61802bfc530c015ffa18600aff90c30057fa861802bfc430c007ffb10600aff9883004dfcc41802bfd620c0017eb106003ff188300c7fea418063fe520c031fea906018ff148300bffe841805ffe420c02ffea106017ff10830057fe641802bfe320c001ef190600aff4c830057f8641802bdc320c007ffb08600aff98430005fcc21802bfd610c0017eb086003ff184300c7fea218063fe510c031fea886018ff144300bffe821805ffe410c02ffea086017ff10430057fe621802bfe310c015fe988600aff0c430007fe4218003fe210c001fe9086000ff084300cdfcc018063ff500c007ff2806018ff5403001ff8a01805fff400c007ff2006017ff5003001ff8801802bff300c015ef9806003ff8c030057f4601802bfd300c001ee980600afe4c03004ffecb90026ff65c8013ff32e4002bf9972004ffacb9005afd65c8013fe32e4009bf1972004ffec990026ff64c8013ff3264001bf9932004ffac990056fd64c8013fe3264009bf193200affea990057fe54c802bfeaa64015ff1532004ffec790026ff63c8013ff31e400abf98f2004ffac790002fd63c8013fe31e4009bf18f200b7fea79005bfe53c802dfea9e4016ff14f200affe8790057fe43c802bfea1e4015ff10f2004ffea590027fe52c8013f72964009ff54b200b7daa590027fc52c8013ffa164009ff90b2004fdc8590027fd42c802bf6a164009ff10b2004ffe6590027fe32c8013fe9964009ff0cb2004ffec390027fe61c80017f30e4009ff58720005fac390027fc61c802dffa8e4016ff947200b7faa39005bfc51c802bffa0e4015ff907200affa8390057fc41c8001ff98e4000ff8c720007fa6390003fc31c8013ff90e4009ff8872004ffa4390027fc21c802dffa864016ff943200b7faa19005bfc50c802bffa064015ff903200affa8190057fc40c8001ff9864000ff8c320007fa6190003fc30c8007ffb2c4014bfd96200a7fccb1000afe6588029feb2c4014bf596
  | 4 => 0x827fd2108401f69084209fd48421027fec010827fe60084017f3004209ff58021005fac010813fc6008441ffa804220ff94021107faa010883fc500843fffa00421fff900210fffa801087ffc4008415ffb2e600abfd9730057fccb9800afe65cc015bf32e60029f99730057facb9807afd65cc015beb2e60009f59730057f8cb9802afc65cc015ffb26600abfd9330057fcc998006fe64cc015feb26601dbf59330057f8c99802afc64cc03bffaa6601dff953300effaa998077fc54cc015ffa9e600aff94f30057bca79802bfd53cc03deea9e600aff14f30057fe879802bfe43cc015fea1e600aff10f30057fec59802bfe62cc0137f316600aff58b30005fac59802bfc62cc03dffa96601eff94b300f7faa59807bfc52cc03bffa16601dff90b300effa8598077fc42cc015ff996600aff8cb30057fa659802bfc32cc015ffb0e600aff98730005fcc39802bfd61cc0017eb0e600aff187300f7fea39807bfe51cc03dfea8e601eff147300effe8398077fe41cc03bfea0e601dff10730057fe639802bfe31cc015fe98e600aff0c730007fe4398003fe21cc001fe90e6000ff087300f7fea19807bfe50cc03dfea86601eff143300effe8198077fe40cc03bfea06601dff1033001ffecb18072ff658c039ff32c6002bf996300e7facb18072fd658c007fe32c6002bf1963001ffec918066ff648c033ff3246001bf992300cffac918066fd648c007fe3246001bf192300cffea918067fe548c033feaa46019ff152300d5fac718073ff538c015ff29c601cff54e30057f8a718067ff438c015ff21c6019ff50e30057f8871800fff628c001ff3146009bf98a30007fac518002fd628c007fe314601cffd4a300e7fca518073fd528c039fe2946019ffd0a300cffc8518067fd428c033fe214600affcca30007fc6518003de328c001fe994600aff0ca30007b8651800fff618c001ff30c6000bf98630007fac318002fd618c007fe30c601cffd46300e7fca318073fd518c039fe28c6019ffd06300cffc8318067fd418c033fe20c600affcc630007fc6318003fd318c015fe18c6000ffc8630007fc4318003fd218c001fe10c600abf982300e7fea11800ffe508c039fea846003ff142300cffe811800ffe408c033fea046003ff10230057fe6118003df308c015fd984601bffd95300ddfeca9806ffe654c0057f32a601bff595300ddfaca9806ffc654c0057e32a601affd91300d5fec89806bfe644c0037f322601aff591300d5fac89806bfc644c0037e322601affd51300d7fca89806bfd544c035fe2a2601bffd4d30057fca69806fde534c037fea9a601bf754d30057f8a69806bff434c015ff21a601aff50d30057f88698003ff624c0017fb126000ff98930007fac498003fc624c0137e312601bffd49300dffca49806ffd524c037f
  | 5 => 0x922110ffac910886fd6488409fe3244201bf1922110ffea910887fe5488443feaa44221ff15221027fec710802ff6388401ff31c420abf98e21007fac710802fd6388409fe31c420abf18e21127fea710893fe5388449fea9c4224ff14e2110ffe8710887fe4388443fea1c4221ff10e21115fac510893ff5288413ff2944224ff54a2104ff8a510887ff4288413ff2144221ff50a2104ff88510803ff3288401f79944209ff8ca21007fa6510827fc3288401f61944209bf98621127fea310813fe5188449fea8c4204ff1462110ffe8310813fe4188443fea0c4204ff10621007fe6310813fe3188401fb18c4200ff4c621007ea6310813fc3188413ff90c4200fbc862104fee4310813ff6088401ff3044200bf98221007fac110802fd6088409fe3044224ffd4221127fca110893fd5088449fe2844221ffd022110ffc8110887fd4088443fe2044223ffd952111dfeca9088ffe65484057f32a4223ff5952111dfaca9088ffc65484057e32a4222ffd9121115fec89088bfe64484037f3224222ff59121115fac89088bfc64484037e3224222ffd5121117fca89088bfd5448445fe2a24200ffd8d21005fec690803fe63484157f31a4200ff58d21005fac690803fc63484157e31a4223ffd4d2111ffca69088ffd5348447fe29a4222ffd0d21117fc869088bfd4348445fe21a4223ffd492104ffca49088ffd5248413fe2924222ffd092104ffc849088bee4248445fea124222fb5092104ff88490803ff3248413ff1924200ff4c92104ff8649088fff5148447ff28a4223ff5452111ff8a29088bff4148445ff20a4222ff50521117f88290803ff3148401ff18a4200fd8c521007fa6290803f53148401fe18a4209ffc852104fee4290803fe2148401f710a4200ffd8121005fec090803fe6048401feb024200ff18121005f8c09088fff5048447ff2824223ff5412111ff8a09088bff4048445ff2024222ff50121117f88090813ff65084137fb284209ff99421015fcca10827fd65084417eb284204ff1942104df8ca10813ff64084137fb204209ff9902100dfcc810827fd640843f7eb204204ff1902104df8c81087fff540843fff2a0421fff550210fff8a810813ff63084137fb184209ff98c21055fcc610827fd63084017eb184204ff18c2104df8c610883ff5308441ff2984220ff54c21107f8a61087fff430843fff218421fff50c210fff88610826fe6208413ffa904209ff9482104ffaa410827fc5208413ffa104209ff9082104ffa8410827fc4208413ff9904200fbcc82104ffc6410827fd3208413fe1904209fb0c82110dfcc210883ff5108409ff2884220ff54421027f8a21087fff4108409ff208421fff50421027f88210803ff3108409ff1884200ff4c421027f86210827ff2108413f79084204ff8842104fec4210
  | 6 => 0x5fe21a6200ffd8931005fec498803ef624c40177b126200ff98931007fac498803fc624c4137e3126200fb18931005d8c4988afff524c457ff292622bff5493115ff8a4988abff424c455ff212622aff50931157f8849882bff324c401ff1926200ff4c931057f864988afff514c457ff28a622bff5453115ff8a2988abff414c455ff20a622aff50531157f8829882bff314c415fb98a6200ff8c531007bc6298803ff604c4017fb026200ff98131007fac098803fc604c4017e302622bffd413115ffca0988affd504c457fe282622affd0131157fc80988abfd404c455fe2026204ffd9431055feca1882bfe650c4057f328620adf99431014fcca1882bfd650c4517eb28620adf59431004faca18813fc650c4157e3286204ffd9031055fec81882bfe640c4037f320620aff5903113dfac818813fc640c4157e3206227ffd503113ffca81889ffd540c44ffe2a0620abf98c31057fea61882bfe530c415fea98620aff14c31057fe861882bfe430c415fea18620aff10c31027fec41882bfe620c4137f310620aff58831005fac418813fc620c451ffa906228ff94831147faa4188a3fc520c44fffa106227ff9083113ffa841889ffc420c415ff990620aff8c831057fa641882bfc320c4537f3086228ffd4431027fca2188a3fd510c409fe2886227ffd0431027fc821889ffd410c409fe208620affcc431057be6218813fe310c415fb188620aff4c431007ba621882bf5310c409ffb00620aff98031005fcc01882bfd600c4017eb006204ff18031147fea0188a3fe500c451fea806228ff1403113ffe801889ffe400c44ffea006227ff1003104ffecb90826ff65c8413ff32e4202bf9972104ffacb9089afd65c8413fe32e4209bf1972104ffec990826ff64c8413ff3264201bf9932104f7cc990806be64c8413feb264225bf5932104f7ac990802bd64c8413fe3264209bf1932112ffea990897fe54c844bfeaa64225ff1532104ffec790826ff63c8413ff31e420abf98f2104ffac790802fd63c8413fe31e4209bf18f21137fea79089bfe53c844dfea9e4226ff14f2112ffe8790897fe43c844bfea1e4225ff10f2104ffea590827fe52c8413fea964209ff14b2104ffe8590827fe42c8413f72164209ff50b2112fda8590827fc42c8413ff9964209ff8cb2104ffa6590827fc32c844dffa8e4226ff94721137faa39089bfc51c844bffa0e4225ff9072112ffa8390897fc41c8401ff98e4200ff8c721007fa6390803fc31c8413ffb064209ff98321005fcc190827fd60c84017eb064209ff18321137fea19089bfe50c844dfea864226ff1432112ffe8190897fe40c844bfea064225ff10321027fecb10892ff6588449ff32c4202bf99621127facb10892fd6588409fe32c4202bf19621027fec910886ff6488443ff3244201bf9
  | 7 => 0x19027fe320c813f71906409ff4c83204fba641902bed320c813ffb086409ff98432005fcc219027f6610c8017b3086409ff58432005fac219027f5610c8017ab086409ff18432187fea2190c3fe510c861fea886430ff1443217ffe82190bffe410c85ffea08642fff1043204ffec019027fe600c8017f3006409fe98032005f4c019027fd600c8017eb006409fe58032005f2c019027fc600c861ffa806430ff94032187faa0190c3fc500c85fffa00642fff9003217ffa80190bffc400c815ffb2e620abfd9731057fccb9880afe65cc415feb2e622ebf59731057f8cb9882afc65cc415ffb26620abfd9331057fcc998806fe64cc415feb26622dbf59331057f8c99882afc64cc45bffaa6622dff9533116ffaa9988b7fc54cc415ffa9e620aff94f31057bca79882bfd53cc45deea9e620aff14f31057fe879882bfe43cc415ef21e620aff50f3116fba879882bfc43cc415ffb16620aff98b3104dfcc59882bfd62cc4017eb16620aff18b31177fea5988bbfe52cc45dfea96622eff14b3116ffe85988b7fe42cc45bfea16622dff10b31057fe659882bfe32cc415fe996620aff0cb31177fea3988bbfe51cc45dfea8e622eff1473116ffe83988b7fe41cc45bfea0e622dff10731057fec19882bfe60cc4017f306620aff58331005fac19882bfc60cc45dffa86622eff94331177faa1988bbfc50cc45bffa06622dff9033116ffa81988b7fc40cc409ffb2c622cbfd9631167fccb1880afe658c459feb2c622cbf59631027f8cb1880afc658c409ffb246229bfd923114ffcc918806fe648c453feb246229bf59231027f8c918806fc648c453ffaa46229ff9523114ffaa9188a7fc548c4557eb1c622cffd4e31057fca7188b3fd538c415fe29c6229ffd0e31057fc87188a7fd438c415fe21c6204ffd8a31007fcc518826fe628c401feb146200bf58a31027f8c5188b3ff528c459ff294622cff54a31167f8a5188a7ff428c453ff2146229ff50a3114ff8851882bff328c401ff1946200ff4ca31057f8651882afe618c459ffa8c6204ff94631167faa318813fc518c453ffa0c6204ff9063114ffa8318813fc418c415ff98c6200f7cc631057ee6318813ff608c401ff3046200bf98231007fac118802fd608c409fe304622cffd4231167fca1188b3fd508c459fe2846229ffd023114ffc81188a7fd408c453fe204622bffd953115dfeca988affe654c4057f32a622bff5953115dfaca988affc654c4057e32a622affd9131155fec898803bf644c4015fb22622aff9913100dfcc8988abfd644c4557eb22622aff1913100df8c8988abbc644c4035e322622affd5131157fca8988abfd544c455fe2a2622bffd4d31057fca6988afde534c457fea9a622bf754d31057f8a6988abff434c415ff21a622af790d31157fa86988abdd434c41
  | 8 => 0xf50b321afda8599027fc42cc815ffb0e640aff98732005fcc39902bfd61cc8017eb0e640aff187321b7fea3990dbfe51cc86dfea8e6436ff147321affe83990d7fe41cc86bfea0e6435ff10732057fec19902bfe60cc8017f306640aff58332005fac19902bfc60cc86dffa866436ff943321b7faa1990dbfc50cc86bffa066435ff903321affa81990d7fc40cc813ffb2c6409bfd963204ffccb1900afe658c813feb2c6434bf5963204ff8cb19026fc658c813ffb246409bfd923204ffcc919006fe648c813feb246433bf5923204ff8c919026fc648c867ffaa46433ff9523219ffaa9190cffc548c8637eb1c6434ffd4e32057fca7190d3de538c869fea9c6434f754e32057f8a7190cfff438c815ff21c6433ff50e32057f88719026fe628c813ffa946409ff94a3204ffaa519027fc528c813ffa146409ff90a3204ffa8519027fc428c813ff9946409f7cca32057de6519027ff618c813ff30c6400bf9863204ffac319002fd618c813fe30c6434ffd46321a7fca3190d3fd518c869fe28c6433ffd063219ffc83190cffd418c867fe20c6409ffd823204ffcc119002fe608c813feb046400bf5823204ff8c1190d3ff508c869ff2846434ff542321a7f8a1190cfff408c867ff2046433ff5023219ff881190cbff654c8657fb2a6432ff99532015fcca990cbfd654c8657eb2a6432ff19532015f8ca990c7ff644c8637fb226431ff9913200dfcc8990c7fd644c8637eb226431ff1913200df8c8990c7ff544c863ff2a26431ff5513218ff8a8990cbff534c815ff29a6432ff54d32057f8a6990c7ff434c815ff21a6431ff50d32057f886990cbff524c813ff2926432ff5493204ff8a4990c7ff424c813ff2126431ff5093204ff8849902bff324c815f79926409ff8c93204fbc6499003ff614c8017fb0a6400ff98532007fac299003fc614c8017e30a6432ffd4532197fca2990cbfd514c865fe28a6431ffd053218ffc82990c7fd414c863fe20a6400ffd8132005fec099003fe604c801feb026400ff18132005f8c0990cbff504c865ff2826432ff54132197f8a0990c7ff404c863ff2026431ff5013218ff88099027ff650c8137fb286409ff99432015fcca190277e650c8053f3286409ff59432185faca190277d650c8013eb286409ff1943204df8ca19027ff640c8137fb206409ff9903200dfcc819027be640c8035f3206409ff5903217dfac819027bd640c8015eb206409ff1903204df8c8190bfff540c85fff2a0642fff5503217ff8a81902afe630c815ffa98640aff94c32057bca61902bfd530c861eea98640aff14c32057fe861902bfe430c815fea18640aff10c3204dfcc419027ff520c813ff2906409ff5483204ff8a419027ff420c813ff2106409fb9083204ffa84190bfed420c813fe2106409ffcc83204fbe64
  | 9 => 0x400100300000400000001100000300500800700400000000100000900000000200100900400000600200100000200200000100400900200800600300800400200000900f00500000000200200001200100400200300200000200300401400b01000100000000000100000000800000100000500100000200100200000200200100000200300200100000200200500200900000b00000100000000100d00600000400400000900300002000000000100300100300100000000500f03300100500003200d00000001200100000000000200000200300000100100001e00500100200400900b00800000000b00000a00100400000000200700100200100200200000200301100100700000700000000300500100300500100000200200300400000100000b00d00100a00300100000100200601000500b00300100100400000001100f00300200600000500101d00200000000300000301300000400002d00000000000000f00300000000600300200300900100100100400200000300100200900100000300200001600a00100000900600000000200000400400100d00000001500000200000400001500000000000900500400d00300700600800400200b00800400300500000400200000100100500000100201600101100100700200000100f00300300000900000d01200900900300000100400400d00000300401900200200000100300a00000000300001800000300400500000000100100400000100300000400100e00100900000000600300800500800700000100b00100200400000200000a00000100300300002000300000000000101300000300a00300000100100200200800103e00400700000000500000200000000a00700100600200100100000300100601200000000200800000001200a00400200100400000800b00900c00400400300401400101200100000500801200200000500c00000000100200000200400500100200100100000300200400f00100300101a00001700400e00000900700000200000300200200300200000200000100000000b00300500300100400300000100001900000000300400400100b00000300300000000100100301e00800400300200100200000200100200100000000000000300400000d004002001000008000001004003000005006006000003006001008008001001057fecb9902aff65cc815ff32e6402bf99732057facb990dafd65cc815fe32e640abf19732057fec99902aff64cc815ff3266401bf99332057fac9990d6fd64cc815fe326640abf193321affea9990d7fe54cc86bfeaa66435ff15332057fea79902bfe53cc815fea9e640aff14f32057fe879902bfe43cc815fea1e640aff10f321b7fea599027fe52cc86dfea966409ff14b321affe8599027fe42cc86bf72166435f
  | 10 => 0xa720000000007fe00000000000029000038e000000000c089602e8816a58000b58300eb00d81f2000b2af14eeaabc7e6f12eb64d6836962bd090c466ea0a1a2644d2be41aaa288e05147a818a26e000d84b96000b88e8436a0003c6772bfe9a47143a81de2ec6662f4a624faa7a1e8ca27366e8434822bb88ca9e2000cf4dc889609e2fe000000a1e39c000d645ac000c300000000000000000000003601ae8b40000dab7c000000038aa80000000005ee04800098ce04000000000bf0c64d080ee2268aa0000688982b200062e88a24a0b8000000c1ac901d44a60000002de000722000e6c6b82a2a3e000a86000a7c000000240a06f541f078e000000000a48000b0e522342ee4e06e189b8668a268d2c70c66e5230e14e000f8042280e84800050aee6368d98216000bc25cadf6000000d5c0006926f6542000da6dcc000596f86000e64742000b82bdeaea0005bc00076ed4e15a686ba6380c0a1e24eead827a51a6c82e6000e2a97e3d8208000000000abe1401a2458a16f6c0006fa402000000370e4aa30042000fc023635a4da00000000000074ed8e6b2372f18314f46cce744bb46aa1fefb0ca400013804454400000093096a5f44bc8ee8c4650000000cfe7c41b43e4d723dafa600028c554000b02000e584800ce4763ae7a40000001ce0e84a20009da0008a2000b84000000b72000a00322196a96e32cb6e7ae88ea883e00000000016e75033c93c93268424e94e16267a274fbe000dea000e0c26c6ec07cae06d0bd82504e038a7ba386446f5e2005f600047cd62790958f200003b6000654d34000098f08e7e00060873c44e45c9b4000000000afc3b2000fbabf81604241260005c06e257c000000000000858d20c3a000000000000ebaaa6a88afa000fc65a6464ec8000000fb61c44cc0000001122a65747f8d8ab089ac2b8808e1aaf05b2eeec8e9f24863a040e98075c3c218ce60f9c1cacfac6e832a840fc9c2000d66332c5c00005ed3ae86f666c44fcdce3f000a52808cc10f24dd89fc93ee9c00066e29cc9448e0e4000338ed454e6eaeca00071cfd00000b0000af40b6000204662000d261ea90a8a6000000ddc000000000b18000b36020956000000000710eb2b7644c10ca20000ac200011876c04c0000008ae000362230f5a42c000ba08be0000001a4e8e2860000000000004000008e26dc00000000000000000000000300300000300500e00600100000300000101a00700000f00500100000100500400000900600e00000500300000800000000400000300100900400100000201500000000b00b00000400302000300100000001000e00300000700000000200300100000100000000500200100600a00000400800000a0020000030000030000090040000010040000020000000020070000050040010000010
  | 11 => 0x29263812ea022c442e12aa6c0a471e17803046a65c00034e84c5ec092256ab611ce28f2c000c9c412000a0492c000000000000000760000f82000340000000000000000000d9af1c6f24920005349b0468986000000000000000ce80000d6b483f4746000000d7473a0005feebc000000000000f90000a5c00000000096e000000b640cc00000020a6180000003dc000000ada00009a246aaa17ebfaa32258c28ad094600057e95c4deb3e788000ed0000b86e148f069637441855a8505d6000ea206c000bbcbb20000800000f0cc2c92000000000000000934000000bd4716000000452560b56000e62000f52e8cf38000b78000000000bea41ccf07a00000006b6000da400000000000000014c5ba0006c697400000028a000000000eb400062c1ec4f8000a646f001258c000de0000a4651c028f10f3219497860ebc82bac2cbbe000b6c00068cbb0000c182e0b20a22000770ae20007ae0008f2000d6aed6364000614dd4c78000b42d2400021a000540000000000000afe1ac0be43a4043a22785ce000000000b941da23c2880000004720003c82aa9d4000000000d9e0000007c05c866cecc536ceccb064211631c3bea0c7c6066ef8000a6a0a0bfc382072348c34e5c99296c0006c0e0e4fef920c6912af21b0b0a1ba052000734c588fa556df44787e0ef45f0e5e000e76c440000000009e0aec9ee0009d600021e0007f0000f0231e0006c2328d4c00003e0009143ca000496000682000a94c740009facd0448aa4d4613eaf60000008fc000000000004000000000000000024000ac6000000000450000b3c00060aa4c6527dc0a2c40c8c99aa10dc6a52482a76d9ce90a4028222acac954b9e13050000000058ed0600000012c1eeb320008849e4700000ee0058fa4284dfcbcca240007c8000000b5e9ea8547bc3943bc000adc000ef000000000086af1ed7636600058400051e40c488d54410000000000846000f4c45ef6a00000000000000075a0000004d4144be80000004d000000083476a2200000000000005e857a1c8000e16000f840007988680003ee2be180a9e3feb7006a000b160000009f8578d96000e820000009c4bc6aa09ae4303362ac49a04e940e00b062d6c867eafaa6e6c4c0829067080000005b000000000072600063c0009521360005a4014000000000966944c88000894000c5e8ecd58e40fbc72a0001d800098800000032a1fa7d689e000000000e660006a01460002f2000d700006d67d0000764000000a0a000346000c000000006caaca00049c0002a00003561c200085afb8a121b8e4c83088e5206ac408000198f50000e427304ae8183306603f8fc4cbc9de016508e4e766facda081cd9470c3266a2bf67848380000000000000000005aa000000000c72000680000e54cd4e10000262eac0003faf3000
  | 12 => 0x2e548f2a00090ee2046c0007d8000b7a63289a40a0008f41f498e7e8a140325f800017ad40db27b65b6e3ed80398182e704eca2af64a56234800ad46248609108cc904ebe69e1e0cf236ca8ebf4d0a25e7b00003901fcf4089cd1aa5a9428e6000000000d904ce000cc600000079c6ae43c1ccbae8f653a4e235810a6045fa0000009c6000000000000050ec25c29fe0000c4000000000000d00bce0001b200059200033a000000000000ba4000b60c7ab280f25da9f0b9288c8f80ea9d83d024c9940ca0000000002609be000000320f7a00052e0008b6e9e7a2edc270c0c0ba86608e4c40561e6de84547f6b1a48cd7a0007b2c26becceef1aa1c4ea712000cd8fce55ee94948242000670000f6000000000035e7fcf3cd3243eb4e6460000005f2000132cb270400000000000039e5020008645d4000dda12462a8e49baa4a000000000000000baccb8810b9cb1c0dc72868a91ab2600016a00018867872c996d28dbe826a784dcb522d849465a5b88ace48c7656e4f40026d859af482dc07e2c211af9a7c2e227ccb3a2101dc612c622cc6a85de442000bd69ca73ef22474dae30619e000dc2176d16a0ea388b20000000e02ae00000000034ade637a000558ce0d30000e503d455094a000adec3cf8c3104a4000000000000b8c000000000a8a00000000091c094e021044beea406e606658e8a000d7e6ee000000e268d6ae4b62254000122000c5a7f226a7186225cc000876428ae84f2d5af3a740084b6e000dd01a03b0eb8000b300007de000000148000000df0aceccc7520006daf763d600060c9f6fd6f26598c36000602d2200020250c530312000dd6484f98000d443e6a2e000000814000cc01148746bcb38e44000ce438c7cabe638830ad8c73813afaea822e20d48822b4db892ed0c2a8e12c041845880006a469a4b4d820003b800014a99c0008a4da82ea17c0000003b4000000000302cfc294000000000000c4ee7c4ba0008127b864a086d10fa00000009ce6e0c6c00045a0e600022c9ec0002380feb4c880da227e0009a62f659456a7ac8202ee85ec52000000000a54000000000000efa0001c60c80004e42663961d66402f85e6438aee2067249f4ef62d0000d681f6000ac4c48b24f5c6d299ea080c00003aa334deef705e20009aa000cd683c34446ea2c5ae85c49874abe0caa28e00029aaac000ec636ecd26f82327d2990000e960003e0e6800084487e61e000074e72be201c3c4000582000000706dc0134a9ac960006cc0008ce0005760000005a083a53e6fc6486340000000000000000f4000000000a7ebb6b6650ec82000000e24000000dde532dc400016c87c4b00000001bc66acdc000c129380000fa00000092a35279679ac68d2a0007be0000007801d0c1e000564000f4e54cb5c01e8ea67e1d2ab2c2033e460
  | 13 => 0x6d18efef0e6984c20ae68800002a0f6414218376b1e00e0008d80004322ce456998106000354bd23ce0000007ee84e6647e46260000000000b4a6e12800000000029e000000000fb4000f0453cf6879ea68000a92000748000970cda00098af9e762000156baab5a00088600072ec160003506b03de48af78fd2b9a000000000212000d6c25ca3a0648c20000000004f63f6c2ee2e21c000a98000b0c00000000000000000025247e000dba000510a5e2fcdaa5b4ee80a837cc7c8560009b2078000936892eaa0000008880009c800082a67c05adacf0c000000d1200095eab847a000000ba8000a7400000000000000091eeae272000e3600000010081a2b0d140005c4f28000000b80000b50a8cca0ef20003ba0002b60009c0000102c56758ce2d420000009e8e6e30421400055ce78c420009205d80464e656c166152df27fa75e3ec172a3c524f16b2eae659ef724620620000006de908000a6637e0000000003f2000fca8da7cee74cb4000000676f74b00f00000d4850449e000088000d4a000950672000f42f8a000000ccac3e9bcb7400078c2e413c0000000004ca23e0000ac4442fa000ece000610000bbab34000e6a620e922d295aee241e4a080a054000190bca87244a3a492200064ed3e07a1a6ce62988b00000000180007024aa000000fa20009cce1e000de20008a07f4512dfa3d200000065600000097a7ece3c318000d2c000000000384ede3c05660005dc1f8924af8000000870000000d5272000000000000002e02600000000056800000000000000000000004011eabad867540000000008c6000f3e0001a82c0b8efcc6f4d1c4ac00cdb48c0d041bef34ab0e983e8000c32c4a9d2cf65160000008c80000000004e8a4e82e31a00000070a0b200000032c61aa700ded92f948a8c24a42b4a0000bc090c9a890d88000dfee5610e526000006e305a2b6ad7863a61cf4a0000009e6000000000000d02dbccf8ea6ed8824000000d561586ce0005d28fe0005060000000003a6000f56d6ec600ecf7c0e2e9af06000000774a60acc4b83ccc7e186036000bc439a2c62280a60000762220008dee0800000078603c8d0000538000806cbe90087a4209d0a5000020e70e00065e000000392e38000cde416000b10000de4000f629a8f58000000a3600000000000082c000000590d5eefc00047034c690378000c068d400000000015c97c000000d2e00005c87852cb444c8000000224248000000852c020009a0c3800012000019c0000005e41b6000b46d7cad2fd4972d0e54600001a2c81680704b271a7aa000beecea4a857000081e9dc00000017415430c0000000005e032469c840cc48bcfb2644436000000010bdc000000000000628000f968627780000000000000008dc0000009160aa000902000bc09180f85520000002
  | 14 => 0x7562a4ca86fe49019a00002274c02c600316ab459c802ec05c6c50f2edca1500000007d4f8e3ea2caf0a000df8000db60000009683e2e2c308b12804000000580e46406000d38c46000c9e000000000000c54000d1e1c0d50e5a000000ec46a6000000732000b8ab14000000562296000000fc894c0001421100006be00000093a0002bc00032eb7eaa2c0e79400000025a0d064c674000f8800054abf2b0400009c776000000060ac000000042a0000008428b89a2c8ae34000000000000000000000000518636fa8000f7e00000000052aca600078a23aad68ba0000002680000000000005866164b6000b22bda86e28000000000041a4c6fc2984c80000cc84f04d8000f4400058a170aae0000d2000ac8244000000c1c5d05fcc14eec000000000c2200003a164000cae0966b418e00077c768dd21e4976c9800086c68e2d4000000a90000000cba9265ea00077e0008e86ba6d4192a183ac7928286303fced200063e9b684a5be35c000000000f36e1c000000b68d3c000a80000b900002f0e0a426e801080007b45725a8000000000a9c928782000b540000002766e4a4477ac6aba204af6e0c2d600007e2964db008a440b2c7da008c2a20c15ee3ac84000034a3480cdec694b984c0982000b40000eda7a627c2dad3
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xd7558c10014fc7558c10004ff7458c1000cfe7458c10004fd7458c1000cfc7458c1001cff7358c1001edf7358c10006de5358c10006dd5358c10006de4358c10006dd4358c10004ff7258c1004cfc7258c10054ff7158c10024fe7158c10054fd7158c10024fc7158c10026de3158c10026dc3158c10054ff7058c1001cfe7058c10054fd7058c1001cfc7058c1001ede3058c1001edc3058c1001cff75d8810014fe75d8810004fd75d881001cfc75d881001cff74d881000cfe74d8810004fd74d881001cfc74d8810054fe73d8810004fd73d8810024fe71d881001ef671d881001cfe70d881001efa70d8810004fd769881001eef629881001eec629881004cff765881001eec6258810004ff7558810014fe7558810004fd7558810014fc7558810004ff745881000cfe7458810004fd745881000cfc7458810004ff7358810054fc735881001cff725881001eef7258810006ee5258810006ed5258810006ee4258810006ed425881004cff7158810024fe715881004cfd7158810024fc7158810026ee2158810026ec215881004cff705881001cfe705881004cfd705881001cfc705881001eee205881001eec2058810054ff76cc81001cfe76cc810004fd76cc81001cfc76cc810056de63cc810006dd63cc81004cff768c81001cfe768c810004fd768c81001cfc768c81004eee628c810006ed628c810004ff764c81001cfe764c810004fd764c81001cfc764c810056de634c810006dd634c81004eee624c810006ed624c81004cff760c81001cfe760c810004fd760c81001cfc760c8100357e750c8100057d750c81002dbe740c810005bd740c810025f6710c810005f5710c81001dfa700c810005f9700c810004fd76cc410004ff764c410005bf744c41002dbc744c410005ef724c410005ec724c410004fd76c841002dbe74c8410005bd74c8410004ff7648410004fd76cc0100357e75cc0100057d75cc010004ff764c010004fd76c8010004ff76480100057f75480100357c7548010005df7348010005dc7348010026f576c401001ef765c40101d6f565c401001df570c401001ef660c401001df9768401001ef9768401004cf9768401001efb64840101cef96484010025f97184010026fa618401001ff26184010004ff76440100057f75440100357c7544010005bf744401002dbc744401001df77644010006f77644010004f776440100077775440101c774754401001ef765440101c6f56544010007b774440101bfb4744401001df7704401001ef6604401001ff23044010007f13044010025fb7644010006fb7644010004fb76440100077b75440101c7787544010007bb74440101bfb87444010026fb64440101bef9644401001dfb714401001ff37144010026fa6144010027f26144010027f23144010007f13144010
  | 1 => 0xc510054fc764c5100067f654c51015e7c654c510005bf744c51005dbc744c510006bf644c510156bc644c510006df634c510056dc634c510005ef724c510005ec724c510005fb704c510005f8704c510004fe760c5100657e750c5100057d750c5100067f650c5101467c650c510006bf640c51013ebc640c510007d5310c510004fe76c851001cfc76c85100067f65c85101367c65c851005dbe74c8510005bd74c8510006bf64c851012ebc64c8510006ef62c851004eec62c8510005fa70c8510005f970c8510004fe76885100067f65885101267c6588510006bf648851010ebc648851004cfc76485100067f654851011e7c6548510006bf6448510116bc6448510006ef624851004eec6248510005fb7048510005f87048510004fe76085100067f65085101067c6508510006bf64085100febc6408510004fe76cc110024fc76cc1100657e75cc1100057d75cc1100067f65cc1100f67c65cc110006bf64cc1100eebc64cc110006df63cc110056dc63cc110005f671cc110005f571cc110004fe768c1100067f658c1100e67c658c110006bf648c1100cebc648c110054ff764c110004fd764c110054fc764c1100067f654c1100de7c654c110006bf644c1100d6bc644c110006df634c110056dc634c110005f7714c110005f4714c110004fe760c1100067f650c1100c67c650c110006bf640c1100bebc640c110004fe76c8110024fc76c81100067f65c81100b67c65c8110006bf64c81100aebc64c8110006ef62c811004eec62c8110005f671c8110005f571c8110004fe76881100067f65881100a67c6588110006bf648811008ebc648811004cff7648110004fd764811004cfc76481100057f75481100657c75481100067f654811009e7c6548110006bf6448110096bc6448110005df7348110005dc7348110006ef624811004eec6248110005f77148110005f47148110004fe76081100067f65081100867c650811005dbe7408110005bd7408110006bf640811007ebc6408110007e920081100067f65c41100767c65c4110006bf64c4110046bc64c41100077b65c41101f77865c4110025fb74c4110205f974c4110007bb64c41101ffb864c4110027f251c41101f7f151c41100067f658411006e7c6584110006bf648411003ebc648411005df6768411001df775841101edf575841100077765841101e7746584110007b764841101dfb46484110007f3608411001ff240841101dff1408411001cff75d8c10014fe75d8c10004fd75d8c1001cfc75d8c1001cff74d8c1000cfe74d8c10004fd74d8c1001cfc74d8c1004cfe72d8c10004fd72d8c10024fe71d8c1001ef671d8c1001cfe70d8c1001efa70d8c10004fd7698c1001edf6398c1001edc6398c10054ff7658c1001edc6358c10004ff7558c10014fe7558c10004f
  | 2 => 0x47f7558d10014fe7558d10004fd7558d10014fc7558d100067c7558d100147c7558d10004ff7458d10006bf7458d10004bf7458d1000cfe7458d10004fd7458d1000cfc7458d10006bc7458d1000cbc7458d10006df7358d10006de5358d10006dd5358d10004ff7258d10006ef7258d10004ef7258d1004cfc7258d10006ec7258d1004cec7258d10004ff7158d10006f77158d10004ff7058d10006fb7058d10004fe7618d100067f6518d100067c6518d10006bf6418d10006bc6418d10056de6318d10006dd6318d1004cfe76d89100067f65d89100067c65d8910006bf64d8910006bc64d8910004ff75d8910014fe75d8910004fd75d8910014fc75d8910004ff74d891000cfe74d8910004fd74d891000cfc74d8910054fe73d8910004fd73d8910024fe71d8910024fc71d891001cfe70d891001cfc70d89100657e75989100057d75989100067f65989100067c659891005dbe7498910005bd7498910006bf6498910006bc6498910006ef62989100057f75589100657c75589100067f65589100067c6558910005bf745891005dbc7458910006bf6458910006bc6458910005df7358910005dc7358910004ff75589100067f75589100047f7558910014fe7558910004fd7558910014fc75589100067c75589100147c7558910004ff7458910006bf7458910004bf745891000cfe7458910004fd745891000cfc7458910006bc745891000cbc7458910004ff7358910006df7358910004df7358910054fc7358910006dc7358910054dc7358910006ef7258910006ee4258910006ed4258910004ff7158910006f77158910004ff7058910006fb7058910004fe76189100067f65189100067c6518910006bf6418910006bc641891004eee6218910006ed6218910054ff76cc910004fe76cc910004fd76cc910054fc76cc9100067f65cc9101b67c65cc910006bf64cc9101aebc64cc910006ef62cc91004eec62cc91004cff768c910004fe768c910004fd768c91004cfc768c9100067f658c9101a67c658c910006bf648c91019ebc648c910006df638c910056dc638c910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c9101967c654c910006bf644c91018ebc644c91004cff760c910004fe760c910004fd760c91004cfc760c9100657e750c9100057d750c9100067f650c9101867c650c91005dbe740c910005bd740c910006bf640c91017ebc640c910006df630c910056dc630c910006ef620c91004eec620c910005f6710c910005f5710c910005fa700c910005f9700c910004fe76cc51001cfc76cc5100067f65cc5101767c65cc510006bf64cc51016ebc64cc510006df63cc510056dc63cc510005fa70cc510005f970cc510004fe768c5100067f658c5101667c658c510006bf648c51014ebc648
  | 3 => 0x8704c61006d7e750c6100057d750c61003dbe74c8610005bd74c861004eee62c8610006ed62c861001dfa70c8610005f970c861004cff764861004eee6248610006ed6248610005fb704861001df8704861006d7e75cc2100057d75cc2100057f754821006d7c7548210005df7348210005dc734821001fe8204821001df576c4210006f576c421001ef765c4210216f565c4210005f976c4210026f976c4210025fb74c421020df974c42100657e76d95100667e76d95100147e76d95100067f64d95100067e64d95100067d64d95100067c64d95100073c64d95100063c64d95100077771d95100677471d95100077a40d95100077940d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067e42d95100067d42d95100067c42d95100067f71d95100667e71d95100667d71d95100667c71d95100067f41d95100067e41d95100067d41d95100067c41d95100067f70d95100667e70d95100667d70d95100667c70d95100067f40d95100067e40d95100067d40d95100067c40d95100667d10d951005dbe76d911005ebe76d911000cbe76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110007b651d9110007b551d9110007bb70d911005fb870d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006be53d9110006bd53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006be52d9110006bd52d9110006bc52d9110006bf71d911005ebe71d911005ebd71d911005ebc71d9110006bf51d9110006be51d9110006bd51d9110006bc51d9110006bf70d911005ebe70d911005ebd70d911005ebc70d9110006bf50d9110006be50d9110006bd50d9110006bc50d911005ebd10d9110054fe76d8d100067f65d8d100067c65d8d10006bf64d8d10006bc64d8d10004ff75d8d10014fe75d8d10004fd75d8d10014fc75d8d10004ff74d8d1000cfe74d8d10004fd74d8d1000cfc74d8d1004cfe72d8d10004fd72d8d10024fe71d8d10024fc71d8d1001cfe70d8d1001cfc70d8d100657e7598d100057d7598d100067f6598d100067c6598d1005dbe7498d10005bd7498d10006bf6498d10006bc6498d10006df6398d100057f7558d100657c7558d100067f6558d100067c6558d10005bf7458d1005dbc7458d10006bf6458d10006bc6458d10005ef7258d10005ec7258d10004ff7558d100067f7558d10
  | 4 => 0xcb10024fc768cb10056de638cb10006dd638cb10004ff764cb10024fe764cb10004fd764cb10024fc764cb1004cff760cb10024fe760cb10004fd760cb10024fc760cb100757e750cb100057d750cb10045be740cb10005bd740cb10056de630cb10006dd630cb10025f6710cb10005f5710cb10005fa700cb10005f9700cb10005bf744c710045bc744c710005ef724c710005ec724c710027d4314c710045be74c8710005bd74c87100757e75cc3100057d75cc310056de63cc310006dd63cc310025f671cc310005f571cc310054ff764c310056de634c310006dd634c310005f7714c310025f4714c31004eee62c8310006ed62c8310025f671c8310005f571c831004cff76483100057f75483100757c7548310005df7348310005dc734831004eee6248310006ed6248310005f77148310025f47148310045be7408310005bd740831001cff75d8e10014fe75d8e10004fd75d8e1001cfc75d8e1001cff74d8e1000cfe74d8e1001ebe74d8e1000cbe74d8e10004fd74d8e1001ebd74d8e10004bd74d8e1001cfc74d8e1004cfe72d8e1001eee72d8e1004cee72d8e10004fd72d8e1001eed72d8e10004ed72d8e1001ef571d8e1001efa70d8e10004fd7698e1006d7e7598e100057d7598e1001edf6398e1001edc6398e10054ff7658e1001edc6358e10004ff7558e10014fe7558e10004fd7558e10014fc7558e10004ff7458e1000cfe7458e10004fd7458e1000cfc7458e1001edf7358e10006de5358e10006dd5358e10004ff7258e1004cfc7258e1001ede3058e1001edc3058e1001cff75d8a10014fe75d8a10004fd75d8a1001cfc75d8a1001cff74d8a1000cfe74d8a10004fd74d8a1001cfc74d8a10054fe73d8a10004fd73d8a1001ef571d8a1001efa70d8a10004fd7698a1001eef6298a1001eec6298a1004cff7658a1001eec6258a10004ff7558a10014fe7558a10004fd7558a10014fc7558a10004ff7458a1000cfe7458a10004fd7458a1000cfc7458a10004ff7358a10054fc7358a1001eef7258a10006ee5258a10006ed5258a10006ee4258a10006ed4258a1001eee2058a1001eec2058a10054ff76cca1001cfe76cca10004fd76cca1001cfc76cca1004eee62cca10006ed62cca1004cff768ca1001cfe768ca10004fd768ca1001cfc768ca10004ff764ca1001cfe764ca10004fd764ca1001cfc764ca1004cff760ca1001cfe760ca10004fd760ca1001cfc760ca1006d7e750ca100057d750ca1003dbe740ca10005bd740ca1004eee620ca10006ed620ca10005f6710ca10005f5710ca1001dfa700ca10005f9700ca10056de63cc610006dd63cc61001dfa70cc610005f970cc610054ff764c610005bf744c61003dbc744c610056de634c610006dd634c610005ef724c610005ec724c610005fb704c61001df
  | 5 => 0x1cfe719842001ef67198420026f65198420006f5519842004ef72198420026f4219842001ef6109842001ef41098420004ff7558420014fe7558420004fd7558420014fc7558420004ff745842000cfe7458420004fd745842000cfc7458420004ff7358420054fc735842001ef77158420006f65158420006f5515842004ef7215842004ef4215842001ef6105842001ef41058420054ff76cc42001cfe76cc420004fd76cc42016ebe64cc420006bd64cc420056de63cc420006dd63cc420024ff768c42001cfe768c420004fd768c42014ebe648c420006bd648c420026f6618c420006f5618c420004ff764c420004fd764c42001cfc764c420005bf744c42007dbc744c420156be644c420006bd644c420056de634c420006dd634c420005ef724c42004dec724c420006f6614c420006f5614c420024ff760c42001cfe760c420004fd760c4200857e750c4200057d750c42013ebe640c420006bd640c420004fd76cc0200857e75cc0200057d75cc0200eebe64cc020006bd64cc020004ff764c0200d6be644c020006bd644c02022efa604c02001def7648020006ef7648020004ef76480200076f75480202276c754802001eef6548020226ed654802001eef644802001fae644802021eed644802001fad6448020006ad6448020007cf7348020007cc734802001def704802004feb704802001eee604802001fea604802001fea404802021fe94048020024ff75d8f10014fe75d8f10004fd75d8f10024fc75d8f10024ff74d8f1000cfe74d8f10004fd74d8f10024fc74d8f1004cfe72d8f10004fd72d8f10026f671d8f10026f970d8f10004fd7698f10026df6398f10026dc6398f10054ff7658f10026dc6358f10004ff7558f10014fe7558f10004fd7558f10014fc7558f10004ff7458f1000cfe7458f10004fd7458f1000cfc7458f10026df7358f10006de5358f10006dd5358f10006de4358f10006dd4358f10004ff7258f1004cfc7258f10026de3158f10026dc3158f10024ff75d8b10014fe75d8b100267e75d8b100147e75d8b10004fd75d8b100267d75d8b100047d75d8b10024fc75d8b10024ff74d8b1000cfe74d8b10004fd74d8b10024fc74d8b10054fe73d8b10026de73d8b10054de73d8b10004fd73d8b10026dd73d8b10004dd73d8b10026f671d8b10026f970d8b10004fd7698b10045be7498b10005bd7498b10026ef6298b10026ec6298b1004cff7658b10026ec6258b10004ff7558b10014fe7558b10004fd7558b10014fc7558b10004ff7458b1000cfe7458b10004fd7458b1000cfc7458b10004ff7358b10054fc7358b10026ef7258b10006ee4258b10006ed4258b10026ee2158b10026ec2158b10054ff76ccb10024fe76ccb10004fd76ccb10024fc76ccb1004cff768cb10024fe768cb10004fd768
  | 6 => 0xf63cc120056dc63cc12004dee72cc120005ed72cc120004fe768c1200067f658c1200e67c658c120006df638c120056dc638c120005fa768c120006fa768c1200077b658c12027778658c12027df9738c120007db638c120056fa638c120056f8638c120007d8638c120056d8638c12004dfa728c12004df8728c12001efb628c120277ea528c120277e9528c12026fea428c12026fe9428c120267da328c120267d8328c120054ff764c120004fd764c12004cfc764c1200067f654c1200de7c654c120006df634c120056dc634c120005ef724c12004dec724c12004df8764c120056f8764c12004cf8764c1200077b654c12025f78654c120007db734c120007db634c120056fa634c120056f8634c120007d8634c12025fda534c12025fd9534c120007eb724c12004dfa724c12004df8724c120007e8724c12025fea524c12025fe9524c120257ea424c120257e9424c120004fe760c1200067f650c1200c67c650c120006df630c120056dc630c12024dfa700c1200067f65881200a67c6588120006df6388120006dc638812004dfa708812004efb608812001def7588120245ed75881200076f658812023f6c658812001def7488120235ed7488120007cf6388120007cc638812001dee708812001eef608812004feb608812001fea3088120007e93088120006bf7559020006be7559020006bd7559020006bc7559020006bf7359020006be7359020006bd7359020006bc7359020006bf5359020006be5359020006bd5359020006bc535902004ebf725902004ebe725902004ebd725902004ebc725902004ebf525902004ebe525902004ebd525902004ebc525902004ebf325902004ebe325902004ebd325902004ebc3259020006bf7159020006be7159020006bd7159020006bc7159020006bf5159020006be5159020006bd5159020006bc515902004ebf215902004ebe215902004ebd215902004ebc215902007ebf705902001ebe705902007ebd705902001ebc7059020006bf505902001ebe5059020006bd505902001ebc505902001ebe305902001ebc305902004ebf205902004eaf205902001ebe205902004ebd205902001ebc205902001ebe105902001ebc1059020004ff7558c20014fe7558c20004fd7558c20014fc7558c20004ff7458c2000cfe7458c20004fd7458c2000cfc7458c2001cff7358c2001edf7358c20006de5358c20006dd5358c2004cff7258c2004cfe7258c2004cfd7258c2004cfc7258c2004ede3258c2004edc3258c20004ff7158c20024fc7158c2001cfe7058c2001cfc7058c2001ede3058c2001edc3058c2004efa2058c2004ef92058c20024ff7598420014fe7598420004fd7598420024fc7598420024ff749842000cfe7498420004fd7498420024fc7498420054fe7398420004fd7398420
  | 7 => 0x8d20006df5218d20286de5218d20006dd5218d20286dc5218d20006df4218d20286de4218d20006ce4218d20006dd4218d20006cd4218d20286dc4218d20056df7118d20056de7118d20056dd7118d20056dc7118d20006df5118d20006de5118d20006dd5118d20006dc5118d20006df4118d20006de4118d20006dd4118d20006dc4118d20286df2118d20286dc2118d20056df7018d20056dd7018d20056d97018d20006df5018d20006de5018d20006dd5018d20006dc5018d20006df4018d20006de4018d20006dd4018d20006dc4018d20286df2018d20006dd2018d20286dc2018d20004fe76cc92001cfc76cc9200067f65cc9201b67c65cc920006df63cc920056dc63cc920005fa70cc920005f970cc920054fc764c9200067f654c9201967c654c920006df634c920056dc634c920005fb704c920005f8704c9200067f65d85200067c65d8520006df63d8520006dc63d8520004ff75d8520014fe75d8520004fd75d8520014fc75d8520004ff74d852000cfe74d8520004fd74d852000cfc74d8520054fe73d8520004fd73d8520006ee42d8520006ed42d8520006f741d8520006f441d852009d7e75985200057d75985200067f65985200067c6598520005de7398520005dd7398520006df6398520006dc6398520006f761985200057f755852009d7c75585200067f65585200067c6558520005bf7458520095bc7458520005df7358520005dc7358520006df6358520006dc63585200067f65185200067c6518520006df6318520006dc6318520006f56118520024ff7518520014fe7518520004fd7518520024fc7518520024ff741852000cfe7418520004fd7418520024fc7418520054fe7318520004fd7318520006f74118520026f44118520004fe76cc520004fd76cc520054fc76cc5200067f65cc5201767c65cc520006df63cc520056dc63cc520005fa70cc520005f970cc520004fe768c520004fd768c520024fc768c5200067f658c5201667c658c520006df638c520056dc638c520004ff764c520004fe764c520004fc764c5200067f654c52015e7c654c520005bf744c520095bc744c520006df634c520056dc634c520005ef724c52004dec724c520004fe760c520004fd760c520024fc760c52009d7e750c5200057d750c5200067f650c5201467c650c520006df630c520056dc630c52004dee720c520005ed720c520005fa700c520005f9700c5200067f65885201267c6588520006df6388520006dc6388520006f76188520026f46188520005fa7088520005f970885200067f654852011e7c6548520006df6348520006dc6348520006f76148520006f46148520005fb7048520005f8704852004fe8204852004cfe76cc12004cfc76cc12009d7e75cc1200057d75cc1200067f65cc1200f67c65cc120006d
  | 8 => 0x67f40d95200067e40d95200067d40d95200067c40d952028e7f20d952009e7d20d952028e7c20d9520054fe76d8d200067f65d8d200067c65d8d20004ff75d8d20014fe75d8d20004fd75d8d20014fc75d8d20004ff74d8d2000cfe74d8d20004fd74d8d2000cfc74d8d20006df53d8d20006de53d8d20006dd53d8d20006dc53d8d20006df43d8d20006de43d8d20006dd43d8d20006dc43d8d2004cfe72d8d2004cfc72d8d20024fe71d8d20004fd71d8d20054de76d8d20006df65d8d200075f65d8d200065f65d8d20006de65d8d20006dd65d8d20006dc65d8d200075c65d8d200065c65d8d20006df64d8d20006de64d8d20006dd64d8d20006dc64d8d20007ce52d8d20007cd52d8d20007ce42d8d20007cd42d8d20267db70d8d20267db20d8d20267d820d8d20006df75d8d20006de75d8d20006dd75d8d20006dc75d8d20006df74d8d20006de74d8d20006dd74d8d20006dc74d8d20006df54d8d20006de54d8d20006dd54d8d20006dc54d8d20006df72d8d20266de72d8d20006dd72d8d20266dc72d8d20006df52d8d20266de52d8d20006dd52d8d20266dc52d8d20006df42d8d20266de42d8d20006dd42d8d20266dc42d8d20006df71d8d20006de71d8d20006dd71d8d20006dc71d8d20006df51d8d20006de51d8d20006dd51d8d20006dc51d8d20006df41d8d20006de41d8d20006dd41d8d20006dc41d8d20266df21d8d20266dc21d8d20266df70d8d20006dd70d8d20006df50d8d20006de50d8d20006dd50d8d20006dc50d8d20006df40d8d20006de40d8d20006dd40d8d20006dc40d8d20266df20d8d20266dc20d8d2009d7e7598d200057d7598d200067f6598d200067c6598d20006df6398d200057f7558d2009d7c7558d200067f6558d200067c6558d20004ff7558d200067f7558d200047f7558d20014fe7558d20004fd7558d20014fc7558d200067c7558d200147c7558d20004ff7458d2000cfe7458d20004fd7458d2000cfc7458d20006df7358d20004ff7258d20006ef7258d20004ff7158d20024fc7158d20004ff7058d20006fb7058d20004fe7618d200067f6518d200067c6518d20056de6318d20006dd6318d20005de7618d20006de7618d20004de7618d20006df6518d200075f6518d200065f6518d20006de6518d20006dd6518d20006dc6518d200075c6518d200065c6518d20006df6418d20006de6418d20006dd6418d20006dc6418d20007ce5218d20007cd5218d20007ce4218d20007cd4218d20007d97018d20287db2018d20287d82018d20056df7518d20056de7518d20056dd7518d20056dc7518d20056df7418d20056de7418d20056dd7418d20056dc7418d20006df5418d20006de5418d20006dd5418d20006dc5418d20056df7218d20056de7218d20056dd7218d20056dc721
  | 9 => 0xe7458e20004fd7458e2000cfc7458e2001edf7358e20006de5358e20006dd5358e20004ff7158e20024fc7158e2001cfc7058e2001ede3058e2001edc3058e20056de63cca20006dd63cca2001dfa70cca20005f970cca20054ff764ca20056de634ca20006dd634ca2004fcc324ca20005fb704ca2001df8704ca2001ef76198620024ff7598620014fe7598620004fd7598620024fc7598620024ff749862000cfe7498620004fd7498620024fc7498620054fe7398620004fd7398620026f65198620006f5519862001cfe709862001ef6109862001ef41098620005bf745862008dbc745862001ef46158620004ff7558620014fe7558620004fd7558620014fc7558620004ff7458620006bf7458620004bf745862000cfe7458620004fd745862000cfc7458620006bc745862000cbc7458620004ff7358620054fc7358620006f65158620006f5515862001cfc705862001ef6105862001ef41058620054ff76cc62001cfe76cc620004fd76cc62001dfa70cc620005f970cc620024ff768c62001cfe768c620004fd768c620004ff764c620004fd764c62001cfc764c620005bf744c62008dbc744c620005ef724c62004dec724c620024ff760c62001cfe760c620004fd760c6200a57e750c6200057d750c62001dfa700c620005f9700c620026f66188620006f5618862001dfa7088620005f97088620006f66148620006f56148620005fb704862001df870486200a57e75cc2200057d75cc22001df9768c22001ef9768c22004cf9768c220056fa638c22001fda638c22001fd9638c22001ef8638c22004dfa728c22001fea728c22001fe9728c22001df8728c220267da328c220267d8328c220005fb764c220006fb764c22001fdb734c220056fa634c220056f8634c2202a7da534c2202a7d9534c22004dfa724c22004df8724c22001ded76c822004eed76c822001eef65c8220296ed65c822001eef64c822029eed64c822001fea60c822001fea50c8220297e950c822009d7e76d952009e7e76d95200147e76d95200067f64d95200067e64d95200067d64d95200067c64d95200076f72d952009f6c72d95200076e42d95200076d42d952028f7b20d952028f7820d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200067e73d95200067d73d95200067c73d95200067f43d95200067e43d95200067d43d95200067c43d95200067f72d952028e7e72d952009e7d72d952028e7c72d95200067f42d952028e7e42d95200067d42d952028e7c42d952028e7e32d952028e7c32d95200067f71d95200067e71d95200067d71d95200067c71d95200067f41d95200067e41d95200067d41d95200067c41d952028e7f21d952028e7c21d952028e7f70d952009e7e70d952009e7d70d952009e7c70d9520
  | 10 => 0x8430004ff7558430014fe7558430004fd7558430014fc7558430004ff7458430006bf7458430004bf745843000cfe7458430004fd745843000cfc7458430006bc745843000cbc7458430004ff725843004cfc725843001ef77158430006f65158430006f55158430006f64158430006f54158430056f73158430056f4315843001ef6105843001ef4105843004cff76c843001cfe76c8430004fd76c84300bdbe74c8430005bd74c843004eee62c8430006ed62c8430024ff768843001cfe7688430004fd7688430055de7388430005dd73884302b7cc3288430026f66188430006f56188430004ff7648430004fd764843001cfc7648430005df7348430055dc734843004eee6248430006ed6248430006f66148430006f56148430024ff760843001cfe7608430004fd7608430287cc320843001ddf764c030006df764c030004df764c03001edf654c0302aedd654c030285dc724c03001ddf704c030057db704c03001ede604c03001fda604c030004ff7558f20014fe7558f20004fd7558f20014fc7558f20004ff7458f2000cfe7458f20004fd7458f2000cfc7458f2004edf7358f2004cfc7258f2004ede3258f2004edc3258f20004ff7158f20024fc7158f2004efa2058f2004ef92058f20024ff7598720014fe7598720004fd7598720024fc7598720024ff749872000cfe7498720004fd7498720024fc7498720054fe7398720004fd7398720026f6719872004ef72198720026f42198720004ff7558720014fe7558720004fd7558720014fc7558720004ff745872000cfe7458720004fd745872000cfc7458720004ff7358720054fc735872004eee4258720006ed425872004ef7715872004ef7215872004ef42158720054ff76cc72004cfe76cc720004fd76cc720024ff768c72004cfe768c720004fd768c720026f6618c720006f5618c720004ff764c720004fd764c72004cfc764c720005bf744c7200adbc744c720005ef724c72004dec724c720006f6614c720006f5614c720024ff760c72004cfe760c720004fd760c7200b57e750c7200057d750c72004dee720c720005ed720c7200b57e75cc3200057d75cc320056de63cc320006dd63cc32004dee72cc320005ed72cc320266df638c320056dc638c320054ff764c320056de634c320006dd634c320005ef724c32004dec724c320286df630c320056dc630c32001cff75d8e20014fe75d8e20004fd75d8e2001cfc75d8e2001cff74d8e2000cfe74d8e20004fd74d8e2001cfc74d8e2001eed72d8e20266de32d8e20266dc32d8e20024fe71d8e20004fd71d8e2001efa70d8e20004fd7698e200a57e7598e200057d7598e2001edf6398e2001edc6398e20054ff7658e2001edc6358e20004ff7558e20014fe7558e20004fd7558e20014fc7558e20004ff7458e2000cf
  | 11 => 0x267cc320863001dfa7008630005f9700863001ddd76cc230056dd76cc2300575e75cc2300575d75cc23001edf65cc2302cedd65cc230265de72cc23001fda60cc23001fda50cc2302cfd950cc230004ff75d8930014fe75d8930004fd75d8930014fc75d8930004ff74d893000cfe74d8930004fd74d893000cfc74d8930006ef52d8930006ec52d8930006ee42d8930006ed42d8930024fe71d8930004fd71d8930006ef62989300057f75589300dd7c75589300d5be7418930005bd741893004eee6218930006ed6218930006ef628c93004eec628c930005fa708c930005f9708c93004cfc764c930006ef624c93004eec624c930005fb704c930005f8704c930004ff75d8530014fe75d8530004fd75d8530014fc75d8530004ff74d853000cfe74d8530004fd74d853000cfc74d8530006de53d8530006dd53d853004cfe72d8530004fd72d8530006f761985300057f75585300dd7c7558530005bf74585300d5bc7458530005ef7258530005ec7258530006f56118530024ff7518530014fe7518530004fd7518530024fc7518530024ff741853000cfe7418530004fd7418530024fc741853004cfe7218530004fd7218530006f7618c530026f4618c530005fa708c530005f9708c530005bf744c5300d5bc744c530005ef724c530005ec724c530006f7614c530006f4614c530057d4314c530005fb704c530005f8704c530004fe76c8530004fd76c853004cfc76c85300d5be74c8530005bd74c8530005fa70c8530005f970c8530004fe7688530004fd7688530024fc7688530006ef628853004eec6288530004ff7648530004fe7648530004fc7648530004fe7608530004fd7608530024fc7608530055de7308530005dd7308530006ef620853004eec6208530005fa7008530005f97008530055fa708c130056fb608c13001ddf758c1302c5dd758c130266dc628c13001dde708c13001edf608c130057db608c130004ff7558830014fe7558830004fd7558830014fc7558830004ff745883000cfe7458830004fd745883000cfc745883001eef7258830006ee5258830006ed5258830006ee4258830006ed4258830056ef3258830056dc3258830056ec3258830004ff7158830024fc7158830056fa3058830056f9305883001eee205883001eec2058830055dd768c830286dd768c830056df658c8302bedd658c830055de728c830057ce728c830056df628c830286dd628c830005dd708c830266de608c830057da608c830024ff7598430014fe7598430004fd7598430024fc7598430024ff749843000cfe7498430004fd7498430024fc749843004cfe7298430004fd729843001cfe719843001ef67198430026f65198430006f55198430026f64198430006f54198430056f73198430026f4319843001ef6109843001ef4109
  | 12 => 0xd7558730014fc7558730004ff745873000cfe7458730004fd745873000cfc7458730056de5358730006dd5358730004ff725873004cfc7258730056f77158730006f74158730006f44158730056f73158730056f4315873004cff76c8730054fe76c8730004fd76c87301367e65c87300067d65c87300edbe74c8730005bd74c8730024ff7688730054fe7688730004fd76887301267e65887300067d6588730026f66188730006f56188730004ff7648730004fd7648730054fc764873011e7e65487300067d6548730006f66148730006f56148730024ff7608730054fe7608730004fd76087301067e65087300067d6508730055de7308730005dd730873001eef6298a3001eec6298a3001eec6258a30004ff7558a30014fe7558a30004fd7558a30014fc7558a30004ff7458a3000cfe7458a30004fd7458a3000cfc7458a30006ee5258a30006ed5258a30006ee4258a30006ed4258a30004ff7158a30024fc7158a3001cfc7058a3001eee2058a3001eec2058a3004eee628ca30006ed628ca3001dfa708ca30005f9708ca302e6df658ca302e6dd658ca30055de728ca30267ce628ca30266dd628ca30007cd628ca30267da708ca30005dd708ca30267d9708ca30056de608ca3004cff764ca3004eee624ca30006ed624ca30057cc324ca30005fb704ca3001df8704ca30005dd760ca30056dd760ca300575e750ca300575d750ca302dedf650ca302dedd650ca300579e740ca300579d740ca30057ce720ca30266dd620ca30267ce420ca302d7cd420ca30057d6710ca30057d5710ca30057da700ca30005dd700ca30057d9700ca30005d9700ca30057da600ca3001ef76198630024ff7598630014fe7598630004fd7598630024fc7598630024ff749863000cfe7498630004fd7498630024fc749863004cfe7298630004fd7298630026f65198630006f5519863001cfe709863001ef6109863001ef4109863001ef46158630004ff7558630014fe7558630004fd7558630014fc7558630004ff745863000cfe7458630004fd745863000cfc7458630004ff725863004cfc7258630006f65158630006f5515863001cfc705863001ef6105863001ef41058630026f6618c630006f5618c63001dfa708c630005f9708c630005bf744c6300cdbc744c630005ef724c630005ec724c630006f6614c630006f5614c630005fb704c63001df8704c63004cff76c863001cfe76c8630004fd76c86300cdbe74c8630005bd74c863001dfa70c8630005f970c8630024ff768863001cfe7688630004fd7688630055de7388630005dd738863004eee6288630006ed6288630007cc3288630004ff7648630004fd764863001cfc7648630005df7348630055dc7348630024ff760863001cfe7608630004fd760863004eee6208630006ed6208630
  | 13 => 0x8c2104cfe7258c2104cfc7258c2104eec7258c2104cec7258c2104ede3258c2104edc3258c2104eec3258c2104ecc3258c21024fe7158c21024fc7158c21026de3158c21026dc3158c2104ef62158c2104ef52158c21004ff7058c2101cfc7058c2104ded76cc8212f6ed76cc82104eef64cc82130eed64cc82104dee73cc82104fce73cc82104eef63cc8212f6ed63cc821005ed71cc8212b6ee61cc82104fe661cc821004fd76cc42104dec72cc421004ff764c421005bf744c4210fdbc744c421005ef724c42104dec724c421306f6614c421025ef7648421006ef7648421004ef7648421026ef64484212feed64484212f5ee73484212f5ec7348421025ef714842104fe77148421026ee6148421027e66148421027e651484212efe5514842101cff7598021014fe7598021004fd759802101cfc759802101cff749802100cfe7498021004fd749802101cfc7498021054fe7398021004fd739802101efa709802101efa5098021006f9509802101efa4098021006f9409802104efb209802101ef82098021026fb109802101ef81098021004ff75580210067f75580210047f7558021014fe7558021004fd7558021014fc75580210067c75580210147c7558021004ff745802100cfe7458021004fd745802100cfc7458021004ff7358021054fc7358021026fb7058021006fa5058021006f95058021006fa4058021006f9405802104efb205802104ef82058021026fb1058021026f810580210067f74597300067e74597300067d74597300067c74597300567f73597300567e73597300567d73597300567c73597300567f43597300567e43597300567d43597300567c43597300067f72597300067e72597300067d72597300067c72597300067f42597300067e42597300067d42597300067c42597300567f32597300567e32597300567d32597300567c32597300067f71597300067e71597300067d71597300067c71597300067f41597300067e41597300067d41597300067c41597300567f31597300567e31597300567d31597300567c31597300f67f70597300f67e70597300067d70597300f67c70597300067f40597300067e40597300067d40597300067c40597300567f30597300567e30597300567d30597300567c3059730004ff7558b30014fe7558b30004fd7558b30014fc7558b30004ff7458b3000cfe7458b30004fd7458b3000cfc7458b30056ef7258b30056ef3258b30056ec3258b30004ff7158b30024fc7158b30056fa3058b30056f93058b30024ff7598730014fe7598730004fd7598730024fc7598730024ff749873000cfe7498730004fd7498730024fc749873004cfe7298730004fd7298730026f67198730006f74198730026f44198730056f73198730026f43198730004ff7558730014fe7558730004f
  | 14 => 0x4ff745822100cfe7458221004fd745822100cfc7458221004ff7358221054fc7358221024fc7158221006fa4058221006f94058221026fb1058221026f81058221054fe76d8d21004ff75d8d21014fe75d8d21004fd75d8d21014fc75d8d21004ff74d8d2100cfe74d8d21004fd74d8d2100cfc74d8d21006de53d8d21006dd53d8d21006df43d8d21006dc43d8d2101cfe70d8d21004fd70d8d21006df6398d21005bf7458d21115bc7458d21004ff7558d21014fe7558d21004fd7558d21014fc7558d21004ff7458d21006bf7458d21004bf7458d2100cfe7458d21004fd7458d2100cfc7458d21006bc7458d2100cbc7458d21006df7358d21004ff7258d21006ef7258d21004ef7258d21004ff7158d21006f77158d21004ff7058d2101cfc7058d21004fe7618d2111d7e7518d210057d7518d21056de6318d21006dd6318d21004fe76cc921024fc76cc921006df63cc921056dc63cc921005f671cc921005f571cc921054fc764c921006df634c921056dc634c92104fcc324c921005f7714c921005f4714c92104cfe76cc52104cfc76cc521006df63cc521056dc63cc52104dee72cc521005ed72cc521004fe768c521005f6768c521006f6768c52133df5738c521056f6638c521056f4638c52104df6728c52104df4728c521026f7628c521337e6428c521337e5428c521054ff764c521004fd764c52104cfc764c521005bf744c521115bc744c521006df634c521056dc634c521005ef724c52104dec724c52104df4764c521056f4764c52104cf4764c521007b7744c521327b4744c521007d7734c521007d7634c521056f6634c521056f4634c521007d4634c52132fd6534c52132fd5534c521327d6434c521327d5434c521007e7724c52104df6724c52104df4724c521007e4724c521327e6424c521327e5424c521004fe760c52111d7e750c5210057d750c52131df6710c52104df6718852104ef76188521025ef7488521315ed74885212b6ee63885212b6ec6388521025ee7188521026ef618852104fe76188521027e63188521007e53188521004ff75d8121014fe75d8121004fd75d8121014fc75d8121004ff74d812100cfe74d8121004fd74d812100cfc74d8121054fe73d8121004fd73d8121006ee42d8121006ed42d8121006fb60981210057f755812111d7c7558121005bf7458121115bc7458121005df7358121005dc7358121006f9601812101cff7518121014fe7518121004fd751812101cfc751812101cff741812100cfe7418121004fd741812101cfc7418121054fe7318121004fd7318121004ff7558c21014fe7558c21004fd7558c21014fc7558c21004ff7458c2100cfe7458c21004fd7458c2100cfc7458c21024ff7358c21026df7358c21006de5358c21006dd5358c21006de4358c21006dd435
  | 15 => 0xe7498321004fd749832101cfc7498321054fe7398321004fd739832101efa7098321006fb509832101ef8509832104efb209832101ef82098321004ff7558321014fe7558321004fd7558321014fc7558321004ff745832100cfe7458321004fd745832100cfc7458321004ff7358321054fc735832104eee4258321006ed425832104efb7058321006fb5058321006f8505832104efb205832104ef82058321024ff75d8e21014fe75d8e21004fd75d8e21024fc75d8e21024ff74d8e2100cfe74d8e21004fd74d8e21024fc74d8e21026ed72d8e21026f671d8e2101cfe70d8e21004fd70d8e21004fd7698e21026df6398e21026dc6398e21054ff7658e21026dc6358e21004ff7558e21014fe7558e21004fd7558e21014fc7558e21004ff7458e2100cfe7458e21004fd7458e2100cfc7458e21026df7358e21006de5358e21006dd5358e21006de4358e21006dd4358e21006ef7258e21024fc7158e21026de3158e21026dc3158e21004ff7058e2101cfc7058e21056de63cca21006dd63cca21025f671cca21005f571cca212b6ed76cca2136eef64cca2136eed64cca2104dee73cca212b6ef63cca212b7ce63cca212b6ed63cca21007cd63cca212b7e671cca21005ed71cca212b7e571cca2104eee61cca21054ff764ca21056de634ca21006dd634ca21005f7714ca21025f4714ca21005ed760ca2104eed760ca2104f6e750ca2104f6d750ca2104fae740ca2104fad740ca21366ef640ca21366ed640ca2104fce730ca212b6ef630ca212b6ed630ca212b7ce530ca2135fcd530ca2104fe6710ca21005ed710ca2104fe5710ca21005e5710ca2104fe6610ca2104fea700ca2104fe9700ca21025f5768c621026f5768c62104cf5768c621056f6638c621027d6638c621027d5638c621026f4638c62104df6728c621027e6728c621027e5728c621025f4728c6212b7e7328c6212b7e4328c621005bf744c62110dbc744c621005ef724c62104dec724c621005f7764c621006f7764c621007b7744c621307b4744c621027d7734c621056f6634c621056f4634c621357d6534c621357d5534c621307d6434c621307d5434c621007e7724c62104df6724c62104df4724c621007e4724c62104de4724c6212b7e7324c6212b7e4324c621025ed76c862104eed76c862104fae74c862104fad74c8621026ef64c862134eed64c86212b5ee73c862104dec73c8621027e661c8621027e651c8621347e551c8621026fb609822101cff7598221014fe7598221004fd759822101cfc759822101cff749822100cfe7498221004fd749822101cfc7498221054fe7398221004fd7398221024fe719822101efa4098221006f94098221026fb109822101ef81098221026f86058221004ff7558221014fe7558221004fd7558221014fc7558221
  | 16 => 0x94310067c40594310567f30594310567e30594310567d30594310567c30594310267f10594310267c1059431004ff7558831014fe7558831004fd7558831014fc7558831004ff745883100cfe7458831004fd745883100cfc7458831026ef7258831006ee4258831006ed4258831056ef3258831056ec3258831056f63158831056f53158831026ee2158831026ec2158831004ff705883101cfc7058831025df764c431006df764c431004df764c431026df654c4310275e654c431376dd654c4310275d654c4310065d654c4310079f744c43137f9c744c431026df644c43137edd644c431007cf724c431007cc724c431025df714c431057d7714c431026de614c431027d6614c431027d6514c431377d5514c43101cff7598031014fe7598031004fd759803101cfc759803101cff749803100cfe7498031004fd749803101cfc749803104cfe7298031004fd729803101efa709803101efa4098031006f94098031056fb309803101ef83098031026fb109803101ef81098031004ff7558031014fe7558031004fd7558031014fc7558031004ff745803100cfe7458031004fd745803100cfc7458031004ff725803104cfc7258031026fb7058031006fa4058031006f94058031056fb3058031056f83058031026fb1058031026f81058031006bf7559321006be7559321006bd7559321006bc7559321006bf7359321006be7359321006bd7359321006bc7359321006bf5359321006be5359321006bd5359321006bc535932104ebf725932104ebe725932104ebd725932104ebc725932104ebf525932104ebe525932104ebd525932104ebc525932104ebf325932104ebe325932104ebd325932104ebc325932112ebf715932112ebe7159321006bd715932112ebc7159321006bf5159321006be5159321006bd5159321006bc515932104ebf215932104ebe215932104ebd215932104ebc2159321006bf7059321006be7059321006bd7059321006bc7059321006bf5059321006be5059321006bd5059321006bc505932104ebf205932104ebe205932104ebd205932104ebc2059321004ff7558f21014fe7558f21004fd7558f21014fc7558f21004ff7458f2100cfe7458f21004fd7458f2100cfc7458f2104edf7358f2104cfc7258f2104ede3258f2104edc3258f2104ef62158f2104ef52158f21004ff7058f2101cfc7058f2116ebe64cc721006bd64cc721056de63cc721006dd63cc72104dee72cc721005ed72cc72114ebe648c721006bd648c721054ff764c721005bf744c72112dbc744c721156be644c721006bd644c721056de634c721006dd634c721005ef724c72104dec724c7211357e750c7210057d750c72113ebe640c721006bd640c72101cff7598321014fe7598321004fd759832101cfc759832101cff749832100cf
  | 17 => 0x4eee731893104eec7318931006ef53189312f6ee5318931006ce5318931006ed5318931006cd53189312f6ec5318931006ef43189312f6ee4318931006ed43189312f6ec431893104eef711893104eed711893104ee57118931006ef5118931006ee5118931006ed5118931006ec5118931006ef4118931006ee4118931006ed4118931006ec41189312f6ef3118931006ed31189312f6ec311893104eef701893104eee701893104eed701893104eec7018931006ef5018931006ee5018931006ed5018931006ec5018931006ef4018931006ee4018931006ed4018931006ec40189312f6ef30189312f6ec3018931006bf648c93119ebc648c931006ef628c93104eec628c931005f6718c931005f5718c93104cfc764c931006bf644c93118ebc644c931006ef624c93104eec624c931057cc324c931005f7714c931005f4714c931006bf648c53114ebc648c531006ef628c531006ec628c531055f6718c531056f7618c531025df758c531395dd758c531025df748c53138ddd748c5310079f648c5313879c648c531007cf628c531007cc628c531025de718c531026df618c531057d7618c531006bf64d8131006bc64d8131006ef62d8131006ec62d8131004ff75d8131014fe75d8131004fd75d8131014fc75d8131004ff74d813100cfe74d8131004fd74d813100cfc74d8131006de53d8131006dd53d813104cfe72d8131004fd72d8131006fb50d8131006f850d8131155be7498131005bd7498131006bf6498131006bc6498131005ee7298131005ed7298131006ef6298131006ec6298131006fb60981310057f755813115d7c7558131005bf7458131155bc7458131006bf6458131006bc6458131005ef7258131005ec7258131006ef6258131006ec6258131006bf6418131006bc6418131006ef6218131006ec6218131006f9601813101cff7518131014fe7518131004fd751813101cfc751813101cff741813100cfe7418131004fd741813101cfc741813104cfe7218131004fd7218131006fb501813101ef850181310067f74594310067e74594310067d74594310067c74594310567f73594310567e73594310567d73594310567c73594310567f43594310567e43594310567d43594310567c43594310067f72594310067e72594310067d72594310067c72594310067f42594310067e42594310067d42594310067c42594310567f32594310567e32594310567d32594310567c32594311467f71594310267e71594311467d71594310267c71594310067f41594310267e41594310067d41594310267c41594310567f31594310565f31594310267e31594310567d31594310267c31594310267e21594310267c21594310067f70594310067e70594310067d70594310067c70594310067f40594310067e40594310067d405
  | 18 => 0xd73d913139ebc73d9131006bf53d913139ebe53d9131006bd53d913139ebc53d9131006bf72d9131006be72d9131006bd72d9131006bc72d9131006bf52d9131006be52d9131006bd52d9131006bc52d913139ebf32d913139ebc32d913139ebf71d9131156be71d9131156bd71d9131156bc71d9131006bf51d9131006be51d9131006bd51d9131006bc51d913139ebf31d9131156bd31d913139ebc31d9131006bf70d9131006be70d9131006bd70d9131006bc70d9131006bf50d9131006be50d9131006bd50d9131006bc50d913139ebf30d913139ebc30d9131006bf64d8931006bc64d8931004ff75d8931014fe75d8931004fd75d8931014fc75d8931004ff74d893100cfe74d8931004fd74d893100cfc74d8931006ef52d8931006ee52d8931006ed52d8931006ec52d8931006ef42d8931006ee42d8931006ed42d8931006ec42d893101cfe70d8931004fd70d8931006ef65d8931006ee65d8931006ed65d8931006ec65d8931006ef64d8931007af64d8931006af64d8931006ee64d8931006ed64d8931006ec64d8931007ac64d8931006ac64d8931007ce53d8931007cd53d8931007ce43d8931007cd43d89312b7e771d89312b7e731d89312b7e431d8931006ef75d8931006ee75d8931006ed75d8931006ec75d8931006ef74d8931006ee74d8931006ed74d8931006ec74d8931006ef54d8931006ee54d8931006ed54d8931006ec54d8931006ef73d89312b6ee73d8931006ef53d89312b6ee53d8931006ed53d89312b6ec53d8931006ef43d89312b6ee43d8931006ed43d89312b6ec43d89312b6ef71d8931006ed71d8931006ef51d8931006ee51d8931006ed51d8931006ec51d8931006ef41d8931006ee41d8931006ed41d8931006ec41d89312b6ef31d89312b6ec31d8931006ef70d8931006ee70d8931006ed70d8931006ec70d8931006ef50d8931006ee50d8931006ed50d8931006ec50d8931006ef40d8931006ee40d8931006ed40d8931006ec40d89312b6ef30d89312b6ec30d8931155be7498931005bd7498931006bf6498931006bc6498931006ef6298931005bf7458931155bc7458931006bf6458931006bc6458931006bf6418931006bc641893104eee6218931006ed6218931005ee7618931006ee7618931006ef6518931006ee6518931006ed6518931006ec6518931006ef6418931007af6418931006af6418931006ee6418931006ed6418931006ec6418931007ac6418931006ac6418931007ce5318931007cd5318931007ce4318931007cd4318931007e571189312f7e731189312f7e4311893104eef751893104eee751893104eed751893104eec751893104eef741893104eee741893104eed741893104eec7418931006ef5418931006ee5418931006ed5418931006ec541893104eef7318931
  | 19 => 0x803204ef9525803204ef8525803204efb425803204efa425803204eea425803204ef94258032006e9425803204ef8425803204efb325803204efa325803204ef9325803204ef83258032006fb7158032006fa7158032006f97158032006f87158032006fb5158032006fa5158032006f95158032006f85158032006fb4158032006fa4158032006f94158032006f84158032056fb3158032056fa3158032056f93158032056f8315803204efb215803204efa215803204ef9215803204ef82158032004ff7558b31014fe7558b31004fd7558b31014fc7558b31004ff7458b3100cfe7458b31004fd7458b3100cfc7458b31056ef7258b31056ef3258b31056ec3258b31056f63158b31056f53158b31004ff7058b3101cfc7058b3101cff7598331014fe7598331004fd759833101cfc759833101cff749833100cfe7498331004fd749833101cfc749833104cfe7298331004fd729833101efa7098331056fb309833101ef83098331004ff7558331014fe7558331004fd7558331014fc7558331004ff745833100cfe7458331004fd745833100cfc7458331056de5358331006dd5358331004ff725833104cfc7258331056fb7058331056fb3058331056f8305833114dbe7498a31005bd7498a31026ef6298a31026ec6298a31026ec6258a31004ff7558a31014fe7558a31004fd7558a31014fc7558a31004ff7458a3100cfe7458a31004fd7458a3100cfc7458a31006ee4258a31006ed4258a31024fc7158a31026ee2158a31026ec2158a31004ff7058a3101cfc7058a3104eee628ca31006ed628ca31025f6718ca31005f5718ca3104cff764ca3104eee624ca31006ed624ca31005f7714ca31025f4714ca31025dd76cc631056dd76cc631026df65cc6313a6dd65cc631026df64cc6313aedd64cc631027d661cc631027d651cc6313a7d551cc631026fb609823101cff7598231014fe7598231004fd759823101cfc759823101cff749823100cfe7498231004fd749823101cfc749823104cfe7298231004fd7298231024fe719823101efa4098231006f94098231026fb109823101ef810982310057f75582311657c7558231026f86058231004ff75582310067f75582310047f7558231014fe7558231004fd7558231014fc75582310067c75582310147c7558231004ff745823100cfe7458231004fd745823100cfc7458231004ff725823104cfc7258231024fc7158231006fa4058231006f94058231026fb1058231026f81058231155be76d9131156be76d913100cbe76d9131006bf65d9131006be65d9131006bd65d9131006bc65d91310079f73d91311579c73d91310079e53d91310079d53d913139fb731d913139fb431d9131006bf75d9131006be75d9131006bd75d9131006bc75d9131006bf73d913139ebe73d9131156b
  | 20 => 0x4ef4525843204ef7425843204ef6425843204ee6425843204ef54258432006e5425843204ef4425843204ef7325843204ef6325843204ef5325843204ef43258432006f77058432006f67058432006f57058432006f47058432006f75058432006f65058432006f55058432006f45058432006f74058432006f64058432006f54058432006f44058432056f73058432056f63058432056f53058432056f4305843204ef7205843204ef6205843204ef5205843204ef4205843201cff7598032014fe7598032004fd759803201cfc759803201cff749803200cfe7498032004fd749803201cfc7498032024fe7198032004fd719803201cfe709803201efa7098032006fb509803201efa5098032006f9509803201ef85098032006fb409803201efa4098032006f9409803201ef84098032056fb309803201ef8309803204efb209803201ef8209803201efb7598032006fa7598032006f9759803201ef8759803201efb7498032006fa7498032006f9749803201ef87498032006fb5498032006fa5498032006f95498032006f85498032056fa7398032056f9739803201ef87398032056fb5398032056fa5398032056f95398032056f85398032056fb4398032056fa4398032056f94398032056f8439803204efa729803204ef9729803201ef8729803204efb529803204efa529803204ef9529803204ef8529803204efb429803204efa429803204ef9429803204ef8429803204efb329803204efa329803204ef9329803204ef8329803201efb7198032006fa7198032006f9719803201ef87198032006fb5198032006fa5198032006f95198032006f85198032006fb4198032006fa4198032006f94198032006f84198032056fb3198032056fa3198032056f93198032056f8319803204efb219803204efa219803204ef9219803204ef82198032004ff7558032014fe7558032004fd7558032014fc7558032004ff745803200cfe7458032004fd745803200cfc7458032056de5358032006dd535803204eee4258032006ed4258032004ff7158032024fc715803204efb7058032006fb5058032006fa5058032006f95058032006f85058032006fb4058032006fa4058032006f94058032006f84058032056fb3058032056dc3058032056f8305803204efb205803204ef82058032006fb7558032006fa7558032006f97558032006f87558032006fb7458032006fa7458032006f97458032006f87458032006fb5458032006fa5458032006f95458032006f85458032056fb7358032056fa7358032056f87358032056fb5358032056fa5358032056da5358032056f95358032006d95358032056f85358032056fb4358032056fa4358032056f94358032056f8435803204efb725803204efa725803204ef8725803204efb525803204efa525
  | 21 => 0xd7159032006bc7159032006bf5159032006be5159032006bd5159032006bc5159032056bf3159032056be3159032056bd3159032056bc315903204ebf215903204ebe215903204ebd215903204ebc2159032006bf7059032006be7059032006bd7059032006bc7059032006bf5059032006be5059032006bd5059032006bc5059032056bf3059032056be3059032056bd3059032056bc305903204ebf205903204ebe205903204ebd205903204ebc2059032024ff7598432014fe7598432004fd7598432024fc7598432024ff749843200cfe7498432004fd7498432024fc7498432024fe7198432026f67198432006f75198432026f65198432006f55198432026f45198432006f74198432026f64198432006f54198432026f44198432056f73198432026f4319843204ef72198432026f4219843201cfe7098432004fd7098432026f77598432006f67598432006f57598432026f47598432026f77498432006f67498432006f57498432026f47498432006f75498432006f65498432006f55498432006f45498432056f67398432056f57398432026f47398432056f75398432056f65398432056f55398432056f45398432056f74398432056f64398432056f54398432056f4439843204ef6729843204ef57298432026f4729843204ef7529843204ef6529843204ef5529843204ef4529843204ef7429843204ef6429843204ef5429843204ef4429843204ef7329843204ef6329843204ef5329843204ef43298432026f77098432006f67098432006f57098432026f47098432006f75098432006f65098432006f55098432006f45098432006f74098432006f64098432006f54098432006f44098432056f73098432056f63098432056f53098432056f4309843204ef7209843204ef6209843204ef5209843204ef42098432004ff7558432014fe7558432004fd7558432014fc7558432004ff745843200cfe7458432004fd745843200cfc7458432056de5358432006dd535843204eee4258432006ed425843204ef77158432006f75158432006f65158432006f55158432006f45158432006f74158432006f64158432006f54158432006f44158432056f73158432056f4315843204ef7215843204eec215843204ef42158432004ff705843201cfc7058432006f77558432006f67558432006f57558432006f47558432006f77458432006f67458432006f57458432006f47458432006f75458432006f65458432006f55458432006f45458432056f77358432056f67358432056f47358432056f75358432056f65358432056d65358432056f55358432006d55358432056f45358432056f74358432056f64358432056f54358432056f4435843204ef7725843204ef6725843204ef4725843204ef7525843204ef6525843204ef55258432
  | 22 => 0x8232004fd749823201cfc749823204cfe7298232024fe7198232004fd719823201efa709823204efb209823201ef82098232004ff75582320067f75582320047f7558232014fe7558232004fd7558232014fc75582320067c75582320147c7558232004ff745823200cfe7458232004fd745823200cfc7458232006de5358232006dd535823204cfc7258232004ff7158232024fc715823204efb705823204efb205823204ef82058232004ff75d8532014fe75d8532004fd75d8532014fc75d8532004ff74d853200cfe74d8532004fd74d853200cfc74d8532006f741d8532006f441d853201cfe70d8532004fd70d8532006f76198532005bf745853218dbc7458532006f56118532024ff7518532014fe7518532004fd7518532024fc7518532024ff741853200cfe7418532004fd7418532024fc74185322f6ef32185322f6ec3218532006f74118532026f4411853201cfe7018532004fd7018532004ff75d8132014fe75d8132004fd75d8132014fc75d8132004ff74d813200cfe74d8132004fd74d813200cfc74d8132024fe71d8132004fd71d8132006fb50d8132006f850d8132006fb60981320057f75581321957c7558132006f9601813201cff7518132014fe7518132004fd751813201cfc751813201cff741813200cfe7418132004fd741813201cfc7418132286de3218132286dc3218132024fe7118132004fd7118132006fb501813201ef850181320067f74594320067e74594320067d74594320067c74594320567f73594320567e73594320567d73594320567c73594320567f43594320567e43594320567d43594320567c435943204e7f725943204e7e725943204e7d725943204e7c725943204e7f425943204e7e425943204e7d425943204e7c425943204e7f325943204e7e325943204e7d325943204e7c32594320067f71594320067e71594320067d71594320067c71594320067f41594320067e41594320067d41594320067c41594320567f31594320567e31594320567d31594320567c315943204e7f215943204e7e215943204e7d215943204e7c21594320067f70594320067e70594320067d70594320067c70594320067f40594320067e40594320067d40594320067c40594320567f30594320567e30594320567d30594320567c305943204e7f205943204e7e205943204e7d205943204e7c2059432006bf7559032006be7559032006bd7559032006bc7559032056bf7359032056be7359032056bd7359032056bc7359032056bf5359032056be5359032056bd5359032056bc535903204ebf725903204ebe725903204ebd725903204ebc725903204ebf525903204ebe525903204ebd525903204ebc525903204ebf325903204ebe325903204ebd325903204ebc3259032006bf7159032006be7159032006b
  | 23 => 0x1000e003007000401200300000040000010020004000002000000c01000100000200060000008000000000000000800200500000000040000038014002000001000000a000004000000200000b800c002002000000400e000000804800001101180000020040020004000002002000000000100000040020000000000008001000000000600000100000020000030000002001000000000200100180100000000028004002000001001000000000280240000040008010004000000000c00000100280100040000000028000007000000800a001003000000000b000001400000200100080000000008028000001000800c0040040008000006001000000c000008000800401200000200000220020028004000003000000000000200100040040000040014004008000000c00a0090008000002001000800000a003001800c00200a002001400400400480100060030000008000001000000000000700000000040010010000002012000000400400200500000000050000000002004005802400000000000000000060030000000003024ff7598732014fe7598732004fd7598732024fc7598732024ff749873200cfe7498732004fd7498732024fc749873204cfe7398732026f67198732056f73198732026f4319873201cfe7098732004fd7098732004ff7558732014fe7558732004fd7558732014fc7558732004ff7458732006bf7458732004bf745873200cfe7458732004fd745873200cfc7458732006bc745873200cbc745873204cfc7358732006ee4258732006ed4258732056f77158732056f73158732056f43158732004ff705873201cfc705873201cff7598332014fe7598332004fd759833201cfc759833201cff749833200cfe7498332004fd749833201cfc749833204cfe7398332266de3298332056dc3298332024fe7198332004fd719833201efa7098332056fb309833201ef83098332004ff7558332014fe7558332004fd7558332014fc7558332004ff745833200cfe7458332004fd745833200cfc745833204cfc7358332006ee4258332006ed4258332004ff7158332024fc7158332056fb7058332056fb3058332056f83058332024ff7598632014fe7598632004fd7598632024fc7598632024ff749863200cfe7498632004fd7498632024fc749863204cfe72986322b6ef329863204eec3298632026f6719863204ef72198632026f4219863201cfe7098632004fd7098632004ff7558632014fe7558632004fd7558632014fc7558632004ff745863200cfe7458632004fd745863200cfc7458632006de5358632006dd535863204cfc725863204ef7715863204ef7215863204ef42158632004ff705863201cfc705863201cff7598232014fe7598232004fd759823201cfc759823201cff749823200cfe749
  | 24 => 0x8004003000400200100c00000000000008004002000000000400a00e000801c0040050038004004002003000400200f00000080000000000000020001000001800e0010000000000006000800001400100180140000000010028008001003800000c000000000400a003002000400000000000000060000000000000001001800000000000880400080090000000000005001800000200100700080080000008004000002002800000000100080000000000000008000000001804400400400080480220000000008008001000000001c000001000001000000000000040000008010004000002801c01c0000000008008000000801400200400080180000010050004008005002000800a00000080080000020018004002000005801800601600200000000050000000010000000801800400d0000004000003002004c000000004800800000100000200000010010004000001004800c000000007000000201e000000800c00700000000420030018060002007000800c004001002001400c004001800000e000000002000400c000000400200200080000000070000000004002000000000000900100040020080018000008002002000801600c00080000000020010024000007002803c00200500080040000000008008000004002006400000a0068010004009000001800400000180040060020008004008000001800c0080000050000006000000000c0040020000004000006000801000200b00100000000030000004002001001800c00000000100000000000020000002000000800000400200000000040000000000018004000800000c00100000000020040000000008000000800400800e0000000002001000000000600500080000020000028000000000008000c002002000000000800d0000000004000002800000000000000000000000000010004002000800000a007000000000e0000050020000001008800000c000000800000400800100000000010010000008003001000800400300000040020050028000006001003800000c000000000001e000000001000200100080040020010048008000002001800c00c01700080040020020028008002000000801c0020090048004000000000800c0000080000008004001000803c000000000004000e0030000000000010000802400e001001800400a00000180000020000000008000002001803c002005004000c0020030010000002009000001c0000000050004000006000800c00a0040008004006000006801c0000000030010000000007800000600100000140080000000000022000000801000000300f00000000010000004000000000801400200200100140000000000008002005000800000000100180000000010000008000000002000c00c003008000000000000
  | 25 => 0xc90002529da000064c1968ddeb9b00013740000000000000a240006d6a9486ae000000129c00000059e000000000060080000007240002ae1d3a0006eb800000014a00000006f023c2fa92e4e042f9251af0191a90210a26a52cec8a64aa3d1b22c3900024a0c00f143f08001af60005b4800000082774198ed3ce00050ebaa80007d938994f518c3696e79d7000087b3670374a98286393864916c81252b1434e46457552b338278000000000002e26e0000000000a837be8001df01b779829400000000001100000000000369000000000039cc00000000002e5d7c0000b100006ac00000000000000007778001be00000000000a66bfa780800000018200000000000003eeaeccd1c0000000000000000001c006000002000800801800400000040020000004004018001800800200000000180000010000004004000000800c00000100200000000010068000004001000800c00000000080040000000060004008002002800000c005001800400000a000000000000200000000020000000004000000000000000200500280040060000010000008001000800000000200380040080000020024000000000800c002000000803800e0050000018000000000000400e00100000000160020008004002001005000c000006001000400e000000800801e013000800000000200200140040020028004004001001000c00200400000140000000020000010001000000c0000080008010000000000000000400000500000040000018000004000000000c002001001000c0060000010010050000000001c008000000000800400700080000020000000000004000004800800200000000180000020010008008005001000c004001000000c00c000002800800000000100040020010000000000000002000c00200200000100000030000000002000000801800000100400140040030000008008005000801c000000000800c00a00600000180000060008000000000006000000800000000040020060000000000004000000800400400000080040050000058002005002000000c000002001c008000000000000000100080140040030000000000003000800c002003000000c0000020000000002000001801c00000000480240000050010000002000003000000000000080080000000018000006001000802c0020010000028004002001001400200000180200020070000004000001000800c000002002000400400000200040020010010020004001001801400400300080000000020000010000006000000000000400880000000000000018000004000800000000200080000000000028000004003000002c008005000001c0020020000008000006002800000000000000140160010008004006000001000000e00d000800000400100180040
  | 26 => 0x2b653000000000000006d0b7f84f20002668000deece726e00000000000000001f02000000265800062200000000000000033de011c3450000b0000000000000000000000000001d2000071480008a400011aa55000000073c00008caea800000000000000000000fea00000012e00001ac4b680000008cc33f8000000000000000077600000006acd2600029880000000007a900000001a86240000000b3d0000001186546000096c0000002c3000077c11600000000009f00b900000007b60000000f90000000000182648f4652ea18cc637570b99952e1c1698a6bcde40da2e32cfc2be0000001d3509c0002769fb4000188000000000000059000010f21e54ec125102a00029000200000006b38001a567a10001ebc00000006817582c887400000015d40000001880f2200066d3dc40000000000000000d263a32b31c640000000c30b4af6f446891c93e1d67d8800000029d01ba0843b06640001d080000000003a708d682c1de800000080b0002f91dec4141ae8d61cc800000026ec78600000017e00006b93f613e8000000000000000000000000008c6a934550000e3ae33659a4404ce0006c20434b16da0243216c00062e00039591321225fc8ae400000000000000000000dc8001d7e00000000000000006cd8001ac041128d000057cca917b000000000000039f92ac2b031e800119a77630d0fcc380000344000011a000000070c000d6a415956d60a000000143c00000000001cc000c386831058bba2f058302ec5e86c75d89c2000000000000000000000b080000000000002159686000000366000000052a372572a4ff28c2448000d68540b6b05d00003d5b2e0000000642244d5ecf7659b8000000b8042232040000004e280008a6af14f18000000f3104d0000000000000000103a00000034483ec4ab177b77c0000000001c50638de0000000000000036d800000000038904ec000000029b7617e40000000675edc000000000000099061389ec6960001c0800128e00068a00000004ba2160e0800000000012246a4d821cb3c9400000000000000000000000000000aad39a8000000c176698000000cb600000002480000000000000f1e257a00c0007a35d09504b8e1684a4b2417140000002d180006712648000076f74351000107a011000000000000000000000007c0452a7b43f87771a70ae8c2461c11c8b3d928c65752061dc223ee10daa74b2aaf43ab98c0000f423d11b28c020001d1000000025e0000001f2c8f53139cbc000ab600000009c600025820a80000044489d6d6e80c208e81a04ec4d8219ae34f6000000000010fcbe20f89dd400000000027e4bf89d714700006e66b300018e903400000007881600de523b168aee8a900000015d8000365800000069b00000004c40000000000c9600000002f5564b
  | 27 => 0x7e02a7a70c0000003ed0000ac819a00000000000000001510000000000000000020458e93106b44ce0000000e125217d185e80000e50001cb0ad28462f636040000001b625dc0002230000cbc0000000001f1930a0000000ab00008c900022f03bcad600000000000005d58001b1e6ea6bf81f960053275184696d600000016e400000003b80000002d400000013680001420b8400000040b80014ba8c21318001c1a42519215200001a44179b50e2ecac00007f40000f92d680000004da00000000000001400001d3cc2074b8001d4e0002c4b738cac00000000015b000000022c577639474600016a000000000000000005740fc4c2a000000080c0000005258000000000482313c96c0006d989b563c17029c1515f367ff0000001e3e0000000001552000196b4550d200000029ad038cf100000000001eb3c18000a0ad2400031dc122c7d68eb4701d24fc4be000131e0000003d3d270a8f7c5398893c00000000000003e80810ac900e0000002cacdca46a0003a693100004343341884b100848a4dec446600000000000004280001d9400000000009f200000000000000000000aade5046200035b8000f050000000cd247422daca8d5c000083ba54fd692239483ecd60000539a2140002a108e0c600000000002c99a6023445e80000000000000000000000000000000000024200000005ff0000001c3800000000000000005c3800072a0000000001b50bf100002bca6c000000260800000000036ad13a00037880000cc2980000000000000000000000000000034a800000060a000163600000000000001f078d3cdc00009c7b800016fa0002f08000000f3e2f100017723cd25e0a88000000000000000000000000000002a50000000000000370952d3a000000000005ac71546f80009500000000000000000000000145200007587680aa79c122b57d950000426240c0000007b48001c460000000000000000000160c00000074a00000000000000f78000000390aae8fa4000647ac55cb637b42f25300009504298e20622bd708807d0e340000000ab400060f000000000092300000001046cf54693a9e24ecb00036b80000ee00029b81fa2811660000000efd0e72de80001ca0060000000000249800000055f0001c1400000000012a44c80005c09320ce4b836d90001be66ec439adb92e086c1c62b040000004e7000007e79b71a00c4b0e000505b59800042135b2bac4148fb12b2c4c00033f0000001c060001720ca11f800023aaf8453e7a600025780007f32d900005fc04f45c000000091c0001db00000003aa800000005c4641fe59b60000002e50000000387800133a0000000001218b1837fb839848e8e00012080000006ca000000059900015608603a40001cb9c72dc73d9a9bc31c21d79015c9b900004378770000ac30000
  | 28 => 0xbd9c000bc400006d9d58e75201b6140005ea0002899688d080001bf405c00000034440000000003cf00002b44b7000064aab017e8000000000000000000000024c02d40000000001724000e7b00000904b00000000000000000000362117654a0000001c900005730001d0c00000007b446c0004328000f88852000372800000028711f00000005d3000000057c0000081b3c6c260d0000000dda000000112e0f406430e80005ce5960000000000000012d3780000000001322000000000076c0000651da40000002070001c9e00000000014ae1aa15f99b4000d725368fc80bc1254100c1d89af385dba48465600e0499294000b75000009852c1930001ff434c4e0148000157a0000000000b960000000000000000634050800000078980000000005b20000000a48000328d31619913bb8fc0c6f8b1e38adc2521b100000000008133ee1cf0d1a00000008c8e16f2155a144c0000005713e7d3acae70002b6c000800239146c00000028b0d700007620d12969616f1d00000018e624b0002ee9412000000000000000000000000008641868000000fba0000000d5e7ef3e580008704e97612e88000000000000000022f0000000cb22ce00000000000001b08be8000e090001f41d1ed2f000037c0007c342e80000000f500000014283f7000197812c000000331400000018100000001566fc0000de047d24c8001b7e9244830000f30154000000000058a000000000046800023a8e020003a180008ec000000182dc20a7c0000000000f0f00000000004f70000000000000000000000045e1c284ad1bc22b04088cd108f870000000000a7700000007d40004ca0000000ad900023b54b00005fe00000001443c98000000000449af08a5a1f70002ed000054e6c39b600000004f63c341fe58d0000001c3ef3600009bc5dc6ba0a8904c00000000000000000ed4599d0400000039980008a80653190000000000000113c0000003600000c86e201cb80000000001538000000000000000000000000012451500000fd9b897d8000685a7d54a60007af04d400000000000013ec25d43880008983fa000147c6bc0000000000000000797b6640000005173208d2c30f4ba00000003c82d481bc000c6c03393f4d1800000000000000006780000000802000000188e4f542088a42b058463e28052ae190123290c000b5d6530000000000463800178a00000038e96ac24c24d21d800033000035bdcc280548780000600006cb000000000000000015ea0000000c9c25a8954418c6920aea11348c504c28b53d6ae316d8e5200007a4000f2b1c20000fb6e0a103000000000000013849e2df22eb8a6ceba1c5000000000000075332680000000000000000000348aad40f20002409319ed07fe0001661988baf000112426200002827640004d95b1a06d07e
  | 29 => 0xa39866fb6717c60f739328a8a003d458fa624beea116b08000000000000222800000d3a92f280000000001ea40000007d7000000000000015700000005c4800000009f0000000000000000000000000000000018a2fa575a8bc80000006e68c7400000001c8ee4c92bf748888840008817d8095c00098752300000000005040ce43a0350000000029055a426affd25a8a12360878a207721221034000a3a00002900000000003654000d1f67eadcc636085000072c0000000000000a5cd050001cc483438d6178dc492c00000001a8cdc6b70000000c8480d00000003060005b80eac0000007db9111a181e000000000000000003641cfe000191b675dc40006e9ac94948000000000000000000000000f87ee000000000000043e0000000000000000128a3df00007740000001302b1400000000000000000000001721c36d280001650000ea90003c99e68ae066b80748e2cca0000000000000225917069e4640002f4c1ae9250000000000cff0003dd5cf8515196000000000051180000000e472c38ec00000000000000000000000000a1000011800000009750de000109000000036240000004cb974103062b7008000000000335ad00270000739004c2d6000424af2d2f00000003b614be0003d000000008b900000000000000001ab000000000018d9916b27661aed9b840000000c180000001a503e0000000388b745c0a000000000000000000000000000006f580017320005bb8ee9bac00079f800107841f1f21a5da709ab0003b10000000000061400000051a00000000002f4800154864d00027f99d2ef500037d97f0d1600000000000000002499b1aad744e00000009ff0002f04000000295000041c0000000000000da760b00000000000000860000bcf0000c20000c2900014d56346fe31c2ca400000000000000a4e265af9134d1e01f00032380000000003ea5f680ec00000000000d91d3b7b8000886000026400000000001640ac0000000001746aaf00019d80000000000001ee60000000000578000594000000000000000000009cb000000000000000000000000007a4800189800020c00006ec00028f00010f40000003af03e60000541bd9b98df50b1b2d095ceec5338920e08a4e0002fedb185b4000000158e152020a9d01c20bc00000000000f25421c01ac409b0000001160000180b96400000010bbb80000eaf0001e3063c21c5cebc4420c26a3cb0e84f646580000000000000000122cf246e400027c4000c594438001c9cd52368379400000017c00000006d36522b0027ce6d4d6a908aae28a45380000d691b2598000000e4500026780000000001af4000a3b6a01e900002120000000000dba283b000000000023000032e0aa1ff92f575a0000dd1e9c3fc3465ada3ddca01b300000000006e73f2b6c0000000062
  | 30 => 0x80201c888a30000000086c1c00000000008d10000c41f0600078418e4ebe5ab1a097d891000041402182266ab0000bb521cba9657213dcbe00000000000000000000000b76f041288e94b3800047218b1ed8c807de000000000000000015f4a5b000000073a000538000073c7b50002b4d84a7f23fc0e7c75ea862e9ba65dfe5473a48bec000a90114310dc0400070b800169062139d0000000a320001db488e0000589a551b63e50002f7000000010100007000002b12c04000a711bb958dc0c492653a5603b64cb0000000000aae0000001de800041190dd632f4654127f4bbcf2e4e90708012bcd4390000000d9f1af80000006756202cd0000f1900003452e218c000000000000022a8001dd0c79000184c79e000471b888de80003623400dae6f55f4a26cca28293db8938b18b235cfb95088423e3eaa85c48431372b8f5d7167aa7722f7d9eed5d38c1824000593000268800000000028789d0e9341c00013189db50e00000007d30003530000000000349d9542f5202ba6c42000000000000000000001ae197a74a00000011960004060c48000ad13c6b1ac00000000000000004a23c110b800000032980013de6f9000130cd4ebfe0000000000000000000066c00000000000000000000000000d1316d800000000000027a8c9425c42e0000a04b655d600000000000000710000000352993d6b400000003f90480007b68000000737000000067600000013c888200000017900007bc47c3cb00f45bc63100000000001aaaf613b4ce85d80000d9ae5a000254927c000587012800000b000000000000000000019cc1ad06a975043400079e8000d7e00041c8000d0600000000005a000072f000097eb6200002e969400028490adc6a128000168173c0000440badb6867a1aa01ec7f83c466f33900003ef68381fc000d33199977d95e00000031b8000eab1e580003f20000002161c5e0002918ac4000000014000000000014d000000000000000000000000168000000b0d7db206442674000000003ce00051f31e800000031f3c540000001952cd8eacf07273b99c00000000000000000005162a9c0001605908a8c2dcec32d51d109de000000000093a0000000000000c850003578b461c9247000000097f5198f680006cc6a30000000c332ac87209d88610002d70000f170002b28f0e0000732ed5c540000000000bb000056900003a20001990000000dd50000000000000599acbd4c00005e71c59eb00000001f8800000000012299ca0000000ff4b800000000abd6b2000000217c0000000000001644afc34fbcc8a3804c1b524dd0c03640002d55140d9375d000000017e518bde9bc2ba01ff1e41c00e2718b23c882000061f96046e810f00c82dc000c36000048d6f000000000000000000000de4000aef2372399b523f40000db4e8
  | 31 => 0x2bfc4700002dd0000cf8a7f00000000001570000d10000000000000000000011204cc0001ea0003700ba2000000345d04a000000000000036b1610f4800029116e0854fac0000000b78f8a27a00030a8000b3500000000000006ee09fd0d450b00024b000012c392975553241b4d5087cf4a4190002509b7c93a0be2d605e2dd9174800000098a0000001c50f2d73b30380002aa000160933893d0000000000000000329571ca755df2351f340001739c8800000000000018ea00021ea22caf2000641800000000048431e0000000000281d9781a900029f40000000000000724f00000000000000037d176400000068096f45c63cc16d0000000000000000025e000510223c00079f0000000936e2576b8000000e6b0003b3d3b836f0000ef060ad557ab94516721401d022f8bcc00024b9890000a510000ea5eb846149000000000005b780002f000022cb51cb4ee743be0824fb00000853b98000000000000106a3d64d700000000007bda89000074769b8001b0c2264e30000000cf93e130200a805d00035e97a49b87440c11ea00002ae97d000000066b000000001b0000000000edd71b22bd754c0b1da000051600014a1658c6a00026931ed0b298e46e0001a9400008a800000000000033bd5a045600007fc0000000000f0907c00009fafb523e5010000000af604d710a050192000624b464000dfa0000000000b530003e200000000001d80d68000000000106800007b0001a7aa8b0bfad1d18a16c540162126a00073ea564a92ee50002b2dafa00025080000000000000000872fb31d98001c30000000008c000e980cf103c00056d00000000000001752fa9bd416a7a2000c7e05600eb9eec0001b81e71fd800000000000018b80005500001e66b04610b740d5a7f141d381d1f410008d834c7f000024aac09a9200035514e5d9200000000000005da000387400000000039e82180000001ba0b9e00000000008b4000322911884c2992d300017984b42651d7813a111781197c00e0002da800000000043c000000000000021b40003170000ec4000c197c83c2c59615a38fb5d4000000000297807000070222c946099849f9f30e7c0005533ddc00000000000000000360000000000c601cd00000000000000000000c2b5b085d800094b0000ce0168db900011ccdac0f000000000007f40ce0000000892000000056c000345ada8ae8667075210100c55e45a020c6c45cd1038000ddc97e00000000000003ef00018206a1660b7edceeda50002611bfe00000000015a80000002e082740000000001e360000002aec000efe00000000006051c8b48c0003d81760000b5c0000000000be408f5c280007920000001000000b840a68001d24f4b18028841f80000000e98cdea6c0003c38ff670d000000000069a5c7be5000000044
  | 32 => 0xab00019c20000000004ede00016fba8000012e000326dcb8dbb4a78001c920000003a04c1ca640000000000000000000000074c00000000000004d8a831ab40006c5800000000000023404e0000000000000000000005380004b500028ac00053e0000001ab0eda00000000000000001428d92c71067a3ad90ce4c76991c11d8c701340b25158a6100024cd32a8f0246884400014c7d00000000a1f7181b0c00000062a832c0000000003c9d37ade835e000000000050a9d2c0000000000001f2a00000017b8000d3a50d000000077b0001970000000323006965c43573700010ce000000212d53400000000000000005edb3acadc7686768000b580000000000f500003c005f41864b2172bd3561e0000000000e7000037e028c37e0000000000000e4712980017ea00060c00000000006a40001d7600034480018b0000000000000000000026f800000021900003a8000000000000000000037c506e9d152036016f20000000000000f3908703cc000000000163c000f0675c0000000de2000000000080147413916f6ef76fa0fa4c9c1e47a18000000e5312796cc0000001c1a60c000b16522988c83addd6e22859614bb8269b08d29cbbd2a83104bc0daf0501008000785000270431200000037051f2c6d58b80000a2000000000000000000000012ca00000000017864f33fb9f5000034d066b7912ba5424460c84f167ac39ea45c6125800000660000e2d68d90893ccd2900000000000000000000caafad000047cdbe1951a9bd740000000000000d149396798001c3c0000000000000000000000000002c000277587c00072100000000007c6015d57200000016a0000000000000023c8e0000000000000000000000000000001128ef428c288b62800094360306bc88aade00009400004fb7c98000000cee000000000000000000016bc0000000b8000072d000246141e000000000000000000012411de2f30003c400004df0ac99756d0b7104a3504b3e61b629036c0009bf00020410c62a476f000012ee894f03e35938eee0fc2b713ca127762b1fcc825e749dba1cf3252c7aa80007ba00044a17bc000000266000000072a00028e00009861b194a0c06d1e49a0000000e3c3850efc57ab070000001b7af8900000002cab54000050c0000001570001a7c0c1000000000000000000011b00000003551ebed7300000017e8faf0000df95300004bb067c000297000177000000070a8000cca4485b00000000000000000010e0001e9a67c0000007a030c800000023f000000000000038f80000000003d6c0000000000000e68000000196ccee0000aeba0800000037c00000000000003128000c6a000000000098d102800145e1b404c279045800000009f0802b3153409005ee32e5110a0d7cedb77bf0de80b4f416168000b6e0002c800000
  | 33 => 0x4cad3f0a33820000000030000152a4cf000187c0000000000001c9615e0001b6515c8ee54900007120002bc3b706e0000567000000040c0000000000000000000000000000019f8000000649aeb8000000000000162400000005700005b600000000000000000000d6a4274198000e64000000000113e0000000000000000000000000099900000019b213735d9b98dba00069e0000d6253a2378000000d2d00000017e0b976848000000c356ef2b90000a370000df40006440000000000000000158581a00064f1d203c26070000f540009a60003e140000004601648e1c8fd2fc8c288549d300000000000005c88484f2a000000284800043c000273c000b450001d65daac110000001a4a05f53d27e8a0c0001dc12a8000eb95349ef8d3a0e2383b8f59a4c7461329e554200054383bc0000003c41a19e943a36bb3d8d17400012900000000004212aad3bce246718000000d353cb80000000000000001290b570003ca802c00076a0000000fb852233e1148ece6feb53987600000000000000007159081a420000000000000fa41390000000cea09c80000003a800a000199aef2526068c8f400000005d00000006c70000da28557302044000000000000000000057f000000074e57d9d44bb6ee100000cd3dcb1c60f8299af2c306f49298d7c56560f000000000068795e80000004c933d400000000000000000000003c580000000002be1ab60000138000f12a106018000000f7f77e00003c6b7e1730b350aeac4709000000000000008810620000000001e8a2a04fe0000000b0c1be0000000b2d00025a8000ccf4712db4ace000000000195a0000002f20000a190001de0b3a20f65b9fe80000056f7a10c17ef3b54500013469d500016c4000e2c0000000044a8c000253400000046eb7500000003f380000000000000001522eea64f90f8fd22434078000c2887d26826a06ca68114788059920000d081d000028800000000000005050000000a6a0000000000f0a3a7b40c0000005a700015bec5d00028d50ea628000000056ae7909ead3cce60186e2afacefe93c01296389821843c3353d1b400029584159ec70367da400bfcd5372aae18566e845de00000000000002e71d0000036f0000632c1b292a8e5f766483ba2128000730000000188cc575e819edf5600000004607c61bd00027ac00000054f80000006a600019998be57f0000001bda00001900019ba6840fa833803ce2e745aa209bc69200000010a20000000000fd40d8000390c0000005d200000004060003264000c631623bc0000ed130324a8000000644800054cbe81b30000ec6d57480a6b13e68c10002685ac81bb794800000068552080012280000003bc598022251fb7e4ef25c41b92f94ca84080091e68ce8a9e3f2220972462d25d9145878cbb1f10000000f826
  | 34 => 0x4a0012556e000169b7b02ea4f800013d140cd0e1a486c08be90b0002fb9d2c00000035dd1b262900017c40000000000000000000000000078a7bd0000228000cc64bd8000c1800000000000000004fdb648a7e58500026dc0003dc00000007a2fa805980016a4537000000000000021d00018501cf75ea225ed48d500017a17b40e8308919c000ead243800193aec6000000000056f41826e926261633c029c000000000000000000000009f80005043310a2400006441b00000006265e30000124cd46b5bde445caa870780013920002aa800000072066a800000000000006340000002f9b68880e0000001b200006982429d981f4295748800000067d00004484faef93b20f6d8c8ec84d22385eac62a6fbafbd7c07b90000000dd23b70000000000b3a0000eb07d60000000000e388c40001a40000a4f351b12c8da00066606804180005eb00013d279e00000000000000003864afc0000000000000f2408235d085e4363c7a0b88760006dc00000009b35a4a34c0000001858b4938e000650000000095a022351000000034f33800000000000000fae0000000d0800000027f00000000001b700015f2daa72324a40000000000001956c6f26380f8c3089605c195df6a04700000007b20003630d1c67c000281876546c00003c0b60dc65b80000000000d9a1fc9cd9b7800047396bc0008450002750000cec6e30000aac0000002c247322780a280007da00000017489dc0345ef2fcc00000043ba5e4d503ec0000a4951c000000066db62000000135dec018f113b8e000096c0002af122cc910002544f94c0a3c52e400007fc79a9358b3c00000000019e40005002198ed40000002a1400042d39f80007ea000732800000083b000000053800061eb514f829f87c780000000000000000000000000136c8380001208001696000000000000000005931d8662a634670a1451a95f0003944000c4400000000000000000001dc64f0000289c00000000021b8d8ab7c10580000000000002971ad23b00001df4782c8c25bb2c8b480002d810107cc9e20001ac80000007cf19c15383031ac99480da02a000000098029e354a58001400000000019fcc310d3a4ad4b200000000000000d428c9bb41420450000000000d220000001d804805c400000000001a18000000f0c5ec82b4c4a76b4cd8aeca482c70000000e20bc72148ae174e0005cd0000000eb0000280800019160380016604ad1913308590de34e4000800038a0003e616ce000000000000000000009547800c00000000586b380000000b36f6b76f8000a52000404800134a96161b800188a663000000000000000000000004120000000000000000000000000045f80000000004b2000000000068132852a60000001688f7400033cb7f0000ec10001dc4000000369270185c0000e38001
  | 35 => 0x6113319a96220000000001e060000000000000000070000000003c1f0b2e8000000154b2e458cca200000000000007d91f7c67800053d9ee0000770000000000012600000015dc0005bb2680282b0862d8001db28ad00026049ecf654e23e10000bb258a00000000000000000000ac921200000005a170d1c7863e0003f400000000000003bac0008627c328f400000011d9498000000574acc83dcd710001e050d60004c00001c262490380189406000720ab68000cfc663ba942cc00017f8001a7200023000000000000001f39558000000000000000000029898187540983344020d516850540000477512ad04a8616f11681d8000ecd6a105a4000e4d0000dfc3cce8d00002f8c7e0002f83b4800000000000018681c62612bb40000007cc800000015500000007cea3c0bc8000000edb00017b4c80eb20003ee4000634000284db6c0c70000000db4f800000da0000000000201000000000035e0d8257d00000000005400000001ae0f1c1adaefdc18650502182025488800016f862ac6764bbb5846e55239cabdca5e47800008a83f400000000000fad3b696187559a33503ab8589629735a680019b000000000000000000000eb800056a00000000009c2000000000075a6580ca4fc600009b000000000000025ac00069956780008b000048aa64da6cd7e5550001a8632666e00bc7a0d3270a39c0000c5029d9d400560000b699851e26317a6324800095c4f08000000000273000000000000015d53e4000104000000000000000000000000002435d6e1323b999a000080e1002f55cd200000008944be4177b208650a80003ac00008feab160900009aa597000059c3aa00012510a13e800008080000000000000001288000000000015c07132605edf428a600006b800038f0002dfdef8e680000000000000071a5bd7ecc7e6b6397400000000002ac000000000074c000000000211c00003d690000000025900000001a40002860cf400097259201a400099a4b3000058226578c0fedb0608b4b1a4d8ecab3b3022d45c62000000000036ad7c5818000f7e00000000000000007748001e8e4230003acd58c72b000178decce6368d1eb80000000000138d40000000000183af727a724c800000048e8000906abe00000011ae000375800000000000000015ba000736000000000000020982e25fd00009b11fe23d2a9a6e5436000293ba7da680006a680000000004748000b348984aa8f1980a2e24511315e74fa630f042c00039c0003088c3256b7c7000102c000000332dcd408431e00013be2dd00000000004be3e3860423206c0003ab800080800031c9d9800029a00012fa103250233c120b423b7016c93800052680003160003b3af98aec1a527109cc73646908b8b5cc2e5bf616273081468236aabc00000002912814328000
  | 36 => 0x3b9c0000004d900006ce1cc084365c0000000a7b58ce0c9e80002029808a2840f000174af23000045030044e0000000000dd20372e58df68f313a00008ba0000003a2800051764400017300000002728cc00005b90000c04a4900028600000006a5800000001c42d0934d0ec61204b009536cf47d5012014414906b1230000f095c98cd0f920006640d205a25730002bf40000003da31796cca89634b68c7ecaa33e6973134e0003bf21fc000a550000001156000000000075a00077d800157e7840460001f22eb63080311d6200032391e43640a9493a51941a275000010800038b53f2734f3a0004970000680dc30c5338802aab32e10b64e1800000024c105a00000000000000e76e58001f2e60d0000000a9a5510001e5076aa7800000000000003e880000000000002b9400000000000000000000000000000000000000026869c00000000005680000e41aca73b0000000000f5304480000006940000000a3a00000038dc4b415300001000000006f30000e360000000000000000440074990e5c11068e4c958f5a0003e89c9400002c15b00000000000f800000000001ca1ea21f246b1ec40e4b4c00000000000005642bc98a6ad5000000000066c1412348bd61df00006f9d686a40a5902c0000001b02a5800000048500000000007c90001f4e00034026d40008b72e28000de60000000000ea6000484800000000000000009ca88e00015c05502314b40d300000000f4155070c0000000000000000063382d0447f0000073413c000742b4b80000000000000000a2d317a6d8b86efa507000079492f48cbbb52f4000000135000000000003c40005fa000000000000012a0000000a767ce0000000ec70000dd400003a20aa5880000005250480f9ebdd62725a523433a533000181e89e00000000003aa75100004747e606e0001eb29f720f00015280cc47b0000e3200048f315850e000218800000076144d00000000956f39e38dc0d1860aa41c158cbe1c735648685fb4ada3f8b94147268beb192c38700023950e060a23d8d4414a0000f632fc76419600000004e2ef321fb2c4000c540003d8528217300018cc0000007ce80a4000177720000196a00005b302554481f000000047e00000000000000000000001ce20005feb411a2000053935400000006da8000bca0000000000000000007b9bc0000000000001ab80350000c380000004d836999f426b29e16445f80005798cdc04200000000000000000002f5058ad0d0000000000f48000114000000016abd50db80000000c800000000000001bb64eb0000000000b3e0000001e442ca56120c80002160c300000000000000001adabd12b880003de44300000000000000002b8cacc000000000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc3f655d03244001878caba064880022fe1f640c9100045ec3ec81922000c3e75d90324400187aebb2064880031dd96710c9100063a32ce21922000cb7649c43244001968c9388648800e3d219710c9100063bb2ae21922000c74655c4324400196ec8b8864880032d191710c9100066bb1ae21922000ce7625c432440018f6cb38064880031e196700c9100065db24e01922000cb8649c032440091f10cb8064880031ed95700c9100063c32ae01922000cbb645c03244001970c8b80648800336d8d700c91000675b12e01922000c3c74d95314400117d0dba262880030fd97744c5100061e32ee898a20778be87d9131440e71790fb2262880031bd97724c5100063632ee498a2000caf64dc93144001958c9b9262880031bd94724c51000636328e498a2000caf641c93144001958c8392628800333d8c724c5102f666318e498a2000c7865dc131440018f0ca382628800a1f216760c5101443e432ea18a2000c3c645d431440010ff0fb2862880321f61f650c5100061f3aec818a2000c3d75d903144001aaaea988628800395d95310c51000c5e424ed90a2000c3e74d9721440011790cba642880030fd9574c85100061e32ae990a20008bf87d93214400117b0fb2642880031e19670c85100063c32ae190a200287c859db30440010f90cbae60880030f19175cc1100043fc3ecb982200087d87d97304400187cebb2660880030f5d764cc1100065a324e39822000cb4645c730440010ff0abb2608800a1f215764c1100045fc22ec98220018bc845d930440011df04bb260880263b209764c1100043fc2aec902200287c855d9204400117f08bb240880062f21176481100046fc1aec902200a8dc835d920440010fd0dbaa40880030f19375481103b43f43eca902205187c87d95204400187eebb2240880030f1d764481100062fb2ee69022000c5c65dcd204400193ec9b9a40880032719373481100062fb28e69022000c5c651cd204400193ec839a408800327190734811028666310e69022000ccc73d8920440071ed0db8a40880032d19371481100065a320e290220018bc849d8204400187ce9b28408803e2f21974081100061fb2ae81022000c3c655d0204400117f0fb20408802e2f61f6408110006d4ba2401022000eab6448020440198ecedb2c208802f2d9db648411000477c12eab1820098ec825d563040071f100baac60800e3721d5358c1001d6c402a6b1820038dc8750d63040011bf06ba2c40802a3720d74588100247a40ae8b1020038ec8754962040071d90ea12c408012b9205425881001c6e43ac699020038ec8758932040131eb02bb064080263e601760c8100063a3aeec8802000cb474dd910040018eeedbaa20080032dddb74440100063c3aeec8802000cb874dd910040018f6edbaa20080032eddb7444010
  | 1 => 0xaea324c6880021fa1f6558d100061e3a6cab1a200087e871956344001878e832ac6880030fd977458d100061e32ee8b1a20008be87d91634400187eebb22c6880030f1d76458d100045f438c8b1a2000c3f751916344001878ea322c6880031bd977258d100063632ee4b1a2000caf64dc96344001958c9b92c6880031bd947258d1000636328e4b1a2000caf641c96344001958c8392c6880022fe117558d1000c5e422eab1a20008ef825d563440131d904baac6880023ee017558d100061fbaee8b1a2000c3c75dd163440010ff0aba2c68800a1f2157458d1000477c12e8b1a20098ec825d1634400187eea3a2c6880030f1d47458d100162e3aca6b1a207bccc7294d63440051b90ea9ac6881eb331c95358d1000637baee4b1a2000c6c75dc9634400195ee9b92c6880032b1d37258d1000637ba8e4b1a2000c6c751c9634400195ee8392c6880032b1d07258d1000667b98e4b1a2000c7875dc163440011bf0eb18c688002b32096318d100061f3a6cb3122000c3e74196624400187ecaba4c4880030f19574989100061f3aec93122000c3d75d92624400187cea324c4880030f5d464989100143f436eab12200087e87d956244001878e9b2ac4880021fa1c65589100061e3a0cab1220018be86dd1624400187ecbba2c4880030f19774589100045f43ec8b122000c3f75d916244001878ebb22c4880022fa1c64589100061fba8c8b122000c3c7519162440018becbb9ac4880031719773589100064fb26e6b122000c9c64dcd62440018beca39ac4880031719473589100064fb20e6b122000c9c641cd624400117f08baac4880062f21175589100046fc1aeab12200a8dc835d5624400187eebba2c4880030f1d774589100043fc2ae8b12200287c855d162440011bf06ba2c48802a3720d74589100047bc0ae8b122000c3f751d16244001878ea3a2c48800317dd773589100062e3aee6b122000c9f74dcd6244001938e9b9ac48800317dd473589100062e3a8e6b122000c9f741cd6244001938e839ac488003331cf725891000e563a484b122079ccc7390962440031d90ea12c4881e3331cd42589100065a3a6e2b1220008ef87588624400159906b10c4880021fe1576cc9100143e42aed99220008bf845db324400317908bb664880021fe15768c9100143e42aed19220008bf845da324400317908bb4648800a1fa17764c9100043ec2eec99220018be84dd9324400117b09bb264880021fe15764c9100143e42aec99220008bf845d9324400317908bb2648800a1f216760c91000c5e424ec19220048f4819d832440071f1013b064880021fe15760c9100143e42aec19220008bf845d8324400317908bb064880021f219750c9100061e322ea192200087f87d9432440010fb0fb2864880030f9d3650c9100045e432e81922000
  | 2 => 0x9764c4200045ec36e898840008be8759131080011790eb2262100272b1c9644c42000657326e49884000cad64dc931080139c8e530a62100030f991750c4200061f3aac81884000c3d75590310800187cc8bae60100030f9d564cc0200061ebaac99804000c6c75dd920080018deedbaa40100038bdd56448020007163aac89004003caf705912008013d56e0b22401000faa841644802000667bb6e69004000e8d64dcd200800199eec39a4010003531d4734802000746b20e690040048dc8754d63c40091b90ea1ac7880123b21d4258b100246fc3ac7196200ac5e635d432c401593cc6ba06588003175d5630cb100064eba2c61962004cd67158c32c40131f70cb80658802b3698d700cb100066cb1ae0196200ac5e635d730c40018baeab1e618800e3721d5358e1001c7643aa4b1420038ec8750962840071df0eb1665080271b989750ca1004e57312e81942000c6d75588328400195ae8b10650800f3a9c1620ca1004c7bc32e21942009ce6625c432840019cac4b8865080272b98974c861000656ba2c590c200087d8799365440010ff0eb26ca880029ba0864d951000536c10c9b2a2000e2e821936544001c5b04326ca880038e60064d95100653b436e3b2a2000e3864903654400187ae83a6ca880029ba0874d951000536c10e9b2a207da7a801d365440014f3003a6ca88003175cc73d95100053741687b2a2000a6d82d0f65440010fd0e21eca880021f61c43d95100051f424e5b2a2000a3d849cb65440014bf06b96ca880029720d72d95101c53d406e3b2a200087e8710765440190fb0e20eca8800297a0c41d95100052ec1883b2a2000a6e8210765440014db0420eca880029ea0041d95100053cc0083b2a2038a7681dc365440010fd0fa06ca880021f61f40d95100053741081b2a2000a6d82103654400187cedb2ec8880022f61e65d91100051f42ccbb2220008bf87597644400153d0632ec888002a760c65d91100051f430cbb222000c3e761976444001c3d0632ec8880038760c65d91100071ac08cbb222000e346594764440175750db86c8880030f5d475d91100054f418ebb222000a9d831d764440f956d023aec888002ad60475d91100051f42ce7b222000a3d859cf644400155f04b9ec888002ab20973d91100070fa9ca7b222000a9e83d4b644400153b07a96c8880022fa1c52d91100045ec38a5b222037aba80dc7644400117d0fa8ec8880022f61f51d91100054f418a3b222000a9d83147644406f56d03b86c8880022fa1c50d911005c5ec38a1b222000a9e83143644400153b06286c888002aba0850d911000556c10a1b222000ab681143644400156b02286c8880030f9d36598d100061f3a0cb31a2000c3f655d26344001878caba4c6880030f9d76498d100061ebaec931a2000c3e75192634400187
  | 3 => 0x31a4000e8d4250063480a159d04200c690002b36084018d200052fc2a4031a4000a5c8548063480159b0c738664900031e197704c9200063c328e09924000cdb631c132480131f301baec2900072b9d142d852000572c1083b0a4000ea54210761480015e30020ec29000317d9673985200062e32ce730a4000c5f655ce61480018b8cab9cc290003179d763985200062ebaec730a4000c5e7518e61480018baea31cc29000a1fa1b75585200043f43ecab0a4000c3c74d9561480010fd0e32ac2900030f1d065585200061fb2ee8b0a4000c3c65dd161480018becbb9ac2900031719773585200062fb28e6b0a4000c5c651cd61480011bd0fb1ac29000317dd763585200062e3aec6b0a4000c9f74d8d6148001938e9b1ac29000237a1c63585200062fba8c6b0a4000c5c7518d614800193ee831ac290003271d063585200047bc3ac230a4000ab48458461480010ff0abb6629000a1f21576cc5200246e41aed98a400acd8639c331480010ff0abb4629000a1f215768c5200143f42eec98a400087d85dd9314800317d093b262900022f612764c52004c76410ec98a4000c3c74d9531480a38d8e5b2a62900030fd97744c5200061e32ee898a4073c9c63dd1314800193ee9b1a6290003271d3634c52026666396c698a4000c6f65dc931480018d8cbb92629015b3318f724c5200143e42cec18a400087f855d831480050f90abb062900021f219750c5200562e31aea18a400087f87d9431480010fb0fb286290003179d7630c5200062ebaec618a400accc635c831480159b0c738062901da1f21975cc1200562e31aeb982405187f87d9730480010fb0fb2e6090003179d763cc1200062ebaec7982400accc635cb30480018f0cb3b4609002ab6a1b638c1200066d3b6c71824000e5b6518e3048001cb0ca31c60900021fe15764c1200143e42aec982404cccc72d8d30480018d8cbb9260901471e1db654c1200566c3b6e6982404ccd876d8d30480159b0ec31a609000396194634c120005d4c20e4982404cdcb731c930480a38dcedb2c40901479ad836588120266673b6c7102400acce7618e2048001c98ca31c40900030fdd6755902004d57416e6b20400faad82dcd640800147d0a39ac8100028f61473590200070fa9ca6b204000aaf8254d640801355904a9ac810002aee01535902001d5c402a6b204000a3e851c5640800147b0a38ac810002a7a0c71590200054ec18e2b204009aae821c5640801f55b0438ac8100032d5c4715902001d5d400e2b20400fab9801c5640800117d0fa8ac8100022f61f51590200054f418a2b204000a9d8314564080131d904baac61000e3e2017558c2001c6e43aa6b1840008bf845ce610800317908b9cc21000e3d21d515842000c5e426ec98840008bf845d9310800317908bb2621015a3be0
  | 4 => 0x34800159b05b8ec69000297a1671d8d200052ec2ce3b1a4000a9e84d47634800153b09a8ec69000237a1c51d8d200046ec38a3b1a40008de8710763480011bb0e20ec69000297a1441d8d200052ec2883b1a404cace82107634800159b0420ec690002b6a0041d8d200056cc0083b1a4000a5f855c363480014b90ab86c69000396d4250d8d200046f438a1b1a40008dd87143634800153d08286c690002a761050d8d2026567410a1b1a4000acd8214363480015ad02286c690002b560450d8d200052f42e81b1a4000a5d85d03634809959d04206c690002b360840d8d200074ca0081b1a400ac5c635d663480018bcebb1cc690003175d76398d200043f43ecab1a400087e8719563480011bf06baac6900023be097558d200047dc02eab1a400087f855d163480050f90aba2c69000237e0d7458d200047bc0ae8b1a40048f4815d163480018beebb9ac690003171d77358d20006363aee4b1a4000c7875dc163480ed8f2e0328c69000237e1d6318d200052fc2ac631a4000a5c8558c63480018bcedb28c6900023761e6518d200046fc3aca31a4000a9e84194634800153b08328c690003179d86518d200070f420ca31a4000e1d841946348001c9b04328c6901fb96c806518d203f72c100ca31a40008dd8799063480014bd0b320c690002976166418d200046fc3ac831a4000a5f8559063480014b90ab20c690002b5e056418d200056a40ac831a4000ace869486348001c98cb290c690003931955218d2000727b2c8431a4000e4c659086348001c9ecaa10c690003931954218d2000747b228431a4000e5b655c06348001cb0cab80c69000387d525418d2028567414a831a4000acd8295063480015b5012a0c690002b66025418d2028567410a831a4000acd8215063480151bd0fa90c6900023761f5218d200056dc02a431a4000ad88054863480f159b09210c6901e7b29c24218d2028764b848431a4050acf8450863480a1d1f08a10c6901e3a39d14218d203c746ba28431a4000e8e545086348001d1aa8a10c6901e3b29c14218d203c764b828431a4000a9e84d44634800153b09a88c690142b3a0b5118d2000566c16a231a4000adb8054463480015b100a88c69002a37a1c5118d200046ec38a231a4050ace82d04634800159b05a08c690003a350a4118d200546f4388231a40008dd8710463480014bd0a208c690002976144118d20285674108231a4000acd821046348001d1a84208c690002b6a004118d200056cc008231a4000acf8254063480a159904a80c69002a37a1c5018d200046ec38a031a4000a9e84140634800153b08280c690142b3a085018d2000566c10a031a4000ad68114063480015ab02280c690003965405018d200052f42e8031a4000a5d85d0063480a159d05a00c690002b360b4018d2000746a168
  | 5 => 0x802a3da1f41587300556b41882b0e6000ae58210561cc0015e30020ac3980030f9d165c87300061f32ae990e6000c3d655d321cc0158bce6b28439800317595730873001c7643aa4b1460038ec87509628c00317d09b8ac5180022f6137158a300066db2ae01946000cd9655c0328c099b9484b80651800372509700ca3001c7a43aa2b0c6000acd83d4b624c00155b08296c4980063be1d42d89300045fc22e3b1260018bc845c7624c0011df0eb10c4980029b21562189300047bc3ac230a600087f855d8214c0050f90abb0429802733189730853004e74312e010a600a8dc835d5620c0151b906ba2c4180023de0574588300247a40ae8b1060038ec87549620c0071d90ea12c41802ab320d42588300045fc22eab0860018bc845d5610c00317d0fba2c21800e3d21d515843001d78402a2b086001cb474905610c0071e90ea0ac2180272b98974c843000656ba2c590860008bf845d9210c00317908bb2421802b351cd614843028666192ec10860008bf845d931c800317908bb2639000e3b209764c72004e72394c298e40508df8758f30c8013998e4b1a619000e3721d5358e202646fc3ac799440008bf845d5618800317908baac31000e3e201755862001c7a43aa2b0c40008bf845d9318800317908bb263100021f61e64d95200052f41cc9b2a4000a5d8399365480010ff0eb26ca9000297e0d64d95200052e41ac9b2a4000a778159365480014e902b26ca9004e9ba1b72d95200071632285b2a4000c3d741d365480a34dd043a6ca900029b60874d952040d3d400e9b2a4051a79801d365480018bae639eca902029ea0073d952028d3cc00e7b2a4051a6e82d0f65480014db05a1eca900021fa1c43d95200043ec3887b2a4044a7a80dcb65480a3c5884a16ca901fe9ea0371d952028d3cc06e3b2a4000a5e839c765480014bb0738eca900028fe1171d95200051e422e3b2a400087e8710765480010fb0e20eca9000297a0c41d95200052ec1883b2a4051a6e8210765480014db0420eca900029ea0041d95200053cc0083b2a405187e87d0365480010fb0fa06ca901469ba0840d952000536c1081b2a4000c5d75d4f634800159b05a9ec69000b171d653d8d200146fc3aa7b1a40018df8750f63480014bd0a21ec6900029761443d8d200054f420cbb1a4000a9d841976348001c3d0832ec6900038761065d8d2000726c10cbb1a4000a5e8599363480014bb0b326c69000297e1564d8d200052e42ac9b1a4000ad78159363480015a902b26c6900039319652d8d200062eba8ebb1a4000a9e841d7634800153b083aec690132b3a0875d8d2000566c10ebb1a4000a5e859d363480014bb0b3a6c690132b3a0874d8d2000566c10e9b1a4000e1f5495363480011bd0fa96c6900023761f52d8d200054f426e3b1a4000a9d84dc76
  | 6 => 0x51ec28e6b264200e1f5394d64c840153f06b8ac990802a720d715932134d57c12e2b2642008be87d4564c840117b0fa8ac990802a7a0c51593210054ec18a2b264200a3e85dc164c840147b0bb82c990802ade05705932142d5a40ae0b264209aae821c164c844b55b04382c9908022fa1c50593210045ec38a0b264200a9e8314164c840153b06282c990826aba08505932100556c10a0b264200ab68114164c840156b02282c99080a1fa177058f210043ec2ee0b1e42008bd86dd131c84e717d0eb2263909de2f21d644c72104e56392c898e4200cae64dc931c840195ac9b9263908030f991750c7210061f3aac818e4200c3d7559031c840395ce8a12c190802b660c505832104d75410a0b064200af18114160c84091b90ea9ac7108123721d4358e210143f42ee0b1c420087d85dc163884bd1df0cb8e651080339d91710ca2100672b22e21944256dc6535c43288401b8aa6b8865108032d1d3764c62104cf343ee498c4200ce776dc93188401b4ee83926310803691d0724c6210247c43a80b0442028df8754f63484014bb0a21ec6908021fe1570d8d210143e42ae1b1a42008bf845d5634840317908baac6908023be097558d210047dc02eab1a42038f8805d563484011bf06ba2c6908023be097458d210047bc0ae8b1a4200c9c74dcd634840195ee9b92c6908032b1d37258d210065a3a6e2b1a42008df8758c634840153908b18c6908022fe11764c52100c5e422ec98a4200c9c74d8d31484ad998c7b9262909cf2d1db744c521005aac28c698a4256ce476dc931484139c8ec3926290803691d0724c52104d724326310a4256ec4634c621484011f70eb00c0908263b2097558c210047dc02eab1842038f8805d563084131d904ba2c6108123d2057458c213de66394a6b1842048dc8754d630841359904a9ac6109eb331c95358c210246e43a86b184209acc8250d63084099cca3bb242108033954776484210143f43eeab00420087f855d160084050f90aba2c01080b1e1d650580210247c43aa0b0042048f88750160084095e102a02c0108030fdd2745973000537414e8b2e6000a6d829d165cc1094f5013a2cb980029e60274597300552f41ee4b2e601ea5d83dc965cc0014f700b92cb9820e9e20172597300051f420e4b2e6000a3d841c965cc00147d09b8acb980028f61371597300053dc02e2b2e6082a78805c565cc0154bd0638acb9807a9760c71597300043f43882b2e600087d8710565cc0154bd0620acb980029760c41597300053741082b2e6000a6d8210565cc0014f50020acb980029e60041597302cd2fc1ae0b2e6000a6f825c165cc0014d904b82cb980021fa1f40597300043ec3e80b2e6000a6e8210165cc0014db04202cb980062fa137158b300045ec26e2b1660048f4815d261cc0058bceaa9ac39
  | 7 => 0xc57154c624c4131dd0fa18c4988023b61f431893100573c0a863126200ae48150c624c40155d09a88c498802ab61351189312f56741ea23126200acd83d44624c401c9aa7a88c4988039354d51189312f567418a23126200acd83144624c40159f06a08c49897ab320d411893104c774388231262008ed87104624c4014dd0a208c4988029b61441189312f567418823126200acd83104624c401d4a82208c498802baa00411893100574c00823126200aaf844c4624c40155908988c49897ab3a0f501893100566c1ea03126200e4d53940624c4131dd0e280c4988023b61c501893100557420a03126200aad84140624c4bd59d06280c498802b360c501893100726a98a03126200ae681140624c4015cb02280c4988029ba17401893100536c2e80312625eace83d00624c40159b07a00c498802b9e0540189310057240a8031262098ee87100624c4011db0e200c4988273918a718c9310065a326e29926200cb4641c5324c4019cec438a6498803a3190628c5310162f3aaa7b026200ad983d43604c4015b306286c0988039654c50d813100578c08a1b026200caf649ca604c401958c9394c0988032bd91729813100656322e53026200cae74d8a604c40195ae9b14c0988032b9d0629813100656ba0c530262018be86dd1604c4e71790dba2c0988022fa1f64581310061fbaec8b026200c3c75d91604c40117d0e322c0988030fdd464581310061e3a8c8b026200caf64dc9604c401958c9b92c0988032bd90725813100656320e4b0262008ee87d89604c4018deebb12c0988031b1d7625813100657ba6c4b026200cac74d89604c4011dd0e312c0988031bdd46258131006363a8c4b026200caf74189604c401958e8312c0988023ee1d60181310053c42ac03026200c3f749d1650c4154bd07b92ca188a29760f72594310051f420e4b286200a3d841c9650c4014bf06a12ca1882a9720d42594310053bc0a84b286204a7481509650c40147d08382ca188028f61070594310552f418e0b286228a5d831c1650c4014dd04382ca188029b60870594310253b408e0b286228a75811c1650c4010fd0fa02ca188021f61f40594310053741080b286200a6d82101650c4151b906ba2c4188123b21d42588310556641a84b106200c9c74dd9310c4099aca3bb2621880335547764c4310070e3a2ca9886204c5f71595310c415caee2b2a621881395c41654c4310064fbb6e89886200e1d65dd1310c40199eedb92621880393597724c43100667bb0e49886200e4d651c9310c401b18e839262188021fe1572980310143e42ae530062048f887501600c40187eeb3aac990802a7a0e75593210054ec1ceab264287ab6819d564c840156b033aac990826aba0b735932112d56c16e6b264200ab7815cd64c850d56902b9ac9908028fa1473593210
  | 8 => 0x7a96c8988022fa1c52d91310045ec38a5b2262738be87d47644c40117b0fa8ec8988038dd4651d913139d4f418a3b226200a9d83147644c51356d03b86c8989cead60770d913100557414e1b226200aad829c3644c40147f0ab86c8988028f21570d91310045f438a1b2262008bd87143644c4e753d06286c898802a760c50d913100557410a1b226200aad82143644c40156d02286c898802ad60450d913100636baea5b126200acd83d4b624c4051df0ea96c498802aba1052d893100556c20a5b1262018ef8750b624c40155d0932ec498802ab61265d893100557c22cbb126200aac84597624c4015d700b2ec498802ba20165d893100537428c9b126200a6d85193624c401c5d0a326c4988038b61464d893100746c18c9b126200e8c6490f624c40155d093aec498802ab61275d893100636ba8ebb126256ace831d7624c40159b063aec4988029ba1474d893100536c28e9b126256ace831d3624c40159b063a6c4988038bd5254d89312b72729ea7b1262008ee87d0f624c4011db0fa1ec498802abe1171d893100556422e3b126200aae84d47624c40155b09a8ec49880399d4651d89312b567418a3b126200acd83147624c4011dd0e20ec4988023b61c41d89310053742883b126200a6d85107624c4ad59d0620ec498802b360c41d89310057540083b126200ae980107624c4014dd0bb86c4988029b61770d893100566c1ee1b126200aae849c3624c40155b09386c4988023ba1c50d893100476c38a1b126200aae84143624c40155b08286c49895ab3a0c50d893100566c18a1b126200ae681143624c4015cb02286c4988029ba1740d893100536c2e81b1262008ee87103624c4011db0e206c4988272b1897498931006573a6c53126200cad74d8a624c40117d0fb22c4988022fa1c64589313be5ab88c831262008ef87588624c40155f08b10c498802ab211621893100476c3cca3126200aae84994624c40155b09328c4988023be1d651893100557c22ca3126200aac84594624c4015d700b28c498802ba2016518931006573b6c831262008ed87990624c4011df0eb20c4988029ba14641893100536c28c83126200cae76190624c401c5d0a320c4988038b614641893100746c18c83126288ea731190624c511d4862320c498803a3d92531893100746324a63126200e4f6554c624c401d1ec8a98c498803a3191531893100567434863126200e8c6490c624c401d18c8a18c498803a9d91711893100752322e2312625eace83d50624c40159b07aa0c498802b9a07541893100572c0ea83126200e2f54950624c4bd59d062a0c498802b360c54189312f72729ea6312627bec67194c624c4f7d8ae3298c49897b93e1553189313d7273aaa6312627ae4d7554c624c401c9ea8a98c4988039355153189313d76338aa6312627ae
  | 9 => 0x51980320055cc26a3300640aada83146600c8015b30628cc01900e3ea1c41980320047cc38833006400a7a85106600c8014f30a20cc01902ab6a0c41980320056cc18833006409aea82106600c8015d30420cc0190072b9d1425803204c7d43ea0b00640aada83d41600c801cb2a7282c0190263e21d50580320055d420a0b006400ab984141600c8155b506282c0190039654c505803204d75410a0b006400af281141600c8015e302282c0190263ea1f40580320053d42e80b006400a7985d01600c8135d505a02c019003aa50b405803204c7c43a80b006400ea942501600c8135d504202c01902ab620f75580320556d41ceab006400ad9839d5600c8015b706baac01902ab620d755803200575c12eab006409ae8825d5600c801575083aac019002ae61075580320556d418eab006400ad9831d5600c8135d5043aac019002ba608755803200579408eab006400af1811d5600c8014f50b3a2c0190029e61674580320556d41ce8b006400ad9839d1600c8135d5053a2c019002ba60a74580320056dc1ae8b00640aad8835d1600c8135d5043a2c019002ba60874580320556d41ea8b006400ad983d51600c801c76a92a2c019026baa0a545803200574c14a8b00640aada83151600c8015b3062a2c019026baa08545803200574c10a8b006400ad88754d600c8155b70aa9ac01902b96e1553580320072dbaaa6b006400e587554d600c801cb6a8a9ac0190039655153580323d72da92a6b00647ae595254d600c8f5d9484a9ac019026bae11425803204f55c2284b006400eaa74509600c801d52e8a12c019003aa951425803200754aa284b006478eca53509600c801d92a6a12c0191e3aad0d42580323c754a1a84b00640aada839c5600c8014f70ab8ac0190029e21571580320055dc22e2b006400ab8845c5600c8155b106b8ac019026ba20971580320055d426a2b006400ab984d45600c8155b507a8ac019002b660f51580320072ca9ea2b006409aea82d45600c8015d305a8ac0190039654d51580320556d418a2b006400ad983145600c8135d505a0ac019002ba60b415803200754a1482b0064008fa87105600c8011f30e20ac0190029ea1441580320053cc2882b00640aada83105600c8015b30620ac019026baa08415803200574c1082b006400ea942105600c8091d90ea12c51895a3be1d628ca310043fc2ae8b04620287c855d1608c4091f10ea02c1188022f61e65d913100557414cbb226200aad82997644c40117f0eb2ec898802abe0965d913100556412cbb226200abb80597644c40157100b2ec8988aaa7a1b73d91310061eba8ebb226273a9e831d7644c40153b063aec898a2aada0475d913139d5ac08ebb22626fab681dcf644c4e7c3ca7a9ec898982ada0472d913139d5ac08e5b226273a9e83d4b644c40153b
  | 10 => 0x3086400ab5849d6610c801c6ea92a4c2190029de1570984320053a42ae13086400ab7845c2610c80156908b84c2190123da1c50984320047ac38a13086400ab684142610c80156b08284c21902ab5a0c50984320056ac18a13086409ae682142610c8015cb04284c2190029da1740984320053ac2e813086409ae682102610c8015cb04204c21900b179d5535843204c7b43ea2b086400ab684d45610c80156b09a8ac21902ab5a0f51584320072aa9ea2b086409ae682d45610c8131e90ea8ac2190039554d51584320556b418a2b0864098f687d05610c8135cd05a0ac219003a950a415843204c7a43a82b086400a7685105610c8014eb0a20ac21902ab5a0c415843204d7341082b086400ea542105610c8015e50020ac219002bc60041584320055b424eab086400ab5849d5610c8155ad073aac219002b560e755843204d73414eab086400ae5829d5610c8015cf04baac219026b920975584320556b418eab086400ad5831d5610c8135c905ba2c219026b9a0a745843200572c14e8b086400ad7835d1610c8155a906ba2c219002b9e09745843204d72412e8b086400a76851d1610c8014eb0a3a2c21902ab5a0c74584320056ac18e8b086409ae6821d1610c8015cb043a2c219002bca00745843200578c00e8b08640aad683d51610c8015ab07aa2c2190038dd52545843204d73414a8b086400ae582951610c8155ad062a2c219002b560c545843204d73410a8b086400ae582151610c8155af0aa9ac21902b95e1553584320072b3aaa6b086400e557554d610c801caea8a9ac2190039555153584323d72ba92a6b08647ae555254d610c8f5d8c84a9ac219002b921d425843204d73c2284b086409ea784509610c801d4ee8a12c219003a91d14258432007532a284b086400ea554509610c8f1d8ca6a12c219003b154d42584323c753a1a84b086478ea543509610c8135cd05382c2190029de1570584320053a42ae0b086400ab7845c1610c80156908b82c21902ab520d705843204d72412e0b08640aad683d41610c8015ab07a82c2190039554e50584320047b438a0b0864008f587141610c80156d08282c219002ad61050584320556b418a0b086400ad583141610c801caaa6282c219026b9a08505843200572c10a0b086400a7685d01610c8014eb0ba02c21902ab5a0f40584320056ac1e80b086409ae682d01610c8015cb05a02c219003a950b405843200752a1280b086409ae682101610c8015cb04202c21900e3e201759803201c7c402e9300640087f855c6600c8050f90ab8cc0190022fe11719803200c5e422e330064038f8805c6600c8014f50ba04c0190029e61740980320053d42ce93006400a79859d2600c801c76a92a4c0190029ee1571980320053c42ae33006400abb845c6600c80157108b8cc019002aea13
  | 11 => 0x80180a00100100300480900200000300580000500000100180200100000000100000100100100100080000600080000000080000100200000080100400100000080000600000000180000480180100180500680000000100000000200000200680000301200280100780100500000100100300000000100400080a80000280080380000200000000280000100700000200000300180080100000280000280000000080100200100180200080000000100880200000500080180c0000018008000008000010000000000018000008000070028000020010070000010018000010010020010018030018000000030048028008020021fe1570987320143e42ae130e64008bf845d561cc80317908baac3990023ee01755873201c7c402eab0e64018be87dd161cc803958e8a12c3990022fe11719823200c5e422e3304640287e87dd5608c8010ff0aba2c11900a1f21574582320047bc0ae8b0464048f4815d1608c8058b8eb29ac11900b171d553582320056ac1883b0a6400ae582107614c8011ef0eb08c299002ad21161185320043fc2ae030a640287c855c0614c8018f2eba86c099002b660c50d813200574c10a1b0264008fb87580604c8014f10ab00c0990022fe11711813200c5e422e23026400c3f749d1650c8134dd053a2ca1923a9b60a74594320051f426e2b286400a3d84dc5650c8d74df04b8aca190269b20971594320552f418e2b286430a5d831c5650c8010fd0e20aca190021f61c41594320552f41882b286400a5d83105650c8134dd0420aca190029b60841594320053d40082b286400a7980105650c8b74bf06b82ca1902a9720d705943246d37c12e0b286409a6c825c1650c80147d08382ca190028f61070594320552f418e0b286430a5d831c1650c8134dd04382ca190c29b60870594320053b408e0b286400a75811c1650c8010fd0fa02ca190021f61f405943204d3741080b286400a6d82101650c80187eeb3aac81902aa7a0e75590324654ec1ceab20648ba9f835c5640c81553906b8ac8191b2abe09715903204d56412e2b206400a3e851c5640c80147b0a38ac81902aa7a0c715903217d4ec18e2b206409aae821c5640c85f55b0438ac819002aea0071590320055cc00e2b2064008be87d45640c80117b0fa8ac81902aa7a0c51590320054ec18a2b206400a3e85dc1640c80147b0bb82c81916aa7e0d70590320554e41ae0b206409aae821c1640c85f55b04382c8190022fa1c50590320045ec38a0b20640aa9e83141640c80153b06282c819026aba08505903200556c10a0b206400ab681141640c80156b02282c8190123d20575984320247a40ae93086400ab684d46610c80156b09a8cc2190021fe1570984320143e42ae130864008bf845c2610c80317908b84c2190123d20570984320055b424eb
  | 12 => 0xd5b911e29910e4bf0891404ea0000000e70c40005055333f142003a56b0001c11af0000003875515920000003b333e22b09f45d5c65c701f0fd2fc2d921b54e3803584072db0000ed0002620003395f100000000000000000056052b22200046c00065232f2e60002d708d35c14b2a33e04f80d42f404d0220000003981481465910ea0000002ce35d2352952d36501ae0000560002b50000000001da6000002630001661e60004d834900000031a0000000000634753016584e92a20005f70002266042235d94ae14945e2520ce4465c95755b604130616006d0f10000c20005824db00050732957f3f242764b51200000013824700000016e5430002cd00010400049751f00057a5354602705f80000000000003d000024d5ae00000016411d62515d0e22194220005c026016b34343a04700000000000000000b2c20670001074bd00028024c0da0000000203d51340000004df4f009704436342408300000000000000000000000000028100024400057100000025f00064d1fd3520003a100000020c0000000000003e12f526802f10a00000000000000000045900000000000000051944c0005275955db00000001a64f00060548200000004e1a531b0f905000000000000100100000100800000100000080300000480100980000000501200000000400000580100480080080000000000000180100380080100180180800400280080680000000080280300000100080200280500280c00180180000000000480100b00200000100180080300080000400300080100080000000000000000180000000000400200380180000100500080000100000100600000180000a00100080080000180680000080200200300280080180400000500080000180000000080000000000000200180080180300180180100000000000000000100080480000080400000300000000280080200400280100000000200000000380180000080380000180000300180300100380000380000000080100000180780000300000080080000000000100500200000000080080000100280000000000200100580000680000080000000000000180100000100200100200200600200880080200180b80200180000000000a80600080080680000000080000080000100200300100100000000000400100100280000080180580500000100300000000100180080000500000000200000580000180180080000600100400000000500180000100000000000000000200000000100000000080000100100080100000200000180280100280000200200c80380080000080280180000000280200080700280080000a00180000000080080380100680a003002000801001800801804800800000002000001801800001801801000000801803000003800804800800800000
  | 13 => 0x36e00000000000000034f1c20001a80000000000000000002e14d52104b542c39e1753f500003100001d1ff00000000000000000026d5545b40000000002cf3ef24a00013f2860000000000000000b10001d812b2fe31613539549d47442302e0000000000fc16100062001718300045522e2454c628453d00000000004900063858700000000000033b0000000000000403ec4f92f904f3850102c35a45dd00000013900000000011750b0000000000000000000000003440000904180000000000000370000280005f20001fa00045c0000002590000000c80000000000000004bc1fc62f1f815500034d21e00008c34e6151c53330004514cc3b424b0004ff5630000002e41b25550004d34dd29f09b09a07543300038600001949c52034a00036c2f241d1e14850000000001020005374b40002d035405941b00011960f00041a2e06070000002ed0000002580006356303b80001095df64917843728c0b921d4c81110124533616270000005fb1503ac4aa1700000004ac00015a0003e53a40ca2290000000000003070000000000006601be0000003c51885d54e41cd4455fe44046935f1cb0000fb00000003400000038915200038e02d2910001f400000000000000000000000000043c31e2fd45f40f14556813c4795a300043e19836b1250000000002da4d749644a0000005470000001730300a330f17603c3005f65ee1b604b27d27f2530001a700038a0002fb2ef5ef0790000000f343b0e053932333c1f203361c4a30002c549f0000003766161156330000c76340005780002af34200063e4af3b912254500006e0000000001b80004fc00000000021c64161254800000053f52841f2d800000027b00047b33046640e4a600000000000000063a0003720005be0001c34ad52300050f00014723719500000000000000012e6240000003c200061000000000000037d0002c41015583f705f0000000000000133a700000000000006f0000000000002e30002143b21543e44140000000002b900038223d3d32270000000bc00013b3603a31b32df00000000055b33714a0001c444800000000003663d02b3d629a0002575d30000bb14f49a5fc0000000000001d62515ac2483cf1a253e0ad00000017439b2bd40b00037014237e50056e0004fb2f121a1e402c0d15a70000005e20af00044b0000000000006294700003414e561b23b3ae15822848155e0002b84785890000163cb4da38b31737a0f20c10000570003282b050600000003e4f40005bd00000007a4de00020d13200000062d3150000004b80000690ff4022693a84281ec0c664813d58d03243829254a0003cc00000051d0cd0004d60000000000000003560000ac00012919b1684a72b71441dd11f4670004250a800000034746b00028b0004c45d63e93bb5d11
  | 14 => 0x1b11f01cc00000037c0003fe0000004fa18e00039120e2790004360003a90000001aa06c3af5da2826453021bb50d0003f359d1dc4e807442b0000005cf0003c10001d25a62f33e848d0b21a33b000000000016d00000000051b0000f80000000000000006400003d80021d900000015e0002aa0000233a20000000002c828f0003080001690000000000005b81800003040000001ce4002554353ff5342184501a917e49516f0000002b213e00000000000000000000000000042d0000001363a65775ed5e30000003ad5d20000000001210000000001c661d00056f1e92940000000000005e032021107800032a20307f0000942ee6080004f55720000000000001851620000e640c4012a10c50000000002f605351059e00015b0000004a90524940005d032d0005fd1860000000000000004c90005f40dd1a43d45ec3114b903557d5ff0182a965c28a2a80c00a92ac20065d53c2a500055026a4b64522e728e3324304390fa2e919d2ae0b033d5c265a52f4413f022c6550002d23650000000005210006033712200000004060bf02134819f17b1ed31232e0000000ec3ca0000001ca52a6020b80001ab2490002ec00000000000055a57b00046856d00f00001459327e4884d901500053030e3f808e11800558e3c347f0930e402a1a112d1ef2bb36a00057654449028500030511046200000000051c0002660000000003ee0000000000000000000000005805e80000b52420000001d10000003f40250005110000000004d15b258400050e0a55a50556185595183da00040a65900000021200000046d37807751739643225a40448b39900000000053a0000d90000000f04c300000000000058c0003e650a0004b000011c0000002d405b4e212a64e16c5b33380000000001c72bc3830000005030000000002cb5f50cc2e823400000052c58f5ce37b00000000128859f00039a0006260000003a00006283c75e46010860bd3dc5735e915318454f0004890004e70245940e90d66434094921b05530ef0000004f30a40004e600000000058b59b60c47a62c2e23ed1945e100023800000058312431d59a01e45647100044d0000004170002090000950000000000000000000004770000000005de0000000005010002ea4a401b55f3c40000290003213fd4166420000000000000000005d80000001f50002301162082f75af00000009244400000000064443106a56400054c00000000000000000000013a00000000048e1fb65f51e0000000005310000006190000000000005740000000000000004190000004eb00045700026f0001373663254be0a20005cb5860000000004ce3de26e3673d93353240763c65400f710310c36f60d2055c136d4cd3532654133e70000005c54913143775560b40984a261130c53b0e50cb00000000000000
  | 15 => 0x5080004840e132200000000060b4a500051500029742f1a00005b01e30003bf01c48328d19703d5900e80000002780a10962bf5b74c73b13df4f200032b0aa54b12f0ba2c62f80000000000000004a83d10612b10000003bc34663c12663918d00007200005e48c38415f0002390000002ff0004a14d05242133c03ba4b258820a63725b0d819024038852618909e1ba5ba36823131009d27525461f46a00000a61400048f3640074471bd4ca4f65a92560000005dc3fb5e754204610f00000000000000000009908f0005981db00043d00048a0003504ed42a0650d01053ce22521f2711fe00051412c61700017c0005bc65638c5620000000810000000000000002c90000002870001b900000000035717729b37300000850207d56c3f64ef0800002902831bc4150434ba0d713117d2b44dc52e0002070005a80000001960003594653cd16a33400011b20115900000017100049801100040d4760000000000000000001d460a0003c800000058a44e0000eb3360001911e038f1ac0000000034fe00023a25d0004e021700000e2d53d709c2244724423ea00000000034b30d2ba6231630d35040000605970003ab6530005522a45e60001276465660b34f12a64e10000000000002930001c80000000000000be0000002be00029e00000000056147d00000000023f08a0715b100900031812800035b27229d1932cc00012304a65b0040b61f904c0003be3b70001e85c84030000004214a021656918a0001c01de24e5090d22776361330512500de3813fa3b620f34c1cf37f0000001000000005d400000032746f34502755c6542963313405360006095f00d549b5c30000a618f02633f60e5854c130961e6510000001f10002b300019e54d4f751300046e0000000000005ab23600000044f0910001720000000640ee2215161df2ad40800007c31c19946400000032c19c0000005290003550000000000000000000000000000005cd2e500000024147300000023c3aa23e0420000002de0005ca5f90001b453247e63100010b00043f0c314e2d139d1ee03f0450e341e1ea29c03b3260f50a739439018b5c464c2ca2ab48750c00030330a1084493c90004291432d61bf0681c94ec0a000000049927341c0000004fd00036959600008419a4b34cb00017919207037500057e45400017f00005c1d73b52610004bb45b0000380ab0000f60002c75ad0000000000000002f00000004ee3f90005b500049e51a6476324c21e213026b4b152233a4d256a00600035a0005d70004126220000002eb5aa5a05e52464b75f30000002890001b525c0df0000ae22d0cf0000002dd0dc2dc0002045990000000000885cc00020600022a00000c12000041142614c00000000000031f00014d5bb00024f0db60654925e42e0005790000000001eb00007b
  | 16 => 0x39f5a238d0000002740002760000000000003d200000000022f39c00000000000063f20b2a714117a5380000003e362e1812983db2fa00000000000000000000000006200d1142023fc4100c90000000000000000f45ea3a50000002b60005703621670002c054100005a0003bd00000000006b00030b4580003970004c50001e500056700007300000000059c1ad0004051b71f700008b43400000021562b1512645bf26700000000011a0005a14631d300035115c3dd0004e365e0871d000047c00000000064a1a600000000000000011300010608506615703900058100052d23300000000005463b0005fa00057c2320820000001d53931124866134ab35e27a0b71e700000000055d00000045a0001f30000000000000001874610001650485653eb00000000049331300062a0003e24806574cf26c00000000000054655700000007e5eb0004d43922a00fe00000061a4c01f600000000000000005800000000000037900031944362118c18224300005d00000015652500000027c0002c13740
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x1204003002000056000212e5421e206c680389430a0058a000000880044c01d0090000323c0000060005249c0000098022468061f5aa800e34a54000e01600160000000003c0000000180000c00a00002810068561153d45610c801a25855084158432006a850980105610c801615949d553584320059164a7554d610c801647925d553584320058965474509610c801685931d14258432005a864074509610c801e055454d42584320061561d53141610c801a158454c50584320069154d82141610c801a258550b4058432006a160d42d01610c801a198454c50580320069454d81141600c801a298550b4058032005866507554d600c801649921d55358032005946447554d600c801629959d14258032005a264e74509600c80168b935d142580320078255153509600c801a198454f51580320069254d82d45600c8018a98750841580320068a61542105600c801a89835084158032005916475454c624c401a0d8454f51189310061361d53140624c401a0d8454c50189310069154d81140624c401a515360450d813100703594741c9310c401689909514218d200062361d421046348001a0d855084118d20006a2509801046348001a0d8550b4018d20006a8509801076148001c0c7559073480200068a609801936544001a158360465d9110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x5
  | 2 => 0x6
  | 3 => 0x1
  | 4 => 0x2
  | 5 => 0x4d
  | 6 => 0x4e
  | 7 => 0x124d
  | 8 => 0x138d
  | 9 => 0x3
  | 10 => 0x4
  | 11 => 0x94d
  | 12 => 0x94e
  | 13 => 0x124e
  | 14 => 0x138e
  | 15 => 0x8d
  | 16 => 0x8e
  | 17 => 0x128d
  | 18 => 0x98d
  | 19 => 0x98e
  | 20 => 0x128e
  | 21 => 0x150d
  | 22 => 0x150e
  | 23 => 0xcd
  | 24 => 0xce
  | 25 => 0x12cd
  | 26 => 0x9cd
  | 27 => 0x9ce
  | 28 => 0x12ce
  | 29 => 0x168d
  | 30 => 0x168e
  | 31 => 0x20d
  | 32 => 0x20e
  | 33 => 0x140d
  | 34 => 0xb0d
  | 35 => 0xb0e
  | 36 => 0x140e
  | 37 => 0x154d
  | 38 => 0x154e
  | 39 => 0x24d
  | 40 => 0x24e
  | 41 => 0x144d
  | 42 => 0xb4d
  | 43 => 0xb4e
  | 44 => 0x144e
  | 45 => 0x16cd
  | 46 => 0x16ce
  | 47 => 0x3cd
  | 48 => 0x3ce
  | 49 => 0xccd
  | 50 => 0xcce
  | 51 => 0x15cd
  | 52 => 0x15ce
  | 53 => 0x170d
  | 54 => 0x170e
  | 55 => 0x94055
  | 56 => 0x94056
  | 57 => 0x124055
  | 58 => 0x138056
  | 59 => 0x124955
  | 60 => 0x124956
  | 61 => 0x95256
  | 62 => 0x138956
  | 63 => 0x138955
  | 64 => 0x95395
  | 65 => 0x125395
  | 66 => 0x139256
  | 67 => 0x98095
  | 68 => 0x98096
  | 69 => 0x9d295
  | 70 => 0x99295
  | 71 => 0x128996
  | 72 => 0x99296
  | 73 => 0x992d5
  | 74 => 0x9c995
  | 75 => 0x9c996
  | 76 => 0x12cb
  | 77 => 0x12c995
  | 78 => 0x12c996
  | 79 => 0x989d5
  | 80 => 0xcb
  | 81 => 0x134b
  | 82 => 0x151296
  | 83 => 0x151295
  | 84 => 0x9d296
  | 85 => 0x9c0d6
  | 86 => 0x140c
  | 87 => 0x15c0d6
  | 88 => 0x9d2d6
  | 89 => 0x1692d6
  | 90 => 0x3d2d5
  | 91 => 0x3d2d6
  | 92 => 0x15d2d6
  | 93 => 0xb0216
  | 94 => 0x20c
  | 95 => 0xb0215
  | 96 => 0xb5415
  | 97 => 0x170215
  | 98 => 0xb1415
  | 99 => 0xb1455
  | 100 => 0xb4b15
  | 101 => 0xb4b16
  | 102 => 0x144b15
  | 103 => 0xb0b55
  | 104 => 0x155416
  | 105 => 0x155415
  | 106 => 0xb5416
  | 107 => 0x3d416
  | 108 => 0x3d415
  | 109 => 0x171415
  | 110 => 0xb4256
  | 111 => 0xb4255
  | 112 => 0x144b55
  | 113 => 0xb5455
  | 114 => 0xb5456
  | 115 => 0x148c
  | 116 => 0x16d456
  | 117 => 0x16d455
  | 118 => 0x14b
  | 119 => 0x28c
  | 120 => 0xd0c
  | 121 => 0x160c
  | 122 => 0xecb
  | 123 => 0x17cb
  | 124 => 0x954d5
  | 125 => 0x95316
  | 126 => 0x140d3
  | 127 => 0x98056
  | 128 => 0x992d6
  | 129 => 0x99316
  | 130 => 0x168056
  | 131 => 0x168096
  | 132 => 0x169316
  | 133 => 0x154055
  | 134 => 0x154255
  | 135 => 0x1554d5
  | 136 => 0x28214
  | 137 => 0xb4055
  | 138 => 0xb54d5
  | 139 => 0x3d455
  | 140 => 0x3ced5
  | 141 => 0x3d296
  | 142 => 0x3cd16
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 2028
  | 6 => 4029
  | 5 => 1633
  | 4 => 46
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
  | 8 => packedAt gbK8 (1700+((h/20+packedAt gbK8 (1560+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (83148+((h/676+packedAt gbK7 (75036+(h % 676)*12) 12) % 2944)*12) 12
  | 6 => packedAt gbK6 (210851+((h/1343+packedAt gbK6 (193392+(h % 1343)*13) 13) % 7076)*13) 13
  | 5 => packedAt gbK5 (102875+((h/544+packedAt gbK5 (96347+(h % 544)*12) 12) % 2608)*12) 12
  | 4 => packedAt gbK4 (3325+((h/15+packedAt gbK4 (3220+(h % 15)*7) 7) % 80)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffe1f03e0ffc1e00f87803fc2cc71fc3cc33f
  | 1 => 0x7803e003ff07fffffff8003fcd324e60c7fc3f
  | 2 => 0x8003fffc0007fe000fffffc3f1c38f87070fc7
  | 3 => 0x3fffffff800000ffffffc3e03f007f80ff8
  | 4 => 0x3fffffffffffff00000003ffc0007fff000
  | 5 => 0xfffc000000000000000000003ffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x887a0721604ad12125848286404410ac1cc31b
  | 1 => 0x50886000a9014248eac8052884124660415c2d
  | 2 => 0x112a9640045b5024315298311c08b85070546
  | 3 => 0x4221528ada9000048c6256302e037002e80ab0
  | 4 => 0x4439cf314e63997000418023bec0007b6a000
  | 5 => 0x678000c018802018004060203fbbed50000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefaeafeccf880feeefaeafeccf880feeefaeafeccf880feeefaeafeccf880feeefaeafeccf880feeefaeafeccf880feeefaeafeccf880feeefaeafeccf880, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36244
namespace PEqualNP.Outside.L_meta_36244
open PEqualNP.Outside.L_meta_36244.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 1 := bs1_4_0
theorem alls1 : ∀ k ≤ 4, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 2 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 6 := bs2_4_0
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
theorem bs3_3_0 : Interval s3Atlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 2 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 6 := bs3_4_0
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
theorem bs5_2_0 : Interval s5Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 5 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 25 := bs5_3_0
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
theorem bs5_4_384 : Interval s5Atlas 4 384 30 := block_range (n:=30) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 414 := (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat bs5_4_96 (concat bs5_4_128 bs5_4_160))) (concat (concat bs5_4_192 (concat bs5_4_224 bs5_4_256)) (concat (concat bs5_4_288 bs5_4_320) (concat bs5_4_352 bs5_4_384))))
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
theorem bs5_5_608 : Interval s5Atlas 5 608 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 616 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 bs5_5_192) (concat bs5_5_224 (concat bs5_5_256 bs5_5_288)))) (concat (concat (concat bs5_5_320 bs5_5_352) (concat bs5_5_384 (concat bs5_5_416 bs5_5_448))) (concat (concat bs5_5_480 bs5_5_512) (concat bs5_5_544 (concat bs5_5_576 bs5_5_608)))))
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
theorem bgb_4_32 : Interval gbAtlas 4 32 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 46 := (concat bgb_4_0 bgb_4_32)
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
theorem bgb_5_1632 : Interval gbAtlas 5 1632 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1633 := (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 bgb_5_384)))) (concat (concat (concat bgb_5_416 (concat bgb_5_448 bgb_5_480)) (concat bgb_5_512 (concat bgb_5_544 bgb_5_576))) (concat (concat bgb_5_608 (concat bgb_5_640 bgb_5_672)) (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 bgb_5_800))))) (concat (concat (concat (concat bgb_5_832 (concat bgb_5_864 bgb_5_896)) (concat bgb_5_928 (concat bgb_5_960 bgb_5_992))) (concat (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088)) (concat (concat bgb_5_1120 bgb_5_1152) (concat bgb_5_1184 bgb_5_1216)))) (concat (concat (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312)) (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408))) (concat (concat bgb_5_1440 (concat bgb_5_1472 bgb_5_1504)) (concat (concat bgb_5_1536 bgb_5_1568) (concat bgb_5_1600 bgb_5_1632))))))
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
theorem bgb_6_4000 : Interval gbAtlas 6 4000 29 := block_range (n:=29) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 4029 := (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat (concat bgb_6_224 bgb_6_256) (concat bgb_6_288 bgb_6_320)) (concat (concat bgb_6_352 bgb_6_384) (concat bgb_6_416 bgb_6_448)))) (concat (concat (concat (concat bgb_6_480 bgb_6_512) (concat bgb_6_544 bgb_6_576)) (concat (concat bgb_6_608 bgb_6_640) (concat bgb_6_672 bgb_6_704))) (concat (concat (concat bgb_6_736 bgb_6_768) (concat bgb_6_800 bgb_6_832)) (concat (concat bgb_6_864 bgb_6_896) (concat bgb_6_928 bgb_6_960))))) (concat (concat (concat (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 bgb_6_1088)) (concat (concat bgb_6_1120 bgb_6_1152) (concat bgb_6_1184 bgb_6_1216))) (concat (concat (concat bgb_6_1248 bgb_6_1280) (concat bgb_6_1312 bgb_6_1344)) (concat (concat bgb_6_1376 bgb_6_1408) (concat bgb_6_1440 bgb_6_1472)))) (concat (concat (concat (concat bgb_6_1504 bgb_6_1536) (concat bgb_6_1568 bgb_6_1600)) (concat (concat bgb_6_1632 bgb_6_1664) (concat bgb_6_1696 bgb_6_1728))) (concat (concat (concat bgb_6_1760 bgb_6_1792) (concat bgb_6_1824 bgb_6_1856)) (concat (concat bgb_6_1888 bgb_6_1920) (concat bgb_6_1952 bgb_6_1984)))))) (concat (concat (concat (concat (concat bgb_6_2016 (concat bgb_6_2048 bgb_6_2080)) (concat (concat bgb_6_2112 bgb_6_2144) (concat bgb_6_2176 bgb_6_2208))) (concat (concat (concat bgb_6_2240 bgb_6_2272) (concat bgb_6_2304 bgb_6_2336)) (concat (concat bgb_6_2368 bgb_6_2400) (concat bgb_6_2432 bgb_6_2464)))) (concat (concat (concat (concat bgb_6_2496 bgb_6_2528) (concat bgb_6_2560 bgb_6_2592)) (concat (concat bgb_6_2624 bgb_6_2656) (concat bgb_6_2688 bgb_6_2720))) (concat (concat (concat bgb_6_2752 bgb_6_2784) (concat bgb_6_2816 bgb_6_2848)) (concat (concat bgb_6_2880 bgb_6_2912) (concat bgb_6_2944 bgb_6_2976))))) (concat (concat (concat (concat (concat bgb_6_3008 bgb_6_3040) (concat bgb_6_3072 bgb_6_3104)) (concat (concat bgb_6_3136 bgb_6_3168) (concat bgb_6_3200 bgb_6_3232))) (concat (concat (concat bgb_6_3264 bgb_6_3296) (concat bgb_6_3328 bgb_6_3360)) (concat (concat bgb_6_3392 bgb_6_3424) (concat bgb_6_3456 bgb_6_3488)))) (concat (concat (concat (concat bgb_6_3520 bgb_6_3552) (concat bgb_6_3584 bgb_6_3616)) (concat (concat bgb_6_3648 bgb_6_3680) (concat bgb_6_3712 bgb_6_3744))) (concat (concat (concat bgb_6_3776 bgb_6_3808) (concat bgb_6_3840 bgb_6_3872)) (concat (concat bgb_6_3904 bgb_6_3936) (concat bgb_6_3968 bgb_6_4000)))))))
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
theorem bgb_7_2016 : Interval gbAtlas 7 2016 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2028 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 bgb_7_480)))) (concat (concat (concat (concat bgb_7_512 bgb_7_544) (concat bgb_7_576 bgb_7_608)) (concat (concat bgb_7_640 bgb_7_672) (concat bgb_7_704 bgb_7_736))) (concat (concat (concat bgb_7_768 bgb_7_800) (concat bgb_7_832 bgb_7_864)) (concat (concat bgb_7_896 bgb_7_928) (concat bgb_7_960 bgb_7_992))))) (concat (concat (concat (concat (concat bgb_7_1024 bgb_7_1056) (concat bgb_7_1088 bgb_7_1120)) (concat (concat bgb_7_1152 bgb_7_1184) (concat bgb_7_1216 bgb_7_1248))) (concat (concat (concat bgb_7_1280 bgb_7_1312) (concat bgb_7_1344 bgb_7_1376)) (concat (concat bgb_7_1408 bgb_7_1440) (concat bgb_7_1472 bgb_7_1504)))) (concat (concat (concat (concat bgb_7_1536 bgb_7_1568) (concat bgb_7_1600 bgb_7_1632)) (concat (concat bgb_7_1664 bgb_7_1696) (concat bgb_7_1728 bgb_7_1760))) (concat (concat (concat bgb_7_1792 bgb_7_1824) (concat bgb_7_1856 bgb_7_1888)) (concat (concat bgb_7_1920 bgb_7_1952) (concat bgb_7_1984 bgb_7_2016))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 5 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 5 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 24, 25),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 3, 11),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefaeafeccf880feeefaeafeccf880feeefaeafeccf880feeefaeafeccf880feeefaeafeccf880feeefaeafeccf880feeefaeafeccf880feeefaeafeccf880
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277074666 * 2 ^ 32 + 4274845824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36244.Model.Repr at out
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

def mono : List Gate := [⟨.or,[4,5]⟩,⟨.and,[0,1]⟩,⟨.or,[3,5]⟩,⟨.or,[6,7]⟩,⟨.and,[0,8]⟩,⟨.or,[2,4]⟩,⟨.and,[1,11]⟩,⟨.or,[10,12]⟩,⟨.and,[9,13]⟩,⟨.and,[2,3]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4274845824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074666 * 2 ^ 32 + 4274845824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36244

open PEqualNP.Outside.L_meta_36244 in
theorem PEqualNP.Outside.L_meta_36244 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4274845824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074666 * 2 ^ 32 + 4274845824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
