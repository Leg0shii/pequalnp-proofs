import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36641.Model
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


end PEqualNP.Outside.L_meta_36641.Model

namespace PEqualNP.Outside.L_meta_36641
open PEqualNP.Outside.L_meta_36641.Model
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

def SBf (j : Nat) : Nat := [4, 4, 7, 7, 7, 7].getD j 0

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

end PEqualNP.Outside.L_meta_36641

namespace PEqualNP.Outside.L_meta_36641
open PEqualNP.Outside.L_meta_36641.Model
def s0K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (i*5) 5
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (6+((h/1+packedAt s0K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xfff87fe00ffffffffe01fe03fffffff0047ff8
  | 3 => 0xf0fffffff007fc03fffffffc07f007ffff8e3f
  | 4 => 0xfffffffff80003fffffffff80007fffff03f
  | 5 => 0xff007ffffffffffc0001fffffffff80007ffc0
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x2010096152292428a224562c58b568b6a9b6db
  | 2 => 0x442692bb44b26a51451caf02ad5a7551a45b78
  | 3 => 0x8d4224ca6ea4529a69493b560663266b368e2d
  | 4 => 0xee84471388c763639191cd9b340c478dc77036
  | 5 => 0x8f7781c0f078383e1e1f1e3c78f840e07ed80
  | _ => 0
def s0Atlas : Atlas := ⟨3,rawDecor 62 s0Pos s0Neg, 0xccc0c0c0cc000000ccc0c0c0cc000000ccc0c0c0cc000000ccc0c0c0cc000000ccc0c0c0cc000000ccc0c0c0cc000000ccc0c0c0cc000000ccc0c0c0cc000000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36641
namespace PEqualNP.Outside.L_meta_36641
open PEqualNP.Outside.L_meta_36641.Model
def s1K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s1K3 (i*5) 5
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s1K3 (6+((h/1+packedAt s1K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xf807f807f807ffffffe03f80fe03fffff318ff
  | 3 => 0xfff80007fffff807ffffc000fffff80ffc1fc7
  | 4 => 0xfffffff80007fff807ffffff0003fff01fe0f8
  | 5 => 0xfffffffffff8000007fffffffffc00001fff00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x590848304850889090a2c59516545a95256b5b
  | 2 => 0xaf4295529533952523d02ab0aac2af2e5318ad
  | 3 => 0x3256c6a4e4a5247645756044cd9b318b9c15c6
  | 4 => 0xc464e4c6c6c646447679b3668113c5c31ea0f0
  | 5 => 0x787070707078787879e3c78f1e2060c1bde00
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xaaaaaa00a0a0a000aaaaaa00a0a0a000aaaaaa00a0a0a000aaaaaa00a0a0a000aaaaaa00a0a0a000aaaaaa00a0a0a000aaaaaa00a0a0a000aaaaaa00a0a0a000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36641
namespace PEqualNP.Outside.L_meta_36641
open PEqualNP.Outside.L_meta_36641.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x1e52380803000022004c6213e1c79b2c0001d009d500003411c0c41223005c200220059234654264a0000a5621014000ca890a0c10410c0004100050103ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x2b29082d91000014000e9f85802587260d8b0000241583078f1f1c88820016060ca89c181a96ac0a8d1d97998e1e8f8000188011a82510002a15170005000000001a0392829d098a2c8481ad0c1b23012290a70400a9aaa3a193a6aba11900000927a220a01e24949300069b8b920002090024007060831336000800c58c80040c00414083970240188b7a92876c5250ebea6a15714d429faa2653c544cb9a64194f943419eaa4835f53506b8a6a0dbd4941b6292837b50506f0a0a0e7d4d41ce29a83af5250758a4a0edd4541dda82833c5050770a0a0ce141419f2a0836e52cc6daa598cf952319eaa4636e528c6daa518cf950319eaa0635e53c86baa790cf952219eaa4435e53886baa710cf950219eaa0435e53902baa7205b94a40b6a94819e539033aa7206b94a40d6a94813d519027ca1204f544409f28081ba501027ca9984f553309faa2613c544c2dea4985b14930bba8a6174514c2dca4185b548309f2a6413d54c827ea8904f15120afa9a415c53482eea2905d14520af298415d530827ca9884f55310dc206213f5484278a9084fd51109e2a2215f53442b8a6885bd4910b6292213e540427aa8085794c10aea98216e52042daa4086e10010
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x8e0a0240c605a3191320cb0c5314941c6d4c50507185314141cad4850507285214141c394e52902396510010
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 8
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (i*5) 5
  | 5 => packedAt s2K5 (i*16) 16
  | 4 => packedAt s2K4 (i*27) 27
  | 3 => packedAt s2K3 (i*38) 38
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (6+((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s2K5 (788+((h/14+packedAt s2K5 (704+(h % 14)*6) 6) % 63)*7) 7
  | 4 => packedAt s2K4 (2694+((h/30+packedAt s2K4 (2484+(h % 30)*7) 7) % 111)*8) 8
  | 3 => packedAt s2K3 (312+((h/2+packedAt s2K3 (304+(h % 2)*4) 4) % 10)*4) 4
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffffff81fffffe07ffffffffe03fffe3ffe3f
  | 1 => 0x3f81ffffffffffff81f03e07ffffffffc88fff
  | 3 => 0x3ffe03ffe03f81fffe003ff83ffc1f01f0f3cc
  | 4 => 0xc00003ffffc001ffffffc0003fffe001ff03f0
  | 5 => 0xfffffc00000001ffffffffffc0000001fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x84882808c489082016514a284a212954133615
  | 1 => 0x11245191091260c580a4148694c652a8c888ea
  | 3 => 0xa6149aa243a42b6aaa0927b227691c0d70d34c
  | 4 => 0x3459634492074db34d3d812439b38831bd03b0
  | 5 => 0x386183871c3871dc71ce39c701c210c1eeec00
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaaa88cc888888eeaaaa88cc888888eeaaaa88cc888888eeaaaa88cc888888eeaaaa88cc888888eeaaaa88cc888888eeaaaa88cc888888eeaaaa88cc888888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36641
namespace PEqualNP.Outside.L_meta_36641
open PEqualNP.Outside.L_meta_36641.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x15a51a440000000aa8003021b0a80026000c4920e28e210000023524c7813200000007c3173450022009cc163a015003c0870b48008001000004040300c040102043ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31df31fe31fd31dd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30de30fd30fc30dc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x3600009c003400020000985600000076141ab600000000000000964200060000000000004808ac8e16705a72a60000380090b000ae4c006c00b200005494001c5800005c32b43a104e00248a26122c008c646a0c4a827c0062004000222e8400000000000092007400a088500000003e00000000007a0e00000004a400807e006886182800005e0a20a2a860aa9a9e7866440052000000303c1e002a000000466e000600010600010003051402010504000003000000000200020000000b00b7a92876c5250ebea6a15714d42d6a10853f544ca78a8995b94b41b6a96835e53906baa720db94a41b6a94835e53106baa620d794331aea9c633f544c678a898dbd4931b6292637b504c6f0a098e7d5131ce2a263cf524c798a498f5d4531eda82635c504c7b0a098d614131af298633e54c867aa990cf952219eaa4435e53886baa710d794c21aea98435e53d02baa7a057d4d40ae29a816f52502d8a4a05dd4540ba28a816e52102daa4204f952309eaa4616e528c2daa5186795230ceaa461ce528c39aa5185754630af284615d510c2bca0187694030af29e415d53c827ea8904f15120afa9a415c53482eea2905d145209f2a0413d54082bca7885754f10ec186215f53842b8a7084fd51109e2a2215f53442b8a6885bd4910b6292213e540427aa8085794c10aea98216e52042daa408760c010
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0xce00648002a000a318d4210b0c5414931c6d50504c7185414131d2d48504c7485214131c3952528c259650c010
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 8
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (i*5) 5
  | 5 => packedAt s3K5 (i*16) 16
  | 4 => packedAt s3K4 (i*27) 27
  | 3 => packedAt s3K3 (i*38) 38
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (6+((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s3K5 (788+((h/14+packedAt s3K5 (704+(h % 14)*6) 6) % 63)*7) 7
  | 4 => packedAt s3K4 (2724+((h/30+packedAt s3K4 (2484+(h % 30)*8) 8) % 161)*8) 8
  | 3 => packedAt s3K3 (312+((h/2+packedAt s3K3 (304+(h % 2)*4) 4) % 12)*4) 4
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xff81ffffffffffe07ffffe03fffffffe3f8fff
  | 1 => 0x3ffffff81fffffff81f03fffff03ffffc8fe3f
  | 2 => 0x3ffe03ffe03f81fffe003ffc1ffc1f01f0f3cc
  | 4 => 0xc00003ffffc001ffffffc0001fffe001ff03f0
  | 5 => 0xfffffc00000001ffffffffffe0000001fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x80a428890489204016524a41254431541384d5
  | 1 => 0x15085110c91248a580a414964a234aa8c83a2a
  | 2 => 0xa6149aa243a42b6aaa0a275913e91c0d70d34c
  | 4 => 0x3459634492074db34d3c81921cb38831ed03b0
  | 5 => 0x386183871c3871dc71cf39e380c210c1beec00
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeaeac8c8a8a88888eaeac8c8a8a88888eaeac8c8a8a88888eaeac8c8a8a88888eaeac8c8a8a88888eaeac8c8a8a88888eaeac8c8a8a88888eaeac8c8a8a88888, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36641
namespace PEqualNP.Outside.L_meta_36641
open PEqualNP.Outside.L_meta_36641.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x9a00000000018018287c000000122b4e5c01e0038e82504068c009400400240112aa4596001550836001994c003a2407118a24840131e0060800040c0000280080ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31df31fe31fd31dd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30de30fd30fc30dc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x420000000c00561c64660052a24c6e8468000088b0000016a400003400288600000080a02a0000000006462c6a4a008e7a0400000000008c18b200a6000000240000000072ae78605e9a3c484e9832003e007c003800ac909630b69408209c580a7400000e1aa8929e000222361e6c0000007e147610aa6270448212b48a0026005c504000002e003a000000005a000054000002000903030a1500080f05000a0300000000000003000000020201010a05b7a92876c5250ebea6a15714d42d6a10853f544ca78a8995b94b41b6a96835e53906baa720db94a41b6a94835e53106baa620d794331aea9c633f544c678a898dbd4931b6292637b504c6f0a098e7d5131ce2a263cf524c798a498f5d4531eda82635c504c7b0a098d614131af298633e54c867aa990cf952219eaa4435e53886baa710d794c21aea98435e53d02baa7a057d4d40ae29a816f52502d8a4a05dd4540ba28a816e52102daa4204f952309eaa4616e528c2daa5186795230ceaa461ce528c39aa5185754630af284615d510c2bca0187694030af29e415d53c827ea8904f15120afa9a415c53482eea2905d145209f2a0413d54082bca7885754f10ec186215f53842b8a7084fd51109e2a2215f53442b8a6885bd4910b6292213e540427aa8085794c10aea98216e52042daa408760c010
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x400aec68200040a318d4210b0c5414931c6d50504c7185414131d2d48504c7485214131c3952528c259650c010
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 8
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (i*5) 5
  | 5 => packedAt s4K5 (i*16) 16
  | 4 => packedAt s4K4 (i*27) 27
  | 3 => packedAt s4K3 (i*38) 38
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (6+((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s4K5 (788+((h/14+packedAt s4K5 (704+(h % 14)*6) 6) % 63)*7) 7
  | 4 => packedAt s4K4 (2724+((h/30+packedAt s4K4 (2484+(h % 30)*8) 8) % 147)*8) 8
  | 3 => packedAt s4K3 (312+((h/2+packedAt s4K3 (304+(h % 2)*4) 4) % 13)*4) 4
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xff81ffffffffffe07ffffe03fffffffe3f8fff
  | 1 => 0x3ffffff81fffffff81f03fffff03ffffc8fe3f
  | 2 => 0x3ffe03ffe03f81fffe003ffc1ffc1f01f0f3cc
  | 3 => 0xc00003ffffc001ffffffc0001fffe001ff03f0
  | 5 => 0xfffffc00000001ffffffffffe0000001fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x80a428890489204016524a41254431541384d5
  | 1 => 0x15085110c91248a580a414964a234aa8c83a2a
  | 2 => 0xa6149aa243a42b6aaa0a275913e91c0d70d34c
  | 3 => 0x3459634492074db34d3c81921cb38831ed03b0
  | 5 => 0x386183871c3871dc71cf39e380c210c1beec00
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeac8eac8a888a888eac8eac8a888a888eac8eac8a888a888eac8eac8a888a888eac8eac8a888a888eac8eac8a888a888eac8eac8a888a888eac8eac8a888a888, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36641
namespace PEqualNP.Outside.L_meta_36641
open PEqualNP.Outside.L_meta_36641.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x41117360002100140002a00e804e5801100100000000000009000b00004804a00000000149c1c640805600d0014000001a000000c00a080000023006002800495130e001823e8000018000260078780000204100020c1010414000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21ef21fe21fd21ed21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20ee20fd20fc20ec20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x1b19239e0f00038000000d00000000001f00128711868c9401a60eab9d082910050e228f8c1d8924058a9321a31cac831807961700248019802780271f8026829c2d000a00000008800000099220801895822a0028139a842516aa8dad8000001128909a0029a5ab0bac001b978620009e8100150b04a122001481820c004b602141882098000080000024004960048000100800eb7a92876c5250f3a8621d7d4d42ae29a853f544ca78a8995794f41aea9e835e53906baa720db94a41b6a94836e52106daa420cf953319eaa6633e548c67aa918db94a31b6a94636e520c6daa418db94321b6a94433f5448678a890d7d4d21ae29a437b50486f0a090ebd5121d62a243cf5348798a690f9d4521f5a82436c50487d0a090da14121b7290436e52d02daa5a057d4d40ae29a816f52502d8a4a05dd4540ba28a815e53102baa6205b94b30b6a96613f544c278a8985bd4930b62926177514c2e8a2984f950309eaa0613e548827aa9105794e20aea9c41ae548835aa9107394e20e6a9c416d51882dca1105b54420b728041ea50082dca5885b54b10f4106216f52842d8a5084fd51109e2a2215f53442b8a6885bd4910b6292213e540427aa8085794c10aea98216e52042daa4087a08010
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x20e800006ac04002a31894310f0c5414d21cad5050487285414121d2d4c50487485314121c395253882696508010
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 8
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (i*5) 5
  | 5 => packedAt s5K5 (i*16) 16
  | 4 => packedAt s5K4 (i*27) 27
  | 3 => packedAt s5K3 (i*38) 38
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (6+((h/1+packedAt s5K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s5K5 (802+((h/14+packedAt s5K5 (704+(h % 14)*7) 7) % 90)*7) 7
  | 4 => packedAt s5K4 (2694+((h/30+packedAt s5K4 (2484+(h % 30)*7) 7) % 122)*8) 8
  | 3 => packedAt s5K3 (312+((h/2+packedAt s5K3 (304+(h % 2)*4) 4) % 14)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x3fffffffffffffe07ff01ffffffffffe38ffff
  | 1 => 0xff81fff81fffffff81ffff03ff03ffffcf8e3f
  | 2 => 0x3ffe03ffe03f81fffe001ffc1ffc1f01f0f3cc
  | 3 => 0xc00003ffffc001ffffffe0001fffe001ff03f0
  | 4 => 0xfffffc00000001ffffffffffe0000001fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x108829090489408016540546254621541834d5
  | 1 => 0x85245090c912286580a2aa214a215aa8c38a2a
  | 2 => 0xa6149aa243a42b6aaa0a93a913a91c0de0d34c
  | 3 => 0x3459634492074db34d3cc0c21cf388317d03b0
  | 4 => 0x386183871c3871dc71cf1cf380c210c1beec00
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xeca8a888eca8a888eca8a888eca8a888eca8a888eca8a888eca8a888eca8a888eca8a888eca8a888eca8a888eca8a888eca8a888eca8a888eca8a888eca8a888, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36641
namespace PEqualNP.Outside.L_meta_36641
open PEqualNP.Outside.L_meta_36641.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c381821404000040850002380850000001027fd5007fe54007f55007fc54027fd4c05fe53007f54c05fc5301ffd0c05fe43007f50c05fc43027fd4803fe52007f54803fc5201ffd0803fe42007f50803fc42017fcc803fe32007f4c803fc32027fd4401fe51007f54409fc5101ffd0401fe41007f50407fc41017fcc401fe31007f4c405fc3100ffc8401fe21007f48403fc21027fd4001fe50007f54009fc5001ffd0001fe40007f50007fc40017fcc001fe30007f4c005fc3000ffc8001fe20007f48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x842000ffd9510005feca880037f65440013fb2a200cff99510025fcca88003fd65440017eb2a200cff19510025f8ca880037c65440093e32a2000ffd9110005fec888003bf64440015fb22200bff9911001dfcc888003fd64440017eb22200bff1911001df8c888003bc64440075e322200cffd511005ffca888003fd5444017fe2a22000ffd8d10005fec688003df63440016fb1a200aff98d10015fcc688003fd63440017eb1a200aff18d10015f8c688003dc63440056e31a200cffd4d10057fca688003fd5344015fe29a200bffd0d10057fc8688003fd4344015fe21a2000ffd8910005fec488003ef624400177b122009ff9891000dfcc488003fd62440017eb122009ff1891000df8c488003ec624400376312200cffd491004ffca488003fd5244013fe292200bffd091004ffc8488003fd4244013fe212200affcc91004ffc6488003fd3244013fe192200cffd4510007fca288003fd5144019fe28a200bffd0510007fc8288003fd4144017fe20a200affcc510007fc6288003fd3144015fe18a2009ffc8510007fc4288003fd2144013fe10a200cffd4110007fca088003fd5044019fe282200bffd0110007fc8088003fd4044017fe202200affcc110007fc6088003fd3044015fe1822009ffc8110007fc4088003fd2044013fe1022000ffc4110007f62088003fe1044001fb0822000ffd9410005feca08023fe65040097f3282000df99410024fcca08003fd65040017eb282000df59410004faca08023fc65040097e3282000ffd9010005fec80801ffe64040077f3202000ef9901001d7cc808003fd64040017eb202000ef590100057ac80801ffc64040077e3202008ffd501003ffca808003fd540400ffe2a02000ffd8c10005fec60801bfe63040057f3182000f798c10015bcc608003fd63040017eb182000f758c10005bac60801bfc63040057e3182008ffd4c10037fca608003fd530400dfe2982007ffd0c10037fc8608003fd430400dfe2182000ffd8810005fec408017fe62040037f3102000fb9881000ddcc408003fd62040017eb102000fb58810005dac408017fc62040037e3102008ffd481002ffca408003fd520400bfe2902007ffd081002ffc8408003fd420400bfe2102006ffcc81002ffc6408003fd320400bfe1902000bf98410047fea208003fe5104001fea882008ff1441003ffe8208003fe4104001fea082007ff10410037fe6208003fe3104001fe9882006ff0c41002ffe4208003fe2104001fe9082005ff08410005fcc008023ff5004001ff2802000ff54010047f8a00801fff4004001ff2002000ff5001003ff8800801bff3004001ff1802000ff4c010037f86008017ff2004001ff1002000ff4801002ff84008003ff1004001fb8802000ff84010007f42008003fd1004001fa8802000fe44010
  | 1 => 0x3fd6148001fe30a4000bf185200bffea290003fe5148001fea8a4017ff145200b7fe8290003fe4148001fea0a4016ff105200affe6290003fe3148001fe98a4015ff0c52000ffe4290007ef2148003ff10a4001ff48520007da4290007fc21480037fb024017ffd4120007fca090003fd504802ffe2824016ffd0120007fc8090003fd404802dfe2024015ffcc120007fc6090003fd304802bfe1824001ffc812000ff64090007fe2048001f71024001ff0812000fd84090007f82048001ffb2e2000bfd97100a7fccb88012fe65c4001feb2e2000bf597100a7f8cb88012fc65c4001ffb262000bfd931009ffcc98800efe64c4001feb262000bf5931009ff8c98800efc64c4029ffaa62013ff95310007faa98804ffc54c4001ffb1e2000bfd8f10097fcc78800afe63c4001feb1e2000bf58f10097f8c78800afc63c4029ffa9e2012ff94f10007faa78804bfc53c4027ffa1e2012ff90f10007fa878804bfc43c4001ffb162000bfd8b1008ffcc588006fe62c4001feb162000bf58b1008ff8c588006fc62c4029ffa962011ff94b10007faa588047fc52c4027ffa162011ff90b10007fa8588047fc42c4025ff9962011ff8cb10007fa6588047fc32c4029ffa8e2000ff94710007faa388053fc51c4027ffa0e2000ff90710007fa838804ffc41c4025ff98e2000ff8c710007fa638804bfc31c4023ff90e2000ff88710007fa4388047fc21c4029ffa862000ff94310007faa188053fc50c4027ffa062000ff90310007fa818804ffc40c4025ff9862000ff8c310007fa618804bfc30c4023ff9062000ff88310007fa4188047fc20c4001ffb2c2000bfd9610087fccb08012fe6584001feb2c2000bf59610087f8cb08012fc6584001ffb242000bfd921007ffcc90800efe6484001feb242000bf5921007ff8c90800efc6484021ffaa4200fff95210007faa90803ffc5484001ffb1c2000bfd8e10077fcc70800afe6384001feb1c2000bf58e10077f8c70800afc6384021ffa9c200eff94e10007faa70803bfc538401fffa1c200eff90e10007fa870803bfc4384001ffb142000bfd8a1006ffcc508006fe6284001feb142000bf58a1006ff8c508006fc6284021ffa94200dff94a10007faa508037fc528401fffa14200dff90a10007fa8508037fc428401dff994200dff8ca10007fa6508037fc32840017eb0c2010ffd4610007fca308003fd5184021fe28c200fffd0610007fc8308003fd418401ffe20c200effcc610007fc6308003fd318401dfe18c200dffc8610007fc4308003fd218401bfe10c2000bf98210087fea108003fe5084001fea842010ff1421007ffe8108003fe4084001fea04200fff10210077fe6108003fe3084001fe984200eff0c21006ffe4108003fe2084001fe904200dff08210007fe2108003f71084001fd8
  | 2 => 0x30017fca69800bfd534c005fe29a6002ffd0d30017fc869800bde434c005fea1a6000f750d30017f88698003ff624c0017fb12601bff9893000dfcc498003fd624c037fe3126001bf189300effea49806ffe524c001fea92601bff149300e7fe849806ffe424c001fea12601bff10930017fe649800bfe324c005fe9926002ff0c930007fec298002ff614c001ff30a6000ff58530007f8c298002fc614c03bffa8a6000ff94530007faa298077fc514c039ffa0a6000ff90530007fa8298073fc414c005ff98a6002f7cc530017fc629800bfd314c001ee98a6002ff0c5300dffe4298003fe214c001fe90a601bff08530015fec098077ff504c001ff2826000ff541300eff8a098073ff404c001ff2026000ff501300e7f8809800bff304c005fd9826002ff8c130007bc609800bfc304c005ee1826002fe0c1300dffe409806ffc204c001ffb2c4000bfd96200d7fccb10012fe6588001feb2c4000bf596200d7f8cb10012fc6588001ffb244000bfd92200cffcc91000efe6488001feb244000bf592200cff8c91000efc6488035ffaa44019ff95220007faa910067fc5488001ffb1c4000bfd8e200c7fcc71000afe6388001feb1c4000bf58e200c7f8c71000afc6388035ffa9c4018ff94e20007faa710063fc5388033ffa1c4018ff90e20007fa8710063fc43880037eb144001ffd4a200d7dea510007fe5288003fea944001ff14a2000fd8a510007ff4288003ff2144001ff50a2000ff88510007ff3288003ff1944001ff4ca2000ff86510003ff6188001ff30c4000bf98620007fac310002fd6188001fe30c401affd4620007fca310003fd5188035fe28c4019ffd0620007fc8310003fd4188033fe20c4018ffcc620007fc6310003fd3188031fe18c4001ffc862000ffc4310003ee2188003fe90c4001ff0862000fd84310006fe6088035ffa844000ff94220007faa11006bfc5088033ffa044000ff90220007fa8110067fc4088031ff9844000ff8c220007fa6110063fc3088003ff9044001fbc822000ff64110007fc2088003fc1044000ffd9520005feca900037f65480013fb2a4017ff99520025fcca90003fd65480017eb2a4017ff19520025f8ca900037c65480093e32a4000ffd9120005fec89005bfe64480077f3224000ff59120005fac89005bfc64480077e3224017ffd51200b7fca890003fd544802dfe2a24000ffd8d20005fec690057fe63480057f31a4000ff58d20005fac690057fc63480057e31a4017ffd4d200affca690003fd534802bfe29a4016ffd0d200affc8690003fd434802bfe21a4001bfd892000ffea490007fe5248003f72924001ff54920007daa490007fc5248003ffa124001ff9092000ffa8490007fc4248003ff9924001ff8c92000ffa6490007fc3248001ffb0a4000bfd8520007fcc29000
  | 3 => 0xfa848000ff94240007faa12009bfc5090007ffa048003efd024001ff6812000ffc4090007fc2048025ffcc24012ff86120093ff2090049fe1048000ffd9540005fecaa008ffe65500097f32a8000ff59540005facaa008ffc65500097e32a8003bfd914001ffea8a000ffe5450007feaa28003ff15140007fec6a0002ff6350001efb1a8000b7d8d40117fcc6a000afe6350001feb1a8022ff18d40015f8c6a0003dc63500056e31a8023ffd4d40117fca6a0003fd5350045fe29a8003ffd0d4001f7e86a000ffe4350007fea1a8000ef50d4001ff886a0003ff62500017fb128021ff9894000dfcc4a0003fd6250043fe3128001bf1894011ffea4a0087fe5250001fea928021ff1494001ffe84a000ffe4250007fea128003ff10940117fe64a0087fe3250001fe9928021ff0c940007fec2a0002ff6150001ff30a8000ff58540007f8c2a0002fc6150047ffa8a8000ff94540007faa2a008ffc5150007ffa0a8003efd054001ffc82a000ffd4150001dea0a8003ff10540117fe62a0003fe3150001fe98a8022ff0c54010ffe42a0003fe2150001fe90a8021ff0854001dfec0a008fff5050001ff2828000ff5414011ff8a0a000fff4050007fda028003ff901400077c80a000ffc4050007de2028003fe10140117fe60a008bfc3050043ff9028021ff08140007fecb18002ff658c041ff32c6004bf99630007facb18002fd658c041fe32c6004bf19630007fec918002ff648c03fff3246003bf99230007fac918002fd648c03ffe3246003bf19230107fea91807ffe548c001feaa4601fff15230015fac71800bff538c005ff29c6002ff54e30017f8a71800bff438c03fefa1c6002ff90e30017fa871800bfc438c005ee21c6000ffd8a300f7fcc518006fe628c001feb146000bf58a300f7f8c518006fc628c041ffa94601eff94a30007faa51807bfc528c03fffa14601eff90a30007fa851807bfc428c005ff9946002ff8ca30017fa651800bfc328c001ffb0c6000ff98630005fcc318003fd618c0017eb0c6000ff18630107fea318003fe518c001fea8c6020ff146300fffe8318003fe418c001fea0c601fff10630017fe631800bfe318c001ef18c6002ff4c630017f8631800bdc318c03dff90c6000ff88630007fa431807bfc218c0057f3046020ffd4230007fca118003fd508c041fe284601fffd0230007fc8118003fd408c03ffe2046002ffcc230017be611800bfb308c005fe1846002fe0c2300f7fe411807bfc208c001ffb2a6000bfd95300effcca98012fe654c001feb2a6000bf595300eff8ca98012fc654c001ffb226000bfd91300077ec898002bf644c039ff3226003bf99130007fac898002fd644c039fe3226003bf1913000778c89800ebc644c03bffaa2601cff95130007faa898073fc544c0057fb1a6002ffd4d
  | 4 => 0x3ff6294055ff314a001bf98a50007fac528002fd6294055fe314a001bf18a50027fea528013fe5294055bf294a004ff54a50027f8a5280137c5294059ffa14a02aff90a50007fa85280abfc4294057ff994a02aff8ca50007fa65280abfc3294001ffb0ca000ff98650005fcc328003fd61940017eb0ca000ff18650027fea328013fe5194001bf28ca004ff54650027f8a3280137c5194059ffa0ca000ff90650007fa83280b3fc4194057ff98ca000ff8c650007fa63280affc3194055ff90ca000ff88650007fa43280abfc21940097f304a004ffd4250026fea128013fb5094009fe284a004fe14250167fe81280b3fc4094057ff984a02bff0c250157fe41280abfc20940097fb2aa000ffd9150005fec8a80a7fe64540077f322a000ff5915014ff8c8a800efc6454009ffaa2a004ff95150027faa8a8013fc5454001ffb1aa000bfd8d50147fcc6a800afe6354001feb1aa028ff18d50015f8c6a8013ff5354009ff29aa004ff54d50027f8a6a80a7ff4354051ff21aa000ff50d50147f886a8003ff62540017fb12a000fbd8950005dec4a809ffe62540037f312a000ff5895013ff8c4a8006fc6254001f6312a001bb18950027fea4a80137f5254009ff292a004ff54950006faa4a8013fc5254053ffa12a027ff90950007fa84a809ffc4254051ff992a027ff8c950007fa64a809ffc3254001ffb0aa000bfd8550007fcc2a8003fd6154001fe30aa000bf18550027fea2a80137f5154009ff28aa004ff54550006faa2a8013fc5154053ffa0aa000ff90550007fa82a80a7fc4154051ff98aa000ff8c550007fa62a80a3fc315404fff90aa000ff88550007fa42a809ffc21540097fb02a004ffd4150027f6a0a8013fe5054001bf282a004ff14150026f8a0a8013f85054053ffa02a029ff10150147fe60a80a3fc305404fff902a027ff08150007fecb20002ff659004dff32c8004bf99640007facb20002fd659004dfe32c8004bf1964001dfac92000fff5490007ff2a48003ff5524001ff8a920003ff639004bff31c8002bf98e40007fac720002fd639004bfe31c8002bf18e40137fea720097fe5390001fea9c8025ff14e4001ffe872000ffe439004bdf21c8003ff50e4001ff8872000fbc4390001ffb148024ff98a4000dfcc520003fd62900017eb148024ff18a4000df8c52009bff5290049ff2948000ff54a40127f8a52000fff4290007ff2148003ff50a4001ff88520097ff3290049ff1948000ff4ca40127f86520003ff6190001ff30c8000bf98640007fac320002fd6190001fe30c8026ffd4640007fca320003fd519004dfe28c8003ffd064001ffc8320003be4190007fea0c8003ff1064001f788320097ff3190001ff18c8000ff4c64012ff86320093ff2190001ff10c8000ff48640127f8432000efe609004df
  | 5 => 0xc531017f8629880bdc314c405fa18a6233ffc853119ff84298803ff604c4017fb026200ff98131007fac098803fc604c4017e3026235ffd41311aff8a0988d3ff404c469fe2026202ffcc131017be609880bfc304c467ff9026233ff08131007fecb10802ff6588465ff32c4204bf99621006fccb108127e6588401feb2c4200bf59621006facb108027d6588465fe32c4204bf19621007fec910802ff6488463ff3244203bf99221007fac910802fd6488463fe3244203bf19221197fea9108c7fe5488401feaa44231ff15221007fec710802ff6388461ff31c4202bf98e21007fac710802fd6388461fe31c4202bf18e21197fea7108c3fe5388401fea9c4230ff14e2118ffe87108c3fe4388401fea1c4230ff10e2100dfac510807ff5288403ff2944201fb94a2100ffaa510803ed5288403fe2944201ffd0a2100ffc8510807fd4288403fe2144201ffcca2100ffc6510807fd3288403fe1944201bf98621197fea310803fe5188401fea8c4232ff1462118ffe8310803fe4188401fea0c4231ff10621187fe6310803fe3188401fe98c4230ff0c62100ffe4310807ef2188403fb90c4201ff0862100fe84310803ff6088401ff3044200bf98221007fac110802fd6088401fe3044232ffd4221197f8a1108c7ff4088463fe2044230ffcc221187f86110807ff2088403fe1044201fb08221007feca90802ff654845fff32a4204bf99521007faca90802fd654845ffe32a4204bf19521007fec890802ff644845dff3224203bf99121007fac890802fd644845dfe3224203bf1912117ffea8908bbfe5448401feaa2422eff15121007fec690802ff634845bff31a4202bf98d21007fac690802fd634845bfe31a4202bf18d2117ffea6908b7fe5348401fea9a422dff14d21177fe86908b7fe4348401fea1a422dff10d2100dfec490807ff524845ff7a924201ff9492100ffaa490807fc5248403f62924201ffd092100ffc8490807fd4248403fe2124201ffcc92100ffc6490807fd3248403fe1924201bfd852117ffea290803fe5148401fea8a422fff14521177fe8290803fe4148401fea0a422eff1052116ffe6290803fe3148401fe98a422dff0c52100ffe4290807f72148403ff10a4200fb8852100ff84290807ec2148403fa10a4200ffd8121005fec090803fe6048401feb024200ff18121005f8c0908bfff504845ffe282422effd0121177f880908b7ff304845bfe1824201ffc812100fde4090807fc20484097eb2ca000ffd9250167fcc92800efe6494001feb24a000bf59250167f8c92800efc6494009ffaa4a004ff95250027faa928013fc5494001ffb1ca02bff98e50015fcc728003fd63940017eb1ca02bff18e50015f8c728013ff5394009ff29ca004ff54e50027f8a7280b3ff4394057ff21ca000ff50e5015ff88728
  | 6 => 0x7fe32a8204bf1954101dfec8a080fff5450407ff2a28203ff5514101ff8a8a0803ff63504017fb1a823aff98d41015fcc6a0803fd6350475fe31a8202bf18d411dffea6a08ebfe5350401fea9a823aff14d4101ffe86a080ffe4350475df21a8203ff50d4101ff886a080fbc4350401ffb128200bfd89411cffcc4a0806fe6250401feb128239ff1894100df8c4a08efff5250473ff2928200ff549411cff8a4a080fff4250407ff2128203ff5094101ff884a08ebff3250473ff1928200ff4c9411cff864a080eff6150477ffa8a8200ff94541007faa2a08effc5150407ffa0a8203fdd054101ffc82a0803be4150407fe20a8203ef1054101fe882a08ebff3150475fe18a8239ffc85411cff842a0803ff60504017fb028200ff98141007fac0a0803fc60504017e302823bffd41411dff8a0a080fff4050407dfa028203ff101411d7fe60a08ebfc3050473ff9028239ff08141007fecb18802ff658c471ff32c6204bf99631007facb18802fd658c471fe32c6204bf19631007fec918802ff648c46fff3246203bf992310077cc91880ebe648c401feb246200bf592310077ac918802bd648c46ffe3246203bf192311c7fea9188dffe548c401feaa46237ff15231015fac71880bff538c405ff29c6202ff54e31017f8a71880bff438c405ff21c6202f790e31017fa8718803dd438c405fe21c6200ffd8a311b7fcc518806fe628c401feb146200bf58a311b7f8c518806fc628c471ffa946236ff94a31007faa5188dbfc528c46fffa146236ff90a31007fa85188dbfc428c405ff9946202ff8ca31017fa651880bfc328c4057f30c6238ffd4631007fca318803fd518c471fe28c6237ffd0631007fc8318803fd418c46ffe20c6202ffcc631017be631880bf7318c405fe18c6202fd0c6311b7fe43188dbfc218c401ffb046200ff98231005fcc118803fd608c4017eb046200ff182311c7fea1188e3fc508c46fffa046237ff10231017fe611880bfc308c405ee1846236ffc82311b7f84118803ff654c4017fb2a6235ff99531025fcca98803fd654c4017eb2a6235ff19531025f8ca98803ff644c4017fb226234ff9913101dfcc898803fd644c4017eb226234ff1913101df8c8988d7ff544c469ff2a26200ff551311a7f8a89880aff634c405ffa9a6202ff94d31017faa69880bfc534c405ffa1a6234f7d0d31017fc869880bfd434c405fe21a6202f710d31007fec498802ff624c467ff3126201bf98931007fac4988cffc624c4037e3126235ffd493119ffca498803fd524c467fe2926234ffd093119ffc8498803fd424c467fe2126202ffcc931017fc649880bfd324c405fe1926202bfd85311affea298803fe514c401fea8a6235ff145311a7fe8298803fe414c401fea0a6234ff10531017fe629880bf7314c405ff18a6200f78
  | 7 => 0x28913ff4394487ff21ca200ff50e5121ff88728803ff6294485ff314a201bf98a51007dcc528806ee6294401feb14a200bf58a51007dac528802ed6294485fe314a201bf18a51027fea5288137f5294409ff294a204ff54a51006faa528813fc5294489ffa14a242ff90a51007fa852890bfc4294487ff994a242ff8ca51007fa652890bfc32944097f30ca204ffd4651026fea328813f75194409fe28ca204fd14651227fe8328913fc4194487ff98ca243ff0c651217fe432890bfc2194401ffb04a200ff98251005fcc128803fd60944017eb04a200ff18251027fea128813fc5094409be284a244ffd0251227f8812890fff3094487fe184a242ffc8251217f84128812ff6554401ffb22a200bfd915120ffcc8a880efe6454401feb22a241ff1915101df8c8a8813ff5454409ff2a2a204ff55151027f8a8a8803ff63544017fb1aa240ff98d51015fcc6a8803fd6354481fe31aa202bf18d51027fea6a8813fe5354409fea9aa204ff14d5120ffe86a8903fe4354401fea1aa240ff10d51007fec4a8802ff625447fff312a201bf98951007fac4a88fffc62544037e312a204ffd4951027fca4a88ff7e5254409fea92a204ff14951026f8a4a8907ff425447fff212a200ff509511fff884a8903ff325447fff192a200ff4c9511fff864a8812ff6154409ffa8aa204fdd4551027fca2a88037e5154409fe28aa204df14551027e8a2a8907ff4154483fe20aa240ffcc551207f862a88ffff215447ffe10aa200ffd8151005fec0a8803fe6054401feb02a200ff18151005f8c0a8813ff5054409bfa82a204ff1415120ffe80a8907fc4054481ff982a240ff0c1511fffe40a88fffc2054401ffb2c8200bfd96411f7fccb20812fe6590401feb2c8200bf596411f7f8cb20812fc65904077eb248203ffd524101ffca92080ffd5490407fe2a48200ffd8e411effcc72080afe6390401ef31c8202b798e41007fac720802fd6390401eeb1c8200b758e411eff8c72080afc639047dffa9c823dff94e41007faa7208f7fc5390407ffa1c8203efd0e4101ffc872080ffd4390401dea1c8203ff10e41007fec5208f3fe62904037f3148200ff58a41005fac5208f3fc62904037e314823effd4a411e7fca520803fd5290479fe2948203ffd0a4101ffc852080ffd4290407fe214823dffcca411e7fc6520803fd3290479fe1948203bf986411f7fea320803fe5190401fea8c823eff1464101ffe832080fbf4190407fba0c8203ff1064101fe883208f7ff319047bfe18c823cffc86411e7f84320803ff6090401ff3048200bf98241007fac120802fd6090401fe304823effd42411f7f8a12080fff4090407fe2048203ef102411effe61208f7fc3090479ff904823cff08241007fecaa0802ff6550477ff32a8204bf99541007facaa0802fd655047
  | 8 => 0xfd4d52027fca6a9013fd5354809fe29aa44affd0d5224ffc86a9003fd4354893fe21aa401bfd895200ffea4a9013ef5254803ff292a401df9495200ff8a4a90077c5254803f6292a401db1495200ffe84a9007fe4254803fe212a401ffcc95200ffc64a9007fc3254801ffb0aa400bfd8552007fcc2a9003fd6154801fe30aa400bf18552027fea2a9013fc5154809be28aa44affd0552257f882a9127ff3154893fe18aa401ffc855200ff842a9007ec2154801ffb02a400bfd8152007fcc0a9003fd6054801fe302a400bf18152027fea0a90137f5054809fe282a44affd0152257f880a9127ff3054893fe182a401ffc815200fde40a9007fc2054801ffb2a8400bfd9542247fccaa1012fe6550801feb2a8400bf59542247f8caa1012fc65508037fb228403ffd514201ffca8a100ffd5450807fe2a28400ffd8d42005fec6a111ffe63508057f31a8400ff58d4223ff8c6a100afc6350891ffa9a8447ff94d42007faa6a111ffc5350807ffa1a8403ff90d4201ffa86a100ffc43508037fb128401ffd494200ffca4a1007fd5250803fe2928401ffd094201fde84a1007fe4250803df2128401ff1094200f7884a1007ec4250803ff9928401ff8c94200ff864a1003ff61508017fb0a8400ff98542007fac2a1003fc61508017e30a8448ffd4542247f8a2a100fff4150807fe20a8447ffcc54223ff862a1007ff2150803fe10a8400ffd8142005fec0a1003fe6050801feb028400ff18142005f8c0a1123ff5050891fe2828403ffd014201ff880a111fff305088ffe1828401ffc814200ff840a1003ff654c8017fb2a6446ff99532025fcca99003fd654c8017eb2a6446ff19532025f8ca99003ff644c8017fb226445ff9913201dfcc899003fd644c8017eb226445ff1913201df8c89911bff544c88bff2a26400ff5513222ff8a899006ff634c805ffa9a6402ff94d32017faa69900bfc534c805ffa1a6402ff90d32017fa869900bfc434c8037fb126401ffd493200ffca499007fd524c803fe2926401ffd093200ffc8499007fd424c803fe2126401ffcc932017de6499007fe324c803ef1926401ff0c93200fb86499007ec324c801ffb0a6400bfd8532007fcc299003fd614c801fe30a6400bf18532237fea29911bfc514c88bffa0a6445ff10532017fe629900bfc314c803ff90a6401ff08532007fec099002ff604c801ff3026400ff58132007f8c099002fc604c88dffa826446ff1413222ffe8099117fc404c805ff9826402ff0c13200ffe4099007fc204c8097eb2ca200ffd9251227fcc92880efe6494401feb24a200bf59251227f8c92880efc6494409ffaa4a204ff95251027faa928813fc5494401ffb1ca243ff98e51015fcc728803fd63944017eb1ca243ff18e51015f8c728813ff5394409ff29ca204ff54e51027f8a7
  | 9 => 0x7bf2a2a803ff1515401ef8a8aa00fbc5455001ffb1aa800bfd8d54287fcc6aa00afe6355001feb1aa850ff18d54015f8c6aa013ff5355009ff29aa804ff14d5401ffe86aa00ffe4355007fe21aa800ffd8954005fec4aa13ffe62550037f312a800ff5895427ff8c4aa006fc6255009ffa92a804ff94954027f8a4aa00fff4255007ff212a803ff10954287fe64aa13ffe325509ffe192a800ffd8554005fec2aa003fe6155001feb0aa800ff18554005f8c2aa013ff5155009fe28aa803ffd055401ff882aa143ff31550a1fe18aa84fffc855427ff842aa003ff60550017fb02a800ff98154007fac0aa003fc60550017e302a804ffd4154027f8a0aa00fff4055007fe202a850ffcc154287f860aa13fff205509ffe102a802bfd9553007fec8a9802ff6454c9dff322a603bf99153007fac8a993bfc6454c077e322a604ffd5153027fca8a9813fd5454c09fe2a2a602bfd8d53017fea6a9813df5354c05ff29aa602df94d53017f8a6a980b7c5354c05ee29aa602ffd0d53017fc86a980bfc4354c01ffb12a600bfd895326ffcc4a9806fe6254c01feb12a64dff1895300df8c4a9813ff5254c09ff292a604ff14953277fe84a9937fe4254c9bfe212a602ffcc953017fc64a980bfc3254c01ffb0aa600bfd8553007fcc2a9803fd6154c01fe30aa600bf18553027fea2a9813fc5154c9dffa0aa64eff10553017fe62a980bfc3154c9bff90aa64dff08553007fec0a9802ff6054c01ff302a600ff58153007f8c0a9802fc6054c09ffa82a604ff14153277fe80a993bfc4054c05ff982a602ff0c15326ffe40a9937fc2054c01ffb2a8600bfd9543267fccaa1812fe6550c01feb2a8600bf59543267f8caa1812fc6550c057fb228603ffd514301ffca8a180ffd5450c07fe2a28602bfd8d43017fea6a180bfe5350c05fea9a8602ff14d43017fe86a180fdf4350c05ff21a8602ef90d43017f886a180bbc4350c05ee21a8602e710d43007fec4a1802ff6250c97ff3128601bf98943007fac4a192ffc6250c037e312864cffd494325ffca4a192ffc5250c07ffa128603ff9094301ff884a180bff3250c05ff1928602ff0c943007fec2a1802ff6150c01ff30a8600ff58543007f8c2a1802fc6150c99ffa8a864cff1454301ffe82a180ffc4150c07de20a8602ffcc543017f862a180bdc3150c97ff90a864bff08543007fec0a1802ff6050c01ff3028600ff58143007f8c0a1802fc6050c99ffa82864cff1414301ffe80a180fbf4050c07fe2028602ffcc143017be60a180bfc3050c97ff902864bff0814300dfecaa9003ff64548017fb22a44aff9915201dfcc8a9003fd6454895fe322a403bf19152027fea8a9013fe5454809feaa2a404ff15152007fec6a9002ff6354893ff31aa402bf98d52007fac6a9127fc63548057e31aa404f
  | 10 => 0x2002000800000200000000000020030000004000009000000400000500000040000000020004000001000000800400000000080000000008000008000000800000000000000000000000008004002001006000400000400000000020000000004008001000000000200400000000000000028000000001000800c000000000000800000100000040020000008000008002000800c0000010000004002000000000c0000010020004008000000000000000200000040160000000000000000000800000600000000080000000030000006000003000000000000000000060000020000000005000001000200000000040040020008000000000000803c00000000000040000020000008002000000000000200000000040040000008000000002000000000000000280000000000078000004000000001000600000080000020060000000000000000000800000100000000080000028000002001000800c00200000000080060010010000012001000801c008001000800000800000000000020000018004000000000000000000000000100020020008000004000000000400000000000000000000000004002002000000c0000000000000000002000800000600300200100040010000000002000000000000000000000000020080000004000002000800000000300000040060020020004002002000800000a00000000000000010000000000002001000000a00200200000000010000000000003001800000000300100080020020000004006000000000400200000000000000000010000002002000000000200000000080040010000000000002001000000000000000000020020028000002001000000c00600000000100060000020000004006000000000000100000040080010010000002002000000000000000080080040010000000000000000000400200600000000020000000000000000000000800200100180000040050000008004000000000000200100000000040000008000004001001000000200000080080040000008008000000001000000c000000000400400000000000020000000000000002000800800000c000800000a000000800400200000000000020000008000008000000000000000100180040000000000000006001000800000200400000040000000008000000001000001000400000180040020010030000000000001000000e0030000004000003000000000000400000000000010000000000002000000400000200080000000000028000002000000800000a0000048000000000001001000000200100000000000000000000001001000000000000000000020000010010006000000000000a0010000004000004000000400000000100eff65550077fb22a803ffd51540277ea8aa00ffe5455
  | 11 => 0x5c140c04c800082f000000000000000000003f40000001eac00000000000006ac226000000000000000000000007451e180000000000fd8d6000000036c800111a0002af8000000000000100017a00019615b8e9814d20e145400050730b9ec4000000000111400000000002a044432f00007f00000000000a4846817a13d80004c2000000000041c64600001b10f60000000000000000000000000000000000000000002b4000000000000000008820003de8a1057e00003100009804590001e780001f62158cf400000028b183cb6e0c403384dcae400000006cc00073a000000098c5950000b8800000000000000005da00000000000003578000000545135a0c400000000000001f800f000000074c000000106800000002900006340b8000000005e14400000000000000000b28b2200000021d40000002d480000000000000000a620000bf0000000000000140800000000001e00000000000000e060003a8000000000000016e80000000000000000000000000000000018f800000065d000000014600000000000000000000000ade00010b0000df4244108000083089b4420e205160000001f8000000000000003a22330000000446000279800000000000000d000000035800000007640000000000036000000086821d000000000000008d0000000000216800000000026502b08b04423868000000000000000000000000000000000000000000d1802000021d0000000000000000000000011b40000000d300010900004490e88000000000000000000000000000000001cc8ff4000000000182c00000000000000920000000c501e20002c5000034250f000093c00008000016106b80000f39c1c0000000000384b500002c900000006f93558000de800000000000000ec0000000c120002bc000090413800000000001f00001b0497812d3b40000000000000018cf0c0000000000bee00042b05c40000003ec9740baa00000000000004b238e07c8000000000000000000000000000000000000000000000000000000000000000000000002501f4c660000000121042812412d80000006b43a21bfc00064500000000002820000000ce0000000000000000000000000005a2000104000000036000000002b927380000010000000004001000800000000000180040000000000004002000000000400600000000000000000000000000000000000000400000100040000010008000006002000000800000300000000000000000000008000000000400000200000000040010000004004000000000800e00400180000020010008010000004000800400200000000000040000000000000005000000000c00100100000040000000004002000000000000200000080040000000028004000000000000c0000020000000006000001
  | 12 => 0x60001cb8d9a08900c00000000000001c4901400000000000000000000adc00029000000000005fb00400000000000000000000000000147c0000002ba800002600000000000000000000000000000089000000000000000000000040001de0bae000251800000000008880000000004498000d6400000000000000000af80000000000000db00000000c500000000000f3000000032e00000000000000000000000000000000000000000000000000001d219e0a4a271000219c00000024e888400023f2011a74d0e70f0001e4400081900020dc1a200000001b8000000153800059e00000021149ec39b0000000ce20003b00000c925e329b80000003110000000880000000000000014c2319e2ca30000000013400000000000009820000348000000000332000000000031380000000002488000000000445800079a0de1d80000bde000000000000046600000008b81230001d4c00000000000000000000578000eaa00000000007de7300000000000000000000000000014a80000e873d2c8138cdf00002d680002b60703b99fe80000000000f98000000000124000000019c96c800000000000000006e700000000000003d68000d8800000010e80000001798000c62000000000000000000000000000002ab0000000000000000000048900000007c0382000000000000000000003320943e90000000264000000077a7170e28000000304000000000000033d000000000000000000000000cd13c50a20003e080001c8839000000063c7a50000b0821225f00000000000000000f5c0008130001e30a5600000487043360e52dc89400000000e9863ccb0000000000000000000006b40002bd31f80000000002ed80000003600001600000000291841479e0e6000000000000000a847039200004f80000003ba07b1cac000420000000000007e00000010fe1940000cd491417500000000000000ab00000000000188000000000000000000000000000009540000000000000000000000000000000000001c000034e00000000000000000080000000000000088e00000007723fe000215c0000003c712f403c0000001ba4ff80001ec07d000000006480000000000000000000000000000000057b00005600002fe000000106400000012e000018b00000000000000000bb50c6000000000000071e33a8b18000000000000000055042c0000a5c0000000000000000324000000083406c06d400000034b80000000000d7a1b476a0003e18000b8e1d228019b0b7e0000000708eac000366092800061d09522242c600007f1fe50583a3000000000037b0000e381f048000017e000011b000041800030b23900000000000001e200000001a800000000000001cec00032a01e8000f06000000128497e78200000006de0000000288292000000000
  | 13 => 0x300007770000000000000000000000000000000000000000001588bfe10e000000000000000017787ca000000000005833c000003400000000000000000470000000e3a000000000003a198000000107a00000000000004a700000000004c83f89ec800048c0000314b3000000007a40004fc000000000000040f8c881c60000000000f3400000005b000000000006489ea00000380000005e000000000000000001138f700000000000000000000220c0006fb2031b700002f1000000000000027f80007b400000000000be48e2aa1594a9a00003e00000000001578000e0a0000001934fee28d0000000000000000000000000000018b0000000000000000084f00002b800000000000000005ec397800000017c069800074e000000000000000000000000000000000ef800000000000000000001ee800000000044880010f80000000000000000000126cd42000000000004a0000a1068000000000000005d45f02e618b800001f15800000001600000000000046000000000002d3bf000000000000000000000000758000000000000000000000002a000000000000011d8000000000000000000000000000003f0124800000000000000000004990000000ba8000000000000000000009580000000002188e320003710a0c00063a0000000000000120800071e6f10000000000000000000000012f1520ad40004833d00f300000003280b8400000000000002ca51e0002260cca00000000000000000000ab0a8800000009fc4b04650000a5cc385c201c016902e2890001d2903c26a0001fd000000000000000000000001f6901649f000000000015216e8f4513a0001548bd400000000000000001f90000000a802c800000006240002ac00000000000c18000d6c00043b894800062422f000067444d000000000038111d07000000001838f84fec1de2d7800000000020d87d4dd068030387700000004378ac80460001b3040400000000000000000000821e1ca380001bc000024e0000000000000000000000000027700000009dc00000012c00000000001dd8f2c000000000000075b11e8000000000000000000000000000000005d12689eb800000025580000002e62da19a0ae00003e113540000000000cfcd140000000dcc2420002e780002da8280000000000000378078481c273423800000000032000007c826d0000000a0c0001c1800000000014b0000000280000000000032400008040007e50001a18cb22d100021109e869e00000009ac2cb3001360a7204517a21c489218e25c8000a662de42c800000000000000000000002ab9b200005b02a0907c00080716a00000000001c480000000003fd85f400000006180000000000000000fda7390000000ccc7660000000000000000000000000000000010b800005690f000082
  | 14 => 0x372b39b600000001a280000000d930280000000000000fcc00041913d000000025300000000000000000000652000000000000000000000000000000001c003ee71a00000000b863c3c2000039e00035d85e42942b3000000062000043280000000000b48f58a3a779000000000000000004ec000000000000007e00000000ac1943c928080002300560a3000000050831400000000000000000ab400000000000001da06f800000018c00000000000001c507acd8600000000008c0000000000000000000000000000000000000f3600000000000000000001048af27e1000000000000000006dcf722400000bb000000040000009ee6aa00000000000001a900000000000000d340000002ee153c75600011700010c0385080000000020d00000000000003d2000000000023200004bc00008f0000000767000000047200000000000000000000000000000000000000073c3f4914c0001e4000000000066f21500005780002cf8ba41605f200000000007310000000638522000199c00050a000072800000000000003dc387000000000064e402067904e0000000000e8c00000000000005ae37b12d00000004110c5c000000000000021800005f145c0006fc00000000004e500003a400000000016840007d60000000c527f22c080000000003cf97a00000c7000000000085a000000000000000000000000001a2000000039c1cc00000000000000000000618000000000000000000000000000000fd0fa0496035800000000000000000000000000000000003000000012a0000001760556000390140c0003ae03080000002fd1d880006ea86b000000000000000000000000004450000000000000033400000034708c09ba27e00000000000000000a6c0000000000fac00066b00000008fa00000004f000000000000006ec000000000000000016e20ac6502f90001e240a248144398d86f400022a800113253f2ae000000071b1d600000000000000000000000000000029000000000000000002cd80006ca000047000000040905200140005e40000000ca20003b0800000000000000008fc691000058843000000011ac0008691810f4000000037500000000000430e7c34e000000000000000000012480000000001694ba4000000000000000026f032c682000000029486e7a900000000001503e001cc000000000000031a000000000006a0000de8000000000000000000000000000000000000000000436000000159010400000009e00000003e200007ce00000000000000000000000c601d7000000076622a31900006003bb0001b5ca5a08f0ff98040000003e5800000000000007800000001f916303040003429d38a4e0b50059aa000003000000000007be36715ac68c87a225210c000000094800000085e000000111031900000
  | 15 => 0x2fc00000000016380007e400004d90be245000000000069800004f80000001d919dd15011714985847400003030000000096104800000085200010bc00085000004fd06c0000000000bc4000000036c0000000001df40002f00000a7c0008a10001d7cad40001cd00000000002a997ac00015d153109c28000000000000000000ba0000000000000168000014f000080cf9800000000000004ce00000000000002dd89310d465524d000000000000000000003800000000b0c27500000000002d80001b90426000000000000000000018400006d300019842743ca000000000000000013ec0002d3371a034fdc00000000009c0486000000000053b3790000000000000000000043000000007dc00000000000000000000d440000000000000000000000000000000000000e8000000000000000050c0000000000639295000061c6f500000000007720000cec00028600010f40000b42050f50cc400000002a49c473504886e44b8820000000000000038b0000d4400000000000000000001a680005872f99e840002e441f00002f04e4000214c8a041315d151c66e1573a900000b01681a780000000000a89d5045a173190a1b8d2c000426000000005e0af00000000000000000000425000000000020a049890c0000003c013bc0001fd3091b3c02e0000000000000000000000000012c1860000d7a0000001d680006a428c92d426a00000000000001ef0000000d0222f00000006860000000000db4197005000083a0004170000f44000266227d07600006900000000002ce0efc3e200000000000003c7000000038e09e00000000000000001150e5400000000000000000368ccc0006de00000000000000000000000000000000000000032797d0b9a000000000000000000020089ae000000000000011400000000000000000210ae68a73c680000000000000000e122360001a3c00000000000000005c800000003be000195800000000033a00010920001ca0c8cbd25a300000000003f50000d386700000000734000785094000000073e00006b000047300022183540000440000c7a0000aa8000ddc71136480009584970000000000000037800022c00000003d40001313e70c2800000000000000000121bf9ab80000000000000000000000000000000000011a000000000000000003c40000000000873000000000034000000000003790000000f1e80c00000000005ee1f600000000003e41410000000000000000061900000000000003d5000000000000001303ac29d00011e400056d00018dc4a80000000da0b78000123127800000000019500000000000000bb2000000000000000000000006b62fb000000000007f0e60f2c5680000b9000000055e1c800000007c90679981046000000000018200000000009107
  | 16 => 0x3ff0bbceba0000001c18d58816000000000000004d954800020c00000009887272df1530ce4597000000025673f00000000000002a50000000824000000000000039180000000002790000000000000000000000000000000001d021480000000003ee00000000000000000000000000177455c7d7000000000076a2bb8000b80000000000000000000000002324dc09104cc00000000000000000000000000d72000000033062c057000000014c48b0000000000896306000014000000000000000000000570e5800000000004a200002085fc00057f0001bf400001c2d980000000000000000000000000000000000010015c40006113348000000000000000000000000002340007141fb08f88a470c1eca0a400069300000000000000000000d3200000000008de0000df1a540000000000dd00007f005b0140000000315800000081500021f8ffe5fc000118859200000000002047d400000000005b627e8a8c5825301cb80000000000000000000775000000000038c000134800000000000000004a400000000000001fc8bdceda000000000000047730180000000000000000000000000000000000000000006fa6b700000000005d3000000000074714c9cb4fbe0001c59b510d00c62d60a2000000000016ac0001b1000000000077f0000a8400088c000100c00000019b0000b9635d00011fccbc2a825b000000000000003e8000306309800000000000006a0496000325000000000000000008162060000000cf60000001e5c8ea000000010c0006ad000000000000000000000000003db00000000f200000000003643318018000000000000079c00000000000000000000000af800036d80000000000000000000276000068861243211883741a80002c1988c3e63320000000fe63c800000005ac000000000000000014e00000000000d91738bea00035303b400000000000009d46c628d000000000022b186c0000000f40a3c00002707d80000002fa134000000000043312b800022b4529efc0000002ae8000e0200021a800000000000014f08f40000000bb800000000000000002c700000000000000000000aa200000000000000002978000000000269800027205304d000007821c3d38354000726000000000000000000000005a60000000000000000210400000010f80000000000000000000000000000075e00000000cc7b6814000000000000000000000004ad000004000000000000000000000000000000000000000000012500010f80000003dd0000000000000000000000000000006dc00000020840000001270000000000043908c0000000000000c5419c27300000000591b39b7472a0373f61c8400000000000000000001d680000000000000000000071000000000035a0000000c7c1ce0739aa44240000000
  | 17 => 0x70c00000000000000000000df800016b00000000006a700000000003a90000e4c0001763e680010d8000000000000032d0000a5000000042e8890dd600000000000000000000000ffa00000000003a857d11e005000079340d02ac3680000000000a9c2f200020140000000001fa878c0003210000000555000000000011d2218000000000000000004404a00000001fa0000000000000000000000000000000000000000000000d08d8400000000000000003b89f14000000000000000056000000000000001058c6c0002e80db000000060d0000cf8000000000044d06600000000000006ba0000190000000000000000000000000000000000000000b260ff00000004f8000000000087600000010a00006be11d800000000000000000002070001e8c000000000000030a000025800000050e0000b6800012e00001dc32a1c844f13b400067c11014f400000000000000000d000000000007990001b80000743000220470800000000000005c326680001b410b00000000000000001b7ca120830001718fc469b000136887e36d00000000005ea0d2000000200000000000000000001880ff000e42a09bc13a0000001948cfc2fc3948000000000238981000000000000000000ef000000000049802da1347ee0421550a3000000000000000000002f30b34bfc0bb00000004ca181000000035600023c0000a6a000000022c00000000000000000002c78000e6c00000000000000000c892500005f107a0b0c90a0000ed8f0894c00000000000000000001af07da00000000000003a800000000000002e2000000000000000007f426030b000096e5b522da04800068331c000000000000000010780000000d8c46a50b09ea10904a61e0900af842a2702370000cda3e90000000000000202800000000000000000000001e98000000000000000000000000000000000001bb8b3800063422d1f3cc980000000000000000219800000000029b10e433e00000000000000002b1800000000000005dcb7076f1e007746e4000000197c0002172890000b62000000000000000000003a8e9e0000000000000000000177c0000000000d7c0006140001db824c5d642a800000084e05c8000bfa8a60000000bce0002d510d800079c000000095e47b0000000b12000000000000048d44a8320000000000000000048735880010f27622528000dac00024a88a45b2561000000000000000001980000002880000a507ca000000000014532080000000000001a800004c900000001e00000000c3400025a0000000fbc0003ab93ac2204481ee000000058b4008000ee80001028f54000000000000000000000010100000001f50a440002b806700000002273168000a407bb0000000e820003850000c4c00000000000004671f12184c961e531a81f4848
  | 18 => 0x20003ec00009520000000000d940000c400000000002bd00003b247023500007c600014c103000079000019701f280816b8000000000139000000040700000000000000001a8c000000000000000009200000000000000001a10d0437017b02302ce00000000000000b21681c4c00000004c956400078a3929ccc78241635a94e000000040800000000000001b54000000000000000000029483580000003d8000000000000009d0c2a10f00000006a80000088000ebc000000000112e03b000000000000000007a83c600002a800000021a00000000003de3688b486aa00000006ec0006ed0001f540005ca0001e54a740000c01f6c00000000000000000000f68000f6e000000000076e000000000000067300000000000000ff05b800028500000000000000a700008e80000000894a4c0000000000d66000000000000000000000009be00000000000000000000000f682e300005a80007c70001078000000000000000054600000000000c000000004c4000222000000081c12c8000d3e000000000078a0000000000ef488533e80000004cf000000000000000000010b60000000000580000000000107400015b0000f2409000018681b8524000000000071500000000000001a400011446e613388b09740002ba00008440d700000000000000000000000255000000000076b0000000b2887600000000007dd3ac8000cfe2c500000000000000000000d8a00000000008966ec2960d789f01c310880f8da400000000000006430001434bca0000000000ea20000000000000608022000068e39d12b9ebc0000000000c8020e000000000014200000009a400000044e10b80000000000000000493000000060a0000000000962184346a1906d638d0b800000003151b11e98c4239626a02c40007c62cc80000007323da800000000000000000001a9329897500c0000001fac00000000000000000000000000534000000132c0720000c4911800066e15d82a8b040a71f4103c0001bc2c28e481e60000000000754000416800000000000000006f80000000be0000000000000010a8a3319892000065a3f19c402b255b00000a400006800000000003fb03b00000000000df800000000000019d8000000000000000008120a14511526f31b48000000000384000106a0002a5800000000000001c800000002e9e040000000818000000190000113cd8e000000172400000030f80000008a000000004d8000000000000000000002dc0000000001808000000000000000000000000005fe45d23e000089834a00012a00000000f10000000000000059000000000000000421a537f105428600000000000000000000000000000000000000000000000000000003d41b9400000035f800000046c000000000033100000000000000000064000000000
  | 19 => 0x15337780000005320001d60602000104000000000029a0e8400000000000009860002510000cd400000000000000000cb1c600000000000000f7882a34480002960000000000000202000000076c0004391098f304510002118cae0002b6169c0000e200000000005110000000c1c0002f0868cdc281b0000000000334000000000040105d000000001a2108000d240000001d24000000189800000080f000000028e41707707180007ef00022680003bc0000000c8e48f00000010fa000000000000000000000000000001a98da80001542bf000000010a3f306e0d20000000000000040d0000618d4a00000000000001ae00000000002a242510203d80023110194bec00000015d8054000000000000021e00017b451c0000000f7c0000000001b401ee00044a19e464c6f711b8000000000000000000000000009e400000000020e000056609a18bc00000000012700000003a10000e160000000000000000000000000031d00000010800000000000000000000000054000000000000000000000000b3a0000000000000000000000000068b00000005620003d99d000001663e88000000000000000077000000000000000000000fc4000000000000023e3f822f8bace9a00018c0000000000000000087077000000011040001b880010e03080000000c760002309340f582810a0800000059e0000c9c5aa000000000000081100000000004690000000000000000000000000025d800000000000000002de76916f8000ef82a51a5891c090000000000115400000015080000240000000000000000000000000000000000000000000ab498e8780000000ec671f2fc800000058d276000000080909800000000000000000000000000000000000000009980000003a5800047000000000000000000000810fea00000000000000000000d84000000000000000000000000980000002740b1000000000000009f40003ce936400000002788a00f20000000000000000382000013800000000000000000000000e500000000000b7a000000067400007a278000000021900009f5120000000000000000000007100004470ea800072220f2628c3c0000000001c3901c07b00000c81d00980000ed00002db0599d20e48803000000000073404504200000004520d24a7c7653440000b4804e000000000006a2161d70c14000000000110077b00019580000002cd1db00000000000000000000000000002c0000000000000000173864c0ea0002cb00000000000000000e044b300000000000000000000374187000000000051b192872c000000447800000000000015a4000000000130903a000000000000000041800000000000000ff000001b41f9384b8a028086800109600000000000004db000000036000000000009f229e0ec10449d
  | 20 => 0x2f6060000000000050521880000000000000000a420001701f9c00000012104547fe3d232d9b2c49a000000150c00000000000000002630000000fd000000007e00000000001e500000bc32200000006251cf00002b44be0000e9400000000000000000000000000000694000000000000004b80006060000000000184722000000050e5492c41ce0000000000000000000000013f800000000000004640000000000000000000000000034c00000000002e500000000000000000000000000000000000000000000006ae5481370a2800000000000000000000001ae0a26000000115c0005fa0000d640000000000000000000000000059802e00
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xd6290010005f67190010005f5719001007cff765001011e7e65500100067d655001001ebe6450010006bd6450010005df7350010035dc7350010116de6350010006dd635001010eee6250010006ed6250010074ff768c010014fe768c010014fd768c010034fc768c0101067e658c0100067d658c0100febe648c010006bd648c010016de638c010006dd638c0100f6ee628c010006ed628c010005f6718c010005f5718c010074ff764c0100ee7e654c0100067d654c010005bf744c01003dbc744c0100e6be644c010006bd644c010016de634c010006dd634c0100deee624c010006ed624c01006cff768801000cfe768801000cfd768801002cfc76880100d67e65880100067d65880100cebe6488010006bd64880100c6de6388010006dd638801000eee6288010006ed6288010005f67188010005f5718801006cff76480100057f75480100457c75480100be7e65480100067d65480100b6be6448010006bd64480100aede6348010006dd634801000eee6248010006ed624801002fe820480100a67e65c40100067d65c401009ebe64c4010006bd64c4010096de63c4010006dd63c401008eee62c4010006ed62c401008ef576c40100077665c40100077565c4010007b664c4010007b564c4010007d663c4010007d563c4010007e662c4010007e562c40100867e65840100067d658401007ebe6484010006bd6484010076de6384010006dd638401006eee6284010006ed6284010005f57184010006f6618401002df9768401006ef9768401000cf976840100077a6584010007796584010007ba6484010007b96484010007da6384010007d96384010007ea6284010007e96284010005f97184010006fa6184010007f26184010004ff76440100057f75440100457c75440100667e65440100067d6544010005bf744401003dbc744401005ebe6444010006bd6444010005df7344010035dc7344010056de6344010006dd6344010005ef724401002dec724401004eee6244010006ed6244010005f77644010006f77644010004f77644010007777544010007747544010007766544010007756544010007b77444010007b47444010007b66444010007b56444010007d77344010007d47344010007d66344010007d56344010007e77244010007e47244010007e66244010007e56244010005f77044010006f66044010007f25044010007f15044010005fb7644010006fb7644010004fb76440100077b75440100077875440100077a6544010007796544010007bb7444010007b87444010007ba6444010007b96444010007db7344010007d87344010007da6344010007d96344010007eb7244010007e87244010007ea6244010007e96244010005fb7144010007f37144010006fa6144010007f26144010007f25144010007f15144010
  | 1 => 0x810004ff764c810004fe764c810004fd764c810004fc764c8102367e654c8100067d654c81022ebe644c810006bd644c810016de634c810006dd634c81000eee624c810006ed624c810005f7714c810005f4714c810024fe75984100a4fd7598410024fc759841001cfe749841009cfd749841001cfc7498410014fe7398410094fd7398410014fc739841000cfe729841008cfd729841000cfc72984100a4ff7694410024fd76944100267e65944100067d6594410226be6494410006bd649441021ede6394410006dd639441002dee7294410005ed7294410216ee6294410006ed6294410005fa7094410005f970944100a4ff76544100267e65544100067d655441020ebe6454410006bd6454410206de6354410006dd63544101feee6254410006ed625441009cff769041001cfd76904101f67e65904100067d659041001ebe6490410006bd6490410035de7390410005dd73904101eede6390410006dd63904101e6ee6290410006ed6290410005fa7090410005f9709041009cff76504101de7e65504100067d655041001ebe6450410006bd64504101d6de6350410006dd63504101ceee6250410006ed625041003fb44150410094ff768c410014fd768c4101c67e658c4100067d658c41003dbe748c410005bd748c4101bebe648c410006bd648c410016de638c410006dd638c4101b6ee628c410006ed628c410005fa708c410005f9708c410094ff764c4101ae7e654c4100067d654c4101a6be644c410006bd644c410016de634c410006dd634c41019eee624c410006ed624c410037d4314c41008cff768841000cfd76884100457e75884100057d75884101967e65884100067d658841018ebe6488410006bd6488410186de6388410006dd638841000eee6288410006ed6288410005fa7088410005f9708841008cff764841017e7e65484100067d6548410176be6448410006bd644841016ede6348410006dd634841000eee6248410006ed6248410024fe7598010084fd7598010024fc759801001cfe749801007cfd749801001cfc7498010014fe7398010074fd7398010014fc739801000cfe729801006cfd729801000cfc729801004cfd7198010084ff7694010024fe7694010024fd7694010044fc76940100267e65940100067d6594010166be6494010006bd649401015ede6394010006dd6394010156ee6294010006ed6294010005f67194010005f571940100477b5094010084ff76540100267e65540100067d655401014ebe6454010006bd6454010146de6354010006dd6354010005ef725401002dec725401013eee6254010006ed625401007cff769001001cfe769001001cfd769001003cfc76900101367e65900100067d659001001ebe6490010006bd649001012ede6390010006dd6390010126ee6290010006e
  | 2 => 0x14fe73d8810006de73d8810014de73d8810004fd73d8810006dd73d8810004dd73d8810014fc73d881002cfd72d881008cfe71d8810006f671d881006cfe70d8810006fa70d8810004ed7698810006ef6598810006ee65988100076e65988100066e6598810006ed65988100076d65988100066d6598810006ec6598810006ef6498810006ee6498810007ae6498810006ae6498810006ed6498810007ad6498810006ad6498810006ec6498810006ef6398810006ee6398810007ce6398810006ce6398810006ed6398810007cd6398810006cd6398810006ec639881000cff76588100067e65588100067d6558810006be6458810006bd6458810006de6358810006dd635881002eec6258810004ff7558810024fe7558810024fc7558810004ff745881001cfe745881001cfc7458810004ff7358810014fe7358810014fc7358810006ef7258810006ef525881002eee525881002eec5258810006ef425881002eee425881002eec4258810006ef325881002eee325881002eec325881000cff715881000cfd715881002cfc715881002eec215881000cff705881000cfd705881002cfc705881002eec205881002def765881002eef765881000cef7658810006ef6558810006ee65588100076e65588100066e6558810006ed65588100076d65588100066d6558810006ec6558810006ef6458810006ee6458810007ae6458810006ae6458810006ed6458810007ad6458810006ad6458810006ec6458810006ef6358810006ee6358810007ce6358810006ce6358810006ed6358810007cd6358810006cd6358810006ec6358810006ef7558810006ee7558810006ed7558810006ec7558810006ef7458810006ee7458810006ed7458810006ec7458810006ef5458810006ee5458810006ed5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef5358810006ee5358810006ed5358810006ec5358810006ef4358810006ee4358810006ed4358810006ec435881002eef7158810006ee7158810006ec7158810006ef5158810006ec5158810006ef4158810006ec4158810006ef3158810006ec315881002eef7058810006ee7058810006ec7058810006ef5058810006ec5058810006ef4058810006ec4058810006ef3058810006ec3058810006ec1058810004ff7654810004fe7654810004fd7654810004fc76548100267e65548100067d6554810256be6454810006bd645481024ede6354810006dd635481000eee6254810006ed625481002f6c5254810005fb7054810005f87054810004ff7650810004fe7650810004fd7650810004fc76508102467e65508100067d655081001ebe6450810006bd645081023ede6350810006dd635081000eee6250810006ed6250810005f77150810005f4715
  | 3 => 0x671d8c10074fe70d8c10006fa70d8c10004dd7698c10006df6598c10006de6598c100075e6598c100065e6598c10006dd6598c100075d6598c100065d6598c10006dc6598c10006df6498c10006de6498c100079e6498c100069e6498c10006dd6498c100079d6498c100069d6498c10006dc6498c10006de6298c10006dc6298c10014ff7658c100067e6558c100067d6558c10006be6458c10006bd6458c10036dc6358c10004ff7558c10024fe7558c10024fc7558c10004ff7458c1001cfe7458c1001cfc7458c10006df7358c10006df5358c10036de5358c10036dc5358c10006df4358c10036de4358c10036dc4358c10004ff7258c1000cfe7258c1000cfc7258c10036df3258c10006de3258c10036dc3258c10014ff7158c10014fd7158c10034fc7158c10036dc3158c10014ff7058c10014fd7058c10034fc7058c10036dc3058c10035df7658c10036df7658c10014df7658c10006df6558c10006de6558c100075e6558c100065e6558c10006dd6558c100075d6558c100065d6558c10006dc6558c10006df6458c10006de6458c100079e6458c100069e6458c10006dd6458c100079d6458c100069d6458c10006dc6458c10006de6258c10006dc6258c10006df7558c10006de7558c10006dd7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c10006de5258c10006dc5258c10006df4258c10006de4258c10006dc4258c10036df7158c10006de7158c10006dc7158c10006df5158c10006dc5158c10006df4158c10006dc4158c10006df2158c10006dc2158c10036df7058c10006de7058c10006dc7058c10006df5058c10006dc5058c10006df4058c10006dc4058c10006df2058c10006dc2058c10006dc1058c10004ff7654c10004fe7654c10004fd7654c10004fc7654c100267e6554c100067d6554c10276be6454c10006bd6454c10016de6354c10006dd6354c1026eee6254c10005f77154c10005f47154c10004ff7650c10004fe7650c10004fd7650c10004fc7650c102667e6550c100067d6550c1001ebe6450c10006bd6450c10016de6350c10006dd6350c100379c4350c1025eee6250c10005fb7050c10005f87050c100457e75d88100057d75d88100067e65d88100067d65d881003dbe74d8810005bd74d8810006be64d8810006bd64d8810035de73d8810005dd73d8810006de63d8810006dd63d881002eee62d8810024fe75d88100067e75d88100247e75d8810004fd75d88100067d75d88100047d75d8810024fc75d881001cfe74d8810006be74d881001cbe74d8810004fd74d8810006bd74d8810004bd74d881001cfc74d8810
  | 4 => 0x90100067e75d90100247e75d9010004fd75d90100067d75d90100047d75d9010024fc75d901003cfd74d9010014fe73d9010006de73d9010014de73d9010004fd73d9010006dd73d9010004dd73d9010014fc73d901000cfe72d9010006ee72d901000cee72d9010004fd72d9010006ed72d9010004ed72d901000cfc72d901009cfe71d9010006f671d901007cfe70d9010006fa70d9010004bd7699010006bf6599010006be65990100073e65990100063e6599010006bd65990100073d65990100063d6599010006bc6599010006be6399010006bc6399010006be6299010006bc629901001cff76590100067e65590100067d655901003ebc6459010004ff7559010024fe7559010024fc7559010006bf7459010006bf545901003ebe545901003ebc5459010004ff7359010014fe7359010014fc735901003ebf4359010006be435901003ebc4359010004ff725901000cfe725901000cfc725901003ebf4259010006be425901003ebc425901001cff715901001cfd715901003cfc715901003ebc415901001cff705901001cfd705901003cfc705901003ebc405901003dbf765901003ebf765901001cbf7659010006bf6559010006be65590100073e65590100063e6559010006bd65590100073d65590100063d6559010006bc6559010006be6359010006bc6359010006be6259010006bc6259010006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf5359010006be5359010006bc5359010006bf7259010006be7259010006bd7259010006bc7259010006bf5259010006be5259010006bc5259010006bf3259010006be3259010006bc325901003ebf7159010006be7159010006bc7159010006bf5159010006bc5159010006bf3159010006bc3159010006bf2159010006bc215901003ebf7059010006be7059010006bc7059010006bf5059010006bc5059010006bf3059010006bc3059010006bf2059010006bc2059010006bc1059010004ff7655010004fe7655010004fd7655010004fc76550100267e65550100067d655501001ebe6455010006bd6455010286de635501027eee6255010005f77155010005f471550100457e75d8c100057d75d8c100067e65d8c100067d65d8c1003dbe74d8c10005bd74d8c10006be64d8c10006bd64d8c10036de63d8c1002dee72d8c10005ed72d8c10024fe75d8c100067e75d8c100247e75d8c10004fd75d8c100067d75d8c100047d75d8c10024fc75d8c1001cfe74d8c10006be74d8c1001cbe74d8c10004fd74d8c10006bd74d8c10004bd74d8c1001cfc74d8c10034fd73d8c1000cfe72d8c10006ee72d8c1000cee72d8c10004fd72d8c10006ed72d8c10004ed72d8c1000cfc72d8c10094fe71d8c10006f
  | 5 => 0x67f65481100be7c6548110006bf64481100b6bc6448110006df63481100aedc6348110006ef624811000eec6248110005f77148110005f471481100067f65c41100a67c65c4110006bf64c411009ebc64c4110006df63c4110096dc63c4110006ef62c411008eec62c41100077b65c41100077865c4110007bb64c4110007b864c4110007db63c4110007d863c4110007eb62c4110007e862c41100067f65841100867c6584110006bf648411007ebc6484110006df6384110076dc6384110006ef628411006eec6284110007776584110007746584110007b76484110007b46484110007d76384110007d46384110007e76284110007e46284110007f360841100467e65d941003dbe74d9410005bd74d9410035de73d9410005dd73d941002dee72d9410005ed72d9410044fd75d941001cfe74d9410006be74d941001cbe74d9410004fd74d9410006bd74d9410004bd74d941001cfc74d9410014fe73d9410006de73d9410014de73d9410004fd73d9410006dd73d9410004dd73d9410014fc73d941000cfe72d9410006ee72d941000cee72d9410004fd72d9410006ed72d9410004ed72d941000cfc72d94100a4fe71d9410006f671d9410084fe70d9410006fa70d94100047d76994100067e64994100067c64994100067e63994100067c63994100067e62994100067c6299410024ff76594100467c65594100067f7559410004ff745941001cfe745941001cfc74594100467f54594100067e54594100467c5459410004ff7359410014fe7359410014fc73594100467f53594100067e53594100467c5359410004ff725941000cfe725941000cfc72594100467f52594100067e52594100467c5259410024ff7159410024fd7159410044fc71594100467c5159410024ff7059410024fd7059410044fc70594100467c50594100457f76594100467f76594100247f76594100067e64594100067c64594100067e63594100067c63594100067e62594100067c62594100067f74594100067e74594100067d74594100067c74594100067f73594100067e73594100067d73594100067c73594100067f43594100067e43594100067c43594100067f72594100067e72594100067d72594100067c72594100067f42594100067e42594100067c42594100067f32594100067e32594100067c32594100467f71594100067e71594100067c71594100067f41594100067c41594100067f31594100067c31594100067f21594100067c21594100467f70594100067e70594100067c70594100067f40594100067c40594100067f30594100067c30594100067f20594100067c20594100067c10594100457e75d90100057d75d90100067e65d90100067d65d901003ebe64d9010035de73d9010005dd73d901002dee72d9010005ed72d9010024fe75d
  | 6 => 0xf6494510226bc6494510006df639451021edc639451004dee7294510005ed7294510006ef6294510216ec6294510024fc76545100067f65545100267c6554510006bf645451020ebc6454510006df6354510206dc6354510006ef62545101feec6254510005fb7054510005f8705451007cfe76905100067f65905101f67c6590510006bf649051001ebc6490510055de7390510005dd7390510006df63905101eedc6390510006ef62905101e6ec629051001cfc76505100067f65505101de7c6550510006bf645051001ebc6450510006df63505101d6dc6350510006ef62505101ceec6250510005fb7050510005f87050510074fe768c5100067f658c5101c67c658c51005dbe748c510005bd748c510006bf648c5101bebc648c510006df638c510016dc638c510006ef628c5101b6ec628c510014fc764c5100067f654c5101ae7c654c510006bf644c5101a6bc644c510006df634c510016dc634c510006ef624c51019eec624c510005fb704c510005f8704c51006cfe76885100657e75885100057d75885100067f65885101967c6588510006bf648851018ebc6488510006df6388510186dc6388510006ef628851000eec628851000cfc76485100067f654851017e7c6548510006bf6448510176bc6448510006df634851016edc6348510006ef624851000eec6248510005fb7048510005f870485100a4fe76941100067f65941100267c6594110006bf6494110166bc6494110006df639411015edc6394110006ef6294110156ec6294110024ff7654110064fd7654110024fc76541100067f65541100267c6554110006bf645411014ebc6454110006df6354110146dc6354110005ef725411004dec7254110006ef625411013eec6254110005f77154110005f4715411009cfe76901100067f65901101367c6590110006bf649011001ebc6490110006df639011012edc6390110006ef6290110126ec629011001cff765011005cfd765011001cfc76501100067f655011011e7c6550110006bf645011001ebc6450110005df7350110055dc7350110006df6350110116dc6350110006ef625011010eec6250110005f77150110005f47150110094fe768c1100067f658c1101067c658c110006bf648c1100febc648c110006df638c110016dc638c110006ef628c1100f6ec628c110014ff764c110054fd764c110014fc764c1100067f654c1100ee7c654c110005bf744c11005dbc744c110006bf644c1100e6bc644c110006df634c110016dc634c110006ef624c1100deec624c110005f7714c110005f4714c11008cfe76881100067f65881100d67c6588110006bf64881100cebc6488110006df63881100c6dc6388110006ef628811000eec628811000cff764811004cfd764811000cfc76481100057f75481100657c7548110
  | 7 => 0x8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d8910006ef75d8910006ee75d8910006ed75d8910006ec75d8910006ef74d8910006ee74d8910006ed74d8910006ec74d8910006ef54d8910006ee54d8910006ed54d8910006ec54d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d8910006ee53d8910006ed53d8910006ec53d8910006ef43d8910006ee43d8910006ed43d8910006ec43d8910006ef71d891004eee71d8910006ed71d8910006ef51d8910006ec51d8910006ef41d8910006ec41d8910006ef31d8910006ec31d8910006ef70d891004eee70d8910006ed70d8910006ef50d8910006ec50d8910006ef40d8910006ec40d8910006ef30d8910006ec30d89100057f75589100657c75589100067f65589100067c6558910005bf745891005dbc7458910006bf6458910006bc6458910005df7358910055dc7358910006df6358910006dc635891004eec6258910004ff75589100067f75589100047f7558910024fe7558910024fc75589100067c75589100247c7558910004ff7458910006bf7458910004bf745891001cfe745891001cfc7458910006bc745891001cbc7458910004ff7358910006df7358910004df7358910014fe7358910014fc7358910006dc7358910014dc735891004cff7258910006ef725891006cff7158910006f7715891008cff7058910006fb7058910005ee761891004eee7618910004ee7618910006ef65189100076f65189100066f6518910006ee6518910006ed6518910006ec65189100076c65189100066c6518910006ef6418910007af6418910006af6418910006ee6418910006ed6418910006ec6418910007ac6418910006ac6418910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc6318910004ff7654910004fe7654910004fd7654910004fc76549100067f65549100267c6554910006bf6454910256bc6454910006df635491024edc6354910006ef625491000eec625491004f6c5254910004ff7650910004fe7650910004fd7650910004fc76509100067f65509102467c6550910006bf645091001ebc6450910006df635091023edc6350910006ef625091000eec6250910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c9102367c654c910006bf644c91022ebc644c910006df634c910016dc634c910006ef624c91000eec624c910084fe76945100067f65945100267c6594510006b
  | 8 => 0x6df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d10006de62d8d10006dc62d8d10006df75d8d10006de75d8d10006dd75d8d10006dc75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df52d8d10006de52d8d10006dc52d8d10006df42d8d10006de42d8d10006dc42d8d10006df71d8d10056de71d8d10006dd71d8d10006df51d8d10006dc51d8d10006df41d8d10006dc41d8d10006df21d8d10006dc21d8d10006df70d8d10056de70d8d10006dd70d8d10006df50d8d10006dc50d8d10006df40d8d10006dc40d8d10006df20d8d10006dc20d8d100057f7558d100657c7558d100067f6558d100067c6558d10005bf7458d1005dbc7458d10006bf6458d10006bc6458d10056dc6358d10005ef7258d1004dec7258d10004ff7558d100067f7558d100047f7558d10024fe7558d10024fc7558d100067c7558d100247c7558d10004ff7458d10006bf7458d10004bf7458d1001cfe7458d1001cfc7458d10006bc7458d1001cbc7458d10054ff7358d10006df7358d10004ff7258d10006ef7258d10004ef7258d1000cfe7258d1000cfc7258d10006ec7258d1000cec7258d10074ff7158d10006f77158d10094ff7058d10006fb7058d10005de7618d10056de7618d10004de7618d10006df6518d100075f6518d100065f6518d10006de6518d10006dd6518d10006dc6518d100075c6518d100065c6518d10006df6418d100079f6418d100069f6418d10006de6418d10006dd6418d10006dc6418d100079c6418d100069c6418d10006de6218d10006dc6218d10004ff7654d10004fe7654d10004fd7654d10004fc7654d100067f6554d100267c6554d10006bf6454d10276bc6454d10006df6354d10016dc6354d1026eec6254d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100067f6550d102667c6550d10006bf6450d1001ebc6450d10006df6350d10016dc6350d100579c4350d1025eec6250d1000cfe76d89100067f65d89100067c65d8910006bf64d8910006bc64d8910006df63d8910006dc63d891004eee62d8910024fe75d8910004fd75d8910024fc75d891001cfe74d8910004fd74d891001cfc74d8910014fe73d8910004fd73d8910014fc73d8910006ef52d891004eee52d891004eec52d8910006ef42d891004eee42d891004eec42d8910006ef32d891004eee32d891004eec32d891000cfe71d891004cfd71d891000cfc71d891004eef21d891000cfe70d891004cfd70d891000cfc70d891004eef20d891004dee76d891000cee76d8910006ef65d89100076f65d89100066f65d
  | 9 => 0xc43d911000cfe72d9110004fd72d911000cfc72d911005ebf42d9110006be42d911005ebc42d911001cfe71d911005cfd71d911001cfc71d911005ebf41d911001cfe70d911005cfd70d911001cfc70d911005ebf40d911005dbe76d911001cbe76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006be63d9110006bc63d9110006be62d9110006bc62d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006be53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006be52d9110006bc52d9110006bf32d9110006be32d9110006bc32d9110006bf71d911005ebe71d9110006bd71d9110006bf51d9110006bc51d9110006bf31d9110006bc31d9110006bf21d9110006bc21d9110006bf70d911005ebe70d9110006bd70d9110006bf50d9110006bc50d9110006bf30d9110006bc30d9110006bf20d9110006bc20d91100057f75591100657c75591100067f65591100067c655911005ebc6459110005df7359110055dc7359110005ef725911004dec7259110004ff75591100067f75591100047f7559110024fe7559110024fc75591100067c75591100247c755911005cff7459110006bf7459110004ff7359110006df7359110004df7359110014fe7359110014fc7359110006dc7359110014dc7359110004ff7259110006ef7259110004ef725911000cfe725911000cfc7259110006ec725911000cec725911007cff7159110006f7715911009cff7059110006fb7059110005be761911005ebe7619110004be7619110006bf65191100073f65191100063f6519110006be6519110006bd6519110006bc65191100073c65191100063c6519110006be6319110006bc6319110006be6219110006bc6219110004ff7655110004fe7655110004fd7655110004fc76551100067f65551100267c6555110006bf645511001ebc6455110286dc635511027eec6255110014fe76d8d100067f65d8d100067c65d8d10006bf64d8d10006bc64d8d10056de63d8d10024fe75d8d10004fd75d8d10024fc75d8d1001cfe74d8d10004fd74d8d1001cfc74d8d10006df53d8d10056de53d8d10056dc53d8d10006df43d8d10056de43d8d10056dc43d8d1000cfe72d8d10004fd72d8d1000cfc72d8d10056df32d8d10006de32d8d10056dc32d8d10014fe71d8d10054fd71d8d10014fc71d8d10056df31d8d10014fe70d8d10054fd70d8d10014fc70d8d10056df30d8d10055de76d8d10014de76d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10
  | 10 => 0x42100267c6554210005ef725421006dec725421001cfd769021001ebe6490210006bd6490210005f67190210005f5719021003cff7650210006bf645021001ebc6450210005df7350210075dc7350210014fd768c210016de638c210006dd638c210005f6718c210005f5718c210034ff764c210005bf744c21007dbc744c210006df634c210016dc634c21000cfd768821000eee6288210006ed6288210005f67188210005f5718821002cff76482100057f75482100857c7548210006ef624821000eec6248210005f576c4210006f576c4210005f976c4210006f976c4210024fe76d95100667e65d951001cfe74d9510004fd74d951001cfc74d95100667f54d95100067e54d95100667c54d9510014fe73d9510004fd73d9510014fc73d95100667f53d95100067e53d95100667c53d951000cfe72d9510004fd72d951000cfc72d95100667f52d95100067e52d95100667c52d9510024fe71d9510064fd71d9510024fc71d95100667f51d9510024fe70d9510064fd70d9510024fc70d95100667f50d95100657e76d95100247e76d95100067e64d95100067c64d95100067e63d95100067c63d95100067e62d95100067c62d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067e42d95100067c42d95100067f32d95100067e32d95100067c32d95100067f71d95100667e71d95100067d71d95100067f41d95100067c41d95100067f31d95100067c31d95100067f21d95100067c21d95100067f70d95100667e70d95100067d70d95100067f40d95100067c40d95100067f30d95100067c30d95100067f20d95100067c20d95100667c6559510005bf745951005dbc7459510005df7359510055dc7359510005ef725951004dec7259510064ff75595100067f7559510004ff7459510006bf7459510004bf745951001cfe745951001cfc7459510006bc745951001cbc7459510004ff7359510006df7359510004df7359510014fe7359510014fc7359510006dc7359510014dc7359510004ff7259510006ef7259510004ef725951000cfe725951000cfc7259510006ec725951000cec7259510084ff7159510006f771595100a4ff7059510006fb70595100057e76195100667e76195100047e76195100067e64195100067c64195100067e63195100067c63195100067e62195100067c621951001cfe76d91100067f65d91100067c65d911005ebe64d9110024fe75d9110004fd75d9110024fc75d9110006bf54d911005ebe54d911005ebc54d9110014fe73d9110004fd73d9110014fc73d911005ebf43d9110006be43d911005eb
  | 11 => 0x6dc7359210014dc735921007ebf4359210004ff725921000cfe725921000cfc725921007ebf415921007ebc4059210004ff7655210004fe7655210004fd7655210004fc7655210005f77155210005f47155210076de63d8e10024fe75d8e10004fd75d8e10024fc75d8e1001cfe74d8e10004fd74d8e1001cfc74d8e10006df43d8e10076dc43d8e1000cfe72d8e10004fd72d8e1000cfc72d8e10006f571d8e10076dc31d8e10006fa70d8e10076df30d8e10005bf7458e1007dbc7458e10076dc6358e10004ff7558e10024fe7558e10024fc7558e10004ff7458e10006bf7458e10004bf7458e1001cfe7458e1001cfc7458e10006bc7458e1001cbc7458e10006df7358e10076de4358e10004ff7258e1000cfe7258e1000cfc7258e10076df3158e10076dc3058e10004ff7654e10004fe7654e10004fd7654e10004fc7654e10005f77154e10005f47154e10004ff7650e10004fe7650e10004fd7650e10004fc7650e1001ebe6450e10006bd6450e10016de6350e10006dd6350e100779c4350e1006eee62d8a10024fe75d8a10004fd75d8a10024fc75d8a1001cfe74d8a10004fd74d8a1001cfc74d8a10014fe73d8a10004fd73d8a10014fc73d8a10006ef52d8a1006eec52d8a10006f571d8a1006eec21d8a10006fa70d8a1006eef20d8a100057f7558a100857c7558a1006eec6258a10004ff7558a100067f7558a100047f7558a10024fe7558a10024fc7558a100067c7558a100247c7558a10004ff7458a1001cfe7458a1001cfc7458a10004ff7358a10014fe7358a10014fc7358a10006ef7258a1006eee5258a1006eef2158a1006eec2058a10004ff7654a10004fe7654a10004fd7654a10004fc7654a100267e6554a100067d6554a1000eee6254a10006ed6254a1006f6c5254a10004ff7650a10004fe7650a10004fd7650a10004fc7650a10005f77150a10005f47150a10004ff764ca10004fe764ca10004fd764ca10004fc764ca10005f7714ca10005f4714ca10064fd76946100067f65946100267c659461006dee7294610005ed7294610024ff76546100267e65546100067d6554610005fb7054610005f8705461005cfd7690610006bf649061001ebc6490610075de7390610005dd739061001cff765061001ebe6450610006bd645061007fb44150610005fb7050610005f87050610054fd768c61007dbe748c610005bd748c610006df638c610016dc638c610014ff764c610016de634c610006dd634c610077d4314c610005fb704c610005f8704c61004cfd76886100857e75886100057d7588610006ef628861000eec628861000cff764861000eee6248610006ed6248610005fb7048610005f87048610024fd76942100267e65942100067d6594210005f67194210005f57194210044ff76542100067f655
  | 12 => 0xc7358b10006ef7258b10006ef5258b1008eec5258b1008eec2158b1008eef2058b10004ff7654b10004fe7654b10004fd7654b10004fc7654b100067f6554b100267c6554b10006ef6254b1000eec6254b1008f6c5254b10005fb7054b10005f87054b10004ff7650b10004fe7650b10004fd7650b10004fc7650b10004ff764cb10004fe764cb10004fd764cb10004fc764cb10024fd76947100267e65947100067d659471008dee7294710005ed7294710005fa7094710005f97094710044ff76547100067f65547100267c655471001cfd769071001ebe6490710006bd6490710095de7390710005dd7390710005fa7090710005f9709071003cff7650710006bf645071001ebc6450710014fd768c71009dbe748c710005bd748c710016de638c710006dd638c710005fa708c710005f9708c710034ff764c710006df634c710016dc634c71000cfd76887100a57e75887100057d758871000eee6288710006ed6288710005fa7088710005f9708871002cff7648710006ef624871000eec6248710064fd76943100067f65943100267c65943100a77b5094310024ff76543100267e65543100067d6554310005ef725431008dec7254310005f77154310005f4715431005cfd7690310006bf649031001ebc649031001cff765031001ebe6450310006bd6450310005df7350310095dc7350310005f77150310005f47150310054fd768c310006df638c310016dc638c310014ff764c310005bf744c31009dbc744c310016de634c310006dd634c310005f7714c310005f4714c31004cfd7688310006ef628831000eec628831000cff76483100057f75483100a57c754831000eee6248310006ed6248310005f77148310005f4714831008fe820483100867e65d961001cfe74d9610004fd74d961001cfc74d9610014fe73d9610004fd73d9610014fc73d961000cfe72d9610004fd72d961000cfc72d96100067e52d96100867c52d9610006f571d96100867c51d9610006fa70d96100867f50d96100867c6559610005ef725961006dec72596100067f7559610004ff745961001cfe745961001cfc7459610004ff7359610014fe7359610014fc7359610004ff7259610006ef7259610004ef725961000cfe725961000cfc7259610006ec725961000cec72596100867f52596100867f51596100867c505961007ebe64d9210024fe75d9210004fd75d9210024fc75d9210014fe73d9210004fd73d9210014fc73d9210006be43d921007ebc43d921000cfe72d9210004fd72d921000cfc72d9210006f571d921007ebc41d9210006fa70d921007ebf40d921007ebc6459210005df7359210075dc7359210004ff7559210024fe7559210024fc7559210006bf7459210004ff7359210006df7359210004df7359210014fe7359210014fc7359210
  | 13 => 0xc120005ef7588120005ed75881200076f65881200d6ee65881200d6ec65881200076c65881200d66c6588120005ed7188120006ec618812000dee708812000fea708812000eef608812000feb60881200a67e65d971008dee72d9710005ed72d971001cfe74d9710004fd74d971001cfc74d9710014fe73d9710004fd73d9710014fc73d971000cfe72d9710006ee72d971000cee72d9710004fd72d9710006ed72d9710004ed72d971000cfc72d97100a67f52d9710006f671d97100a67f51d9710006f970d97100a67c50d97100a67c65597100067f7559710004ff745971001cfe745971001cfc7459710004ff7359710014fe7359710014fc7359710004ff725971000cfe725971000cfc72597100067e52597100a67c52597100a67c51597100a67f505971009ebe64d9310095de73d9310005dd73d9310024fe75d9310004fd75d9310024fc75d9310014fe73d9310006de73d9310014de73d9310004fd73d9310006dd73d9310004dd73d9310014fc73d931009ebf43d931000cfe72d9310004fd72d931000cfc72d9310006f671d931009ebf41d9310006f970d931009ebc40d931009ebc6459310004ff7559310024fe7559310024fc7559310006bf7459310004ff7359310014fe7359310014fc7359310006be435931009ebc4359310004ff725931000cfe725931000cfc725931009ebc415931009ebf4059310004ff7655310004fe7655310004fd7655310004fc765531009dbe74d8f10005bd74d8f10096de63d8f10024fe75d8f10004fd75d8f10024fc75d8f1001cfe74d8f10006be74d8f1001cbe74d8f10004fd74d8f10006bd74d8f10004bd74d8f1001cfc74d8f10096de43d8f1000cfe72d8f10004fd72d8f1000cfc72d8f10006f671d8f10096df31d8f10006f970d8f10096dc30d8f10096dc6358f10004ff7558f10024fe7558f10024fc7558f10004ff7458f1001cfe7458f1001cfc7458f10006df7358f10006df4358f10096dc4358f10004ff7258f1000cfe7258f1000cfc7258f10096dc3158f10096df3058f10004ff7654f10004fe7654f10004fd7654f10004fc7654f10004ff7650f10004fe7650f10004fd7650f10004fc7650f10006bf6450f1001ebc6450f10006df6350f10016dc6350f100979c4350f10005fb7050f10005f87050f100a57e75d8b100057d75d8b1008eee62d8b10024fe75d8b100067e75d8b100247e75d8b10004fd75d8b100067d75d8b100047d75d8b10024fc75d8b1001cfe74d8b10004fd74d8b1001cfc74d8b10014fe73d8b10004fd73d8b10014fc73d8b1008eee52d8b10006f671d8b1008eef21d8b10006f970d8b1008eec20d8b1008eec6258b10004ff7558b10024fe7558b10024fc7558b10004ff7458b1001cfe7458b1001cfc7458b10004ff7358b10014fe7358b10014f
  | 14 => 0x5ec7054920007e8705492000eef605492000feb60549200bf6f50549200067f65d85200067c65d8520024fe75d8520004fd75d8520024fc75d852001cfe74d8520004fd74d852001cfc74d8520014fe73d8520004fd73d8520014fc73d8520006f741d8520006f441d8520006f731d8520006f431d852006ef621d852006ef521d85200bd7e75985200057d75985200067f65985200067c6598520006f7619852004df970985200057f75585200bd7c75585200067f65585200067c6558520005bf74585200b5bc7458520005df73585200addc735852008dfb70585200067f65185200067c6518520006f56118520024fe7518520004fd7518520024fc751852001cfe7418520004fd741852001cfc7418520014fe7318520004fd7318520014fc731852002eee5218520006ed5218520006f74118520006f44118520006f73118520006f4311852002eef211852002ef6211852002ef5211852002eec2018520004fe7694520004fd7694520004fc76945200067f65945200267c659452000dee7294520005ed72945200076d5294520004ff7654520004fe7654520004fc76545200067f65545200267c655452000dee72545201ff6e5254520004fe7690520004fd7690520004fc76905200067f65905201f67c6590520006bf649052001ebc64905200adde7390520005dd739052000dee7290520005ed7290520004ff7650520004fe7650520004fc76505200067f65505201de7c6550520004fe768c520004fd768c520004fc768c5200067f658c5201c67c658c5200b5be748c520005bd748c520006df638c520016dc638c52000dee728c520005ed728c520004ff764c520004fe764c520004fc764c5200067f654c5201ae7c654c520005ef7548520005ed75485200076f654852017eee654852017eec65485200076c654852017e6c654852000def714852000fe77148520007e76148520006ec6148520007e46148520007eb7048520005ec7048520007e87048520005e8704852000eef604852000feb604852029cfe76941201567f65941200267c659412000dec72941201576e52941200bf7b5094120157e82094120024ff765412000cfe765412013cfd765412000cfc76541200067f65541200267c6554120005ef725412000dec72541200076d525412013fe82054120294fe76901200067f65901201367c659012001cff765012000cfe765012010cfd765012000cfc76501200067f655012011e7c6550120006bf645012001ebc6450120005df73501200addc7350120005ef725012000dec725012028cfe768c1200067f658c1201067c658c120014ff764c12000cfe764c1200dcfd764c12000cfc764c1200067f654c1200ee7c654c120005bf744c1200b5bc744c120006df634c120016dc634c120005ef724c12000dec724
  | 15 => 0xf7159520004fc71595202b4ff7059520006fb70595201557e76195200be7e76195201547e76195200067e64195200067c64195200067e63195200067c631952029f6e72195200bf6d721952029e7f621952029f6f211952029e7f601952029f7b201952029f6c201952029f78201952001cfe76d91200067f65d91200067c65d91200b6be64d9120024fe75d9120004fd75d9120024fc75d9120014fe73d9120004fd73d9120014fc73d9120006be43d91200b6bc43d9120124ff72d912000cfe72d9120124fd72d912000cfc72d9120126bf42d9120126bd42d9120004fe71d9120004fd71d91200b6bc41d912000cfd70d91200b6bf40d91200057f75591200bd7c75591200067f65591200067c65591200b6bc6459120005df73591200addc7359120005f77159120005f471591202adfb7059120004ff75591200067f75591200047f7559120024fe7559120024fc75591200067c75591200247c7559120124ff7459120006bf7459120004ff7359120006df7359120004df7359120014fe7359120014fc7359120006dc7359120014dc735912010cff7259120006ef7259120004ff7159120006f77159120004f77159120004fc7159120006f47159120004f471591202acff7059120006fb7059120004ff7655120004fe7655120004fd7655120004fc76551200067f65551200267c6555120014fe76d8d200067f65d8d200067c65d8d200aede63d8d20024fe75d8d20004fd75d8d20024fc75d8d2001cfe74d8d20004fd74d8d2001cfc74d8d20006df43d8d200aedc43d8d200f4ff72d8d2000cfe72d8d200f4fd72d8d2000cfc72d8d200f6df32d8d200f6dd32d8d20004fe71d8d20004fd71d8d200aedc31d8d2000cfd70d8d200aedf30d8d200057f7558d200bd7c7558d200067f6558d200067c6558d20005bf7458d200b5bc7458d200aedc6358d20005f77158d20005f47158d202a5fb7058d20004ff7558d200067f7558d200047f7558d20024fe7558d20024fc7558d200067c7558d200247c7558d20004ff7458d20006bf7458d20004bf7458d2001cfe7458d2001cfc7458d20006bc7458d2001cbc7458d200f4ff7358d20006df7358d200dcff7258d20006ef7258d20004ff7158d20006f77158d20004f77158d20004fc7158d20006f47158d20004f47158d202a4ff7058d20006fb7058d20004ff7654d20004fe7654d20004fd7654d20004fc7654d200067f6554d200267c6554d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200067f6550d202667c6550d200af9c4350d20005ef7250d2000dec7250d200bdec7654920026ec7654920024ec765492000def755492000f6f75549200076f6554920026ee6554920026ec65549200bf6c65549200266c6554920005ef71549200bf6c5154920007eb7054920
  | 16 => 0x620005dd7390620004ff7650620004fd7650620004fc765062001ebe6450620006bd6450620005ef725062000dec7250620004ff768c620004fe768c620004fd768c6200cdbe748c620005bd748c620004ff764c620004fd764c620004fc764c620016de634c620006dd634c620005ef724c62000dec724c6200d5ee75886200076e75886200d56e75886200076d75886200d5ec7588620006ef6588620006ed658862000dee718862000fe67188620007e66188620006ed6188620007e56188620007ea7088620005ed7088620007e9708862000eee608862000fea608862000cff7694220024fe769422000cfd76942200267e65942200067d659422000dee7294220005ed72942201576c52942200d77b5094220157eb20942202b4ff76542200067f65542200267c65542200d5ef725422000dec72542200d76f525422013feb205422000cff769022001cfe769022000cfd769022001ebe6490220006bd649022000dee7290220005ed72902202acff7650220005df73502200c5dc735022000cff768c220014fe768c22000cfd768c220016de638c220006dd638c22000dee728c220005ed728c2202a4ff764c220005bf744c2200cdbc744c220024fe76d95200be7e65d952001cfe74d9520004fd74d952001cfc74d95200be7f54d95200067e54d95200be7c54d9520014fe73d9520004fd73d9520014fc73d95200be7f53d95200067e53d95200be7c53d9520154ff72d952000cfe72d9520154fd72d952000cfc72d95201567f52d95201567d52d9520004fe71d9520004fd71d95200be7f51d95200be7c51d952000cfd70d95200be7f50d952029d7e76d95200247e76d95200067e64d95200067c64d95200067e63d95200067c63d95200076f72d95201576c72d95201576f21d95201577b20d95201576c20d95201577820d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200067e73d95200067d73d95200067c73d95200067f43d95200067e43d95200067c43d95201567f72d95201567e72d95201567d72d95201567c72d95201567f42d95201567e42d95201567d42d95201567c42d95201567f32d95201567e32d95201567d32d95201567c32d95200067f71d95200067e71d95200067d71d95200067c71d95200067f41d95200067c41d95200067f31d95200067c31d95201567f21d95201567e21d95201567d21d95201567c21d95201567f70d95200be7e70d95201567d70d95200067f40d95200067c40d95200067f30d95200067c30d95201567f20d95201567e20d95201567c20d95200be7c65595202b5fb7059520154ff75595200067f7559520004ff745952001cfe745952001cfc7459520004ff7359520014fe7359520014fc735952013cff7259520006ef72595200d4ef7259520004f
  | 17 => 0xdec72596200d76f52596200067f7559620004ff745962001cfe745962001cfc7459620004ff7359620014fe7359620014fc73596200d6ef725962013e7f52596200d6ef52596200d66f525962013e7d525962013eec5259620004ff7159620004fc71596200d67f515962013eec215962000cfc70596200d67c505962013eef20596200cebe64d9220295fa70d9220024fe75d9220004fd75d9220024fc75d922010cfd74d9220014fe73d9220004fd73d9220014fc73d9220006ed72d9220004fe71d9220004fd71d9220294fe70d9220006fa70d922001cff76592200cebc6459220004ff7559220024fe7559220024fc7559220006bf7459220006bf54592200cebc5459220004ff7359220014fe7359220014fc73592200cebf435922010ebf425922010ebd4259220004ff7159220004fc71592200cebf415922000cfc70592200cebc4059220004ff7655220004fe7655220004fd7655220004fc7655220005ef725522000dec72552200c6de63d8e2028dfa70d8e20024fe75d8e20004fd75d8e20024fc75d8e2001cfe74d8e20004fd74d8e2001cfc74d8e200dcfd73d8e20006ed72d8e20004fe71d8e20004fd71d8e2028cfe70d8e20006fa70d8e20014ff7658e200c6dc6358e20004ff7558e20024fe7558e20024fc7558e20004ff7458e2001cfe7458e2001cfc7458e20006df7358e20006df5358e200c6dc5358e200c6de4358e200dedf3258e200dedd3258e20004ff7158e20004fc7158e200c6df3158e2000cfc7058e200c6dc3058e20004ff7654e20004fe7654e20004fd7654e20004fc7654e20005ef7254e2000dec7254e20004ff7650e20004fe7650e20004fd7650e20004fc7650e2001ebe6450e20006bd6450e20016de6350e20006dd6350e200c79c4350e2002dfa70d8620006f76198620024fe7598620004fd7598620024fc759862001cfe7498620004fd749862001cfc7498620014fe7398620004fd7398620014fc739862008ef6219862008ef521986200057f75586200d57c7558620004ff75586200067f75586200047f7558620024fe7558620024fc75586200067c75586200247c7558620004ff745862001cfe745862001cfc7458620004ff7358620014fe7358620014fc7358620006ef525862004eec525862004ef6215862004ef5215862004eec215862004eef20586200d57e75186200057d75186200cdbe7418620005bd74186200c5de7318620005dd7318620006f5611862006dfa7018620004ff7694620004fe7694620004fd76946200067f65946200267c659462000dee7294620005ed72946200d76f5294620004ff7654620004fd7654620004fc76546200267e65546200067d6554620005ef725462000dec72546201ff6c5254620004ff7690620004fe7690620004fd76906200c5de739
  | 18 => 0xf72585300ddec7258530095fb7058530006bf6418530006bc6418530006f56118530024fe7518530004fd7518530024fc751853001cfe7418530004fd741853001cfc7418530036de4318530006dd431853000cfe7218530004fd721853000cfc7218530006f75118530006f45118530036df3118530036f63118530036f53118530006f72118530006f42118530036dc3018530004fe7694530004fd7694530004fc76945300067f65945300267c6594530006bf6494530226bc6494530015de7394530005dd73945300ddee7294530005ed7294530004ff7654530004fe7654530004fc7654530006bf645453020ebc6454530004fe7690530004fd7690530004fc7690530006bf649053001ebc6490530015de7390530005dd73905300079d4390530004ff7650530004fe7650530004fc7650530006bf645053001ebc6450530015de73505301d79e4350530005df744c530005dd744c5300079f644c5301a6de644c5301a6dc644c5300079c644c5301a69c644c530015df714c530017d7714c530007d7614c530006dc614c530007d4614c530006d4614c530007db704c530005dc704c530007d8704c530016df604c530017db604c530004fe7688530004fd7688530004fc76885300ed7e75885300057d7588530006bf648853018ebc6488530015de7388530005dd7388530006ef628853000eec6288530004ff7648530004fe7648530004fc7648530006bf6448530176bc64485302c4fe7694130006bf6494130166bc64941300ef7b5094130024ff7654130014fe7654130144fd7654130014fc76541300067f65541300267c6554130006bf645413014ebc6454130005df7354130015dc7354130005ef72541300ddec72541302bcfe769013012ebf649013001ebc6490130015dc739013012f9e439013001cff7650130014fe7650130114fd7650130014fc7650130006bf645013001ebc6450130005df7350130015dc73501300079d4350130005df748c130005dd748c1300079f648c1300fede648c1300fedc648c1300079c648c1300fe9c648c130005dd718c130006dc618c130015de708c130017da708c130016df608c130017db608c1300d67e65d96200cdbe74d9620005bd74d96200c5de73d9620005dd73d96201576c52d962029dfa70d962013cfd75d962001cfe74d9620006be74d962001cbe74d9620004fd74d9620006bd74d9620004bd74d962001cfc74d9620014fe73d9620006de73d9620014de73d9620004fd73d9620006dd73d9620004dd73d9620014fc73d9620006ed72d96200d6ef52d96201567e52d96201567c52d9620156ec52d96201566c52d9620004fe71d9620004fd71d96200d67c51d9620156ec21d962029cfe70d9620006fa70d96200d67f50d9620156ef20d9620024ff76596200d67c6559620
  | 19 => 0x913012ebe73d913012ebd73d913012ebc73d913012ebf53d913012ebe53d913012ebd53d913012ebc53d9130006bf72d9130006be72d9130006bd72d9130006bc72d9130006bf52d9130006be52d9130006bc52d913012ebf32d913012ebe32d913012ebd32d913012ebc32d9130006bf71d9130006be71d9130006bd71d9130006bc71d9130006bf51d9130006bc51d913012ebf31d913012ebe31d913012ebd31d913012ebc31d9130006bf21d9130006bc21d913012ebf70d91300e6be70d913012ebd70d9130006bf50d9130006bc50d913012ebf30d913012ebe30d913012ebc30d9130006bf20d9130006bc20d91300e6bc64591302d5fb7059130004ff7559130024fe7559130024fc755913012cff7459130006bf7459130114ff7359130006df73591300fcdf7359130004ff725913000cfe725913000cfc7259130004ff7159130004fc71591302d4ff7059130006fb705913012dbe76191300e6be761913012cbe7619130006bf6519130006be6519130006bd6519130006bc65191302bf9e73191300e79d73191302bebf6319130006be6219130006bc62191302bf9f31191302bebf60191302bfbb30191302bf9c30191302bfb83019130004ff7655130004fe7655130004fd7655130004fc7655130006bf645513001ebc64551300e5dc7650d3001edc7650d3001cdc7650d30015df7450d300179f7450d300079f6450d3001ede6450d3001edc6450d300e79c6450d3001e9c6450d30005df7150d300e79c4150d30007db7050d30005dc7050d30007d87050d30016df6050d30017db6050d300e79f4050d3000cfe76d8930006bf64d8930006bc64d89300deee62d8930024fe75d8930004fd75d8930024fc75d893001cfe74d8930004fd74d893001cfc74d893000cfc73d8930006ef52d89300deec52d89300deee32d89300c6ed32d8930004fe71d8930004fd71d89300deec21d8930014fd70d89300deef20d89300057f75589300ed7c7558930005bf74589300e5bc7458930006bf6458930006bc64589300deec6258930005f77158930005f471589302cdfb7058930004ff7654930004fe7654930004fc7654930006bf6454930256bc6454930005df7354930015dc73549300df6c5254930004ff7650930004fe7650930004fc7650930006bf645093001ebc6450930006bf64d8530006bc64d8530024fe75d8530004fd75d8530024fc75d853001cfe74d8530004fd74d853001cfc74d853000cfe72d8530004fd72d853000cfc72d8530006f751d8530006f451d8530076f631d8530076f531d8530006f721d8530006f421d85300e5be7498530005bd7498530006bf6498530006bc6498530006f76198530055f970985300057f75585300ed7c7558530005bf74585300e5bc7458530006bf6458530006bc6458530005e
  | 20 => 0x4fe7690630004fd7690630006bf649063001ebc6490630015de7390630005dd73906300ff9f4390630004ff7650630004fd7650630004fc765063001ebe6450630006bd6450630005df7350630015dc73506301d79c43506300fdde748c6300079e748c6300fd9e748c6300079d748c6300fddc748c630006df648c630006dd648c630015de718c630017d6718c630007d6618c630006dd618c630007d5618c630007da708c630005dd708c630007d9708c630016de608c630017da608c630004ff7688630004fe7688630004fd76886301057e75886300057d7588630004ff7648630004fd7648630004fc7648630005df7348630015dc734863000eee6248630006ed6248630014ff7694230024fe7694230014fd76942300267e65942300067d6594230015de7394230005dd73942301077b509423015fdb30942302dcff7654230005ef72542300f5ec7254230147db3054230014ff769023001cfe7690230014fd769023001ebe6490230006bd6490230015de7390230005dd739023012f9c43902302d4ff7650230006bf645023001ebc64502300fddf7350230015dc73502300ff9f4350230024fe76d95300ee7e65d953001cfe74d9530004fd74d953001cfc74d953015cff73d9530014fe73d953015cfd73d9530014fc73d953015e7f53d953015e7d53d953000cfe72d9530004fd72d953000cfc72d95300067e52d95300ee7c52d9530004fe71d9530004fd71d95300ee7c51d9530014fd70d95300ee7f50d95300ee7c6559530005bf74595300e5bc7459530005ef72595300ddec7259530005f77159530005f471595302ddfb705953015cff75595300067f7559530004ff7459530006bf7459530004bf745953001cfe745953001cfc7459530006bc745953001cbc7459530144ff7359530006df7359530004ff7259530006ef7259530004ef725953000cfe725953000cfc7259530006ec725953000cec7259530004ff7159530006f77159530004f77159530004fc7159530006f47159530004f471595302dcff7059530006fb705953001cfe76d91300e6be64d9130024fe75d9130004fd75d9130024fc75d9130006bf54d91300e6be54d91300e6bc54d913012cff73d9130014fe73d913012cfd73d9130014fc73d913012ebf43d913012ebd43d913000cfe72d9130004fd72d913000cfc72d91300e6bf42d9130006be42d91300e6bc42d9130004fe71d9130004fd71d91300e6bf41d91300e6bc41d9130014fd70d91300e6bf40d91302bdbe76d913001cbe76d9130006bf65d9130006be65d9130006bd65d9130006bc65d91300079f73d913012f9c73d9130006be62d9130006bc62d913012f9f31d913012fbb30d913012f9c30d913012fb830d9130006bf75d9130006be75d9130006bd75d9130006bc75d913012ebf73d
  | 21 => 0xc65596300067f7559630004ff745963001cfe745963001cfc74596300067e54596301067c54596301467f53596301467d5359630004ff725963000cfe725963000cfc72596301067f5259630004ff7159630004fc71596301067f5159630014fc70596301067c50596301057e75d92300057d75d92300febe64d923012f9c43d92300f5ee72d9230005ed72d92302bdfa70d9230024fe75d92300067e75d92300247e75d9230004fd75d92300067d75d92300047d75d9230024fc75d9230114fd74d9230006dd73d92300fedf43d923012ebe43d923012ebc43d923012edc43d923012e9c43d923000cfe72d9230006ee72d923000cee72d9230004fd72d9230006ed72d9230004ed72d923000cfc72d9230004fe71d9230004fd71d92300febc41d923012edc31d92302bcfe70d9230006fa70d92300febf40d923012edf30d923001cff76592300febc6459230015dc73592300ff9f4359230004ff7559230024fe7559230024fc7559230006bf74592300fedf7359230116bf43592300fedf4359230116bd4359230116dc4359230004ff725923000cfe725923000cfc7259230004ff7159230004fc71592300febf4159230116dc3159230014fc70592300febc4059230116df3059230004ff7655230004fe7655230004fd7655230004fc7655230005df7355230015dc73552300f6ee62d8a302e5fa70d8a3000cff7658a300f6ec6258a30004ff7558a30024fe7558a30024fc7558a30004ff7458a3001cfe7458a3001cfc7458a300f6ee5258a30006ef4258a300f6ec4258a300f6ee3258a300aeed3258a30004ff7158a30004fc7158a300f6ef2158a30014fc7058a300f6ec2058a30004ff7654a30004fd7654a30004fc7654a300267e6554a300067d6554a3000eee6254a30006ed6254a300f76c5254a30004ff7650a30004fd7650a30004fc7650a30005df7350a30015dc7350a30035fa70d8630006f76198630024fe7598630004fd7598630024fc759863001cfe7498630004fd749863001cfc749863000cfe7298630004fd729863000cfc7298630096f63198630096f53198630005bf74586300fdbc7458630004ff7558630024fe7558630024fc7558630004ff7458630006bf7458630004bf745863001cfe745863001cfc7458630006bc745863001cbc7458630006df4358630056dc4358630004ff725863000cfe725863000cfc7258630056f63158630056f53158630056dc3158630056df30586301057e75186300057d75186300fdbe7418630005bd74186300f5ee7218630005ed7218630006f56118630075fa7018630004ff7694630004fe7694630004fd76946300f5ee7294630005ed7294630004ff7654630004fd7654630004fc76546300267e65546300067d6554630005df7354630015dc7354630004ff7690630
  | 22 => 0x4940006df635494024edc635494010f6c5254940004ff764c940004fe764c940004fc764c940006df634c940016dc634c940006df63d8540006dc63d8540024fe75d8540004fd75d8540024fc75d8540014fe73d8540004fd73d8540014fc73d854000cfe72d8540004fd72d854000cfc72d8540006f751d8540006f451d854007ef641d854007ef541d8540006f721d8540006f421d8540115de7398540005dd7398540006df6398540006dc6398540006f7619854005df970985400057f755854011d7c7558540005df7358540115dc7358540006df6358540006dc6358540005ef725854010dec725854009dfb7058540006df6318540006dc6318540006f56118540024fe7518540004fd7518540024fc7518540014fe7318540004fd7318540014fc731854003ebf4318540006bd431854000cfe7218540004fd721854000cfc7218540006f75118540006f4511854003ebf411854003ef6411854003ef54118540006f72118540006f4211854003ebc4018540004fe7694540004fd7694540004fc76945400067f65945400267c659454001dbe7494540005bd7494540006df639454021edc639454010dee7294540005ed7294540004ff7654540004fe7654540004fc7654540006df6354540206dc6354540005bf73505400079f63505401d6be63505401d6bc63505400079c63505401d69c635054001dbf715054001fb77150540007b76150540006bc6150540007b46150540006b46150540007bb7050540005bc7050540007b8705054001ebf605054001fbb6050540004fe768c540004fd768c540004fc768c54001dbe748c540005bd748c540006df638c540016dc638c5400079d438c540004ff764c540004fe764c540004fc764c54001dbe744c540005bd744c540006df634c540016dc634c5401a79f434c540004fe7688540004fd7688540004fc768854011d7e75885400057d758854001dbe7488540005bd7488540006df6388540186dc6388540006ef628854000eec6288540004ff7648540004fe7648540004fc7648540006df634854016edc63485402ecfe7694140006df639414015edc639414011f7b5094140024ff765414001cfe765414014cfd765414001cfc76541400067f65541400267c6554140005bf745414001dbc7454140006df6354140146dc6354140005ef725414010dec7254140005bd73901400079f639014012ebe639014012ebc63901400079c639014012e9c6390140005bd7190140006bc619014001dbe709014001fba709014001ebf609014001fbb60901401067e65d96302c5fa70d9630144fd75d963001cfe74d9630004fd74d963001cfc74d9630006dd73d963000cfe72d9630004fd72d963000cfc72d9630004fe71d9630004fd71d96302c4fe70d9630006fa70d9630024ff76596301067
  | 23 => 0x6ef7259540004ef725954000cfe725954000cfc7259540006ec725954000cec7259540004ff7159540006f77159540004f77159540004fc7159540006f47159540004f4715954030cff7059540006fb7059540014fe76d8d40116de63d8d40024fe75d8d40004fd75d8d40024fc75d8d40014fc74d8d40006df53d8d40116de53d8d40116dc53d8d40116de43d8d400fedd43d8d4000cfe72d8d40004fd72d8d4000cfc72d8d40116df32d8d40006de32d8d40116dc32d8d40004fe71d8d40004fd71d8d40116df31d8d40116dc31d8d4001cfd70d8d40116df30d8d40115de76d8d40014de76d8d40006df65d8d40006de65d8d40006dd65d8d40006dc65d8d400079f74d8d400ff9c74d8d40006de62d8d40006dc62d8d400ff9f41d8d400ffdb40d8d400ff9c40d8d400ffd840d8d40006df75d8d40006de75d8d40006dd75d8d40006dc75d8d400fedf74d8d40116de74d8d400fedc74d8d400fedf54d8d400fede54d8d400fedd54d8d400fedc54d8d40006df72d8d40006de72d8d40006dd72d8d40006dc72d8d40006df52d8d40006de52d8d40006dc52d8d400fedf42d8d400fede42d8d400fedd42d8d400fedc42d8d40006df71d8d40006de71d8d40006dd71d8d40006dc71d8d40006df51d8d40006dc51d8d400fedf41d8d400fede41d8d400fedd41d8d400fedc41d8d40006df21d8d40006dc21d8d400fedf70d8d40116de70d8d400fedd70d8d40006df50d8d40006dc50d8d400fedf40d8d400fede40d8d400fedc40d8d40006df20d8d40006dc20d8d40116dc6358d40305fb7058d400fdde7618d40116de7618d40006df6518d40006de6518d40006dd6518d40006dc6518d401179e7418d401179d7418d4012edf6418d40006de6218d40006dc6218d402ff9f4118d402d6df6018d402ffdb4018d402ff9c4018d402ffd84018d40004ff7654d40004fe7654d40004fc7654d40006df6354d40016dc6354d40115bc7650d40016bc7650d40014bc7650d4001dbf7350d4001f9f7350d400079f6350d40016be6350d40016bc6350d401179c6350d400169c6350d40005bf7150d401179c3150d40007bb7050d40005bc7050d40007b87050d4001ebf6050d4001fbb6050d401179f3050d4000cfe76d8940006df63d8940006dc63d894010eee62d8940024fe75d8940004fd75d8940024fc75d894000cfc74d8940014fe73d8940004fd73d8940014fc73d8940006ef52d894010eec52d894010eee42d89400ceed42d8940004fe71d8940004fd71d894010eec21d894001cfd70d894010eef20d89400057f755894011d7c7558940005df7358940115dc7358940006df6358940006dc635894010eec6258940005f77158940005f471589402f5fb7058940004ff7654940004fe7654940004fc7654940005bf745494001dbc745
  | 24 => 0xf3258a40126ec3258a40004ff7158a40004fc7158a40126ef2158a4001cfc7058a40126ec2058a40004ff7654a40004fd7654a40004fc7654a400267e6554a400067d6554a4000eee6254a40006ed6254a401276c5254a40004ff764ca40004fd764ca40004fc764ca40005bf744ca4001dbc744ca4003dfa70d8640006f76198640024fe7598640004fd7598640024fc7598640014fe7398640004fd7398640014fc739864000cfe7298640004fd729864000cfc729864009ef6419864009ef54198640005df735864012ddc7358640004ff7558640024fe7558640024fc7558640004ff7358640006df7358640004df7358640014fe7358640014fc7358640006dc7358640014dc7358640006be435864005ebc4358640004ff725864000cfe725864000cfc725864005ef6415864005ef5415864005ebc415864005ebf40586401357e75186400057d751864012dde7318640005dd7318640125ee7218640005ed7218640006f5611864007dfa7018640004ff7694640004fe7694640004fd7694640125ee7294640005ed7294640004ff7654640004fd7654640004fc76546400267e65546400067d6554640005bf745464001dbc745464012dbe73906400079e739064012d9e73906400079d739064012dbc7390640006bd639064001dbe719064001fb67190640007b66190640006bd6190640007b56190640007ba7090640005bd7090640007b9709064001ebe609064001fba6090640004ff768c640004fe768c640004fd768c64001dbe748c640005bd748c640016dc638c64012f9e438c640004ff764c640004fd764c640004fc764c640005bf744c64001dbc744c640016de634c640006dd634c64012f9c434c640004ff7688640004fe7688640004fd76886401357e75886400057d7588640004ff7648640004fd7648640004fc7648640005bf744864001dbc744864000eee6248640006ed624864001cff7694240024fe769424001cfd76942400267e65942400067d659424001dbe7494240005bd74942401377b5094240167bb409424030cff7654240005ef7254240125ec725424014fbb4054240024fe76d954011e7e65d9540164ff74d954001cfe74d9540164fd74d954001cfc74d95401667f54d95401667d54d9540014fe73d9540004fd73d9540014fc73d954000cfe72d9540004fd72d954000cfc72d95400067e52d954011e7c52d9540004fe71d9540004fd71d954011e7c51d954001cfd70d954011e7f50d954011e7c6559540005df7359540115dc7359540005ef725954010dec7259540005f77159540005f4715954030dfb7059540164ff75595400067f755954014cff7459540006bf7459540004ff7359540006df7359540004df7359540014fe7359540014fc7359540006dc7359540014dc7359540004ff7259540
  | 25 => 0x8550004fd7318550014fc731855000cfe7218550004fd721855000cfc72185500467f52185500067d52185500467f5118550046f65118550046f55118550006f74118550006f44118550006f73118550006f431185500467c50185500057f72545500076f62545501fe7e62545501fe7c62545500076c62545501fe6c62545500257f71545500277771545500077761545500067c61545500077461545500077b70545500057c70545500077870545500267f60545500277b6054550004fe7690550004fd7690550004fc76905500257e75905500057d7590550006bf649055001ebc6490550145de7390550005dd7390550006ef62905501e6ec6290550004ff7650550004fe7650550004fc7650550006ef62505501ceec6250550004fe768c550004fd768c550004fc768c5500257e758c5500057d758c55014dbe748c550005bd748c550006df638c550016dc638c550006ef628c5501b6ec628c550004ff764c550004fe764c550004fc764c550006ef624c55019eec624c550004fe7688550004fd7688550004fc76885500257e75885500057d7588550006ef628855000eec62885500076d5288550004ff7648550004fe7648550004fc76485500257e75485500057d7548550006ef624855000eec624855017f6f52485500057d72941500076f62941501567e62941501567c62941500076c62941501566c62941500057d71941500067c61941500257e70941500277a70941500267f60941500277b60941501367e65d96402edfa70d964014cfd75d9640006bd74d9640014fe73d9640004fd73d9640014fc73d964000cfe72d9640004fd72d964000cfc72d9640004fe71d9640004fd71d96402ecfe70d9640006fa70d9640024ff76596401367c65596400067f755964014e7f545964014e7d5459640004ff7359640014fe7359640014fc73596400067e53596401367c5359640004ff725964000cfe725964000cfc72596401367f5259640004ff7159640004fc71596401367f515964001cfc70596401367c50596401357e75d8e400057d75d8e4012ede63d8e4012f9c43d8e40125ee72d8e40005ed72d8e402fdfa70d8e40014ff7658e4001dbc7458e4012edc6358e4012f9e4358e40004ff7558e40024fe7558e40024fc7558e4012ebe4358e4012ede4358e400e6dd4358e4012ebc4358e40004ff7258e4000cfe7258e4000cfc7258e40004ff7158e40004fc7158e400e6bc4158e4012edf3158e4001cfc7058e400e6bf4058e4012edc3058e40004ff7654e40004fd7654e40004fc7654e40005bf7454e4001dbc7454e40126ee62d8a40315fa70d8a4000cff7658a40126ec6258a40004ff7558a40024fe7558a40024fc7558a40004ff7358a40014fe7358a40014fc7358a40126ee5258a40126ee4258a400b6ed4258a40006e
  | 26 => 0xcfe76d895013eee62d895000cfc75d895001cfe74d8950004fd74d895001cfc74d8950014fe73d8950004fd73d8950014fc73d895013eee52d89500d6ed52d8950006ef42d895013eee42d895013eec42d8950006ef32d895013eee32d895013eec32d8950004fe71d8950004fd71d895013eef21d895013eec21d8950024fd70d895013eef20d895013dee76d895000cee76d89500076f75d89500d76c75d8950006ef64d8950006ee64d8950006ed64d8950006ec64d8950006ef63d8950006ee63d8950006ed63d8950006ec63d89500d76f51d89500d7eb50d89500d76c50d89500d7e850d89500d6ef75d895013eee75d89500d6ec75d8950006ef74d8950006ee74d8950006ed74d8950006ec74d89500d6ef54d89500d6ee54d89500d6ed54d89500d6ec54d8950006ef73d8950006ee73d8950006ed73d8950006ec73d89500d6ef53d89500d6ee53d89500d6ed53d89500d6ec53d8950006ef43d8950006ee43d8950006ed43d8950006ec43d8950006ef71d8950006ee71d8950006ed71d8950006ec71d89500d6ef51d89500d6ee51d89500d6ed51d89500d6ec51d8950006ef41d8950006ec41d8950006ef31d8950006ec31d89500d6ef70d895013eee70d89500d6ed70d89500d6ef50d89500d6ee50d89500d6ec50d8950006ef40d8950006ec40d8950006ef30d8950006ec30d895013eec6258950325fb70589500d5ee761895013eee761895013f6e751895013f6d7518950156ef6518950006ef6418950006ee6418950006ed6418950006ec6418950006ef6318950006ee6318950006ed6318950006ec631895031f6f51189502b6ef601895031feb501895031f6c501895031fe8501895013d7c765495000e7c765495000c7c76549500257f72549500276f72549500076f625495000e7e625495000e7c625495013f6c625495000e6c62549500057f715495013f6c21549500077b70549500057c70549500077870549500267f60549500277b605495013f6f2054950004ff7650950004fe7650950004fc7650950006ef625095000eec6250950004ff764c950004fe764c950004fc764c950006ef624c95000eec624c950006ef62d8550006ec62d855001cfe74d8550004fd74d855001cfc74d8550014fe73d8550004fd73d8550014fc73d855000cfe72d8550004fd72d855000cfc72d8550086f651d8550086f551d8550006f741d8550006f441d8550006f731d8550006f431d855013dee7298550005ed7298550006ef6298550006ec6298550006f76198550065f97098550005bf745855014dbc7458550005df7358550145dc7358550005ef725855013dec7258550006ef6258550006ec62585500a5fb7058550006ef6218550006ec6218550006f5611855001cfe7418550004fd741855001cfc7418550014fe731
  | 27 => 0xc5158a50156ef2158a50024fc7058a500be7f5058a50156ec2058a50004ff7650a50004fd7650a50004fc7650a500057f7550a500257c7550a50004ff764ca50004fd764ca50004fc764ca500057f754ca500257c754ca50045fa70d8650006f7619865001cfe7498650004fd749865001cfc7498650014fe7398650004fd7398650014fc739865000cfe7298650004fd729865000cfc72986500a6f651986500a6f55198650005ef7258650155ec7258650004ff745865001cfe745865001cfc7458650004ff7358650014fe7358650014fc7358650004ff7258650006ef7258650004ef725865000cfe725865000cfc7258650006ec725865000cec72586500067e52586500667c5258650066f65158650066f551586500667c51586500667f5058650165be7418650005bd741865015dde7318650005dd7318650155ee7218650005ed7218650006f56118650085fa70186501557e72946500076e72946501556e72946500076d72946501557c72946500067d62946500257e71946500277671946500077661946500067d61946500077561946500077a70946500057d70946500077970946500267e60946500277a6094650004ff7690650004fe7690650004fd769065015dde7390650005dd7390650004ff7650650004fd7650650004fc76506500057f75506500257c755065001ebe6450650006bd6450650004ff768c650004fe768c650004fd768c650165be748c650005bd748c650004ff764c650004fd764c650004fc764c6500057f754c6500257c754c650016de634c650006dd634c650004ff7688650004fe7688650004fd76886500257e75886500057d758865000eec62886501576e5288650004ff7648650004fd7648650004fc76486500057f75486500257c754865000eee6248650006ed62486501576c524865001cfe76d915014ebe64d915001cfc75d915014ebe54d9150136bd54d9150014fe73d9150004fd73d9150014fc73d9150006be43d915014ebc43d915000cfe72d9150004fd72d915000cfc72d9150004fe71d9150004fd71d915014ebc41d9150024fd70d915014ebf40d915014ebc6459150005df7359150145dc7359150005ef725915013dec7259150005f77159150005f47159150335fb7059150014fe76d8d50146de63d8d50014fc75d8d5001cfe74d8d50004fd74d8d5001cfc74d8d50146de53d8d50106dd53d8d50006df43d8d50146dc43d8d5000cfe72d8d50004fd72d8d5000cfc72d8d50004fe71d8d50004fd71d8d50146dc31d8d50024fd70d8d50146df30d8d50005bf7458d5014dbc7458d50146dc6358d50005ef7258d5013dec7258d50005f77158d50005f47158d5032dfb7058d50004ff7650d50004fe7650d50004fc7650d500057f7550d500257c7550d501479c4350d5025eec6250d50
  | 28 => 0xd2101ebc6450d21006df6350d21016dc6350d2116f9c4350d2135cfe76945210267e65945210067d659452100dee729452117ded729452117f6f5294521024ff765452100cfe76545211fcfd765452100cfc76545210067f65545210267c6554521005ef725452100dec72545211ff6c5254521354fe769052116dde7390521005dd739052101cff765052100cfe76505211ccfd765052100cfc7650521006bf645052101ebc6450521005ef725052100dec7250521177b4415052134cfe768c521175be748c521005bd748c521014ff764c52100cfe764c52119cfd764c52100cfc764c521006df634c521016dc634c521005ef724c52100dec724c52116fd4314c52117dee75885210076e758852117d6e75885210076d758852117dec7588521006ef6588521006ed658852100dee718852100fe6718852100eef618852100fe76188521005ed7088521024fe75d8121004fd75d8121024fc75d812101cfe74d8121004fd74d812101cfc74d8121014fe73d8121004fd73d8121014fc73d8121006fb50d8121006f850d812108efa20d8121006fb60981210057f755812117d7c7558121005bf7458121175bc7458121005df735812116ddc735812117d7e75181210057d7518121006f96018121024fe75181210067e75181210247e7518121004fd75181210067d75181210047d7518121024fc751812101cfe7418121004fd741812101cfc7418121014fe7318121004fd7318121014fc7318121006ef521812102eec5218121006ee211812102eec2118121006fb5018121006f8501812102eef201812102ef92018121166be64d9250345fa70d925001cff7659250166bc6459250166be545925011ebd5459250004ff7359250014fe7359250014fc7359250166bf4359250004ff725925000cfe725925000cfc7259250006be4259250166bc4259250004ff7159250004fc7159250166bf4159250024fc7059250166bc405925015ede63d8e5033dfa70d8e50014ff7658e5015edc6358e50004ff7458e5001cfe7458e5001cfc7458e5015ede5358e500eedd5358e5015ede4358e50004ff7258e5000cfe7258e5000cfc7258e50006de3258e5015edc3258e50004ff7158e50004fc7158e5015edf3158e50024fc7058e5015edc3058e50004ff7650e50004fd7650e50004fc7650e5001ebe6450e50006bd6450e50016de6350e50006dd6350e5015f9c4350e50165be74d8a50005bd74d8a5015dde73d8a50005dd73d8a50156ee62d8a501576c52d8a5031dfa70d8a5000cff7658a500257c7558a50156ec6258a501576e5258a50004ff7458a5001cfe7458a5001cfc7458a50004ff7358a50014fe7358a50014fc7358a501567e5258a50156ee5258a501566e5258a500beed5258a501567c5258a50004ff7158a50004fc7158a500be7
  | 29 => 0x4eef215822104efa205822104eec20582211957e75182210057d75182210067e65182210067d651822118dbe7418221005bd7418221185de7318221005dd7318221006f96018221024fe76d952117e7e65d952100dee72d952117f6f52d952101cfe74d9521004fd74d952101cfc74d9521014fe73d9521004fd73d9521014fc73d9521214ff72d9521214fd72d952117eed72d952117ced72d95212167f52d952117eef52d952117e6f52d95212167d52d9521216ec52d952100cfd71d952117e7f51d9521216ec21d9521004fe70d9521004fd70d952117e7c50d9521216ef20d952117e7c6559521005bf7459521175bc7459521005df735952116ddc73595211ff6c5259521375f77159521005fb7059521005f87059521214ff75595210067f7559521004ff7459521006bf7459521004bf745952101cfe745952101cfc7459521006bc745952101cbc7459521004ff7359521006df7359521004df7359521014fe7359521014fc7359521006dc7359521014dc73595211fcff7259521006ef725952117eef52595211fe7e52595211fe7c52595211feec52595211fe6c5259521374ff7159521006f7715952117e7c51595211feec2159521004ff7059521006fb7059521004fb7059521004fc7059521006f87059521004f8705952117e7f50595211feef205952101cfe76d9121176be64d9121024fe75d9121004fd75d9121024fc75d9121006bf54d9121176bc54d9121014fe73d9121004fd73d9121014fc73d9121176bf43d91211e4ff72d91211e4fd72d91211e6bf42d91211e6bd42d912100cfd71d9121176bf41d9121004fe70d9121004fd70d9121176bc40d9121176bc645912136df77159121004ff7559121024fe7559121024fc75591211e4ff7459121006bf7459121004ff7359121014fe7359121014fc73591211ccff7259121006ef725912136cff7159121006f77159121004ff7059121004fc7059121004ff7655121004fe7655121004fd7655121004fc7655121005ef725512100dec7255121014fe76d8d2116ede63d8d21024fe75d8d21004fd75d8d21024fc75d8d2101cfe74d8d21004fd74d8d2101cfc74d8d21006df53d8d2116edc53d8d2116ede43d8d211b4ff72d8d211b4fd72d8d211b6df32d8d211b6dd32d8d2100cfd71d8d2116edf31d8d21004fe70d8d21004fd70d8d2116edc30d8d2116edc6358d21365f77158d21004ff7558d21024fe7558d21024fc7558d21004ff7458d2101cfe7458d2101cfc7458d211b4ff7358d21006df7358d2119cff7258d21006ef7258d21364ff7158d21006f77158d21004ff7058d21004fc7058d21004ff7654d21004fe7654d21004fd7654d21004fc7654d21005ef7254d2100dec7254d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21006bf645
  | 30 => 0xe435922118ebc43592211cebf42592211cebd425922100cfc715922118ebc4159221004ff7059221004fc705922118ebf4059221004ff7655221004fe7655221004fd7655221004fc76552210267e65552210067d65552211957e75d8e210057d75d8e210067e65d8e210067d65d8e2118dbe74d8e21005bd74d8e21186de63d8e2134df671d8e21024fe75d8e210067e75d8e210247e75d8e21004fd75d8e210067d75d8e210047d75d8e21024fc75d8e2101cfe74d8e21006be74d8e2101cbe74d8e21004fd74d8e21006bd74d8e21004bd74d8e2101cfc74d8e2119cfd73d8e21006ed72d8e2134cfe71d8e21006f671d8e21004fe70d8e21004fd70d8e21014ff7658e210067e6558e210067d6558e21186dc6358e21004ff7558e21024fe7558e21024fc7558e21004ff7458e2101cfe7458e2101cfc7458e21006df7358e21006df4358e21186dc4358e2119edf3258e2119edd3258e2100cfc7158e21186dc3158e21004ff7058e21004fc7058e21186df3058e21004ff7654e21004fe7654e21004fd7654e21004fc7654e210267e6554e210067d6554e21004ff7650e21004fe7650e21004fd7650e21004fc7650e212667e6550e210067d6550e211879c4350e21005ef7250e2100dec7250e21195ef7654a21026ef7654a21024ef7654a2100def7554a2100f6f7554a21026ee6554a211976e6554a210266e6554a210076d6554a21026ec6554a21005ef7154a21007e77154a21007e47154a2100eee6154a2100fe66154a211976c5154a21005ec7054a211976f5054a2100cff7694621024fe769462100cfd76946210267e65946210067d659462100dee7294621005ed72946210076d5294621217e72194621374ff76546210267e65546211fe7d655462100dee72546211ff6e52546211ffe7215462100cff769062101cfe769062100cfd76906211f67e65906210067d659062101ebe6490621006bd6490621185de7390621005dd739062100dee7290621005ed729062136cff76506211de7e65506210067d655062118fb4415062100cff768c621014fe768c62100cfd768c6211c67e658c6210067d658c62118dbe748c621005bd748c621016de638c621006dd638c62100dee728c621005ed728c621364ff764c6211ae7e654c6210067d654c621187d4314c6211957e75d82210057d75d82210067e65d82210067d65d82210067e65982210067d6598221006fb6098221024fe7598221004fd7598221024fc759822101cfe7498221004fd749822101cfc7498221014fe7398221004fd7398221014fc739822106ef920982210067e65582210067d6558221004ff7558221024fe7558221024fc7558221004ff745822101cfe745822101cfc7458221004ff7358221014fe7358221014fc735822104eee5258221006ed5258221
  | 31 => 0x8131006f96018131024fe7518131004fd7518131024fc751813101cfe7418131006be741813101cbe7418131004fd7418131006bd7418131004bd741813101cfc7418131006df4318131036dc431813100cfe7218131004fd721813100cfc7218131006de3118131036dc3118131006fb4018131006f84018131036df3018131036f930181311967e65d962135df671d96211fcfd75d962101cfe74d9621004fd74d962101cfc74d9621014fe73d9621004fd73d9621014fc73d9621006ed72d962135cfe71d9621006f671d9621004fe70d9621004fd70d96211fc7d76996210067e64996210067c64996210067e63996210067c63996213776e72996211976d72996213767d62996213767e61996213776f21996213777721996213777421996213776c2099621024ff76596211967c65596210067f7559621004ff745962101cfe745962101cfc74596211967f54596210067e54596211967c5459621004ff7359621014fe7359621014fc73596211967f53596210067e53596211967c53596211fe7f52596211fe7d525962100cfc71596211967c5159621004ff7059621004fc70596211967f50596211967c50596213757f76596211967f76596210247f76596210067e64596210067c64596210067e63596210067c63596211ff6e72596210076d72596211ff6f21596211ff7721596211ff7421596211ff6c20596210067f74596210067e74596210067d74596210067c74596210067f73596210067e73596210067d73596210067c73596210067f43596210067e43596210067c43596211fe7f72596211fe7e72596211fe7d72596211fe7c72596211fe7f42596211fe7e42596211fe7d42596211fe7c42596211fe7f32596211fe7e32596211fe7d32596211fe7c32596211967f71596211fe7e71596211fe7c71596210067f41596210067c41596210067f31596210067c31596211fe7f21596211fe7e21596211fe7d21596211fe7c21596210067f70596210067e70596210067d70596210067c70596210067f40596210067c40596210067f30596210067c30596211fe7f20596211fe7e20596211fe7d20596211fe7c20596211957e75d92210057d75d92210067e65d92210067d65d922118ebe64d9221185de73d9221005dd73d9221355f671d9221024fe75d92210067e75d92210247e75d9221004fd75d92210067d75d92210047d75d9221024fc75d92211ccfd74d9221014fe73d9221006de73d9221014de73d9221004fd73d9221006dd73d9221004dd73d9221014fc73d9221006ed72d9221354fe71d9221006f671d9221004fe70d9221004fd70d922101cff76592210067e65592210067d655922118ebc6459221004ff7559221024fe7559221024fc7559221006bf7459221004ff7359221014fe7359221014fc7359221006b
  | 32 => 0x4fc705953101cfe76d91311a6be64d9131015de73d91311a79f43d9131024fe75d9131004fd75d9131024fc75d91311ecff73d91311ecfd73d91311a6dd73d91311a4dd73d91311eebf43d91311a6df43d91311eebd43d91311eedc43d913100cfe72d9131004fd72d913100cfc72d9131014fd71d91311a6bf41d91311eedc31d9131004fe70d9131004fd70d91311a6bc40d91311eedf30d91310057f75591311ad7c75591311a6bc64591311d79c4359131005ef725913119dec7259131395f77159131005fb7059131005f87059131004ff75591310067f75591310047f7559131024fe7559131024fc75591310067c75591310247c75591311ecff7459131006bf74591311d4ff7359131006df73591311a6df43591311d6be43591311d6bc43591311d6dc43591311d69c4359131004ff7259131006ef7259131004ef725913100cfe725913100cfc7259131006ec725913100cec7259131394ff7159131006f771591311a6bc41591311d6dc3159131004ff7059131006fb7059131004fb7059131004fc7059131006f87059131004f870591311a6bf40591311d6df3059131004ff7655131004fe7655131004fd7655131004fc7655131005df7355131015dc735513100cfe76d893119eee62d8931024fe75d8931004fd75d8931024fc75d893101cfe74d8931004fd74d893101cfc74d893119eee52d8931006ef42d893119eec42d893119eee32d8931186ed32d8931014fd71d893119eef21d8931004fe70d8931004fd70d893119eec20d893119eec625893138df77158931004ff7654931004fe7654931004fc76549310067f65549310267c6554931006ef625493100eec625493119f6c5254931004ff7650931004fe7650931004fc7650931005df7350931015dc7350931384fe769453119dee7294531005ed72945311af77519453121fd43194531024ff7654531014fe7654531204fd7654531014fc76545310067f65545310267c6554531005df7354531015dc7354531207d4315453137cfe769053101ebe6490531006bd6490531015de73905311a5dd73905311a79f439053101cff7650531014fe76505311d4fd7650531014fc7650531006bf645053101ebc6450531005df7350531015dc73505311d79c43505311a5de748c5310079e748c5311a59e748c5310079d748c5311a5dc748c531006df648c531006dd648c531015de718c531017d6718c531016df618c531017d7618c531005dd708c531024fe75d8131004fd75d8131024fc75d813101cfe74d8131004fd74d813101cfc74d813100cfe72d8131004fd72d813100cfc72d8131006fb40d8131006f840d8131096fa30d8131006fb60981310057f75581311ad7c7558131005bf74581311a5bc7458131005ef725813119dec72581311a5be7418131005bd741
  | 33 => 0xf7655231004fe7655231004fd7655231004fc765523101ebe6455231006bd64552311bddf7650e3101edf7650e3101cdf7650e31015df7450e310179f7450e3101ede6450e311bf9e6450e3101e9e6450e310079d6450e3101edc6450e31005df7150e31007d77150e31007d47150e31016de6150e31017d66150e311bf9c4150e31005dc7050e311bf9f4050e311c57e75d8a310057d75d8a311bdbe74d8a31005bd74d8a31006be64d8a31006bd64d8a311b6ee62d8a313a5f671d8a3100cff7658a31006be6458a31006bd6458a311b6ec6258a31004ff7558a31024fe7558a31024fc7558a31004ff7458a3101cfe7458a3101cfc7458a31006ef5258a311b6ec5258a311b6ee3258a3116eed3258a31014fc7158a311b6ec2158a31004ff7058a31004fc7058a311b6ef2058a31004ff7654a31004fd7654a31004fc7654a31256be6454a31006bd6454a31005df7354a31015dc7354a311b76c5254a31004ff7650a31004fd7650a31004fc7650a3101ebe6450a31006bd6450a31014ff7694631024fe7694631014fd76946310267e65946310067d6594631226be6494631006bd6494631015de7394631005dd73946311b5ee7294631005ed72946311c777519463121fd7319463139cff765463120ebe6454631006bd6454631207d73154631014ff769063101cfe7690631014fd769063101ebe6490631006bd6490631015de7390631005dd73906310079d4390631394ff765063101ebe64506311d6bd6450631015de73506311d79e43506311bdbe74d8231005bd74d8231006be64d8231006bd64d8231006be6498231006bd6498231006fb6098231024fe7598231004fd7598231024fc759823101cfe7498231004fd749823101cfc749823100cfe7298231004fd729823100cfc7298231076f93098231006be6458231006bd6458231004ff7558231024fe7558231024fc7558231004ff745823101cfe745823101cfc7458231056de4358231006dd4358231004ff725823100cfe725823100cfc7258231056df3158231056fa3058231056dc30582311c57e75182310057d75182311bdbe7418231005bd7418231006be6418231006bd64182311b5ee7218231005ed7218231006f96018231024fe76d95311ae7e65d953101cfe74d9531004fd74d953101cfc74d95310067e54d95311ae7c54d953121cff73d953121cfd73d953121e7f53d953121e7d53d953100cfe72d9531004fd72d953100cfc72d95311ae7f52d9531014fd71d95311ae7f51d9531004fe70d9531004fd70d95311ae7c50d95311ae7c655953139df7715953121cff75595310067f7559531004ff745953101cfe745953101cfc7459531204ff7359531006df7359531004ff725953100cfe725953100cfc725953139cff7159531006f77159531004ff7059531
  | 34 => 0x8141004dd7318141014fc7318141006be431814103ebc431814100cfe7218141004fd721814100cfc7218141006be411814103ebc411814103ebf401814103ef94018141006fb3018141006f830181411c67e65d96311bdbe74d9631005bd74d96311b5ee72d9631005ed72d9631385f671d9631204fd75d963101cfe74d9631006be74d963101cbe74d9631004fd74d9631006bd74d9631004bd74d963101cfc74d9631006dd73d963100cfe72d9631006ee72d963100cee72d9631004fd72d9631006ed72d9631004ed72d963100cfc72d9631384fe71d9631006f671d9631004fe70d9631004fd70d9631024ff76596311c67c65596310067f7559631004ff745963101cfe745963101cfc74596312067f53596312067d5359631004ff725963100cfe725963100cfc72596310067e52596311c67c5259631014fc71596311c67c5159631004ff7059631004fc70596311c67f50596311bebe64d923137df671d9231024fe75d9231004fd75d9231024fc75d92311d4fd74d9231006dd73d923100cfe72d9231004fd72d923100cfc72d923137cfe71d9231006f671d9231004fe70d9231004fd70d92311d4bd7699231006bf6599231006be6599231006bd6599231006bc65992313979e73992311bf9d7399231396bd6399231006be6299231006bc6299231396be61992313979f3199231397b73199231397b431992313979c309923101cff76592311bebc6459231004ff7559231024fe7559231024fc7559231006bf7459231006bf54592311bebe54592311bebc54592311d6bf43592311d6bd4359231004ff725923100cfe725923100cfc72592311bebf4259231006be42592311bebc4259231014fc71592311bebc4159231004ff7059231004fc70592311bebf40592311bebc4059231395bf76592311bebf765923101cbf7659231006bf6559231006be6559231006bd6559231006bc65592311d79e73592310079d7359231006be6259231006bc62592311d79f31592311d7b731592311d7b431592311d79c3059231006bf7559231006be7559231006bd7559231006bc75592311d6bf73592311d6be73592311d6bd73592311d6bc73592311d6bf53592311d6be53592311d6bd53592311d6bc5359231006bf7259231006be7259231006bd7259231006bc7259231006bf5259231006be5259231006bc52592311d6bf32592311d6be32592311d6bd32592311d6bc32592311bebf71592311d6be71592311d6bc7159231006bf5159231006bc51592311d6bf31592311d6be31592311d6bd31592311d6bc3159231006bf2159231006bc2159231006bf7059231006be7059231006bd7059231006bc7059231006bf5059231006bc50592311d6bf30592311d6be30592311d6bd30592311d6bc3059231006bf2059231006bc2059231004f
  | 35 => 0x5ebf415824105efa405824105ebc40582411f57e75182410057d75182411edde7318241005dd7318241006de6318241006dd63182411e5ee7218241005ed7218241006f96018241024fe76d95411de7e65d9541224ff74d9541224fd74d95412267f54d95412267d54d9541014fe73d9541004fd73d9541014fc73d95410067e53d95411de7c53d954100cfe72d9541004fd72d954100cfc72d95411de7f52d954101cfd71d95411de7f51d9541004fe70d9541004fd70d95411de7c50d95411de7c65595413c5f77159541224ff75595410067f755954120cff7459541006bf7459541004ff7359541014fe7359541014fc7359541004ff725954100cfe725954100cfc72595413c4ff7159541006f77159541004ff7059541004fc7059541014fe76d8d4101dbe74d8d411d6de63d8d411d79e43d8d41024fe75d8d41004fd75d8d41024fc75d8d411d6be43d8d411d6de43d8d411bedd43d8d411d6bc43d8d4100cfe72d8d41004fd72d8d4100cfc72d8d4101cfd71d8d411bebc41d8d411d6df31d8d41004fe70d8d41004fd70d8d411bebf40d8d411d6dc30d8d410057f7558d411dd7c7558d411d6dc6358d411d79c4358d41005ef7258d411cdec7258d413bdf77158d41005fb7058d41005f87058d41004ff7654d41004fe7654d41004fc7654d41005bf7454d4101dbc7454d4100cfe76d89411ceee62d8941024fe75d8941004fd75d8941024fc75d8941014fe73d8941004fd73d8941014fc73d89411ceee52d89411ceee42d894118eed42d8941006ef32d89411ceec32d894101cfd71d89411ceef21d8941004fe70d8941004fd70d89411ceec20d89411ceec62589413b5f77158941004ff7654941004fe7654941004fc76549410067f65549410267c6554941006ef625494100eec62549411cf6c5254941004ff764c941004fe764c941004fc764c941005bf744c94101dbc744c9413acfe76945411cdee7294541005ed72945411df775194541227b44194541024ff765454101cfe765454120cfd765454101cfc76545410067f65545410267c6554541005bf745454101dbc745454120fb441545411d5be73905410079e73905411d59e73905410079d73905411d5bc7390541006bf639054101dbe719054101fb6719054101ebf619054101fb76190541005bd7090541024fe75d8141004fd75d8141024fc75d8141014fe73d8141004fd73d8141014fc73d814100cfe72d8141004fd72d814100cfc72d814109efa40d8141006fb30d8141006f830d8141006fb60981410057f75581411dd7c7558141005df73581411d5dc7358141005ef72581411cdec72581411d5de7318141005dd7318141006f96018141024fe7518141004fd7518141024fc7518141014fe7318141006de7318141014de7318141004fd7318141006dd731
  | 36 => 0xc3058e411eddf7658e411eedf7658e41014df7658e41006df6558e41006de6558e41006dd6558e41006dc6558e411a79e7458e410079d7458e41006de6258e41006dc6258e411a79f4158e411a7d74158e411a7d44158e411a79c4058e41006df7558e41006de7558e41006dd7558e41006dc7558e411a6de7458e411a6dd7458e411eedc7458e411a6df5458e411a6de5458e411a6dd5458e411a6dc5458e41006df7258e41006de7258e41006dd7258e41006dc7258e41006df5258e41006de5258e41006dc5258e411a6df4258e411a6de4258e411a6dd4258e411a6dc4258e411eedf7158e411a6de7158e411a6dc7158e41006df5158e41006dc5158e411a6df4158e411a6de4158e411a6dd4158e411a6dc4158e41006df2158e41006dc2158e41006df7058e41006de7058e41006dd7058e41006dc7058e41006df5058e41006dc5058e411a6df4058e411a6de4058e411a6dd4058e411a6dc4058e41006df2058e41006dc2058e41004ff7654e41004fd7654e41004fc7654e41016de6354e41006dd6354e411edbf7650e41016bf7650e41014bf7650e4101dbf7350e4101f9f7350e41016be6350e411ef9e6350e410169e6350e410079d6350e41016bc6350e41005bf7150e41007b77150e41007b47150e4101ebe6150e4101fb66150e411ef9c3150e41005bc7050e411ef9f3050e411f57e75d8a410057d75d8a411edde73d8a41005dd73d8a41006de63d8a41006dd63d8a411e6ee62d8a413cdf671d8a4100cff7658a41006de6358a41006dd6358a411e6ec6258a41004ff7558a41024fe7558a41024fc7558a41004ff7358a41014fe7358a41014fc7358a41006ef5258a411e6ec5258a411e6ee4258a41176ed4258a4101cfc7158a411e6ec2158a41004ff7058a41004fc7058a411e6ef2058a41004ff7654a41004fd7654a41004fc7654a41005bf7454a4101dbc7454a4124ede6354a41006dd6354a411e76c5254a41004ff764ca41004fd764ca41004fc764ca41016de634ca41006dd634ca4101cff7694641024fe769464101cfd76946410267e65946410067d659464101dbe7494641005bd749464121ede6394641006dd63946411e5ee7294641005ed72946411f7775194641227b741946413c4ff7654641206de6354641006dd635464120fb741546411edde73d8241005dd73d8241006de63d8241006dd63d8241006de6398241006dd6398241006fb6098241024fe7598241004fd7598241024fc7598241014fe7398241004fd7398241014fc739824100cfe7298241004fd729824100cfc729824107ef94098241006de6358241006dd6358241004ff7558241024fe7558241024fc7558241004ff7358241014fe7358241014fc735824105ebf4358241006bd4358241004ff725824100cfe725824100cfc7258241
  | 37 => 0x895101cfc74d8951014fe73d8951004fd73d8951014fc73d89511fe7e52d89511feee52d89511fe6e52d8951196ed52d89511fe7c52d8951024fd71d89511967c51d89511feef21d8951004fe70d8951004fd70d89511967f50d89511feec20d8951005bf745895120dbc7458951005df7358951205dc73589511feec62589511ff6c52589513ddf77158951005fb7058951005f87058951004ff7650951004fe7650951004fc76509510057f75509510257c7550951004ff764c951004fe764c951004fc764c9510057f754c9510257c754c9511fd7e72945510076e72945511fd6e72945510076d72945511fd7c72945510067f62945510257e71945510277671945510267f61945510277761945510057d709455101cfe74d8151004fd74d815101cfc74d8151014fe73d8151004fd73d8151014fc73d815100cfe72d8151004fd72d815100cfc72d81510a6fa50d8151006fb20d8151006f820d8151006fb6098151005bf745815120dbc7458151005df7358151205dc7358151005ef72581511fdec72581511fdee7218151005ed7218151006f9601815101cfe7418151004fd741815101cfc7418151014fe7318151004fd7318151014fc731815100cfe7218151006ee721815100cee7218151004fd7218151006ed7218151004ed721815100cfc72181510067e52181510467c52181510067e51181510467c51181510467f5018151046f95018151006fb2018151006f820181511f67e65d96411edde73d9641005dd73d96411e5ee72d9641005ed72d96413adf671d964120cfd75d9641006bd74d9641014fe73d9641006de73d9641014de73d9641004fd73d9641006dd73d9641004dd73d9641014fc73d964100cfe72d9641006ee72d964100cee72d9641004fd72d9641006ed72d9641004ed72d964100cfc72d96413acfe71d9641006f671d9641004fe70d9641004fd70d9641024ff76596411f67c65596410067f755964120e7f545964120e7d5459641004ff7359641014fe7359641014fc7359641004ff725964100cfe725964100cfc72596410067e52596411f67c525964101cfc71596411f67c5159641004ff7059641004fc70596411f67f50596411eede63d8e413d5f671d8e41006df6598e41006de6598e41006dd6598e41006dc6598e411ef9e7498e411ef9d7498e411d6dd6498e41006de6298e41006dc6298e4137ede6198e413bf9f4198e413bfd74198e413bfd44198e413bf9c4098e41014ff7658e411eedc6358e41004ff7558e41024fe7558e41024fc7558e41006df5358e411eede5358e411eedc5358e411eede4358e411a6dd4358e41004ff7258e4100cfe7258e4100cfc7258e411eedf3258e41006de3258e411eedc3258e4101cfc7158e411eedc3158e41004ff7058e41004fc7058e411eedf3058e411eed
  | 38 => 0x17f6c5058a5117eee7558a5117eed7558a51216ec7558a51006ef7458a51006ee7458a51006ed7458a51006ec7458a5117eef5458a5117eee5458a5117eed5458a5117eec5458a51006ef7358a51006ee7358a51006ed7358a51006ec7358a5117eef5358a5117eee5358a5117eed5358a5117eec5358a51006ef4358a51006ee4358a51006ed4358a51006ec4358a51216ef7158a5117eee7158a5117eec7158a5117eef5158a5117eee5158a5117eed5158a5117eec5158a51006ef4158a51006ec4158a51006ef3158a51006ec3158a51006ef7058a51006ee7058a51006ed7058a51006ec7058a5117eef5058a5117eee5058a5117eed5058a5117eec5058a51006ef4058a51006ec4058a51006ef3058a51006ec3058a512157f7654a5100e7f7654a5100c7f7654a510257f7254a510276f7254a5100e7e6254a512176e6254a5100e6e6254a510076d6254a5100e7c6254a510057f7154a51007777154a51007747154a510267e6154a51027766154a512176c2154a510057c7054a512176f2054a51004ff7650a51004fd7650a51004fc7650a5100eee6250a51006ed6250a51004ff764ca51004fd764ca51004fc764ca5100eee624ca51006ed624ca51215ee72d8251005ed72d8251006ee62d8251006ed62d8251006ee6298251006ed6298251006fb609825101cfe7498251004fd749825101cfc7498251014fe7398251004fd7398251014fc739825100cfe7298251004fd729825100cfc7298251086f95098251006ee6258251006ed6258251004ff745825101cfe745825101cfc7458251004ff7358251014fe7358251014fc7358251004ff725825100cfe725825100cfc72582510667f52582510067d52582510667f5158251066fa50582510667c5058251225be7418251005bd741825121dde7318251005dd7318251215ee7218251005ed7218251006ee6218251006ed6218251006f9601825101cfe76d915120ebe64d915120ebe54d91511f6bd54d9151014fe73d9151004fd73d9151014fc73d915120ebf43d915100cfe72d9151004fd72d915100cfc72d9151006be42d915120ebc42d9151024fd71d915120ebf41d9151004fe70d9151004fd70d915120ebc40d915120ebc64591513edf77159151014fe76d8d51206de63d8d5101cfe74d8d51004fd74d8d5101cfc74d8d51206de53d8d511c6dd53d8d51206de43d8d5100cfe72d8d51004fd72d8d5100cfc72d8d51006de32d8d51206dc32d8d51024fd71d8d51206df31d8d51004fe70d8d51004fd70d8d51206dc30d8d51206dc6358d513e5f77158d51004ff7650d51004fe7650d51004fc7650d51006bf6450d5101ebc6450d51006df6350d51016dc6350d512079c4350d5100cfe76d89510257e75d89511feee62d89511ff6e52d895101cfe74d8951004fd74d
  | 39 => 0xe75d8532004fd75d8532024fc75d853201cfe74d8532004fd74d853201cfc74d853200cfd73d8532014fd72d853238ef631d8532366f621d8532004fe70d8532004fd70d85322357e75985320057d759853222dbe7498532005bd7498532006f76198532006f56118532024fe7518532004fd7518532024fc751853201cfe7418532004fd741853201cfc741853200cfd7318532014fd72185323a6f5311853234ef52118532004fe7018532004fd7018532024fe75d8132004fd75d8132024fc75d813201cfe74d8132004fd74d813201cfc74d813200cfd73d8132014fd72d8132004fe71d8132004fd71d81322cefa30d81322a6fa20d8132006fb60981320057f75581322357c7558132005bf745813222dbc7458132005f77158132005f47158132006f96018132024fe7518132004fd7518132024fc751813201cfe7418132004fd741813201cfc741813200cfd7318132014fd7218132004fe7118132004fd71181322e6f9301813228ef92018132226be64d925121dde73d9251005dd73d9251215ee72d9251005ed72d9251405f671d925101cff7659251226bc6459251226be54592511debd5459251004ff7359251014fe7359251014fc7359251006be4359251226bc4359251004ff725925100cfe725925100cfc7259251024fc7159251226bc4159251004ff7059251004fc7059251226bf4059251225be74d8e51005bd74d8e5121ede63d8e51215ee72d8e51005ed72d8e513fdf671d8e51014ff7658e5121edc6358e51004ff7458e5101cfe7458e5101cfc7458e5121ede5358e511aedd5358e51006df4358e5121edc4358e51004ff7258e5100cfe7258e5100cfc7258e51024fc7158e5121edc3158e51004ff7058e51004fc7058e5121edf3058e51004ff7650e51004fd7650e51004fc7650e510057f7550e510257c7550e5121f9c4350e5125eee6250e51216ee62d8a513f5f671d8a512176e7598a512176d7598a511feed6598a51006ef6498a51006ee6498a51006ed6498a51006ec6498a51006ef6398a51006ee6398a51006ed6398a51006ec6398a5135eee6198a513df6f5198a513dfe75198a513dfe45198a513df6c5098a5100cff7658a51216ec6258a51004ff7458a5101cfe7458a5101cfc7458a51004ff7358a51014fe7358a51014fc7358a51216ee5258a5117eed5258a51006ef4258a51216ee4258a51216ec4258a51006ef3258a51216ee3258a51216ec3258a51024fc7158a51216ec2158a51004ff7058a51004fc7058a51216ef2058a51216ec2058a51215ef7658a51216ef7658a5100cef7658a5117f6e7558a510076d7558a51006ef6458a51006ee6458a51006ed6458a51006ec6458a51006ef6358a51006ee6358a51006ed6358a51006ec6358a5117f6f5158a5117fe75158a5117fe45158a51
  | 40 => 0x8d4240edf32d8d42004fe71d8d42004fd71d8d4223edf31d8d42004fe70d8d42004fd70d8d4223edc30d8d420057f7558d422457c7558d4223edc6358d4244def7258d42004ff7654d42004fe7654d42004fc7654d42024fe75d8542004fd75d8542024fc75d854200cfd74d8542014fe73d8542004fd73d8542014fc73d854201cfd72d85423b6f641d854236ef621d8542004fe70d8542004fd70d85422457e75985420057d759854223dde7398542005dd7398542006f76198542006f56118542024fe7518542004fd7518542024fc751854200cfd7418542014fe7318542004fd7318542014fc731854201cfd72185423cef54118542356f52118542004fe7018542004fd7018542024fe75d8142004fd75d8142024fc75d814200cfd74d8142014fe73d8142004fd73d8142014fc73d814201cfd72d8142004fe71d8142004fd71d81422f6fa40d81422aefa20d8142006fb60981420057f75581422457c7558142005df735814223ddc7358142005f77158142005f47158142006f96018142024fe7518142004fd7518142024fc751814200cfd7418142014fe7318142004fd7318142014fc731814201cfd7218142004fe7118142004fd7118142316f94018142296f92018142024fe76d95322367e65d953226cfd75d953201cfe74d9532004fd74d953201cfc74d95320067e54d95322367c54d953200cff73d953200cfd73d95324467f53d95324467d53d9532014ff72d9532014fd72d95324367f52d95324367d52d9532004fe71d9532004fd71d95322367f51d9532004fe70d9532004fd70d95322367c50d9532024ff76595322367c6559532005bf745953222dbc745953242ddf735953243def7259532434ff75595320067f7559532004ff7459532006bf7459532004bf745953201cfe745953201cfc7459532006bc745953201cbc745953242cff7359532006df735953226cff7259532006ef7259532004ff7159532004fc7159532004ff7059532004fc705953201cfe76d913222ebe64d9132024fe75d9132004fd75d9132024fc75d913225cfd74d9132006bf54d913222ebc54d913200cff73d913200cfd73d9132426bf43d9132426bd43d9132014ff72d9132014fd72d9132416bf42d9132416bd42d9132004fe71d9132004fd71d913222ebf41d9132004fe70d9132004fd70d913222ebc40d913201cff76591320057f75591322357c755913222ebc645913240ddf735913241def7259132004ff75591320067f75591320047f7559132024fe7559132024fc75591320067c75591320247c7559132414ff7459132006bf745913240cff7359132006df735913225cff7259132006ef7259132004ff7159132004fc7159132004ff7059132004fc7059132004ff7655132004fe7655132004fd7655132004fc7655132024f
  | 41 => 0x1cfc74d8d5224ede53d8d52486dd53d8d52006df43d8d5224edc43d8d52024fd72d8d5242edf32d8d52004fe71d8d52004fd71d8d5224edc31d8d52004fe70d8d52004fd70d8d5224edf30d8d52005bf7458d52255bc7458d5224edc6358d5247def7258d5226f6c5258d52004ff7650d52004fe7650d52004fc7650d5224f9c4350d5225f6c5250d523776c52d855200cfd75d85523767d75d855201cfe74d8552004fd74d855201cfc74d8552014fe73d8552004fd73d8552014fc73d8552024fd72d85523deed72d85523deef52d85523767e52d85523767c52d8552376ec52d85523766c52d85523def651d85523de7c51d8552376f621d8552376ec21d8552004fe70d8552004fd70d85523de7f50d8552376ef20d85522176c5298552006f76198552005bf7458552255bc7458552005df735855224ddc73585521ff6c5258552005fb7058552005f8705855235f6c5218552006f5611855200cfd751855201cfe7418552004fd741855201cfc7418552014fe7318552004fd7318552014fc7318552024fd72185523f6f5511855235ef52118552004fe7018552004fd70185522b76c52d815200cfd75d815201cfe74d8152004fd74d815201cfc74d8152014fe73d8152004fd73d8152014fc73d8152024fd72d8152004fe71d8152004fd71d8152326fa50d81522b6fa20d8152255be7498152005bd749815224dde7398152005dd73981521576c5298152006fb609815213f6c525815229f6c5218152006f9601815200cfd751815229e7d751815201cfe7418152004fd741815201cfc7418152014fe7318152004fd7318152014fc7318152024fd721815231eed721815231eef521815229e7e521815229e7c521815229eec521815229e6c5218152004fe7118152004fd711815231e7c511815229eec211815231e7f501815231ef9501815229eef201815229ef92018152024fe76d95422467e65d954227cfd75d954200cff74d954200cfd74d95424767f54d95424767d54d9542014fe73d9542004fd73d9542014fc73d95420067e53d95422467c53d954201cff72d954201cfd72d95424667f52d95424667d52d9542004fe71d9542004fd71d95422467f51d9542004fe70d9542004fd70d95422467c50d9542024ff76595422467c655954245dbf7459542005df735954223ddc735954246def7259542464ff75595420067f755954245cff7459542006bf7459542004ff7359542006df7359542004df7359542014fe7359542014fc7359542006dc7359542014dc735954227cff7259542006ef7259542004ff7159542004fc7159542004ff7059542004fc7059542014fe76d8d4223ede63d8d42024fe75d8d42004fd75d8d42024fc75d8d4200cfd74d8d42006df53d8d4223edc53d8d4223ede43d8d42456dd43d8d4201cfd72d
  | 42 => 0xe70d9543004fd70d95432667f50d9543024ff76595432667c655954349dbf74595434addf73595432879c4359543005ef725954325dec72595434a4ff75595430067f755954349cff7459543006bf7459543284ff7359543006df7359543004ff7259543006ef7259543004ef725954300cfe725954300cfc7259543006ec725954300cec7259543004ff7159543004fc7159543004ff7059543004fc705954300cfe76d894341f9c43d894325eee62d8943024fe75d8943004fd75d8943024fc75d8943014fd74d894301cfd73d8943006ef52d894325eec52d894325eee42d894325eee32d8943004fe71d8943004fd71d894325eec21d8943004fe70d8943004fd70d894325eef20d89430057f75589432657c755894323f9c435894325eec62589433979c43d8543024fe75d8543004fd75d8543024fc75d8543014fd74d8543396bd74d854301cfd73d85433bedd73d85433bedf43d8543396be43d8543396bc43d8543396dc43d85433969c43d854300cfe72d8543004fd72d854300cfc72d85433bef641d85433bebc41d8543396f631d8543396dc31d8543004fe70d8543004fd70d85433bebf40d8543396df30d85431ef9c4398543006f761985430057f75585432657c75585431d79c4358543005ef725854325dec7258543005fb7058543005f8705854337f9c4318543006f56118543024fe7518543004fd7518543024fc7518543014fd741854301cfd731854300cfe7218543004fd721854300cfc72185433d6f5411854337ef53118543004fe7018543004fd70185432d79c43d8143024fe75d8143004fd75d8143024fc75d8143014fd74d814301cfd73d814300cfe72d8143004fd72d814300cfc72d8143004fe71d8143004fd71d8143306fa40d81432d6fa30d81432657e75981430057d759814312f9c439814325dee7298143005ed7298143006fb60981431179c43581432bf9c4318143006f96018143024fe7518143004fd7518143024fc7518143014fd74181432bebd741814301cfd73181432fedd73181432fedf43181432bebe43181432bebc43181432bedc43181432be9c431814300cfe7218143004fd721814300cfc7218143004fe7118143004fd71181432febc41181432bedc31181432febf40181432fef940181432bedf30181432bef9301814301cfe76d9152256be64d915245f6c52d915200cfd75d9152256be54d9152496bd54d9152014fe73d9152004fd73d9152014fc73d9152006be43d9152256bc43d9152024fd72d915245ebf42d9152004fe71d9152004fd71d9152256bc41d9152004fe70d9152004fd70d9152256bf40d9152256bc6459152005df735915224ddc735915248def725915227f6c5259152014fe76d8d5224ede63d8d5242f6c52d8d5200cfd75d8d5201cfe74d8d52004fd74d8d52
  | 43 => 0x8554006f76198554006f5611855401cfd7518554024fd7418554014fe7318554004fd7318554014fc731855400cfe7218554004fd721855400cfc7218554406f551185543aef54118554004fe7018554004fd701855401cfd75d8154024fd74d8154014fe73d8154004fd73d8154014fc73d815400cfe72d8154004fd72d815400cfc72d8154004fe71d8154004fd71d8154336fa50d815430efa40d8154006fb6098154005df7358154285dc7358154005ef725815427dec7258154005f77158154005f47158154006f9601815401cfd7518154024fd7418154014fe7318154004fd7318154014fc731815400cfe7218154004fd721815400cfc7218154004fe7118154004fd7118154346f950181542eef9401815401cfe76d9153276be64d9153014fd75d9153276be54d91534c6bd54d9153024fd73d915349ebf43d915300cfe72d9153004fd72d915300cfc72d9153006be42d9153276bc42d9153004fe71d9153004fd71d9153276bf41d9153004fe70d9153004fd70d9153276bc40d9153276bc64591534bddf7359153005ef725915326dec725915300cfe76d895326eee62d8953014fd75d895301cfe74d8953004fd74d895301cfc74d8953024fd73d895326eee52d8953006ef42d895326eec42d895326eee32d8953004fe71d8953004fd71d895326eef21d8953004fe70d8953004fd70d895326eec20d8953005bf7458953275bc745895326eec6258953014fd75d855301cfe74d8553004fd74d855301cfc74d8553024fd73d855300cfe72d8553004fd72d855300cfc72d85533e6f651d855339ef631d8553004fe70d8553004fd70d8553275be7498553005bd749855326dee7298553005ed7298553006f76198553006f56118553014fd751855301cfe7418553004fd741855301cfc7418553024fd731855300cfe7218553004fd721855300cfc72185533fef55118553386f53118553004fe7018553004fd7018553014fd75d815301cfe74d8153004fd74d815301cfc74d8153024fd73d815300cfe72d8153004fd72d815300cfc72d8153004fe71d8153004fd71d815332efa50d81532defa30d8153006fb6098153005bf7458153275bc7458153005ef725815326dec7258153005f77158153005f47158153006f96018153014fd751815301cfe7418153004fd741815301cfc7418153024fd731815300cfe7218153004fd721815300cfc7218153004fe7118153004fd711815333ef950181532c6f93018153024fe76d95432667e65d95434a79c43d9543284fd75d9543014ff74d9543014fd74d95434b67f54d95434b67d54d954301cff73d954301cfd73d95434a67f53d95434a67d53d954300cfe72d9543004fd72d954300cfc72d95430067e52d95432667c52d9543004fe71d9543004fd71d95432667c51d9543004f
  | 44 => 0x8000401000000070004003000c0040000006001400500000080010000005400d00080000048002000c00a0000021000800a002c01f00000000010001006001300240390008000000401e000400a00340000000002001801d000000100180000038001001000300040000004002002800200040090000010000001e007c003000c000000000f013c000000c00000e8007014800a000c003002c0090090002013c000000001700180010000002005c00500140090004002001800100d0000000c0080000000001c00800180310000004008803e00000020050014000400500000000000003000000100080130018003000400a001c016000000200080050124004000002400000170000056001c00000000070000001001001a006c000000400800300000010001000c00c002c018001c04f00380130010003004400000000000014011000402e0034007004400100080030004007009804e000000e015400000000050034000001c045002c00b00000000004002009405d001c00100240010080017004c0520008003001000d00d0021005400000e402b004800100040000008000000c0010030004000401c000c0000008002001000000000000030001007c01d0008012000c000003c0000000015021c00000980050008002001400200040000000005002c00f001c0250000001009405c000c00b00100070048009000c000003400200240000000001005400500040030048000005800000240090050005000800900440020004007001800400000010058001002400d0008005004401b003001f008c03a000000000580000014000000000200140070004037001000b000c01000440020004005002c00000500000008004002c003001c00300100040004002002400f001c000002c000000000300740010014000000000600100000008008000001200440020004008001801c0008000014fe76d8d54286de63d8d5401cfd75d8d54024fd74d8d54286de53d8d54286de43d8d5400cfe72d8d54004fd72d8d5400cfc72d8d54006de32d8d54286dc32d8d54004fe71d8d54004fd71d8d54286df31d8d54004fe70d8d54004fd70d8d54286dc30d8d54286dc6358d54005ef7258d5427dec7258d5400cfe76d895427eee62d895401cfd75d8954024fd74d8954014fe73d8954004fd73d8954014fc73d895427eee52d895427eee42d8954006ef32d895427eec32d8954004fe71d8954004fd71d895427eef21d8954004fe70d8954004fd70d895427eec20d8954005df7358954285dc735895427eec625895401cfd75d8554024fd74d8554014fe73d8554004fd73d8554014fc73d855400cfe72d8554004fd72d855400cfc72d85543eef651d85543c6f641d8554004fe70d8554004fd70d8554285de7398554005dd739855427dee7298554005ed729
  | 45 => 0xc013006800000180000048006004000100040000000000011c007003c000000800d000000000000120000011002800400ac001003400000f0008000400600100000004011002c00700240010024000000000a003000600100170004001002c0000078002004c0000000000008800300040060000001004000000440010008014001000200040000130004000000000000030004000000000d00000050004039003800200000000004000001000b00300430014003008c01000340150000016006c00100540010010002000400300440010004001002c02f001c001002400600000030008006003800e003800b0010000000400000780000018036002800100240000004001003c00100600010010004011000b003000c00100050000005001800000200000014001000c00100000020070001000001a000800900000030000002005c00b003000a000000f0014002002001100100010030001000000e00000240004001000000000000000014000004c011001400a005c004002c00600180020028017001c0010024008000000100180060058000000c0060040004000c001002000c00140000000004004c0060014003000000500340020004056000000600c4043006800c000001e00340020034048003800a0260002001402c00080100014003000000100140030044008000001f000c00000000040038000000400b00000130018008000c0030008013006800000480000004004000c005002c01100300250000000002800d0008011000c002003000600300010030000001000200000020000002000000a001c001005000a00e400000080090000007002c003002400000100110038002000000d00040040000004000000a00000020000004000c0000000008005800400280060024003000000200180000018013000c0010008011001800f000c000000000101d0013000c001002800100040070038005003c0030018000000c000000c0050010010000001a000c001001401b00c400000d400400000050014003000c008001400e0000000000400b0000000002c001002800e0008010001001100040080010002003800400240090000002000c00201680040018014001c00c0000007000c0150070003000c004004803a000800700000000000000003c0000020017000c004000c00000000310020006009c00b000c00f0000001001000000000050008007002000d0000027000401900640000004022001000000440020070000000800000000200014007003c0010000009000000100380000058003005c00c002802c00100120024005005c0200004003011800f000000700100030034002000001600100010014000000c0100000006001800400080010094001004000000000210054005001000000080000004000000000700e4005000000
  | 46 => 0x4001000000c0008002000001e000001f00380070050001000c00600040000000000001c000000001f00040030000037003c0040000002002400c0094003000400d0000002000000200080000010003002c008003c0060008002002000400000000000033000000300080100004007000c0000010013000400c0000000001c00000000000084004000803b0000000000c005001000200dc002002c033000c00a00000010000000004800300580000004000002c019000400b0018001003c0030038006001802b0008002002c00b00140000020007000c00000a4002004002f000000c00600040000008004000500040000008001001c01100a0007000402a0018000000c00c003400d01440020014002000c0110010000000c003001c007006c0000000006000800000240020000006003800f000400300040110000005001001b000c005000400a005c0010000004000400000080080040002004800601b4002006400900080090018000001800000040020004004000000e00140100028025000800700500180000002000400000280000004006001000a0070016000400100cc00000100000008025004800a00000a0001c011000800e000000a002c001000c0020054008000400c006007d000000c003800300080040008005000000000000070008000001c0040000000001400000000270010005000401c0004003000c009000c00700480000008002000800e000400c0054016000001b001000f000400f000000a00300040020000001c01d002c003000803e001000400040020038006003c004004c004001801c000000000340000050013006c00000000110028001000c008003c05000380060004001007c00b0008004001c000000803600b8000002800b000c0060010000002800a00000040008001005000000080030004025000001900040060020017000000500040080074000000c019007c0090040025000c0000054005001800500a801100040140014000006c0160008010000c0060000007000800400180000048002000000400000070018001000001400f400200340040000005002c000008c0030000009000c00d0000002013c0000068007006401500500000000006000000b00080d500000010000000000400900140110040007000000900040010008004005400000040030018000003c006000400d00040020020004002001a0038000008000f004c00200000010000000002000d0060003002c009000c00300140030000000000c005000000200200000034005000c0030064006000c0070030004002800700c8000001c00f0000003009800900ac0020050001001800b0004003001001b002c001004c00800200010018001001800800000000054003001800b000000100080000008000000c00b0030005004400000
  | 47 => 0x4c00d00f0004006400000100000004000000800b000004e00600050054003000c00b003400000140010008024001000100100040080002007c00b001401400c80050010015002c02300740000014001002c00000b80100000000000001c00280020000002000c003002c00c003800000100000004000000c00400000010010000003400b0088007000c0080004001001800000200000000000000400200000040024018000000500000090018060002001a00000030000004000400000100020058000013c00000000010004000001c007002001d0008001005800600000010034003000c0030044002006800200000010000004000c001000400400bc0020020018004000000940230064003000400e0000002005c00e0000008000c00c00140020024005005000000200030018000002c00d0018002004802d000000400000080038000000000000080020024000000001100000100000006005400000200010014001000c0040020007000c003000002f00bc028001000200040000004000007c00a002c03e009401c0000001000000a000c02000000010000015000000a0008002001000e002400600e40000000000000c009007800200000050044026011000a0004000002c00100000010038002004c00500380040000006001400e0070008000c00d000400d008800b000000900080000034002000c00d007801b005000f00000000074003000003e0024025000400000100040044002000c00700a400c000000d0004000005c00200080020008015000000300040040000022009400900000010014005001004e00240030014005002801100000010000001001c01e0004005000800c0044003001400000000060150002002c008013c000002002200a400c000000c0004000004801f00180000004004000400300b402100000070024001000000800540100000004004c024004001600680060030002000002d000402b000c002000000000c803e001c003002801d00380030014000000000200ac0040054004003c01000440060004000000000600200010000001007000f004c00900180010010002000400000040000004003005800300180000000004000c000005c001000002800700000068002000c002000c000002c00200100060000026009400b0058004001800a00000000000001001c0010000006000001500180030034009001401a010c0020024001000000300000020020008000c00a000c001000400f003c00900000000008001007400000180010020099000400000080020008021005c0000048007000c00600f0062000c00300080000004000004c0000030001013401f00040000000011000c0000000003002c00300480000060000000c00200180030054018000000000800770014003000c00b0040001000000b00200
  | 48 => 0x7d49cd0ffa506934e5792a5263311aa78eabd253900000a20946149b438e8c05f8d0335385989a9407c1e60228a2deabe1812667328a9de87a67d912c28cc369092e2edaa559dc21260e7c6c9ac2674e0a1a00000000001b8e0002838de10000ea992d06e790e20001f4e416b8d407ca4f8bc80000cd629f0000000073f23b876c27f87f908b4366b8089e422426d939fa76382323e100007ff8000e0909f011f0b5c7ac9aeab848000c281f0600010c40130000a132ea40001c62c87000000000004b700001cf04303288000000000055403e80742d3e000a64a9a30b0e0001460b268000b7e00005ba80003e01140cc3b782e9b000093813f05bd9af819b1f72000130cae93ad60002b147b4137c97a248400015180000424ab70e2a6469de83e7322cc2c15c4512139e8979e0a5a6000010e324225cacb67e01702000336e0001846139b09c89717966ba1410203af00a3482487a5b37860b25dca95b59216caef870c993867a9946000000016380000000542c108006002c02600200040048007001c018000001b002c003001c0060048022001c00a0000000007000b0030000003400300000000004000001800000080020000002001c0010000012000001300500010000000000400000000010028000003800000100210000001000400a00180010030000002c000000c000002000f000400f001c00400040010010000000c0100008000000004f000800a000c00600280000028001012800000000000008001000803a000c04d003c0070074005000000d00b800d000800300b4004001000600080010028009001c0070000012000400a000000000e8046000c062003c00100200010004003002800500000170004004002c001000000100300030018006000004e00040010044002001c0010008000000c023001801e00cc009001000a004400a00100020004005002c00000000010000001001800100240050000022000c000005400b000400000040000018002001000b002400100000060000000001800500b400100200010004001000c00200180090000000000c00d0118004000400d00380060000005000c0010008001000000e00340060004000002800b00000050008000000000900000030020007002c009000800000180520074007000c000000c00800140060004003009800e000c00100c0000000400100040050000000000c0070010003000000e009000d001800f0024000000000700fc00300a002e0000000002800c000002200a800a003800b01d8014002c0000054004000400900d8016003000300700000008000000001300400030000008000000100280000018000000c02500300020104004004c008003800500000010004004000400900200030000005000000300000080010001002c00b00580010038000004400d0
  | 49 => 0x3ef8000b6780001690000d65030600020dabef0000052984000000000002fc4a418da00d609b20c59b0400034460002f7e0342d0810199c293e80009e0800000037ac000000000297300369fb6000121ebfc80003b080000000000000000025ba0a8171a492000312c000134600000000002216089314a9872a0e97c8000c80224a02d80947bf26fa000000026c2c92cb4a5fa01933ac56a10be45881bc0001feec49800045d065aeb8ba50000327ca7db4d23813ace4a6b6c8650b3ba48fa2fc4fb126217c04742250000d5e0d08981b5e29599dd207f308a6d1abf0b32357200033fcaf59f2c83a316c0002644097800050a8f52b8db2128c5908e1198eec00005f6b2093b6d92ada825d2b08a013b0c82ca9544142d8a0001a421ea8000330998ed38800023bb908b92b68eb24217800039486e5b0461c00000cd203848ae914c92a1c1ec55000097324aa7321a2a00035f03bd85945890000000083c13700000000000bed010cd3d0ca46900000a6c0000bb2b84c8ee87b492800f2819b1ce0001f3a57494a8ebe02be419894a122b5d826b35e63b3b3ec612000049b88407b60a108cf96ca4fd0ad67211d127e3a2622abb98c50b8d1e98a31b6303a18aa86182a7e7ba2c11e3a3610c8d787ec0954737b0aaab7a8f658eb03c6b9376a08ab482519152636b1fbe86725c659ca652bd08d72ab3924c6eb977448a00009f30ae27482ffc000177cb6a92da40d99669921ea8cbf895ac63315ed88354824b308033dab922af2d12e8510547bc27a6726991692f338c8d7325c71c04b490dab0047120f83c192aa000168a3471a845a8b24a0001470def3adcd12800000015b0de5b70ea26b8ac981000000038a4ce900008c9064000015323d99680d098000404b264a73ab6a9c600000d59b0aa1a971e69b87702318bb000035588aa800048c10200000000000000012500367172a9a0003188b0a0a1c000000000000009a38f24535b150748a8807cc3036d9a864c5e78000ccc275ab0aa9f4dfb80009068000c5f0000000175c4ce12ce4581e7e6a8b7c0c799a3cd66af3e81d28f800000005ea3370be20000b979bfc000093811011f8000000000017504a323f60e800001a00000ad2a92e10003ced218fe6110b47a500176cd6a0b0a08e0000000000059d800044d800000019ae00029e400000000003a800002482c0130dc7c0921cb811f4ad5d019ad678000b0e85b80063858000096000024d88ad2c7ce3d1bdc6d5a028a492ca60002ac6000230a8db94b0e0b2e269c31368c4300ac218000021b00009301cc4a71a310d3583382f39a6846593aa9c39b441e22a6a523af3a1fa1438a290a182bd16b0768b3d0ec59a48ba0045811ead2e04c156e00017fabb00806e60a6ba94a80009f908701b989e8000313c61aa1f40f911d02dba35083aa
  | 50 => 0xa1e410980000001072c9b04f05b080000002aa80000000d2a00008af949612721587372fa4000170c6e51562000376c6aea9ece0c00000000b8a1bf91ec00023882c080003d20000cc42800537aa344f63666e5f20ec0000be82a908d0b482a94dec38a80f4a8e6cce8cd2c76b3d892000007563648bec80000000586e402d748aa31cc00019364c4000000006ac79a2e086ac1692d4fb82a0002fd653a01ea0000c04b1ca4400002ec4e81b942a21b0967fd000095b9be052b0aa63a280000003a823f5b34c5bb00006ef1108e36972812ab62e31b2f5000016ac0612682250b58e00021f601a00000001ece000092a00000006078000000334a9d82c4ae1f80000000c06000015a0001094bb380001dda39a4c22ad80002cd4b600df877e87ee6da22a691f21c80000000000015c71106a236f15b4ceb802a1d1a90ebeaaafa1539a606ac800034fb04400000005c92d44db2a8364e1273a0172466978aaba613896a9b504346e1a3001c11d9a0832ff4135296c0002d566ca88e65f68d8e5d115ee4011d8294c29082a7083414f9a000b921d61828db4e8d08ae5f63b140000000394286e0000000580000011f90960dc0000016935ee0186c8a54254c9e5000084d00000d7a7fcc88b40016c0df4b358000b04a0222b4ad765cb8000d859f28983225852700002ff26c00ab8c9acef9290343102800021eadc909ea00024e40002f9aa250a9a5cd02007ba1a2c5d6b6808920c52e5ab8c2147acd29070ed000000005fc9be484400004341a7080d80009c1a60037ab0f42f23168d5f80000000000657000022f8000000000000000002fe80000002a32ae21b6a2be000000017fc4ac045ed52807632d2ea0553288e000301e7648a625a18e6a000166a0001e804bfa5ae62c12324fb85303572f367760af23d5242c27ca622c5d2ba23339b749be32347deb5642171fba2ca01d25810000c189b62ad5800075c3028000094ea4100003a7a7dc1f92f5a73919b225fad6c7619f2e079000000008f881230100453a769a401ac3c1055c70d157c0002bb0bd125005a9b45e00000009a4800000018a00001c86857800000005040001b54a3223ca0cb1490cb70684d6db4ca9269506206117ee22aa062c998f4982824ae451b8a0b41990d391248de40000e3b9454000000045529260001442d7da446a4f0f6e0002902e7112b82b6a3fe2e384f60000be2b0230ac95d187e8940ef498e9168bb7a4ca7e2360ae8fb556c6a0330dcf085a003a54600027b800006d82c890746cbb4c0af6800097903622b12f227be918225c212a57a1500000000033fa49e0a52426140000023702c4000378cb2b0000c9ca2e80001a465551956578b0a689f852c00026c2474a2e01892b727570650379a754859b7483092a300003056e8700008a406040308000a80b2bc
  | 51 => 0x658dacf00002e844ed0968db515bc3250000cd080000000000be2b5aa00026320db2ba0829b20c47622fe0cd10a28dd914247733f60003a12e650000a1f80008468ba878099d4ce0172c0000de8dba998c00039ec28d25f467d2f2c104ae9071a1d624b032a0d470198c7e8e1a3330244b5b9986e361d72d680958162388e5f0804079d03a28ca818ce418662afcaf8e0de1c3840f8ef8e5584c616281b69c68e1840e086a15b1ec232d9242de829724461ea0813a9d437c9bf489334889299b3201231f294619b81d52c680a028c2944ada01291660c05a958a7812d2b4e2778e6405fe9a893e41d380008beb5ec0c63364b2208bc2e9213aa8da16c4d6290c0001db63cf15380278000d49000057694848fa285443c00001c18afc0000000ba28d42000074472ca9dab6ca5f6906273c12100008e726a40002792c41800044f800050fb0cc96f8000e9fb800a37b220c53000047ca5d01c08f0c1760000dd680000900b2400000000f7a3e4ab01d50dff800033813dcc4e1222000195258fa79800021da348b504431a254a68afd03af9fc41de00002bb8000a6f8fc09659fae0002a22b9d139a0000d4410d8000000000032a800000010245a31b362e49a9034280005c9a588c3da42837b21b81e29658a128816c2ca84e8dd289800000b051c915a0000f8288403d40000000b010000bde00004bc299600002d6a0e800046a0000e2b94fe0000000c8d995058228400000000b960000180230c54d8b724de20c275eab0400022785632ae40000c66000170edc1876a30b8104321811c2f7b34657c274e00036aa946a59c3da2bee61d88e096da1ee39b2cb80003ab460cb41c3e321b24ce80007f4a23adf180001c38000cf88000cee23280000000a6a3598ea5943639e25062a0ab46d3b2f72996ab2acdcb202cc886ba3c9979ce1f2dea154af027e92348e0497c4a829046ca4978437e94808cb055e67498569902b1a32f17560c417a6b2702605912c2c6c62740d1e04a092511cc03814d8279adf03d92fec2a0381e0153076a3612263f7012843f24b6d2580bc78b03280788030d283ab2ce12efa200ab66bbc800000039f6000199a04a8bbaa7f0000dcf9c221d61da4b56b0e4000209e8040ed4b7a2184323a71c000275c76a04e486335fa3442852c09a448d88b0ae8bb871c5372696a7290cc01b383853285200002f2e00015480c30000d318c3cebbb5ee1d88408ea7911469b0a70da5a5b0954179a8dc9d6c29d1a86bab0d14849aa9ecb82f14a813074ea396140b9b6c28038000e5b0d58882025a0000000d0b800000009ae25e26eede71b4e8cd03fc83526ca99a21ca7d69bd20000742c9408f279209bc835957805d37a806c867000017de79c842035921360000ea45d19b78a68324ca3f80000448000b840d161721d0865d8000841
  | 52 => 0xe0c9ca5d88b8b25b166620a720e6931a2b11ad703369ef6d811cc602180002111b1a2429ef42f588eaa7624d4a9ea62a62600000e480006f129800c20a2a12e2a8e3b58f9a8f8a7649bf800000000242ab0e1000020de5ebaa76d101f6ce31144a3de1ee08a5b2769f639b6903366c2e10000954ac42699272add9829e34ca320b2f8ee0c3b28326ae2970812890e1bba2a0e7d1a243fb1ac03030000e3037fae61a3360000a0cdde8aaa190b6e454f80003a4145810307482629fb811894ead8c15141e380000002b6293a93f21ce266e11320ac993965cc62aed493f9a82aa72ed620490768d1b46e36fb0f0568142c30286eae14b672d70a82a0001264d0aa3c0d2f0b861bd3406b312784e8ba03800000009488000338807ed53b45c65b1620385057010eaee438d837c4f0b280a2b2f3c825a6ace959fbc00023426fe0dca14521684621d0a0000000365b52adf28000ce9800000000001ca0b580002098071a05255fa1ceaa919fc596ad4209e01b80000982a5f000000009de8b3800054f31140551c2c8a188da0003366438090071da94e0001ee40000000a3d17767a2a36a8140ae47a886926d61f3ce09970886f9d1edde035a2822c946a9ae40199245070d969a96e395a89eb6b6369a7e0000167c1aaafc085f800042c2a50c0b27bc1a52146bed99c6a34344878c15fa3dd2fba2e5a6bcc549cd68242ebaad6116cb329772a162000e3728da82ab600d2780006c30000a08906a2ad996463c80000001e540000000e0e937e00000000001cfae9000009d79a0875f9204ca7ba3215d80009dd964c20eb1e4c513a9c03f17ec5af98ca00005a8b1a8b1e05ea8b2706116a712000021d35fe1d4000000000007348d94a44a03a07b2f920001c0a2aa098cc0c2cce4351838998a01ca5810f42cc0000b16870a000200c637b9c245192129ec8000275000000015ea00039a60002a3e08a0ffcb0893040d080000001166d7cb4ace7580009d58c08478a6de52b800061f05ac0d3062eb7533fa00030c00000000000000000028f20000000bb4a2a213e86dc60328be7f03710405a32e2df000023380001c2000053823aab78b0982ad00001e036d0e52a70000007a25f28000534b494d8b367eb878e0c70ab1602a7934c0001e66c67800000000000000000bb09910db79810e171a0ed39800035a9590b0d33bc1efbb0400000000000000000163801c836edce229461925080000000e0589e04240b9ecad9bba2ff9b8c25013f6ce58452dea8000b11000061e165edb1a9c052db6640f6a91e2d92ad21780e4600000005e807c200029e800013c65d9000000027386bb1e1214d02b0d43050a51d978299e8000000061a7da28425eab5a2b793a4e2771e1800a02023cc3a282f33214a1da58e1be9560653a8627af80000002220446928019a092
  | 53 => 0x26868a298d5418ec0d41fea56fa8688f38a3669425609458e1e2601b6c77a8eca715b0e893c2434000130eb8806b2cbc8598e0638b89fb88fe0b69f542ee38fe2a3a5cee2231808540000a031b241a2800070526aae03b46c80f8cc80002212ce08000b539920c10197e9720000bd20ba60780dc4606a2f2dd4b4f85cd8e480000000b1580003f499ee0ef96ee8228000cc629406f680008b924b4de6246879e03c8563adf4b130172a6931ee2e51b109389bb8d91a8bce7f99be11c8cfae191b840d20daa71b019e0cfabfa000051c3db258a0002e8679005b68da118c48229dc7f22f66c4bb6bae1e0000000065ca14151ac5180001b3883e83c80a82b3394c82e8c8ac1837b80002238479a304c20800000000aa79732e48420f3e0392ee61c62fdcb8fba1aca90000c12281ad45357a6eb12d62b9940e8709b48cb38e981da3860d58170a00021720000bc20302d98e1c12f800018623e28b487ba908c272ad84964abc200027f4c9a00000002dc60000000000299a000164e0e0000000000ea00034a4000130a78c8f1a8131ca687992e8c2895e086da1a4ce29d2cb8334ee29d800060f0e3e45c1b9a9ac89ccb378000ddc97d65f31f9ad243580bd92d26452aeecde1900200000005410e8c518b77400000000000000667b03881fa3a43c637be0000d129d88000aeb197200000000000000e82800000018c80000000d83112e00026800001c7a8430000970a06092588ca0112f5e5e50000db81cf272395ecd3a03a4708205a9cb0a72cd78a5a68117c0dbb8cf2046804ae6721d4eb6226c59a0e06a48800000000007c1256200027080001d560002f807b18000433a2ac8c2129216f163400005444d800003a6b1d600038eabdb800018434e09e72f408079ef214b8e54d968b14547820ecda093ce97a0e64ca0490195ab1e2b4000015621304ad975ed9d31f693b3874270800064c212c000219862fba18850359072a34c84dbacd809c9c062531dd681f13921a626949c58e7e4f698bc7aab2e894734762c1a2749cf96aad9a38cccb9af0c2f1b9ac00800eeb578f9227004a214e0dceb73869ac4d283404faa2c0000956d9b922a5b69a5c240ba422593472d1a0d76d0686b04baa780c3581928e42078a28b5e40000e82000338edc62d0c032086e0000122b3f80006d714ee2af978665d10d22dd8000af9a4c42efb4fec9838d27d1a36600000000fd3832e611b88d7d14fcd10800078001dc687a0a4aeca92075211a2df3aeb2b7e808c0d01a34179108415a00000000d740000d5200000000003af6c46800000007ec3300e64000000000000006aa9696d5f3ae0000092eb3191721cb0b54d28b2c2d3137166431b52df62f6000001cc29a9cea00000008bda2c000022ec7130000da1a88c47c0e00000000000011c0af8825400004188d
  | 54 => 0xc383f22cf809c000398a1d800005950000c1ba1bcaeb8dc6a4ca3928508000510076c39682e0d0d80007830aba0600000da12c5e41e19cc55106bed8e09c4677b04e2938000a0a37e465533e6586b8b6e5d0b401778c1465eaa16bbf24da8222be008d06c05ad1e7a1ef00007c92fe07610db225b1c9024c26e46620c1e81a9db8c760e709528000c2db3e800034ae444817e0ae8000eba104c000119eaa1a1a000000006e89f606c8aa8a75d3aead110210dd0ab36801b4320001f407b137ec7a9000022a83f03d09f6acb12cdae0fa1a8bba8000e2f80000002cf445391d46b7b9704c680004db2c80cf2883663536c455283b061a371a1cd913821e000057d0000832a7e2d950000cf0a916000365c64ba6d2ba337a6bdf000004900004bb8d8acdf36dc00017a25ff800800000001bc23f49a60000e4680008622fc67a232980000000353800069f8b52617b0f2c478b3600000005bc80000ef13a800021ec00024c8dc32f32af0232629430c200012de16804bee5fadd63f20000264003ebee150e7f419982c10e4e40c8faa168909aac4a61205238500b034f2858b7221dca9ee8e28b3472f0fac18a80008810000a082b5caa02f7a01eba2030c21209c786aee2626dc3ca8000033800054b266c00032b290135b2088392c000324e2db145ce7f039e65bb0584ec2a3aaa316c4e98b40a1e4a9f888f02221e317d4024ad3caf2841c75d871a6fa89945d89caa575a3a2db020fa823195eaa837c86a78cbe31aa14a8e19288608b68c137b1a67812ac4e2988003fa9cba254b854accaa70c783002d2ea8c03e928fc4488f70000279aca192e4b7fb7e6b0e057400000008f1000000000009e280000000000dd38d9eca981e600033047e0a89c6a38a0eb46a77c0b729ac3ea140a933afd86af95deacd2e880000164c0a8c686d81e6a1fc800044800006dc00000000c968f418e400032d6292b658c37a3328d6143056533c07501c5410506b66abab5e1cf88e895aa398000000000031ec1d78000d13a3d455e800000021441fd90b67a51f5e45f36b8d5ab4d43bb8aa297500007599ad8e9baf82c6720cec839cd0529000056e8000000000048f00005388fc48df8a32eb48d2800034b20002726363213e000000000000005320c02a31b408e6382c8085800085a99a4afda040a9100002a82616055aae8000194c3da9e0800024548b19d24ae9800020200008458ee882bba4c2e8bafc38cb97a4cd89a834aa0ee346a4c667400000000000000283e7c503d69d1a7580000e34cc31c42000222e300366210f26da09ba7ae6cf9a0caa408848e033d4b3c89180482d8e01f14d420885628c18000dfdb81ce480000cce35a6000103a000038e50d1f1a58ba3b08ef26182bdb78800006e8269a5a0377253a9d434aa29200004e59c0c8e09f9ce7188
  | 55 => 0x2e2347c000000000002a6bc384b000015964ab0000cc0a252a3b8000514b6286b4877adf796ba011a5c083915929cc94bc9e8a536adf8000d6f800003711b2977b392ccc9060b2301a212218ac4d2368828a28d6e809216dc780de0002f34e218b60eac0000dddb4f006fb0d0c6e207a5d800b84f004b2d65b054be88c8c6398000384a2ae2160000a5bb10e00016a0000000002e8000e748a042f90eaec840b00357b884529b51899e2056818a52e6e70dfcb9700003b00000ce78000000174004780004f5000064a823a6b8a0840001fb219ca18627b000074b85c452e8c543f786a6d6d26340002d5800017dcb170000572051a738a67c000240a4a1299e10a9e1a000000056d99ba37b95ca68e2c8a4218d6678802f6b2a39f076f329c4eb28464473148ade32f83b724e84e509085a390488281fd870c138803d1a5689a8196152391034b39d8c6d1aa8af509d202889a47e81dfe04386fc5be1cc0df88614c81aabebe591a065c1c949aa09f491c3a9404417e29f031c23ef0ff8dbd2a3cc6196ae340351653080004148d680001e104cd1850d3d83eca53074c93f272e95f85ea9dd0b985d305d000019a227400000002db487607ceb1d369400000002de000057630d2dbca2887679eac584000081d80000001fda23905be79900004ef03cc46c00007a70000d740c1a4c08daeda800004208cd0e663500ae6a7b6ca084461f4ba260000a920002624905048646127a0a0c000080b31120003530ccd08827db9bbeb419d28a0928ba8fc8bf21f18f00165992cb589f741b132d047a960cce1ad2a624900eb9880004669df60000000000041a0000a90c4e93de28fa6146e9b2fa00e80007e12f8c40f00004ad27e881c96944d9088a4738ad401d0be6e0ba92a7f2a09aaaa9f50d332bdc3cb35863b902ee3a00000e5a00000f12c54c9003ba8f6b5222ef28a86529f22ca40bf018cbafa8600360a9bb28ca518646e9f243072808482f2906800000009c12efe35e834a7ce34ea000289200009a24dd1cb80002f2a4a0af76a6e850628e0000bb88d867d884ca0002cea0002bcc51a0cc6eaf22c8a979ad0838800076ba3dc7a984f4d268000a9c925e6c7a53c7a321aee23097c00018947ea8a6c91e95f8e110000276800086eab1646e88f6a2229bcc3eb3f007da21889b805050a1890395ad00be131fc00003544ecb1224c02ff0bd2b9ee9a2a34a9ea85e8b3328b02f611246930cd66fb26866c530123568b4e96d09ce658115643a828266a05c0d5689d6c5f800045e80000001a360001996156800000000002e300000002cb239eb07e9dc800000023d61590dde4f10686000000000033c458b336a00001b41382a2eb0fb5422d2b7941169a7c000361e68a285a7ac1a1a8190000abc12cc4af1a66730b94e48b1abc28ba6b81172ab27
  | 56 => 0x6df0262a52217412f22b6c0b85cad86ad8c000248e03483140002dacbe410dc7b29ddcad325346c4ad02370b42005807ae0001e261e505e21338286670000000f1da650324b2c240000eb10b44db499f0cdd019c522800027187228853b0a025b8727f500005023410c8f92d41d58d041b30290e40acc0a749e509408e76953b9b0bc723b279787b274f838c649908acfd00000f70000c4c9a4a0860ec4e0292c60f1ac6256223de19f248609734b0d0f25ba9ec0000a20a8b6955b75400005c220818709fc000040d228a000000079c350e5178000a38806a000102e4578da45538000d8c93a200001a819280000003a2265883fa9748070736a7860003128cbd13aeb059cae2c62092d511fec4521150c3bb936000208007f9934d339b3821283d0e189372b0298180001f18d870dfe2b184e2669a31c7878676b0f31900000eacb002bbed81a63ccd3800000009b400000000001b2815ab792c1aa44a0000f340000540c8e25d664f0846a5fa44233e257800017584a99ee2638860cce23aac77989e400016e67f1800091b3ac2bbc0c265cfa58cb52950c7160b563be920a7b4959e36d83eaeaeaa64d6903ee000000000020e06760d8258195aadcd37b6b1385ba0c900006888000d15b84e2858fd80001f0c00036bc0001f9873b84fe70a07825c52b50926227631ba6be94980007a120fc6f79d8c8ce394496f000000010c23101c5ab27988cb3f121847f145648816663310a58bad15a49c4124ac1a0b42ca680000000db8181821a4d69bb60000e164cc900a6ed00000000ca800031980002ac269c88ec556101e6e4a5a400000008448000ec206749ed2e0e751adc4a4b1a9230d800000022325799646cff8a20b85aa20afa80004d52532e1a291c00001d48270ee2316b39cabf27147ad33dc53e9586ead83b4df0b0e600002de00036ceaa9a9c267fb1c42c838ce82d1ffc42e8ec83b332529699f7c398952872d93d65f3800093d00001bc98f01c4146cc9e17e43f09902b8c89f6cbc3540e280b3894a00009bd089cdac0faed340eb26ad87c06bd8ac208fa8a04f8124609318f62e691f695690fa244baf24b9966c682832e2282cec3c48d30000082e20e27f20003730000063c000355e0000000717b89041035c8cf1b53678886d2766178055ca660ac62c702c408667718000c8a27d6480251edbe800034bb33c8f632fc0050e3a0b49b3a0608b8090f0000103990848d0a982909d9063a9a320b50296c003102601000000014da72006a40003a8a000249c82f16dc12580001d00000000291a00000000000000000000021d8000d0c30ea1910000a9d0000000179000020040003610b0b8bb21299bc2bf29c2e51f39807458000000171ca91b7a22fe21c4ac08000b6b99aa00037e00000000638198a6989e2e7140492000065e9500
  | 57 => 0x821c4d98000d55000027eae5a91800004f400000000000e5e0320a390000440a74877e1d1cc788000ae113fc00025ead3086e4623b2ac0000ab23550000000345846e11347b30000e253a3c9513764c1c9b5a7df8000000000073da34ee4a8000000000064a0f44447933ed732db60002a127fc00002660000bec044a14c8214a98800021080000000000000018e00000d6000000000000006cc0dcc6358ab00002cd0c1481900000d70b3e38f81952b7c6e8392ebc99a4ec822d94756ac6e668137627e00b2e9c8c7e7c28000743138237211101f2939895b0fd0a6410b47af2452e26955e651000077434beb748a4071f337e87f9eee2df95a2e62152aea2069e66c0a6400002ec00001da74117200000000de28a66eafaaf23ddb740477ad5c95f1afebbd12520000c1c6a2b2eecf594445702c3264795408a9226818a297ab199e38136800000017e8d9d85d4c0528d4ce68000baf1276b99000049a1254b5f27bee25b3eee9123cc1fe8beadfd1be87b6af5cb4c8852cc6a4de8af113c5018bd29508f5a305980a733a8ceb1838dea028252a4c2b9834f07dee0a298c9b992f40d93216e578108c77b916166a7c210436a2481a37cc251bb0d37a25a70f8d2621581facb31fdeadd050cd97b3d213412b2e99ad6481b03024f281441f89a1234e0f2204ba4102c485667c4801ec5700588488000e39a7ce00000003821f420002cb0c458000b3b9a9cce882f036e91ac0000dd80a7125891ca6e23491fdc0002b8084f22cc7dc10a6773246a8efafe2149245a0000000cb7832a9cdba780548000b38ae346080000000304ac23100800000003aa9de000035f8b6f0000000000000030500000000d0480003e18000e6a855696b0000123b5ea00018280000a067cd9be6c6f082a73b2ee8d6eaf703f197f8c4c16122303254a2d00003b61a5804029e66018f4e92b892233a82660df800090839924c5a9cc10ba5f04e1b124483898ecf308723e52dde520963086380008679798000233a000189e0001e8e1b5000000000001550cd8e28838813f1ace31337605c59816d90000007123ec000000094839220000f466e0a192ac8255eae7169e00000009d4b7d6ec0b070a179a546f3abe8e9900a46ab2766a3b293ab93a98ae31ab7a000278cbc68a60da61236de932886880000d7506084590f90cd81b081e4000000000000001dd4b8ba8c472b159816000000002fd200000006b52b4800000008b10fe29359e345fa8c567960082a963660ded00005ba1a98000000029e00003af31562a51f2aad03a084a614a281c00001fc245c00023940002d1c000272287811da30b0000000000042a000005d8000a3e80000000eb43528bf474192d84bea31e03ea60205e1a52673a17ce49952232c090cbd1b612a571df45c0014cdbf0b4627239e234ead9c
  | 58 => 0x821fab0ab501022c1f18a83688e42a5aa7fa1e12c7ac1e016c6f2ba162f4330a47b910006ba396b5c84ba5b416421ceb8825130ec659415300bca3d2be52d901bda3b67c200ece6a02f856ca22a7499ff60e430324c6288a51b8f9e4cb86b4e500774c190c461422bf43a994c4bcc04f2cf832be5ee21541580ea075e00001a087d6930a7ead4f36a6ac189be59207a8ce40276d75805668eb0c4000003400038f2bc4309a808363e00004aca9f3162397a46e0000aec0002f0a806133ccc80dc0cd00000a82000090e9766bc1800000021829f6b466c4a85aa69e0000ddf9e627d5b63a0000000000068cec1a76e4c4adee88095426e6088ea1203264601d4e0a108fadc990bcb4c22268d30b7410fb158781b5084e829b6dd588969428cfcb730060d5b85823192d46b4da6f033936d84e3947abe72e7009b208e31782427f59dece9531d466b1c66367300c8c6a63813a3ada105827c3aa2e1a1140bdc61bb36c03a2a78000188a00007987fe98b20002ca426483e615ea594a5a042c4282654a86957004d0000000386a000027a00000006258000be800000000000a29800000022b20000916000035cae423604901bfe71831700002fa8a2580004d8b60e5698000000171ae0f13440c780004caad6033c36be000253e0000000960000000022460000000000301a000000000019f80000c840ba0000c038000358b8c88c4ac060000456000259886592ae4410000000345400018861d680005009d520000000ab8b71c00029b40bd31c6dc5000000000009941b509a6b26679f320407b91c6d89b4b46861e4a95c0ede1fd382257c9a14a891e9849f2ecc56b9bf63201fe60cea04400021a60002200000056ec50301820b0fe84200000000220a92e80001cc9860dd7869c63a3736b68b2aa2419b668bc07ccb101ce84cc0fa02cf2a84d011bb29b58a30d2d912c144ba3850115dc8053aec39d06583298f2e90f8cd47ed2af4e8eba8699a91a66fc39286b30ad8672938c3c797c687890562ce8eb8b1d90ae77b8880382912ad0a319ad6f37dcbaaa82c59f98bad8092a88fbb4facc7b636a6705dab80144e6a59f8cc3e09b8b41322aa5d11324983262c60a05cbf330346368db09f119dcc32aa7e9189cf8d169e3c873123889596c668733de11b2ed004ca9926488f40a42b9de7e28f1663ba864209030a746859e1caad481b78ba08a3046e164a3fc26d8b0c5b5a1c049c04d605994f24e939c81011b7e3962dc8b47805e9882e6a39002b219ea40e7eb3a0cb398f8e93c8186081118a0699fce00037022a106520002a6883d984a90228ca0b32702eb1a05e00000000001202ae09e6c485320a4f39130caa2fe600015fc17b1c267e4a6c4000155a39739127d4a742b79a12e957148c2d3003211a800077c044e59583a800001b061d1296524
  | 59 => 0x1d6e74c8c2a0c487fe51aa1f233d15205a0aff8154217688a0000e6680000000000dd400000001f94d7731086bcb2840ed828c009800000000000fe2db000038b0d448a1e0001b720002938de00b5a8b696708ae137030638f024502a0000158491fbaf0291137a4a81198a0420cc3d88000b43a13245b8c905eeb59c6c1ad686f23afec080b507d604c4da0b44c5a102a2d078dd43a52e4626eb5689441912b9d9dc047226465bfb73ad4431ae2ed00a0baa2944df40344e2a8ca0d47a4a2802800057fb9be06218d0188277e98c19ec0d3ba4661e97f407d239e0000000acb000000030e2ad900000003708d008d06cac2148ae2a87c0000e4aa8300000b29bcc00000001278e2ed8a9f206808000014b7127c730cea17000079db9e40000000855943c000110654908325da2872bce079a89397b6491341845e072000001c8ccdaf161eb2456dc801682952dd800015641e82ebe0000000000363488787d038c0000e75059c9c28716000194800000000bf2ce05261ada24c800086b2e600003176c23aaec8890c3200002ce00012560000e28000100c00027acdcb27c8c7411cacb890e80000b2c42cb75800000007040c50e550000a3a00004e2800022900009490000e15997c7d214f01878000b03b76e13008880000000000000067d80005d5031a000000000000000000000a878000c169e82a27800019ab0bae0d80000002f4c000107066026f22ca8000000110cc322b260ae109c4068000cc91c928b29c98dab8000000341403fa1dcac9189c6bb86365b4a818d628000120020ad200cee3fc2e44ea6800024120c80c100004ef8c3e35b2b3c610a1284c98cde5e228ae8be00d8b5483aec8c38343cd8000e010df6d46a6a01d4884c725ba684438a12bf08fe023515b81a8002e219153abf3ac6cced2744713850e02d36ec000276a0002a5417333ce757b52867135e87c79c1ade7960a4bd891c2362e7875a070cc96ad4c86d29fa3ed000094b00006070dda84936e6b5faf58ba8b356b2116e400000000500c1200b092052ca05873d2a14e4e8fb27cfb96077f2264bdb1a6a0002674cc51e906ea11943ec2e92b4295c640a80000c718d8000352c03291b4051942260c2af6b2805fad24aab48b5b1046d289a04a936248f2115c4398c1050e9b2000010ca883b1be7e98d6eb8500ccdf1000085b9000732a4767d98c2098b37bae6b95763fda7cad6238422828f7e3a20c74abf808e0f803465f48fcc1f2010a1e798c6570a74ac0729360000000a240000a0f3aca5398090000000084080000001c1c5ef000000038ca3ee0000e340b1c000000039a00000000000a038000ba5b72e0000000e00a71200000008a10ae02b72914c7faffacc1866ee6eb87658720d08b08c76a6abab8e47355288fa1f0eb30e38226b17ac648dd6beb2bb
  | 60 => 0xde000102656280000002cb476b1446000000000007e600022e65fb80000002514102b0248d78fb67de15ce000000000036cc5f9ab2221780005c1994041f3398ac41e4499c94ce07a172a6b5b5b01a3b768637066008db5e0ccf9834000000031380005cca8568208f14169b1ca0002e82394ae1853300005318e86b3a167a08f2e48bd500008a7129462e2edca6200007cc8ef03e9ae228de862c7290000e770c625d20d84ab5098672889aabb8186c0001e5aec029d0621067ed1d386c4b2162a740aadab4921643a89c5242792860899b7ac2a295acaea7a8231337a8bd148849ea1e87670d80ba6000087480006f60126d1fb8fcc278000a870000a051210bca367cb948764a4619829b61ac295a1c4a00032cac24a5486a931b241b88c82852e8ec6c2a4809939f292f94a03c700008d9323ab6fa190000000000010300000000213affe24db52e00018c200022342010efc4b883c2d29a812000052a0000f1000000000000f0a00000003740000cdda3c643b0422b808fcee5919e67fc968885e860280c039c4d030b8d1800006cf0cb289cb87a9689efeb3093fe86a800000000000000c7840613d224e80000002844000125c7f08012d4d0f4a7f820fe000160e74024dc000000000029de616a3c2107a5380000e4cb21816e25780007001bd6aab048282897ac6051c3a00000002b3800083c39b232e35c40003a48c2113f80002094006b9ce3c80000c56b9668f9800000025a85af096229a00000002b0e0000000da78000c8cab6e000000000025e6d2380002f12fc8000242447a0084dba054ab03293ed0e8acad85248c0000b1a00000004c72aae3220000185983e0000c82000234088322d07620bd4e5725ee933000082180002143810b9ca582bbbb7b29baae2c4f22012c5aad341f12df62f007dcb828332d60889e3d6281c7a4945a8313b18c380a46630229a63f0000a4a0000cd52cfaad3977a82f94bec6537d21e9122489f2eb07e888b2cc20e026db90eea972b54762ba902262b6c00000003ad814e28897f600002e2e17b32a0001d341ed8000e7680622dc00008318000cbb00002ed993a1e1966e65e08b68ba8d50b620000a333a8c71a8000a548590c470b320561b2c15f2b52af60382bda94b429e8000000148626700009a7000099580006b289fe8e3964000026c600000000da81deeb9a44e00131ac53d30a4e5610fed2e19140002fbe8fc03d84c8b9347e59836e5ba6420dda9e26ddada465aa7ba3fb84d211136420002f7400000000000b5e000136a32b265897b2c52000080c000245e01380008ebb086e7e1db40000000000000000006c20002b1c6490000887009a49d0000470ba60000000002b8256c723a043a380006c03a52c17342c55716646d308101460c5cb66a768acc2ca29abae3ad6e1b020002ef600
  | 61 => 0x2c1b40b4581ce904aa385ad8630b8c1d424e408d228f0f0e941057e88c04ec3f294aa82d85f457519e48e837e8aa21be251e069685c13eadad3ac8d76aba818e8886705b8faa982e66e8410a4dd101183b9872e776a4ac8462910e432f0822a2ce400001c030e000010a0a0271d2db8addbaf49f985ce0af3ad000037f000006e21c981c20002f1800000e60848000ba50d9000039b4d4e9994db89556e83a2d25b31ba4c7a983a2da0000c5b8000d369d641b4039a0cf03b2baba6ce7683a70d5b1ec84e998b68429c6e771294a47e8516911229e42a8f7acb1a068b740000a6bad144a38f7c4390de4b940e6038896a425221382ba09848cf1088cea82ea4d0a7305090a00a59195ac690f3811a393e8d6a2405423b0e5b6085427f1cf02eb0eda91d26b664fa22c03d87e0c4fb656567257620699da32792f29669d4cbadb2742fbae062b219062c5aec8934b94625415cc95e8000ca51510362000000000009822e3c03e00002760000c63adc275835de6c3b732000120ce050c28126b2b40001dba0001d3a445b4dc92206ec7721d4485700005470000aa6224479ba63663f9858622126697e1e4ce2f37d47a7973a1322878a1b1ac8d570bec8b62bfca07815e09d17b45de26fc6a235fcd0f9d147b9a4ee3372e7a12ba61a6789ae0c1e9fccbf9099ac95a1c69e792ba072991cc31b2ea1b823a86bd39cae879c886818988505a6ecc36866652532b8551aa421759bf205c1272188941218e35d2e3d85fc3bc8ff4daa119c23f391ee08298e47f9c3cc2f80003bfa9ea6b71fe841629b8aa89eb8c3f156c1db82587c9b498e4f09e29b42f62ae5000049b127ee27b2267440d2000000004302e68000303a0202384ea61c9c207a30214438ec8fa90d84c196c0b72b7fc69e959aa89abc63ca2236000282e0f031d2da904ea2b798a4b5e1e0e1ae29784f9818abc1141e46183cab5407fc0002c1ed71b99e29f27fe0000796b261cfe0000000b062c1022b2f1eaf7a5841180000b1f9dca0be96f4a59a5d800005369f4110a5062314b050d0eaf2063ed1c15f65b51568ada00004c518260000c581a42d1846392becab9afcc7012c467e8e2ccca354c4f31d1898fa87a778950a9e39e9a1f6b31c00020340000730765b9e000004f82cbb2da41118d200025e0c50b700000348400000005d2b8e2b190f4ce1bab0c75aa50e04e90f6000182eba7b28e000327e0310910000395204e0000a69800031f216040191e00000270b4b17229930ff2b8a800000032c8418b69a58600000000892b87000025117c8791b7f2b16135600014b8eab9d2ad0912ec90c8000339b462000054c3d81566e12800020c173cd5c17b00000088ace8c7a378176a00000000001158a58a61e1862d54e1187b0000000038f0000000395000019e80002f86a6c9ab44e03a
  | 62 => 0x2ec6d42afa658c907add883685609aa06c70aea01080000fd8766c6a9ac408b16229f1a6a614e80003a133ea526847621f10b8e7a36ac1872a100e584d87b5af5666db8e472f94d0908a0c00b1904e73328dca7204eee46280882e122e7350a7e794a866324ac306a031f0da7141ca92b9048740102ae5ae38dca800065a226079584c2de3b2967ab8b90b9f2f12c4d86c6d58a370041990a7ad86783ee8ffe08c276c00008de85491443ce9d0e202b506e8a9b16479211ce969c048c3800000000000000000cb000000000000db5800004d9250709228000017d0c0f8712e680b6a68fb24864618f8a7f858c2deb27a238899600026260002610ab80000ec484cca96aa92388000000000002a3175271fb7f80000464486a0d23ba80009729b8000000000002acacfcaf9e5b21a8cc4600008fe013c000000000013247851d300001f444c8105e000278800031bada480c60000000bf500000003aa46fba884600a65c3a48fe4cc0311000038e0c17ab280000a8ac5e06a87fe000024a0000ba717a49f4ad3ad7016f08d528eaa09aabc01980007f8b394c480fd478a39761613618022a2d4997a4f61eea1fc7be07f81a217b26bc03a65db925a28e9e865b7a7703e5adf2bc91d9469107d840b1ce6000249067c8000c4282c201b98a6a2aa4a411224066cd20165e498fa0000000b23800090780001be09763a700006402e6c33b2c3664c9f9023c0b9c3cc947e0000000dc2ac48789260ed630c724072fdaa3c24b04a89bfa0000000d9e0000ae7bae409f8000900a72425e8000000129e00027a422431007b7a7ec8411e1cad10fa299f82d8508000023d00000001d7ca0098aee9d38d65ae374c87e2942075a024adc1c642a18c70b5ab5ac6112194ddf3520a612b8cdd28398b932a66aa0a0d8b9501d868c0366c7e322e711a5fe1dfb5ae71e11be0000000b9fa9003d700005c62fe800016fc37c390a0000d92dbe00007d300000000000ab9ab3ebda29982d9b52653030bce892d2877c825041905aec659628c9c0828289b5ce609024eb440000cd42bb4b908374000364c88897f02bc255849e367a0000000ea8a9c42b01c0800000000002a28000321ecb6000007e2bd09a219bca6534fc00000e290ba35241f80005aa0038d72abaa493aaccd05a3b40002cdc2beb866e7323acc7d001674d8e2678ab0d44379770391062667200bed08a14c61533128db001ce06906c31294327c000000a6180004b3840c2211263e23aa844eb6520a3b6feb8a0e2491615ac5b3829a4cb000012300007551192000234418d39d0b2f3a5c6f5293400006ca000340e000052286c0f022468000a058000505000040400001e72400d913576e6f3502c978648c9bae6e8c8b4529768f723d585f261c800000000000000000c91b184c3f8000297071e8
  | 63 => 0xaba9ae69d3123a62d0322b77242a3a583acdf302aa1b6990e000201a3b4aa4c0000000514393889c39a224f8000ca88394e4c2e9a4b297120000b08b068386ccb9a74e438000310b3c8db68ccab0088d66410d98bf787b8e248000aae2d7a779229291e0d4c46f092441702a872303e2527a02683d1f16008ba7a53e33b09131c8a43e12e08021f3437480000002f4e999a1de2a21ac6c13250c0c00a4c06e837ab0811907dd8caeae3978e2599502de6ad222a598c4000109881080000001128c539a10580b164b7000003d43218da2ab860000000b8900001f5117605405d2179957400000002eb8d60100b0b42978f5e000135039bab5ae2c8c480002bfe68b8bf600000005e300000002206aedb9623873a5849a9a9a3522b2e00013b8000155200022b000000000000c3a3c20454dc12c78207000067822dc9b20546aef0000603800000027de0002eb898bb32c54ba5aab3d89eed0d088cc029c02ad0861266d2dbaaf3af9896416e05d3aac85a42ab0866a59e6612aee74f1e3e28911f40459626b2e82a433a01a44eeb224899adda22eb1a003c34d836a332672c10c8e799d809a126cc0ffa3a6696b48c9ad279614f2670410abe446926f6cd8aff67aead66bb633e4436b932b2bb8badac80003181652785b2f6230b6f0deb864e664971000005ee628a8060a2988069d9dcecc5a00214a177ee6e335237892fc6ea9ec08152bba78d934a76c822e7e1ae56560364eb092bf8001b450a75a8706d798cea61871472797e03e637da87e9daab60b7ead51ba92205321a1df346a15e0d367d7026a15cba847bb389c55a9704b64a6640bf8b82585a3e06561b4224d2416d6129829ac335c720b35a4fa091e0ee25b258f2a000353924435b9964feb26a4c79e425a70724675b75c5ce0e0e72d39720509d4a09a33da5e2a02a5ac9ed43112a2a0040d340dc875c218bad47ea302250980a6c913344454a8e005f0a568450470308b63c80baad01af39c06171466704a3faa182100587b5321b5ba4a4f897bebebb6082570000cfe0000aad8c349fdb06ce9a80009ba2464b699a26703a5861770a6e22987eacb50734af139ea856a38c8a39ce00002554000206ecec9bc600025c48b88000710000076f800051d2d960c38d409a7800012db23c5d0a5724050ab8aa5b4640d4929c2d89dde2f6b80c614aad63ac272842496e2939b0d8dbdb1e805a98082949bd083722820000000399800079380000000000626a31800031dc685b2580002a4e00020465be8000068385ad94306659d14ec34611aeeaa8d7e28b00000002438bfa800042b00003ae8afe843ac1c0002dfc22c2caa01e29f21d2b848000248a7c4135c00001aaea8372800028b84e710f2ce8221a9b8087a62a904a847b48ad598baa326184c71c8d56267a5fc0261edc00023620cd8
  | 64 => 0xad800003f69512697800012a295e545964a35f374616d33a81838194233000073602b41409b90cedb49c99d8000000153461980000000000eb03770003214ec022d860819afa0ad967832ea356959203ca9b2feeb78317208211b6bd4886857414f6475b6700a4ac50e3a02ac4a283aac01821eace3a000e2a87439c8be0a902dec3518d02afb024680ca4d0e2d1352058aea66f038800003b10
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x87e8759520040110f90eb2a40080039a08165480100061fbaac89002000c3c7559120040018beeab1a4008003171d5634801000637baac49002000c6c75589200400b5d100b1240080038d59564c40100072ab2ac78802000ea56458b1004001d8ac6b1620080023d61e61840100263cbb4cb0802008c79765961004007972ed324200801f2e5d964840100166cbb4c70802006cd97658e1004001d32c8b1c20080073a5da628401002e74bb2c50802000e696558a10040011f30f30c20080121f217764401001c5e426ec88020028dc83dd910040031d905bb220080321f61b75440100061f326ea8802000c5e63dd510040018dcc5baa20080021fa1d65440100443e43aca8802000c3c7459510040018b8e6b2a20080031b1c9654401005c5ec36e88802000c3e65dd1100400187acbba220080032798f744401000657316e888020008be87591100400f1790eb2220080030fdd564440100061e3aac88802000c9c735911004001958e4b22200802a3761b73440100062f32ee68802000c5d65dcd100400193cc9b9a200800327593734401000667316e688020008de8758d100400d1b90eb1a200800317dd563440100062e3aac68802000c9f7458d1004001938e8b1a2008003331c9634401004c76c36e48802000c6e65dc910040018dacbb9220080032b993724401000656b26e48802000cce63dc9100400199ac7b9220080023ba1d624401002c7643ac48802000c6f7558910040018d8eab1220080032bdd16244010006563a2c48802000ccf735891004001998e6b1220080031de1776440100063a42eec8802000cb784dd9100400196909bb2200800335e0f76440100066a41eec8802000ce782dd910040019c905bb220080031dddb75440100063bbb0ea8802000c777699510040018eeecb2a20080032dddb74440100065bbb0e88802000d34751d1100400196eed32220080032ddd964440100071ab2ac88802000cd776dcd10040019aeec39a2008003551d473440100066bbb4c68802000cd77658d1004001caacab1a200800339ddb724401000673bb0e48802000da4741c91004001b88e6392200800339dda624401000673bb2c48802000ea5645891004001d8ac6b1220080031ee1776440100063c42eec8802000cbb84dd9100400197109bb2200800336e0f76440100066c41eec8802000ceb82dd910040019d105bb220080031eddb75440100063dbb0ea8802000c7b7699510040018f6ecb2a20080032eddb74440100065dbb0e88802000cbb769911004001976ecb22200800336ddb73440100066dbb0e68802000d98741cd10040019b6ed31a200800336dd963440100074cb22c68802000ceb76dc910040019d6ec39220080035a1d4724401000675bb4c48802000ceb765891004001cd2cab1220080063ea1e6144010
  | 1 => 0x2cbb82a4080033a58b70548100047cc30e0a902099d68521c152040090fd0b3b284080021f61676508100045ec24eca1020028de839d942040011bb073b284080023b60a76508100243f428eca10200087d851d942040051bd063b284080023760c765081000c5e43ac8a1020038ec87589420400196ac9b8a84080033958b71508100047ac30e2a10200487e859d932040010fb0b3b2640800e2fa12764c8100045ec24ec99020008dd839d932040011db053b264080121fa14764c8100043ec28ec99020038be841d9320400117b083b264080063721d634c8100147643ac49902000cd563dc532040019cac5b8a64080023d618714c81000637392cb2882000cae72592510400199ce4b1ca2080023be19729441017e3732ae52882000c6d655ca510400195cc8b94a2080032b59172944100066731ae52882000ccd635ca51040f71df0eb14a2080be3b61d62944100063cb2ae12882000c5e73596410400193ce6b24820800237e1973904100062f32ae72082000c5d655ce410406993cc8b9c820800327591739041000667312e720820778df8758e41040691bb0eb1c8208003339cd629041000666b9ac52082000cb9645c24104001c6882b2a820801ead20564504100075220ac4a082000c3e74596310400117f0cba462080030f995748c4100061eb2ae9188203ac9e635d2310400195cc4ba462081ca2fe1d648c4101d45ec3ac91882000c9e7458e310400193ae8b1c62080032b9d1628c41000656ba2c51882000cd9635c23104001ca862b2a620801ab5205634c4100076218ac4988200087f865d6210400187cc8bac42080031798d75884101fe37312eb108206e87f87596210407f0fb0eb2c42080030f9d564884100061ebaac91082000c5e7558e21040018baeab1c42080031b9d5628841000636baac51082000ce9625c22104001c76a0b24a00800396d41639401000735a82c52802000c75655c650040018d8e4b2aa0080032b1c9645401000666392c6a8020278ed86dc950040358dccbb92a0080031b597725401000657326e4a802000cad64dc9500400199cc7b92a0080033358f72540100047743ac4a8020058ec87589500400196ac8b8c8008003171cd65500100064e39ac8a0020228dd86dcd40040018bccbb9a80080031759773500100fe4f326e6a002000c9d64dcd400400199cc5b9a800800237a1d63500100346e43ac6a002000ccf735894004001998e6b1280080033558d718c0100061e3a2ca980201c8bd86dd1300400187ccbba260080030f597744c01012e4f31ee89802000cae62dd1300400117d0eb22600801e2f21d644c0100064fba2c69802000c9c7458d300400195ee8b1260080032b1d1624c01000672b12e3100201787d86dd5200400187cc9baa40080031798f754801015637316ea9002000
  | 2 => 0x659881000556c20cb3102000ace83196620400159b0632cc4080029ba17649881000536c2ec93102000ace83d92620400159b07b24c4080038b996649881000716b2cc93102000e2e655926204001c5acab24c4080029ba14649881000536c28c93102000ace83192620400159b06324c4080029ba17639881000536c2ec73102000aae84d8e620400155b09b1cc40800393996639881000726b2cc73102000e8e6498e6204001d1ac931cc40800393995639881000726b2ac73102000e8e6458e6204001d1ac8b1cc4080029ba14639881000536c28c73102000aae8418e620400155b0831cc4080029ba17725881000536c2ee4b102000aae84dc9620400155b09b92c408002b3a0f725881000566c1ee4b1020008ee87d95620400155d09b2ac408002ab61365588100056741ecab102000acd83d9562040018deed32ac4080031bdd9655881000477438cab102000aae84195620400155b0832ac408002b3a0c655881000566c18cab1020008ee87d9162040014dd0bb22c4080029b61764588100056741ec8b102000acd83d91620400195eed322c4080038b996645881000716b2cc8b102000caf765916204001c5ccab22c4080038b595645881000477438c8b102000a6e8519162040014db0a322c408002b3a0c645881000566c18c8b1020008ee87d8d62040014dd0bb1ac4080029b617635881000557426c6b102000aad84d8d620400199eed31ac40800393996635881000726b2cc6b102000e8e6498d6204001d1ac931ac40800333dd963588100072732ac6b102000e4d6558d6204001d1cc8b1ac408003a3591635881000477438c6b102000a6e8518d62040014db0a31ac408002aba10635881000556c20c6b102000ae8805d562040018daea3aac408002b9205745881000717aa4a8b102000ae4815cd6204001c9ea729ac408003a350c43588100053742ce2b102000a6d859c5620400b1dd0fa8ac4080023b61f515881000575400a2b102000ae980145620400159d07a0ac408002b360f41588100055742662b102000aad84cc562040014dd0a382c4080029b614705881000477438a0b1020008ed87141620400159d06202c408002b360c40588100057340880b102000ae581101620400155d08182c408002ab61030588100057340860b102000ae5810c162040014dd0a082c4080029b61410588100055742020b102000aad84041620400159d06082c408002b360c105881000636296eca90200087d859d9520400717d093b2a4080022f61276548100146f41ceca9020008dd839d952040011db053b2a4080031b149765481001c5f420eca9020008bd841d952040051bd063b2a4080023760c765481000c3e43acaa902001a6c825955204001c58a4b22a4080039314963548100247643ac4a902004a6c8558952040018f
  | 3 => 0x8b182000a5d85d91630400159d05b22c608002b360b6458c100064fbb4c8b182000e1e659916304001c3acb322c60800327dd96458c100070f32ac8b182000e1d6559163040011bd0e322c60800297a146458c100052ec28c8b182000ace82191630400159b04322c60800297a146258c100052ec28c4b182000a9e84189630400153b08312c60800317dd67558c100056a40aeab182000ad8805d1630400193ae83a2c60800387d525458c100056a40ae4b182000a9e849c5630400153b0938ac608002b3a0b5158c1000566c16a2b1820068de87d0563040011bb0fa0ac608002b6a004158c100056cc0082b182000a5e85c8563040014bb0b90ac608002a7a107058c100054ec20e0b182000ace82141630400159b04282c608002b5a045058c100056ac08a0b1820008de8710163040011bb0e202c60800297a142058c100052ec2840b182000ad68108163040015ab02102c60800297a141058c100052ec2820b182000a9e84041630400153b08082c6080021f6167654c1001c5f424eca9820008bd849d953040011bb073b2a6080063ba0a7654c1000476c14eca9820038be841d9530400117b083b2a6080063ba087654c1000476c10eca98200287c8759553040091b90eb1aa6080031d5977154c100066ab1ee2a9820008f5861c5530400193887bb286080121fa167650c100043ec2ceca1820008bd849d943040011bb073b286080063ba0a7650c1000476c14eca182000c9c435d943040090fd0a3b286080021f6147650c1000c77410eca1820008ed821d94304001c3886b2a860800a2f21d6450c100154e41ac8a1820038dc8758d430400753908b1a86080032e5937050c100066cb1ee0a1820008f9861c14304135b308638286080031b98975d88100043ec3ccbb102000c3e7499762040018bce732ec4080021fe1d65d88100061f3a2cbb102000c5e73597620400187ccaba6c4080030f59574d881000657312e9b1020008bd87993620400187ceb326c4080030f5d664d88100064f39cc9b1020008bf87593620400187ceab26c4080030f5d564d88100064f39ac9b102000c5e655cf62040018bacab9ec4080032799173d88100064eb22e7b102000cce625cf62040011bb0f31ec408003179d663d88100062ebacc7b102000c9e7498f620400193ae931ec40800237e1d63d88100062f3aac7b102000c5d7558f620400193ce8b1ec408003275d163d88100243fc3aebb102000c3e759d3620400187aeb3a6c40800e2fe1d74d88100061f3aae9b102000c3d755d362040018bceb39ec408003175d673d88100064f3a4e7b102000c9d749cf62040051bf0eb9ec408003179d573d88100062ebaae7b102000c9e745cf620400193ae8b9ec408002aba13659881000556c26cb3102000ace83d96620400159b07b2cc408002aba1
  | 4 => 0x40400153b0632ac808002aba08655901000556c10cab202000a3e8518d640400147b0a31ac808002aba08635901000556c10c6b202000a3e85189640400147b0a312c808002a7a0c62590100054ec18c4b202000c3f759d5640400156902baac808002ae20173590100064eb98e6b202000e1f5394d640400156902b92c808002a7a0e71590100054ec1ce2b202000aae82d45640400155b05a8ac80801e2fa1f31590100045ec3e62b202000aba800c564040015730018ac8080028fa1721590100051ec2e42b202000a9e831c1640400153b06382c808002aba08505901000556c10a0b202000ab681141640400156b02282c8080022fa1c30590100045ec3860b202000a3e85081640400147b0a102c808002ada0420590100055ac0840b202000a3e85041640400147b0a082c8080021f61676550100045ec24ecaa020028de839d954040011bb073b2a8080063ba0a765501000476c14ecaa020028de831d954040011bb063b2a8080063ba08765501000476c10ecaa0200387c8759554040091790eb22a8080031d59771550100065ab26e2aa020008f5861c554040018bcc6baec6080021f61e65d8c100061f3a4cbb182000c6e7299763040010ff0eb2ec6080030f9d165d8c1000637392cbb182000c3e655d3630400187acaba6c6080032798d74d8c100045ec3cc9b182000c3e75993630400187aeb326c6080032b9ca64d8c100045fc3ac9b182000c3e75593630400187aeab26c6080032b9c964d8c100063732ae5b182000c6d655cb630400195cc8b96c6080032b59172d8c100066731ae5b18200487f875d7630400187ceb3a6c6080030f5d674d8c1001c5fc3ae9b182000c3e755d3630400187aeaba6c6080031b9d672d8c1000636bace5b182000cae749cb630400195ae9396c6080063be1d72d8c10006373aae5b182000c6d755cb630400195ce8b96c6080032b5d172d8c100054f426cb3182000a9d84d96630400159d05b2cc608002b360b6598c100054f420cb3182000a9d84196630400159d0432cc608002b36086598c100052f42ec93182000a5d85d92630400159d05b24c608002b360b6498c100070f32cc93182000e1d659926304001c3ccab24c608003875956498c100052f428c93182000a5d85192630400159d04324c608002b36086498c100052f428c53182000a5d8518a630400153d08314c608002a76106298c100052f42ee6b182000a5d85dcd630400153d09b9ac608002a76137358c1000567416e6b182000acd82dcd63040018beeba9ac60800237a1f6558c100054f426cab182000a9d84d95630400159d05b2ac608002b360b6558c100062fbb4cab182000c5f7659563040011bd0e32ac608002a7a106558c100054ec20cab182000ace82195630400159b0432ac60800237a1f6458c100052f42ec
  | 5 => 0x8003b118c62841100061f32ae9b282000c5e655cf65040018dccab96ca0800e2fe1d74d94100064f3a4e7b282000c9d749cf65040051bf0eb9eca08003279d173d94100064eba2e7b282000cae749cb650400195ae9396ca08003339ce72d941000666b9ce5b2820018ef875cb650400195ce8b96ca080032b5d172d94100066739ae5b282000ccd735cb65040014bd06324ca080029760c649941000537410c93282000a6d82192650400147d0831cca080028f610639941000537410c73282000a6d8218e650400147d08314ca080028f61062994100052f418c53282000a5d8318a650400147d09baaca080028f61375594100052f41eeab282000a5d83dd565040014dd05baaca080029b60b75594100061fba4a8b282000c5f7394d65040014bd06322ca080029760c645941000537410c8b282000a6d82191650400147d0831aca080028f610635941000537410c6b282000a6d8218d650400147d08312ca080028f61062594100052f418c4b282000a5d83189650400187ee93a2ca080029d20574594100062fb9ce6b282000a74815cd65040014f100b92ca080031b5c8725941000537414e2b282000a6d829c565040014bd07a0aca080029760f41594100051f42662b282000a3d84cc565040110fd0f90aca080021f61f21594100053d40042b282000a798008565040014dd04382ca080029b60870594100052f41880b282000a5d8310165040014ed02202ca080029d60440594100051f42060b282000a3d840c165040014ed02182ca080029d60430594100043f43840b28200087d87081650400187cc8baec8080021f61e65d90100062f39ccbb202000c6e7299764040010ff0eb2ec808003179cd65d901000637392cbb202000c5e655cf64040018bacab9ec8080032799173d90100063732ae5b202000c6d655cb640400195cc8b96c8080121fe1d75d90100062f3ace7b202000c5d759cf64040051bf0eb9ec808003179d573d90100062ebaae7b202000c6e759cb64040018daeb396c808003339ce72d901000666b9ce5b2020018ef875cb64040018dceab96c8080031b5d572d90100066739ae5b202000ccd735cb640400153d07b2cc808002a760f659901000557416cb3202000aad82d96640400153d0632cc808002a760c659901000557410cb3202000aad82196640400147d0a31cc8080028f614639901000557410c73202000aad8218e640400147d0a314c8080028f61462990100054f418c53202000a9d8318a640400147d0bba2c8080028f61774590100054f41ee8b202000a9d83dd1640400155d05ba2c808002ab60b74590100061fbaea8b2020008be87d95640400153d07b2ac808002a760f655901000557416cab202000aad82d95640400187eed32ac8080030fdd965590100045f438cab202000a9e831956
  | 6 => 0x1476432e528a2000c6f655ca514405f8d8cab94a2880032bd91729451000656322e528a2000ccf635ca5144001998c6b94a2880023be1f629451004c76c3ec528a2000c7b65dc151440019d0c5b82a2880031ed94705451000674310e0a8a2000c5e73d96414400193ce7b2482880f63721973905100062fb2ae720a2000c5c655ce414400193ec8b9c82880d327191739051000666312e720a20008df87d8e41440151bb0fb1c8288003339cf629051000666b9ec520a2000cd863dc14144001976c838282880033618c70505100061f3a6cb18a20378bc865d2314400187ecaba462880030f195748c5101d64e31ae918a2000cac625d2314400117f0fb24628802e2f61f648c5100064f3a6c718a2000c9d74d8e314400195ce9b1462880032b5d3628c5100065c326e098a2000cb8641c131440019b6c638262880ca1f21975885100061e322eb10a2000c5c635d6214407f8d8c4bac42880021fe1f65885100643ec3ecb10a2000c3e75d92214400187aebb244288003179d763885100062ebaec710a2000c6e75d8a21440018daebb1442880031e19770485100063c328e090a2000ceb621c121440018d8e5b2aa0880032b1cb645411000666396c6a8220008ee86dc950440018decbb92a08806b1b197725411000657b26e4a822000cac64dc9504400199ec7b92a0880033318f725411031c7743ec4a82201a8ec87d895044001968c9b8aa0880033518f71541100063bb28e2a822000cb4641c550440019a8c638aa088003171cf65501100064e39ec8a0220008de86dcd40440018becbb9a80880031719773501100064fb26e6a02201fc9c64dcd4044001998c5b9a808817e37a1f63501100fc6e43ec6a022000ccf73d894044001998e7b1280880031d197715011000672316e2a022000c74651c5404400196ec838a80880033918871501100061e3a6ca98220008be86dd1304400187ecbba260880030f197744c11012e4e31ee89822000cac62dd130440af17d0fb2260880962f21f644c1100064fba6c69822000c9c74d8d304400195ee9b1260880032b1d3624c1100063a32ee29822000ce462dc530440018e8ca38a608800335d8c714c11000672310e2982200087e86dd52044001878c9baa40880031718f754811015636316ea902205387e87d9520440550f90fb2a40880030fdd764481100061e3aec89022000c5f75d8d20440018b8ebb1a40880031bdd76248110006363aec49022000cb464dc520440019a8c7b8a40880032d19071481100066a318e29022000ce7621c52044001d30c831e20880039a19462c41100663b3b6cb0822004c7676196104401796cedb24208800f2d9d864841100071a328c9082200acd676d8e10440059acec31c208800395194638411004e733b6c50822001ce67618a1044001d48c8314208
  | 7 => 0x9f64dcd6244001938c9b9ac4880033318b73589100046f43ec6b122000c5f75d8d62440018b8ebb1ac48800327dd363589100064e3a6c6b1220008de8718d62440018beea31ac488003171d463589100064fba0c6b122000c9c7418d62440090fd0fbaac48800e2fa1f74589100061fbaee8b122000c3c75dd1624400187eea3a2c4880030f1d474589100146f43ee6b122000c5f75dcd62440018b8ebb9ac48800327dd373589100064e3a6e6b122000c5f751cd62440018b8ea39ac48800327dd073589100064e3a0e6b122000c6f75dc962440018d8ebb92c4880032bdd37258910006563a6e4b122000ccf73dc96244001998e7b92c4880032d1d371589100066a39ee2b122000c7875dc162440018dcedb28c4880023b61e65189100053742cca3122000aae84994624400155b09328c488002b3a0e651891000566c1cca31220008ef87594624400155f08b28c488002ab211651891000567c1aca3122000acc8359462440014dd0c328c4880031b9d86518910006573b6c83122000e2f65d906244001c58cbb20c4880023b61e64189100053742cc83122000a6d85990624400155d09320c488002b3a0e641891000566c1cc831220008ef8759062440014df0ab20c4880029b215641891000567c1ac83122000acc83590624400155d0c320c4880032b9d8641891000717b28c83122000e2c65190624400199cedb18c48800393d9763189100072632ec63122000e8f64d8c6244001d18c9b18c4880023b61e63189100053742cc63122000a6d8598c624400155d09318c488002ab61263189100056741cc631220008ef8758c62440014df0ab18c4880029b215631891000557c22c63122000aac8458c624400159d0c318c488003339d8631891000727b28c63122000e4c6518c6244001d1ec8318c488003a3190631891001c5f426eca9220008bd84dd952440051bd07bb2a4880023760f765491000636294eca92200087f855d9524400117f08bb2a48800e2f21176549100046fc1aeca9220028dc835d952440011df04bb2a4880023ee01765491000636290eca92200187e87d9552440034dd05b2aa4880038b14b645491000726296c6a9220048ee87d8952440094dd0bb12a4880121fa1776509100043ec2eeca1220028de83dd942440011bb07bb284880021fe1576509100243e42aeca1220008bf845d942440011bf06bb2848800a3720d765091000477c12eca1220008f7815d9424400317d0fb22848800e3ba1f62509100243f42eec992200087d85dd9324400717d09bb264880022f613764c9100043fc2aec992200487c855d9324400117f08bb2648800e2f211764c9100046fc1aec99220008ef825d932440011ef02bb2648800637a1f634c9100147743ec49922000c6e72d96514400195ce5b24a288003339cb63945102
  | 8 => 0x9328c688002b3a0a6518d1000566c14ca31a20008df87594634400153f08b28c688002a72116518d1000567c12ca31a2000acc8259463440014bd0c328c688003179d86518d100064f3b6c831a2000e1f65d906344001c38cbb20c6880023761e6418d100052f42cc831a2000a5d85990634400153d09320c688002b3a0a6418d1000566c14c831a20008df8759063440014bf0ab20c688002972156418d1000567c12c831a2000acc82590634400153d0c320c688003279d86418d100070fb28c831a2000e1c6519063440014bd0b310c688002976166218d100054f424c431a2000a9d84988634400717d09bb2a6880022f6137654d1000c77416eca9a20008ed82dd953440010ff0abb2a6880022fe117654d1001c5e422eca9a20008df835d953440011df04bb2a6880063b2097654d100047bc0aeca9a200287e87d9553440091bd0fb1aa6880121fa177650d100043ec2eeca1a20018ee82dd943440011db05bb286880032710e7650d100043fc2aeca1a200487c855d9434400117f08bb2868800237e0d7650d1000477c12eca1a20018ec825d943440011f700bb286880032710c7650d100070e21ecaa1a20028be87d91434400553d07b22868800e37a1f6350d1001d4f426c6a1a2000aae84997624400155b0932ec488002b3a0e65d891000566c1ccbb122000aaf84597624400155908b2ec488002b3e0d65d89100056641acbb122000e2f65d936244001c58cbb26c4880029ba1664d891000536c2cc9b122000ace83993624400159b07326c4880029be1564d89100053642ac9b122000acf83593624400159906b26c4880038bd9464d891000716328c9b122000e4f65d8f6244001c98cbb1ec488003a3d9363d891000746326c7b122000a6e8598f62440014db0b31ec488002aba1263d891000556c24c7b122000a6f8558f62440014d90ab1ec488002abe1163d891000556422c7b122000e4f6518f6244001c98ca31ec488003a3d9063d891000746320c7b122000c6f759d76244001c5ea92a6c48800393d4e53d891000746a1887b122000a6f855c762440014d90ab8ec4880023ba1f51d891000476c3ea3b122000ace83d07624400159b07a0ec488002aba1331d891000556c2663b122000a6e85dc362440014db0bb86c4880023ba1c50d891004c76c38a1b122000ace83103624400159b06206c488002aba1030d891000556c2061b122000c6c62dd562440010fd0fb2ac4880030f1d365589100062e39ecab12200087e871956244001878e832ac488003171cc65589100061fb2ee8b122000c3c65dd16244001958c5ba2c4880022fa1f64589100061fbaec8b122000c3c75d916244001938e7b22c4880022fa1c64589100061fba8c8b122000c3c751916244001938e6322c48800317d9773589100062e32ee6b122000c
  | 9 => 0x725911000637ba8e4b222000c6c751c9644400195ee8392c88800333dcc725911000666398e4b222000c7475dc564440019c8e5b8ac888003361cf70591100061f3b6ca32220008bd87994644400147d0b328c888002a7a0e65191100054ec1cca3222000aae82994644400155b05328c8880022fe1d65191100054fc1aca3222000a9c83594644400155f04b28c888002ab20965191100051f430ca3222000c3e76194644400147d0b318c8880028f616631911000557414c63222000aad8298c644400147d0b310c8880028f61662191100054f41cc43222000a9d8398864440051bd07bb2a8880023760f765511000c77416ecaa220008ed82dd954440010ff0abb2a8880022fe1176551100046fc1aecaa220028dc835d954440011df04bb2a8880063b20976551100047bc0aecaa2200387e87d95544400917d0fb22a888003175d753d8d100054f424cbb1a2000a9d84997634400159d0532ec688002b360a65d8d100054fc22cbb1a2000a9c84597634400159f04b2ec688002b320965d8d100070fb2ec9b1a2000e1c65d9363440014bd0b326c6880029761664d8d1000567414c9b1a2000acd8299363440014bf0ab26c6880029721564d8d1000567c12c9b1a2000acc825936344001c3eca326c6880038719464d8d100052f42cc5b1a2000a5d8598b634400153d09316c688002a761262d8d100062eba8ebb1a2000c9f749d36344001c3ea92a6c688002a7e1171d8d100054e422e3b1a2000ace82d47634400159b05a8ec68800237a1f41d8d100046ec3e83b1a2000a5e85c8763440014bb0b90ec688002a7a1370d8d100054ec26e1b1a2000ace82143634400159b04286c68800237a1c40d8d100546ec3881b1a2000a5e8508363440014bb0a106c6880031718f7558d100043f43ecab1a2000c3c74d9563440018d8e5b2ac6880021fa1c6558d100061e3a0cab1a2000c6c72195634400187ecbba2c6880030f1977458d100064e31ee8b1a20008be87d91634400187eebb22c6880030f1d76458d1000656396c8b1a20008be87191634400187eea322c6880030f1d46458d1000656390c8b1a2000c6f65dc963440018d8cbb92c6880032bd937258d1000656326e4b1a2000ccc63dc963440090fd0fbaac68800e2fa1f7458d100061fbaee8b1a2000c3c75dd1634400187eea3a2c6880030f1d47458d100062fbaee6b1a2000c5c75dcd634400193ee9b9ac688003271d37358d1000c7743ee4b1a2000c6f75dc963440018d8ebb92c6880032bdd37258d10006563a6e4b1a2000ccf73dc963440018deea392c6880031b1d47258d1000657ba0e4b1a2000cac741c9634400199ee6392c6880031d1d77158d1000672396e2b1a2000cb874dc163440018bcedb28c6880023761e6518d100052f42cca31a2000a9e84994634400153b
  | 10 => 0x984201aa6c8558a20840018d8ebb1241080030f5d254d95100062eb9ca7b2a2000a5e8399365440014bb07326ca880029ba0a64d951000536c14c9b2a2000a3e8498f654400147b0931eca880029ba0a63d951000536c14c7b2a2000a3e8498b654400147b09316ca8800297a0e62d95100052ec1cc5b2a2000c3d741d365440018bae639eca880031bdca72d951000537c12e3b2a2000a6c825c765440014bd07a0eca880029760f41d95100051f42663b2a2000a3d84cc765440010fd0f90eca880021f61f21d951000537416e1b2a2000a6d82dc365440014bd06206ca880029760c40d95100051f42061b2a2000a3d840c365440010fd0e106ca880321f61c20d95100061e32ee8b2a2000c5c65dcd65440018d8cbb92ca8800e2fa1f74595100061fbaee8b2a2000c3f751d165440051bd0fb9aca8800317dd773595100064fba6e6b2a2000c9c74dcd65440018beea39aca8800327dd073595100064e3a0e6b2a20018ee87dc965440018deebb92ca880032bdd37259510006563a6e4b2a2000ccf73dc96544001998e7b92ca880031bdd4725951000657ba0e4b2a2000cac741c9654400199ee6392ca88003331cc72595100065a3a6e2b2a2000cd473dc565440019d0e5b82ca8800297a0e64195100052ec1cc832a2000a6e8299065440014db05320ca880028fa1263195100051ec24c632a2000a6e8298c65440014db05318ca880028fa1262195100051ec24c432a2000a5e8398865440014bb07310ca880030f5d754d91100054f41ccbb222000a9d83997644400155d0532ec888002ab60a65d91100054fc1acbb222000a9c83597644400155f04b2ec888002ab20965d91100051f42cc7b222000a3d8598f644400155d0531ec888002ab60a63d91100051f42cc5b222000a3d8598b644400153d07316c888002a760e62d91100061eba8ebb222000c9f739cf6444001c3ea729ec888002a7e0d71d91100054e41ae3b222000aae82d47644400155b05a8ec8880022fa1f31d91100045ec3e63b222000a3e85c87644400147b0b90ec888002a7a0f70d91100054ec1ee1b222000aae82143644400155b04286c8880022fa1c30d911005c5ec3861b222000a3e85083644400147b0a106c8880030f19375591100043f43ecab222000c5c73d9564440018d8e5b2ac8880021fa1c65591100062e398cab222000c6c7219564440018becbb9ac8880031719773591100064e326e6b222000c6f65dc964440018d8cbb92c8880032b19372591100243f43eeab222000c3f75dd16444001878ebba2c88800a37a1f73591100062fbaee6b222000c5c75dcd644400193ee9b9ac88800317dd473591100062e3a8e6b222000c9f741cd64440031dd0fb92c8880031bdd77259110006363aee4b222000caf74dc9644400199ee7b92c888003331cf
  | 11 => 0x480012df0ab8c40900031b195718812000c76c38c31024000ce57118620480031df0eb96cb880029ba0b755971000637b94a4b2e20028df875cf64c400153d07ba2c98800a37a0e76553100046ec1cecaa620018ee829d954c40011db053b2a98800e2fe1d74d8f100054f426e6b1e20038be849d953c400117b093b2a7880063ba0a7654f1000476c14eca9e2000c9c43dd943c400117b093b287880023760e7650f100043fc2aeca1e200487c855d943c400193886bb287880023be097650f1000c76412eca1e20028be87d9143c400553d07b22878800e37a1f6350f1001d4f426c6a1e209cd98431c143c40090ff0ebaec5880029ba177258b1000637baea4b162000c6c52dd952c40010fb0b3b2a5880023b60a7654b100045fc22eca9620038bc845d952c40011bf06bb2a58800a3720d7654b1000636292eca96200187e87d9552c40034dd05b2aa5880123ba1f6254b100253742ec4a96209bd68521c152c40090fd0b3b285880021f6167650b100146f41ceca1620008dd839d942c40090fd0b3b265880021f616764cb1001c5f424ec99620008bd849d932c40018dce4b2ca3880fe9ba0b65547100064f39ac920e203aa9e83d9141c400193ce8b1c63880d2a7a13634c710006373aac510e202fa6e85d8921c40554dd05b2ca1880031b1c9655431012d4f41ec92062000c9c7359140c400196ac838a818807ea7a13638c3100064e3a2c69862000cd5631c530c40354dd0bb1441880031b1d5624831000636b94a5b2c20018ee87dc965840018deea392cb0800a37a1f73592100064fba0e6b2420008df835d954840051b906bb2a9080023be09765521000c76412ecaa420038be87dd16384001938e9b9ac7080022fe117654e1001c5e422eca9c20008ef825d953840031d904bb2a7080121fa167650e100043ec2ceca1c2000c9c439d943840031dd053b287080023b60a7650e100045fc22eca1c20008df835d94384001938863b2870800a2f21d6450e100154e41ac8a1c20038dc8758d438400753908b1a87080031b5d752d8a100243f43eeab142000c6c75dc9628400717d093b2a5080022f6127654a100146f41ceca9420008dd839d952840018d8a53b2a5080021fe157654a1000477c12eca942000c6c521d952840030f90eb2aa5080069b2096554a100247643ac4a942004a6c8558952840010ff0abb285080121f2157650a100046fc1aeca1420028dc835d942840010ff0abb265080121f215764ca100045fc22ec99420038bc845d932840018dce5b2ca3080fe9b20965546100064f39ec920c203aa9c83591418400193ce9b1c63080d2a7211634c610006373aec510c202fa6c8558921840019d2c438243080aa9b209659421000636396caa842025a9c835924084001938e7b22810807ea7211638c2100064e3a6c6
  | 12 => 0x31b1d77258d200063bbaee2b1a4000c7475dc5634800196ee9b8ac6900032d1d37158d200063bba8e2b1a4000c74751c5634800196ee838ac6900032d1d07158d200066bb98e2b1a4000ce7721c563480010ff0abb2a6900022fe117654d2001c5e422eca9a40008ef825d953480011ef02bb2a6900023d2057654d200143f43ecaa9a400487e85dd943480010fb0bbb286900032710e7650d200043fc2aeca1a400487c855d9434800117f08bb2869000237e0d7650d200047bc0aeca1a40008f4815d94348001938863b286900038710f6550d2000477436e4a1a4000c6c65dc943480094dd0db2aa49005f1b1db655492000477436e2a92407bc6c65dc552480551dd0c382a49014f1b194705492029eb5ba8e0a9240008df835d361480051b906ba6c2900022fe1173d852001c5e422e7b0a4000ad683d07614800156d0998ec2900021fa1f65585200061e3a6cab0a4000c5c73d9561480010fd0e32ac2900030f1d065585200062e398cab0a409bc7b70195614800187ecbba2c2900030f19774585200062fb2ee6b0a4000c5c65dcd61480a78dce4328c2900023de1d61185200055a422c230a4000ad48358461480f71df0ea90c2900131b1d552185200056b41e8230a4000ab684cc461480031dd043b4a2900ab1b9cb659452017e3632ae528a40009e8805ca51480032df0ea94a2900129b2195294520006373b2a528a4000c6e521d951480010ff0abb482900121f21576905200146f418ed20a40008dd831da41480018bce7b2c8290003279cf64905200062fb2ae720a4000c5c655ce41480018d8cab9482900121fa1776505200043ec2eeca0a400087f855da31480090f90abb4629000e2fa10768c5200045ec20ed18a4000c3e74d96314800187ecaba462900030f195748c5200064f3a6c718a4000c6c655ca31480090fd0bbb262900021f617764c52000477436ea90a402fc6c65dd5214805f8d8cabaa42900027a201754852029d37436ca90a4000e6465d8521480231dd0e30a429000399d9461485200073432ee090a400d8ee861c121480012db0a38242900031b194704852000734328e090a400d9ea861c121480019d50c38242900035aa147048520006b4c28e090a4000d6b651c121480019d4ca38242900033a1947048520006b4328e090a4000c68651c121480558d8e5b2aa09006b1b197725412000cb643aa4a824004a6c8654950480038d8eca92a090002da20152541200062e39ecaa024000c9c73d9140480018becbb9a80900031719773501200063632ee4a024000c3c74d95304800187ecbba260900030f197744c1200064e3a6c69824000c6c65dc930480091dd0dbac409006b1b197758812000c76432eb102401ac6c655d620480a74dd0db2c40900ab1b9db658812015735b06cb1024004c6e7619620
  | 13 => 0x64f3a4e7b2c4000c9d749cf6588001c98a539ecb1000a37e1d73d96200064f3a2e7b2c4000c9d745cf6588001c98a4b9ecb100031b14971d96204ef34294e1b2c402ac6c72dd5658800187eebaa2c9100022f61276552200146f41cecaa440008dd839d954880018beeba9ac71000e2fa127654e200045ec24eca9c40008dd839d953880090fd0b3b287100021f6167650e200145e43ac8a1c4002a9c8359143880071b90eb1a871000ea72116350e2000636296eab0c400487e87dd561880018dd05baac3100031b60b75586200063610eeab0c4000c6f20dd561880011dd0fa92c3100031bdd752586200047bc3ac230c4000c6f525da51880558dce5b2ca3100031b59772546200146f41eed20c40008dd83dda41880010ff0abb283100121f21576506200146f418eca0c40008dd831d9418800156902b22831000e2fa13768c6200045ec26ed18c400087f855d931880090f90abb2631000e2fa10764c6200045ec20ec98c4000ad48158d31880dd2df0ebac431006b1b9d7658862000477c3acb10c401ac6e75596218801b1df0eb0c43100029be156188620006373aac310c4000d6a759c221880231df0cb8443100035a5d5708862000636b2ae5284400187e87d9550880558d8e5b2aa1100030f5d254d95200062eb9ca7b2a40018ec825c7654800187ae83a6ca90003175cc73d952000537c12e3b2a402aa6c825c765480014db0438eca9000297a0f41d95200052ec1e83b2a4000a3e84cc7654800147b0998eca9000297a0c40d95200052ec1881b2a4000a3e840c3654800147b08186ca900029b60a641952000536c14c632a40008df835c764480051b906b8ec8900021fa1f65591200062e39ecab22400087e8719564480018b8e632ac89000317d9773591200062e32ee6b224000c7765dc564480018e8cbb8ac8900031dd9471591200063a328e2b224000cb4641c564480090fd0fbaac89000a37a1f73591200062fbaee6b224000c5c75dcd64480018beea39ac890003171d473591200064fba0e6b224000c6c75dc964480018eeebb8ac8900031d1d771591200066bb9ee2b224000cd473dc564480018eeea38ac8900031d1d471591200065bba0e2b224000cd7731c564480019a8e638ac89000339dc871591200043fc2aecaa240008df835d954480051b906bb2a8900023be0976551200047bc0aecaa240008f4815d954480070fd0fb2aa8900022fe1171d8d2001c5e422e3b1a400087e87d956348001878e9b2ac6900021fa1c6558d200061e3a0cab1a4000c3f65dd16348001878cbba2c6900031dd977158d200063a32ee2b1a4000c77651c563480018e8ca38ac6900033518c7158d200243f43eeab1a40038be87dd1634800187eebba2c6900030f1d77458d200061fba8e8b1a4000c3c751d16348001938e9b9ac690
  | 14 => 0xc82594644c00156f02b28c898002ad20565191300054ec1cc432260008bf845d9544c0011bf06bb2a8980023be09765513000c76412ecaa260008f7815d9544c0011e902bb2a8980122fa1f645513001d4f436c8a1a601cc9c76d91434c0011bd0db8a86981df271937150d3012c6f430e0a1a6057c9c641c1434c0afb36e838286980031b5d752d89300043fc2ae3b12600487c855c7624c00117d0fb22c4980030fdd764589300061e3aec8b1260008be87191624c00187eea322c4980030f1d464589300065bb26e2b126000cb464dc5624c00196ec838ac4980032d190715893000672310e2b1260038be84dd9524c00117b09bb2a4980031b14a765493000636290eca926000e2c52d91524c001938c9b9aa4980062fa1f645093000477c12ebb0a60018ec825d7614c0010ff0ab96c2980121f21572d853000573416a3b0a6000a7685c87614c00117d0fb22c2980030fdd764585300061e3aec8b0a6000cac72d91614c00117d0e322c2980030fdd464585300061e3a8c8b0a6000cac72191614c139976e0322c2980032bd93725853000656326e4b0a6057c9e73190614c0011ef0eb08c2980029d215611853000572412c230a60778df8750c614c007938e8a18c298002b9a0b51185300056ac18a230a6000a7685c84614c0015ab06108c2980022fe11769453001c5e422ed28a60018ee821da514c0011db043b4a2980031b9cb659453000657396c928a6000c5f655ce514c001938c8b9ca2980032bd91729453000656322e528a60038be84dd9514c00117b09bb2a29800a37a0c769053012e4f39ec920a6034c9c645ce414c00533f0ea1c829800ea721943905300064f3b28720a6000c9e431d9414c0011bd0dba262980d327193744c5301a64e322e898a60009d8805d1314c0af53d0db226298003a5193614c5300946f438c298a6000e9764185314c001d28c830a629804ab5a1c614c5300066b438c298a6000e9864dc1314c01d1bd0c382629800267610704c5300064e320e098a6000e98641c1314c00117f08bb4429800e2f21176885300243f428ed10a600087d851da214c001878c8bac42980030f9d764885300061ebaec910a6000c9c645ce214c0018dcebb14429800e2fa1376485300045ec26ec90a6000e3b50d92504c0018d8e5b2aa0980032b1cb64541300062fb2ee6a826000c9c64dcd504c00195ec9b92a0980032b193725413012e4e39ec8a02601fc9c64dcd404c0053390ea1a809800ea721943501300164e3b286a026000b988050d404c0071bd0dba4609807f27193748c1300146e432e9182601fc9c645d2304c0af53d0db246098097279db648c13001e4f3b0c9182600099f845c6304c001938c8b8c609800a3761c618c1300066ab88c31826000e2c529d3658800717f0eba6cb100038b14974d962000
  | 15 => 0x638282a0003a618c705054001c5f420ed18a803ac9c635d2315003f93ce9b1c62a000e67e1d438c5400154e4328718a8000c9e7650e315000193e863b262a00eb2718d744c540004dc402e898a80008df835da21500051b906bb442a00121fa1476885400043ec28ed10a8000c5c635d62150001938c6ba442a0003179d763885400062ebaec710a8000c6e75d8a21500051bd07bb242a00023760f76485400072da86c72828000c6c72d95505000187ecbba2a0a00032718f745414000666396c6a828000ccf63dc95050001998c7b92a0a000e2f219739014012e4e31ae72028025a9e86d8e405004593cedb1c80a000b279d86390140004cfc1ae32028000c9c635c6405000717b0e30c80a00032d5c461901400061fba4a8b2c6000e1c439d7648c0090ff0ebaec9180038710d75d9230006373ace5b246000c6d759cb648c001d1887396c9180063be1d72d9230006373aae5b246000c6d755cb648c001d1886b96c9180032710d71d92304f74c21ce1b246025c9c73dd1648c0010fb0b3b2a9180063ba0a765523000476c14ecaa4600187c87595528c0034d904b2aa5180123b21d6254a300253642ac4a946000c9c43dd1618c00717d0fba2c31800327a0f74586300064ec1ee8b0c6000c9c31dd1618c00193e61ba2c31800237a1f43586300064fba686b0c60008f787584618c0031dd05bb4a3180023b60b76946300045fc22eca8c60038bc845d9518c0031dd043b2a3180023b60876546300062eb2ee6a8c6000c9f435da418c04b93ce7b2483181ca67e1d748c6300fe4f3a6c918c60008df87592318c03f93ce8b24631803a37e1d618c6300054fc22c318c6000c9e74586318c001b34e9384631804a37e19708c6300243f42eed10c600087d85dda218c00117f08bb2431800e2f21176486300243f428ec90c600087d851d9218c0018bacab9ca11800a2fa1f645023012e4e39ec8a046000c6d7294b654c0011df04b8eca980063b20971d95300063a328e2b2a60038be87dd1654c001938e9b9aca980063ba1f725953000657ba6e4b2a6000cac74dc9654c0018deea392ca980032bdd07259530006563a0e4b2a6000cb774dc5654c001968e9b8aca9800339dcb715953000672396e2b2a6000c77751c5654c00196ee838aca980032d1d071595300066bb98e2b2a6000ce7721c5654c0019c8e438aca980030f5d754d91300146e41ae3b226000aaf82597644c00155904b2ec898002ade0565d91300055a40acbb226000c3d751d7644c00153f06b8ec898096a720d71d91300054ec18e3b226000aae82d47644c00155b05a8ec8980028fa1721d91300051ec2e43b226000aae82143644c00155b04286c8980028fa1420d91300051ec2841b2260008bd87994644c00153b07328c8980022fe1d651913000557c12ca3226000aa
  | 16 => 0x190640006cd39ce120c80138bf865c2419000193c86bb463200121fa1776886400043ec2eed10c80008df835d921900051b906bb243200121fa1476486400043ec28ec90c8000c3d655d250900018dae5296caa00023be0971d954000c76412e3b2a8000c74651c565500051bd0fb9acaa000327dd0735954000c7743ee4b2a8000ccf73dc96550001998e7b92caa00031bdd4725954000667b98e4b2a8000ccc731c965500019aee7b8acaa0003351cf715954000673b96e2b2a8000ce472dc565500018eeea38acaa00032ddd071595400066bb98e2b2a8000cd4731c565500019cee438acaa0003391c871595400062ebaea7b1a80028bc845c7635000159f04b2ec6a0002b320965d8d400056bc0acbb1a8000ad48159763500018baea3aec6a0002a7e1171d8d401154e422e3b1a8000a9d841c7635000159d05a8ec6a0002b360b51d8d400052f42e43b1a8000a5d85c87635000159d04286c6a0002b360850d8d400052f42841b1a8000a5d8508363500011bb0f328c6a0002a76126518d400046fc3aca31a8000acf82594635000159904b28c6a0002b5e056518d400056a40aca31a8000a9d8498863500091bd0fb1aa6a000aa7a1b6350d401164e3b6c6a1a80008be86dc543500e5938c7b8a86a007e2fa187050d402be4e318e0a1a805fd9b731c143500018daeba96c4a00021fe1571d89400243e42ae3b1280008de87d8d62500018beebb1ac4a0003171d763589400046f438c6b128000c5f7518d62500018b8ea31ac4a000335d8f71589400066a31ee2b128000cd7631c562500019a8c638ac4a00033918871589400146f41eeca9280008dd83dd952500018d8a53b2a4a00031b14876549400064e31ee8a928000e4c52d8d52500031bd0fb1a64a00023be0975d854000c76412ebb0a800087f855cb61500090f90ab96c2a0002b9a0b51d85400053b42e43b0a80008de87d8d61500018beebb1ac2a0003171d7635854000666396c6b0a80008de8718d61500018beea31ac2a0003171d4635854000666390c6b0a809fcdb7018d615000199ec7b92c2a00033318f72585403964f3a0c630a80008f78758461500014e90ab08c2a0002b920961185403945fc3a8630a8002c9c7350c61500015cd05a88c2a0002ad61051185400053b42e4230a8000ab58408461500011bf06bb4a2a000a3720d769454000c77410ed28a80008ed821da51500018dce5b2ca2a00030fd9574945400064e31ae928a8000cce72d8e515000199ec6b94a2a00033318d72945400146f41eeca8a80008dd83dd9515000117d0db9a82a00eb2718f73505401d54f436c6a0a8000e9463d85415002717d0e30a82a0003a5d8c61505400074a318c2a0a8013ab687185415000196d0e30a82a0003a618f705054007c5f430e0a0a800099d831c14150001938c
  | 17 => 0x12a000a6f855c7625404f4d90ab8ec4a80029b61471d89500056741e83b12a000acd83d07625400155d0998ec4a8002ab61331d89500056741881b12a000acd83103625400155d08186c4a8002ab61030d895000476c3cc8312a000a6d8599062540011df0eb20c4a8002b3e0d64189500056641ac8312a000ae78159062540015c902b20c4a80023b61e631895000536c2cc6312a0008ef8758c625400155f08b18c4a8002ab211631895000573c0ac6312a000ae48158c62540034dd0db12a4a809f1b1db62549500043f436e2a92a06ec6c62dc552540350fd0c382a4a814f1b188705495031eb5b90e0a92a0038ee87d8942540051dd0fb1264a800237e0d74d85500146e41ae9b0aa0008bf845cf615400717908b9ec2a8002b5a0f41d85500055b42663b0aa0008ee87d89615400195ee9b12c2a80032b1d3625855000667b9ec4b0aa000ccc73d8961540011dd0e312c2a80032bdd06258550006563a0c4b0aa000ccf731896154001998e6312c2a82833adc06258550376373a8c430aa0008f787584615400156908b08c2a8002b520d61185503743fc3aa430aa001c6c7254861540015ad07a08c2a8002ada1331185500043f436e4a8aa03fc6c62dc9515407f4dd0db12a2a80039918b61545500a43f438c2a8aa000e6862dc151540210fd0c382a2a80025b608705455000636310e0a8aa000e68621c151540011df04bb482a80063b20976905500146f418ed20aa0008dd831da41540018d8c4bac82a80030f5d764905500064f39ec920aa000ccc625ce415400199ce7b1482a8003335cf629055000c77416eca0aa0008ed82dd941540011df04bb462a80063b209768c55001c5f420ed18aa0008bd841da31540018d8c4bac62a80032b189748c5500062ebaec718aa000c9e74d8e315400195ce9b1462a80032b5d3628c55000c77416ec98aa0008ed82dd931540090fd0a3b442a80ff1b18975885500d6373aec510aa00496f8754a21540034d90ca9442a80031b9d9528855000637a90ec90aa03fc6c625d521540012f100baa42a80121f219729415015636312e5282a02aa6e86d8a505404f8dcedb14a0a806b9ad83629415000e373b0c5282a00096f825c650540018d8c4b8ca0a80121f61c61941500063ab88c3282a000c5f7394d65900030f90eb2aa5200069b2096554a400247643ac4a948004a6c85589529000193887b9ac32000a37a1f73586400064f426e6b0c8000c9d84dcd619000193883b9ac32000327d0373586400045f43c86b0c8000c9f7390d61900011ef0eb08c3200063ba0b769464000476c16ed28c80008df835d951900051b906bb2a3200063ba08765464000476c10eca8c8000c3d65dd1519004b33f0eb9c83200022fe1d639064012e4f39ac720c800f8bf87586419000153f06b0c8320003279cd6
  | 18 => 0x84019b6e7b82ca90803361cf705952100734296e0b2a4200c6c521c165484018f6ea382ca908032edd070595210065c3a0e0b2a4200cdb731c165484019b0e6382ca908033adc8705952100734290e0b2a4200c7a851c165484019d504382ca908033a608705952100675a90e0b2a4200c7a521c165484018f0a4382ca908033a148705952100634290e0b2a4200c78511c165484019d042382ca908030f5d754d91210045fc22ecaa242008df835d954484051b906bb2a8908023ee0176551210047c402ecaa242008ee86dc954484018baeba9ec6908022fe117654d2101c5e422eca9a42008df835d953484011f700bb2a6908023e2017654d2100477436e4a9a420087f855d943484090f90abb286908023be097650d210047dc02eca1a42008f8805d9434840517d0fb22869080aa7a0f6450d2101c6f43ec6a1a4203a9e84d8d43484030ff0eb2ca2908ff1b9c965945210053c402cb28a4200c6f65dc951484dd2df0ebac42908ff1b9d9758852100c76c3ecb10a422fc6e75d9621484091df0eb2c42908bf1b9d5658852100574402cb10a4200ae98214360484011f70eb00c0908029e215601812100636292ea302420487f875d460484018df04ba8c0908031b20975181210063610aea3024200c78805d460484018de40ba8c0908023b61f521812100636baea430242018ed8788460484014dd0b108c0908031b5d6211812100574c04423024200c7975d406048401cd6a5a80c090802ba60850181214cf34290a030242028bc87591439400553906b22872800e3721d6350e5001d4e422c6a1ca00097980dd542940012f301baa65280031b14b725865000c7743ee4b0ca000c6e85dc961940018db0bb92c3280031b147725865000637a86e4b0ca00087e8794961940018dee5292c3280023de1d6118650154b7c3ae528ca00087f8758a51940558dce4b14a3280421fe1d619465000537c12c328ca000c6e725865194001ad4e5384a3280521fe197094650006b4b92e128ca0028de83dda41940011bb07bb483280023be09765065000c76412eca0ca0028de831d941940011bb063b283280030fdd564506500055a40ac8a0ca0038be84dda319400117b09bb463280023be09764c65000c76412ec98ca0038be841d9319400117b083b2632800317dd5634c6500056a40ac698ca000c6e525da21940012f700bac43280031bdd562486500046fc1ae3b22a0028dc835c76454001968c838ac8a80022fe1171d8d5001c5e422e3b1aa000cd4631c563540031dd05bb286a80023b60b7650d500064e21ceca1aa000c9c431d943540018d8c5baa86a80061f21571d895000567c1ac9b12a000acc8359362540015cf02b26c4a8002b920564d895000557c22c7b12a000aac8458f62540015cf02b1ec4a8002b920563d895000746a1887b
  | 19 => 0x2a7a1231181310064eba4623026200ad9808c4604c401972e9a00c098803a6d0f40181314d74c218803026200a6d8219265884014db0431ccb108030fdd254596210062fb9ca6b2c4200b68805c9658840187ee93a2cb1080317dce73596210052f41e82b2c4200a5d83d05658840147d0998acb108028f61331596210063db84e0b2c4200a6f825c1658847f4dd04382cb108029b60870596210052f41880b2c4200a5d8310165884014ed02202cb108029d60440596210051f42060b2c4200a3d840c165884014ed02182cb108029d60430596210043ec3ccbb244200c5e7399764884010ff0eb2ec910803179cd65d92210062f32ae7b244200c5d655cf64884090ff0ebaec910803179d673d92210062ebace7b2442028df875cf64884018bceab9ec910803175d573d9221006373aae5b244200a9e83dd164884051bd06382c9108023760c70592210043ec2cecaa442028de839d954884011bb073b2a91080e1f21d65552210043ec3ccbb1c4200c3e7499763884010ff0eb2ec7108030f9d165d8e210061f32ae9b1c4200c3d655d363884090ff0ebaec7108030f9d674d8e210061ebace9b1c42038bf875d3638840187ceaba6c7108030f5d574d8e21006373aae5b1c4200a9e84dcd638840717d08382c7108022f6107058e210043ec2ceca9c42038be849d9538840117b093b2a71080a1f21d6554e210064e21eeca1c420487e859d943884010fb0b3b287108022f6127650e210046ec1ceca1c4200c9c435d943884090fd0a3b287108021f6147650e210070e21acaa1c4200c6e65dc943884094df0cb2aa5108cb1bdd96554a211fc76c36e2a94426ec6e65dc552884ddaceebb8aa5108023b6187054a2131e37328e0a94423fc6e72596518845f8dccab94a3108065be1d529462102537c32a528c4201c6d7654a51884016cf02a94a310803179cd65906210064f39ac920c4200c5e655ce41884018bacab9c83108031b99572906210071a20acaa0c4200c3e74596318840187ccaba463108030f595748c6210064f3a2c718c4200c6e655ca3188401ca862b2a631080237e0d74982210146e41ae930442008bf845ce608840717908b9cc1109bb1b1ca655822131c7643aa4b044204c6e7554960884010fb0f328c1108030f9d265182210062f39cca304420087f87594608840187ce8b28c110803179cd65182210061f32ae83044200c3d655d060884018bccab98c1108031759573182210047dc3ac030442018ee829c365484018f0ca382ca908035a148705952101c5f43ee8b2a4200e2c52dd16548401c58a43a2ca9080a37a1f73595210064fba6e6b2a4200c9c74dcd6548401c98a5b9aca9080327dd073595210064e3a0e6b2a4200e4c521cd654847f4dd0bb92ca90a879914b71595210065dba6e0b2a4200cb874dc1654
  | 20 => 0x56c10a0b246200ab681141648c40156b02282c9188028fa1420592310051ec2840b246200ab681081648c40156b02102c9188022f612765523100c77414ecaa462008ed829d9548c4091790eb22a91880ea7e196450e311be4fbb2c8a1c623a8dd86dc5438c4e593cc9b8a87189cb65dd37150e310046ec30e0a1c625fc9e641c1438c40117b0f326c5188030f9d664d8a310061ebacc9b1462008bf87593628c40187ceab26c5188030f5d564d8a3100637baea4b14620487e851c1628c4010fb0a382c5188031b14b7654a3100636292eca9462038be841d9528c40117b083b2a5188038b1496454a310064f326e6a9462018bc87591428c4018dce4b2ca3188032b9c964946310071ba8ac928c6200c5d655ce518c40193cc8b9ca3188032b991729463100656b22e528c623ac9e73592418c46993cc8b9c831880a67e1d439063101d4fc328720c6202c9d7650e418c40172f02a1c83188023be09759823100c76412eb304620087f855ca608c4090f90ab94c1189cb271ce64582312fc6e43a86b046203c9e7450d608c40117b0f320c1188030f9d664182310061ebacc83046200cae72990608c40117f0eb20c1188030f9d564182310061ebaac83046200cae72590608c40195cc8b90c1188032b59172182310047dc3ac03046200c3d74953654c4051bd07386c8988032e1907059131006cc218e0b22620487e87dd5644c401c3887baac8988038710c75591311d54f426e6b2262018ee87dc9644c4018deebb92c8988031b1d772591310074621ee4b226200c6f751c9644c4018d8ea392c898803a310c72591315174a21ee2b226200c7b75dc1644c4018f0ebb82c898803a610f705913100675b96e0b226200ce872dc1644c40193886382c8988031edd470591310063c3a8e0b226200cbb741c1644c4019b6e6382c898803a610c705913100675b90e0b226200ce8721c1644c40197508382c89880336a0c70591310066cc18e0b226200cdb431c1644c40197486382c8988032e10c70591310066c218e0b226200c98431c1644c40197082382c898803360c470591310043fc2aecaa262008ef825d9544c4031d904bb2a8988023ee0176551310047c402ecaa262008de86dcd544c4030fd0fb2aa4988069ba0b65549310247743ec4a926204a6e85d89524c401b8862b94a29880317d9773545310145fc3ac920a623ac9e73592414c40157100b2482989ca67e1d748c5311d64f3b2e918a62028dd87d92314c46993ce9b24629880e37e1d648c5311a64f3a2c918a6200ad880592314c4015b306206c0988023ee1d60181310055c422c03026200c9c435d0604c40717f0eba0c09880327e0d74181310064e41ae83026200c9c315d0604c40197100ba0c09880327cc174181310046ec3e863026200c9d74d0c604c4051bb0f188c0988
  | 21 => 0x821c165904011db04382cb20802b3a0b6598e4100566c16cb31c8200a9d84196639040153b08314c72080317dd75358e410046f43ecab1c8200ace82d95639040159b05b2ac72080237a1c6558e41005cc402e8b1c8200c5f759d5639040159d05a8ac720802b360b5158e410052f42e42b1c8200a5d85c85639040153f08b82c7208f6a7a107058e410054ec20e0b1c8200ace82141639040159b04282c720802b5a045058e410056ac08a0b1c8200a5e8508163904014bb0a102c720802b5a042058e410056ac0840b1c82048dc8758d539040553f0cb1a87208f727dd96350e411a45ec36e2a1c8272c9e63dc543904efb2ee7b8a87208022f6187050e412be4f318e0a1c82008dd8798f62904018bceb31ec520803175d663d8a410046fc3ac7b148200c5e7558f62904018baeab1ec5208031bdd75258a410243f428e0b14820087d851c162904018d8a5bb2a5208031b1497654a410146f418eca9482008dd831d9529040193cc7ba2a520803931496354a4100c6e43ac69948200c6e72596519040187acaba4a3208032798d749464100667392c728c8200e575158e519040199cc6b94a3208033358d729464100477c12eb30482018ec825d660904010ff0ab94c1208121f21572982412be4e3a4c6b0482578bc8750d609040593ce6a1ac1208023761e63182410062f3acc63048200c5d7598c609040199ce5318c12080237e1d63182410062f3aac63048200c5d7558c609040199ce4b18c1208033398d721824100666b1ae430482008fb8758060904018bae729ecaa080a2fa1270d8d410066c318e0b1a8200d98431c163504030fd0fb2aa4a08069ba0b65549410247743ec4a928204a6e85d895250401b4882b94a2a08030fd9774545411d4cfc3ae720a823dc9e765ce415040717b0fb1c82a08eb279cf63905410055cc2061b0282008fb8758060504015b106b00c0a08032710d73181410146fc3ae63028200c9f845cc605040193908b98c0a08032710573181410064fa02e630282008bd8790c605040193ae7218c0a080e2f61e41181410054f41c823028200c9d73904605040157301208c0a0803365cf30181410074d21e6030282a3e98430c0605040717f0eba6cb18803279d173d9631006573a4e5b2c6200cad749cb658c4031df0eb96cb188032b9d172d963100656ba2e5b2c6200a6e82dd5658c4018dee5292cb188063ba08705963100476c10e0b2c6200aae82d96648c40155b05b2cc918802a760c65992310054ec18c53246200c3f75d51648c40117d0fb2ac918802aba0b655923100556c16cab2462008be87195648c40173100b9ac9188030fdd6755923100557416a2b246200aad82d45648c40147d0b90ac9188028f61721592310054fc1ae0b24623aa9e831c1648c40153b06382c918802aba085059231005
  | 22 => 0xb80c2a100a3720d70185420243f42ce3b02840087d859c760508051bd0738ec0a10023760e71d81420047dc3ac03028400c3d74953654c80717d0fba2ca990030fdd4745953252e2fbaee6b2a6400c9c74dcd654c801958e9b92ca990030f5d754d91320243f43eeab226400c3c75dd1644c8018b8ebb9ac8990031b1d772591320043fc2aecaa264008bf845d9544c8011bf06bb2a8990023be0976551320047bc3ac230a640087f855c0614c8090f90ab80c2990022fe11701853201c5e422e030a640487e859c7604c8010fb0b38ec09900e2fa1271d81320045ec24e3b0264008fb87580604c8051bd06382c9288023760c705925101c5f420e0b1ca2008bd841c1639440193887bb287288032710d7650e5100c77410eca1ca2008ed821d943944018dcc5baa87288025d6077550e510056741ec9314a200acd83d9262944014db0a324c528802aba136398a5100556c26c7314a200a6d8518e62944016d100baac5288023ba1f6458a510056741ec8b14a200acd83d9162944011dd0e322c5288023ba1f6358a5100557426c6b14a200aad84d8d62944011dd0e31ac528803a350c4358a510056741e82b14a200acd83d05629440155d0998ac528802ab6133158a5100537c2ae0b14a242a6e851c162944014db0a382c5288033a5c07058a510056741880b14a200acd8310162944015cd02202c528802b96044058a510055742060b14a200aad840c162944015cd02182c528802b96043058a5100d37c32c4a94a242c6f76589529445f0fb0db8aa5289bb1b98b7154a513deb3b96e2a94a20087d861c152944a78dcc4382a52880e3b21d6250a510147643ac4994a2008df835d260944051b906ba4c1288022fe11739825101c5e422e7304a253c6c7598960944a70f90ea92c1288071b9c9525825100476c3cc4304a200cae74988609440195ae9310c128803339ce621825100666b9cc4304a2008ef87588609440195ce8b10c1288032b5d162182510066739ac4304a200ccd7358860944011f70eb00c12880a2fa1f6450d510154f41ec8a1aa2038de87d8d435440753d09b1a86a88061fa1670d895100674310e0b12a200d68521c1625447f2df0eb94a2a890b1b9d972945510243ec3ec528aa23fc6e72d8a51544014f30a106c0a88023ee1d601815100574412c0302a200c6c525c860544031df0eb90c0a88031be1572181510063642ae4302a200c6c515c860544018dea0b90c0a88021f61e521815100636b94a4302a20487d8794460544014dd05288c0a88031b5ca51181510053cc04a2302a200ce972c806054401cd4a5900c0a8a939a14820181510064eba4e7b2c82028df875cf659040199ce7396cb20803335ce72d964100c77c3ae5b2c8200cce735cb659040199ae6b96cb208029ba0b755964100637b94a4b2c82018ee
  | 23 => 0x13000000c000002000804400000700000400040000000018000000005800000400000100000000260010030000002005800000a000000000000a000003800400200200100080120000000018010005002800800000e000001401800600080080000010060018008001000800000200200100000020040047bc3ac230aa8008df835c061550051b906b80c2aa0023be09701855400c76412e030aa8028de839c760550011bb0738ec0aa0063ba0a71d815400476c14e3b02a8008fb8758060550011ef0eb08c2a98022fe11701855301c5e422e030aa6008ef825c06154c031d904b80c2a980e2fa1271d81530045ec24e3b02a6018ee829c76054c011db0538ec0a98023ee1d601815300636b94a5b2a86008ef825c76550c031d904b8ecaa18063ba0a70d954300476c14e1b2a8600d8c43dc96550d5987eebba2caa1aaf17dd7735954300c7743ee4b2a8600c6f751c96550c0195ee8392caa180333dcc725954300636baea5b12860087f855c76250c090f90ab8ec4a18121fa1670d89430043ec2ce1b128600d1c43dd56250c011df04baec2a18063b20975d85430043fc2ae5b0a860487c855cb6150c090fd0b386c2a18021f61670d85430064e21ce1b0a86018ee829c36150c011db05386c2a1a8b2d5d361985435566ab9ec330a8600d1c43dd56150c01b1887b92c2a18036610f7058543006cc218e0b0a86008f7875846150c01a3886bacc0a18036310d72981430047dc3ac0302869eabb845806050d535b706b00c0a18023be09751814300c76412ea302860087f855c86050c090f90ab90c0a18021fe1571181430243e42ae23028600c9c435c46050c011df04b88c0a18063b20971181430046fc1ae3b22a4028dc835c764548051bd07386c8a90023760e70d9152006a6296e6b22a4008bf845c7635480717908b8ec6a900e2fa1270d8d520045ec24e1b1aa400d2c52dd163548018d8a5bb286a90032710e7650d520064e218eca1aa400c6c521d943548011bf06ba6c2a900a3720d74d85520045fc22e7b0aa4038bc845cf615480717d09386c2a90022f61270d85520146f41ce1b0aa4008dd839c361548018d8a5386c2a92871d5d7619855254672b96c330aa400d2c52dd16154801a98a5b9ac2a90035a14b7058552006b4290e0b0aa4008f7875846154801a58a4ba4c0a90035314973981520047dc3ac0302a49da7b85580605494f5d704b00c0a900237e0d74181520146e41ae8302a4008bf845cc605480717908b98c0a90022fe11711815201c5e422e2302a4008df835c460548051b906b88c0a90031b14971181520062eb9ca7b2a84a6c3f75dd165508051bd0fb9acaa100317dd473595420064fba0e6b2a8400ccc73dc965508018baeba9ec6a10023de1d61185420043fc2ae030a840487c855c061508011bf06
  | 24 => 0x100040040000020004006004003800001000100000000020070000004000003000000000600100100100000020010000002001001001000a000008004800800a0000010000008009002800a004000801800400000480040020000018010000000000800000e011001000c018006001800c01400e00100080040010040014018006000801000a001002800000c004003000000c000000000402800100080040040020020030012016001000c00000a000800001a00e000801000a00100280080000080000000000003005800800000e00480000060030000008004000001801c00200d0078018000002002801000000f000000800200100100040000030010004002009000800001200000200480040010010000002000001800c006000000002000600100000080000190010018000000001801000e003009001400c0000000034000003007000000800000000040120000040000000001000802400000700080000060040000028000001003001801000100480000080010028008002000002000000000300180100040020038028002002000000801e000003000000000300000280020000020030002002000002801a0000008008000005000800400a001004800000400600080000040000008000058000000000002600100a000000000a0028004002000001800c00001000080100000040038000000009000000400000000080000040090018000008004000000400600000900000060030020028004008000002c010000000001400c001001800000c0050028004000001000803c006001002800001801a001800000c00100200040020020008008002004004800400a0090028004000003003000c00600500080000000000000024006002000000402c000002000401600600200140000070020004004000003800c004004001800400200100180000000060020038008000000000000200000200000020060030000002009007003400200100080000020000078004000004001004000e002000001800c00000100000000000008004004000000000000400000000000100030108010016004001800c006007000000400000900000000020010000018000003000003800c0000028008000000000000403a00f00600240000110008000002009004000401e0000008000002000002000c01400000080640060000000000000000000001800000000000080000010010000006000002801000200f00380000120000018004032000000002c004005000000400400e0020074002000000800c002000000804c000000000001000a0070010020000010001000c0060000010004002003000800000e00300000a000002600a802800000400e0000016001007000008200100300140040080018000006002000002800400e0028004002001001000
  | 25 => 0xe96c400000000000006f84840000000c6eb0d18f88a0d400001e400006f240c2fa80000000002e00000a7000052e1fd80000f012e8000000000000012d9280004ee000068c20d6250d2d1a867c65f0001786000142a15c0fa1f61dea65ccf630c59da9e8eb69b35eaa240000baf3de8760b060005670778032ba21bdb00803e46c4e8168053c0004ae1ebd5a8b2d20b000199c9e30000e792907a625123255ec6e00f31c2c9f090541e1ab40002620b480001fc94d60698992a64c8000155d1121ae03b8cd000026a0000001594a5859d0001548000533a178b5278155b84b54700000000000574b7300000000000000ce000038c572140805444a6350000001546000314a6880006d34ce2efc88c0004b21c797b40000001fb0000bd112d094168273b00c1248f00aa845e2bc400068b481239973a6e8360a22914c03245ba2fd8a488e466a768612b6f58d80011e270f157090000019235896bc9f469158830fd1a490430625008645df0040964baa52544b215000000000080160000000014008000001800000600400300000000060008008000004001001001c006000801400000000080000000000030004004000000001000a00f000008801400c0018008004006004000400c000000800800800200c8030012000000000401000d0000000002001000005c00e0020018000000014000000c004000004000c0260020010010002003000000400600a0000004000000005000c00a0030018010000001002800400c000001000400e0000010010000003000000400c027000000000c0000020000002008001801406000b00a800c002000000000401801400000100000030068068000000006005800400100b0004000001000801c00400000c8008000000001000001400800f800001600d003000800e0150000008006007004800000400d002000c00001a005801c01200c000000001e0130038000010001004000000c008000800c00000200380440000000020004002009003002c00e001000800c01000200080000040000020050002000010806400c0000008008030002005800000001100080040000010070008032006003007800000200100180000000010000000000003001c0000070078000012003002001400401a00000040140050000018000001003800000400a002800c000000002802400200e000000000400000280440300030038024004003000001000c000000001401e00400980080040000000038050001001803000000000600000000000048000004013001800400000f0008020004000003002c016000000802803c006002000c00400b002801000400f00000000240010040010000006006800000000000200080020020008000000002001005c00c00e001000c02000400a001c00a0020048008004004003002c00000
  | 26 => 0xf9800093200015a0e3a00000019a8000578042a1580000002a914a97fa85c3a680006f477e3f916ec000a1b406000038a0005c28f9c9306ee1b59e8945691c2fc00000000534a817b00d20000000db889633d00000000005263610afc6b6c3d5bb80017e01c3125a840abc4190001198c360000000780f2695500000000004701e132695ba2c437c9e599c80bb5448000000000000000000000000006344d200000000000008f800023c00005455dc90fc37c7b00000aa02b20753eea6118d00391ac0000c9263800015e80009960b50ae000090f00020d80006330001a7ce32cd82c78268ce000019db20ceca37f2c60f7465464c380a66583019f0d60f540000003cd1f841289ef000000000000000032800007f400010ec9b44f30002ae04e20ae6799ad4c329b8099285c0000000002dfc7b4ce81a281c4dd2694000000000003510005c00009fa09408055d08352ed834058e70509d00e039e37245527a953c00000000009647eb43b0bcc5a631962b0dc0a062a158d064c0820e74b92c38b6ec894051a98d2e93930200011dc3bb1750af0e0096e4130b8422a6d24ab9e64d7035506e80989a241b0fe859001ea9200025051f8c864e000016525414e13274000000190a718dfc69328f80005dcc2360780011aa30147a281806637114e10800009df011acc4b782101e81d7c0c65242538848b149ce25d810088e0813d892f400067f00000000000000fe06814eec430001d4000080f000000124a9311360904ecc7f900000000000001448000b7e96a0bd00000005e642416a07de3154519734ea80001d386a00008e300021800e09461d786f0000bf107c95380605481498001266b60657032cc0e63f3230cd89a80000000000a0aad257d32c52400000001d9c59000000000006304dc03c1c810a0b4d000165800026e000323493e485000211400000000000013b624e1682fe59440002ad08800001ee34e86140c400000000013f600000032b47123174388fb471a4370002d7410600013791a400041866c80007ec60653e0844bca00015997b800097962aa17585e0004ef264c000000000049000009d00000016d69aa0002df018e30d000012513600029084980004be03600011b68c015330780000004250350906a0763f9dd197a11d41d02b4af200000030d00006c4604916d39e3671a70000d924501b680008c613d075177502eb080b72ea526a000000000000000037a80000004cf61e1b511307520000a500000003590000000c6c4331e3c00000028f17b55843c916b00000005c7000000004a000000000196e0003bc011107200058980014a67f15ae00000000000000000000a9a00000016e037704b9084000157553a8900001dc00000010f8000000000000030e1f980000000005ec8000000000000000000000030
  | 27 => 0xaa9b8d80cadb3c51270eee45300019b0000a2044618ec46cb3443f279578c51307928882ec0002278a28000b6e23412b960201e048a0a00004390000000e0484400000003ae00063e8000e6476d2401a8cc9cbe6143800118e10800025386ba05641b99c4b10a70000000000080908904d855a7ee1fa02c5916b7600027dc000afb2741b2c4ce0002152ed00004f46788f2d6245125588960000c4d0000a1971a2b5614958945e000000000000099e000082d3060005e2b38c816a5d00000000002342daac2918600000009d498a1c10cba0b800000015531012cea1e3ac9cd525e23219f00010060000001df5902000000000136a62704c9d0d5aea806020000000cdd5ad80019de74e654801d69415d411a0096e4c1010e1310b462964381c84d20261039800156000000025c0fb40005d1b36914e27d5fb2390006b3c252078d706aa149624407d68ed2868e58e8e3a1625afacfe0a451bf292c0004f50f4a510c8e21d0000fa8000000000000175427a000000000000000021b400000000001f000000000012cc4aa0000000000d8e0005c62b0033403f0003144a5e0004110f3000000058f0000f1200000024ed8c4b112788000afc00004a8200eacab200002f515214516d975d41200033a157479c000564000088870816c0e48d0235a4c830a800007b31214fc0009d8582000000000000000000009d5017800000000000000018f0af234391b800097b61c8e753149750c40fec000aec00016400000003f02ea189c00000011dc000000000000000000000000000000000000000276c1611480016ea8923ec000028e47100000000006bc0001d459089c900000009de77150e8000c2c0005282df4af67831b01604732b0535e80000000000001c992180002f18000fa600040880001f6000669800064867261580016002420b300004420000288000000000092800000017d4f4013c000914116295d37400033687b06b204c48f060c0000003600000000000000000156a2222c22a100000002468000c8aa744db05e0ccc66502400000009760000000a6800021780000000003838000000000485800000086b41280017e66092ae0fc886c000000166000081600000004e6139185a51400004e00000005e098027807514760001c2800133e0da34db0300000000001c90c28b0332e0468c22a1f1669268fa23f844f00000007182ab228491800044fac08000aab5a410d48241cd000290c82abcf1579f50f5c27f38827488b8b805389e2c00036f17130446ccc64080ac180000675010f3c600b780e5035419a7a119f8f1c0000002f9af6c2ac000000000111ac9b0000b180005433d280006a26d100000003e6c251c40000a560001d62b2c75461065a860546e0003302b101c0000409b24421899b16a8bec00000004300000009be64e19d40
  | 28 => 0x53279c5ba00017300015dca8c250800007400000021a80000004c28000fb200017d0000000000000084d4240003511218e0800002aa69509c0000000000000c2d11501ad94e0000000a1077241024b0000000000000033824085351317dc6ae36828e91607b87e504e218d4907340482a2000021600000012960004400000cdc0004b69a3c93600037d8000242744539149cf466302bb27e0cb40000000000f6ebe347112783806762aa8000a6e9eb5c71b20d8c22734331b40004ec403800186679d4f880018ca79e00000008ce168417800000046b0238000000785534a8503166b44de04152520ac3ef3259248000519b23d5cecb6316aa3849e7900002b65702a231482a14bfe13e64caab8000c1f00021b986038c22523449600003da000000043a4d880010f4279663883d17c6bf3e503e80002b22da332420c11c40a2498cf4a1310100000000000d31f1800000014a9024000cac008819424e59762213a812606f42006e82a49ab5f50000000ccc1b6280400000041895b0000000378232d5f802018214d48c4bc7490850cc3ca040aa8e2d4380003c3942943036a5350f4469e2ab1050af566085923d0bb04ae62f0002a340004612cd000000000000002d586a3872d99c58000a9f118800076a595000300c3ca0000001cdc4767c700000002ea06d20500008102cf3070000c406b631f000000083f3a018b07280004b4047802e29f1cfb314c24441662014800000016d000000078d1548860000000441b3080000000002a0c0006575eb00009d600000000000000005d89c8911e0c800000000000001248a749f2b6a28588fce240763ac16486605f658b83d55c4aef2d100001b614021e94805ea00055c80000001943eb80000007b35b4800019434a20889a0e18b9f04110c40000000001f10cd600000000000003423e7ac311224cb00022b048abbe0002b240004e446f88b45ec28d000060000000053dab9464c445521051009a00000021bc000bd307422189c47d63efacf4c06000000000000084131e9690000490371317c2f89bf36c9584d1a48b0a3086564c9f631d011979c3493d500017c296b5f909b4f5616c48090752c24fb2519d78c0239c531000000000054e800021cbfa00003301c600063c8000000cb949f0000000000481a9300002ac5fd800064a0003f38000f92b500000000f2e0002161a48000a4415d91bc0000000000000428000507aca1060aed4da2bac0000005c122050b40000000000000000000000000000000000000000000000000ec25fb4d6a4a94000000000000b3200000004659ac1d100000683e40000508000000000537000161621734529a108e5ab2408d10e4e0005c400018ba2880002e3c00000000000015a27f50da1a1023ebbb1a013d89a413859b269969c5494b78c508506005
  | 29 => 0x49b000000000000022ad5200f4452a4b93827c30000b645183ec41690b8c9e5c1635ab04436b2c0253378000000563971183264005402c8000bcb5b683256866f466830980001d600014b400006a0000f800000000002608000000000221c00000000022d82ee0002529ef8ee056e2a3192d9d60003a29a853e60000000000c260003418f342bc3053c8a0b168800014b80005f80000002290000000000000000074100000004e80005f72530b00000000124d0f60000000d8400018a00000012b2ad500010c19da00020b9ee40000000001bd8d9e35f0000001048a310ac08115ac98b36800000000000600a440003d94030c895f22f25a02d158cc3fa4f82900f0ca2e1291e81670c7150c82e8cb20002b2b1b800000000000014b67a70000000000be45ffaa286a41f5493b16c71457500700014726a9505ad4800010b096233c2a23e21ff8000000abb2ea0000eec8bb0002de835e41e49f8af894ca272e615c0e46a0500014ccb0a5f03a50e0cd9881b0001cd8bd09cc46814b8354b9e03f92d88a29d714c1f14000cb432c30e018624640fb170ed84ee24c85711d8b911cd8a956ce14a0189358124bed2810970f1c00000000004c000025e00000001e748b8ed0172000321a8b44d600000000005c66e159000019ca1990000000e149bd00000016660004ff00000007cd40e1ef00000000adad886ec5101288160aa85c60001f08000000000000044c0000002660aee77200000004a60000000000952ca129ca654b8a9c4000000000000013300011647530001bad8a0519000000000000011c8000c3000001b80000007cb0000678470a4f0aa1244c2e000000000000086223680000002a000018a13524791fba8d800000036280003aa00059ab05cab04d341c1ccce1c1172d90000038000000255064659f098800102ac481a401740003981d825252f4515419a04189e173005219d4e627b0000b3037019500000017304de06c9c952569873aba1b192e29b1b4841cb3c2c51e09771474caa48c8000050a795d9000000000040d0cdc00038e25fa94919012e0000000b42b53010817c8840004ea2e54edc000000336d45400053080000000001e01c5c0009370fbb294000a990b799e43905440002d50d1c9123f51b9ce7000000000018480000002a2c0000000002358a3469a48b1d8139456065db150184ba12ec9ce556c0ee54c000174aa6444e8c18b7c5d0068aa8887c0002fca28000094700028348000000031ffc000c0a1db00000005c200028c135c1e20f503d865c79b38fa3e41cc8e75e80001334a7644291d426600032a0fa000010f62f037862671b10d1e70774aad04217f90a42df357a5897d00a42b792e49568584ecb2146346311ea000036200049e2488ed6208145822c8fe0001db86dc0007e40000000c8283e3058434
  | 30 => 0x116081d07e15f1348ad00cd846cfb83203d626b09500000ef9a551280003a12ae903c8005ad033d174c410a41c18c040160f680000008c42fd04d400000047f29bcc140005ba0000dbc8460f8087816e000256000089ccb32a580000000000000508000b32054a4688f000000012a800074859f8ec40000000000000a8e00057ea7e4000000516011411e0002c5800018c5282f4b28c00000000000000000000000ac400000002f00008e64e90000000a228ae3da87f866a31c00019e0a9a00c65d15fd1ee42400a210d1624d94542bd00860003251af8000c151250000000542361800026e0005e200000008d70002ee8000ce146e80000000002f0000000000000000000000000000000388000635000040612b37e80000009cd00000016ac42352f8d1d930c82496931c34294f45a198c7ae38f1d1923d1e439104b21a195e4e75208390012c0829f0000acebe54be87c4bf80001a0800000000018b05b40000005d3188c000000405800123a0000001c5583a0000002784bce02d3cf94a52ba0003feace40000002f5000000083d20313dc35abca49d199cbe4000540ac659000000002f08e7e000484000000000044c8c6ca8000000033c87481600000000cd00003988000000b2300031842fc5c90003398000000000230995600039f0ae4000cbf10a8000000b5e5a88001782aa529d973c1542e900033c00000001bc04512e83ee4d029691d6cc3629a145628b610bc98b91389060000000baca4a0000d500b8ae0000015000069803a154432000000000005d64940000f6d4fa00043b90104743815f016e4856713000267586e0003570be06ea523000000000000023293413864ca2261788000c760002f3000000000018683f64522a8000000000040917d065a00018127b000014c626254437e1d200000000004fe2a98890cc26ea57f0524d1884900011d80006d82d514200006f73b419597249920b2ab611d4b1848481917be95f11f3220a1e969000323000000000000f0000000000000000015f20100018c08973fd20800000002600000000000000000000000000000000000f7000000100aa3c00024d00004db55f84fc0006da000000046accf11eaa0800006100000000001a74f480000000ed00019f55985fd4ab06ec00000000000000000000000000000c050000ca40009d64b3000000020e3aa8000000000000000131811827929e1578b2400023053da00008219dcd10c2e5cb000092a5cb4bb8000000000000000000000000025fd1fe00000000001a668200014300000003aeaca944a3ae1960b2c000000326828c0000000002cf8806bab605872d5c28c50a706cd54c7ad0001b7c0480000001651842000567b30000000027283c45687b6195868d51e2e50000ee164ea562bead3003a90a4a1a8c80000000d48000000004
  | 31 => 0x21fe80000000000000000ca60000001f995e000051a32480001ce2d39fb47bc0000000000000b25569a56c00019d654167405c00000000000001eb2b48000dca45e4e4338136e14b28ba3d840ac280002bfc00084c06b2134b74cc62e880018ae0222800f90000a9c1a18000f1000000018340000363f1800000000027018e538a8e563a00000006365de23197ba9e20000b4800000021a0001656cd53779de47e0918449ab15586af3334987d69e03e28b26c80840be00031643fe000000000000080e5c5b32816000000017c45aebef0000001862c2000000005924142d29fcc00061546e000000085f4740000a7892837880000000005dbaf7000058d3e720d0ef847c1940bfc000000376800186402a5c80568000b1d00000d02f600000003b000072e61d80002520004f015ac94000067380000008d307c27f43de0000000ea000000000000007c231e6392e4c40c5223980000d0a86404c00ac7340e528e00000006f30b898f0b123391c9ad8c0000571fc8efd5b8a66000074c98498905122cd1348fb05c28386620272b311d018ab7e52311f40002b0000000101000000027740000003b1000148e74613f33b99ae0000de800000000024e800000000b00000000000001ec0b009fa0ab25a8ba04ec00013bb0694ea6ec0e12d7c33000045780000007f711994c00007ba00012dd5f03335ec000112a00000000016960002240584000ca654980000fc0005c50764b1c0fd64a8b80e50c9012daa50000bb0372097c00000000000016387fe0002a5800007a2af80013728cc532a638cb6c42535ae1ca082d12708000a361fa51e8b7800000000000010fe000000000000085b04f80009f84ed00000000004c30b9000030e5875fe0000000514000103cd0048a12f2d9000024700027b899c0005b308ac41200025c07e152e457000272c3128ef0001eecfb60000000000000c1b000271c22600057a9151536c0003300007943c63e90000000000000248c00072d000006c9ba3a938e31158b05da0a0800000074c1fab3b15cc5361328cc80dc73c1318c4101ab9b5fa108881c1b5176a8fd5b46215f480008c835000031e877c00000000011d205a00000008ac00d0000000674c4647ab2c80009910a80a650d22370b19fed9a259135b81c8bd60eb25680000000001be80000000000002f9d6f60004ca1e54b3600000033890086f85751a957383033128428f04b2222680012bc9e42a503041be9af54898ac58665105a02f0a7a70d4c0917591420c1e20f7c54e0005d01ea0ad4b6815b9f88ca4608631a438b0c3a20003370000000366800000087d0001b38bb030a000000000014f3ca000000000000000009629e633211f9692395000073065e0000001c4411a24c20fa7fd1c0c7e50a97214a800011187a13a29fc1de1b5cf7e1f4554800
  | 32 => 0x40e0001f880017a40000002d94e2809e3448bc40009070000000db6c872e99aec5e800004400016ae2b600010980000000fc80015c8000000040000059c0000000f1800000020a94069f4000319c852000528942400035c4672b34000000384933576c96c02d9ec92c098807786c968c7645598000ab29654279cac7869a300000000b2460000000179a0005ac9d680005a600004d000074f2e50fa4000254000000035698d26080016d800000006100000af3e00000000aaa4c7aa5549200048680000007d000000004f81b6000000000000017c91a8d3200000011c980e00000002940003270000000000a6d000090d982a293b49ea5422c7b5040000000000000000000012237d00009cc0001c30b9d5bc0000000000000aac3f78b513eaa5e000000072e77f425ae64c886ac000040c000000122117c866b210b39c0c3c882158b1a7800000044100011c20005ff00000000000001ae40005c32201ff0df811135986891b0b0735500000000000000000000b42439a0ac00065d33f2288188c0e08b237800073d5e495b54c000035800018ea000000026c0003740002f891fa60501e8008c90270331048d34e00009e332193e3b356f83a45346dd21e021c6e6bec42a9d251b4ccd2b98c219966426008d4d5eec49445814154087463b8d3570c5ac339af509be0000c622d45460a75dc2c7d76a5de53180a40000004422cdc83493d30785ace74c2c43293612e265e0f089348f627266f9238670b9720081e59d47a44a131c17900002129cbc000bd73fc00000008bd00005d0d487294a924e07a600011e0001978a21000000030c81805b00000000120452454d4e2e45a3aba4e589b058a800000091f62d00000000000000e942a6c270813350000a871672e50a580000000000000000000135c000c141178000ac600000030d8de440d1b19c6831e4135c4b0883a04435d20000cde45509780018e600014189211f49131b10000000a7e0000bbd15a56451aadc47ac1b0311197cd5676a64f00010326962660000eea00000000000000000001f552fc33c00000000009a10c704c074c292095022530c0002c98eb40c000000000008b20000000000d943070002abd8f803b000122062400000005340000000001d8cd386e6140087c000c8e0000000000a2828300018de6d50000e1149a91137fac3cef6c1200000000003fe1af2b1800075c4bc00000582fd14780000006dc1b280006ac9300340000bc83e52989f201a4c3e21c08c19600e20bf9fa549cb091170bf8c648ca00097480005b635425281fe2a21888e00f085ae2c112bd1e6000000000090e4270880000000a6c0000f149120000000a397f07c141900000000000ed800000000000014059d28724be02309aaa0c0ed21857800000ee80000000000000000bc20005bc800175a3b
  | 33 => 0x8e5c20c3ca1c9a860e0000a302dc46c92081ae1621650001076a7f18e938cc6877314121e40268b96522eb120053a45c1738b7a1a4203a58d76627824b9e4800a2a443aa0a582634c52aaaf4c3800000000014b2a0a5de80018d24ba3950000166000597a86821200000000000000002ba2eb8e9600000020040005713bd0000000449000141c0000e113200015c60bf51f2af898c4b400000003727b83e613241403d2008246c7f81821b200016b0bf554328599a4878000209d2e60d8216956d88e38261d18a974eb2e36b0694a98bde2d6a6ed1102c22d80725734c932a780015681963cc00005ee6ba07980008385b822d25687c63a027f8eac322cb85fb9954ca00dc421071c5829582028e404ac5324f917bcede9d33f400
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x143c1804081c00280c083008140028183c014999010d711814300513a5852dcd645480142e9614b7458d520041b66052dd94354801c0c431487650d520041b660529c3615480106e9814971181520051a640525c4605480146a9614870589510051a640515c8605440106d97a0a51181510051a65e52c80605440106e981497654a4100526a58431c163504014999010573181410042765e8390460504014999790f30181410041ba60525d9528c4e589576e05439063100526a58431c1644c40141e9710f755913100523a5c431c9644c401c0c7510c725913100526640431c1644c40149a9710c705913100706dd4431c1644c401c187510c70591310072210f721c1644c401c88431c8705913100526e60431c1644c4014999810c705913100526a44431c1644c401498940c47059131006269cc80592414c40189a74201648c53100526640315d0604c40109d97a1231181310052665f43d00604c4dd86576e0552946210051aa58521c1654840142e9714b74595210050ba5c521d1654840144e9714b735952100513a5c521cd6548401c0c7414873595210051aa5c52dc165484014699014870595210051aa5c521c16548401c2b7414870595210070a1d0521c16548401c4b731487059521007121cc521c1654840146b9814870595210051a660521c1654840146a9114870595210051a254211c1654840186a7220165945211fc1b66365dc9514840186a7520165885210051a640215d4604840106d97a1621181210051a65f52d4060484018686220175485503741ba5b825c6505400106e9818971941500041b660529d9525000189863201744c54039427a5b835c6405000109e9818d71901400050765c435d7648c00148d9710e72d9230007039d4439cb648c0014969110d71d923000427a6274586318c00106d9814a765493000626190805d1314c00109d98190704c5302be261d88050d404c0af09e96e11718c13000427a60645c6304c00142d9714a74d96200050b65c525d3658800144d9714a73d9620007039d0529cf658800144d9714973d962000519a44525c7658800106e989d561886201541b261655ca50880018686520172945200061a194805d5214800106d9819470485200051ae60651c1214800146998194704852029e1a1d88054950480a706e96e1571881200041ba60655c6204800109d9810f7650f100041b66052dd952c400106e981497654b1000427660431d943840014999010c7650e100041b660529d9528400106d981487654a100051a640521d9528400146895588704861000526640431d943440014699014876549100051a241721c96504001498905cc735901000526241741d16304001898436187050c100051a241751d562040018685261870548105261a21c205952004133868801d56248010
  | 1 => 0x34b32bb1889ab6220484071016302611942294a126952ea0001d81828012b41c3280170681308d9818801780291bac00321a062d000f19372e0cb3800b8d1e1080a7b5910a00002823802496b52d80001e9f082a3128b693af1d0f89a9a1802b1b379202132f802307802a8ea519b9158e1fb88c05800a8000002cb8208b00000003a709240525831c8000000380008000c0c0030001c08c400040804480014
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x808000240da910c521d9435480104c5432018ae8302620081a2a1900857518121
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x4
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x4b
  | 6 => 0x4c
  | 7 => 0x4d
  | 8 => 0x4e
  | 9 => 0x94b
  | 10 => 0x94c
  | 11 => 0x94d
  | 12 => 0x94e
  | 13 => 0x124b
  | 14 => 0x124c
  | 15 => 0x124d
  | 16 => 0x124e
  | 17 => 0x138b
  | 18 => 0x138c
  | 19 => 0x138d
  | 20 => 0x138e
  | 21 => 0x98c
  | 22 => 0x98d
  | 23 => 0x98e
  | 24 => 0x128c
  | 25 => 0x128d
  | 26 => 0x128e
  | 27 => 0x9cb
  | 28 => 0x9cd
  | 29 => 0x9ce
  | 30 => 0x12cb
  | 31 => 0x12cd
  | 32 => 0x12ce
  | 33 => 0xa0b
  | 34 => 0xa0c
  | 35 => 0xa0e
  | 36 => 0x130b
  | 37 => 0x130c
  | 38 => 0x130e
  | 39 => 0xa4b
  | 40 => 0xa4c
  | 41 => 0xa4d
  | 42 => 0x134b
  | 43 => 0x134c
  | 44 => 0x134d
  | 45 => 0xb0c
  | 46 => 0xb0d
  | 47 => 0xb0e
  | 48 => 0x140c
  | 49 => 0x140d
  | 50 => 0x140e
  | 51 => 0xb4b
  | 52 => 0xb4d
  | 53 => 0xb4e
  | 54 => 0x144b
  | 55 => 0x144d
  | 56 => 0x144e
  | 57 => 0xb8b
  | 58 => 0xb8c
  | 59 => 0xb8e
  | 60 => 0x148b
  | 61 => 0x148c
  | 62 => 0x148e
  | 63 => 0xbcb
  | 64 => 0xbcc
  | 65 => 0xbcd
  | 66 => 0x14cb
  | 67 => 0x14cc
  | 68 => 0x14cd
  | 69 => 0xccd
  | 70 => 0xcce
  | 71 => 0xd0c
  | 72 => 0xd0e
  | 73 => 0xd4c
  | 74 => 0xd4d
  | 75 => 0xe8b
  | 76 => 0xe8e
  | 77 => 0xecb
  | 78 => 0xecd
  | 79 => 0x104b
  | 80 => 0x104c
  | 81 => 0xcb
  | 82 => 0x10b
  | 83 => 0x14b
  | 84 => 0x168b
  | 85 => 0x180b
  | 86 => 0x198b
  | 87 => 0x10c
  | 88 => 0x14c
  | 89 => 0x150c
  | 90 => 0x180c
  | 91 => 0x198c
  | 92 => 0x8c
  | 93 => 0x14d
  | 94 => 0x150d
  | 95 => 0xcd
  | 96 => 0x168d
  | 97 => 0x198d
  | 98 => 0x8d
  | 99 => 0x8e
  | 100 => 0x150e
  | 101 => 0x168e
  | 102 => 0x180e
  | 103 => 0xce
  | 104 => 0x10e
  | 105 => 0x24b
  | 106 => 0x28b
  | 107 => 0x2cb
  | 108 => 0x16cb
  | 109 => 0x184b
  | 110 => 0x19cb
  | 111 => 0x28c
  | 112 => 0x2cc
  | 113 => 0x154c
  | 114 => 0x184c
  | 115 => 0x19cc
  | 116 => 0x20c
  | 117 => 0x2cd
  | 118 => 0x154d
  | 119 => 0x16cd
  | 120 => 0x19cd
  | 121 => 0x20d
  | 122 => 0x24d
  | 123 => 0x154e
  | 124 => 0x16ce
  | 125 => 0x184e
  | 126 => 0x20e
  | 127 => 0x24e
  | 128 => 0x28e
  | 129 => 0x18cb
  | 130 => 0x178b
  | 131 => 0x188c
  | 132 => 0x160c
  | 133 => 0x1a4b
  | 134 => 0x17cb
  | 135 => 0x1a0c
  | 136 => 0x164c
  | 137 => 0x170d
  | 138 => 0x15cd
  | 139 => 0x1a8b
  | 140 => 0x194b
  | 141 => 0x1a0d
  | 142 => 0x164d
  | 143 => 0x170e
  | 144 => 0x15ce
  | 145 => 0x188e
  | 146 => 0x160e
  | 147 => 0x1a8c
  | 148 => 0x194c
  | 149 => 0x1a4d
  | 150 => 0x17cd
  | 151 => 0x18ce
  | 152 => 0x178e
  | 153 => 0x14053
  | 154 => 0x10054
  | 155 => 0x15393
  | 156 => 0x11394
  | 157 => 0x15353
  | 158 => 0x11314
  | 159 => 0xd395
  | 160 => 0x9396
  | 161 => 0x19cbd3
  | 162 => 0x184b94
  | 163 => 0xc055
  | 164 => 0x8056
  | 165 => 0x1a57d3
  | 166 => 0x1a9953
  | 167 => 0x9296
  | 168 => 0x154b16
  | 169 => 0xd2d5
  | 170 => 0x16cb55
  | 171 => 0x1a57d5
  | 172 => 0x1a9954
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 2219
  | 6 => 7565
  | 5 => 3316
  | 4 => 115
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
  | 8 => packedAt gbK8 (1700+((h/20+packedAt gbK8 (1560+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (91710+((h/739+packedAt gbK7 (82103+(h % 739)*13) 13) % 5703)*13) 13
  | 6 => packedAt gbK6 (398414+((h/2521+packedAt gbK6 (363120+(h % 2521)*14) 14) % 9079)*14) 14
  | 5 => packedAt gbK5 (210009+((h/1105+packedAt gbK5 (195644+(h % 1105)*13) 13) % 4815)*13) 13
  | 4 => packedAt gbK4 (8354+((h/38+packedAt gbK4 (8050+(h % 38)*8) 8) % 139)*8) 8
  | 3 => packedAt gbK3 (246+((h/1+packedAt gbK3 (243+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffc07ff801fffffffffffff463f1fc638ffff
  | 1 => 0xfffff80fffff00ffe01fffffb9c8e47fcf8e3f
  | 2 => 0xf03ffff0001fff03ffe07e00c1f0f879f0f3cc
  | 3 => 0x3fffffffe00003ffff8000fe00ff81ff03f0
  | 4 => 0x3ffffffffffffc00000000ffff0001fffc00
  | 5 => 0xffc000000000000000000000fffffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x25000b284055144aa28c2aa021309c21834d5
  | 1 => 0xdc8c580532aa08a94115355418c8641cc38a2a
  | 2 => 0xe22ead500a93ea227d447806c170b869e0d34c
  | 3 => 0x44373669dcc03043979e1018ee00f6817d03b0
  | 4 => 0x883bc78e6f1cbcf006082060f7ed0001beec00
  | 5 => 0xf0204007000c08018104180fdbedf76000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeac8eca8a888eeeaeac8eca8a888eeeaeac8eca8a888eeeaeac8eca8a888eeeaeac8eca8a888eeeaeac8eca8a888eeeaeac8eca8a888eeeaeac8eca8a888, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36641
namespace PEqualNP.Outside.L_meta_36641
open PEqualNP.Outside.L_meta_36641.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 1 := bs0_3_0
theorem alls0 : ∀ k ≤ 3, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 1 := bs1_3_0
theorem alls1 : ∀ k ≤ 3, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 8 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_32 : Interval s2Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_64 : Interval s2Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 92 := (concat bs2_4_0 (concat bs2_4_32 bs2_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 44 := (concat bs2_5_0 bs2_5_32)
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
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 8 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_32 : Interval s3Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_64 : Interval s3Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 92 := (concat bs3_4_0 (concat bs3_4_32 bs3_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 44 := (concat bs3_5_0 bs3_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 1 := bs3_6_0
theorem alls3 : ∀ k ≤ 6, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
  · exact alls3_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 8 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_32 : Interval s4Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_64 : Interval s4Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 92 := (concat bs4_4_0 (concat bs4_4_32 bs4_4_64))
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 8 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_32 : Interval s5Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_64 : Interval s5Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 92 := (concat bs5_4_0 (concat bs5_4_32 bs5_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 44 := (concat bs5_5_0 bs5_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 1 := bs5_6_0
theorem alls5 : ∀ k ≤ 6, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
  · exact alls5_6 i (by omega) hi
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
theorem bgb_4_96 : Interval gbAtlas 4 96 19 := block_range (n:=19) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 115 := (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96))
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
theorem bgb_5_3296 : Interval gbAtlas 5 3296 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 3316 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 bgb_5_384)))) (concat (concat (concat bgb_5_416 (concat bgb_5_448 bgb_5_480)) (concat bgb_5_512 (concat bgb_5_544 bgb_5_576))) (concat (concat bgb_5_608 (concat bgb_5_640 bgb_5_672)) (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 bgb_5_800))))) (concat (concat (concat (concat bgb_5_832 (concat bgb_5_864 bgb_5_896)) (concat bgb_5_928 (concat bgb_5_960 bgb_5_992))) (concat (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088)) (concat (concat bgb_5_1120 bgb_5_1152) (concat bgb_5_1184 bgb_5_1216)))) (concat (concat (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312)) (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408))) (concat (concat bgb_5_1440 (concat bgb_5_1472 bgb_5_1504)) (concat (concat bgb_5_1536 bgb_5_1568) (concat bgb_5_1600 bgb_5_1632)))))) (concat (concat (concat (concat (concat bgb_5_1664 (concat bgb_5_1696 bgb_5_1728)) (concat bgb_5_1760 (concat bgb_5_1792 bgb_5_1824))) (concat (concat bgb_5_1856 (concat bgb_5_1888 bgb_5_1920)) (concat (concat bgb_5_1952 bgb_5_1984) (concat bgb_5_2016 bgb_5_2048)))) (concat (concat (concat bgb_5_2080 (concat bgb_5_2112 bgb_5_2144)) (concat bgb_5_2176 (concat bgb_5_2208 bgb_5_2240))) (concat (concat bgb_5_2272 (concat bgb_5_2304 bgb_5_2336)) (concat (concat bgb_5_2368 bgb_5_2400) (concat bgb_5_2432 bgb_5_2464))))) (concat (concat (concat (concat bgb_5_2496 (concat bgb_5_2528 bgb_5_2560)) (concat bgb_5_2592 (concat bgb_5_2624 bgb_5_2656))) (concat (concat bgb_5_2688 (concat bgb_5_2720 bgb_5_2752)) (concat (concat bgb_5_2784 bgb_5_2816) (concat bgb_5_2848 bgb_5_2880)))) (concat (concat (concat bgb_5_2912 (concat bgb_5_2944 bgb_5_2976)) (concat bgb_5_3008 (concat bgb_5_3040 bgb_5_3072))) (concat (concat bgb_5_3104 (concat bgb_5_3136 bgb_5_3168)) (concat (concat bgb_5_3200 bgb_5_3232) (concat bgb_5_3264 bgb_5_3296)))))))
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
theorem bgb_6_7552 : Interval gbAtlas 6 7552 13 := block_range (n:=13) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 7565 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)) (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 bgb_6_416)))) (concat (concat (concat bgb_6_448 (concat bgb_6_480 bgb_6_512)) (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640))) (concat (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 bgb_6_768)) (concat (concat bgb_6_800 bgb_6_832) (concat bgb_6_864 bgb_6_896))))) (concat (concat (concat (concat bgb_6_928 (concat bgb_6_960 bgb_6_992)) (concat (concat bgb_6_1024 bgb_6_1056) (concat bgb_6_1088 bgb_6_1120))) (concat (concat (concat bgb_6_1152 bgb_6_1184) (concat bgb_6_1216 bgb_6_1248)) (concat (concat bgb_6_1280 bgb_6_1312) (concat bgb_6_1344 bgb_6_1376)))) (concat (concat (concat bgb_6_1408 (concat bgb_6_1440 bgb_6_1472)) (concat (concat bgb_6_1504 bgb_6_1536) (concat bgb_6_1568 bgb_6_1600))) (concat (concat (concat bgb_6_1632 bgb_6_1664) (concat bgb_6_1696 bgb_6_1728)) (concat (concat bgb_6_1760 bgb_6_1792) (concat bgb_6_1824 bgb_6_1856)))))) (concat (concat (concat (concat (concat bgb_6_1888 (concat bgb_6_1920 bgb_6_1952)) (concat (concat bgb_6_1984 bgb_6_2016) (concat bgb_6_2048 bgb_6_2080))) (concat (concat bgb_6_2112 (concat bgb_6_2144 bgb_6_2176)) (concat (concat bgb_6_2208 bgb_6_2240) (concat bgb_6_2272 bgb_6_2304)))) (concat (concat (concat bgb_6_2336 (concat bgb_6_2368 bgb_6_2400)) (concat (concat bgb_6_2432 bgb_6_2464) (concat bgb_6_2496 bgb_6_2528))) (concat (concat (concat bgb_6_2560 bgb_6_2592) (concat bgb_6_2624 bgb_6_2656)) (concat (concat bgb_6_2688 bgb_6_2720) (concat bgb_6_2752 bgb_6_2784))))) (concat (concat (concat (concat bgb_6_2816 (concat bgb_6_2848 bgb_6_2880)) (concat (concat bgb_6_2912 bgb_6_2944) (concat bgb_6_2976 bgb_6_3008))) (concat (concat (concat bgb_6_3040 bgb_6_3072) (concat bgb_6_3104 bgb_6_3136)) (concat (concat bgb_6_3168 bgb_6_3200) (concat bgb_6_3232 bgb_6_3264)))) (concat (concat (concat bgb_6_3296 (concat bgb_6_3328 bgb_6_3360)) (concat (concat bgb_6_3392 bgb_6_3424) (concat bgb_6_3456 bgb_6_3488))) (concat (concat (concat bgb_6_3520 bgb_6_3552) (concat bgb_6_3584 bgb_6_3616)) (concat (concat bgb_6_3648 bgb_6_3680) (concat bgb_6_3712 bgb_6_3744))))))) (concat (concat (concat (concat (concat (concat bgb_6_3776 (concat bgb_6_3808 bgb_6_3840)) (concat (concat bgb_6_3872 bgb_6_3904) (concat bgb_6_3936 bgb_6_3968))) (concat (concat bgb_6_4000 (concat bgb_6_4032 bgb_6_4064)) (concat (concat bgb_6_4096 bgb_6_4128) (concat bgb_6_4160 bgb_6_4192)))) (concat (concat (concat bgb_6_4224 (concat bgb_6_4256 bgb_6_4288)) (concat (concat bgb_6_4320 bgb_6_4352) (concat bgb_6_4384 bgb_6_4416))) (concat (concat (concat bgb_6_4448 bgb_6_4480) (concat bgb_6_4512 bgb_6_4544)) (concat (concat bgb_6_4576 bgb_6_4608) (concat bgb_6_4640 bgb_6_4672))))) (concat (concat (concat (concat bgb_6_4704 (concat bgb_6_4736 bgb_6_4768)) (concat (concat bgb_6_4800 bgb_6_4832) (concat bgb_6_4864 bgb_6_4896))) (concat (concat (concat bgb_6_4928 bgb_6_4960) (concat bgb_6_4992 bgb_6_5024)) (concat (concat bgb_6_5056 bgb_6_5088) (concat bgb_6_5120 bgb_6_5152)))) (concat (concat (concat bgb_6_5184 (concat bgb_6_5216 bgb_6_5248)) (concat (concat bgb_6_5280 bgb_6_5312) (concat bgb_6_5344 bgb_6_5376))) (concat (concat (concat bgb_6_5408 bgb_6_5440) (concat bgb_6_5472 bgb_6_5504)) (concat (concat bgb_6_5536 bgb_6_5568) (concat bgb_6_5600 bgb_6_5632)))))) (concat (concat (concat (concat (concat bgb_6_5664 (concat bgb_6_5696 bgb_6_5728)) (concat (concat bgb_6_5760 bgb_6_5792) (concat bgb_6_5824 bgb_6_5856))) (concat (concat (concat bgb_6_5888 bgb_6_5920) (concat bgb_6_5952 bgb_6_5984)) (concat (concat bgb_6_6016 bgb_6_6048) (concat bgb_6_6080 bgb_6_6112)))) (concat (concat (concat bgb_6_6144 (concat bgb_6_6176 bgb_6_6208)) (concat (concat bgb_6_6240 bgb_6_6272) (concat bgb_6_6304 bgb_6_6336))) (concat (concat (concat bgb_6_6368 bgb_6_6400) (concat bgb_6_6432 bgb_6_6464)) (concat (concat bgb_6_6496 bgb_6_6528) (concat bgb_6_6560 bgb_6_6592))))) (concat (concat (concat (concat bgb_6_6624 (concat bgb_6_6656 bgb_6_6688)) (concat (concat bgb_6_6720 bgb_6_6752) (concat bgb_6_6784 bgb_6_6816))) (concat (concat (concat bgb_6_6848 bgb_6_6880) (concat bgb_6_6912 bgb_6_6944)) (concat (concat bgb_6_6976 bgb_6_7008) (concat bgb_6_7040 bgb_6_7072)))) (concat (concat (concat bgb_6_7104 (concat bgb_6_7136 bgb_6_7168)) (concat (concat bgb_6_7200 bgb_6_7232) (concat bgb_6_7264 bgb_6_7296))) (concat (concat (concat bgb_6_7328 bgb_6_7360) (concat bgb_6_7392 bgb_6_7424)) (concat (concat bgb_6_7456 bgb_6_7488) (concat bgb_6_7520 bgb_6_7552))))))))
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
theorem bgb_7_2208 : Interval gbAtlas 7 2208 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2219 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 (concat bgb_7_480 bgb_7_512))))) (concat (concat (concat (concat bgb_7_544 bgb_7_576) (concat bgb_7_608 bgb_7_640)) (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 (concat bgb_7_768 bgb_7_800)))) (concat (concat (concat bgb_7_832 bgb_7_864) (concat bgb_7_896 bgb_7_928)) (concat (concat bgb_7_960 bgb_7_992) (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088)))))) (concat (concat (concat (concat (concat bgb_7_1120 bgb_7_1152) (concat bgb_7_1184 bgb_7_1216)) (concat (concat bgb_7_1248 bgb_7_1280) (concat bgb_7_1312 bgb_7_1344))) (concat (concat (concat bgb_7_1376 bgb_7_1408) (concat bgb_7_1440 bgb_7_1472)) (concat (concat bgb_7_1504 bgb_7_1536) (concat bgb_7_1568 (concat bgb_7_1600 bgb_7_1632))))) (concat (concat (concat (concat bgb_7_1664 bgb_7_1696) (concat bgb_7_1728 bgb_7_1760)) (concat (concat bgb_7_1792 bgb_7_1824) (concat bgb_7_1856 (concat bgb_7_1888 bgb_7_1920)))) (concat (concat (concat bgb_7_1952 bgb_7_1984) (concat bgb_7_2016 bgb_7_2048)) (concat (concat bgb_7_2080 bgb_7_2112) (concat bgb_7_2144 (concat bgb_7_2176 bgb_7_2208)))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 4 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 24, 26),(inputs.getD 2 zero, 34, 38),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 17, 21),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 5, 21)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeac8eca8a888eeeaeac8eca8a888eeeaeac8eca8a888eeeaeac8eca8a888eeeaeac8eca8a888eeeaeac8eca8a888eeeaeac8eca8a888eeeaeac8eca8a888
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372936 * 2 ^ 32 + 3970476168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36641.Model.Repr at out
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

def mono : List Gate := [⟨.and,[3,4]⟩,⟨.and,[2,5]⟩,⟨.or,[2,5]⟩,⟨.or,[6,7]⟩,⟨.or,[3,4]⟩,⟨.and,[8,10]⟩,⟨.or,[1,11]⟩,⟨.and,[1,9]⟩,⟨.or,[1,12]⟩,⟨.or,[0,13]⟩,⟨.and,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372936 * 2 ^ 32 + 3970476168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372936 * 2 ^ 32 + 3970476168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36641

open PEqualNP.Outside.L_meta_36641 in
theorem PEqualNP.Outside.L_meta_36641 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372936 * 2 ^ 32 + 3970476168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372936 * 2 ^ 32 + 3970476168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
