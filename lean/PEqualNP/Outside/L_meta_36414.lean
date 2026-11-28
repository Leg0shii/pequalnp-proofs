import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36414.Model
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


end PEqualNP.Outside.L_meta_36414.Model

namespace PEqualNP.Outside.L_meta_36414
open PEqualNP.Outside.L_meta_36414.Model
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

def SBf (j : Nat) : Nat := [6, 5, 6, 8, 8, 6].getD j 0

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

end PEqualNP.Outside.L_meta_36414

namespace PEqualNP.Outside.L_meta_36414
open PEqualNP.Outside.L_meta_36414.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0xcb010074018a10460480a00068bf43bd43bf42bd42df32ee32dd32ed32cd32be41bc41be40bc40
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x10018120008c0011602b14038020280d05354e32c7a12658d424cb1e86996350d32c72a2658d544cb1a6520ce94241c6990838d329026ca320634c840
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x990a1185544ca886055132c24ca50907053294640
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 13
  | 3 => 13
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
  | 4 => packedAt s0K4 (228+((h/4+packedAt s0K4 (208+(h % 4)*5) 5) % 17)*5) 5
  | 3 => packedAt s0K3 (371+((h/4+packedAt s0K3 (351+(h % 4)*5) 5) % 24)*5) 5
  | 2 => packedAt s0K2 (155+((h/1+packedAt s0K2 (152+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x83ffe0ffc3fe1f0ff0ff0ff87f07f83e99f673
  | 2 => 0xfc1fff07fc3fe1f0ff0ff0ff87f83fc1667b9c
  | 3 => 0xffe3fff8003fffff000fff1ff8003fff878c1f
  | 4 => 0x3ffffffc001fffff0001fffffc001f80fe0
  | 5 => 0xfffc0000000001ffffffffe000000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xa840223104082002301301280912889408b231
  | 2 => 0x9404612005002205105104882509284225294
  | 3 => 0x108a8840aaa511550888aa1550212529850c0a
  | 4 => 0x52931084a20555998aa0881664a50109d00d40
  | 5 => 0x631a1ce7333999eeeccecc8440c60631ffe000
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcfcfcc0fcfcfc00fcfcfcc0fcfcfc00fcfcfcc0fcfcfc00fcfcfcc0fcfcfc00fcfcfcc0fcfcfc00fcfcfcc0fcfcfc00fcfcfcc0fcfcfc00fcfcfcc0fcfcfc00, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36414
namespace PEqualNP.Outside.L_meta_36414
open PEqualNP.Outside.L_meta_36414.Model
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
  | 0 => 0x1ffffc0ff0f87c3fc3f87fff87f0383e99f793
  | 2 => 0xe0787ff0ffff87c3fc3f8703f87fffc166c9fc
  | 3 => 0xff807fff00fffffc003ff803ff803fff870e1f
  | 4 => 0x7fffff0007ffffc00003ffffc001f80fe0
  | 5 => 0xffff8000000007fffffffffc00000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x4310046201108004c04809198091888c085391
  | 2 => 0x490088a240400881441882288824928422c0b4
  | 3 => 0x842551042aa445582225504255022531850c0a
  | 4 => 0x96566248a835566eaa844093664b0119d80f40
  | 5 => 0x1864438cccc667b3333664e0440c0621f7a000
  | _ => 0
def s1Atlas : Atlas := ⟨4,rawDecor 61 s1Pos s1Neg, 0xfafafaaafaf0fa00fafafaaafaf0fa00fafafaaafaf0fa00fafafaaafaf0fa00fafafaaafaf0fa00fafafaaafaf0fa00fafafaaafaf0fa00fafafaaafaf0fa00, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36414
namespace PEqualNP.Outside.L_meta_36414
open PEqualNP.Outside.L_meta_36414.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x2900580200012029c8301800100018c60bf42bd42df32dd32bf41bd41de31dc31be40bc40df30dd30
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x1094058c000818d424ca5aa5a0d354831aca80632d521026aa2205354b30
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
  | 4 => packedAt s2K4 (212+((h/4+packedAt s2K4 (192+(h % 4)*5) 5) % 22)*5) 5
  | 3 => packedAt s2K3 (197+((h/2+packedAt s2K3 (189+(h % 2)*4) 4) % 10)*4) 4
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xf8ffffc1fc3e1fe1fc3f0fffc3f8387f4cf70f
  | 1 => 0xff0787fe3fffe1fe1fc3f0e0fc3fff87b349f3
  | 3 => 0xfff807ffc03ffe3fe003ff00ffc03ff8c38e3c
  | 4 => 0x7ffffc0003ffffc0000ffffc000fc0fc0
  | 5 => 0xfffff8000000003fffffffff00000000fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x8110044004420002404012240488812041305
  | 1 => 0x10400888101002040841104404121204114052
  | 3 => 0xa22255108aa9106ac222aa08aa812560c28c28
  | 4 => 0x86b566252a0d54b376a88812f3258132ec0f80
  | 5 => 0xc4c64439b331993d9b33cc9c22060644fbe000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaaeeccee88eeeeeeaaeeccee88eeeeeeaaeeccee88eeeeeeaaeeccee88eeeeeeaaeeccee88eeeeeeaaeeccee88eeeeeeaaeeccee88eeeeeeaaeeccee88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36414
namespace PEqualNP.Outside.L_meta_36414
open PEqualNP.Outside.L_meta_36414.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x40e225c59e004c00c30587840000005248ce9a2001300000000d00500a12a011250418d83321d200389c01f14804831541c8153003042000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x437e51087de4210fd88421f690843f521086fca010df54021bf29e817d53d02fca5a05f54b40bf28e817d51d037e83a06f50740beaa4817e53902faa7206fd0e40dea1c817e52902faa5206f90a40de214817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c53502fea4a05f14940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea9881bf431037a86205f94840f7290816e52102faa4207b54840b6a9081be421037884205f94440fb288817651102faa2207d54440baa8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330ef21e61dd43cc2fca5985f54b30ef19661dc32cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa7185f94a30f7294616e528c2faa5187b54a30b6a94617e518c2faa3185f94230fda0461f8408c3be61187ecc230bfaa2617e544c2faa8985f15130ef21a61dd434c2fea4985f14930ef19261dc324c2fea2985f14530ef98a61dd314c3f680987e10130fd98261de304c2fea8185f95030beaa0617c540c2fca6185f94830bea90617e510c2faa2185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c83de65907b0cb20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53883bca7105794e20bea9c41dd53882baa7105f14e20bea94417e51882faa3105f94220fd18441f930883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a417e53482faa6905f14d20f721241ed42483de64907b0c920bfa8a417c51483de42907b48520fd18241f930483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20bf290417e51082faa2105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43f681887e10310bfaa4217e54842faa9085f15210bfa9c217e53842faa7085f14e10bfa94217e52842faa5085f14a10bea8c217e50843f461087e4c210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea6885f94d10bea9a217c53442fea4885f94910bea92217c52443ec82887d50510fd18221f930443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf288217e50043f680087e10010fb88021fa10043ea20087e44010
  | 1 => 0xc5250fd8a4a1db14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42dfa1a85bd4350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e5310afaa6215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332f7a1665ec42ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf298657e520cbde84197b10832ef99065ee320cbba64197b4c832bf28865f6510caeca2195f54432faa886575510cafca0197e94032bd280657d500cbf2a0195e54032bf29e837d53d077e87a0ef50f41bf296837d52d077c85a0ef10b41bf286837d50d06faa920df94e41bea9c837e52907dca520db94a41bea9483ed52906daa520df94641dfa0c83f741906fca120df54241bfa9a837c535077e86a0ef50d41bfa92837c525077c84a0ef10941fba0a83be41506fea0a0fed4141bda82837c50507f0a0a0de14141bf2a0837e53106faa620df94841bea90837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331bf296637d52cc6fca198df54331bfaa4637e548c6faa918df15231bea9c637e528c6faa518f78ca31ee194637e518c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c6fea498fbd4931b7a92637c524c7d8a498db14931fb98a63de314c6fea098df14131bfaa0637e540c77ca818cf95031beaa063bd540c67aa818df15031bf298637e520c7dca418db94831bea9063ed520c6daa418f78c831ee190637e510c7be6218fd8c431ee98863f5310c6fca018fe94031bd280637d500c7f2a018de54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21f7a1643ec42c87dc6590fb4cb21bf286437d50c86fea910df95221df2a4433e54886faa910ef552219eaa4437c54886fea710df94e21bea9c437c53886faa510fbcca21f6194437e51887ec6310fd4c621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a43df53486bea690df94d21bea9a437c53487b8a690d714d21f7a1243ec42487dc6490fb4c921fb18a43f531487ee4290fb88521bfa82437c50486fea810df95021beaa0437c54086fea610df94c21bea98437c53086fca410fbcc821f619
  | 2 => 0x90ba9a538222c4811c1600003d04f4a4824ff0004da6e41825939807c00120000000000001ee26cd88c8000830c28002f22b8cc8ce49a938d60ff0681580005549889cca1bd3aa62010a641be4251023531a0088ea4730258c000e01a61944e13c4563a8b9000458748000001dc001131ae0be8b4790ed33a1e0bda423ac0007d8700005e8b388e13e0b91d98f3cc530cb82000a4f85f8c62c20405013706c52d300951a80000025a00035cfb0001328f4781dc262000000ad4ec0008da01000444001704660004424f3f60000018a0d04090e0f11d2000e408f02e9a8000493d06cc001c332a0013199b08a001398000287b8448a700079cdd89d000000000a128a5706020e1a20012e9ca24e8e02c83f0ce0005b8a6000000302542468e8dd217354864af99e3301b0c91c73ca12d1f0cc4d88fc6c25800000102266170000a402b0007504008c34e738528220348bc851413f01a4f98c20540010b1781f80001f12f07a000499b521c5fc648853f84e43a99f43a0008f96b4e0478618af01a8f0fa2394de1f0f212c000484c9a5100045d209490244d47180005853c868e24d0000620dd1b80001c0040005547d0fe46e844858c143e8c0b71514ea0003082f00000000872364710d598e2484648b0ef0cc774e28a30fe9885a80030004c189c930c1282f07425c7aca11df19e5b0ba2060d47a9370820001207e81b0003ac0024b46c5192526b2444ac280000002f4a9800268384001d12180ec001a32c07fc0000000009894932000000fa8003124943e8b13080b46b15d35a500f00002b0630b998b34c7c4272570005c44c0000c8815390000000640700048a000d78790866e0e81072740610a25b088348138ec0142880316512c1001aa440500a4c114d3de0001b8ca4e8460001e938c80ceda6116c894d20000e6000000000008200e9fd09a0000502c050180d0000100017004000740505c05094020a0390040b0100300400028000181b0100001c0e0d00c00007038001201200c00004110000400018000090100300002000000180000803000080001d024070040a02405000280000402c0500400000000040604403040000740100c01040000040903c07008000f8020200000000010050540001421000020240100409000030140305c02130000040002c030140003822000020040000c0000018000040600702c0001401030000080b0081705c0000c03000010040002000010070080b00c051a80f05c05000020080600414010070080b04419024260000100002048050000100c04000040580b05c0701c0003827bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121fe94243bd284877d5090ff2a121de54243efa1a87be4350efea4a1fbd4943b7a92877
  | 3 => 0xa912a22a21c2627110257882a2836e6d03b8000186a0002220222a10397641e1d82e25f2f88a40009e00003c7a9bc1144fce79e2420568002020b614cfd0922c85b49306f0a21b4311363da11ca20944bc99c7c1081083991084117299438800168688118542fa72c5496926615c000002cc9dcac8000000cce00003f233480000000234000000009706d20b33400000000000000db00022884873a180728c50685204a88cf09da1ca924059bf03c5dd0022a0643cc6c8ab49051c809132207dc318002c44ec000080003909c2461bc40c658001d0314ab8ba4aa760230a42a8900b507b12243c7a1b03d886d171be1b60005f1563bc958a820a012418f188318e6440006b0000004d000338868a511a0001b8968f60002c8d017e1580001d15b08468521a154689400a91203894cf91cd0b0879098031f20000014327a169121d33529a400016464538b41d917860c980d00002ec820d50006584b8aa3202ccb79d707801cf81280ba218e107e30e
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0xb548c26d62d52309b988548c26d62152309d984548c2756115230da982528c2e96210230bc584408c34e52cc230ae993308c26f62551309b189544c27761551309d185544c2da6090d3097195434c2cc6250d30a7590324c2d5610c930b6980324c23e64145308f590514c26e62145309b588514c2cc624c5309e997404c2da6310130e650c404c2e96210130bc584404c2ba64cc130b398a304c27a60d50309798c540c26e62150309b588540c27661150309d584540c23e6494c308f592530c25f654c0309ed95300c27661d53209d58754c823e6414f208f59053c82766114f209d58453c82ad640cb20b958432c823e64947208f59251c82cc63487209798f548825d63d52209798c548825d63152209d984548827561152208f992538823d6494e20c7992538831d6494e20d6982538835a534c220d394f208823e64951208f994544832d62151208f992534823d6494d208fd91534823c6454d209dd8553482746154d20cb152424826c65509209b997324832c54cc920ab590324832c540c920b958432482ea600c920cb153214832c5448520b318d21483645148520ce15230482ea628c1209e1953048338544c120f20c930482ce63881209798c540825d63150209b988540827661150209d584540826e62d4c208f990530823d6414c209d98453082756114c209e980530825e63940209758e500826f65480209ed95200826e62d53109b58b54c426f6254f109b18953c423e6414f108f59053c426e6214f109b58853c423e64d4b108f59352c425f6354b109718d52c42f06050710ec50740c42f16110310ec90440c425e63152109758c548426e62152109b588548426e62d4e109b58b538423e6494e108f592538425e63d4a109758f528423f6454a108f191528423e64951109ed81544423e6515110cd584544423e6494d108f592534423f6454d108f191534426f6254d109b189534423e64949108f592524423f64549108f191524425f63549109718d524433454905109d1954144338548c1109e1953044338544c110ce153104425e63d50109758f540426e62d50109b58b540423d6595010ce181540423e64150109798c540425d63150109b988540426d62150109d984540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c108f990530423d6414c109798c530426e6214c109b588530427a6014c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520423e64148108f590520425e63148109758c520426e6214810ce553400435953d00109e59440043595310010cd55310042796584010d654e10042776544010cd551100427b6544010ae19110043595344010
  | 1 => 0xcb365494432cd552510cb365454432cd551510cb674254432d9109510cb663254432d94c9510cb3a5494032ce552500cb725194032dc546500cb3a5454032ce551500cb725154032dc545500ca7a6094f419e58253d06ac6250f41cb94b41906ac6250d41ad18543506b66190941ab98a415065e63141419758c505066e62141419b588505075a6314141d658c505073b4314141ce50c505076a6214141da588505073a4214141ce108505073a41141419bd89531066c6254c418fd9541106b860504419dd95411067a60d53319e58354cc66f62553319b18954cc66e62943319b58a50cc66e62d52319b58b548c67b60552319e181548c6d5610ca318fd91508c63c64542319b98a544c66d62951319bd89544c66c62551319ed81544c6786055131d9584524c74c528c5319b98b540c66d62d50319e983540c67960d50318f596540c63e64150319b988540c66d62150319e980540c6796015031cb952520c72d5494831cb951520c72d5454831d354a320c765528c43197d95310c6cc624c4319dd95310c765524c431ce952500c7395494031da94a500c7695294031ce951500c7395454031da949500c7695254031d68c9500c7583254031d6cc5500c75931540319e98354c867960d53218f99053c863d6414f219e98053c86796014f219798e50c865d63943218f993538863d64d4e218f990538863d6414e219e98053886796014e21cb953328872e540ca21b958432887c4328c621b9189318872e54c86219798e544865d639512197d8d544865c63551219ed81544867860551219798e534866f6254d218f990534863d6414d219e98053486796014d2197994534871e6414d21c7590534874d6214d21d5584534875a6014d21d6580534866e65d0921d314f42486e661d0921d314c424866e658c921d314e324866c654c921d314d3248754538c521f18ca3148674654c521ab992214874c53885219b98b540865e63150219758c540867a60150219e580540863e6414c218f590530866e6214c219d984530867a6014c219e580530866d65cc8219b59432086e5610c8218f992510863d64944219bd9521086cc63484219dd95210863f64540218f191500866f6254f409b18953d026e62947409b58a51d02b86050740ab18943902ae62906408f99741502b86050540d6982531031e5350c40ab189431034e5394840d354e521034e5354840d354d521032f4354840cb50d521032d5290840ae58042103565394440d554e51103665294440d954a51103565354440d554d51103665254440d954951103374354440cd50d51103364254440cd109511037060544408f59641102ae6290440cd54641103355110440cd547401023f6550040cd545401027b6550040c798e54cc31e5450f30b318943cc29d640cb30b558432cc2cc624c7309b98
  | 2 => 0x8002c00000142eab123480000000e780062096001945180000134b62386c8002380000800b30008b060002283a3883b2100038cb3b4c9619ea1b2e59a22ea30ecc09a0014ed79f4e130077248c59fcc31ba0018051242d804a00000003926685604262ac000d1800003a00981c5cb70800007317082000002887599831800cc82428b2000000000006a9627f87caab787b2242b2e08f8e2d117ed6a4e188008f00000000e2800221da7226ebe15e9329ab0800e507abb84c3f0001ba9c5300023382521f2581b83b800cfae4e1800000000022e0010ab68700a01a4cae200000461c20000000000b11369a000479588728a00000112c691800001aeaf0009f000990000000022a668380000366000001401424a80000000a84ed2000b9800001844700074b342da9ec1b3c312a000212e39048da720f8b8c21a8e6b5200000002b400000002940012a9eab6000000000089a160008200000002023a800000aed0000301cadcade002789418200000c0800bd3361f80016244e613a488000037c54230da066d60c8b700079000498e0c500063032003ae0039c7d8006f1b66288400000001b4c7000000000000000008328000f1e6171be77a6a39800001c4a8a2a0b9c073a90640161a00ec60000008610b22aa2ea7a284bf82c7e878ca34a00000a48ba46ad2789d82505a86a76c90003d800002ec40a34750001d1160000029274002c00000094a149b2f082940000000d8c2392825db7400364b432c6180011b2a192bae5830148065e22001000d71f00033a00000db8008c8002a8006803a4f800900a0272d6001ac0008000342402fc5b0d40000092b38431749f90e00000af800002d40000000112ac96ae98daae0f26580001c020000001c05000020000402404004030040605800000020280800404014070040300c010380c004010040d0101000408014050000000c0d0040602000014020000001c000180400807008000080b0081002c040080603c00008010080503400014020040404c070100c0240b00800000000000c010030040500c04000020100502800008000340100c01000020100e000010000102c07018010000100000008040180501401014050080000007014000000701c0502c000681601800000000000100e6e62947439b58a51d0e6e62942439b58a5090f3b4394243da98a5090f696294243ae9824350e3f6550c4397d954310e7a6094f429e58253d0aac6250f429798e5090a5d63942428fd954210a6f65508429e98354cca7960d53328f992518ca3d64946328fd91508ca3c64542329d986544ca7561951329bd89544ca7661d50329d587540ca7a60d50329e583540ca3d6595032cb189540ca3e64150329d984540ca7561150329e980540ca796015032cb553420ca6d6510832b358c420ca5f654c8329bd95320
  | 3 => 0x34e2a0be69800a90004b2f2be8005480000000000006c2a65f1144b838d8b1a52a54378b47ba98c412004af62f106a3800078b2db000000002780081a5e0000000000000001aba200072ab1928615c000dc00204000d03fba495b26ab80063a70420007e000dfb540000c003763e018000000038000000c28000029600000558a6718ce4916eb23ac568f4de8005a2ca0019c3e9a40031e0020cec1ea361640000000022000cc87800000000d000981e0d42e8001549709096a8c4e054da8404a0202600002b900013c1b356000000023a74000000485e8f0178764c304441a235
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x680000000380000000700000180010000b14032a8000c0008b600000a016e02d0091e004ba09b0200000480000600a000000000200100000050003515cc4254432a50e4a18a0a0d307150c5050724b1ac4282834c9c64214141a54e5208a0a0d48724c5500c7132a2c219443865916014d21ca2c2b00a690e445398742486a33ac6518a43839905388521a48e4a1aa2205317010951102a8b98c0a8881899895190440b10e4a18809868943588404c348a1ac2202610b5d8540c920c48a8b08649060c5418d2148322318a290a41625d0324c120e10a819260905c1710c93048258bb48220621861915344010
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x200100a808250d611013090987150324c120d00545c4324c120
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 632
  | 4 => 473
  | 3 => 29
  | 2 => 3
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
  | 5 => packedAt s3K5 (19164+((h/210+packedAt s3K5 (17064+(h % 210)*10) 10) % 759)*11) 11
  | 4 => packedAt s3K4 (19544+((h/157+packedAt s3K4 (17974+(h % 157)*10) 10) % 686)*10) 10
  | 3 => packedAt s3K3 (1484+((h/9+packedAt s3K3 (1421+(h % 9)*7) 7) % 69)*6) 6
  | 2 => packedAt s3K2 (184+((h/1+packedAt s3K2 (180+(h % 1)*4) 4) % 11)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xfe3ffff03c7c7f0f1c7f1fffc70383fc31f64f
  | 1 => 0x1fc1f8ffc07ffff01f8fe381f803fffcce487f
  | 2 => 0x1ffe00ffff8078ffe00ffc01fffc03830f8f8c
  | 4 => 0xe00000ffffff80fffff00001fffffc03f00ff0
  | 5 => 0xffffff00000000fffffffffe00000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x42885011808890030411048d412890a8109645
  | 1 => 0x8414212209302030088621108811295046481a
  | 2 => 0x4884b24498194155200b4824d2580a190b8a8c
  | 4 => 0x12944892040128a5520004924a25022b00560
  | 5 => 0x9131800e326264ec9a4c927000c06043ed6000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xfefeeaeafcfc8888fefeeaeafcfc8888fefeeaeafcfc8888fefeeaeafcfc8888fefeeaeafcfc8888fefeeaeafcfc8888fefeeaeafcfc8888fefeeaeafcfc8888, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36414
namespace PEqualNP.Outside.L_meta_36414
open PEqualNP.Outside.L_meta_36414.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x92005c000001d50a287400d10013a24aac01c0038002004130c368c28008000112aa0d160001486126419848000203c0108b007c0131e3c021a004040000240000ff43bf43fe43fd43bd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20ef20fe20fd20ed20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf29861bf430c37a86185f94830f7290616e520c2faa4187b54830b6a90617e510c3eca2185d94430bea8861f5510c2eaa2185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20dfa1e41bd43c83de85907b90b20f6a1641ec42c83de65907b8cb20f699641ec32c82fca3905f54720f790e41ee21c83da43907b08720f7aa641ee54c83daa9907b15320f7a9e41ee53c83daa7907b14f20f7a1e41af43c83dc87907b50f20d6a1e41ec43c83dea3907b94720f6a8e41ec51c83de83907b90720f6a0e41ec41c83de63907b8c720f698e41ec31c83de81907b90320f6a0641ec40c83de61907b8c320f698641ec30c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c538837e87106f50e20bea94416d52882fca3105f54620bf28441fa30883f261107bc8220fd904417f544837ea8904fd5120bf2a2417d54482f8a8906f151209e2a2417f53482fca6905f54d20be29a41bf434837a86907bd0920f721241ed42483d884907bcc920f719241ed32483d864905fd4520be28a41ef21483dc42907b48520f610a41fa30483f260907ec8120f710241ef544835ea8907b95120f6aa241ec5448358a8907bd4d20f729a41ed53483d8a6907bd0d20d7a1a41ee43483da86906b50d20f621a41ef51483dca2907b54520f628a41ef41483dc82907b50520f620a41ef31483dc62907b4c520f618a41ef50483d6a0907bd0120f720241ed40483d880907bcc120f718241ea30483da60907a4c120f6182417f54082fca8105f55020be2a0417f53082fca6105f54c20be29841bf430837a86105f94820b7290417e51082faa2105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10dfa1e21bd43c42fea5885f94b10bea96217c52c43ec83887d50710fb18e21f531c43de41887b48310bfaa4217e54842faa9085f15210bfa9c217e53842faa7085f14e10dfa1c21bd43842fea5085f94a10f7294216e52842faa5087b54a10b6a94217c52842faa3085f94210fd18421f930843de41087b48210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea6885f94d10bea9a217c534437e86886f50d10bfa92217e52442faa4885f14910fb20a21f541443ec62887d4c510fd18221f930443de40887b48110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c530437e86086f50c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf288217e50043de40087b48010fb88021fa10043ea20087e44010
  | 1 => 0xc535077e86a0ef50d41bfa92837c525077c84a0ef10941fba0a83be41506fea0a0df14141bf2a0837e53106faa620efd0c41dea18837e52106faa420df94441dfa0883f6411077a8220fd50441bf280837d50106fea998df95331df2a6633e54cc6faa998ef553319eaa6637c54cc77e8798ef50f31bf296637d52cc6fca198df54331bfaa4637e548c6faa918df15231bea9c63bf438c77a8718df94a31bea94637e518c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c77e8698ef50d31bfa9263ef524c6dea498df14931f6292636c524c7ee6298f78c531bfa82637c504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618efd0c31dea18637e520c7dca418db94831bea9063ed520c6daa418df94431ef98863f6310c7ba6218fd4c431bf28063fa500c6f4a018df54031fca806379500c6fea990df95321beaa6437c54c86fea790df94f21bea9e437c53c877e8790ef50f21f7a1643ec42c87dc6590fb4cb21bf286437d50c86fea910df95221df2a4433e54886faa910ef552219eaa4437c54886fea710df94e21bea9c437c538877e8710ef50e21bea9443ef32887d86510df94621fb18c43f531887de4310fdc8621bf284437d50886fea890df95121beaa2437c54486fea690df94d21bea9a437c534877e8690ef50d21f7a1243ec42487dc6490fb4c921fb18a43f531487ee4290fb88521bfa82437c50486fea810df95021beaa0437c54086fea610df94c21bea98437c530877e8610ef50c21bf29043ef32087d86410df94421f790843f621087da4210fd48421bf280437d50086fca7a05f54f40dfa1e81bd43d02fca5a05f54b40bf28e817d51d037e83a06f50740beaa4817e53902faa7206fd0e40dea1c817e52903dca5205b94a40bea9481ed52902daa5206f90a40de214817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037e86a06f50d40bfa92817c52502fea2a05f14540dfa0a81bd41503f680a06f90140bf2a0817e53103bca6205794c40bea9881dd53102baa6206fd0c40dea18817e52103dca4205b94840bea9081ed52102daa4206f90840de210817e51103eca2205d94440bea8881f551102eaa2206f90440de208817e501037e80207e90040dea0081f940102fea9985f95330df2a6613e54cc2faa9986f553309eaa6617c54cc37e87987790f30dea1e61dd43cc33a87985f94b30bea96617e51cc2faa39877cc730ee98e617f548c2fca9185f55230be2a4617d538c37e87186f50e30bf29461ee528c2dca5185f54a30f6a94616d528c2fca3185f54630bf28461df308c3f661185fd5130bf2a2617d544c2f8a8986fd0d30ef21a61bd434c3ba86986750d30bfa92617c524c2fea2985f14530ef98a61dd314c3f66098778c130bfaa
  | 2 => 0x300402800c0080200001c0280d00200004000002004040000080000100400a00c00003002000008000040000080b00200000005000010018020060580180200000c0000400c0000300d0060080000e000000010000020000200200a02c020100000380380100200c030030140181480200001400001062000010010040000001303e0000081b006004008000000100080003c0180100000800000801000008008000020000000400200c0300600a02c040130020000880100409c0100002001004800000000118050060240080000c0040900e0140280201500000c0000700e000000000040080080001400c0180d00203801000000038000050000080700400a00c0001300200400807008018040060000240180300e0000800701000c00814000000008000040000482100a0040281bbf296877d52d0efca3a1df54743bf286877d50d0f7ea5a1ef94b43dea9687bc52d0f7ea3a1ef94743dea8e87bc51d0f7ea1a1ef94343dea8687bc50d0efaa921cf55243bf29c87bf4390fbe8721df94a43bea94877e5190efaa321df94243bea8487df4350f7c86a1dfd4943f7a92876f5250ef8a4a1fb14943b6292877f5150ef8a2a1dfd4143be28287bf5350f3ea6a1efd4943d7a9287be5250f7aa4a1ef14943d629287bf5150f7ca2a1ef54543de28a87bf5050f7ca0a1ef54143de282877e5410e7ca821df94c43dfa1887de4310f7a8621f750c43bf290877d5210efca221df54443bf280877d5010efca7a15f54f42dfa1e85bd43d0afca3a15f54742bf286857d50d0afaa9215f94e42bea9c85bf4390b7a87215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42dfa1a85bd4350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e5310afaa6216fd0c42dea18857e5210b7e84217b90842dea1085ed4210afca2215f54442bf280857d5010afea9995f95332df2a6653e54ccafaa9996f553329eaa6657c54ccb7e87996f50f32f7a1665ec42ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7196fd0e32dea1c657e528cbbe65197bcca32bf28c657d518cafca1195f54232bfaa2657e544cafaa8995f15132dfa1a65bd434cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf29865bf430cb7a86195f94832f7a1065ec420cbbe64197b8c832ee99065ed320cafca2197d94432bb288657d510cbeaa2195d54432bf28065fa500caf4a0195f54032fca806579500cafca7a0df54f41dfa1e83bd43d06fca5a0df54b41df21683bc42d06fca1a0df54341beaa4837e53906faa720efd0e41dea1c837e52907dca520db94a41bea9483ed52906daa520df94641dfa0c83f741906fca120df54241bfa9a837
  | 3 => 0x9472d0c4c003103304001c0003100c9210003163ac000ad662000001094e0cb000000000000eca0b0eab3cfe8000003c86492510c8fd250b7262b058f2f9000288000005046e48505a30ac64b0aa00000000020c0a4bc84a1e71a66044f9c356cba03e23819ab4581277000cc18a000112000002ad5b47280004e5846694b8e000040ce8800000a88000000945a800000000000fd8000008952613942a48c0b9331d0000002722f0c44000000565dc920005a8008d51b53820000011e3040018d850000804138002b0000d20000001880001b00052d59a83000abc000ea1f453c2f11b0000012a8000004487100000000117004000c2400000412001538002ce0005d069364450f0800000998001550005d0001f5000360000e64c81457d98d1de454f4252000c818aaff0008a8dc0f55fc41d952e221a3700a2e53fe4d593000000aa021118000bf4000004ec724a2800000000000000000000f000000af8000003b496d8e0003aec054e00039ec482a278162a4ceeadc2181141a0ca1ee56534b0f1e8488409750f4890019a91bc09487941488000000003240000000020a0013e3064fea3c07226000001039422929c47e8af0002ecef9514823cd7d0000001a80000017000000000000000000000000000000059cb8cec1f33d226c358000e4000000b90220000019d000001929063c0158002de000520fa25f5c0a480c92d000650000004dc0f0b82ef318000c3068276331238000007d85925942cb8592000000641288000006b40008744e00000248000000000003e000161a061ba000000910000000000060a85061800000aed000c803a8ed7e11d3761c06113224e458bf0002ae7f14700039c69518134240000a23161aa7549e29003858c8d1932420301b8000006d8000001caaa4000d4116000eb1b10c0000000000866b8000e74deca07821164220c150ee63eb64e01404722a4000000000017588f0000000017f54626000180500519118e408c0d4083325184105b12a0001750406f4500a560000000594000003500016492c0000811a8003740000022f0000014215438e5b0003270000017701f000001968004c05694f8ec45200065901000680428da00031000000574001459a2286bc400000048000cda6c0001d038800528bcc5a000000470118181587785f09c000001468d713acb93100032ec388f9c41264643704d274bd003041000000000005600001106650c000b0205000a6c000c7000840b5ab4000b900022045a2fc0008031e951532b55d45588b8b56449e8f900000099d6ba0d3ee9f50c2120c29ccc49874a0b991096f3065b973a1a00000201c03002020000010030020080200a00a0000100100203c00039010020008000000000880002600400812008000008000000000200c00a0040180001c008080010080380
  | 4 => 0x3842c807000a600024e252b1000000000b200001500002c00000000534fc000000000000000008100000048aaf43f0000003158c0a4458c745187766629c000001084450129e1f267d862c73a619c3eb0b154665840734d42c018b0d4443c52b0fc54a9acee30401abe05e0000005f10c800000b74000000005895c8003d40004b8001207904c8e94a6238d81cd2a482860000000000000000ae0bcdfa3707417cff1ac0000000021e2e60010d8000006f859a0f25c235669ee000000718280008ccb30000009952797946c000f88005980ecae2d5000924002b1000678978000f2000001c60000014c8000006f4f30000000cc002810dab594283918c0247b00021c530000004bc7bd43a1f0fe294be8fb6062287f9bc080280679d20b81247f2962ba54cbdaf636844c411b71a2c1cd32ca14268c9b8d617a1955ba8a1daba4181cb4d037c171eb06c3053a928468120842430b6ab9520000007155c01a5da1540019107c0000000040600016a17042901369cc2be0018525d000bdc002d30248f40000001e4aca524612a4f86cabf0006bc442f01a4cad4e8004ae7e8002d82ec8715085855878ce42955a09617605346467194800596000000160c8000003174749840013d0004e000213000000001f9000000000000000010e8000000000000007e70800130600000000000ec968d090b4c69e42389619c2acb21263d80144f0000882689f800000004cb0004f66cc000003da1ec6827e314098ad8000000019786c5100004932331c0000023e2e40014495e41cb481604f3a804d3a171000b14000a8564000000003a0b7c1e8000000000031a00023000000000000eda3c4b8000ca9365ea5a4b69e20000000004c00092cbd0000003e0c20782046ad6daaa0000000406349a0000029a220af06d950556a45188a629c69c000000002b82580045602963000000000f2
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x230483a8548c120ba58e30483ab438c120ea50e304838d434c120ba99530482e8654c120ead5130483a8544c120f2d8d30483cb534c120f214d30483ab434c120f290d30483a9434c120f250d3048389434c120f2cc530483c9314c1209b99430482ae640c120ab59030482e6610c120b958430482ea600c1209b98b540825e63150209758c540826e62150209d984540827561150209b98b530823e6494c208f592530823e6414c208f590530826e6214c209d98453082756114c209e980530831e5350c20c754d430832f4394820cb50e520826f65480209ed95200836a52480209b98b54c426d62d53108f99253c423d6494f109bd8953c426c6254f108f99053c423d6414f109b98853c426d6214f108f99352c423d64d4b109b98b548426d62d52109798c548425d63152109b988548426d62152109b98b538426d62d4e108f992538423d6494e108f990538423d6414e109b988538426d6214e10c794d438431d5350e10cbd0e528432d4394a108fd91528423c6454a10cbd91528432c6454a10cbd0d528432d4354a10da54a3084399434c210da549308426e62d51109b58b544423d63d5110cb98b544432d62d51108f992544423e65151108f58c544433561151108f992534423d6494d108fd91534423c6454d109bd89534426c6254d108f990534423d6414d109b988534426d6214d108f997434423c65d0d108f995434423c6550d108f992524423d64949108fd91524423c645491097d8d524425c6354910cd15241442746550510bc1814144274654c5109e1953044399434c110f44c5304432f54c8110cb153204432f5448110cb151204425e63d50109758f540426e62d50109b58b540423d65950108f58e540423f63550108f990540425e63150109758c540426e62150109b588540427661150108f993530423d64d4c109b98b530426d62d4c108f992530423d6494c1097596530431e5494c10c7552530431e6494c10c7592530431e5454c10c7551530431e6454c10c7591530423e6414c108f590530425e6314c109b988530426d6214c109d984530427a6014c108fd97430423d65d0c10c794f430431d53d0c108fd95430423d6550c10c794d430431d5350c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432f4394810cb50e520432e5454810cb551520434e5354810d354d520432f4354810cb50d520426f60548109b581520423e64148108f590520425e63148109758c520426e62148109b98a500426d62940109b597200432e54c8010cb553200434e53c8010d354f200426f6548010cb951200432d5448010d394d200434d5348010cd553100435553c40109e596100435953840109dd9510043355444010d554d10043e120440109ed9510043595344010
  | 1 => 0xc31d544c030d5545300c27b654c030da549300c371514c0309d98754c827561d53208f99253c823d6494f208f99053c823d6414f209d98453c82756114f20ab99332c82ad64ccb20ab99032c82ad640cb20b998432c82e5610cb208f99251c823d6494720ab99221c82ad6488720d954421c82e661d5320b958754c82e960d5320ba58054c82e960d4f20ab99253c82ad6494f20ab99053c82ad6414f20b998453c82e56114f20ba58053c826f6550f209b19543c832f6550f20cb19543c838f6350f20ab99351c82ad64d4720ba58351c82ae6494720ab59251c83655114720ba58051c826e65907209b59641c82ae64cc720ab59331c826f654c7209b19531c826e650c7209b59431c82ae640c720ab59031c82ea600c720ba58031c82ce6310320b358c40c82e66110320b958440c82ae64cc320ab59330c838d43cc320e350d30c82ae640c320ab59030c82e6610c320b958430c825e63152209758c548827661152209d584548823e6494e208f592538823e6414e208f59053882766114e209d584538831e5350e20c754d4388399434c2208f58f544832d62d51208f992544823e65151208f58c544832d62151208f992534823d6494d208fd91534823c6454d209dd8553482746154d208f990534823d6414d209d98453482756114d208f997434823c65d0d208f995434823c6550d209b997424832c54909209b195424832f54109209b99732482ae64cc920ab593324832c54cc920ba983324826c654c920ab99032482ad640c920cb15032482e6610c920b958432482ea600c920cb15321482ae6488520ab592214832c5448520d914521482ea628c1209e1953048399434c120ab58f54482ae6495120ba58254482eb6055120ab994544832e6515120ab58c54482ae6494d20ab592534832c5494d20ba58253482af6454d20ab19153482e76154d20b918553482eb6054d20ab99053482ad6414d20cb15053482e66114d20b958453482ae65d0d20ab19743482ad6490d20ba98243482e96090d209bd95434826c6550d20cbd9543482ae6550d20ab195434832c6550d208b195434838f6350d20ab99043482ea6010d20ba580434832c54d4520ab99251482ad6494520ba58251482af6454520ab191514832c5454520b3d8d51482cc6354520bad81514836551145209b996414826d6590520bad8141482e86050520ba98041482e96010520ab99331482ad64cc520ba98331482e960cc5209bd95314826c654c5209b994314826d650c520ab99031482ad640c520ba98031482e9600c520cbd53504832c54d4120ead5350483a854d4120ba58f50483ab43d4120ea50f504826e65901209b99440482ce6310120b358c40482e66110120b958440483a94010120ab99330482ad64cc120e350f304826e658c120ba996304836a658c120ead5
  | 2 => 0x6414f218f59053c867a6014f219e58053c863d63952218fd8d548863e64d4e218f593538863e6494e218f592538863e6414e218f590538867a6014e219e580538863f65d0e218f597438863f6550e218f595438872e54cca21cb95032886e5610ca21ba58032886e4624c621cb953218865e63951219758e544863e6494d218f592534866f6254d218f990534863d6414d219e98053486796014d21c7d4d434871c5350d219b99742486e661d09219b996324866c654c9219d1953148754534c521ab992214866e62d50219798c540865d63150219e980540867960150218f992530863d6494c218f990530863d6414c219b98853086766114c219e98053086796014c21c794d430871d5350c219b597320866d650c821b958432086e9600c8218f992510863d64944219bd95210867765484218fd91500863c64540219bd8953d026c6254f40c754f43d026e62947409b58a51d031e5350e40c754d43902ac6250e40cbd0e529032d4394a40cbd0d529032d4354a40cb54842902ae6290640c7d4d435023e65d0540c7991531031d53d0c40c794d43102ac6250c40d394e521034d5394840cbd0e521032d4394840d394d521034d5354840cbd0d521032d4354840c754e421032d5290840c754c42102b96010840d594e51103555394440d994a51103655294440cdd0e51103354394440d594d51103555354440d994951103655254440cdd0d51103354354440cd909511033442544408f596411031d5390440ab98a41103355190440c754c41103355110440c754f401033551d00408fd95401031d5350040cd545401027b6550040c798e54cc26f62553309b18954cc32f6255330cb18954cc31e5450f30a7d9543cc31f6550f30e3d8943cc38c6250f309bd8951cc26c6254730a759331cc26e62d52309b58b548c26e62152309b588548c27661152309d584548c32f4394a30cb50e528c36a6094a308fd91528c23c6454a30cbd91528c32c6454a30cbd0d528c32d4354a308fd91518c23c64546309bd89544c26c62551309dd85544c2746155130a7592434c25c6550d30c7d95434c31c6550d30e3d89434c38c6250d30e6d81434c3986050d308f990514c23d64145309b988514c26d6214530a7593314c39943cc1309b98b540c26d62d50309d987540c27561d50308f596540c23f63550308f58d540c23e64150309798c540c26e62150309b588540c27661150309d584540c23e6494c308f592530c23d65d0c308fd95430c31e5350c30cb952520c32d5494830cbd0e520c32d4394830cb951520c32d5454830cbd0d520c32d4354830cd952510c3355494430d994a510c3655294430cdd0e510c3354394430cd951510c3355454430d9949510c3655254430cdd0d510c3354354430c7553300c35551cc030da54a300c371518c03097d95300
  | 3 => 0x943cbd4c5250f8f5314943ab5805250f2c52d4543ab98a5150ead6294543abd895150eac6254543cb1495150ebb6054543ae1815150f355114543ab98a5050ead6294143cb14a5050eaf6254143ab1895050eb76154143ad1855050eae6214143ab5885050f2c5214143ad9845050eb561141438fd954310e5f6550c43c79514310e6e62940439b58a5010f1d53d0f42ab18943d0b1d5350e42c7d4d4350b1d53d0c42abd894310a3f65508429bd954210b2f6255332cb55042cca3e64946328f592518ca3f64542328f191508ca7661951329d586544ca6f62551329d987540ca7561d50329e983540ca7960d50328f596540cb2c62550328f990540ca7661150329d584540ca7a60150329e580540ca3e6494c328f592530ca3d65d0c328fd95430cb2d54d08329b594420cacd631083297d95320ca6f654c832e350d320cb365494432cd552510cb374394432cd50e510cb365454432cd551510cb374354432cd50d510cb674254432d9109510cb663254432d94c9510cb3a5494032ce552500cb725194032dc546500cb3b4394032ce50e500cb3a5454032ce551500cb725154032dc545500cb3b4354032ce50d500cb6a6254032dad09500cb684254032da8c9500cb693254032c754f43d06ac6250f419b98a50d066d6294341c754d439072f4394a41cb50e529066d6094a41cbd0d529072d4354a419bd81529072e52d06419b98a509066d6294241c7d4d43506ac6250d41ad18543506b66190941ab98a415065e63141419758c505066e62141419b588505066f6254c419b189531071d53d0c41ad587431063f65504419dd95411066e62940419b58a501066f62553319b18954cc72f6255331cb18954cc66e62943319b58a50cc66e62d52319b58b548c66e62942319b58a508c63f64542318f191508c66e62951319b58a544c66f62551319b189544c67b60551319e181544c63e64d49318f593524c72e64d4931cb593524c72f43d4931cb50f524c66d60d4931cbd0c524c72d4314931d9584524c66d60149318f990504c63d64141319b988504c66d62141319b98b540c66d62d50319e983540c67960d50318f596540c63e64150319b988540c66d62150319e980540c67960150318f992530c63d6494c318f597430c63f6550c31cb952520c72d5494831cbd0e520c72d43948319b582520c72e5454831cb551520c72f4354831cb50d520c66f6054831d954a310c65f654c4319dd95310c795434c431d9549310c66e62940319b58a500c73a5494031ce552500c76a5294031da54a500c73b4394031ce50e500c76a6294031da58a500c73a5454031ce551500c76a5254031da549500c73b4354031ce50d500c76a6254031da589500c75b3154031dc8c5500c7593154031dc4c5500c67a60d53219e58354c863e6494f218f59253c863e
  | 4 => 0xc0026f4900303b0002cc5f8002643d29e16b1c100000000000000bf0000f100000000000000000d480042a46c0032003c124ba27a000001bc0140000001814f27656422a7e00055894a3525a085949e638cabc00000106d20001d10000281cb6c52668c001200587d4e2a416d638439a1b52cce071000306175beb2409c35cee000350a899daf4000c6800000280c895ba820006e16d9fb314ce4002d20000003c2bc3c262c001f241c008331a603e4440a8005a68ecd7ae60000016f8a3498a9da100000040cdaa834303e53b1855b2001568b91d421c400e36c65095a2d80000000000019a69c9cb6d0004713ab583be000003276942cc4d2da04e000121996baa48002ee2f2c2c380d15a23399437b094000cb96a636d2c620366a2d918499e038551a233c45abc0a62f625cd49663144ced34b42de4e40cceb0006bc8113e0ed2867e8f009b3f2001ab8d92a49cc1a0922565b46a9ac33a10c5aae74d2001b50002d69b0be16c01cbf93baca0b01d1450b60fc000000000002c55480004a001bd00018cb90ed23824a11c279ef356724af0e53d83c183af13da4bc000000f2000b000030c1b1442890d4d3000067000000f89930d2928d68d045c41000312604c984a92c45e000ab8f336483cbc00000a0000280380400e0000000002c00c0002600e0040500100c0000c82e000024008000020540380001200c138000000680300002401c0780000e01002007000004000060180140000000a0080500000000001000004008010c201c0140280801000802000004094058010060900000f0040000000000404c01039004030040080000000e00000004c0282100200001001000014030020000040280000400000843000004008000000080300200000806002006000020000620100000b00a0040000000e01003005000004000030180181301e00200801802002018000040020080002f0680680b00d0000540285a00e0140100f000014010010160000000203401801005002004008020040000080000400c0500700a0000a0220120300080002e000000000240180280604e010018040120040500500e00c0980100c0140000c05409c00004000040000050020000980e014008000070040240f802006000008100420100282e01a0080000000c0080081000c0680100200a0000002b02a014058000020a41180c0000080000a03e0000181a00401c018009b98a51d0e6d62947439b98a50d0e6d6294343ad98752d0eb561d4b43ab98b51d0ead62d4743ab98a51d0ead6294743cd54451d0eae6294343ab58a50d0eae6214343ab58850d0eb66114343ad58450d0e6e62942439b58a5090e6d60d49439b5805250e6e62141439b5885050e7661141439d5845050e9d60d4d43cbd4f5250f8f53d4943ab5835250eae6294943ab9945250f2e6514
  | 5 => 0x7f3165f687c4202e142c191fa08080d9c8ab326cabfdad0c2488ba8e91120007d0f20134145dd248001488d8c4a09462359012cf0bc00041194480b504c1bf5964d19584b55401d2e000000984001240620dc84000292819a81671264e8e581b4247d9619886004606029c47cdb90b2f33542285f11e2e6cc423252000b258c8cc4d430c482f5386ae9621e7302a989c08f390acd9ea223624f0690bb6683701f23d27c7c142aed5c46f111b251b4b087b8db6b20a4f2810680001668000dc71d4ba191923d55405b6d2360308632c8a34000004e0b18ce2280000013a0c51687fd2b109000000448a6532988a89002aa85ce70ab0ac2652d8003d6a040015351e1f0090b263c489a180024e000001bd29a000000642c4c74001610de430642bf32415c0d10224c475852fd2dc75c001b96c20000006546e1090e0005f2a40003660c0ce8b81010325104894e51896132897000c14390524ccaed29b2e1f42fc283305aa47cd821d3bc611819283ee8d1670bd6e8288982540540011e24233452c2f81600076d968e661e8951c9fd4286d9953462349418f8002fa639a4800406a2c7613d3c62e9702460aa80535a9f10c000a417561ca74c78b021c1ec1d00053074d1900062a001101174bed58790595d202c001e230e2140017f2b48cc208cb2f68001928626ebdc3eb4f262000dd2dd304230288001280fc0011636eb7125a450005614d8001520010580d00084d8812a39834c00114282001ba8e9040d88bb31758ea90d0000000000d716f00051c000006ee6cce02e85000019f8dd6220000000053c000001100b8cb19f27d116d700ea27000b15529d8246088342c14da1305e00007a2705c3531f80012f25149c0d5518004f2000e687500038035800000ad4002e11ce5a50800020c868001a40000f046aec0003e0b194666631ce2294000001adab9000025728003dc3b9501a5000c705bb763f01c44f0a731843c5624369c2594d2245643d1b82f2214cd40000004c95482a8e6e472931abe68e6d0368006de000cd80002e328119fe022af402afa1f60b5560f65c6435b88006bed0489a4f330c8d3d80814a6591d24d6a8ad89926e4c01683ba2c00291c140622f43791480054200148b044d09c4b9018570d806f8ef33e204240001401e8078eb4180016ba5905657d2e80065eda0268001540ec178ff2e2ac0eeb794602bc0025a00881c9fb131d0000220002946352b9190007a0fe2b161acd8679a12ca898eaac032a304f509d5de2b44f9be1100e09b000000a10001d03b200083b7c4546eda2800344000ae0fd5a0001438003a860001a2b618c0508af855ca55aa9505d65758421e442aac9a990000000909cf2167089987f3e6814c895b00cdcca28000002b82a337642239640a86303513f8e441a14
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0xf0b960da0a19e01900017011f1695920e828519140f849d0700151d801788188010800380001b938c8000078a0300001e898012801c1f91090c0400860e11a1000020130a9a089a981482068d1b1c998b05850c0a05304100000028140011c1c0090044892c50a4302a2a1d30705445150e94b80a428287891496114143a8ae6212a219705434c9510caa4b9884a8065c250d32540328d2e0312a620c2f7650f524c782a1aa498863c450d3154031a1ae72a06510e265458432887152a2c019443465c05350d21aa2e029a6290c1d731915008654b80c4a18818654d6010840a48e4a1aa220531701095110306a9cc5208812a5c26290440c4cc4a8c822042c7650d528c306328c4a1a61625c06250d30b12e4302869868862181434c2c8b88c0a1a610b5d8540c920a1ae62a0649062454584324828c3aa8698241435cc5414d20c48a8b08a69042e7599543483062a0c6a8a41511cd5114520992e6302829042c755933148344b1a8020241a85854010120858eab26609050c7550f30482943aa8718241431d5434c120c50ca2a260905897315130482c4ba0a698241c2150534c120b82e229a60905897490d30482943aa8698241521d5434c120e16eaa1a609058a7550d30482c43aa8698241c21d5434c120a10eaa1a609058974cc530482163b286a9421c250d524c2109a2e6302828842e76d512044390aa24088021d054d2044010
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x149d601006668105231ca000420060a21801496114143a0583951610ca21a0983951600ca21921801c94354440c09535c26290440a21809895190440c08655c06250d30c80625c46050d30a0583151610c920a05831516114d20c08655cc544c120d00545c4534c12090a859d5434c120908855d3314c1209088750d524c210
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 820
  | 4 => 894
  | 3 => 68
  | 2 => 15
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
  | 6 => packedAt s4K6 (788+((h/14+packedAt s4K6 (704+(h % 14)*6) 6) % 63)*7) 7
  | 5 => packedAt s4K5 (25143+((h/273+packedAt s4K5 (22140+(h % 273)*11) 11) % 1191)*11) 11
  | 4 => packedAt s4K4 (37250+((h/298+packedAt s4K4 (33972+(h % 298)*11) 11) % 1073)*11) 11
  | 3 => packedAt s4K3 (3486+((h/22+packedAt s4K3 (3332+(h % 22)*7) 7) % 82)*8) 8
  | 2 => packedAt s4K2 (925+((h/5+packedAt s4K2 (900+(h % 5)*5) 5) % 19)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xc7f8ffff078f8ff8718fe3ffe38387fe11f43f
  | 1 => 0xf87f0f8ff80ff1ff81f1fc707c03f8fe6e48cf
  | 2 => 0x7ff00ffff001c7fe01ff807ffc00e18f8f0c
  | 3 => 0xff80000ffffffe07fffe00007fffff01f00ff0
  | 5 => 0xfffffff000000007ffffffff80000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x410a0101101110001002209120888224009415
  | 1 => 0x92106212212602818090c4224411305826484a
  | 2 => 0x352227245303250ab20169056938128c8b8d0c
  | 3 => 0x488488408001445240008124244015002a0
  | 5 => 0x2644cc00e64c49a769c9924e00606411fd6000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfeeafeeafe88fe88feeafeeafe88fe88feeafeeafe88fe88feeafeeafe88fe88feeafeeafe88fe88feeafeeafe88fe88feeafeeafe88fe88feeafeeafe88fe88, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36414
namespace PEqualNP.Outside.L_meta_36414
open PEqualNP.Outside.L_meta_36414.Model
def s5K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x580100bf43bd43ef21ed21
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 4
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (i*5) 5
  | 4 => packedAt s5K4 (i*16) 16
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (6+((h/1+packedAt s5K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s5K4 (67+((h/1+packedAt s5K4 (64+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x3c7e1c78f1e3e3fce31f8e0e18e1c7ff36443f
  | 1 => 0x3f9fe07ffe03fc7f03e3f00fff01f87f4878cf
  | 2 => 0xc01fff80fffc0063fc03fff01ffe00708f8f0c
  | 3 => 0xffe00000ffffff83fffc00001fffff80f00ff0
  | 4 => 0xffffffff00000003ffffffffe0000000fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x8642c09114854440610682a28824431a164415
  | 1 => 0x904092020488081002110445108902408184a
  | 2 => 0x814848324440c9052401a4605a4c11460a8d0c
  | 3 => 0x100112448902000a8a48010104912400e002a0
  | 4 => 0x2211904009931252d392498980102608f56000
  | _ => 0
def s5Atlas : Atlas := ⟨5,rawDecor 31 s5Pos s5Neg, 0xfefcfe88fefcfe88fefcfe88fefcfe88fefcfe88fefcfe88fefcfe88fefcfe88fefcfe88fefcfe88fefcfe88fefcfe88fefcfe88fefcfe88fefcfe88fefcfe88, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36414
namespace PEqualNP.Outside.L_meta_36414
open PEqualNP.Outside.L_meta_36414.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xb004001a1af002100f5724000001300c5500600078000759224c5c03e000001f1c808800000000000000066e82273c0003f4a044a86cedb8036000005a01c2c68706190e8c0166a154b928000005e28a8206ac00624200180a000800006080040000084000c4060004100017fd5005fe54017f55005fc5400ffd4c037f5300ff94c03fd5300df54c03fc5300ffd0c03bf4300ff90c03fd4300ef50c03fc43007fd4801fe52007f54801fc52017fd0805fe42017f50805fc4200ffcc803fe3200ff4c803fc32007fd4401fe51007f54401fc51017fd0405fe41017f50405fc4100ffcc403fe3100ff4c403fc31007fc8401fe21007f48401fc21007fd4001fe50007f54001fc50017fd0005fe40017f50005fc4000ffcc003fe3000ff4c003fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a2000ff9951004dfcca88003fd65440017eb2a2000ff1951004df8ca880037c65440013e32a200bffd911005dfec88802ffe64440057f322200bff5911005dfac88802ffc64440057e322200bffd511005ffca88802ffd5444017fe2a2200affd8d10055fec68802bfe63440037f31a200aff58d10055fac68802bfc63440037e31a200affd4d10056fea68802bfe5344015fea9a200adf54d10057f8a68802bff4344015dfa1a200aff90d10057fa868802bbd4344015fe21a2000ffd8910005fec488003fe62440117f3122000ff58910005fac488003fc62440117e3122000ffd4910007fca488003fd5244001fe292200bffd091005ffc848802ffd4244017fe212200affcc910057fc648802bfd3244015fe1922000ffd4510007fca288003f65144001fea8a2000fd54510007f8a28802fff4144017ff20a200bff5051005ff8828802bff3144015ff18a200afd8c510057fa628802bf53144015fe18a2000ffc8510007fc4288003fd2144001fe10a2000ffd411001ffca088003fd5044007fe282200bffd011001ffc808802ffa4044017fea02200bfe5011001ff8808802bff3044007ff182200afe8c110057fa608802bf93044007fe1822000ffc811001ffc4088003fd2044007fe1022000ffc4110007f6208800ffe1044007fb0822003ffd941001dfeca0800ffe65040137f3282003df99410004fcca0800ffd65040017eb282003df59410004faca0800ffc65040077e3282003ffd901001dfec80800ffe64040057f3202003ef990100157cc80800ffd640400d7eb202003ef590100057ac80800ffc64040077e3202006ffd5010037fca80801bfd540400dfe2a02003ffd8c1001dfec60800ffe63040037f3182003f798c1000dbcc60800ffd630400b7eb182003f758c10005bac60800ffc63040077e3182005ffd4c1002efea608017fe530400bfea982005df54c1002ff8a608017ff430400bdfa182005ff90c1002ffa8608017bd430400bfe2182003ffd881001dfec40800ffe62040117f3102003fb98810005dcc40800ffd62040017eb102003fb58810005dac40800ffc62040077e3102000ffd4810007fca408003fd5204001fe2902006ffd0810037fc840801bfd420400dfe2102005ffcc81002ffc6408017fd320400bfe1902007bf98410007fea208013fe5104001fea882004ff14410037fe8208013fe410400dfea082004ff1041002ffe6208013fe310400bfe9882004ff0c410007fe4208013fe2104001fe9082004ff0841001dfcc00800fff5004007ff2802003ff5401001ff8a00800fff4004007ff2002003ff5001001ff8800800fff3004007ff1802003ff4c01001ff8600800fff2004007ff1002003ff4801001ff8400800fff1004007fb8802003ff8401001ff4200800ffd1004007fa8802000fe44010
  | 1 => 0x3fc21080077f3004003ffd402001ffca01000ffd5008007fe2804003ffd002001ffc801000ffd4008007fe2004003ffcc02001ffc601000ffd3008007fe1804003ffc802001fde401000ffe2008007fd1004003ff4802001fda4010023f92008009ffb2e2000bfd9710007fccb88026fe65c4001feb2e2000bf59710027f8cb88026fc65c4009ffb26200ebfd9310077fcc98800afe64c401dfeb26200ebf59310027f8c98800afc64c401dffaa6200eff95310077faa98803bfc54c4009ffb1e2007bfd8f1003ffcc788006fe63c400ffeb1e2007bf58f10027f8c788006fc63c400fffa9e2007dfd4f1003ffca78801ffd53c400fbea9e2007ff14f1003ffe878801fbf43c400fff21e2007ff50f1003f7a878801ffc43c4009ffb162000bfd8b10007fcc588022fe62c4001feb162000bf58b10027f8c588022fc62c4001ffa962000ff94b10007faa588003fc52c401dffa16200eff90b10077fa858803bfc42c400fff9962007ff8cb1003ffa658801ffc32c4001ffa8e2004ff94710007eca388003fd51c4001faa8e2004ff14710077fe8388013fe41c401dfea0e2004ff1071003ffe6388013fe31c400ffb18e2007ff4c71003fea6388013fc31c4001ff90e2004ff88710007fa4388013fc21c4001ffa862003ff94310007faa18800ffc50c401dffa062003ff90310077fa818800ffc40c400fff9862003ff8c31003ffa618800ffc30c4001ff9062003ff88310007fa418800ffc20c4007ffb2c2003bfd961001ffccb08026fe6584007feb2c2000bf5961001ff8cb0800efc6584007ffb242003bfd921001ffcc90800afe6484007feb24200dbf5921001ff8c90800efc648401bffaa4200dff9521006ffaa908037fc5484007ffb1c2003bfd8e1001ffcc708006fe6384007feb1c200cbf58e1001ff8c70800efc6384019ffa9c200cdfd4e10067fca708033fd5384019bea9c200cff14e10067fe8708033bf4384019ff21c200cff50e100677a8708033fc4384007ffb142003bfd8a1001ffcc508022fe6284007feb142000bf58a1001ff8c50800efc6284001ffa942000ff94a10007faa508003fc528401bffa14200dff90a1006ffa8508037fc4284019ff994200cff8ca10067fa6508033fc32840157eb0c2000ffd4610007fca308003fd5184001fe28c200dffd061006ffc8308037fd418401bfe20c200cffcc610067fc6308033fd3184019fe18c2000ffc8610007fc4308003fd2184001fe10c2003bf9821001ffea10800ffe5084007fea842003ff1421001ffe810800ffe4084007fd2042003ff5021006ff2810800ffc4084007ff9842003ff8c21001ff4610800ffd3084019fc9842003ff0c21001ffe410800ffe2084007fe9042003ff0821001ffe210800ff71084001fd8842000ffd9510005feca880037f65440013fb
  | 2 => 0x2001ffcc310002fe6188007feb0c4000bf5862001ff8c310003ff5188001ff28c4000ff54620007f8a310053ff4188029ff20c4014ff506200a7f8831004fff3188027ff18c4013ff4c62009ff86310023ff2188001ff10c4000ff48620047f8431000efe6088007ffa844003ff9422001ffaa11000ffc5088007ffa044003ff9022001ff4811000ffd4088029fca044003ff1022001ffe611000ffe3088007fd1844003ff4c22009ff2611000ffc3088007ff9044003fbc8220047f64110003ff65480017fb2a4000dfd9520004feca90003fe65480137f32a4000ff59520005faca90003fc65480137e32a4000df19520004f8ca9004bff64480257fb224012ff99120015fcc89004bfd64480257eb224012ff19120015f8c89004bff5448025ff2a24012ff55120097f8a890047ff63480237fb1a4011ff98d2000dfcc690047fd63480237eb1a4011ff18d2000df8c690047ff5348023bfa9a4011ff94d2008ffaa6900477d5348023fe29a4011ffd0d2008f7e8690047fe4348023fea1a4011ef50d2008ff88690003ff5248011ff2924000fb94920007faa490003ed5248011fe2924012ffd0920097de8490023fe4248025fea124008ff10920097d88490047ff3248011ff1924011fb8c92008ffa6490047ed3248011fe1924000ffd8520005fec290003fe6148001feb0a4000ff18520005f8c290003ff5148001ff28a4000ff54520007f8a29004bff4148025ff20a4012ff50520097f88290047ff3148023ff18a4011ff4c52008ff86290023ff2148001f790a4000ff88520007fa4290003ed2148011fe10a4000ffd412001ffca090003fd5048007fe2824012ffd012001ffc809004bfa4048025fea024012fe5012001ff88090047ff3048007ff1824011fe8c12008ffa6090047f93048007fe1824008ffc8120047f6409000ffe2048007f71024003ffd942001dfeca1000ffe65080137f3284003ff59420005faca1000ffc65080077e3284003ffd902001dfec81000ffe64080057f3204003ff59020085fac81000ffc64080077e3204010ffd5020087fca810043fd5408021fe2a04003ffd8c2001dfec61000ffe63080037f3184003ff58c2007dfac61000ffc63080077e318400fffd4c2007efea61003ffe530801ffea98400fdf54c2007ff8a61003fff430801fdfa18400fff90c2007ffa861003fbd430801ffe2184008bf98820047fea410023fe5208011fea904008ff14820047fe8410023fe4208011fea104008ff10820047fe6410023fe3208011fe9904008ff0c82001ffec21000ffe61080017f3084003ff58420005fac21000ffc6108001ffa884000ff94420007faa210003fc5108021ffa084010ff90420087fa8210043fc410801fff988400fff8c42007ffa621003ffc3108011ff9084008ff88420047fa421002
  | 3 => 0xea18a017ff10c5001ffec42800ffe62140117f310a003fb98850005dcc42800ffd62140017eb10a003fb58850005dac42800ffc6214013ffa90a009ff94850006fca428027fd5214013fe290a009df148500c7fe8428063fe4214031fea10a018ff108500bffe642805ffe321402ffe990a017ff0c85001ffec22800ffe61140017f308a003fd98450005ecc22800ffd61140017eb08a003fd58450005eac22800ffc6114013ffa88a009ff94450006fca228027fd5114013fe288a009df144500c7fe8228063fe4114031fea08a018ff104500bffe622805ffe311402ffe988a017ff0c450007fe4228003fe2114001fe908a000ff0845001dfcc02800fff5014007bfa80a003ff9405001ff4a02800ffd5014007bea80a009fe5405001ffe802800ffe4014007fea00a003ff1005001ffe602800ffe3014007fe980a003ff0c050047fecb90022ff65c8011ff32e4009bf99720047facb90002fd65c8011fe32e4008bf19720047fec990022ff64c8011ff3264002bf99320047fac99005afd64c8011fe3264008bf193200b7fea99005bfe54c802dfeaa64016ff15320047fec790022ff63c8011ff31e4001bf98f20047fac790056fd63c8011fe31e4008bf18f200affea7900577f53c802bff29e4015ff54f200aefaa790057fc53c802bffa1e4015efd0f200affc8790057fd43c802bdea1e4015ff10f20047fea590023fe52c8011f72964008ff54b20007daa590023fc52c8011ffa164016fbd0b20047fc8590023fd42c8011fe2164008fb10b20047fe6590023fe32c8011f71964008ff4cb200afda6590023fc32c8011ffb0e4008ff98720005fcc390023fd61c80017eb0e4008ff18720007fea390003fe51c8001fea8e4000ff147200b7fe839005bfe41c802dfea0e4016ff107200affe6390057fe31c802bfe98e4015ff0c720047fe4390023ef21c8011ff10e4008ff48720007da4390023fc21c8001ffa864003ff94320007faa19000ffc50c802dffa064003ff903200b7fa819000ffc40c802bff9864003ff8c3200affa619000ffc30c8007ffb2c4003bfd962001ffccb10026fe6588007feb2c4000bf5962001ff8cb1000efc6588007ffb244003bfd922001ffcc91000afe6488007df3244002af9922001ffac910052fd6488007deb244000af5922001ff8c91000efc6488029ffaa44014ff952200a7faa910053fc5488007ffb1c4003bfd8e2001ffcc710006fe6388007feb1c4013bf58e2001ff8c71000efc6388027ffa9c4013dfd4e2009ffca71004ffd5388027bea9c4013ff14e2009ffe871004fbf4388027ff21c4013ff50e2009f7a871004ffc43880237eb144000ffd4a20047fca510003fd5288011fe2944014ffd0a20047fc8510053fd4288011fe2144013ffcca20047fc651004ffd3288011fe1944003ffd86
  | 4 => 0xffe30d403bfe986a003ff0c3500cdfacb2800fff64940077fb24a003ff99250015fcc92800ffd64940397eb24a003ff1925001df8c928027ff5494039bfaa4a01cff952500e7faa9280737d5494013fe2a4a003ffd8e5001dfec72800ffe63940037f31ca003ff58e500ddfac72800ffc63940077e31ca009ffd4e500defea72806ffe5394037fea9ca01bdf54e5004ff8a72806fff4394037dfa1ca01bff90e500dffa872806fbd4394037fe21ca003ffd8a5001ffcc528022fe6294007feb14a000bf58a5001ff8c528027ff5294001ff294a000df94a50007faa528027fc5294001be294a01cffd0a500e7fc8528073fd4294039fe214a01bffcca500dffc652806ffd3294037fe194a003ffd865001ffcc328002fe6194007feb0ca000bf5865001ff8c328027ff5194001ff28ca000df94650007faa328027fc5194001be28ca01cffd06500e7fc8328073fd4194039fe20ca01bffcc6500dffc632806ffd3194037fe18ca000ffc8650007fc4328003fd2194001fe10ca003bf9825001ffea12800f7f5094013fda84a003ffd025001ffc812800ffd4094007fe204a003ffcc25001ffc612800ffd3094007fe184a01affd91500d5fec8a806bfe64540057f322a01aff591500d5fac8a806bfc64540057e322a009ffd51500d7fca8a806bfd5454013fe2a2a019ffd8d500cdfec6a8067fe63540037f31aa019ff58d500cdfac6a8067fc63540037e31aa009ffd4d500cefea6a8067fe5354033fea9aa019df54d5004ff8a6a8067ff4354033dfa1aa019ff90d500cffa86a8067bd4354033fe21aa000ffd8950005fec4a8003fe6254001feb12a000ff18950045f8c4a8027ff5254001ff292a000ff5495004ff8a4a806bff4254035ff212a01aff509500d7f884a8067ff3254033ff192a019ff4c9500cff864a8003ff61540017fb0aa000ff98550007fac2a8003fc61540017e30aa009ffd4550006fea2a8003fe5154001fea8aa000df5455004ff8a2a806bff4154035ff20aa01aff505500d7f882a8067ff3154033ff18aa019ff4c5500cff862a8003ff2154001ff10aa000ff48550007f842a8027ff5054013fda82a003ff9415001efca0a806bff4054007ff202a01aff5015001ff880a8067ff3054007ff182a019ff4c15001ff860a8026fe6514007ffb20a003bfd905001ffcc82800afe6414007df320a002af9905001ffac828062fd6414007deb20a000af5905001ff8c82800efc6414013ffaa0a009dfd505004ffca828027fd5414031beaa0a009ff1505001ffec62800eff6314007ff318a001bf98c5001fbcc628006de6314007feb18a017bf58c5001fbac628002dd6314007fe318a003bf18c5004ffea6280277f5314013ff298a009ff54c500befaa628027fc531402fffa18a017efd0c500bffc862805ffd431402fd
  | 5 => 0xd21117fa869088bbd4348445fe21a4200ffd4921007dea490823fe5248401fea924208ff14921007d8a49088fff4248411ff2124223fb9092111ffa849088fed4248411fe2124222ffcc921047fc649088bee3248445fe9924222fb4c921047f86490803ff5148401ff28a4200ff54521007f8a29088fff4148447ff20a4223fd9052111ffa829088ff54148447fe20a4222ffcc521117fc629088bf63148445fe98a4222fd4c521117f86290823ff2148411fb90a4200ff88521007dc4290803ff60484017fb024200ff98121007fac090803fc60484077e3024223ffd012111ffc809088ffd4048447fe2024222ffcc121117fc609088bfd3048445fe1824204ffd9421045feca10823fe65084137f3284208ff59421005faca10813fc65084117e3284204ffd9021045fec810823fe64084057f3204208ff59021105fac810813fc64084117e3204220ffd5021107fca810883fd5408441fe2a04204ffd8c21045fec610823fe63084037f3184208ff58c210fdfac610813fc63084117e318421fffd4c210fefea61087ffe530843ffea98421fdf54c210fff8a61087fff430843fdfa18421fff90c210fffa861087fbd430843ffe2184208bf98821047fea410823fe5208411fea904208ff14821047fe8410823fe4208411fea104208ff10821047fe6410823fe3208411fe9904208ff0c82110dfcc210803ff5108409ff2884200ff54421027f8a210883ff4108409ff2084220ff50421027f8821087fff3108409ff188421fff4c421027f86210823ff2108411f79084204ff88421047ec4210823fd2108401f69084208fd48421027fec010823fe60084077f3004208ff58021005fac010813fc6008441ffa004220ff90021107fa8010883fc400843fff980421fff8c0210fffa601087ffc3008413ffb26a009bfd935004ffcc9a800afe64d4013feb26a01ebf5935004ff8c9a800afc64d4013ffaa6a009ff9535004ffaa9a8027fc54d4013ffb1ea009bfd8f5004ffcc7a8006fe63d4013feb1ea01dbf58f5004ff8c7a8006fc63d4013ffa9ea009dfd4f5004ffca7a8027fd53d403bbea9ea009ff14f500effe87a8077bf43d403bff21ea01dff50f500ef7a87a8077fc43d4013ffb16a009ff98b50045fcc5a8027fd62d40017eb16a009ff18b5004ffea5a8027fe52d4013fea96a009ff14b500f7fe85a807bfe42d403dfea16a01eff10b500effe65a8077fe32d403bfe996a01dff0cb5004ffec3a8027fe61d40017f30ea009ff58750005fac3a8027fc61d4013ffa8ea009dfd475004ffca3a8027fd51d4001bea8ea009ff147500f7fe83a807bfe41d403dfea0ea01eff107500effe63a8077fe31d403bfe98ea01dff0c750007fe43a8003fe21d4001fe90ea000ff087500f7fe81a800ffe40d403dfea06a003ff103500effe61a8
  | 6 => 0x1fea00a228ff1005113ffe602889ffe301444ffe980a227ff0c051047fecb90822ff65c8411ff32e4209bf99721047facb90802fd65c8411fe32e4208bf19721047fec990822ff64c8411ff3264202bf99321047fac99089afd64c8411fe3264208bf19321137fea99089bfe54c844dfeaa64226ff15321047fec790822ff63c8411ff31e4201bf98f21047fac790896fd63c8411fe31e4208bf18f2112ffea7908977f53c844bff29e4225ff54f2112efaa790897fc53c844bffa1e4225efd0f2112ffc8790897fd43c844bdea1e4225ff10f21047fea590803ef52c8411ff2964208ff54b21047f8a590823ec52c8411ffa164208ff90b21047dc8590823fd42c844df6a164208ff10b21047fe6590823fe32c8411f71964208ff4cb2112fda6590823fc32c8401ffa8e4200ff94721007faa390803fc51c844dffa0e4226ff90721137fa839089bfc41c844bff98e4225ff8c72112ffa6390897fc31c8411ffb064208ff9832101dfcc190823fd60c84017eb064208ff18321137fe819089bfe40c844dfea064226ff1032112ffe6190897fe30c844bfe9864225ff0c321027fecb10802ff6588401ff32c4209bf99621006fccb108027e6588401feb2c4200bf59621006facb108027d6588409fe32c4209bf19621027fec910892ff6488449ff3244202bf99221127fac910892fd6488409fe3244202bf19221127fea910893fe5488449feaa44224ff15221027fec710886ff6388443ff31c4201bf98e2110ffac710886fd6388409fe31c4201bf18e2110ffea7108877f5388443ff29c4221ff54e2110efaa710887fc5388443ffa1c4221efd0e2110ffc8710887fd4388443dea1c4221ff10e21115fac510803ff5288411ff2944200ff54a21047f8a510893ff4288411ff2144224ff50a21047f88510887ff3288411ff1944221ff4ca21047f86510822fe6188401ffa8c4204ff94621007faa310813fc5188449ffa0c4204ff90621127ec8310893fd4188449faa0c4204ff1062110ffe6310813fe3188443fb18c4221ff4c62110fea6310813fc3188411ff90c4200fbc8621047ee4310813ff6088401ff3044203bf98221007fac110802fd6088409fe3044224ffd0221127fc8110893fd4088449fe2044221ffcc22110ffc6110887fd3088443fe1844200ffd9521005feca90803fe65484137f32a4200ff59521005faca90803fc65484137e32a4223ffd912111dfec890803bf64484015fb224223ff99121015fcc89088ffd64484477eb224223ff19121015f8c89088fbc64484055e3224223ffd512111ffca89088ffd5448447fe2a24222ffd8d21115fec69088bfe63484037f31a4222ff58d21115fac69088bfc63484037e31a4222ffd4d21116fea69088bfe5348445fea9a4222df54d21117f8a69088bff4348445dfa1a4222ff9
  | 7 => 0x288a7fe63944037f31ca229ff58e5114dfac728813fc63944037e31ca209ffd4e5114efea7288a7fe5394453fea9ca229df54e5104ff8a7288a7ff4394453dfa1ca229ff90e5114ffa87288a7bd4394453fe21ca204ffd8a51007fcc528822fe6294401f7314a200bb98a51007fac528802fd6294401f6b14a200bb58a51027f8c528827ff5294401ff294a200ff54a5104ff8a5288b3ff4294459ff214a22cff50a51167f885288a7ff3294453ff194a229ff4ca5114ff86528826fe6194413ffa8ca200dfd465104feea3288b3ff4194409ff20ca22cff50651027f883288a7ff3194409ff18ca229ff4c651027f86328813ff6094401ff304a203bf98251007fac128802fd6094409fe304a22cffd0251167fc81288b3fd4094459fe204a229ffcc25114ffc61288a7fd3094453fe184a22bffd915115dfec8a88affe64544057f322a22bff5915115dfac8a88affc64544057e322a209ffd515115efea8a88affe5454457feaa2a22bdf5515104ff8a8a88abff63544557fb1aa22aff98d5100dfcc6a88abfd63544557eb1aa22aff18d5100df8c6a8827ff5354455bfa9aa22aff94d51157faa6a88ab7d5354413fe29aa22affd0d511577e86a88abfe4354455fea1aa22aef50d51157f886a8803ff62544017fb12a200ff98951007fac4a8803fc62544117e312a209ffd4951007fca4a88037e5254401fea92a209ff14951006f8a4a88afff4254457ff212a22bff5095115ff884a88abff3254455ff192a22aff4c951157f864a8827ff5154413fba8aa200ff94551006fca2a88afff4154457ff20aa22bff5055115ff882a88abff3154455ff18aa22aff4c551157f862a8803ff60544017fb02a200ff98151007fac0a8803fc60544077e302a22bffd015115ffc80a88affd4054457fe202a22affcc151157fc60a88abfd3054455fe182a209bf99451027fec828826ff6414413ff320a202bf9905104ffac8288a2fd6414409fe320a202bf1905104ffea828827fe5414413feaa0a209ff15051027fec628826ff6314413ff318a201bf98c5104ffac62889efd6314409fe318a201bf18c5104ffea6288277f5314413ff298a209ff54c5113efaa628827fc531444fffa18a227efd0c5113ffc862889ffd431444fdea18a227ff10c51027fec428827fe62144117f310a209ff58851005fac428813fc6214413ffa90a209ff9485104ffaa428827fc5214451ffa10a228ff90851147fa84288a3fc421444fff990a227ff8c85113ffa642889ffc32144537f308a209ffd445104efea228813fe5114413fb288a209ff54451006faa228827f55114451ffa08a204ff90451147fa8228813fc411444fff988a204ff8c45113ffa6228813fc3114409ffb00a209ff9805101dfcc028827fd60144017eb00a204ff18051147fe80288a3fe401445
  | 8 => 0xf18d5200df8c6a9027ff5354863bfa9aa431ff94d5218ffaa6a90c77d5354813fe29aa431ffd0d5218f7e86a90c7fe4354863fea1aa431ef50d5218ff886a9027ff5254813f7a92a408ff94952046fca4a90cbff4254811ff212a432ff50952047f884a90c7ff3254811ff192a431ff4c952047f864a9003ff61548017fb0aa400ff98552007fac2a9003fc61548017e30aa432ffd0552197fc82a90cbfd4154865fe20aa431ffcc55218ffc62a90c7fd3154863fe18aa400ffd8152005fec0a9003fe6054801feb02a400ff1815201df8c0a90cbff4054865ff202a432ff50152197f880a90c7ff3054863ff182a431ff4c15218ff860a9026fe6514811ffb20a408bfd9052047fcc82900afe6414811feb20a430bf59052047f8c829022fc6414813ffaa0a409ff9505204ffaa829027fc5414811ffb18a408bfd8c52047fcc629006fe6314811feb18a42fbf58c52047f8c629022fc6314813ffa98a409dfd4c5204ffca629027fd531485fbea98a409ff14c5217ffe86290bfbf431485fff218a42fff50c5217f7a86290bffc43148117f310a408ffd4852046fea429023fe5214811f7290a408ff54852046faa429027ed5214811ffa10a408ff90852047fa8429023fc4214811ff990a408ff8c852047fa6429023fc3214811ffb08a408ff98452005fcc229023fd61148017eb08a408ff18452187fe82290c3fe4114861fea08a430ff1045217ffe62290bffe311485ffe988a42fff0c452047fec029023fe60148077f300a408ff58052005fac029023fc6014861ffa00a430ff90052187fa80290c3fc401485fff980a42fff8c05217ffa60290bffc3014813ffb26a209bfd935104ffcc9a880afe64d4413feb26a22ebf5935104ff8c9a880afc64d4413ffaa6a209dfd535104ffca9a8827fd54d445dbeaa6a209ff1535104ffec7a8826ff63d4413ff31ea201bf98f5104ffac7a88b6fd63d4413fe31ea201bf18f5104ffea7a88277f53d4413ff29ea209ff54f5116efaa7a8827fc53d445bffa1ea22defd0f5116ffc87a88b7fd43d445bdea1ea22dff10f5104ffec5a8827fe62d44117f316a209ff58b51005fac5a8827fc62d4413ffa96a209ff94b51006fca5a8827fd52d4413fe296a209df14b51177fe85a88bbfe42d445dfea16a22eff10b5116ffe65a88b7fe32d445bfe996a22dff0cb51177fe83a88bbfe41d445dfea0ea22eff1075116ffe63a88b7fe31d445bfe98ea22dff0c75104ffec1a8827fe60d44077f306a209ff58351005fac1a8827fc60d445dffa06a22eff90351177fa81a88bbfc40d445bff986a22dff8c35116ffa61a88b7fc30d44557eb2ca204ffd9251165fec9288b3fe64944057f324a22cff59251165fac928813fc64944057e324a209ffd5251167fca9288b3fd5494413fe2a4a204ffd8e5114dfec7
  | 9 => 0x101100600100101b00000600a00800701200100200800100400000100b00200600000000f00100000500000101600600001300000300300600700400300000c00100a00000600c00100001700000100000400100100000100000100000000600000100a01700001800c00200800200100000100400a01200a01101d00400000200000e00200000f00500600000000300200001100000200000000300000300200000301a00200600000300d00200900100100200000000200200000300000400000000201a00800200600b00200200200100000001600200701500000100200800200000103200300d00400100200200100801000000002100000000500400900100300000000f00400000704ffec9a9026ff64d4813ff326a402bf9935204ffac9a90dafd64d4813fe326a402bf1935204ffea9a90277f54d4813ff2a6a409ff553521b6faa9a9027fc54d4813ffb1ea409bfd8f5204ffcc7a9006fe63d4813feb1ea435bf58f5204ff8c7a9006fc63d4813ffa9ea409dfd4f5204ffca7a9027fd53d486bbea9ea409ff14f521affe87a90d7bf43d486bff21ea435ff50f521af7a87a90d7fc43d486dffa16a408ff90b521b7fa85a9023fc42d486bff996a408ff8cb521affa65a9023fc32d4813ffb0ea409ff98752005fcc3a9027fd61d48017eb0ea409ff187521b7fe83a90dbfe41d486dfea0ea436ff107521affe63a90d7fe31d486bfe98ea435ff0c75204ffec1a9027fe60d48077f306a409ff58352005fac1a9027fc60d486dffa06a436ff903521b7fa81a90dbfc40d486bff986a435ff8c3521affa61a90d7fc30d48637eb2ca408ffd9252045fec929023fe64948057f324a408ff592521a5fac929023fc64948117e324a409ffd52521a7fca9290d3fd5494813fe2a4a408ffd8e52045fec729023fe63948037f31ca408ff58e5219dfac729023fc63948117e31ca409ffd4e5219efea7290cffe5394867fea9ca433df54e5204ff8a7290cfff4394867dfa1ca433ff90e5219ffa87290cfbd4394867fe21ca408bf98a52047fea5290237f5294813f7a94a408ffd0a52047fc8529023fd4294811fe214a408ffcca52047fc6529023fd3294811fe194a408ffd8652047fcc329002fe6194811feb0ca400bf58652047f8c3290d3ff4194869ff20ca434ff506521a7f883290cfff3194867ff18ca433ff4c65219ff86329023ff6094811ff304a403bf98252047fac129002fd6094811fe304a434ffd02521a7fc81290d3fd4094869fe204a433ffcc25219ffc61290cffd3094867fe184a432ffd9152195fec8a90cbfe64548057f322a432ff59152195fac8a90cbfc64548057e322a409ffd5152196fea8a90cbfe5454865feaa2a432df5515204ff8a8a90c7ff63548637fb1aa431ff98d5200dfcc6a90c7fd63548637eb1aa431f
  | 10 => 0x2476d1049cc4b9660c000004012208e24f106503664930f9bac0000000001308cf00000001bec7128133889e3476e44e166918861800003d9f9882e4a937e003852e10d33800000007e81fd000000064440804701a41f700000008bc000000000042a00000000000000000000c240007c914a01e4e0000000006540003f8000000000000040b00002480001ba08d4d3e0000ce11ec966685000000000000000000008be1593bd000011e7f818a99482de20a21400007c80001f60000000859000137c0003e239d88304165b810c85a00000b0119800000000800500100000000200001700200000000400d00900100600000100000c00100800300100500000100b00200b00700200000300100100000400101300100000900800200001500000400001300300100000301900000000100500c00100100200600000100000200900000600700000000000200700001500400000000100700000200200000c00100100300000400300000100000a02000e00001600100b00100000000100200900200700300001a00000200000100100200000000000200100100100400500200000200000700100400000300300000000200300100200100100100000000000000600600700000100200300000e00d00000400000000200100001300000000d00000200200001600000000400300200800100000500300f00700300100d00600300400100801100000f00600000000000201300500200300000000400000900200000400001300100c00100600c00000200500700001a00000000700000600000200000300000300d00000100000900500000200000600800200100000100000000100100900500400500000500400701700001000100000200300000000400100100100800a00000200000000000000300200100000f00800c00000300400100000000100000700200001600000d00300001000800000100100101200000000200800100000600000000100100000800000200300100402000900000100500000a01e00000e00200000100000000000100000100e00101200000e00300200300000100800000400000600000400100a00800300b00700001200001f00c00000000100000e00000000000000300000000400c00000000000500200200700c00600900000200200000200000100c00300300200000200300500001000000100100100800100000200200000100100100000000200000600300000b00001000000200000000500000d00400100d00501300500200100f00c00000000200000200600600000100100000100500c00200000400100100400000400000100000200000300000200000100500000700001800000000a00000b006003000001013000010001007004005002000008001001001000000006002005003001004014007002
  | 11 => 0xf0a114f520e21a4000000027d000000067a00001e07f4c3c82222b0fe47500000001a24de23d434d9d880006da0e48b1814a23c00000007bc000000000025654a0001a9d0d675e05586d07c600007a00000000004280000f6421b25d9958e967b90000000178579032800000021f00000007c24980c18000ce60000001c1cac02d10000430c107ce26800fc00005f3a493d80582063e09894a5a5462e3860091a0e91f280004aa1920d3042c7b465e0000d2c0a42c11d393846d600012e9af06c40eb08b8c001f22a600003a80002bf2e881788381a81e08fa4cb80ec1eb80000001f9000011c0000003c6173c1e22df21c815014083a1a685a896a2e510e15303dc3943b003203ba00000002201e446e000000000083600012f80004ec00009c000043300000010124ca0cb80000003ee0a78f0c000000000170400058815b0000f4e0000d598a007c43e1b507a400048c000000000026940316d00007a341b853445e22d09a0e90c125f300000000004bf00000000006270000000d5254f1c880008f0000011059c00060a3828000a0800000004a474430b00001e84ca60e0000000f486f700f00006987ba00000000000000000d0c000298000000027650d1b0902c7a40000000000b7c0b50000db400000014a9ca08cc03400019946a077140f000080e000144000000036c3f8007c6020000fc00000005d22741c9400000000000000000000001cd000064e4300308bf44c90001d60be05bc3629a0c4dc2e425b11f0b6a4082e806fc5c000021316d84de3951c8098c00069901900010a66aa0941f6498278f3218000a600003620684a0e2710aa8000fa20003359194ad86ab40f80000004e20000ea4b745121c900000002a9089091c84600000006b00005da1a78000f8837c2489d848a86580278ea8d5e000000000000070d06381680006132931f74a7e1061220000e0600042f80003c026c2fb069109e000000005400000026c8a805c20003ad800000004a0000000dde0003389da0a164431b00580000000000162c7e00001911908d260933e82130c6485e0e50e20bd67c000012740001d71b70a1c5085710be8da00ce66e21b000000000000020bca920003720000c5c00000019e4fea0e11d98a946f60000000b403da0003de8cb40001be0719f3cb0422442106ec3520461601fece8647330381f02886fa2a280000000002640000e9c5a92fc093c57c56a0d518807ce2341339338ff40b84159f78a1044207703d408600002c8000f5e7df00010c89b00000001220bd479c1c983042c60000b80a140002323cc00000007894148000882367000176c00000000010bc0003b61a89f8cdc60000000000000767000066c15054b28180a466e4a00de00000000001e49aa0db035737280000000003cb1840f906cb0b212c00000003500000e
  | 12 => 0x5110f60bac0700d5000156000000017f9e4c8b472b33d9f9097223000012f4ca624b1350d1c2223690311b98b4e3cb39a9d2800049a08c0a2c2cc00033093b88de0002b193bc0001413518e08de600011584f45d800b3c521101f482e37600140001c207e899800000000000000004ba1b318ec0006b2000000077200009f0000cba00008d9ec4ae03f542183984704cf0e6000104e4ab046165400052200021940005c338d890400082812f80000000003c21a6000051600980000008051df1598d707011251ec0a4a0e437494f4c5a38e3ca0a7c7da33b266a0b0fb07042830a38f3633c18f945c0567913ca9d948fc53c0669134c6e42b00000002a614e07d899082c75d17186590ce7991770df4c2c86917f139838a65501d00a85f830500c0ee083600c4309248bc628f30895a03ac0973bc0000d9e7c7006800074667611500002f60000000000b320003b516040006dc2ba96c000000036890688020003d00fd862c32e42a8fd00224da10a1b5071a7d21fb8b2038c7f60000e0c90c3791591a348947242ec8000000000000113058e07600000003f65440001b280003fb40a00003fc2bd34b0000fce7c62bb18d8a464831bb016ca1438c3af9708fd20000b68000000000000000063435b00000006206b73ad0000a3200000021049e029e2d70268526444143000078c4d63ab0000fd80a7000013000073e00000006b81f40c203100005a242a00000000000000a440000d41218000bdc7360de81b89a64e519a8754cda39e04d850c4d04ac21c094034059f2351f14efe7571ed9dc073466903991b00006b42308bf40001c800016980004e32b08c190b04470f595a4cd4000000160098856200000006667f33d60488dea30f38494310461fa3ea98d0da68082bc19400000003b60fbcd0000000014d400000036b012caa60000000000b28162000047c0004a7000000000000015b95400007cc400000055c55700001b00000000af0330000000000062c0620003b799f40c84373c392948fe83d3c705f076a000000000039600004807a876248e00002980007db27a879400056b11d9484000450000057c5de0003a210882ea09f2950000fd60000001640c78025000000053a0003bd8b6402e76b09688680007271d914d00001023001a740002a300018e40003ce00020a908000011000000000000001d003a800000005cc81e2ad09c800000033e000166040a00000000007360923990768d2000000015fc6460002759050e40421000066884e7170f20f30f2e494035081cbd87770618820f1600642e96140001a72390000a0a458069800000000029d8000bc86c20c9946817a70812d8c20c2a5000bca0c4b1e2462389dd0f0c0e800a114401e45234e150026e154352186cdba00034600000000000000a480004e41f51e14cc41872
  | 13 => 0x1c30838a8e00a2541f2c0000a40000a24a2000037c988838883c02b04980000e000000007b273f0bf811063a37f21494b106800000019b00000000000000f6c0bb0001e000006f23f780005b87370e0139c5140002948a9000020300011a4b423d60000c44ae8000218115cf0425100000006505021ce80000007a101b0000bee56e00000000000300000ef421c000151000038274600013703b60002eb00002280000001bc00d219f00000a0000811000000000000042d868cb981250b0837803201c21019005685862b799200006c80000df800030d00000000004900ec950800083f2279fc80120000000ed08041ff04c8984cb21993861534b0840510c05948d07ff0000aec6ca0001850000d2e0950000c7000000029b00000004820000fcc00003b00013a45000070bd0ca80000000000420c542af0f921709b63873b200000004f200000003e00f33181270c081773a2880857034e00d025815805817b18fce3c07242b86dc95c55100017a00004cc3a39d8c00072133196742947410000798000000000000000074800014c800067500000004462d700010f08066e10001c3cf2073338b02a894236415588b8a5e39f06f8144b220002601d300000002a0800000067432d00005aa7cd40e00000ba33806c0548cb63261a91be0f5c5d424f8c5c6aa86a0728aa05740023c4078865e6c731200000a65dd34a90f4c040000651ff866860f02701c000065f30a1b3400051b19d05b0d4c5e70a280000000002c6847843a1df0f88000dc008b03a96fc5325fb1df889829681742717c4a7c6e70ab05acc940be3be93f807a23a2ff0f146364dd22e89e41ba00034f053000058a000167000000000000003a00003dfa12c88027a00013f0a120d61d5988c94c3a01e21cf400013012e000000015012980000003a1349000044e5a0000000000000027680004ee00038a97349d40000c515ec3640000000ce40007bc05d16ec5ba00000000000003a5164811501a6380000d7cd8200000000000000003511ac090a1940d81d4000055e3be0acceb80b734203240007920001ad800000000000000840000001df90720001bd10c40000000c484746ac5673fe8facab80002d889680000000000000e7800000011dc98e0a100000003225010001a4400042e41280000005fc3230ba01fc7a610f00000003e00fe00004720ce042000000012e000035c8b845900008dc00080c33e02144ac7813600574452318120178000072c26b800000000007c00004bc0001f90000000000000000000002132297e450252400000003de00036c85e00000823c180001ce00000016bc0007531a500004021880000cfd04c0001e99c182420002aa027800082020500000001b81a300000005a3171000000000000000000004de38a0f7cc2e17200000000000000001c70
  | 14 => 0x4fda57c076800000055b208800000000000000003660002d280000000001c08c48dc466804494e05780001359f0c0004f3000000000000000000000000002d5000088a00018a0368abe626000000000068619280000008463f70c08146514158800000000000007cc00023640180008745e503f00001000493068bb4eea4101ad04b05e81a20cf20740fe8510469678dbc0a237a1eccc2424923594383d03852300dbcd144800409788be80000001c3886a60b0ce9ee00000003598218aac0c609c123c00019800005700006db0001c28dda7693e11884b2608729b800047c00000000000000000168000000000000000000000019480007160f72e700cce161811d800005603783aa00dcdd4802000000058a52840d1f68ae671d024000000046336190742ec67a1ba879c1960610a496e416282d150909444a1f52a415b426c0000000000586518000000101c7420000000f6e25435710d0b6e592000199c8ec0000001c6818049516d8b58be44d500000004420ad00000003b00003cd02d000000000000000003d83560a4000000000000000000000809d48b065b3095100072c4d20b8a0c08c842a0139ce80a00003fa15940006d519580004842222cd071c73018d00916f49e880a04a0dc40003491b8000000000000003648244240ad00005943ca0ab8000000000000000000084a0000000ca20001020000e608072bba0647f872d11f8000f3c0bf000000029000000000000000003ce80007583af27e965859c1162bd00000002fb0340ad497849901c8c9cbde54e3dd9868b480a908209fc8927d73fc85184f000800000002200000000000e720c522d912d0c847500000000000000000000000258000000061c330394919c000000178800036c000020975c2b01b13f1085c7a06b12160274d0420035a8c0c20a0003528d4c498000000063ce700014341060e4c5523cf8ae400000037b1f800003ad21695750cc7020000000000000000000095e000000000072e0000000000fd40002901b5c732000251000000000000018740000003fb8000b8c0770001c400000003160dc800000014e0fc4a562ea059864091400000001e027483535d8dcc4582483bb01b426a00029980000000000000d789028153e50b9800032037f800000000007e043cc0c000350874c11446d156091410639c12b8d74ee63401989e88000000300800000000000000000006fd0000cc8d165d5083800060e0001300b9c00057e00000000005550001afc0000000f18000000000000131800074f42691d04625c923d0cd800068800e93c40002c40001760000000000084098a64f10897b4d7c4a32d9163895a4a428a8c100d600019212246a86c900020110480000000000000564000000080c7be2879d6471e0000318a34584182000172909262b32b8bcc632000
  | 15 => 0xcde3ae0ee08347cc3c806e0154c5253123c8ba4d1e80f29d08480004d127b9cbc00021300000007740003568aa800052e3b31b4039c35800000000000000000000edc00000b0000000000000040cc7c0000988f080002f900000000007d641c00001fe0740000000ef22a741f18147fa0000f0925cf5600000000008265ad0ad8bdc06a00033b800000025900000000000001ff8000b5067f3330618e3e1000c60000b187230001e943bc140000122cd1c13c325974c5e0115224000000072e1270bd40005870dc80000007e532a0f740005130000000fb80001a280000005890000b480000003630340bbc11300000800000000000000c387190000a30234000000126ca3c6182f320ec2dc0d13690000d3474d2d580002e88480000b6825e6031e3a04890e00314102e4dbe4090000f3ca384b125c0ff83860000c28000cfc00000000000007e10021210ce40003a89ed49867a842d0f34c3263524b04ccc6237733010ec49a000038815cb8083205b17fc0003dc2b900000004e000000005f418e0001ba01ec000000000000000000000005a64f90001c6004600009388f4d280db3178be05bc5c801791c000000000000000004f8323935015e36300009c800082116a05a4b886bd000000000077208c9ae48180000001ea882a00022a87d883e1510d2a18c658380084800045002414b0d105b034104c124d0ac1ad3408ef059804d37f177cb8a5590379990c9a000423914c2467fc00012a80003a613f1a1c81c4cb1791eb400000023e80000003c03ea0948a3e6ba0001b3800080109010fcc66641000027063c1320000d6400080b09f97f40002cb14d92dcbb81b52591474f684fa00009cc6840001c209d400014700013ec0b800027f9b3019e31314185f853426d16785087aa72243109d039a1cf2cd874803606607782c82145ac13b00b80803bb030111842c20f389a0604f600000017d464200013101f437463d0000000afa0001c506b804c1d113e000081a0f005700000007d329c901035e3d1000149d0a46ee20f0fa0eaa8332ad12d0c9863a395165cbd25430001fc
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xf7358810006ee7358810006ed7358810006ec7358810006ef53588100066f5358810006ee5358810006ed53588100066d5358810006ec5358810006ef4358810006af4358810006ee4358810006ed4358810006ad4358810006ec4358810026ee7158810026ec7158810026ee5158810026ec5158810006ef4158810026ee4158810006ed4158810026ec4158810006ef3158810026ee3158810006ed3158810026ec315881001eef705881001eee705881001eed705881001eec705881001eef505881001eee505881001eed505881001eec505881001eef405881001eee405881001eed405881001eec405881001eef305881001eee305881001eed305881001eec305881001eef105881001eee105881001eed105881001eec105881004cff76d481001cfe76d4810004fd76d481001cfc76d481004e7e65d48100067d65d48101b6be64d4810006bd64d48101aede63d4810006dd63d4810046ee62d4810006ed62d4810044ff769481001cfe7694810004fd769481001cfc769481004e7e65948100067d65948101a6be6494810006bd649481019ede6394810006dd6394810046ee6294810006ed6294810025f67194810005f5719481001dfa7094810005f97094810004ff765481001cfe7654810004fd765481001cfc765481004e7e65548100067d6554810196be6454810006bd645481018ede6354810006dd6354810046ee6254810006ed6254810044ff761481001cfe7614810004fd761481001cfc761481004e7e65148100067d6514810186be6414810006bd641481017ede6314810006dd6314810046ee6214810006ed6214810004fd76d441004e7e65d44100067d65d4410176be64d4410006bd64d441016ede63d4410006dd63d4410006ee62d4410006ed62d4410004ff765441004e7e65544100067d655441015ebe6454410006bd6454410156de6354410006dd6354410006ee6254410006ed62544101cef66154410004fd76c84100067e65c84100067d65c8410136be64c8410006bd64c841012ede63c8410006dd63c8410046ee62c8410006ed62c8410004ff76484100067e65484100067d6548410005bf7448410035bc744841011ebe6448410006bd6448410116de6348410006dd6348410046ee6248410006ed6248410027e4214841001dfb7644010006fb7644010004fb76440100077b754401000778754401001f7a654401001f79654401001efb644401001fba64440101c6f9644401001fb96444010006b9644401001efb634401001fda63440101bef9634401001fd96344010006d963440101bf7b53440101bf7953440101bfbb43440101bfb9434401001fea624401001fe9624401001dfb714401001ff37144010026fa614401001ff26144010027f231440101bff13144010027f22144010007f12144010
  | 1 => 0x901001eba105901001ebd105901001ebc1059010006df7558c10006de7558c100065e7558c10006dd7558c100065d7558c10006dc7558c10006df7458c10006de7458c100069e7458c10006dd7458c100069d7458c10006dc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df4258c10006de4258c10006dd4258c10006dc4258c1002edf7158c10026de7158c1002edd7158c10026dc7158c10026de5158c10026dc5158c10006df4158c10026de4158c10006dd4158c10026dc4158c10026de2158c10026dc2158c1001edf7058c1001ede7058c1001edd7058c1001edc7058c1001edf5058c1001ede5058c1001edd5058c1001edc5058c1001edf4058c1001ede4058c1001edd4058c1001edc4058c1001edf2058c1001ede2058c1001edd2058c1001edc2058c1001edf1058c1001ed71058c1001ede1058c1001eda1058c1001edd1058c1001ed51058c1001edc1058c10046ef7598810046ee7598810046ed7598810046ec7598810046ef7498810046ee7498810046ed7498810046ec7498810006ef5498810006ee5498810006ed5498810006ec5498810046ef7398810046ee7398810046ed7398810046ec7398810006ef53988100066f5398810006ee5398810006ed53988100066d5398810006ec5398810006ef4398810006af4398810006ee4398810006ed4398810006ad4398810006ec4398810026ee7198810026ec7198810026ee5198810026ec5198810006ef4198810026ee4198810006ed4198810026ec4198810006ef3198810026ee3198810006ed3198810026ec319881001eef709881001eee709881001eed709881001eec709881001eef509881001eee509881001eed509881001eec509881001eef409881001eee409881001eed409881001eec409881001eef309881001eee309881001eed309881001eec309881001eef109881001eee109881001eed109881001eec1098810004ff755881004cfc7558810004ff7458810014fe7458810004fd7458810014fc7458810004ff735881000cfe7358810004fd735881000cfc73588100067f53588100067d5358810006bf4358810006bd435881001cff725881001eef7258810006ef4258810006ee4258810006ed4258810006ec4258810006ef3258810006ee3258810006ed3258810006ec3258810044ff7158810024fe7158810044fd7158810024fc7158810026ee2158810026ec215881001cff705881001cfe705881001cfd705881001cfc705881001eee205881001eec2058810006ef7558810006ee7558810006ed7558810006ec7558810006ef7458810006ee7458810006ed7458810006ec7458810006ef5458810006ee5458810006ed5458810006ec5458810006e
  | 2 => 0x1e7e709941001e7d709941001e7c709941001e7f409941001e7e409941001e7d409941001e7c409941001e7f309941001e7e309941001e7d309941001e7c309941001e7f209941001e7e209941001e7d209941001e7c209941001e7f109941001e7e109941001e7d109941001e7c109941001cff755941001e7f7559410004ff7459410014fe7459410004fd7459410014fc74594100067f54594100067e54594100067d54594100067c5459410004ff735941000cfe7359410004fd735941000cfc73594100067f53594100067e53594100067d53594100067c5359410006bf4359410006bd4359410004ff7259410044fc725941004cff7159410024fe715941004cfd7159410024fc71594100267e51594100267c515941001cff705941001cfe705941001cfd705941001cfc705941001e7e505941001e7c505941001ef7105941001ef510594100067f74594100067e74594100067d74594100067c74594100067f73594100047f73594100067e73594100067d73594100047d73594100067c73594100067f43594100063f43594100067e43594100067d43594100063d43594100067c43594100067f72594100067e72594100067d72594100067c72594100067f42594100067e42594100067d42594100067c42594100067f32594100067e32594100067d32594100067c32594100267e71594100267c71594100067f41594100267e41594100067d41594100267c41594100067f31594100267e31594100067d31594100267c31594100267e21594100267c215941001e7f705941001e7e705941001e7d705941001e7c705941001e7f405941001e7e405941001e7d405941001e7c405941001e7f305941001e7e305941001e7d305941001e7c305941001e7f205941001e7e205941001e7d205941001e7c205941001e7f105941001e77105941001e7e105941001e7d105941001e75105941001e7c1059410006bf7559010006be7559010006bd7559010006bc7559010006bf7359010004bf7359010006be7359010006bd7359010004bd7359010006bc7359010006bf53590100063f5359010006be5359010006bd53590100063d5359010006bc5359010006bf7259010006be7259010006bd7259010006bc7259010006bf3259010006be3259010006bd3259010006bc3259010036bf7159010026be7159010036bd7159010026bc7159010026be5159010026bc5159010006bf3159010026be3159010006bd3159010026bc3159010026be2159010026bc215901001ebf705901001ebe705901001ebd705901001ebc705901001ebf505901001ebe505901001ebd505901001ebc505901001ebf305901001ebe305901001ebd305901001ebc305901001ebf205901001ebe205901001ebd205901001ebc205901001ebf105901001ebe105
  | 3 => 0x5729451001df6709451001df47094510026f7609451021f76509451021f745094510217f24094510217f1409451020ff2309451020ff1309451001cfc76545100067f655451004e7c6554510005fb705451001df8705451001df4765451004ef4765451001cf4765451000777755451000777655451004ef6655451004ef465545100077465545101ff7754545101ff755454510205f77354510205f573545101f77753545101f77553545101f7b743545101f7b54354510007765254510007745254510007f3705451001df6705451001df47054510007f070545101fff240545101fff140545101f7f230545101f7f13054510004fe76145100067f651451004e7c65145101edf6711451000775511451001cfe76c851001cfc76c85100067f65c85100067c65c8510006ef62c8510046ec62c851001dfa70c8510005f970c8510004fe76885100057e75885100057d75885100067f65885100067c658851001cfc76485100067f65485100067c6548510005bf744851005dbc7448510006ef6248510046ec6248510005fb704851001df87048510004fe76085100067f65085100067c6508510004fe76d4110024fc76d41100067f65d411004e7c65d4110005f671d4110005f571d41100077551d411004cff7654110004fd765411004cfc76541100067f655411004e7c6554110005f77154110005f47154110007755154110004fe76c8110024fc76c81100067f65c81100067c65c8110006ef62c8110046ec62c8110005f671c8110005f571c8110044ff7648110004fd7648110044fc76481100057f75481100057c75481100067f65481100067c6548110006ef6248110046ec6248110005f77148110005f4714811001ff010481100067f65c41100067c65c411001df671c411001ef761c411001dfa76c411001efa76c411001cfa76c41100077b65c41100077865c4110025fb74c41101e5f974c4110025fb73c41101ddf973c41101d77b53c41101d77953c41101d7bb43c41101d7b943c411001dfa71c411001efb61c411001ff361c4110027f251c4110007f151c4110027f231c41101d7f131c411004e7f749941004e7e749941004e7d749941004e7c749941004e7f739941004c7f739941004e7e739941004e7d73994100047d739941004e7c73994100067f43994100063f43994100067e43994100067d43994100063d43994100067c439941004e7f729941004e7e729941004e7d729941004e7c72994100067f42994100067e42994100067d42994100067c42994100067f32994100067e32994100067d32994100067c32994100267e71994100267c71994100067f41994100267e41994100067d41994100267c41994100067f31994100267e31994100067d31994100267c31994100267e21994100267c219941001e7f7099410
  | 4 => 0x95100067d32195100067c321951004e7f711951004e7d711951004e7571195100067f41195100067e41195100067d41195100067c41195100067f31195100067e31195100067d31195100067c311951004e7f701951004e7e701951004e7d701951004e7c70195100067f40195102267e40195100067d40195102267c40195100067f30195102267e30195100067d30195102267c30195102267e20195102267c20195102267e10195100067d10195102267c1019510044fe76d89100067f65d89100067c65d891004cfe75d8910004fd75d8910004ff74d8910014fe74d8910004fd74d8910014fc74d8910004ff73d891000cfe73d8910004fd73d891000cfc73d89100067f53d89100067d53d8910006bf43d8910006bd43d8910024fe71d8910024fc71d8910006f631d8910006f531d891001cfe70d891001cfc70d8910006fa40d8910006f940d8910006fa30d8910006f930d89100057e75989100057d75989100067f65989100067c6598910006ef62989100057f75589100057c75589100067f65589100067c6558910005bf745891005dbc7458910005df7358910055dc7358910004ff75589100067f75589100047f755891004cfc75589100067c755891004c7c7558910004ff7458910006bf7458910004bf7458910014fe7458910004fd7458910014fc7458910006bc7458910014bc7458910004ff7358910006df7358910004df735891000cfe7358910004fd735891000cfc7358910006dc735891000cdc73589100067f53589100067d5358910006bf4358910006bd4358910006ef7258910006ee3258910006ed3258910004ff7158910006f77158910006f63158910006f53158910004ff7058910006fb7058910006fa4058910006f94058910006fa3058910006f93058910004fe76189100067f65189100067c6518910046ee6218910006ed621891004cff76d4910004fe76d4910004fd76d491004cfc76d49100067f65d491004e7c65d4910005f671d4910005f571d4910044ff7694910004fe7694910004fd7694910044fc76949100067f659491004e7c6594910004ff7654910004fe7654910004fd7654910004fc76549100067f655491004e7c6554910044ff7614910004fe7614910004fd7614910044fc76149100067f651491004e7c6514910005f67114910005f5711491001dfa7014910005f9701491001cfe76d451001cfc76d45100067f65d451004e7c65d451001dfa70d4510005f970d4510004fe76945100067f659451004e7c6594510005ee7294510005ed7294510005f67694510006f67694510205f5759451000777659451004ef6659451004ef4659451000774659451004e7465945101edf773945101edf5739451020f77539451020f75539451020fb7439451020fb54394510007e67294510007e
  | 5 => 0x4fd74d9510014fc74d95100067f54d95100067e54d95100067d54d95100067c54d9510004ff73d951000cfe73d9510004fd73d951000cfc73d95100067f53d95100067e53d95100067d53d95100067c53d9510006bf43d9510006bd43d9510044fe72d9510004fd72d9510024fe71d9510024fc71d951001cfe70d951001cfc70d951004c7e76d95100067f64d95100067e64d95100067d64d95100067c64d95100057f73d95100057d73d95100067f63d95100067e63d95100067d63d95100067c63d95100073f43d95100073d43d951021f7771d95100077631d95100077531d95100077a40d95100077940d95100077a30d95100077930d951021f7610d951021f7410d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100047f73d95100067e73d95100067d73d95100047d73d95100067c73d95100067f43d95100063f43d95100067e43d95100067d43d95100063d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067e42d95100067d42d95100067c42d95100067f32d95100067e32d95100067d32d95100067c32d951021e7f71d95100067d71d95100067f41d95100067e41d95100067d41d95100067c41d95100067f31d95100067e31d95100067d31d95100067c31d95100067f70d951021e7e70d95100067d70d951021e7c70d95100067f40d951021e7e40d95100067d40d951021e7c40d95100067f30d951021e7e30d95100067d30d951021e7c30d951021e7e20d951021e7c20d951021e7e10d951021e7c10d95100067f65995100067f7559510004ff7459510014fe7459510004fd7459510014fc7459510004ff735951000cfe7359510004fd735951000cfc73595100067f53595100067d5359510006bf4359510006bd4359510004ff7259510044fc7259510004ff7159510006f77159510004ff7059510006fb7059510004fe761951004e7e65195100067d65195100057e76195100067e76195100047e76195100067f64195100067e64195100067d64195100067c64195100057f73195100057d73195100067f63195100067e63195100067d63195100067c63195100073f43195100073d43195100077571195100077631195100077531195100077a40195100077940195100077a301951000779301951022776101951022774101951004e7f741951004e7e741951004e7d741951004e7c741951004e7f731951004c7f731951004e7e731951004e7d73195100047d731951004e7c73195100067f43195100063f43195100067e43195100067d43195100063d43195100067c431951004e7f721951004e7e721951004e7d721951004e7c72195100067f42195100067e42195100067d42195100067c42195100067f32195100067e321
  | 6 => 0xf65547100267c6554710027745154710005f77654710006f7765471002777755471002777655471004ef6655471004ef4655471002774655471025f77545471025f755454710255f77354710255f573547101cf7753547101cf7553547101cfb743547101cfb5435471000776525471000774525471001df6705471001df47054710026ef62c8710026ec62c8710005bf7448710075bc7448710026ef6248710026ec624871004e7e65d43100067d65d4310025f671d4310005f571d43100077551d431004cff765431004e7e65543100067d6554310005f77154310025f47154310007755154310046ee62c8310006ed62c8310025f671c8310005f571c8310044ff76483100057f75483100057c7548310046ee6248310006ed6248310005f77148310025f4714831001e7f7559610004ff7459610014fe7459610004fd7459610014fc7459610004ff735961000cfe7359610004fd735961000cfc73596100067f53596100067d5359610006bf4359610006bd4359610004ff7259610044fc725961001cfc705961001e7e505961001e7c505961001ef7105961001ef51059610004ff7558a100067f7558a100047f7558a1004cfc7558a100067c7558a1004c7c7558a10004ff7458a10014fe7458a10004fd7458a10014fc7458a10004ff7358a1000cfe7358a10004fd7358a1000cfc7358a100067f5358a100067d5358a10006bf4358a10006bd4358a1001eef7258a10006ef4258a10006ec4258a10006ee3258a10006ed3258a1001cfc7058a1001efa4058a10006f94058a1001efa3058a10006f93058a1001eee2058a1001eec2058a1004cff76d4a1001cfe76d4a10004fd76d4a1001cfc76d4a10044ff7694a1001cfe7694a10004fd7694a1001cfc7694a1024e7f6594a1004e7c6594a10046ee6294a10006ed6294a10005f67194a10005f57194a10004ff7654a1001cfe7654a10004fd7654a1001cfc7654a10046ee6254a10006ed6254a10044ff7614a1001cfe7614a10004fd7614a1001cfc7614a102467f6514a1004e7c6514a1001dfa7014a10005f97014a1004e7e65d46100067d65d461001dfa70d4610005f970d461021e7f659461004e7c6594610005ee7294610005ed729461004cff765461004e7e65546100067d6554610005fb705461001df870546102267f651461004e7c6514610046ee62c8610006ed62c861001dfa70c8610005f970c86100057e75886100057d7588610044ff7648610005bf744861006dbc7448610046ee6248610006ed6248610005fb704861001df87048610007e5210861001df976c4210026f976c4210025fb74c421023df974c4210025fb73c4210235f973c421022f7b53c421022f7953c421022fbb43c421022fb943c421001ff271c421004cfe76d9510004ff74d9510014fe74d9510
  | 7 => 0x4420005ed7294420026f66194420006f56194420004ff7654420004fd765442001cfc765442004e7e65544200067d6554420006f66154420006f56154420024ff761442001cfe7614420004fd7614420024ff74d9710014fe74d9710004fd74d9710024fc74d9710024ff73d971000cfe73d9710004fd73d9710024fc73d97100067f53d97100067d53d9710006bf43d9710006bd43d9710044fe72d9710026ee72d9710044ee72d9710004fd72d9710026ed72d9710004ed72d9710026f671d9710026f970d971021e7e50d971021e7c50d9710004fd76997100267f65997100267c659971004cff76597100267c65597100267f7559710004ff7459710014fe7459710004fd7459710014fc74597100067f54597100067d5459710004ff735971000cfe7359710004fd735971000cfc73597100067f53597100067d5359710006bf4359710006bd4359710004ff7259710044fc725971001cfc71597100267e51597100267c515971004cfe75d8b100267e75d8b1004c7e75d8b10004fd75d8b100267d75d8b100047d75d8b10024ff74d8b10014fe74d8b10004fd74d8b10024fc74d8b10024ff73d8b1000cfe73d8b10004fd73d8b10024fc73d8b100067f53d8b100067d53d8b10006bf43d8b10006bd43d8b10026f671d8b10026f631d8b10006f531d8b10026f970d8b10004fd7698b10026ef6298b10026ec6298b10044ff7658b10005bf7458b10075bc7458b10026ec6258b10004ff7558b1004cfc7558b10004ff7458b10006bf7458b10004bf7458b10014fe7458b10004fd7458b10014fc7458b10006bc7458b10014bc7458b10004ff7358b1000cfe7358b10004fd7358b1000cfc7358b100067f5358b100067d5358b10006bf4358b10006bd4358b10026ef7258b10006ee4258b10006ed4258b10006ee3258b10006ed3258b1001cfc7158b10006f63158b10006f53158b10026ee2158b10026ec2158b1004cff76d4b10024fe76d4b10004fd76d4b10024fc76d4b10046ee62d4b10006ed62d4b10025f671d4b10005f571d4b10044ff7694b10024fe7694b10004fd7694b10024fc7694b1004e7e6594b100067d6594b1001dfa7094b10005f97094b10004ff7654b10024fe7654b10004fd7654b10024fc7654b10044ff7614b10024fe7614b10004fd7614b10024fc7614b1004e7e6514b100067d6514b10046ee6214b10006ed6214b10025f67114b10005f57114b100267f65d47100267c65d471001df57694710026f5769471001cf5769471004ef66594710027766594710027756594710026f46594710025f7739471026df57394710267775394710267755394710267b74394710267b54394710027e67294710027e5729471001df67094710027f27094710027f1709471001df4709471021f76509471021f7450947100267
  | 8 => 0x1dec70c8520046ef60c8520047eb60c852029fea40c852029fe940c8520297ea30c8520297e930c852001cfe76885200057e75885200057d75885200067f65885200067c6588520285ed7288520006f76188520026f4618852001dfa7088520005f9708852001cfc76485200067f65485200067c6548520005bf7448520095bc7448520006f76148520006f46148520005fb704852001df8704852001cec7648520005ef7548520005ed75485200076f654852028eee654852028eec65485200076c65485200066c6548520007af7448520095ee7448520095ec744852027fac7448520095ac744852027eef644852027eed6448520285ef7348520285ed7348520276ef6348520276ed63485202776f53485202776d5348520277af4348520277ad4348520045ef7148520047e77148520007e76148520026ec6148520007e46148520006e4614852027fe6414852027fe54148520277e63148520277e53148520007eb704852001dee704852001dec7048520007e87048520046ef6048520047eb604852027fea404852027fe94048520277ea3048520277e93048520044fe76d4120044fc76d41200067f65d412004e7c65d4120045ee72d4120005ed72d412004cff7654120004fd7654120044fc76541200067f655412004e7c6554120005ef7254120045ec725412001f78505412001cff755942001e7f7559420004ff7459420014fe7459420004fd7459420014fc74594200067f54594200067d5459420004ff735942000cfe7359420004fd735942000cfc73594200067f53594200067d5359420006bf4359420006bd4359420044ff7259420044fe7259420044fd7259420044fc72594200467e52594200467c5259420004ff7159420024fc715942001cfe705942001cfc705942001e7e505942001e7c505942001eef205942001eed205942004cfe7598420004fd7598420024ff7498420014fe7498420004fd7498420024fc7498420024ff739842000cfe7398420004fd7398420024fc73984200067f53984200067d5398420006bf4398420006bd439842001cfe719842001ef67198420026f64198420006f54198420026f63198420006f53198420046f72198420026f4219842001ef6109842001ef41098420004ff755842004cfc7558420004ff7458420014fe7458420004fd7458420014fc7458420004ff735842000cfe7358420004fd735842000cfc73584200067f53584200067d5358420006bf4358420006bd435842001ef77158420006f64158420006f54158420006f63158420006f53158420046f72158420046f4215842001eef205842001eed205842001ef6105842001ef4105842004cff76d442001cfe76d4420004fd76d442004e7e65d44200067d65d4420024ff769442001cfe7694420004fd7694420045ee729
  | 9 => 0xe7694920046ee76949202c5ed75949200076f659492004eee659492004eec65949200076c659492004e6c6594920095ee7494920045ec7494920045ef73949202dded73949202cf6f53949202cf6d53949202cfaf43949202cfad4394920005ed719492001dee709492001dec7094920046ef6094920047eb609492024f6e509492024f6c50949202d7ea40949202d7e940949202cfea30949202cfe9309492001cfc76549200067f655492004e7c6554920005fb705492001df8705492001dec765492004eec765492001cec7654920045ef75549200476f75549200076f655492004eee655492004eec65549200076c6554920095ee7454920095ec74549202bf6f54549202bf6d54549202c5ef73549202c5ed73549202b76f53549202b76d53549202b7af43549202b7ad4354920005ef7154920007eb705492001dee705492001dec7054920007e87054920046ef6054920047eb60549202bfea40549202bfe940549202b7ea30549202b7e930549200067f65d85200067c65d852004cfe75d8520004fd75d8520004ff74d8520014fe74d8520004fd74d8520014fc74d8520004ff73d852000cfe73d8520004fd73d852000cfc73d85200067f53d85200067d53d8520006bf43d8520006bd43d8520006ee32d8520006ed32d8520006fa40d8520006f940d8520006fa30d8520006f930d85200057e75985200057d75985200067f65985200067c6598520006f761985200057f75585200057c75585200067f65585200067c6558520005bf7458520095bc7458520005df735852008ddc73585200067f65185200067c6518520006f5611852004cfe7518520004fd7518520024ff7418520014fe7418520004fd7418520024fc7418520024ff731852000cfe7318520004fd7318520024fc73185200067f53185200067d5318520006bf4318520006bd431852001cfe701852001cfc7018520004fe76d4520004fd76d452004cfc76d45200067f65d452004e7c65d4520045ee72d4520005ed72d45200076e52d4520004fe7694520004fd7694520024fc76945200067f659452004e7c6594520045ee7294520005ed7294520004ff7654520004fe7654520004fc76545200067f655452004e7c65545200076e5254520005fb705452001df87054520004fe7614520004fd7614520024fc76145200067f651452004e7c6514520045ee7214520005ed721452001dfa7014520005f97014520005ee76c8520046ee76c8520045ef75c8520005ed75c85200076f65c85202aeee65c85202aeec65c85200076c65c85200066c65c8520095ee74c8520045ec74c852029eef64c852029eed64c8520045ef73c85202a5ed73c8520296ef63c8520296ed63c85202976f53c85202976d53c8520297af43c8520297ad43c8520026ec61c852001dee70c8520
  | 10 => 0x95200067d73d95200047d73d95200067c73d95200067f43d95200063f43d95200067e43d95200067d43d95200063d43d95200067c43d952024e7f72d95202ee7e72d95200067d72d95202ee7c72d95200067f42d95202ee7e42d95200067d42d95202ee7c42d95200067f32d95202ee7e32d95200067d32d95202ee7c32d95200067f71d95200067e71d95200067d71d95200067c71d95200067f41d95200067e41d95200067d41d95200067c41d95200067f31d95200067e31d95200067d31d95200067c31d95202ee7f21d95202ee7c21d95202ee7f70d952024e7e70d95200067d70d952024e7c70d95200067f40d952024e7e40d95200067d40d952024e7c40d95200067f30d952024e7e30d95200067d30d952024e7c30d95202ee7f20d952024e7e20d952024e7c20d952024e7e10d952024e7c10d95200067f65995200067f7559520004ff7459520014fe7459520004fd7459520014fc7459520004ff735952000cfe7359520004fd735952000cfc73595200067f53595200067d5359520006bf4359520006bd4359520004ff7259520006ef7259520004ff7159520024fc7159520004ff7059520006fb7059520004fe761952004e7e65195200067d65195200057e76195200067e76195200047e76195200067f64195200067e64195200067d64195200067c64195200057f73195200057d73195200067f63195200067e63195200067d63195200067c63195200073f43195200073d43195200076d72195200076f42195200076c42195200076e32195200076d32195200077a40195200077940195200077a30195200077930195202e77b20195202476e20195202476c20195202e778201952004e7f741952004e7e741952004e7d741952004e7c741952004e7f731952004c7f731952004e7e731952004e7d73195200047d731952004e7c73195200067f43195200063f43195200067e43195200067d43195200063d43195200067c431952004e7f721952004e7e721952004e7d721952004e6d721952004e7c72195200067f42195202e67e42195200067d42195202e67c42195200067f32195202e67e32195200067d32195202e67c321952004e7f711952004e7e711952004e7d711952004e7c71195200067f41195200067e41195200067d41195200067c41195200067f31195200067e31195200067d31195200067c31195202e67f21195202e67c211952004e7f701952004e7e701952004e7d701952004e7c70195200067f40195202467e40195200067d40195202467c40195200067f30195202467e30195200067d30195202467c30195202e67f20195202467e20195200067d20195202467c20195202467e10195202467c101952001cfe76d492001cfc76d49200067f65d492004e7c65d492001dfa70d4920005f970d4920005e
  | 11 => 0x1ebc205922001ebf105922001ebe105922001ebd105922001ebc105922004e7e65d4a200067d65d4a201b6be64d4a20006bd64d4a2001dfa70d4a20005f970d4a2004cff7654a2004e7e6554a200067d6554a20196be6454a20006bd6454a20005fb7054a2001df87054a2004cfe7598620004fd7598620024ff7498620014fe7498620004fd7498620024fc7498620024ff739862000cfe7398620004fd7398620024fc73986200067f53986200067d5398620006bf4398620006bd439862001ef67198620026f63198620006f5319862001cfe709862001ef6109862001ef41098620004ff755862004cfc7558620004ff7458620014fe7458620004fd7458620014fc7458620004ff735862000cfe7358620004fd735862000cfc73586200067f53586200067d5358620006bf4358620006bd435862001ef77158620006f63158620006f5315862001cfc705862001efa4058620006f9405862001efa3058620006f9305862001eef205862001eed205862001ef6105862001ef4105862004cff76d462001cfe76d4620004fd76d462004e7e65d46200067d65d4620176be64d4620006bd64d4620024ff769462001cfe7694620004fd7694620166be6494620006bd6494620045ee7294620005ed7294620026f66194620006f56194620004ff7654620004fd765462001cfc765462004e7e65546200067d655462015ebe6454620006bd6454620006f66154620006f56154620005fb705462001df87054620024ff761462001cfe7614620004fd7614620146be6414620006bd641462001dfa7014620005f970146200057e75886200057d7588620126be6488620006bd6488620026f66188620006f5618862001dfa7088620005f97088620005bf74486200a5bc744862011ebe6448620006bd6448620006f66148620006f56148620047e42148620005fb704862001df8704862004cfe76d9520004ff74d9520014fe74d9520004fd74d9520014fc74d95200067f54d95200067e54d95200067d54d95200067c54d9520004ff73d952000cfe73d9520004fd73d952000cfc73d95200067f53d95200067e53d95200067d53d95200067c53d9520006bf43d9520006bd43d9520044fe72d9520044fc72d9520024fe71d9520004fd71d952004c7e76d95200067f64d95200067e64d95200067d64d95200067c64d95200057f73d95200057d73d95200067f63d95200067e63d95200067d63d95200067c63d95200073f43d95200073d43d952024f6f72d95200076f42d95200076c42d95200076e32d95200076d32d95200077a40d95200077940d95200077a30d95200077930d95202ef7b20d952024f6e20d952024f6c20d95202ef7820d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200047f73d95200067e73d
  | 12 => 0x63198720006f53198720026ef2198720046f72198720026f42198720004ff755872004cfc7558720004ff7458720014fe7458720004fd7458720014fc7458720004ff735872000cfe7358720004fd735872000cfc73587200067f53587200067d5358720006bf4358720006bd435872001cfc7258720046ee3258720006ed3258720046f77158720006f64158720006f54158720006f63158720006f53158720046f72158720046f4215872004cff76d4720044fe76d4720004fd76d472031e7f65d472004e7c65d4720045ee72d4720005ed72d472031f6e52d4720006f661d4720006f561d4720024ff7694720044fe7694720004fd769472004e7e65947200067d6594720045ee7294720005ed7294720004ff7654720004fd7654720044fc76547203167f655472004e7c6554720045ee72547203176e5254720024ff7614720044fe7614720004fd761472004e7e65147200067d6514720045ee7214720005ed7214720026f66114720006f56114720045ef7648720006ef7648720005ef7548720005ed754872028eee6548720046ec6548720007af74487200b5ee74487200b5ec7448720307ac74487200b5ac7448720046ef6448720306ed644872030def734872030ded7348720046ef63487202feed63487202ff6f53487202ff6d53487202ffaf43487202ffad4348720047e77148720026ee6148720307e64148720307e541487202ffe631487202ffe5314872001dee704872001dec704872004e7e65d43200067d65d4320045ee72d4320005ed72d432004cff765432004e7e65543200067d6554320005ef7254320045ec725432001e7f7559620004ff7459620014fe7459620004fd7459620014fc7459620004ff735962000cfe7359620004fd735962000cfc73596200067f53596200067d5359620006bf4359620006bd4359620004ff7159620024fc715962001cfc705962001e7e505962001e7c505962001eef205962001eed2059620006bf7559220006be7559220006bd7559220006bc7559220006bf7359220004bf7359220006be7359220006bd7359220004bd7359220006bc7359220006bf53592200063f5359220006be5359220006bd53592200063d5359220006bc53592200a6bf72592202f6be7259220006bd72592202f6bc72592202f6be52592202f6bc5259220006bf32592202f6be3259220006bd32592202f6bc3259220006bf7159220006be7159220006bd7159220006bc7159220006bf3159220006be3159220006bd3159220006bc31592202f6bf21592202f6bc215922001ebf705922001ebe705922001ebd705922001ebc705922001ebf505922001ebe505922001ebd505922001ebc505922001ebf305922001ebe305922001ebd305922001ebc305922001ebf205922001ebe205922001ebd2059220
  | 13 => 0x845001ef6705845001ef4705845001ef7505845001e77505845001ef6505845001ef5505845001e75505845001ef4505845001ef7405845001ef6405845001ef5405845001ef4405845001ef7305845001ef6305845001ef5305845001ef4305845001ef7205845001ef6205845001ef5205845001ef4205845004d7d76944500067d76944500047d769445034d7f749445034d7d749445004f3e649445004f3d64944503457f73944503457d739445004e7f639445004f5e639445033e7d639445004f5d63944500065d639445033f3f439445033f3d43944502e57e72944500076e72944500056e72944500076d729445004f6e629445004f6d629445004d7e719445004f76719445004f7661944500067d619445004f75619445000675619445021d7d709445021e7e609445004f7a6094450044ff76c845001cfe76c8450004fd76c845004d7e75c84500057d75c8450136be64c8450006bd64c845012ede63c8450006dd63c8450046ee62c8450006ed62c84502e76c52c8450006f661c8450006f561c845001dfa70c8450005f970c8450024ff768845001cfe7688450004fd768845004d7e75884500057d7588450126be6488450006bd648845010ede6388450006dd6388450046ee6288450006ed6288450026f66188450006f56188450004ff7648450004fd764845001cfc76484500057f754845004d7c7548450005bf74484500c5bc744845011ebe6448450006bd6448450116de6348450006dd6348450046ee6248450006ed624845028f6c5248450006f66148450006f56148450024ff760845001cfe7608450004fd76084502e57f750845004d7c7508450106be6408450006bd64084500fede6308450006dd6308450046ee6208450006ed6208450026f66108450006f561084500467f7559720004ff7459720014fe7459720004fd7459720014fc74597200067f54597200067d5459720004ff735972000cfe7359720004fd735972000cfc73597200067f53597200067d5359720006bf4359720006bd435972001cfc72597200467e52597200467c5259720004ff7159720024fc7159720045ef7654b20006ef7654b200476f7554b2004eee6554b20046ec6554b200b5ee7454b200b5ec7454b203376f5454b203376d5454b2032def7354b2032ded7354b203276f5354b203276d5354b20327af4354b20327ad4354b20005ef7154b2001dee7054b2001dec7054b2004cfe75987200267e759872004c7e7598720004fd75987200267d75987200047d7598720024ff7498720014fe7498720004fd7498720024fc7498720024ff739872000cfe7398720004fd7398720024fc73987200067f53987200067d5398720006bf4398720006bd439872001cfe729872001cee7298720026f67198720026f64198720006f54198720026f
  | 14 => 0x4fd7498450024fc7498450024ff739845000cfe7398450004fd7398450024fc739845004e7f53984500067d5398450006bf4398450006bd4398450044fe7298450004fd729845001cfe719845001ef6719845004ef75198450026f45198450006f74198450026f64198450006f54198450026f44198450006f73198450026f63198450006f53198450026f4319845001ef6109845001ef4109845004ef6759845004ef57598450026f47598450026f77498450006f67498450006f57498450026f4749845004ef7549845004ef6549845004ef5549845004ef45498450026f77398450006f67398450006f57398450026f4739845004ef7539845004e77539845004ef6539845004ef5539845000675539845004ef45398450006f74398450006b74398450006f64398450006f54398450006b54398450006f44398450026f77298450006f67298450006f57298450026f4729845004ef7529845004ef6529845004ef5529845004ef45298450006f74298450006f64298450006f54298450006f44298450006f73298450006f63298450006f53298450006f4329845001ef6709845001ef5709845001ef4709845001ef7509845001ef6509845001ef5509845001ef4509845001ef7409845001ef6409845001ef5409845001ef4409845001ef7309845001ef6309845001ef5309845001ef4309845001ef7209845001ef6209845001ef5209845001ef42098450004ff7458450014fe7458450004fd7458450014fc745845004e7f54584500067d5458450004ff735845000cfe7358450004fd735845000cfc735845004e7f53584500067d5358450006bf4358450006bd4358450004ff7258450044fc72584500067e525845004e7c525845001ef7715845004ef7515845004e7c515845004ef4515845004e745158450006f74158450006f64158450006f54158450006f44158450006f73158450006f63158450006f53158450006f4315845001e7f505845001e7d505845001ef6105845001ef4105845004ef7755845004ef6755845004ef47558450006f77458450006f67458450006f57458450006f4745845004ef7545845004e77545845004ef6545845004ef5545845000675545845004ef45458450006f77358450006f67358450006f57358450006f4735845004ef7535845004e77535845004ef6535845004ef5535845000675535845004ef45358450006f74358450006b74358450006f64358450006f54358450006b54358450006f44358450006f77258450006f67258450006f57258450006f4725845004ef7525845004ef6525845000676525845004ef5525845004ef4525845004e745258450006f74258450006f64258450006f54258450006f44258450006f73258450006f63258450006f53258450006f4325845001ef7705
  | 15 => 0xd53988500066d539885004eec5398850006ef4398850006af4398850006ee4398850006ed4398850006ad4398850006ec4398850046ef7198850046ee7198850046ed7198850046ec719885004eef519885004eee519885004eed519885004eec5198850006ef4198850006ee4198850006ed4198850006ec4198850006ef3198850006ee3198850006ed3198850006ec319885001eef709885001eee709885001eed709885001eec709885001eef509885001eee509885001eed509885001eec509885001eef409885001eee409885001eed409885001eec409885001eef309885001eee309885001eed309885001eec309885001eef109885001eee109885001eed109885001eec1098850004ff7458850014fe7458850004fd7458850014fc745885004e7f54588500067d5458850004ff735885000cfe7358850004fd735885000cfc735885004e7f53588500067d5358850006bf4358850006bd435885001eef725885004eef525885004e7c525885004eec5258850006ef4258850006ee4258850006ed4258850006ec4258850006ef3258850006ee3258850006ed3258850006ec3258850004ff7158850024fc715885001eee205885001eec205885004eef755885004eee755885004eec7558850006ef7458850006ee7458850006ed7458850006ec745885004eef545885004e6f545885004eee545885004eed54588500066d545885004eec5458850006ef7358850006ee7358850006ed7358850006ec735885004eef535885004e6f535885004eee535885004eed53588500066d535885004eec5358850006ef4358850006af4358850006ee4358850006ed4358850006ad4358850006ec4358850006ef7158850006ee7158850006ed7158850006ec715885004eef515885004eee515885004eed515885004eec5158850006ef4158850006ee4158850006ed4158850006ec4158850006ef3158850006ee3158850006ed3158850006ec315885001eef705885001eee705885001eec705885001eef505885001eee505885001eed505885001eec505885001eef405885001eee405885001eed405885001eec405885001eef305885001eee305885001eed305885001eec305885001eef105885001eee105885001eed105885001eec105885004d7d76948502e67d76948502e57f74948503657d749485004f3e649485004f3d64948502e57f739485035d7d739485004e7f639485004f5e63948503567d639485004f5d63948500065d63948503573f43948503573d439485004d7e729485004f6e729485004e7f629485004f6e62948502e67d629485004f6d62948500066d62948500057e719485004f76619485004f75619485024d7f709485024d7d709485024e7e609485004f7a609485024f6f2094850024ff7498450014fe7498450
  | 16 => 0x8550006ef62c8550046ec62c8550004fe7688550004fd7688550024fc768855004d7e75885500057d7588550006f76188550026f46188550004ff7648550004fe7648550004fc7648550005bf74485500d5bc7448550006ef6248550046ec6248550006f76148550006f46148550004fe7608550004fd7608550024fc760855004d7e75085500057d750855001dfa7008550005f9700855004ebf755905004ebe755905004ebd755905004ebc7559050006bf7359050004bf7359050006be7359050006bd7359050004bd7359050006bc735905004ebf535905004e3f535905004ebe535905004ebd53590500063d535905004ebc5359050006bf7259050006be7259050006bd7259050006bc725905004ebf525905004ebe525905004ebd525905004ebc5259050006bf3259050006be3259050006bd3259050006bc3259050006bf7159050006be7159050006bd7159050006bc715905004ebf515905004ebe515905004ebd515905004ebc5159050006bf3159050006be3159050006bd3159050006bc315905001ebf705905001ebe705905001ebd705905001ebc705905001ebf505905001ebe505905001ebd505905001ebc505905001ebf305905001ebe305905001ebd305905001ebc305905001ebf205905001ebe205905001ebd205905001ebc205905001ebf105905001ebe105905001ebd105905001ebc105905004edf7558c5004ede7558c5004e5e7558c5004edd7558c500be5d7558c5004edc7558c50006df7458c50006de7458c500069e7458c50006dd7458c500069d7458c50006dc7458c5004edf5458c5004e5f5458c5004ede5458c5004edd5458c500065d5458c5004edc5458c50006df7258c50006de7258c50006dd7258c50006dc7258c5004edf5258c5004ede5258c5004edd5258c5004edc5258c5004e5c5258c50006df4258c50006de4258c50006dd4258c50006dc4258c50006df7158c50006de7158c50006dd7158c50006dc7158c5004edf5158c5004ede5158c5004edd5158c5004edc5158c5004e5c5158c50006df4158c50006de4158c50006dd4158c50006dc4158c5001edf7058c5001ede7058c5001edd7058c5001edc7058c5001edf5058c5001e5f5058c5001ede5058c5001edd5058c5001e5d5058c5001edc5058c5001edf4058c5001ede4058c5001edd4058c5001edc4058c5001edf2058c5001ede2058c5001edd2058c5001edc2058c5001edf1058c5001ede1058c5001edd1058c5001edc1058c50046ef7598850046ee7598850046ed7598850046ec7598850046ef7498850046ee7498850046ed7498850046ec749885004eef549885004eee549885004eed549885004eec5498850046ef7398850046ee7398850046ed7398850046ec739885004eef539885004e6f539885004eee539885004ee
  | 17 => 0x6f66154650006f56154650005fb705465001df870546502257d761465004e7d761465004d7f74146503ad7d741465004d7f73146503a57d73146502267f631465039e7d631465039f3f431465039f3d43146502ed7e721465004f7671146500067d611465004d7f70146502257d701465004f7a6014650044ff76c865001cfe76c8650004fd76c865004d7e75c86500057d75c8650046ee62c8650006ed62c86502ef6c52c8650024ff768865001cfe7688650004fd768865004d7e75886500057d7588650004ff7648650004fd764865001cfc76486500057f754865004d7c7548650005bf74486500e5bc7448650046ee6248650006ed62486500076c5248650024ff760865001cfe7608650004fd76086502ed7f750865004d7c750865001dfa7008650005f97008650004ff74d8950014fe74d8950004fd74d8950014fc74d8950004ff73d895000cfe73d8950004fd73d895000cfc73d89500067f53d89500067d53d8950006bf43d8950006bd43d8950024fe71d8950004fd71d895024e7f6598950006ef6298950005f67198950005f571989502467f6518950046ee6218950006ed621895001cfe7694950006ef6294950046ec629495001dfa7094950005f9709495001cfc7654950006ef6254950046ec6254950005fb705495001df8705495004f785054950004ff74d8550014fe74d8550004fd74d8550014fc74d8550004ff73d855000cfe73d8550004fd73d855000cfc73d85500067f53d85500067d53d8550006bf43d8550006bd43d8550044fe72d8550004fd72d8550005ee7298550005ed7298550006f76198550006f56118550024ff7418550014fe7418550004fd7418550024fc7418550024ff731855000cfe7318550004fd7318550024fc73185500067f53185500067d5318550006bf4318550006bd4318550044fe7218550004fd72185502267e50185502267c50185500057e76d455004e7e76d45500047e76d45503967f64d45503967d64d455004d7f73d455038d7d73d45503867f63d45503867d63d45503873f43d45503873d43d455031e7c62d45500267c61d455001d7e70d455001d7c70d455004e7f60d455004f7b60d455001cfe76945503757d7594550005ee7294550005ed7294550006f76194550026f4619455001dfa7094550005f9709455001cfc7654550006f76154550006f4615455004f745154550005fb705455001df8705455001c7c765455037e7f645455037e7d64545503757f73545503757d735455036e7f635455036e7d635455036f3f435455036f3d43545503167c625455004d7f715455004f7771545500077761545500267c61545500077461545500077b705455001d7e705455001d7c705455000778705455004e7f605455004f7b6054550004fe76c8550004fd76c8550044fc76c
  | 18 => 0xf43547503ff3d43547503167e625475004f77715475004f7761547500267e615475004f74615475001d7e705475001d7c7054750044ff76c875004cfe76c8750004fd76c8750046ec62c875001dfa70c8750005f970c8750024ff768875004cfe7688750004fd768875004d7e75887500057d7588750004ff7648750004fd764875004cfc7648750005bf74487500f5bc7448750024ff760875004cfe7608750004fd760875004d7e75087500057d7508750004ff7458a50014fe7458a50004fd7458a50014fc7458a500067f5458a500067d5458a50004ff7358a5000cfe7358a50004fd7358a5000cfc7358a500067f5358a500067d5358a50006bf4358a50006bd4358a5001eef7258a50006ef4258a50006ec4258a50006ee3258a50006ed3258a50004ff7158a50024fc7158a5001cfc7058a5001eee2058a5001eec2058a50046ee6294a50006ed6294a5001dfa7094a50005f97094a502ed7f7494a503f57d7494a502ed7f7394a503ed7d7394a5024e7f6394a503e67d6394a503e73f4394a503e73d4394a5004d7e7294a5024e7f6294a5024f6e6294a502ee7d6294a5024f6d6294a500057e7194a5024f7a7094a5024d7d7094a502ef797094a5004e7e6094a5024f6f2094a50044ff7654a50046ee6254a50006ed6254a50005fb7054a5001df87054a502457d7614a5004e7d7614a5004d7f7414a503dd7d7414a5004d7f7314a503d57d7314a502467f6314a503ce7d6314a503cf3f4314a503cf3d4314a5004f6e7214a502467f6214a502ee7d6214a500057e7114a5004d7f7014a502457d7014a5004f7a6014a50024ff7498650014fe7498650004fd7498650024fc7498650024ff739865000cfe7398650004fd7398650024fc73986500067f53986500067d5398650006bf4398650006bd4398650044fe7298650004fd729865001ef67198650026f63198650006f5319865001cfe709865001ef6109865001ef41098650004ff7458650014fe7458650004fd7458650014fc74586500067f54586500067d5458650004ff735865000cfe7358650004fd735865000cfc73586500067f53586500067d5358650006bf4358650006bd4358650004ff7258650044fc72586500067e52586500067c525865001ef77158650006f63158650006f5315865001cfc705865001e7f505865001e7d505865001ef6105865001ef41058650005ee7294650005ed7294650026f66194650006f5619465001dfa7094650005f970946503c57f74946503c57d74946503bd7f73946503bd7d739465021e7f63946503b67d63946503b73f43946503b73d43946502ed7e72946500076e72946500056e72946500076d729465004d7e719465021f7661946500067d619465021f75619465021f7a709465021d7d709465000779709465004e7e6094650
  | 19 => 0x8121006bc6498121006fb60981210057f75581210057c7558121005bf745812111dbc7458121006bf6458121006bc6458121005df7358121115dc7358121006bf6418121006bc641812101efa6018121006f96018121024ff75594210267f7559421004ff7459421014fe7459421004fd7459421014fc74594210067f54594210067d5459421004ff735942100cfe7359421004fd735942100cfc73594210067f53594210067d5359421006bf4359421006bd4359421044fe7259421044fc72594210467e52594210467c5259421024fe7159421024fc71594210267e51594210267c5159421004ff705942101cfc7059421004fd76d44210267f65d44210267c65d4421004ff76544210267f65544210267c6554421025ef7648421006ef7648421004ef764842128eee6548421026ec6548421007af744842141fac7448421026ef644842141eed6448421026ef6348421416ed63484214176f53484214176d5348421417af4348421417ad4348421025ef7148421047e77148421026ee6148421027e66148421027e65148421007e55148421027e6414842141fe54148421027e63148421417e53148421004ff75580210067f75580210047f755802104cfc75580210067c755802104c7c7558021004ff7458021014fe7458021004fd7458021014fc7458021004ff735802100cfe7358021004fd735802100cfc73580210067f53580210067d5358021006bf4358021006bd4358021046ef2158021006ed2158021026fb7058021006fa4058021006f94058021006fa3058021006f93058021046fb2058021046f82058021026fb1058021026f8105802101cfc7558b50004ff7458b50014fe7458b50004fd7458b50014fc7458b50004ff7358b5000cfe7358b50004fd7358b5000cfc7358b5004e7f5358b500067d5358b50006bf4358b50006bd4358b5004eef7258b5004eef5258b5004eec5258b50004ff7158b50024fc7158b5001cfe759875001c7e7598750024ff7498750014fe7498750004fd7498750024fc7498750024ff739875000cfe7398750004fd7398750024fc739875004e7f53987500067d5398750006bf4398750006bd4398750044fe7298750026ee7298750044ee7298750004fd7298750026ed7298750004ed7298750026f671987500267f519875004ef75198750026f4519875021e7e509875004e7c509875001cfc7558750004ff7458750014fe7458750004fd7458750014fc7458750004ff735875000cfe7358750004fd735875000cfc735875004e7f53587500067d5358750006bf4358750006bd4358750004ff7258750044fc725875004ef7715875004ef7515875004ef4515875004d7f76547500067f765475004e7f645475040e7d64547504057f73547504057d735475004e7f63547503fe7d63547503ff3
  | 20 => 0x11ebc71d9121006bf31d9121006be31d9121006bd31d9121006bc31d9121486bf21d912111ebd21d9121486bc21d9121006bf70d9121006be70d9121006bd70d9121006bc70d9121006bf30d9121006be30d9121006bd30d9121006bc30d9121486bf20d9121486bc20d9121004fe76d4921024fc76d49210067f65d492104e7c65d4921006bf64d49211b6bc64d4921005f671d4921005f571d492128eee76d4921004ee76d4921045ee75d492128eef65d49210076f65d492128eed65d492128f6c65d492128def74d492147ded74d4921007af64d492146fac64d492128f6f54d492146f6d54d492128def73d4921475ed73d492128f6f53d49214676d53d4921467af43d4921467ad43d4921025ee71d492128fe671d4921005e671d492128fe571d4921046ef61d4921047e761d492146fe641d492146fe541d4921467e631d4921467e531d4921005ed70d492104cfc76549210067f655492104e7c6554921006bf6454921196bc64549210476c5254921005f77154921005f47154921047e42154921005ee7614921046ee761492128dee75149210476e751492128eef651492128f6e651492128eed65149210076d6514921045ef741492145ded7414921007af641492144fac6414921045ef7314921455ed731492128f6f53149214476d5314921447af4314921447ad4314921025ee7114921046ef6114921047e7611492144fe6411492144fe54114921447e63114921447e53114921005ed7014921044fe76d4521044fc76d45210067f65d452104e7c65d4521006bf64d4521176bc64d4521045ee72d4521005ed72d452128f6c52d4521004fe7694521006bf6494521166bc6494521045ee7294521005ed729452104cff7654521004fd7654521044fc76545210067f655452104e7c6554521006bf645452115ebc6454521005ef7254521045ec72545210076c5254521004fe7614521006bf6414521146bc64145210077551145210057e75885210057d7588521006bf6488521126bc6488521045f67188521046f7618852128dee75885210276e75885210056e75885210276d7588521025ec7588521025ef748852143ded7488521007af648852142fac6488521025ef7388521435ed73885214276f53885214276d5388521427af4388521427ad4388521025ee7188521026ef6188521047e76188521027e6418852142fe54188521027e63188521427e53188521005ed7088521006bf64d8121006bc64d812104cfe75d8121004fd75d8121004ff74d8121014fe74d8121004fd74d8121014fc74d8121004ff73d812100cfe73d8121004fd73d812100cfc73d81210067f53d81210067d53d8121006bf43d8121006bd43d8121006ee32d8121006ed32d8121006f631d8121006f531d812111dbe7498121005bd7498121006bf649
  | 21 => 0xd65d4a21025f671d4a21005f571d4a2104cff7654a2104e7e6554a210067d6554a21005f77154a21025f47154a2104e7e65d46210067d65d462104e7e65546210067d6554621027745154621025ed76c8621046ed76c86212aeee65c86210276e65c86210066e65c86210276d65c8621026ec65c8621026ef64c8621496ed64c8621026ef63c862148eed63c862148f6f53c862148f6d53c862148faf43c862148fad43c8621027e661c86210067e65982210067d6598221026fb609822101ef860982210067e65582210067d6558221026f86058221004ff755822104cfc7558221004ff7458221014fe7458221004fd7458221014fc7458221004ff735822100cfe7358221004fd735822100cfc73582210067f53582210067d5358221006bf4358221006bd4358221024fc7158221006f63158221006f53158221006ef2158221006fa4058221006f94058221006fa3058221006f93058221026fb1058221026f8105822104cfe76d9521006bc64d9521004ff74d9521014fe74d9521004fd74d9521014fc74d9521004ff73d952100cfe73d9521004fd73d952100cfc73d95210067f53d95210067d53d9521006bf43d9521006bd43d9521006ed72d952101cfe70d9521004fd70d95210067f659952111dbe7499521005bd7499521006bc6499521115de7399521005dd7399521005bf745952111dbc7459521006bc64595210067f7559521004ff7459521006bf7459521004bf7459521014fe7459521004fd7459521014fc7459521006bc7459521014bc74595210067f54595210067d5459521004ff735952100cfe7359521004fd735952100cfc73595210067f53595210067d5359521006bf4359521006bd4359521004ff7259521006ef72595213167e52595213167c5259521004ff7159521006f77159521004ff705952101cfc7059521004fe761952104e7e65195210067d6519521006bc641952111dbe76d912111ebe76d9121014be76d9121006bf65d9121006be65d9121006bd65d9121006bc65d9121005bf73d9121005bd73d9121006bf63d9121006be63d9121006bd63d9121006bc63d91210073f53d91210073d53d9121007af72d912111fac72d9121007ae32d9121007ad32d9121487b771d912111fb471d9121007b631d9121007b531d9121487b721d9121487b421d9121006bf75d9121006be75d9121006bd75d9121006bc75d9121006bf73d9121004bf73d9121006be73d9121006bd73d9121004bd73d9121006bc73d9121006bf53d91210063f53d9121006be53d9121006bd53d91210063d53d9121006bc53d9121006bf72d9121486be72d912111ebd72d9121486bc72d9121486be52d9121486bc52d9121006bf32d9121486be32d9121006bd32d9121486bc32d9121486bf71d912111ebe71d912111ebd71d9121
  | 22 => 0x962100775419962102776319962100775319962131f7721996210277421996210267f60996210267c609962104e7f749962104e7e749962104e7d749962104e7c749962104e7f739962104c7f739962104e7e739962104e7d73996210047d739962104e7c73996210067f43996210063f43996210067e43996210067d43996210063d43996210067c439962104e7f729962104e7e729962104e7d729962104e7c72996210067f429962131e7e42996210067d429962131e7c42996210067f329962131e7e32996210067d329962131e7c32996210267e71996210267c71996210067f41996210267e41996210067d41996210267c41996210067f31996210267e31996210067d31996210267c319962131e7f21996210267c219962104e7f709962104e7e709962104e7d709962104e7c70996210067f40996210067e40996210067d40996210067c40996210067f30996210067e30996210067d30996210067c309962131e7f209962131e7c20996210267f10996210267c109962104cff76596210267c65596210267f7559621004ff7459621014fe7459621004fd7459621014fc74596210067f54596210067e54596210067d54596210067c5459621004ff735962100cfe7359621004fd735962100cfc73596210067f53596210067e53596210067d53596210067c5359621006bf4359621006bd4359621024fc71596210267e51596210267c5159621004ff705962101cfc70596210257f76596210067f765962104c7f76596210267f64596210067e64596210067d64596210267c64596210057f73596210057d73596210267f63596210067e63596210067d63596210267c63596210073f43596210073d43596210277641596210077541596210277631596210077531596213177721596210277421596210267f60596210267c60596210067f74596210067e74596210067d74596210067c74596210067f73596210047f73596210067e73596210067d73596210047d73596210067c73596210067f43596210063f43596210067e43596210067d43596210063d43596210067c43596210067f72596213167e72596210067d72596213167c72596210067f42596213167e42596210067d42596213167c42596210067f32596213167e32596210067d32596213167c32596210267e71596210267c71596210067f41596210267e41596210067d41596210267c41596210067f31596210267e31596210067d31596210267c31596213167f21596210267e21596210267c21596210067f70596210067e70596210067d70596210067c70596210067f40596210067e40596210067d40596210067c40596210067f30596210067e30596210067d30596210067c30596213167f20596213167c20596210267f10596210267c105962104e7e65d4a210067
  | 23 => 0x4e7f53588510067d5358851006bf4358851006bd4358851026ef725885104eef525885104eec5258851006ee4258851006ed4258851006ee3258851006ed3258851026ee2158851026ec2158851004ff705885101cfc70588510257f76544510067f76544510047f76544510267f64544514ce7d64544514c57f73544514c57d73544510267f63544514be7d63544514bf3f43544514bf3d43544513167e62544510257f715445104f7771544510267e61544510277661544512257c7054451004ff7458051014fe7458051004fd7458051014fc7458051004ff735805100cfe7358051004fd735805100cfc735805104e7f53580510067d5358051006bf4358051006bd4358051004ff7258051044fc725805104e7f515805104ef651580510067d515805104ef55158051026fb705805104efb505805104e7c505805104ef85058051006fa4058051006f94058051006fa3058051006f93058051026fb1058051026f810580510467f7559721004ff7459721014fe7459721004fd7459721014fc74597210067f54597210067d5459721004ff735972100cfe7359721004fd735972100cfc73597210067f53597210067d5359721006bf4359721006bd4359721044fc7259721046ec7259721044ec72597210467e52597210467c5259721046ec5259721004ff705972101cfc7059721046ef2059721045ed76d4b212aeed76d4b210476e75d4b21046ef65d4b212aeed65d4b212adef74d4b214b5ed74d4b212af6f54d4b214af6d54d4b212adef73d4b214a5ed73d4b212af6f53d4b2149f6d53d4b2149faf43d4b2149fad43d4b21025ee71d4b21005ed70d4b2104e7e65d47210067d65d4721045ee72d4721005ed72d472131f6c52d4721045ee7294721005ed729472104cff765472104e7e65547210067d6554721005ef7254721045ec72547213176c5254721025ec7214721004ff755832104cfc7558321004ff7458321014fe7458321004fd7458321014fc7458321004ff735832100cfe7358321004fd735832100cfc73583210067f53583210067d5358321006bf4358321006bd4358321046ee3258321006ed3258321046fb7058321006fa4058321006f94058321006fa3058321006f93058321046fb2058321046f82058321024ff74d9621014fe74d9621004fd74d9621024fc74d9621024ff73d962100cfe73d9621004fd73d9621024fc73d96210067f53d96210067d53d9621006bf43d9621006bd43d9621026ed72d9621026f671d962101cfe70d9621004fd70d9621004fd76996210267f65996210267c65996210047d76996210267f64996210067e64996210067d64996210267c64996210057f73996210057d73996210267f63996210067e63996210067d63996210267c63996210073f43996210073d439962102776419
  | 24 => 0xf73d465152d7d73d46510267f63d46515267d63d46515273f43d46515273d43d465131e7e62d46510276e62d46510066e62d46510276d62d46510277661d46510277641d465151f7541d465121d7e70d4651006ee6298251006ed6298251026fb609825101ef86098251006ee6258251006ed6258251026f86058251004ff7458251014fe7458251004fd7458251014fc7458251004ff735825100cfe7358251004fd735825100cfc73582510067f53582510067d5358251006bf4358251006bd4358251004ff7258251044fc7258251024fc71582510067f5158251006fa4058251006f94058251006fa3058251006f93058251026fb1058251026f81058251004ff74d8951014fe74d8951004fd74d8951014fc74d89510067f54d89510067d54d8951004ff73d895100cfe73d8951004fd73d895100cfc73d89510067f53d89510067d53d8951006bf43d8951006bd43d895101cfe70d8951004fd70d8951006ef6298951005fa7098951005f97098951005bf745895115dbc7458951046ee6218951006ed6218951006ef6294951046ec6294951005f67194951005f571949513157f74949515157d74949513157f739495150d7d73949515067f63949515067d63949515073f43949515073d439495104d7e72949513167f62949510076f62949513176c62949510257e719495131776719495100576719495131775719495104e7f619495104f7761949510057d709495124e7c6094951044fc7654951006ef6254951046ec625495104f6c5254951005f77154951005f4715495104f7451549510057e761495104e7e761495104d7f74149514fd7d741495104d7f73149514f57d73149514ee7f63149514ee7d63149514ef3f43149514ef3d43149513157e721495104f6e72149513167f62149513176e62149510076d62149510257e711495104e7f611495104f7761149510057d70149512467c6014951005ee7294551005ed729455104df6719455104ef761945510257f74945514e57d74945510257f73945514dd7d73945514d67f63945514d67d63945514d73f43945514d73d43945513157e72945510276e72945510056e72945510276d72945510257e71945510267f619455104f7761945510057d7094551004ff74d8151014fe74d8151004fd74d8151014fc74d8151004ff73d815100cfe73d8151004fd73d815100cfc73d81510067f53d81510067d53d8151006bf43d8151006bd43d8151044fe72d8151004fd72d8151006fb30d8151006f830d8151006fb609815121e7f651815115dbe7418151005bd7418151155de7318151005dd7318151005ee7218151005ed721815101efa6018151006f96018151004ff7458851014fe7458851004fd7458851014fc7458851004ff735885100cfe7358851004fd735885100cfc7358851
  | 25 => 0x8a51027e45198a51026ef6098a51026ec6098a51046ef7598a51046ee7598a51046ec7598a51046ef7498a51046ee7498a51046ed7498a51046ec7498a512aeef5498a51006ee5498a51006ed5498a512aeec5498a51046ef7398a51046ee7398a51046ed7398a51046ec7398a512aeef5398a510066f5398a51006ee5398a51006ed5398a510066d5398a512aeec5398a51006ef4398a51006af4398a51006ee4398a51006ed4398a51006ad4398a51006ec4398a51026ee7198a51026ec7198a512aeef5198a51026ec5198a51006ef4198a51026ee4198a51006ed4198a51026ec4198a51006ef3198a51026ee3198a51006ed3198a51026ec3198a51046ef7098a51046ee7098a51046ed7098a51046ec7098a512aeef5098a512aeec5098a51006ef4098a51006ee4098a51006ed4098a51006ec4098a51006ef3098a51006ee3098a51006ed3098a51006ec3098a51026ef1098a51026ec1098a51026ec6258a51004ff7458a51014fe7458a51004fd7458a51014fc7458a51004ff7358a5100cfe7358a51004fd7358a5100cfc7358a510067f5358a510067d5358a51006bf4358a51006bd4358a51006ef4258a51006ee4258a51006ed4258a51006ec4258a51006ef3258a51006ee3258a51006ed3258a51006ec3258a51024fc7158a51026ee2158a51026ec2158a51004ff7058a5101cfc7058a51025ef7658a51006ef7658a51026ef6458a51006ee6458a51006ed6458a51026ec6458a51026ef6358a51006ee6358a51006ed6358a51026ec6358a510076f5358a510076d5358a51007af4358a51007ad4358a5128fe75158a51027e45158a51026ef6058a51026ec6058a51006ed7558a5128eec7558a51006ef7458a51006ee7458a51006ed7458a51006ec7458a5128eef5458a51006ee5458a51006ed5458a5128eec5458a51006ef7358a51006ee7358a51006ed7358a51006ec7358a5128eef5358a510066f5358a51006ee5358a51006ed5358a510066d5358a5128eec5358a51006ef4358a51006af4358a51006ee4358a51006ed4358a51006ad4358a51006ec4358a51026ee7158a51026ec7158a5128eef5158a51026ee5158a51026ec5158a51006ef4158a51026ee4158a51006ed4158a51026ec4158a51006ef3158a51026ee3158a51006ed3158a51026ec3158a51006ef7058a51006ee7058a51006ed7058a51006ec7058a5128eef5058a5128eec5058a51006ef4058a51006ee4058a51006ed4058a51006ec4058a51006ef3058a51006ee3058a51006ed3058a51006ec3058a51026ef1058a51026ec1058a51046ee6294a51006ed6294a51025f67194a51005f57194a51044ff7654a51046ee6254a51006ed6254a51005f77154a51025f47154a510257d76d465104e7d76d46510267f64d465151e7d64d465104d7
  | 26 => 0x1cfe7018552004fd7018552004ff74d8152014fe74d8152004fd74d8152014fc74d8152004ff73d815200cfe73d8152004fd73d815200cfc73d81520067f53d81520067d53d8152006bf43d8152006bd43d8152024fe71d8152004fd71d8152195be7498152005bd7498152006fb609815224e7f651815201efa6018152006f96018152024ff7498452014fe7498452004fd7498452024fc7498452024ff739845200cfe7398452004fd7398452024fc739845204e7f53984520067d5398452006bf4398452006bd4398452024fe7198452026f671984520267f519845204ef75198452026f45198452026f64198452006f54198452026f63198452006f53198452026ef2198452046f72198452026f4219845201cfe7098452004fd709845204e7c5098452004ff7458452014fe7458452004fd7458452014fc7458452004ff735845200cfe7358452004fd735845200cfc735845204e7f53584520067d5358452006bf4358452006bd4358452046f7715845204ef7515845204ef45158452006f64158452006f54158452006f63158452006f53158452046f72158452046f42158452004ff705845201cfc7058452004ff7458052014fe7458052004fd7458052014fc7458052004ff735805200cfe7358052004fd735805200cfc735805204e7f53580520067d5358052006bf4358052006bd4358052046ee525805204eed5258052004ff7158052024fc715805204e7f5158052046ef2158052046fb705805204efb505805204e7c505805204ef8505805204e785058052006fa4058052006f94058052006fa3058052006f93058052046fb2058052046f82058052004ff7458b51014fe7458b51004fd7458b51014fc7458b5104e7f5458b510067d5458b51004ff7358b5100cfe7358b51004fd7358b5100cfc7358b5104e7f5358b510067d5358b51006bf4358b51006bd4358b5104eef7258b5104eef5258b5104e7c5258b5104eec5258b51004ff7058b5101cfc7058b5104d7d7694b5131e7d7694b5131d7f7494b515457d7494b5131d7f7394b5153d7d7394b5104e7f6394b515367d6394b515373f4394b515373d4394b5104f6e7294b5104e7f6294b5131e7d6294b510257e7194b510057d7094b5124e7e6094b51004ff7458351014fe7458351004fd7458351014fc7458351004ff735835100cfe7358351004fd735835100cfc735835104e7f53583510067d5358351006bf4358351006bd4358351004ff7258351044fc725835104ef6515835104ef5515835104efb705835104efb505835104ef85058351026ef6298a51026ec6298a51026ef6498a51006ee6498a51006ed6498a51026ec6498a51026ef6398a51006ee6398a51006ed6398a51026ec6398a510076f5398a510076d5398a51007af4398a51007ad4398a512afe7519
  | 27 => 0x8000000800200000800640020030018028000009001007c000000000000c00000b044fe7598752024ff7498752014fe7498752004fd7498752024fc7498752024ff739875200cfe7398752004fd7398752024fc739875204e7f53987520067d5398752006bf4398752006bd4398752026f6719875204ef75198752026f4519875201cfe7098752004fd7098752044fc7558752004ff7458752014fe7458752004fd7458752014fc745875204e7f54587520067d5458752004ff735875200cfe7358752004fd735875200cfc735875204e7f53587520067d5358752006bf4358752006bd43587523167e525875204e7c525875204ef7715875204ef7515875204ef45158752004ff705875201cfc7058752044fc7558352004ff7458352014fe7458352004fd7458352014fc7458352004ff735835200cfe7358352004fd735835200cfc735835204e7f53583520067d5358352006bf4358352006bd435835204eee525835204eed5258352004ff7158352024fc715835204efb705835204efb505835204ef85058352024ff7498652014fe7498652004fd7498652024fc7498652024ff739865200cfe7398652004fd7398652024fc73986520067f53986520067d5398652006bf4398652006bd4398652044fe7298652026f67198652026f64198652006f54198652026f63198652006f53198652046f72198652026f4219865201cfe7098652004fd7098652004ff7458652014fe7458652004fd7458652014fc7458652004ff735865200cfe7358652004fd735865200cfc73586520067f53586520067d5358652006bf4358652006bd4358652044fc725865228eef5258652046ec5258652046f77158652006f64158652006f54158652006f63158652006f53158652046f72158652046f42158652004ff705865201cfc7058652046ef2058652004ff7458252014fe7458252004fd7458252014fc7458252004ff735825200cfe7358252004fd735825200cfc73582520067f53582520067d5358252006bf4358252006bd4358252044fc7258252004ff7158252024fc7158252046fb7058252006fa4058252006f94058252006fa3058252006f93058252046fb2058252046f82058252004ff74d8552014fe74d8552004fd74d8552014fc74d85520067f54d85520067d54d8552004ff73d855200cfe73d8552004fd73d855200cfc73d85520067f53d85520067d53d8552006bf43d8552006bd43d85522aeef52d855231e7e52d855231e7c52d85522aeec52d855201cfe70d8552004fd70d8552006f76198552005bf7458552195bc7458552006f56118552024ff7418552014fe7418552004fd7418552024fc7418552024ff731855200cfe7318552004fd7318552024fc73185520067f53185520067d5318552006bf4318552006bd4318552
  | 28 => 0x800001c000000800400a003000000000000000400280000010000000002000000000400e0000010000000000005000400400400b80000060110088004018001000000c002000000801400800000100400080000000008000004000005c00400d00480080040030000000000009000003800001400a801c00a000003002000c0030000000004007000809c000001001802000800000080040080040000010000003009002c05000d004000c00400d003802000000d00a800003000100400000000030000008008004003000400000000000040000000010088000000004001800800000000080000010010004000001001000400400100000040040000068004000000001004c022003007800c0000010070000018009000800000600100c800002000800280040200030008008000000007806000800000080000180120008000018004002002000a000000001400200000200640000040010000002003001002800e00000c0000002000004002000c00b0060000000008000002c002000000001c004000004001000001000380000020030000004000000000001000000000580000000010040000004002000800400200000180040000020010028002014001000000c00e00100280160090008000002001001000c01a00800080000000020000004000004002800000800f000000802a00200100080000030000008004004001006000600100080040000010008044006002000800c0020020008014000002000000400000100a000003400a000800000000000180040040050000004000000001000c0060010028008000000000803001400200080080160080000008000004000800400400000000000040010050008006003000000800000c001001000e003002001c002004003000803a001000802400a007000006404200200000dc000001002001c0020020010000000001000000000800c000000000600400000040000040000000004000005803002600800400480020030028028006000008000000000200080080000040020014000008000801400600300000b404c0000000024002005000800c0160090018000000001001000002800d001001000000300000000280010008070000004002005000c0030028004004000001800000a000000000400201000100080040090000054008000000000000000b000000400000000580040040010148000000001004000800e0040018004004011001001c004006015001c01e0030040034000001000001400c00700000040060010010010000001002800000400000000340080020038008000005000800800c009000000800000800200040060060000000004000001000000a00000300000040070000008024003006001000200000200580000140000000002005000000400600b00e0014002
  | 29 => 0x40000048004010000004000c0040010028000030003001000400200e000002000000200480000060000030000002008000001c0000040008024000006002000000000200f0004000004000800c010000001002803c00001280040180000010014000002003800c00004a001003001c0000000008000000001808c0580000008000004006004000000000b00980080040000010008008001000000000a02e000000400400000000100220030038018000006001801c0060040000008062001000000000200000000140080090050020006001001804000001300400180040000028000000008009001800200c000004c018000000800c004000002801c004000000000800001a000803400a001006001800e000003000c0000090000010008000004800c00000e0000008000006000802c040006001000000000a000801400a002003001c0200000008004000008000000400000200780080000010008008008000000801000c0000018000006000000800000000500700000060040000020000003001000400e000000800400000000200080380030058010012004007002401a00800000000000000020000002000000001800200800d8000014000007002c0040130038000028000000809400a0090010010034000002801000000b000000400a0170000000000000001800800a0000040004000008008000400e0000000004004000000000801800700000040040060010004002001003800c00a00a000000000000000880cc00000200000380040000060008020000006000c002000000801c01c000000000800200a00000180000030000000010000000801c002001000000400800100100480100000028000000006004001003200400300000020010000000000000000002c000005000000800200b001800000a00500100180220000018020008002003000000200000080000080030050010004000000000000000600080240000000038014002001002800c00000c0000004002001000004c01c01e0020018032009000001c0140020008018006000002800402c00000780540000000010004004011001000c000000000000401000200080100000040070008008011004800000000100080000000020060010012005000008800c001001800401e006005001801401800680000000020010000000002005000000000000280140b0012001002800000f00300080120000018004008000004801400200000080000040000008000008009000800000600200200000080000018004000000000000400000000080040040140050000000002004000c00000200000000100060048000006014008800800200500f00040000000048004000002001003c008005000004c01800d000800400800d0048020008000003000400e0000008034004002001
  | 30 => 0x38b2324a490d00002e4000000000005660000d7513f803c00000002101273315503b356c000209502749240000000000083923a00001dc000000043b8000177911300000003610000000c3100000000000058429f057440f400000009030000662053cc0739841ef073400020c033a1e840003708179000070d2af4fcc3e94000474c000000022805b0000080000020dce711ff000000002df0950c3c3c3c000063446800000000da848906b000012b000038c4000000103400006e448291c30000000441c5d6421ca03305407018491e9000000000010380000c4d3de471100000003b903711668f1b06a05da14bc0000000edb00009450fbc42c3a4c0001bdc0003e60e471004423043800027e80000000bda0ce05e800009693ab8000000000000008621e9d088430c0001368000000000045b80003070000000004200000000000e6649e40001eace7c2a40000303c24e13488d7141800033507b7000434d3c10a19028089844784a236b0a1804d919931f403728947c138ace800000bef186080949d0b8b1a680003ff4d4a0730000000002e0000fcb00000000000f5a00008bb0000a7815f08ab2aece21017cff30000d0b18e80a8285525242640003a0400000000000000d45000011b09c8000000116946600002fe8c53000072f274000000005ad04a4d2d1b7000000011800000000000000000007f3381c34642548fd0024b3e01ec000001c0060110020000004005000002001000a007800400800400400140080040000014018000000001401801200a8000004001002001c004010000000000801100a0000002008001801c00c00100000080100000000010000005002800800c0000040000012000000802801a01300180100000000048004002000005800000a00000a8000008004000800000200100780000040000008000000005000801c0080010040010000000000001400600f000800c00800000080000020110000004010003000801801200702a003801c001001803c00400300300500020010048000002001001002000400200100040000000028018004003000000000200100000040000010030000000004001002c0000020000004004000001001002a012008000400800a000000c00600500000440020010038054000002000000400000200100000060040000008000002000003c000002000000000400000080080000020028000000000002004002600400200000080020000000000000000801c00000200080080000030000030006000009800400e00000300100000040020024012006000000800e0000030008002001000005400601500080000020040068004000000001802000000000080000000020078018002000001000000800300180080000150010008002001000001c0000020010000004003009000000
  | 31 => 0xca48ac23621b91500adc76629b905211643903dd00be3b209a432e8e0a158456b37607162038ea43c345702ca4313387019c000065800000002b5400000005d04528e0823c07f40000e9d00000003974a5800008ae2c68b4e1b200a10000d171bb077700007eb36000960bb87a300009503e7cc5200000000000e183424afa07280003db51e14620b462418000305000000008da49c03e03bf9228234c691087828f1d38343000000021340000000000147c0002b344902ba889e40202370f4060a411c00000001bc2c2cdbb1d14e1d274400016047301f949ef434cd6a090cce700003bb0de800030d81050298d5400000843fe0000000000047c090b10c43ab498902f000000000006323fc08f10000000000106a0000e8b42bcd1d2378761079103218d4fc449910da042103100001ed0efc00000006011670a592cb0000000123f000000033e0d010d8800000000000000000000000000009d63adc00025d800008049b13d340002fc8000000125400000003710000000000000000c90e5c56000000000000b75000000008580000000000009128d425800000002410000d3e33d002b1c28f75044892a1c0916b1fb08b218189c12c4508616185a9410466e39e40f2493c58e42e0b313a70ea302880000000017334510f422c48a3a9c000000038b37d00000000467000077100011eb1c8d1d600001184a5110316d8da312aced83cf000000000003e040003e3000000000002454efd00000000000bfe00000000de077d00000000000aed2d303de2ad52800dac7c004fc0000000ee9257800012a400000006f00000000000044627487fa00009990000a7a3c300001f70bb3240091b070422f00fc33600000001f18000306d190000052410ed1cd000068b42dd0190000000045c000297c00031e0ae50000fa6000085d09240000000000000000006ece9600000003ee80002d80d3b34b8d9905f8b2d00008a030c412e0000000000000000000003c908070a145a306c80000ffd28a00001cb00000002f40000000000016800000000000000073900000000000d10096c8b948d8e8902a800d0000000000000000000000000fae379c0002388000314436137700001160df1151d05636cc0c6149c50d00003c900000000000a403a99042426c90245d800000003580c34a5b3948e4d11b83440000e0241d82f700000003a384b539b06450000d850000000000085f000000033580ca1ab4000029c1bf0d9c84b00000003b8c0000edc72e00000000001010094cf9134109be218d29315200000e4c0000000dd323c8ef22f940003e3d2990f480000e790b210cc7781c18cfa097817f0000689000124441b07310bf0ed70d14bd132288dd40990c741ac7ff0001283399c0002660e6a2708000300c00038c800042681910000265000000000007df3b
  | 32 => 0x7e905e12e413500006df0000a4225e8000000072a1cd4000189518a1f1c45d00003ee34391413b150db00000000b710cf02c0e1e32fc33129347982e40e40357479c000000001e400010e47131c146940c2d07b00005890eb808c000070000004fa0000000000000000000002bc07f624ec000000012d2584ab100002953cac00000000003968000122c0c3000000045ec00000000000534a96165c00000002131ca09f200000000ec012f08e800018405a40000bb826a50bf4380f0b3eb46980000a3035bc9cb428caab0000032031c00000000002498000000000006f4a133f7c28820a515712a809b1e18000469c47c04cc39d21f08893da91ad44b82cc3d5ca360000c811614e000db49bb1eb8000371800000005b1477828c1bf023e298c0000000ea224d065f38f4e152054f8e1414bd42c150291324564037c2bd313910c00008ed2ae09bf20f4123397c5e30d8c0000000b201ff83683d14ce40000c6b352400017b0f9403f061c06400000fdc96a00005a236d8fa30140b820000864417c0000000000231c000244c78300000001c646533178000000000044d11ff45d03a543700001a7408d4708000000075b0000a3e193c95b2ea1219112c94d3d982863a100000d70ab037a400000006da206c7aa31f823f000000006bc0000000271000000000000000000d5600000003f7800040900000f840002ab013c47a0ae221e4d2c164cae03b646c920481a412040003d280002b2838900000000fc872d00012420ed402d00000002f989f906642420000000419000046a4f640e2800043ac0000000000000000000005a80d5421000000000000c32000000000001e93670cc13cc4cf50070b740000000222000032cc000000022e285cde6285800036b8000012824a00000000d2408f08502a920140000000a3f3ab4000000105b41e503600001970d0000047943f50e9d16300005140000cb719e8e1b34c40003784d080084fce0000cdc22a474f3a2880b1f5800020201d6000100a2a7c000250476844d90e331f0a9527a085946351090a601e530845db1dd40b44058d1a12bc33e319c6950244ecb425c4073bb019e22fc9701e14dd7414d2850cd4cff0000f730b60aeb356800000000000000c1a38641d33e703be0000000000110d0000b1c2b08c1d00005103b009770d6c4e9000027600000002eb80f30000eb40424afc09e87a011c84180bfd20327a866407451444164b1416745d40028cee457846102610b00a6ceab095c5fb000053032705b32e745ea00002583fd0a9d000032d0000000000000000005343fb400000000000a8c000119883f0000c0129880001aa46f6000063126bcb934554d3230b054a04103273ac898e144cc8d1e04b1604f43832afc5aa1ef027f020828212f864d075d0043d811170cc0896056c1143ced1
  | 33 => 0x1f648c40001a9c5254310fb5316c000226400000012a2211800008645bc03d00003cfc00026b400000000000000b670000c20000000000007ed00000002f080000000000157d0f32554e2834003a80b2909d052448642040004418d92000000000010fc380400000000af3330000391850700010c50ba8000000121d000129a2c2511d44e11f10000f6728900000504c164428bcd000050f3300e9a00011a60f3891a1f7400043540003278ac12910cbe183c82b2eac00003a47a90d4484a0948c3b256023937680662340e4a3a6c1c649dc03400ece10000011f20689a2057c0002ef0d7639241ae414473a00000000f0cd441e08000000000021c8f09262806134442d132500004015039157472400005c726051a2411094903307fd0708000000018e184478f45d423d0000000058c68533b080a140c8ce1f105fc000123d068029e0000c1e370c0000000647000119209f09ca000000004e83540a900000000000000049c0000deb0000bc622bc00000000002b18bac45e400036200000000ed22df400010d87843be09471dc0ba7497878800cd0830ce48703880000000026211e8f4f02cc5fd08c4000000026011d00002cac0003f0c0000000502336020320e800025ecfd23ecc000000000000004d510710733104000000000000000001f2c00038446ce208894f1f3c8f8271ce9f00008bd0f3c056055cc873660f473f8441101e8eca0f5cff9091c21509a04881ef4c5a2a805670000f252bc40003cb0000022d2160000ee748a4fd8450c0002dcc20535c86ee466c17d000028a25f000000004ed000000000000001f443b8000099210580000000000000006b00010c81ee11833ff8d633fbcacc325c68141f486f00008812a080004704a0f232c00000006f934f000044bc3bc2fdc0471930af20000aa318ec0003a7815302149f60f10576000000048946652b644bb31b0a370000dfe3fed03c00000000000ee200010ca00000002ef800033684ae047000000007503a480000000b3240cc2c50000f5e2fc4ddb0001128225461a05c000000010b3033c00028081a90000000023800000009c326c90a53be400020040004a20000253088400001f800001931c4914000003f042ac0000000a4c40702890b5c0c000002021f2866600000004344ba600004ee02a4da02c904c50000fdd00011f333e4000000052d229106214600c1182447e2e010612b24352000034e000088d00009ab00e8fcf36e027810a85730cecb6633f07e21010cde18201613ec8fb849140d808281e3000000000010a91a208d200010bd138c00000008ac2f140001ec0000000000025ac4832b4000000010f60000e6d481087b186474221a510419f899c142811a32682e33bc0b071dbd2000d742913c8c6b72e9098239110483f208f91b9506515b82f0227c93e0
  | 34 => 0x28b80000000986000000003f87324658000000016a2b688432fcc183228cd3734a50f8472400025480301238c8936d43da0cac7d93b30b5c0000000237c12b08f00000000000248d22c398000000001d51568b9a00006af0000000000010c39e8cc945b028b00007b50000ac00000b643e1c0002288e951dc8cd23418ed01b8041d2b3c0000b640001028d1f000122e402c4490000aaa16980004a7c0001b586bf17e123e000015d3ed022211e0c40127800036ac0002f54fe61a3c0000000000000000020b000000002810de4fc10000c2d1928f720ca006300002500f98266000086c467901214fc1600000000000000000004d92cdc54319246f345480002354a7f15780000000bc8000079b2f4cca82d68000000124c0000f8414d800035840003ec000041c05d117f82ec0fa800004280000000562102c000000000011580000608f883ae860d2714fd000001be29cd23800011b1333ca971db018c00009240aac5453a5cf90156c000140059b00008db301416d0e8c00000000000000000464400000000000000000000000014809fe00010712d00ef40000c9537a00000000000067c00021844963ba00000000f852c980000000f0a0000fc9000004e00006b30d9000000001fb0000a8c36c47034a800001fa40001fec01d03f418b263cf541265253000099500000000000c452e54000000000000000000000000250c00014b0000014c000203c0e735b456f492c9a0000000000001a1000000000000000000df00000ceb00001f407b0d303750b9c2b58166349c24516210ed00000002b10337061800001c8000000000000002c445e818a00010c00000000139c5f90454d1e1f3000006dc8200920adf1d680da00002a100009c435fc9783b685ce000000000000001b742670000000099027e0000000070c0000000000000000000000000000741315c00000009d700000000000cbd336508c000111000000001890ca1261c0003bcc87d1b288a6000000031cc4a3429c6db2bb84ea34491ea166123b2c9400030a50670000d6411e40003688007000117000000004350000000129549a0993384c32e3988eac3a1c605478cb53239cd284140000012521300007223fc82af3de8124000040e3c2090a00000000000000000100c0000f4e16e000041e0c3d36a00003af044c000000022744773a3cb791d2515d47104b01b04000185d226061410317fd1614118d791958000000024c000001100008f30000e2916e800007c9160000129c0484eb919b00000000000408502533202db272523c0001206199c0001684df9309000034e92050000080000087418008541558000037096c000045e39f420d0c74ca00000f9a1940baa30a8e374008c023c6800000000000610000000042000000000000966152c628000014600004a5000104e0845
  | 35 => 0x88c01aec2e033940003f5000003fc0003b04f44003cda40b78bec282800020c800025fc3e42c5cdee00000000000823000000025b515400011f400011be2dc833f45f41db008c00006a83fd00000000000cea00010553580bfd3d6c4d84568e0f459052324bc8490f949f11c200001f68797211cccb09c092b1ae4487369824d3bfd03e19d49544128c2223bc78e26005633d00a8928051a336f4bd242d80000df00de0000013198490e203045c10088712f3c14a261403d3cdcc6f34cc34f49291c809b0828077927a32590ae14640000668b1b3ded276483847548340000000988224917f000038f0000852000108021d928c000074300000003acc5b023a00002cd0b860fe02be487120f3578e481a0c20c486805a44e44ba056471838ccf5d291400043882272af91120000afe044505a3af48510bbcaa50a40f771d1c12a1cf51250d0461b006c0f00b980fa29a4a2c2084b5901941b32f748ec1398c0c000053c31d0000038cf65000076b1334f0337d481000c4ec60c185871fa80000000c1200000000000c25193873f2acd0170000000000118e15a0c0019012140000000351d1a813c8d0320903d1286c3340720c39413494016b8bd90000bbb00004534560e2a29c0ffa000046a00010b10000359133c0000e7000000000e1000000000000004744c8600000003c18f18000032246b829c3c442790000eb5119055907806be23dd240000000021d400000000003230000198c45b002cc9b167924300002eb000000015710c600000000afc10d229c00039ac000281c6220000c99171429300000000000000185400019048b724b006f1fc911529400e84050b9b19644733b3c8e1000082e332855549fd259111cab929803eb47b0e2200000ae4938000000052642d0b5d170c2d609cc0551d480003170a1400000f7292c00021dc6e144fc41b4a3c000000000000000003af83910000cb000000003da000000000000000000000000027180001a48000000000000008e43f191da213cf2d000106f00001f62070bfc00002bb215800035c025a125c50e00000002778d573488c7206c109011d900e0ad00d72a90eea0000c0a00001df136c00005440002884000454c00000000000decb6929bc9ff2c9c0001d45271367c0003124a8a0000daf00006e8378076206e000000010540000c4a06d07a800011300000f123098a000d580000398f072f80000000015628782b828e0000000000016090bb3ae00000000a750000feb0000ca600206020000fd70000000000000000002ac00010030c847d400000001358bb043a400000012081f6c0000a6800000004cc00008943f4c3c20b409572dc435a0c3844410640003470000216800000001751c843d3408000020e06f800000410000614000001f19bc0000000c9d306400000009a14a18000
  | 36 => 0x1d6400000d8ec73ca465a21a800030f8eaf1088ac722f80000000301059c26f3c780000000b8f000080000000002ce000019f43d8064857d000000017c895c39c86a600000004714ed40f30e2f1eecf14113c0203704a663164000207c0dd496c73403a891411b02f5373883b139481906b44b3313d13534946932cfcb6d010009a46cd12c115c00020580000dc8bc128d096f4a8cf1c174c0002b8c0002ed512114dd22d0000000043c2870918a1028a000000001b12464cbb02c856c406c0001a5921723d8bce000060b06e46cb1d8d2373da49211b3c72023990ea2268cbc1cd8000097c21f0d4cafb343d07748cc6b518585dc1bb423b024ceef2d3cbf8000045f05bd1aa1a0878d0ec400028248cf0000501447c000133804c3e80000000000028980003e5c357000023523f0f4c3ef8c1000000000000aa6491d1620d7c0000764000377800021e813827dc49832b8d7d2f6c62b0000da91d7c00000005e4452400017d8d1300009ec1d4ccce000000002900000000a56000000011ac00012f000000010fb00006ac1a1007600009752de00002a840000000ec919c085009dcb882bdca2d4775119396d0a60fd800039e02c2000000000008551ca4a810001177173000000000000fc4fe900009a748c9133295c00000005e500000000000ecd00009d415940002b7895928ecf7837000002d400003794ed5238c05117d4000287047043c8d140000d2419c4d5811fc9f43eac000000073c063cf2132b02742fa0fe52574bad12c929003d5092101470c14e0cfd000077c32d4aae0000eed000073b0000000000000022ccb2f328d14c0000b4312f400043a000022e80002e1c0002f580000000d8e20440003c04d46068d25f2f240a51548a862a4c8cd48042320b2c00032a40000000ae400004101b887bf4490931000058a00010743a300003e08b1200000000738a2b1fe440c00000000000b4200644f31cac813042d17101c4f4141f8b7f1dfcf9b000003924f0000062011000001b6124c000000029706944a72754b910d2017429b501a0000000000000000000000000a8417088ff3d4800000011941f9000000000000fb4a463774dcb0000000051400021a05c8424cc913dc4092055513a3e0c2e810dc3d50e6d07c228447d06242fb230d1fc330926905887141e2c24b04b0ab42de87461ed034a2cc0c463890733487c1d200002a731a000010ac2cd000000000004d70a74fb10ac000000000000000d16488d1a40000e3500005e22a2c0000000000000038822a8a5500011483dac45a3afc0000f886d31fbcf4935e0000476c28d20191df00011853be8c0600009eb36786510af0e6e318c000000019800006762a6850c1a006a5000046f0000000000000000000000b1c0003540b7b1b18d620be003e000079a12d8e7520a81a201a
  | 37 => 0x611ce3a18000331400000000000cf4000000126c00010a8365ca8e32c8fd949c86a2081d01f37647e300000001e28000000071d00010ac00002c8160cad83724000000000012dcd51000000018d0704000000000005920000000163c697061c74a315007722d8000091000007a125a0750000000072c1e947900000ba5310c000126899d39601000160c2f3914b68013c3a200000003d6400009ac000000106800010cc39fd1d70f1527b000000038e04c21e58d6839441e110bc0002fd000000006480000a0e3ac46380000e4c343400000000000000fea00000222f5c725074000000000000000f2e0c480000000516338c880000129e00000000000000000000031dc0000000cdd1e74176195c6b000007cd0000d35000100f036c8d40000000000000000540000000a9b3c40a0c000000015a4cb84378000000000030dc2f1000116d13005580b88e7b0000d4000000001a4000022d4480334c00046f098944c4e3b00004eb0d4114535c47de19c800000006fe1ecca391d2c61e3bc4bd804c082d222c7ac33340002a00de4112000017c4a611248f9d25e40001380b9400000002a34c820000a040458af4000068700000003e2c0002d2800000000001ec4000262c00000004250000cfb0000000413c00049f00001980be138990150000000000000034080000000dd20c2400027ec3083a4031e2bbcb6e3ea05110f00e05294c983451c1c40ca849d2240e6909b87600000000000100d00008c8000005e00000000000000000000013d0b6105c40001c240001838000032c9840000dfc437c69e2ed85bd000108912987d72dd800000000000000000000032c000039500000002074b3d4918e2310340000000740243004d24e0fe300002060000b5e066c6d021380001e64d4f0a586990000f990000abc000048d000000000009011378adb0b0d1c0188c00018b83b21d100002520fb60c8119733180001b4874c3d0885c22c066d2f303cb308c0002f0cdf2232807f20090a146184d114206a849f49fd06511e70b249050f04b4d1fc40001ac82da0d0809c49e0ce92be400043d000000003f439c052e49944a01c3cd732b4c40f1d590cb16dc00000000003dfc000011417a172896e428899002d4dd5000000000000000000a4700009fc00009e31de871c000090926b113b000058c000102227302512d211d43c5cef633cca9821b4000000023800000000000000000000024785d7000067b2ec466b0000bcb0000000000000032400002b5d22100012570000d340e100003b44dba4570d8b000000021942290db8d1b0000eb6252907a2c2000025cc00000010d200000000f70000000000024700003cd000000006a4447064b46ac1392d590840000cdb00000003d54d4e0000000288c15238b043200005cb2ac88453cc00000f50000398c00
  | 38 => 0x19d09b427000e4041853d0ea80cd00000000c1c000000822500000003f80be3360c80d38d8b891c5400000000b100000002fa47800000000215cd0713500000000ca700010a4000030530d511b20e4f960604ebb0000a2016fc000000000011500001108426132122400000000000ce129c44f72c3000000011a505a43871524e3000000000000f6c0000e0c0c0c0002fd87e0000110523a8000000081e35a45960a3800040a80004780000000000008d00000000edc01a402c00000b700009e00000000000000000010304630d4b0000cf21e7cba210b499a1b5000026947ba028cb632784ce601d016b13a11fe01741020f6c84c118063d3644d150000000190ce42000000000000003e8488a15d4000381000000000003efd29b00004210000b8d423800037306d80b5400046683b626a000046101542fa895f0348c9f1bf40003dbc000401c1cf00008ad00000000000414131c9a6000000001f000005b894b181c2b61c9c000274cc9300010fa371419d12540003dc000007fc40015ed0fe18dc00000010850000d77000092020c51f749711e42c10000000059100000000000beb000000002505cd03ac32549a8f7e2b98aa7000000043f49440000c302b20000000109c10f124d1230b2e282c15e26e4e4f01b4ed300007f048d400000003d90000bf51e980593f34c7100000000000f6e082c0ed07d4b510000168321035e449c000312c000309cbaf3e8806e0058cf64624e7638d08732ee4c7f086826a0890ac527b40004004a7e110caf82c04e6500006032e2922a21ac00046fc53941982ad05ec5b50c0008905c8f61000065d0c642180be4e990b3c22b00000000001028000000000008eb153c0004278000371d18f0000b540000c8e406041e221c8781250cd00f9c22640dd0d6000101d2cf0c2b109c00042e88c502fc43a00011a12d2c5443ea40000000cef0000c7508b4c6900000000000ea0000000026d869b059037506002c03b84d383ccd1b04594d8935b800023f889300000003a20a79167c5c400005ee0b500003e240000000000317c62711a42f3000024f2d94f50249c00c1640fff377cdff1b8d17810d119f105cea5395c63c39789422e78b0e1bd001e00009df00000000000c9800000000e587f8000122f395800000010351da476d1e54fe728f0fe201a0535155ca650ccc2e11138ced088d06e4a3895616b0000178025645391c700003810340db7484400007141502b0c8830e48c6200a4a0d145c02f1fd44e406588042568ea910900b6253828318d8d212888541494510200000000000cb10000000449896800004ff00000001ac400026e000028bc17c00007e6000000000000000000000331c00000009910000000365463000011fd2b8497400002a000000001b0c0001d74acb19e0d8d0e34000000000034
  | 39 => 0x45c0fb0000d8f21100000000000000000000009221b08d7e049813b39504f02a14485320c1ab1b149dd44f83dd1b011ed3ef00971530b0a0d986ae29280002ca000025940000000f5c00002c13fb00000000ec2254c000000000000009b52aa000000000002420787359c000216c000012c00021fc00040b901115500001dd0b3b4a1c2b231ec54215e088500001ee000000044a80001f49220364c000000000027c06c70000add00000002a646691bd4f7d468070b0c702b1437451a1a309602c3401039f80003f6c430190800000004dc000000000000002f9c00005682e73bb8208499865c1f1461329740860ddccf01e90a674730f351e88935130cc3442805bb3a84d3d06d51460f1888c2c60caa0ad46f12b9d1673c082ba0b180c216bca8718a919c1f40e53239479317ccc080e50c4443c0aad42a883c00000003ce46e639380000478da720d0c3a0ef41ea0c309320eb00003f7036946e9212205c0000ca49b300000003e48315124400042b50cd00004f817c00000a50c5d00000001600c090000d7b4260531000000000010ff027829232bc000254400000000001ae80004a605e7321400029ac00000000ef10251dc452c8533c880004860dea2d145d219a088247544510000b1331088c417d07650dc000000000003428efc2460f13046526f02b000027e08dc044c0001b304fd0001261482c0002b38000446088e1fb82f2163427b2738d743fc478c009cc182cd4178000054003c4aa932ac996162c8c10000e3e278800005606731484fda1fdc000000000000001310000df801d437d000000000000000000a1f0000000267c57e000000036f800000011822770ad239a0f5100007c82e3118144a43e3000094607983170e8004303503fe05cc00046d80002c7800047e0c5800008362e0cfd103e000022d07b61d21114417000042086bc32b529720cc8c21f9cfd500003f30b7400040183232ad82630000b4937b4b39000000000000000000000000000004a12390000ad100003d6389438048887760760d230000147000000043bc0002bd40d10000b57354cea840240000388ff72d1d17e15180001718000000040600010580000386335ccfe00000004764bdc19dc0000eb44411b1126e24a00001b5c62646dc0001454d813d0c00031304a148083983628da5473d08d23ecd823ff111101808673b7cd4201885df3aa800000109100274de240b40180404cc30ecd195000000003d85c100002aa39bc00037d80002920000236000003204e14954000000031124e80870000f0e000000014a431f00006390000b2a00000000000000000113c0000000353400015c800000000002e4871e00000002f88f1617840003bdc00000002e500009cd006868e0000dbf36a800049404c116945be2d6ca1130351d02ffd0633c9841f39400
  | 40 => 0xbba3b591cb00012890000b85000000000000001664792000123007f0e17000032f4a040002ce862d0000d8600009ee00000001f54028000070e1b64f9e137444a395414400004b126a80003e180000880ce21af40ab389d25800003ba29dc99721980003834f281eb4e3f000022a0000000049c9da36b430a3a60cc400011b20c6c757000000047ec2a63ef509f000038e00003ca0000bfb0ebca8f20604f12678b06000026d00000000e986b645985c92e810c1000013418311b40001210279421c00010b52160f2a46ec9db461c4f90000d901d901a737dd1f53190bf90000fc000006fa000112b40fc22c14749d949b42d23848d0528cc000000000038e80001919284338063f19fc217000044d000050400004df000000000000000bb4aa20e90a54258c4131cdc00002ec000000000000000003a500000000000481cc922e38d2a209834c15dcb1000006eb33c41dd44b457928d400025f44124360a5e361c000000115122c46a3322c89c126c2fe223c3fc318452b0494000210800038240382ba4000350c15c31952a43b980001654cb6027c77b000108f3c740481e240e540790e60964d5f1774dfa2944a5a0c105712bcc0000000e160000aaf00000004400f802db0633000053a41fc6f20c3c82f0b384d028f518b46751fa053032600004a42f0002a3bece0e0fa028031d88c93b0c7ce16e454e16c8ca513100001f0c550000000031588d117e86b4273c0000000ff64384ca203b85e6052cf2f00003140a88f1534ac5cf01f800000002fd00000000fa51202474a2724fc9672d545224a8451c00006d143c4000209c00000004f645641652d880000000c13000005213b06d50aa043539cc71f050cc11120892d16d10f7000127e05dce85241cf0546bc0462365043000005c00007be086c36f30100c50000d3612fd1d829246de2bf4fe41478b41238007844f43a908480000c08fca44c892e487825c3e90a763c7ca3a3d20aba00012673df03733d18a7b3bd400013d40252a480900000faa1d50e913e28f620d943df0000000000008310a4cb400012560e303ec00005a726f475e3564cdf2c0cc5012d046d435d22710fc2f63744794453461f3290b84205043d3ebcd7c000000027a400600001a62a50e061954000293800000007c2450912243910c20f1c67c050053b3ce0a293fb86860000081442c86022e073e0000da100001c726c0d20378c05b03b0f2700011ee1188d480000b2247bc00010b800011140002e583850954fb7070000000000002ed09620000fac000034b2fb8324134c9c8000014e00003fb0000b150000fc20000000443904042280ad2a70d5218b05093d4c47b2f109641ee4f4b09f408826b800021200441700a6a00010f5366c3cd000124819101f13e5400000008353e4cae8076841a36c000000000002
  | 41 => 0x2f78e390000000307c2b3000000000000002b510e534300000000e7424cc0003d7c00000007d800004ef13f071a146c000000119333dc9710000000000000018f800004c80730000b9f0000d942410db22e84db909a490f2d7c12014a09111210f3a17acbbd2df05e900000003c80e830001291072400000000000dd000000000002820aff000000000009ba00006e900007583594652498ce0339900001aac000424400034fcc0e0a64d9612a0726132839a2818f190000c800c58e1430fd2410874c6e31b46a01a7d02c4180b7e1d35292000037f0000a1a0508a1d3e34e0b142d14f2fb51c615e853e448c31829b0000000106d00002fa10546cd28a865e22a08f400000000000000400077300005513d8cdca38f06e7015076e0000ff515fc3820c6800003652150000c47000000000480001020d6625c8fc547c8a72486c62f231903a000045535e82b900010d9000087e00001f00000edd31a80000000a3200006b80000000000069c00000000050e1f123c00000003b40000dc800004fb00000000000b58000000012e089b188003541303a146e0000247c00000011e622f000002e46a10310d6b2edc1e2000025d00010f90000d5524dcf580000eeb0a1043e2c7d1d224d8000083c0000a945ef000091200000002a7800046f51b521780000db00261da807d0810000000000042e4000417400000009e726300002790000022800000000000000c381de40000fe81f900009bc00000000000000000000028c49a317dce4b17b400000011e24a080002ea400035700000000000132c0000000533000000019a8000000000000000000bd000019500000000b6f2add0234420c334a7449f11c4f320000b1926dc0003180e413c000bc28150c943b0c173cd8b21302cfc718a45ab38b8005373c1f7047400019e4dfb45c8f3e297080345bd0132f90dd04830d6c000019510e03991a28dec0b4c06742f92342650a4f415cd192c080e0034cb0f000000000011b906e873822440002a200004558bb200000001fa000030a00000000000412515f0000f762990000000000000003324980c483d587d346b070141a4dfd2cd87c92b70e8208846fb07f86043970ee50cf03471bfcede08cd17311405d542f0a6815b42ae000000044dce8d290d04b1650e592a4526b1df8c880d80af600000002e60428294800000010750f21094000013705200002efc00000000000000000000111a0000b81000000004884e20000000439c0000000000366800000000003868c7000009d80000275000054d2dc052a229510141149f324f40000000dcd2ddc93934e48d6035809531e83f936300001c1d0d01c5c4c623300000000c791bbcb9702e8b993ac024015a8cb935300b829f4000000000029d000000000570000000196cbca36d07af37ccce825f80001148
  | 42 => 0x27d4a12000115b482400000000ce1100000000079100000001ba85533b1061d000000000000000000000000000002f4b1d000000001b000000001fd082400000002e934bc000000000000011f900000000000fa7000079e0000d26000000007cc841188400037bc8f5079cf3d27980001d7000000005d900000000000b440000000000000007ac4ad39dc51236f0e2d00007102fc0a4100007671f84b332dacbc723a502b0a7c83e00000000000c660000bdf041c000000129600003b9000046344580000000000000000000008fa3eec5d849750ce1ec8b000000000000117c4a2c00014c84650dd8fd63ee40000000d4104f9168000039f08c099b0000000390cba323b8fe849d4000000037e0000000026468d2634261000000000000000000b522494dd641c800003e4000323c0003674cd50354c2e22180641aa8755225c93000000003b800000038aec24584031c6ca8345a8b6a
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xe8d43cc962040071d90e992c408003a350d32588100053742864b102000a6d850c9620400155d08192c408002ab61032588100257340864b102003aea800c962040014dd0a3a2c4080029b614745881000567418e8b102000acd831d162040095cd023a2c408002b9604745881001d75400e8b102000ae9801d16204001c5ea92a2c408002b3a0c545881000566c18a8b102000a6e859cd62040014db0b39ac408002aba12735881000556c24e6b102000a6e851cd62040014db0a39ac408002aba10735881000556c20e6b102004ae6811cd62040015cb0239ac40800ebaa00735881000574c00e6b1020ada6d8594d620400155d0929ac408002ab612535881000727c1aa6b1020ade4f3054d620415bc9a60a9ac4082b29ba14535881000557420a6b102000aad8414d6204001c5ea7a1ac4080038b54f43588100053742c86b102000a6d8590d620415755b0921ac4080039354e435881000726a9a86b102000e8f8350d6204001d1ce6a1ac408003a35cd435881000717a9a86b102000e8e5350d6204001c5aa6a1ac408003a354d435881000706a9a86b1020abe8e3050d6204157d1860a1ac4080029ba14435881000536c2886b1020aaaae8410d62040014dd0b98ac4080029b61731588100055742662b102000aad84cc56204001d1a8798ac408003a350d315881001c77c3ac5a90200387f8759652040098ece2b2ca40800f1e9c165948100265b38ac92902003cba7059252040099ace2b1ca40800f369c163948100063ab2ae32902000cb5645c652040019aac6b8ca4080233998971948100063cb2ae12902000cb9645c252040019b2c6b84a4080233a989709481001c3e43acaa9020038ec8758952040070fb0abb6a20800e1f217765441001c76c12ed90820028bc84dd921040071d905bb242080030f1d265484100061e3a2ca9082004e6421595210404717b0dba242080030f99774484100061eb2ee89082000c9e63dd1210412195cc5ba242080022fa1d64484100345e43ac89082004ea421591210400193ee8b1a4208003271d163484100276210ac69082000caf745892104001958e8b124208012b920562484100063dc2eec8802000c7885dd910040018f6a7bb220080031e54f76440100065da1eec8802000cb943dd910040018f6edbaa20080031edd875440100071dbaac88802000e3875591100400157706b222008002ae60d64440100071da9ac88802000e39535911004007976e2b22200800facdc564440100275918ac88802000eb1315911004009d6442b22200800396a1563440100072cc2ac68802000e5b7558d1004001cb0eab1a2008003a6a1163440100074cc22c68802004ed28158d1004153da302b1a200800f36dc5634401001f69b8ac68802004ed22158d1004001d62c890a2008003b458d2144010
  | 1 => 0xb0b992c808003275cf32590100064eb9a64b2020008be870c9640400117b0e192c8080028fa1432590100051ec2864b202004ab6810c9640400156b02192c80800eaea0032590100055cc0064b2020068be87cc5640400117b0f98ac8080028fa1731590100051ec2e62b202000a9e84dd5630400153b09baac6082b69761e7558c105672b884eab1820ace5a109d56304159caa213aac6082beb6e017558c1001d6c402eab182000c5f875d56304001cb700baac6082b7962017558c1056e2fb82eab1820adc5d705d5630415bcae20baac6082b7968417558c1056f2a882eab1820aca5e851d5630400153d083aac608002a76107558c100052f42ee8b182000a5d85dd163040018baebba2c6082aea761e7458c100070f3ace8b182000e1d759d16304155d2e213a2c6082aba68427458c105574a884e8b182000c5d755d1630400193f0eba2c60800327dd57458c100070f3aae8b182000c9d755d16304001c3aeaba2c608003075d57458c100064fb8ae8b182000c9d715d1630415793ce0ba2c6082af271c17458c1055f4b882e8b1820abe9a105d16304157d2a20ba2c60800297a147458c100052ec28e8b1820aaa9e841d16304001c3ea92a2c60800237a1c5458c100046ec38a8b182000a5e85dc963040014bb0bb92c608002a7a137258c100054ec26e4b182000c9d74dc9630400193ae8b92c60800297a147258c100052ec28e4b182000a9e841c9630400153b08392c608012b5a047258c1002d6ac08e4b182003ada801c9630400b5b300392c60800237a1c4258c100046ec3884b182000a5e8510963040014bb0a212c608012b5a044258c100056ac0884b182003ada8010963040015b300212c6080038bd52549881000567418a93102000acd83152620415b4db0b29cc408002aba12539881000556c24a73102000e4f8354e620415bc9e60a9cc4082b7934c1539881056537428a73102000aae8414e620400155b0829cc4080038bd4f439881000716a9e873102000a6e8590e62040014db0b21cc4082aeab612439881000726a9c873102000e4d5350e6204001d1f06a1cc4082bba39cd439881057746b9a873102000e2f5350e6204001d1ca6a1cc4080038b54d439881000746a9a873102000e0d5350e6204157d1c60a1cc4082afa30c1439881000537428873102000a6d8510e620415555d0821cc4080029ba17319881000536c2e633102000aae84cc6620400155b0998cc408003a350f319881000746a1a633102001c9e7350d620400193ae6a1ac4080038754d435881001c7743e84b1020038ec8750962040014dd0a212c4080029b61442588100056741884b102000acd8310962040095cd02212c40800ebaa00425881001c7743e64b102000a6e85cc962040014db0b992c408002aba13325881000556c2664b102000
  | 2 => 0xe54594100061fba4a8b28200387c8755165040014bd062a2ca080029760c545941000c3e42ee6b2820038f8805cd65040018bae7a9aca0800e1fa1e53594100051f424a6b282000a3d8494d65040070f90ea9aca0800317dcd53594105643f438a6b282000a3e8414d650400147b0829aca08007279cd43594100064eb9a86b282000e1e5350d6504001c3aa6a1aca080030fdd274594100052f418e8b282000a5d831d165041598ee21b9aca082b31d443735941056c3ec3ce6b282000a3e849cd650400147b0939aca080029ee01735941001d3c402e6b282000c5f835cd65040018f700b9aca082b71e201735941056e3b882e6b2820adc75105cd65041590fd0e39aca080028fa1073594100051ec20e6b282000c3f73d0d650400187ae7a1aca082ab8dc4343594105571a88686b28200087e8790d65040010fb0f21aca082ae8f61243594100062eb9c86b282000c5d7350d6504001c3f06a1aca080030fdcd43594100070f39a86b282000c3d7350d6504001c3ae6a1aca08003075cd435941055f0f18286b2820abe1c3050d6504157c6e20a1aca082af8d44143594100043f43886b28200087d8710d650415547d0821aca080129da06725941001d3d404e4b28200087e8710965040010fb0e212ca0800297a0c42594100052ec1884b282004a768110965040014eb02212ca0800e9ea0042594100053cc0084b28200087e87cc965040010fb0f992ca080028fa1332594100051ec2664b282000e1d43cc96504001c3a86992ca080021fa1c32594100043ec3864b282000a3e840c9650400147b08192ca080129da0432594100053ac0864b282003a7a800c965040014f300192ca080021fa1f31594100043ec3e62b282000a3e84cc5650400147b0998aca080038750f31594100070ea1a62b282000c3f759d5640400153d063aac808002a760c75590105565d086e6b2020ab8bd879cd640400147d0b39ac8080028f61673590100064fc1ae6b2020abc9e305cd640415793860b9ac8082af2e84173590105545f438e6b202000a3e851cd640400147b0a39ac8080030fdcf53590100061eb9ea6b2020ace3a10d4d640400117d0f29ac8080022f61e535901056d1ec2ca6b202000c9d7394d640400193ae6a9ac808002aee01535901001d5c402a6b202000e1f8354d640400187ee6a9ac808003879cd53590100061eb9aa6b202000e1d7354d640400183ae6a9ac8080038ee01535901056f1c402a6b2020ade1f3054d640415bc3a60a9ac8082b78e84153590100045f438a6b2020008bd8714d640415947d0a29ac8080028fa1472590100051ec28e4b202000a9e831c9640400153b06392c808012ada0472590100355ac08e4b202003aba801c9640400d57300392c8080022fa1f32590100045ec3e64b202000a3e85cc9640400147
  | 3 => 0x6b122001c9c7350d6244001c3aa6a1ac488007331ce325891000c7643a64b122000e8d434c962440039a8e718ac4880063d21d31589100074aa1a62b122002cb87490162440051f10ea02c488007361ce30589100074ca1c60b1220018f8874c16244001cb2a6982c488003b44c5305891000477c3ac4312200887c855db52440138e8cb38ea48800e3d21971d49100045fc22eca9220028bc845d952440011bf06bb2a4880063720d76549100443f43ecaa922009c74659c452440071e90cb88a4880271d19571149100247c432e02922009c78655c052440018decb394a2881571b196729451000637b2ae528a2051c6c655ca51440134ed0db2ca2880031d9db65945102af3232ce528a2000ce6765ca51440a3cc8cab94a28810f1e1c3655451004e3a3b6eaa8a2000b6682dd551440878e8edb2aa2880271d1d865545100053b434a4a8a2009c747694951440138e8ec292a288002dc600525451021eb9ba8e0a8a2000bb1841c151440017a306382a2880269d21951145102263d380cb90a2000c78655c321440010ff0fb2c42880021f61f658851004c3fc38cb10a200087d871962144001878e9b2a42880030f1d065485100061fb2ee890a2000c3c65dd121440138e8cb38ea08810e5de1d51d411001d3a432a3a822000c77651c550440072e90ea8aa08800e9d219515411001db8402a2a822000975859c720440018e8cb38e40880031d19571c811004672312e3902200087f855d920440130f90abb240880022fe1176481100145e422ec90220008df835d920440031b906bb240880021fa1b75481100043f430ea902205c87e87d9520440bb0f90fb2a40881761fa1c654811004c3e438ca90220038f686dc520440878f4edb2e20880271e9d865c411004c3fc1ae73282009c5f835ce650415b8be60b9cca082b7174c1739941058e1fb9e873282000c3d73d0e65040130fd0f21cca080021f61e439941055d1ec24873282000c5d7390e65040018bae6a1cca0800387e0d43994105861fb9a8732820b0e1e7350e650400187ae6a1cca082c3875cd43994100060eb9a8732820abe1e3050e6504157c3860a1cca080261fa1c43994100043ec388732820aaa3e8410e65040130fd0e214ca080021f61c42994100052f418853282000a5d8310a65040094ed02214ca080029d604429941001d3d400853282000a798010a65040130fd0f994ca080021f61f32994100051f426653282000a3d84cca6504001c3a87994ca080038750d329941004c3f43865328200087d870ca650400147d08194ca080028f61032994100253b408653282000a75810ca65040074f500194ca080029e600329941004c3f43e63328200087d87cc6650400147d0998cca080028f61331994100070ea1e633282000e1d434c6650400587ce9aa2ca0800e1fa1
  | 4 => 0x54416187ee6a18ca882c3879cd43195100061eb9a8632a20b0e1d7350c654400183ae6a18ca882c38d9c543195105871ab8a8632a20b4e1e3050c6544169c3860a18ca880261fa1c43195100043ec388632a20b1a3e8410c65440130fd0e210ca880021f61c42195100052f4188432a2000a5d8310865440014ed02210ca880029d60442195102253d4008432a2000a798010865440130fd0f990ca880021f61f32195100051f4266432a2000a3d84cc865440018bae7990ca880038750f32195100062eb9a6432a2000e1d434c865440130fd0e190ca880021f61c32195100051f4206432a2000a3d840c865440014ed02190ca880029d60432195102253d4006432a2000a79800c865440130fd0e208ca880021f61c41195100052f4188232a2000a5d8310465440014dd04208ca880029b60841195102253d4008232a2000a798010465440130fd0f988ca880021f61f31195100051f4266232a2000a3d84cc46544001c3a87988ca88003175ce31195100070ea1a6232a2000a7b804c465440894f100988ca880261fa1c31195100043ec386232a2000a3e840c4654400147b08188ca88003175cc3119510005374106232a2000a6d820c465440894f500188ca880029e600311951004c3f43e8032a200087d87d0065440014bd07a00ca880029760f401951004c3f43e6032a200087d87cc0654400147d09980ca880028f61330195100062eb9e6032a2000c5d734c0654400193ee6a1ec488007271cd43d89100070ea9a87b122000e95434c76244005974e8a06c488003a650e30d89100072ca9a61b122000ed1314c362440010fd0fb2ac4880030f1d365589100062e39ecab12200087e871956244001878e832ac488003171cc65589100061fb2ee8b122000c3c65dd162440018becbb9ac4880031719773589100043ec1eeab122000c3f75dd16244001878ebba2c4880022f60f74589100043fc2ae8b12200987c855d162440011bf06ba2c4880063720d74589100061fba8e8b122000c3c751d162440018beebb9ac488003171d773589100064fba6e6b122000c9c74dcd62440018bf0bb9ac4880031721773589100064fc26e6b122000c9c84dcd62440010ff0ab9ac4880261f21573589100045fc22e6b1220028bc845cd62440018beea39ac488003171d473589100064fba0e6b122000c9c741cd62440010fd0fa9ac4880261f21f53589100061fba6a6b1220b3c3c74d4d62440018bee7a9ac488007171cf53589100043f43aa6b12200087c8754d624400187ee8a9ac4882cb0f1d153589100062fb9aa6b122001c5c7354d624400117d0fa1ac48800a2f21f43589100061fbae86b1220b1c3c75d0d624400193ee7a1ac488007271cf43589100045f43a86b1220008bc8750d624400187eeaa1ac4882c30f1d543589100064fb9a8
  | 5 => 0x80028f61273d95100062fc1ae7b2a2000a3e841cf654400147b0839eca880029ba0873d951000536c10e7b2a2000a76811cf65440874eb0239eca8810e9ea0073d95100053cc00e7b2a2000c3f73d0f654400187ae7a1eca880021fa1e43d95100043ec3c87b2a2000c5f7390f65440018bee6a1eca8800387e0d43d95100061fb9a87b2a2000e1f7350f654400183ee6a1eca880030f5cd43d95100070e39a87b2a20b5e1e3050f654416bc3860a1eca880021fa1c43d95100043ec3887b2a200087e8710b65440010fb0e216ca8800297a0c42d95100052ec1885b2a2000a768110b65440014eb02216ca8810e9ea0042d95100053cc0085b2a200087e87ccb65440010fb0f996ca880028fa1332d95100051ec2665b2a2000e1d43ccb6544001c3a86996ca880021fa1c32d95100043ec3865b2a2000a3e840cb654400147b08196ca880029da0432d95100053ac0865b2a2043a7a800cb65440014f300196ca880021fa1c41d95100043ec3883b2a2000a5e8310765440014bb0620eca880029ba0841d951000536c1083b2a2043a7a8010765440014f30020eca8810e1fa1f31d95100043ec3e63b2a2000a3e84cc7654400147b0998eca880038750f31d95100070ea1a63b2a200087e870c765440010fb0e18eca880028fa1031d95100051ec2063b2a2000a6e820c765440014db0418eca88003954c431d951021d3d40063b2a2000a79800c765440014dd05b86ca880029b60b70d95100043f43e81b2a200087d87d0365440014bd07a06ca880029760f40d95100043f43e61b2a200087d87cc3654400147d09986ca880028f61330d95100062fb9e61b2a2000c5f734c365440010ff0aba2ca880021fe1573595100047dc02e6b2a200087e87d4d65440030f90ea9aca8800317dcd53595100064fb9a86b2a2001c9c7350d6544001c3aa6a1aca880021fe1d65195100043ec1cec32a200087d8799065440014bd07320ca880029760e64195100043fc3ac832a200087e86dcc65440010ff0fb18ca88003175cf63195100043ec3cc632a2000a3e8498c654400147b09318ca880021fe1d63195100043ec38c632a2000a3e8418c654400147b08318ca88003175cc631951000537410c632a2000a6d8218c654400187ceda18ca880030f9d943195100068eb9a8632a2000e1f6350c6544001c38c6a18ca88003555ce31195102253a4326232a2000f15434c465440014f50d180ca88003c650e3019510006acb9a6032a2000f51314c065440130ff06b98ca8802717e0d73195102253d4068632a2000a7980d0c654416387ee7a18ca880030f5cf431951058f1b38e8632a20b1e3571d0c6544001c7501a18ca880038e603431951004c3f43c8632a200087d8790c654416147b09218ca88003175ce43195100062eb9a8632a2000e1f8350c6
  | 6 => 0x43ec3ea7b16200087f8754f62c40010fb0ea9ec5882c70f9d743d8b100061ebae87b1620b0c3e7550f62c400187aeaa1ec588007279cd43d8b100064eb9a87b162000e1d5350f62c4001d2a8698ec58800a2fa1f7458b100045ec1ee8b1620008be871d162c400153b063a2c5880022fe117358b100145e422e6b162000c3f74d4d62c4167878e9a9ac5880030fdd15358b105961e3a2a6b162000c5f7354d62c40038b8e6a9ac5880022fa1f4358b100145e43e86b1620008be8750d62c40011790ea1ac588007279cd4358b100064eb9a86b162000e1d5350d62c4005958e9212c5880123b21d4258b100247643a64b162000e8d434c962c4001d2a8698ac5880123be1d62d4b100267338ac5a96200487f8759652c40111f70cb84a5880022fe117654b100145e422eca962004a768694951c40016e301292a38810e1fe1d65d431021cbbc3aa3a8620039748754550c402d55908b1641881731b9887548310006363aac49062012aac8458920c40099c8e2b12418800e1f21d53596100062fb9aa6b2c2000c9f7350d6584003938e6a1acb080038754d43596100043ec1eeab14200087f855d162840130f90aba2c5080021fe157358a1004c3e42ae6b14200087e87d4d62840130f90fa9ac5080021fa1d5358a100043e43aa6b142000c3f75d0d6284163878eba1ac5080030fdd54358a105861e3aa86b142000c9f7350d6284003938e6a1ac5080038754d4358a1055f4d18286b1420038ee87d0962840014db0a212c508002b360c4258a1000572c0884b142003aea8010962840071d90e992c508003a350d3258a100075421280b142000e59534c162840134d90ab14a5080031dd967194a100447bc32e3294204987f855d952840071d90eb12a5080261f2157614a1004e3c32ae0294204487f8759751840018decb394a3081571b19672946102ad3642ac590c2051a6c855892184001958e8b1243080223ba0b74d951000476c16e9b2a2000c3d7495365440014f3012a6ca8800a1fe1d54d95100052f418a9b2a2000a5d83153654400147d0929eca880028f61253d951000c3fc3aa7b2a2000c5d7354f654400147d0829eca880028f61053d95100064fb9a87b2a2001c9c7350f6544001c3ca6a1eca880038754d43d95100052f41cc9b2a2000a5d8399365440018bae7b1eca880028fa1263d95100051ec24c7b2a2000a3e8418f654400147b0831eca88003175cc63d951000537410c7b2a2000a6d8218f6544001a3ee6a1eca8800387d8d43d95100070e31a87b2a2043a74864c76544001ca8c698eca88003c550d31d95100078ca1c61b2a2000d5b734c36544001ea262986ca880029ba0b74d951000536c16e9b2a2000a5e839d365440014bb073a6ca880030f5d074d951021d3d400e9b2a2000a79801d3654400147d0939eca8
  | 7 => 0x3d84cc065480018bae7980ca90003175cd301952004d37436cb2924000c6e76d9652480a38d8cab8ca4901271e1c3655492024e363b6caa924009c6c761955248093ad6ea382a49000327dcd43d852000e4e39a87b0a4000e1d5350f6148001d1a86996c290003a650e30d85200072ca9a61b0a400087e87d956148001878e9b2ac290003171cf65585200043f438cab0a4000c3c7419561480018b8e632ac2900030fd9774585200061e32ee8b0a4000c5f65dcd61480018b8cbb9ac2900023de1d611852000e2f39aa630a4000c5d7354c614800393ce6a18c290003275cd43185200070ea9a8630a400487c855db51480091d9053b4a2901771b9cb659452028e3632ae528a400987c851d951480094ed03b2aa2901271e1c36554520006363b4a4a8a4049d687094951480138d8cab90a2901563b21975c85202e637438cb90a4055c6d8719721480ab4df0632e42900029b60c65c852000717a18cb90a4000e2d4319721480abccd0232e42901579960465c852024c3f434eb10a404887c865d621480010fb0fb2c42900021f61c65885200061e3a6ca90a4000c3c74195214800187ecbba242900030f197744852028e3632eea90a40038ec865d5214802535908baa42901469ba1b654852024e363b6ca90a4000d2c74d9521480918d8ec32a42900034b1d0654852028e37438ca90a4051c6d871952148001c58e832a42901469be0c654852000536c18ca90a4000e2f431952148001c5a8632a42901731bdc465485202e733b88ca90a4000e66411952148001cca8232a4290003998c4654852000732988ca90a40129ae87dd12148001c58cbba2429000399197614852000733b28c290a4000e646518521480015cd0e30a429001339a1c614852002573c20c290a4000ae5841852148001d4ee830a4290003a91d0614852002573c18c290a4000ae5831852148001ccea630a42900039954c614852000753a18c290a4000ea5431852148001b50e9b8242901261fe1576541202ee36396caa82400387c8755165080070f90ea9aca1000317dcd535942000e4f39a86b284000c9d7350d6508001c3aa6a1aca10007279cd43984200064eb9a873084000e1d5350e6108001d2a8698cc210007279cd43584200064eb9a86b084000e1d5350d61080071e90ea0ac21000e3d21d31584200074aa1a62b0840048ed825da51080119cce4b0ca2102e31b9cb53d971000c3fc3aa7b2e2000c5d7354f65c416f8dce4a9ecb882db2b9cb43d971000e4f39a87b2e2000c9d7350f65c4001c3aa6a1ecb882bb2b9c943d971000637a9ae5b2e2000c6d535cb65c400195e86b96cb880032b50d72d97100243e43aa8b2e200487c8754d65c40018bee6a9acb88007279cd43597100064eb9a86b2e2000e1d5350d65c40010ff06baec5880261fe1f53d8b100
  | 8 => 0xe18eca900028fa1031d95200051ec2063b2a405da6e820c765480014db0418eca901269ea0031d95200053cc0063b2a405d87e87d0365480010fb0fa06ca9000297a0f40d95200052ec1e81b2a405d87e87cc365480010fb0f986ca900028fa1330d95200051ec2661b2a4000c5f73cc365480018bee6986ca900021fe1574595200043fc2ae6b2a400087e87d4d65480030f90ea9aca9000317dcd53595200064fb9a86b2a4001c9c7350d6548001c3aa6a1aca900021fe1d65195200043ec1cec32a400087d8799065480014bd07320ca900029760e64195200043fc3ac832a400087e86dcc65480010ff0fb18ca90003175cf63195200043ec3cc632a4000a3e8498c654800147b09318ca900021fe1d63195200043ec38c632a4000a3e8418c654800147b08318ca90003175cc63195200053b408c632a4000a758118c654800187ceda18ca900030f9d943195200068eb9a8632a4000e1f6350c6548001c38c6a18ca901229ba1b4219520004b6c388432a4000b4d8310865480016cb02210ca90122daa004219520006a6b9c6432a4048a6c864c86548001e1a86990ca90172daa0a40195202e53c4328032a4000f28425006548001e3287180ca901729e2193019520006acb9a6032a4000e58634c065480130ff06b98ca9002717e0d73195200062f192e632a4000c5c325cc65480914f501a18ca900029e603431952058e1fb9e8632a4000c3d73d0c6548163c5ce5a18ca902c78b5cb43195200071d4068632a4000e3980d0c65480130fd0f218ca900021f61e43195205851ec248632a4000c5d7390c65480018bae6a18ca900029be0943195202e5364128632a4000e1f8350c654816187ee6a18ca902c3879cd43195200061eb9a8632a40b0e1d7350c654800183ae6a18ca900038be094319520007164128632a40b0e2e7250c6548161c5ae4a18ca902e7878c143195205cf0e1828632a400987e8710c65480010fb0e218ca902c68fa10431952004c3f43e6432a400087d87cc8654800147d09990ca900028f61332195200070ea1e6432a4000e1d434c865480b94dd05208ca900029b60a411952004c3f4388232a400087d8710465480014bd06208ca900029760c41195202e5374108232a4000a6d8210465480914f500208ca900029e600411952004c3f43e6232a400087d87cc4654800147d09988ca900028f61331195200062eb9e6232a4000e1d43cc465480b94dd05188ca900029b60a31195200062eb9a6232a4000e1d434c465480130fd0e188ca900021f61c31195200051f4206232a4000a3d840c465480b94dd04188ca900029b60831195202453d4006232a4000a79800c465480130fd0fa00ca900021f61f40195200052f41e8032a4000a5d83d0065480130fd0f980ca900021f61f30195200051f4266032a4000a
  | 9 => 0x31592200055cc0062b24404887f87597528800393ce6a1cc310003275cd43986200070ea9a8730c4000e95434c6618800193ee6a1ac310007271cd43586200070ea9a86b0c40abe9a3050d61880071e90e98ac310003a550d31586200165d3a280b0c4000e59534c16188001da262982c31017b2b9c9649462000657322e528c4000cad645ca51880019cae4b0ca31000e3e201765462001e5d382c828c4000cb9645c0518800187cc93ac43100030f99175886200263b30aeb10c4000c3e75592218800187aeab24431000f2e9c164886200063abaac310c4000cb9645c2218800117b0dba243100022f21d64486202f75210ac890c40038ed82dd3654800187ae92a6ca900029e60254d95200143fc3aa9b2a4000a5e8315365480014bb062a6ca900028fa1253d95200051ec24a7b2a4000a6d8294f65480030ff0ea9eca90003175cd53d95200051f420a7b2a4000a3d8414f654800193ee6a1eca90007271cd43d95200070f29a87b2a4000e1d5350f65480014bd07326ca900029760e64d95200062eb9ec7b2a4000a3e8498f654800147b0931eca900028fa1063d95200051ec20c7b2a4000c5d7318f65480014ed0231eca900029d60463d95200068fb9a87b2a4000e1f6350f6548001c38c6a1eca901269ba1b42d952000717b2685b2a400096e8710b6548001c5ac8216ca90002d360c42d9520005b2c0885b2a4049b6a8010b65480934d90c996ca900039318d32d952000786a1a65b2a405db6a8290365480bb4f10ca06ca90003ca10940d95200078ca1c61b2a405da78864c36548001ab6e6986ca901769ba0b74d952024d36c16e9b2a4000a5e839d365480014bb073a6ca900030f5d074d952024d3d400e9b2a405da79801d3654800147d0939eca900028f61273d95200062fc1ae7b2a4000a3e841cf654800147b0839eca901769ba0873d952024d36c10e7b2a4000a76811cf65480014eb0239eca901269ea0073d95202ed3cc00e7b2a4000c3f73d0f654800187ae7a1eca900021fa1e43d95200043ec3c87b2a4000c5f7390f65480018bee6a1eca9000387e0d43d95200061fb9a87b2a4000e1f7350f654800183ee6a1eca900030f5cd43d95200070e39a87b2a40bae1e3050f6548175c3860a1eca900021fa1c43d95200043ec3887b2a405de2c4250b65480930fd0f996ca900021f61f32d95200051f42665b2a4000a3d84ccb6548001c3a87996ca900038750d32d95202ed3cc06e3b2a4000c77719c765480934db0438eca900021fa1c41d95200043ec3883b2a4000a5e8310765480014bb0620eca901769ba0841d952000536c1083b2a4049a7a8010765480014f30020eca900021fa1f31d95200043ec3e63b2a4000a3e84cc7654800147b0998eca900038750f31d95200070ea1a63b2a400087e870c765480010fb
  | 10 => 0x908a090cae62dd1211400117d0eb2242280022f21d64484500062fbaac6908a009c5c7558d211400193ee8b1a4228003271d1634845028f26292c6908a000c6f75589211400195ee8b1242280032b1d162484500065bba4c2908a000cb47498521140018eeeab0a42280271d1d561484500065bba2c2908a000cb47458521140a3cc8a4b0a422800e3b609760845001c7ac0aec108a000c5f7558c21140138b8eab1842280031ddd5610845004e3a3aac2108a0038ec825d165c80110f90eaa2cb900221f21d53597200062fb9aa6b2e4001c9e7350d65c800193ae6a1acb900038754d43597200247a40aeb30e400087f835d661c80098e902bacc3900131dc41759872004c3fc3ea730e400087d87d4e61c80010ff0ea9cc3900021f61d539872058e1f3ae8730e4000c3d75d0e61c816187ceaa1cc3900030f5d5439872000e4f39a8730e4000c9d7350e61c8001c3aa6a1cc390003a550d319872001c76412e8b0e4000c5f7354d61c80038b8e6a9ac390007279cd43587200064eb9a86b0e4000e1d5350d61c8001d1a86992c3900223d21d41587200457241282b0e40088f4874c561c8001d2a8698ac3900121f21576d47200053ac2cc3a8e4008ce67258751c80118dce4b2ca3900121f617765472001c77416eca8e4062c6e52dd951c80c70ff0eb28a3901463b61b754872028e3732eea90e40169ac845d521c817b35d0fba243901261fe1d65d432001c3e43aa6b2c4000c5f7354d658800193ee6a1acb10007271cd43596200070ea9a86b2c4000c3f759d5648800153d063aac910002a760c755922055c5ec3ce6b244000a3e859cd648800147b0b39ac91000eaea0273592205e55cc04e6b244000c9f835cd648815793c60b9ac9102af270c173592205545f438e6b244000a3e851cd648800147b0a39ac910003275cc73592200061fb9ea6b244000c3d73d4d648800117d0f29ac9100022f61e535922056d1ec2ca6b244000c9d7394d648800193ae6a9ac91000387e0d53592200061fb9aa6b244000e1e7354d648800187ae6a9ac910003875cd53592200060eb9aa6b2440ade1f3054d648815bc3a60a9ac9100022fa1c53592200045ec38a6b2440aca3e8514d648800147f0ab92c9100028f21572592205dd5dc02e4b2440008be87cc9648800117b0f992c9100028fa1732592200051ec2e64b244000c9d73cc9648800193ae6992c9100028fa1471592200051ec28e2b244000a9e831c5648800153b0638ac91017aaba08715922000556c10e2b244003aba801c564880295730038ac9100022fa1f31592200045ec3e62b244000a3e85cc5648800147b0b98ac910003275cf31592200064eb9a62b2440008be870c5648800117b0e18ac9100028fa1431592200051ec2862b24405eaae820c5648800155b0418ac91000eaea00
  | 11 => 0x1400156f08b92c228002ad211725845028f32292e4b08a009a74851c961140014ed0f292c2280029d61252584500053ac1ca4b08a000e37439496114001c6a87292c22802799a0a525845024d3bc04a4b08a049a75809496114093cce41292c22812799482525845004d3b42e84b08a000a7585d0961140014ef0b212c2280269d21642584500053bc2a84b08a009a748550961140011ed0e212c2280023d61c425845004d3b42884b08a000a758510961140015ad06212c228002b560c425845001d7940084b08a000af18010961140134ed0b992c2280029d61732584500055b42664b08a000ab584cc96114001d2a87992c2280029de16325845004d3a42c64b08a000a77854c961140134e90a992c228003a550d32584500047b43864b08a0008f5870c961140134ed0a192c2280029d61432584500055b42064b08a000ab5840c961140075e500192c228002bc600325845004e3b38aed288a00087f835da51140010fb06bb4a2280030fd0d76944500061ea1aed288a000c6e825da51140018db04bb4a2280271da05769445004e3ac0aed288a068c5e8758e51140018bb0eb1ca22800387a1163944500070ec22c7288a000c5f7458e51140018bae8b1ca228003179c9639445004e2f38ac7288a009e567158e51140878bee0b1ca22810f175c1639445021f2b882c7288a043e551058e51140018daed394a2280039358e72944502e4b7c34e5288a05596d869ca51140aba5cc9394a2281574b59272944502ae37b1ce5288a055d4e639ca51140018dac7394a2281575358e729445000626b1ce5288a000d2f439ca5114001a5a87394a2281575998672944502aeb2b0ce5288a05cd6a809ca51140b9ad301394a2281771b98272944502aeb5304e5288a000c6d765ca5114001c9ac6b94a2280031b9c961944500063bba2c3288a000c757458651140018eee6b0ca2280031d5cd61944500071ba1ac3288a000e354358651140018ece4b0ca228003999c9619445000633392c3288a000e657258651140878eee0b0ca22810f1d5c161944502e4b6412eb908a008c6e625d7211401387ceab2642280030f5d564c845001e5d382c9908a009c5e7558f21140018baeab1e42281579314963c845001e6d382c7908a009c767558721140018eaeab0e42281579914961c845001e79382c3908a000cb9645c321140019b2c6b8642280233a98970c845000678b0ae1908a00487d855da211400187cc8bac42280031798d758845031637312eb108a004c76615d6211401387ceab2442280030f5d5648845004e2f3aac7108a000c5d7558e21140138dceab1442280031b5d5628845004e3b3aac3108a000c7575586211400517909bb2422800e3b20b764845001c7a40eec908a0008bf845d9211400517908bb242280022f61b74484500064f31ee8
  | 12 => 0x123da1c32984500047ac3865308a009a76850ca61140014eb0a194c228002ada1032984500055ac2065308a003af2800ca61140015e300194c2280261f21574584500053a40aa8b08a00987c855cd61140014e902a9ac2282c78d147435845000e4f39a86b08a000c9d7350d6114001c3aa6a1ac2282c38d14543584500053b40ca4b08a0038f687d0561140134ed0ba0ac2280269d216415845001c7a43a82b08a009a748550561140134ed0a20ac228002b5a0c41584500056ac1882b08a000ae68210561140015cb0420ac22800ebca00415845001c7b43e62b08a009a7685cc5611400156d0998ac228002ad61331584500074aa1e62b08a009a74858c561140071e90e98ac2280269d21531584500074aa1a62b08a009a76850c5611400156d0818ac228002ad61031584500057341062b08a000ae5820c561140075e50018ac2280269d217745845004d3b42ce8b08a000a75859d161140014ef0aba2c2280269d215745845004d3b428e8b08a000a75851d161140015ad063a2c228002b560c745845000573410e8b08a000ae5821d161140075e5003a2c228002bc60074584500053a43aa8b08a009a77845516114013c6f08aa2c2280029de0d54584500053a412a8b08a0bea7780551611417d4eb00aa2c2282fb8dd0154584505f71aa02a8b08a009a7485dcd61140134ed0b39ac2280029d61673584500055b424e6b08a000ab5849cd61140014ef0ab9ac2280269d215735845000579c02e6b08a003af0805cd61140134ed0a39ac2280029d61473584500055b420e6b08a000ab5841cd61140015cd0439ac228002b9608735845001d79400e6b08a000af1801cd61140014e90ea9ac2280029de11535845004d3bc1aa6b08a009e578354d61140014e904a9ac2282b69de01535845056d3ac02a6b08a0ade573054d611415bcaa60a9ac2280269da1743584500053ac2e86b08a0b1e3754d0d6114001c6aa9a1ac22800ebca03435845000578c0686b08a0b1e3685d0d6114001c6b0ba1ac2282c78dd4f43584500071aa9e86b08a0b1e3452d0d6114155d6501a1ac228003ac60343584505571ba8686b08a0aae3550d0d61140134ed0b21ac2280029d616435845055d5ac2486b08a000e555390d61140134ed0aa1ac2280029d61543584505871baa286b08a000e355450d6114001caaa6a1ac2282c38da1543584500071ac2a86b08a000e978350d6114001d2ce6a1ac228003a55cd43584505871ba9a86b08a0b0e965350d6114001c6aa6a1ac2282c3a554d43584500070aa9a86b08a0b0e345250d6114157c6ea0a1ac2282af8d541435845055f4b18286b08a0abe943050d61140134ed0a21ac2280029d61443584505555b42086b08a009a7685dc961140134ed0b392c2281579914a725845001d79404e4b08a009a74855c961
  | 13 => 0xf17aa686b10a000e2d54d0d62140075d501a1ac428002ba603435885058f1742e86b10a000e2d85d0d6214163c5ea7a1ac4280038b54f43588505575540686b10a000ea980d0d62140134dd0b21ac4280029b616435885055d56c2486b10a000e4d5390d62140134dd0aa1ac4280029b615435885058717aa286b10a000e2d5450d6214001c9aa6a1ac4282c38ba15435885000716c2a86b10a000e8f8350d6214001d1ce6a1ac428003a35cd435885058717a9a86b10a0b0e8e5350d6214001c5aa6a1ac4282c3a354d435885000706a9a86b10a0abe8e3050d6214157d1860a1ac4280269ba14435885000536c2886b10a0aaaae8410d62140ab8d8ebb8ac4280269ba16715885004d3642ae2b10a000aaf845c5621400155908b8ac4280269ba17415885000536c2e82b10a0008ee8710562140011db0e20ac4280269ba14415885000536c2882b10a000ace83105621400159b0620ac42800ebaa00415885000574c0082b10a009a6e85cc562140014db0b98ac428002aba13315885000556c2662b10a000e8d43cc56214001d1a8698ac4280023ba1c315885000476c3862b10a009a6e850c562140014db0a18ac428002aba10315885000556c2062b10a003aea800c562140015d30018ac4281af17a1d63948500062ec3ac7290a000e1e8458e5214001c3b08b1ca42800317dd163948500062eba2c7290a009c5e7258e5214013c9ce4b1ca42812717dc1639485024e2eb82c7290a049e4f2058e5214093c9a40b1ca4281731bdd1629485000636ba2c5290a05cc6f7358a52140018dae6b14a4280038bd0d629485000716a1ac5290a000c5d639c652140071e902ba4c22800e3d205739845000e4f39a87308a000c9d7350e6114001c3aa6a1cc2280022fe1172984500145e422e5308a0038f4815ca61140134ed0b98cc228002ada1331984500055ac2663308a000e9543cc66114001d2a8698cc2280269da1673984500053ac2ce7308a000ab6849ce611400156b0939cc2280269de0d539845004f2bc1aa7308a0ade573054e611415bcaa60a9cc2282c78dd4f43984500071aa9e87308a009a768590e61140014eb0b21cc2282aead61243984500072aa9c87308a000e555350e6114001d2f06a1cc228003a59cd43984500074ab9a87308a0b0e375350e6114161d2ca6a1cc2280038d54d43984505874aa9a87308a000e155350e6114157d2c60a1cc2282afa50c1439845004d3b42887308a000a758510e611415556d0821cc228002ade1172984500055a422e5308a0048f68710a61140011eb0e214c2280269da1442984500053ac2885308a000ad68310a61140015ab06214c22800ebca00429845000578c0085308a009a7685cca61140014eb0b994c228002ada1332984500055ac2665308a000e9543cca6114001d2a86994c228
  | 14 => 0x8805c563140134bd0a38ac62805e976147158c500054f420e2b18a000a9d841c5631400159d0438ac628002b36087158c5001d6d400e2b18a017ad9801c563140134bd0ba0ac628002976174158c5004d2e42c82b18a000a5f8550563140134b90aa0ac62800237a1c4158c500046ec3882b18a009a5e8510563140014bb0a20ac628002b3a084158c5000566c1082b18a003ada8010563140015b30020ac6280269be0d539885004f27c1aa7310a0ade4f3054e621415bc9a60a9cc4282c78bd4f439885000716a9e87310a009a6e8590e62140014db0b21cc4282aeab612439885000726a9c87310a000e4d5350e6214001d1f06a1cc4282bba39cd439885057746b9a87310a0b0e2f5350e6214161d1ca6a1cc4280038b54d439885058746a9a87310a000e0d5350e6214157d1c60a1cc4282afa30c1439885004d3742887310a000a6d8510e621415555d0821cc4280223ba1c419885000476c3883310a009a6e8510662140014db0a20cc428002b3a0c419885000566c1883310a003aea8010662140015d30020cc4280269ba17319885000536c2e63310a000aae84cc6621400155b0998cc428003a350f319885000746a1a63310a0088ee870c662140011db0e18cc4280269ba14319885000536c2863310a000aae840c6621400155b0818cc42800ebaa00319885000574c0063310a00987c855d162140b90f90eaa2c4280261f21573588502e43e43aa6b10a001c9e7350d621400193ae6a1ac4280038754d435885001c7743e84b10a009a6e85d0962140071d90ea12c4280269ba1442588500056741884b10a000acd8310962140015cd02212c428002b9604425885001d7540084b10a0038ee87cc962140134dd0b992c428002aba13325885000556c2664b10a000e8d43cc962140071d90e992c428003a350d325885004d3742864b10a000aae840c9621400155b08192c428002b9a04325885000572c0864b10a003aea800c962140134d90bba2c4280269ba16745885000536c2ce8b10a000a6f855d162140134d90aba2c4280269ba14745885000536c28e8b10a000ace831d1621400159b063a2c428002b9a04745885000572c08e8b10a003aea801d162140015d3003a2c4280029b21d545885004d37c22a8b10a009e2f8455162140014df06aa2c4282fb8bd0154588505f716a02a8b10a009a6c85dcd62140134dd0b39ac4280029b616735885000557424e6b10a000aad849cd62140014df0ab9ac4280269b215735885004d37428e6b10a000a6d851cd621400155d0839ac428002ab610735885000573408e6b10a000ae5811cd62140075d50039ac428002ba60073588500053643aa6b10a000a6f8454d62140134df06a9ac42802793e0d535885056f27982a6b10a0ade4d3054d62140134dd0ba1ac4280029b617435885058
  | 15 => 0xab92c8280268f215725905004d1f428e4b20a018a3d851c9641400153d06392c828002a760c72590500055b408e4b20a000ab5811c9641400757500392c828062ae60072590500045f43e64b20a0008bd87cc9641401347d0b992c8280028f61732590500064eb9e64b20a000c9d734c9641400117d0e192c8280022f61c325905004d1f42864b20a000a3d850c9641400156d02192c828002ad604325905001d5d40064b20a000ab9800c964140d347f0ab8ac8280268f215715905004d1f428e2b20a018a3d851c5641400153d0638ac828002a760c715905000557410e2b20a000aad821c564140075750038ac828062ae60071590500045f43e62b20a0008bd87cc5641401347d0b98ac8280028f61731590500064eb9e62b20a000c9d734c5641400117d0e18ac8280022f61c315905004d1f42862b20a000a3d850c5641400155d0418ac828002ab608315905001d5d40062b20a000ab9800c564140134bd0bba2c62805e976177458c500062ebaee8b18a009a5e859d163141814bb0b3a2c6282c787d527458c5001d6d404e8b18a0c1ad9809d1631415753b0f3a2c6282c787a167458c500070ec2ce8b18a0b1e1e759d16314001c3aeb3a2c6282c78714a7458c5058f0e28ce8b18a0aae9a809d16314001d33013a2c6282ab87d427458c505570ea84e8b18a009a5e855d163140018baeaba2c6282c387d517458c500064fc3ae8b18a0b0e1e855d16314001c3b0aba2c6282c327dd57458c505870f3aae8b18a0b0c9d755d16314001c3aeaba2c628003075d57458c505870e292e8b18a0b0e1c515d1631415793ce0ba2c6282af271c17458c5055f0fa82e8b18a0abe1d505d163140134bd0a3a2c62805e976147458c505554f420e8b18a000a5f8755163141814bb0eaa2c62802697e115458c5004f0fc22a8b18a000e1e745516314001c3ae8aa2c628002972095458c500052e40aa8b18a0bea5f80551631417d4bb00aa2c6282fb87d015458c505f70ea02a8b18a009a5e85dc9631402f4bb0bb92c628002a7a137258c500054ec26e4b18a000c9d74dc963140134b90b392c6281ae97e157258c5004d2e42ae4b18a000c9d745c963140134bd0a392c62805e976147258c500054f420e4b18a000a9d841c963140015ad02392c628002b56047258c5001d6d400e4b18a017ad9801c963140134bd0ba12c628002976174258c5004d2e42c84b18a000a5f8550963140134b90aa12c62800237a1c4258c500046ec3884b18a009a5e8510963140014bb0a212c628002b5a044258c500056ac0884b18a003ada8010963140015b300212c62802697a177158c500bd2ec2ee2b18a000a9e84dc5631400153b09b8ac628003275d37158c5004d2e42ce2b18a068a5f855c563140134b90ab8ac628003275d17158c505fd6dc02e2b18a003ad
  | 16 => 0x1484210043ec1eeab004200a5d831d560084071db05ba2c0108021fe15745802104c3e42ae8b00420087f855cd60084130f90ab9ac0108021fa1f535802104c3e43ea6b00420087e8754d60084010f90ea9ac010807179cd53580210062eb9aa6b004200c3f75d0d6008563878eba1ac0108030fdd543580215861e3aa86b004200c9f7350d6008403938e6a1ac0108038754d435802128e363aa42b004204ee01048560084115d505202c0108123e21d40580210074ca1c60b0042048f8874c16008401cb2a6982c01080317dcd5358b5000e4f39a86b16a000c9d7350d62d4001c3aa6a1ac5a8003175cd53987505be37392a730ea0b6cae72d0e61d400393ce6a1cc3a8003275cd43987500070ea9a8730ea0aecae7250e61d40a38dea6b94c3a80031b54d729875000657a1ae530ea000cad435ca61d40018bee6a9ac3a8007279cd43587500064eb9a86b0ea000e1d5350d61d40c54dd05bb2a3a80123b20976c875002476c16ec90ea0008bf845d921d400517908bb243a81721fe1975087502ec3f43ea8b14a05da6c8255162940bb0fd0fa9ac52800327dcd4358a5000e4e39a86b14a000e1d5350d62940014db0ba12c5280029b6144258a5000566c1884b14a000ae58110962940075d500212c52800e3b21d3258a5000746a1a64b14a00087d869c6529400393ce6a1cc328003275cd43986500070ea9a8730ca0008bf845ca619400517908b94c328003a550d31986500064fb9a86b0ca001c9c7350d6194001c3aa6a1ac32800e3d21d31586500074aa1a62b0ca000d6a709ca51940018dec7394a3280031b58e729465000697a1ce528ca000d2d439ca51940018dce4b0ca3280022fe1176486500145e422ec90ca0008df835d921940031b906bb243280032b1d162486500257240ac490ca009978855c0219400193ee6a1ec4a8007271cd43d89500070ea9a87b12a05dc77659c662540019cec4b8cc4a802339189719895000477c3ac4312a000c9f7350f6154003938e6a1ec2a80038754d43d85502ee37b2ce530aa004ce4615ca61540019cae5b0cc2a80023de1d61185500062eb9ea630aa001c9e7350c615400193ae6a18c2a80038754d43185500043fc1ceda8aa00087d839db515400187e873b6a2a80030f50e76d45500267230ae528aa000ce572d8651540091d904bb642a80121f21676885500063abaec310aa0028be849d9215400117b093b242a82c70fd4f735905055c5ec3ce6b20a009a3e859cd641418547b0b39ac82800327e0d73590505861fa9ae6b20a0abc9e305cd641415793860b9ac8282aa2fa1c735905004d1f428e6b20a018a3d851cd641401347f06a9ac82802787e0d53590500061fb9aa6b20a000e1e7354d641400187ae6a9ac828003875cd535905056f0f982a6b20a0ade1d3054d64140d947f0
  | 17 => 0x224200e1f8354f644840187ee6a9ec89080387dcd53d91210060fb9aa7b224200c3d7354f6448401c38e6a9ec8908022fa1c53d91210045ec38a7b2242c3a3e8514f644840147d0bb96c8908028f61772d912141d5b40ee5b2242008be87ccb644840117b0f996c8908028fa1732d91210051ec2e65b224200c9f73ccb644840193ee6996c890a422fa1f31d91210045ec3e63b224200a3e85cc7644840147b0b98ec89080327dcf31d91210064fb9a63b2242008be870c7644844717b0e18ec8908028fa1431d91210051ec2863b224290aae820c7644840155b0418ec890802aea0031d91210055cc0063b224200a3f855c364484014790ab86c890802a7e0d70d91210054e41ae1b224290aae821c3644840155b04386c8908022fa1f30d91210045ec3e61b224200a3e85cc3644840147b0b986c8908038754f30d91210064fb9c61b224200e1d534c3644840117d0e186c8908022f61c30d91210051f42861b224200a3d850c3644840193ee6186c890a42aba0830d912100556c1061b224200ab6810c3644840156b02186c89098a1f61f65d4921316b2292e3a924251c6f539db52484018daa73b6a4908032bd0e76d492100656a1ceda924200e2f65d9352484013cd0d38ea49081339a1a71d4921024f3c24e3a9242009e5849c75248401b4ec938ea4908036919271d4921024f3c1ce3a9242009e5839c752484a3acea738ea4908035954e71d4921006d3a1ce3a924200da5439c752484012df0eb28a49098ed9e056514921024f240ae02924251d68505c052484092d90ab96a290a432b9cb649452100657b22e528a4200cac645ca51484093c902b94a2908022fe1176545210145e422eca8a4200c3c649d62148401878c8bac42908135908575885210061f3aec910a4200c3d75d922148401a58c93ac42909465be0e7588521004b6c1ceb10a4200d2f439d62148401a5a873ac42908131bd86758852131eb3b0ceb10a4204d66419d62148401aca833ac4290813598c67588521006b298ceb10a4200d2e75d92214840153b06326c09080e3b20974d81210062fb9aa7b024201c5c7354f604840393ce6a1ec090803275cd43d81210070ea9a87b024200e8d434cb6048401d2a8698ec090802a760c64981210145f436e8b0242908bc86dd1604840117d0fb22c0908030fdd764581210061e3aec8b024200c9c73d91604840117d0e322c0908030fdd464581210061e3a8c8b024200a9d831916048401938e6322c09080327d9373581210064e326e6b024200a9d8319060484011f70eb00c0908121f21d54594210243e43aa6b284200c5f7354d650840393ce6a1aca10803275cd43594210070ea9a86b284200cac74dd921084018dea7bb242108031b54f764842100657a1eec9084200cad43dd9210840195eedba24210813991955
  | 18 => 0x84014bd06382cb108029760c705962100536c10e0b2c4204a76811c165884010fd0fa02cb108021f61f40596210052f41e80b2c4200a5d83d0165884c54dd05202cb108029b60a40596210253b40880b2c4200a758110165884010fd0f982cb108021f61f30596210051f42660b2c4200a3d84cc165884018bae7982cb108038750e30596210062eb9a60b2c420087e870c165884010fb0e182cb108028fa1030596210051ec2060b2c4200e1d430c165884c54dd04182cb108029b60830596210253b40860b2c4200a75810c165884138eccab8ea5108031d5977154a210253a40acaa8c4255a6f8399721884014db0732e43108038bd0e65c862100716a1ccb90c4200c9f7350d6088403938e6a1ac1108038754d43582210074aa1a62b044200ae98290160884091f10ea02c110803a650e30582210247c43a60b044200e59534c16088401da262982c110802a760c64d952102476c16e9b2a42048ed82dcf65484030ff0ea9eca90803175cd53d952100e4f39a87b2a4200c9d7350f6548401c3aa6a1eca90802a760c64995210064f398c932a4200c5f655ce65484138b8cab9cca9080327191739952128ea6292e732a4200a9d83191654840117b07ba2ca90802a760c74595210161e3a6a8b2a420287c87551654840117f08b9aca9080a2f21173595210047dc02e6b2a42038f8805cd654840187ee9a9aca90acf0f1d3535952100c3e43aa6b2a4200c3f7454d6548565878e8a9aca9080317dcd535952100e2e39aa6b2a42008be87d0d65484051790fa1aca908022fa1d43595210045e43a86b2a4201c9e7350d654840193ae6a1aca908038754d43595210043fc3aca32a4200a9d83190654840117b0f32ec890802a7a0e65d91210054ec1ccbb2242008bf87597644840117d0db9ec89080a2fe1f63d91210064eb9ec7b2242008bd8798f644840147d0b31ec8908028f61663d91210064fb9cc7b2242008bf8758f644840193ee6b1ec89088e2f61c63d91210051f428c7b224200a3d8518f644840193ae631ec890802aea0063d91210055cc00c7b2242b3c3e76d4f644856587ceca9ec89080347dcd53d91210070fb1aa7b224200e1c6354f644844755d0db96c890802cba1772d9121006c7b9a65b224290ab4864c76448401b2ee698ec890a42aba0b75d912100556c16ebb224200a9e839d7644840153b073aec8908030f5d475d91210045ec3ce7b224200a3e859cf644840147b0b39ec89080327dce73d91210064fc1ae7b2242008be871cf644840147d0a39ec8908028f61473d912148557410e7b224200aad821cf644858b56d0239ec890a42ad60473d91210055d400e7b224200ab9801cf644840187ee7a9ec8908030f5cf53d91210045f43ca7b2242008bd8794f644858947b0b29ec89080327dce53d91210064fb9aa7b
  | 19 => 0x3555cd31996210078aa1a6332c4209c5f835ce65884018bc64b9ccb10803170c9739962158e1fb9e8732c4200c3d73d0e65884130fd0f21ccb108021f61e43996210062eb9c8732c4200c5d7350e65884014df04a1ccb1098e9b20943996210070fc1a8732c42b0c3f7350e6588561c3ce6a1ccb108030f5cd43996215870eb9a8732c4200c1d7350e6588401c5f04a1ccb108038b209439962104c3f4388732c420087d8710e65884130fd0f994cb108021f61f32996210051f4266532c4200a3d84cca6588401c3a87994cb108038750d329962104c3f43e6332c420087d87cc6658840147d0998ccb108028f61331996210062eb9e6332c4200e1d43cc665884018bae698ccb108038750d319962104c3f43e8132c420087d87d0265884014bd07a04cb108029760f409962131d374148132c4200a6d8290265884130fd0f984cb108021f61f30996210051f4266132c4200a3d84cc265884018bae7984cb108038750e30996210062eb9a6132c420987e870c265884010fb0e184cb108028fa1030996210051ec206132c4200e1d430c265884c74dd04184cb108029b60830996210253b4086132c4200a75810c265884090fd0f2a2cb108030fdd254596210243e43aa8b2c4200a5e8315165884014bb062a2cb108121fa1e53596210051f424a6b2c4200a3d8494d65884090f90ea9acb1080317dcd53596210043f438a6b2c4200a3e8414d658840147b0829acb10807279cd43596210064eb9a86b2c4200e1e5350d6588401c3aa6a1acb108129da0664596210271b20cc8b2c420087f865cd65884010fd0f31acb108028fa1263596210051ec24c6b2c4200c5f7398d65884094ed0331acb108261fa1d63596210062fb9ac6b2c42b1c3f76d0d658856187eeca1acb10803475cd43596210070f31a86b2c4200e1d6350d6588401e2a8698acb108030fdd274596210253b40ce8b2c4200a75819d165884014bd063a2cb108029760c74596210043ec3ce6b2c4200a3e849cd658840147b0939acb108129da0673596210053ac0ce6b2c4200c5f835cd65884010fd0e39acb108028fa1073596210051ec20e6b2c4200c3f73d0d658840187ae7a1acb108021fa1e43596210043ec3c86b2c4200a3d8490d65884018bae721acb10803175cd43596210070fc1a86b2c4200c3f7350d6588401c3ce6a1acb108030f5cd43596210070eb9a86b2c4200c1d7350d65884010fd0e21acb108021f61c43596210051f42086b2c4200a3f845c9658840147908b92cb108021fa1f32596210043ec3e64b2c4200a3e84cc9658840147b09992cb108038750f32596210070ea1a64b2c420087e87cc565884010fb0f98acb108028fa1331596210051ec2662b2c4200e1d43cc56588401c3a8698acb108129d20570596210051f420e0b2c4200a3d841c1658
  | 20 => 0x46a1c60b14a200e4d534c162944011dd0e182c5288023b61c3058a5128d3742860b14a200a6d850c1629440155d08182c528802ab6103058a5100746a1860b14a204ae6810c162944015cb02182c528823399897194a5100672b16e2a94a255c6f7398b51944018dae7316a3288038bd0e62d465100716a1cc5a8ca200c6e7098b51944099cce3314c128813399c5629825104477416e8b04a2008ed82dd160944870fd0fa9ac128803175cd53582510064fb9a86b04a201c9c7350d6094401c3aa6a1ac12890e1fa1f515825121d3d406a2b04a2048f8875016094401d3287182c1288123e21d30582510072ca9a60b04a26287d87d5362544c50fb0fa9ec4a8807279cd43d89510064eb9a87b12a200e1d5350f62544011df0eb10c4a89463b61f6294951316b2292e3292a200976869c652544098ed0d38ca4a88031dd8e71949510063ab1ce3292a200d37439c65254401a6a8738ca4a88025d60271949510063a304e3292a20087c865c252544938f0c0b84a4a88025be1d62149512adb3c0ac4292a24887c865c052544918f0c0b80a4a881359145729455100637b1ce528aa200c6d639ca5154401a5e87394a2a88034b50e72945512aeb3b0ce528aa200c6c609ca5154409ace21394a2a88261f219709455121e3c302e128aa204d73105c251544018bee6a9ec0a8807279cd43d81510064eb9a87b02a200e1d5350f605440117f08b96c0a880a2f21172d81510072ca9e61b02a200a79850c36054401d3286186c0a8802ba60830d815100578c0861b02a243c5f655cc60544011f70eb00c0a880317dcd535885100e4f39a86b10a200c9d7350d6214401c3aa6a1ac4288123b21d42588510247643a64b10a200e8d434c962144010ff07bb2a2288021f60f76544510061fa1eeca88a200c3d43dd951144890f90ea9ac02880327dcd435805100e4e39a86b00a200e1d5350d60144890f90ea8ac0289129e201515805102739882a2b00a200ae98290160144091f10ea02c028803a650e30580510247c43a60b00a200e59534c160144091d904ba2cb908221f21d545972102476412e6b2e42b8c6c72d4d65c84110f90ea9acb9080317dcd53597215be36392a6b2e42b6cac72d0d65c840393ce6a1acb90803275cd43597210070ea9a86b2e42aecac7250d65c84094d904b2ea3908129b20965547210064fb9a86b064201c9c7350d60c8401c3aa6a1ac190803a350d32583210457541480b0642088f88750160c8401d3287182c1908223e21d30583210072ca9a60b06420187f8754f65884018bae6a9ecb10807279cd43d96210064eb9a87b2c4200e1d5350f65884094ed03324cb108028fa1263996210051ec24c732c4200c5d7398e65884094ed0331ccb10803175cd63996210068eb9a8732c4200e1e6350e6588401c3ac6a1ccb108
  | 21 => 0x7350e629455dd1ae6a1cc5288038bd4d4398a510074729a87314a200e2d5350e6294401d1aa6a1cc5288038354d4398a512ad3742887314a200a6d8510e62944ab4dd0b98cc5288029b6173198a510055742663314a200aad84cc66294401d1a8798cc528803a350d3198a512ad3742e81314a200a6d85d02629440159d07a04c528802b360f4098a510447743c81314a2008ed8790262944014df0aa04c5289569b2154098a512ad3742e61314a200a6d85cc2629440155d09984c528802ab6133098a5100726a9e61314a200e8d438c262944014df0a984c5289569b2153098a5100726a9a61314a2088ee870c262944011db0e184c5289569ba143098a5100536c2861314a200aae840c2629440155b08184c528803a350c3098a510257340861314a200ae5810c2629440393ce6a1ac528803275cd4358a510070ea9a86b14a2048ec8750962944014db0a212c528802b3a0c4258a5100566c1884b14a204ae68110962944015d500212c528802ba6004258a5100536c2e64b14a200aae84cc9629440155b09992c528803a350f3258a510247643a64b14a200e8d434c962944014db0a192c528802aba103258a5100556c2064b14a204ae6810c962944015d500192c528802ba6003258a5100557424c6b14a200aad8498d6294401c9cc6a9ac5288039358d5358a510074731a86b14a200e8d6350d6294401e1aa6a1ac528802abe117558a5100556422eab14a251a6e851d162944014db0a3a2c528802b3a0c7458a5100566c18e8b14a204ae6811d162944015cb023a2c528802baa007458a5100574c00e8b14a251e2f5495162944095cd032a2c528802b96065458a5128d3742ce6b14a200a6d859cd629440155d0939ac528802ab6127358a5128d37428e6b14a200a6d851cd629440155d0839ac528802ab6107358a5102573408e6b14a200ae5811cd62944015d50039ac528802ba6007358a5100557424a6b14a200aad8494d62944095cd0329ac528802b96065358a5128f27c1aa6b14a200e2f53d0d6294401c5aa7a1ac5289469ba164358a5100536c2c86b14a200e4d5390d6294401c9aa6a1ac528803a3e0d4358a510074739a86b14a200e8d7350d6294401c5ea6a1ac528803a394d4358a5100716a9a86b14a200e8d5350d6294401c1aa6a1ac5289469ba144358a5100536c2886b14a251a6e85cc562944014db0b98ac528802aba133158a5100556c2662b14a200e8d43cc56294401d1a8698ac528802aba127058a5100556c24e0b14a204ae6819c162944014df0ab82c5289469ba174058a5100536c2e80b14a200ace83d01629440159b07a02c5288023ba1e4058a5100476c3c80b14a204ae68110162944015cb02202c5289469ba173058a5100536c2e60b14a200aae84cc1629440155b09982c5288039354f3058a51007
  | 22 => 0x1e01000a00402203200002000001202400000603c00600600200200000000200600202c01200000401400200200a00805203801a00800c00800400a02200400800001e00601201000201000800200600000402e00a04800000000c00602800000800000200600000200200601e00204e00004c00004000201e03000200200000601c03c01202601801401407a00603c07000001000c00000400000004e00005001e00000800001600a03800e00400600003801a01402003602801200200400200201600200000200400e00000601200000401c00a00c02001001c02600000600000009200005802c00200000007800000000c00e00400001200000002000c5d7354e61d480393ce6a1cc3a9003275cd43987520070ea9a8730ea401c9e7350d61d480193ae6a1ac3a90038754d43587520064fb9a86b06a401c9c7350d60d4801c3aa6a1ac1a90029d607539865200e4f39a8730ca400c9d7350e6194801c3aa6a1cc329003a550d319865200e4f39a86b0ca400c9d7350d6194801c3aa6a1ac3290223d21d41586520447a43a62b0ca400e95434c561948930fd0fa9ac129003175cd53582520064fb9a86b04a401c9c7350d6094801c3aa6a1ac129022baa0a40582520447c43a80b04a400e99438c160948111f10e982c1290039654d305825200e4f39a87b0aa400c9d7350f6154801c3aa6a1ec2a90023de1d611855200e4f39a8630aa400c9d7350c6154801c3aa6a18c2a900317dcd53d815200e4f39a87b02a400c9d7350f6054801c3aa6a1ec0a90023ee1d601815200e4f39a87308a400c9d7350e6114801c3aa6a1cc229003a550d31984520062fb9aa6b08a401c9e7350d611480193ae6a1ac2290038754d43584520447a43a82b08a4088f4874c56114801d2a8698ac2291221f21d53580522453c402a6b00a4b1e3850d0d601480193ee6a1ac029007271cd43580520070ea9a86b00a4b0e385050d60148115d505202c0290223e21d405805204d3c42a80b00a409a78858c16014801d3287182c0290223e21d305805204d3c42a60b00a400e59534c160148090f90aba2c5a898e1f21d5458b510243e42ae6b16a26387c8754d62d440393ce6a1ac5a8803275cd4358b510070ea9a86b16a24987f865c252d440193ee6a1ac1a8807271cd43583510070ea9a86b06a2028be84dc960d440117b09b92c1a8802aba126398a5100556c24c7314a200a6d86d4e6294401c9ac6a9cc528803a398d4398a5100746b1a87314a200f0d5350e62944abc5ea92a4c5288029b6075398a5100537406a7314a200aae8494e629440155b0929cc52895793e0d5398a5100537c0aa7314a200a6c8054e6294401c5ea7a1cc5288038b54f4398a512ad3742c87314a200a6d8590e6294401c9aa721cc5288039354d4398a5100747c1a87314a2aee8e
  | 23 => 0x409001400000401000000200200200e00800000401800001005801000002400001200201200400e00400600e00800002600405a00800800400000000400202201800e00200000400000001a00e01a00200001000200400800000000402802001600a00408004800000000200800200802200600002400e00201000e00000400000002c00000400400000e00800000000200c00201200000000000000000001401407200002200002200000000001a00800002a01600200c00400000003800003000202a00a03201600200e00002400e01c08a00e00a01e04800202800400004e00000000000000e00001200a02e01800200c00800001400803000e00001c00000000000403c00000a01000000006000000800000c00000002000000000e00007602005800403801e00600002001c00e02400c00a01a00200e00801203e00000e02402c01c0000a400e00000400001800c02003a00200600801e00601206003c00400000a01601e02c00e00000605c01200000200000c00000603a00a01400c00e05a00600000001400600402a00601600c00200007802401000000402600600e00601004602000201c00201600402802200200e00404e00800800000000a08602000202c02000600c00400400800e00402802c00003603800400201000c00400200002600e00001001e00400002a00200000002201000000600003200400200000200000802200801200003000401405005402a00a00600200800000001000402e00200c02e00400000200000000200002001200801000402000a00001000200604005401200c02a03201002e00401c00000200e02000000000400000200600801804000000202c02400201e00400000002803400000200c00202400003a00c00604404800000200400000c03800a00601400202800002e00600204a06002e02e01001002402600605800c0040bc01000000802a00a00800801000000200800200405000200000403200c00e00000002400200a01400203c01a00801001800a01e00800c00a03802e02200400405c01200001200400000001801201000e00800202200003401000003c03204000400a00401401e00800000800001600201e00000a00001400600000800404001c03200e02206a01a03400000200000200205002c00000203600000000e00001a02000a00e00201800401604201003e00800000e00e04000002200000000200200a00404801603a00606e00000002600403c00000200801e00000605000001e04c04e00400007a00000000000000e02c00204800200c03800000002000200603000c00e00a00c00401000001800207006a00600002000c00403800800401600000200a00000600000400a00600001800000006a00e00e00001e00802402e00808c01c00000800005a0000020100020
  | 24 => 0x9680000000000b93000192c0003a60c4a1643603c55eb1ca847aa1c44a17f83d687b0002ab4d1a0890000b94ab600012c0e9400433b17f8001536202549922923a16b0000bb4f4664c13186c92da14a1f1a65cb120c1361980cb5699846786795a8847235a3556e03ee0840aac85cc3e61b8474e68b0f543a52cd9a1fa2928000e4c0003502550000000000302575e1b80000000f0476658225980006c4000120000091b45494d4b8e0003ea02712ec204124800010eb2c0000f611681522cb231467abe7596a5f0aac7ba4a3884cb2aba8000000174e94e00024b08ba40f01280000000000002dd00207ca0000000ab458033607602be0002ec0f6c000c060f108245601793f188b54321fc0211748bd400000004c0bb25433fc80000000000848000fd415a2ffacb964e0000002bd88f40004999c148f8b670000cc05d2763216b13c104000348878cb6600000024fd1ca0000f6800139c000123a83c4f626737a0ec82de8b51f087d115a5a762aa451170427397236148c14f4e98868198adf2bf043d474b95260ac280000000d6140c0308032921ec836e3370000c41118b910000000000b124f2800161231a143964d6f82ae43f0e652dc00037ea6b8db67683590e443ae25a2b9a49cd1806343430f032a1e82b3905c0c262c2ea9854a8aa8b482a84947c19f18287cc22e6d54830eccf4c798039929817e73144b0ce093851c4c40000dc84d20001e6400000050c00011cc000605029138c0000dc8000d725220c429b80e856a14bac7068c4cb2e300017fe00011e01895c465d4a1181c0000000279e412b600015e0000fe83361bd293983810726f28d400065a00012a85b60001730000ea4832000000000033c0e7000054c7650000000000bd70000238770ab01a625012fc7453dd93f96a830a1ea015851a2261d42ed8c220002c292ec00008c000000040e824000015133c9d414c9398bba4902442ee4bbc00031aa63930670a1ac25243408ac012029809e00201002600c00c0a002600200000400204200005c00200c00008200001603800401003000001600000600000001000200601c05c03002201200000c00000000000c00c00200000a01000000400e00200000802800001c00401a00a00400200000601604400402400000c00200001800001602601a00200e00001600000e00c01200a00000002003400000c00400201c01800c00801400a00e00000000402c00800008600200000000e00000000c02001800c00400a02201000403601200201201602200600000201200000201200400001001003000002600200001000401400000200e00200000c02800e01400c01000600400801201a00000000600400c02a0000180000d600000a04001a03a00000a08800600002401200c01e00200600200000604800400001802c00
  | 25 => 0xac60b28564d563840828758194b971fc2954ac80592f987a8000000461997944a63b28912f85be0ef01a1510fb80000f31d7cd3420e40e82f50e2bf51b3241c0500a80a3267cbfa83014891513ae75d425a4391109af1f890d172c8f43fb84fc9b867734283b50668aa10522e4ef459a04ca9c8ec89b023e80002ae6564d9916ccce3853b70000a0e15528b80011803de1f4b0e800094c03d2ec472662d0c3037c3449205b78000a620000bdaf980007f16290aa556c0002e43084a7836c00002e45fc995073a1ad36295f0f010411ea6df2df2388fea7c61710f297d25e924f2c04044000199057520278a28fa7408ca000000000043a2383c700017d6a9a00ca8d93b800000007292eaa850f22594ab032a2190a757ba493000000060c8493e910e57145bb4790cd50c08ab3d3a6980003250001e5818a000365a37486a0fd07f1e784942a833d88603ee5b51e69c58b4c3981649190fe49fd097a69c30e4fc3b996b55b0b8208699081eeb454ed0aa9464a20485a3f17ec60010c85b8a7272029c1198656c2818b00000cea1d5bd915c0000000001f6533a9f61eb9f0c0000002c200d80007e60073080deeadb5792f097b66ae1f6ae00000bba57c800063ab1d551110d10630c3a32b3967e3b445398f96dc32321f999173615100013400b6b140ae2c9453c06c14d2e355204ae000090884c74f07da9fd09ea9440fa82d6fcadd2fd2350e84bd55f017053eeae80568e0969a000391208045ec1f43802807922cf26b18d8b8a45f603a084c5678c2f919342641350922a54818000446815c9e8b3a03225c12de31357613295668650001f0544400015216411324b54ed80017fac560af0000262b3212e914173ea381c583ad6061ae3d71b8d53cb474848858e065652fca53d2068dc1f13001100a71285a38d30e13353300004acbd05ec08850bc13c2e58d58cec1d2300800106a96a4dca1d4df6713612a77813a9153eda520b3832f0cb19f45ba70c3bead3061001d1611b0045087740800857f40000358714bd0a1b3769a2cf5a4b732026e0ed4af127b2b0806eb7504b05089e6b53000000000086906e883c9c25b25752078d3c0002528000000ada00004991da5eb00000011d40000000000000449228a62cc742ec3a224ed5f60003aa817d6cc79b1778a8c000296000000119400058d800000006f1b70cd0c040002870efd87200032ba1cc3a20d160bae7917630e0da80011fc0e25b98db4cdc4cf41f2a9d126736194304ceb619c4fd0e5c05c61c2de9314d82000426af7d5486a4411923ca6e4334f22940ad048735699a00005065d586f8a4013906b0000aa696b17213118088a44e28ec00ca82558f92acd708be0599bc854a276593000121e00001f8a40e6600034126a498000043e14bc0006195c795b0072b9a04f95717182d350a0
  | 26 => 0x2710eecaf42ba1cc91f654a3b5ad753d28bd5fc1a0d6103794e1863157600031b8000d98c0861611c188818b000000077c0760002fc0fec0cb13914d12e657133aace56bec3500005886f60700e61f792c200023f2d382e83074cc91781e47412020b8507a542588b10406aa7c05d8014b623ef0000af96d6a75302ad180007fb2448000000afa0001f2010cba949191347625263fe8f053a44b60001d2083c9692522fb18906e13e580000006c544f9db160e845538069c0001930df968c8e892100000000002d14c224d823ca0a2ca3058ba22e00bd13bcbf052b5210000236ae7000051d0c60131690000000000000125c6d00000001f9478000056919b57160600000000fa07291b10000d0245a5338add15e000000000170a775000281c93018016201313564822a0a734bf883742a292417c98a04a1b6420495714f86f4b58a11504201141230113a8c64da0a7911b17bcb9e5a029f9ba8604b811ac8cf863664727c162874816349c03612c085c3f98000f2803c2672a60e7a5aa08f92a54b0718167194cd00c2d22390887fe57930615ac0009cc6191ed9376a6b3d4afcc0002ea39f96191a22063f39e187905364950c845c683819603d94a6613000000011e39d0cb800000053e038a0445f200025699381c01d4024a0ec7e02b91c09158e1c0002a3829413c00041fa6f43d87c530c1f5cf9e65118784dd7b8a8f4921740d1221028d25fc7f40000f286a4bca53b5199751596bcf5228004e7600b2129a6cb1e6d24bd8ad0ca453a4b907d80004f747219c000000047f80015f84d837f2ec00000004d10000c1000f23417b97a828345e14c93ea91e628ae212a26bf0579245024a37444902c4d8ba225d18c00f6315016a309666672307800133427112f1f444740001501c0069400035a0000db40155202af4f924b84370b3130c68740b12d181e95060280000005881900f1122e7af00f0e18fc0ab858c2a712b2bc44178b34cfe7da1fa1b4cbc2b9453f1c24e922c12b92cd16c44ac2840d509c626e609236863c58d2d79308be88a35b699155fcae32dd1bd4a921541a08e71620ac31d7221c79686c113820cf2ec4b049802010207e0002abc22a01f54f998800012032e0c880f09f42c584b514a0005ed0a6042472f00019e898c2d759e0d4d5460c602880004d687600013509d02e74c780000000000001eb0c708444330d1562c7375b2a7ece2ea412ef80001f22794852bfc1308466230830000bde01300005424ff00000003662f60001d0c0008cb2200000dba1730000d9000025200b251800693a3a80be13fc00752910913c40000588ac80009aa44d0c98abc0001ec8f80a5082e31f8018000000000000000004000000f80000003132db02000001f5ab64e74080467000000051513bb0acb3a94448c814d4460ab1270f44396
  | 27 => 0x891600000000002340000000eb0ae100000000000d458286ad02e1c1324ac4c85e1835e70d8029a80c4b614844caa9933e1c446b42c00e21ff971278845d01b4f0661e1a8aac86a4a1514d95d5580a8350223649981dc506300400000021e21200000002bd1678bb87ed62a10748ec380475acec2ce3630002cf4d76b7902298c808e6591d12b1d7967df1ae97906b833a5e09e2c6fa78918e19800001f906100000000000ca1e105ea55f1eb10491160000000c6160ca0d2a600018360002158000000ad360100000000001340000fde00000023e440000000026d085405e1a82b914782af37c295000009a00020e4cfc0000001d840000000002a014fa0003d4188d0f0655241838400011a00011b851400040300018600000001db4000278062028d4d00000002dd91407471e780005a085822612743aa9390b814242faaac2300a38d8ebac28c9c84d283a139e27b000000000000013ba3960002065854c1e0000b192ba0004e5086c0d4ac859530d83e00550002d787ee48512601f4b600e80db158c84049a00014089868c62000a491d0c0d071a78089c0a1354292c6065a44a903996aa0dc1c1af200002de15ea91185c5bc3d829b10127040161cac9b670806db0bc0008cc2e699cd7f857021b2ad4e029eb61116a45e200038a8f7cb04348440a0507e406650d2aa14c025f554a154000479274a0a8038ab91e3000178c98221d0941282c4e37c9a201e26430001af95ae3bb0ec91a52b078044127b800092800016d800075a00000017800005d0008c4e80755f411c92f43ce1a6ac896b666361880000006650002edc000943349000126e41f6229dc92ee92e34815dd2263c34b12cbc29c90d00000f494e00929821408b82892b6af0ca3c4ed303000083234f10f28c17641444b888549466d80000d94dc047f20e28b40008b149e971142060d00025784e03701b88000a3671934e228955c2292ebae60d2e000000210ca7ab5900000000002fb09a23d9108000320800041ac1d3d8a78c7ea7b800028ec68656143687e09aeb2961397886886fc2b480003fe9b60fd8648ee200009e80a8336266246178c0000000002cc579469f000092139001734c1a74e5a85215881692e894517e00013480cf367a7c0e3800049f2d20a1a7a429180000008ef3cf89352a604d46f2df573a911162825456a62e62388dcaa00000c8972828a5182b3182c0009001b52260c0811100000004a818542600006e6000000000150c3275e61b9cb3e7b32ed90395dc61d544a020bc077846da128a4e826045134c9281fe1122650e486795ff1e1ce9c23f1cf80c04a6158094ab593e48f31e9866831c89c4e795204168a661f834c0000001f386a04d218d000000000029357a98e40fe166000012800000047880017789cb5688001646a285218000f7e244000
  | 28 => 0x94041a0b830001ee50680d94ea9f88024492184a7086e85ec275042c390372259a605338aef3b7a37c68044113f2b3050217f00022793ce0f85c38580de286710f9da4ce219d22c27a05b8bd36148ea41a478f5620821688a5f1bf85408103874f681c94daa0662619989322320b50a14aa4014502a5e12249085269c7cdfe0844478be8c2478d28a010d84c6dc0d8965cd6617c4c89ffc16c2610820240c882b305a0000bce3cc3f2100cca09ba0a180004280000a085dc5dc2315bf94b93121220830d2434826a4ae00003e20ea0ba9ea8dae3900000e388280005d20001876000430849435e1f518684b0000b303dea68c62237705a98c427661b27da340b1c48e38e80009400a23cd2cac000540095800000000000009bd886b6452b8de1594a5c54229ed02ac3301d82454b2b3631983b03a0b4000016852384e43fc0df906caa605480018700462ae876c00039a0001a6530a0000002bac0008b012326fd38e85a45910c51a400000000007ca4780001884d6c49b053ada800000013991145e847b4068dbce1a0002702fbd0340da0000e28e1e06854125f5448a4a2378cfd732be50c5131cf6e500460880c8d82a751c8d08c44af85f70000000c1a0ad9d2c0000e914a83780002d430b9d4400000043e82c055a2f208800290de0005d69bd8be07a24490000b0e020282ac542548572458fd8d6e7fa30f99bcf8e83a089208811a27a0000bc006200020d97580566930002758b8400016180001e025136a06049786ba50b073d32c4f24c00b2c6d2abc00022dd57c4bf0002d0c0000005131d291c217e5f100006ea16116aa0613de6ca586a8b96d23da4428000aec07700004308ce00046b91c48aa000000000000000010e00015da0001182bf400059b52d826cc780000000001708b7a42f9f08000c533ab2e9800000000025293cc0002f30844de6000294a8b031ebc751a308c0005461f3068d1fa0003611004ca85ce4ec1ad400027c000077c0004fd33c0f7524a00044aa1e94ec7070000000e285f654621a84400ee0001a94dd29902c60000804b410602f249baba325900000003940001a8577028c400000062405256a8c5c8502a236f23b009636b0d08fec2c80005ec9e440002c8117000076c000000155d6ee7353c0800000000000000007e644f09400000004f13eb2fd089462000006607740005780000000b285310000d620bc042aa596961ee199b0653d411460a2ed56b491f47ba02c34c9ff5f20e540b86295678458ea67704f9a2440000003bb83953927cd0dd964513a4182a791a82a67ab2df830d540813491277d4f47dd4598000858acd203a4605b2ac500023b8e164d11e80d84772609000128812477e22126dd7c2a214010d6cef80005ae09b48c61c647d1f311500004c6091564002f1c493ac1e80112068d7c29
  | 29 => 0x6062f2579b440000004b38c0000000000004e07787570002f340f254e31400000002c73f0a1c8510ae92e00a3c82a3dc58712a16427b441595346bc831498888ca262413080d1c99a71e4138ce4d9c4c807e0000cb010e378225d058a8e45f85c4d5e5da3e9895c35a00052d00000000000002a341747c45df1ac148eb3e4c9118446606924a8eb000010308e0afd03677912a80009aa0004641c48000935057106943e3a0324000110c61a5441a9c37415637d302d1143f912024c8e4a2ac3941f611acb0b22989f4f2a4845321c414ee64f3919218d901e12bf912045846d2852a9525a3140a4a70171cb170ef08883543292c18640c143241302c658220b74ab08acab241302219a96b006e2d129a81549a8572861164851046993b936436727825340740d719724bd7388010000cb4ba6a1709196dcef6abf4781324fd85810f49a8953a16845b2f8d252a3d0002eec00000000690287f88c72999cb14f09b55e917eca222fd558870c8e62621a72920a966c95e2a24174a8283c90ba13a20005289c09336284501000080a4b03c99258cb68e7375a2844b2a270002d3c0001991d59bbd3780cd4fe0d54000a3f49e23349be44b5a12c3096274c2d40fb02324443f488f94c2740570123572000015b05c8e72b35250800134aa2f2b7197cdca0004d01ed486e0c84621a1908424f5f880000000000001ce131a000000000000000005931347aab721bb2a0549838827d1b98e3400000015bc00051d00000014620001de80000000005b017b400000000010c160043d00027e40004812878c2c00023b60a8a016a46242cc0a70f78a730280000380000488000181c0005b18000000a975bc2b7850c7ce17991dc0003a700000000009f10a0000075e000000000069600043a0bdd5680b80e39fb863e0000e9a6f80005543ba000020200000005e0000000000052cc1c3e80001058d4ca0015c0000c7a000601aaac0000005f6a554a0812e02704f800864a5c300008b2bb400004e95e6a6521187bd3c23aa6282d84cd26ac3d2a8045940e45a8a9787d45623ce08e4c8c8412e490a500ec0c22905204feb0209b1a282da57c0f3a0703baa8a26ca9bd77e22a198a8acfd628b5681118f0a409371304075a0005f93090064000474a590000bd13a682204964f54d611d4392a5d2dc0d5c1e6bf72e623e011601b5c9284d6ac2da15d000101e000272a4d024255100000000001da12d8000f3aa03527a40958249f3938000ea85ae093989400050c4981dfc37841153a0000f7c82d28b000000038f0002d2800062a2e1800175c07c0000000c4e43b2aaa4113264b93b3a16c1ea95a35523240000fa347800000057857b8000fd000000024980007a05f51d6400059943f98595740002c910186f8243515009cce8b3715d97c56ae4621ff1aa56a000010
  | 30 => 0x9c13422b2500a0383d097dc5286963740f093b268e5fda9581fe85606385d915caaa064800189225c29525e54d2a0e2bd9bb897a0001c9139cec45a53632e851c03b51f20734ac0c3d0899c6c71abaa141298ccd683c2108edc3fa0000001368faa0000002b710ba0001cf28a45aca1e0b480cc0ba0000000030b722d831a0001234c186202c790a690c00000000827fc0002a853f0b680001f00bea52c3ae1af400000010b94b4e0c00027100012c600000019840007f00da13e49d857d5b898510a20004d09a8c40a0ce112a6b56703fd4271d8078ea9234a81600000002da219101c84043c9bb009038c00000a5256c3408c00007460000001b58870c4239f0e6c0343d2175800177a8624050c1105223544d8000304ae60002c6969216c0f9025d11c1a50e100002146bc5d990f98940ac5489d797f226455b8354e
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x160d931d065485200050b25d431952148001a0d8350c65485200069160d311952148001e05434c46548520005a164c741852148001a458354c61485200052925d431852148001a858350c61485200078154d431852148001589931d3704852000d07e5d5350f65c4191c0e7254d43d97100070354d435cb65c400141f9754d43d8b100050765d5350f62c400509c985cd4358b1000607a1d5350d62c400181c8754d4358b100052525d434c562c400341c9754d435961000507a5d5350d628400141c9754d4358a1000e2321d434c96284001629951094058a10005a264c4250162840016a1911094058a100051625d534c1628400148d931d16248610005836486350f654416ba148650d31d9510005836487350f654416b615911cd43d95105ad86a407350f654400181e8750f32d95105ae07a1d43cc76544001a513160031d95100060761373cc3654400341c9754d4359510006076117318c654400184d73608631951000507e5f6350c654400141d9718d4319510005836486350c6544169a148650d311951000686a19438c0654416181d845ce43195105a586a438350c654400181d845cf32195100060761d43cc8654400181d8750f31195105a686201434c4654400181d845cc3119510006135cd820c465440018597360031195100060761173cc0654400181f85e13735891000507a5d5350d624400141c9754d435891000607a1d5350d624400181c8754d43589100052325d434c9624400388c8750d32589100052525d434c562440038948750d31589100052625d438c162440014589754d305891000e1621d534c162440ab86476a0b755451004e1c1d98014951440879537560c70545100050764c74d95214400141d931d065485100041d660659c7204416181d845ce43994100060761d43cca650400181d8750f319941055d262417350d650418d41d979cd435941055d862417350d6504001c1b905cd435941063f062417350d650418fc17105cd435941063f054417350d650400181d8750f32594100060761d43cc56504157898805cd535901063d0765e7354d640418dc18805cd5359010637068417354d6404001c1973e0153590100060761573cc9640418d41d979d57458c1055d26241755d16304001c1b905d57458c1063f06241755d1630418fc17105d57458c1063f06841755d1630418fc15105d57458c1000507657715d1630400181d855d37258c10635836565350e6204001a0d8550f31988100068361543cc9620400160d959cd4358810635836565350d6204001a0d8550f31588100050764c74995210400141d931d16548410004276607458d210400148d931d162484100070654d43dd910040014389754d64440100068660d535911004001458976156344010006866158458d1004001a91816116344010
  | 1 => 0x68a55180d0d6214001a29856034358850586836115390d62140b906c97615435885000583e4d8550d621400160d95e0d435885055da2a438350d621400160d959cd435885000583e557350d621400128d9321171588500068361543cc5621400181d876116394850007035cd4358a5214161a158454e4398450005856567350e61140012959321172984500068561543cca61140012719020954584500049c6408254d6114001a315460343584500068c61580d0d6114161a158454e4358450004992498550d6114001617936154358450005892498550d611400161595e0d435845055da4a438350d6114001615959cd435845000585e557350d6114157690905cd4358450004a564c845c96114001a158350e52584500068561543cc96114001a178550d32584500060760d435da51140ab86581a0976944500060761d8458e511400144e92dd16394450005166427258e5114001c0e9458e729445000703651639ca5114001c4a8058e729445000712601639ca5114001c0d63d0e72944500070358d439ca511400146692dd1619445000519a4b735865114001c157350d61944500051c642725865114001c27439c961944500070950e725865114001c62909c961944500071864272586511400109d9321d6448450004276607458d211400148d931d162484500052564c749852114001495931d161484502ad13a4b7558c211400141f9754d43987200050765d5350e61c800341c9754d435962000607615731cd648818f41d979cd535922064d866427354d648800181d855cf32592200060761573cc564880038948750d31586200052364e645ca518800141d9399275886200050764e645d6218800109f9361b74486200042764c87591218800160d9294d43d9520005856446350f654800122f9859042d95205d683219434cb654800152a9710940d9520005c264c4250365480017219110940d95205d5836487350f6548001615911cd43d95205d586a407350f654817581e8750f32d952000607a1d43cc7654800181d84dcf30d952000d0725d5350d654800181d845cc6319520006155cd8118c654800141f97d8d43195200050765c6350c65480016159118d43195205ce83219434c86548001529971094019520005c264c4250065480017219110940195200051665c634c065480016519118d301952000507650325cc6548001455910c9731952000516640325cc654816181d845ce4319520006132097350c654817361a90e0d4319520007035cf8250c654800142d972094319520007035cc8250c65480016259120943195200060761d43cc8654800181d845cf31195200060761d43cc4654800181d845cf30195200068360d43197214800141d931d365485200050764c74195214800150d931d365485200054364c741952148
  | 2 => 0x4401a0d8550f3258a51005836526354d629440128d932117558a51005836567350d62944016859194d4358a510068361543cc5629440128d93a127058a510068361153cc1629440188d8750c3058a5100683615430c16294401a85436043058a51007035cd4398b51944014709058e71949510070558d439c652544014559318271949510051a241639ca5154401c0d6350e72945510051364c609ca5154401a198550c30d8151006a250d820c36054401a914360430d81510060760d43dd9511456941c9754d4358051647031c95350d65c840341f9754d43d9621006076117398e658840141d940c9739962100515644325ce6588401459900c97399621586076117390e658840184c825cd4399621007035cf8250e6588401c0d732094399621005896448250e658840181d8750f32996210060761173cc6658840181d8750f31996210060761173cc2658840181d8750c30996210068350d820c26588401a1543604309962100507e597350d658840141d979cd4359621005856467350d658840121d9321172596210060761d43cc9658840181d8750f31596210060761173cc1658840181d8750c30596210068350d820c16588401a154360430596210068360d43997218840341f9754d43d95210042766273192654840509c985cd435952155d262417350d654840181e8754d43595210060721d5350d654840109d93e1d65d9121006076177398f644840509e98dcd63d912100427e617318f644840141e96dcd53d9121005866406354f644840149696dcd31d912100607617739cf644840141e971cd53d9121005866407354f644840181d85dcf32d91210060761773cc7644840181e8754f30d912100607617730c3644840188f7360830d912100625dcd810c36448401c0d5350e76d49210056164c649c752484019458354e71d492100529259439c752484019858350e71d49210074154d439c7524840148d9319172945210050764c649d6214840141d9319175885210054364c649d6214840142c9650e75885210064360d439d62148401945834c675885210074150d319d6214840181f7560c6458121006071d583191604840109d981cc645812100427a6064dcd604842d88e7260c64181210052364c74dd92108401c0d5350f764842104c172617354d600840141e9754d43580210050725d5350d6008591c0e7254d43987500070354d435ca61d400388c8750d3258a5000e2521d434c56194001c0f6350e72946500052364c74589219400181f8350e76d45505860761d759d16314197a19856027458c5055d26a43875d1631400160c926157458c506558664274551631400181f875d15458c500049664082551631400181d855d37258c500060761574dc56314157898805d17158c50586836115390e6214001a0d8550f319885
  | 3 => 0x1982703871900488b0419d0601be0024007a8884800b10324e9de00262668b6951ce001b2518002193600000459569e0000001c002307b06e7e1e6998e6058009c0e285aac000182b03052a684f9bc001543e0000514e24878ad102420aa4702c6489a3c8ca25046000d45d0f68f132288520027a6e800339cc8e8f05c1e23b800001ea23930880087088c5985a590701d284381b0a18a4318001c92cb4000ad8005b1266918c1a2b03a0008020c2f000438e461a463317a7d1da010008a04e968963600c0a20400244b3a58a29e800238aca3294800449ee092a83f02000000001420012401a8e9f14c8b88a1aa2c002a0000001f800001c4a8ac6b30000000006800502488a8620d8b802ac820150102922e8da6b0c4a98d6afa18a7182791d85c800001f6578be001846ba60a693c212368089800188521a27290a0027287128a90905f9185b84c5720a8fa4c6800028050a78001790c7803c1215275a74b48d00d2aa001d490a4a5a0000003a82000942c01f0c26e21e479dc2a000a02c293822000000a8666d99e56abc6385800000049aa03a34888de978005d80065800152100004a2d05c561a672000891d22b98a18296469146a0443fa6a4d010000d21b1105e2ba00294a419c001f27f000208fa0fa6e1097c9b16a0b8f49912a1ea760092e29a569f9f0a60007f800850562200058aca511043706489938a09fa972b8650c8868000992081876ab800580006d1c0300003a8b283a8c000ec2799010008000d0c00c20100a00c00040001800020204016150009c782807000140100020000807810260201058000c000041400078000001040040201070440000000040219048045e000201000000302000320000402000180000001c000020c070100219009c80a240c80000000000400090183042000281400010386806070180c0a090380c02005cd0725d5350d60149736189054d435805204c96261534c16014801265912015398a5100583e455350e629440160c9054d4398a510068361543cc66294401a0d8454f3098a510062361d430c26294401a0d8550c3098a51006a150d810c2629
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x2003c000118030000500938000000000b00000a0021c035000300402000000009816849054d4398a5100582140b1a8738ca4a8802c08a058d439ca5154401422d0904b9a8732c4200d015cd9120943996210061092cc1a8738ea4908034049654d439c752484018064b306a1ceb10a4200b01299434c6758852100508b42412e6a18ca90003405736448250c65480018064bb06a18ca90a4000b0129d434c465485200061092ec1a8630a42900034049754d43185214800180c4bb06a9ac88802000a0629d856116344010
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x4
  | 2 => 0x5
  | 3 => 0x1
  | 4 => 0x2
  | 5 => 0x4c
  | 6 => 0x4d
  | 7 => 0x138c
  | 8 => 0x3
  | 9 => 0x6
  | 10 => 0x94c
  | 11 => 0x94d
  | 12 => 0x124c
  | 13 => 0x124d
  | 14 => 0x138d
  | 15 => 0x8c
  | 16 => 0x8d
  | 17 => 0x98c
  | 18 => 0x98d
  | 19 => 0x128c
  | 20 => 0x128d
  | 21 => 0x150c
  | 22 => 0x150d
  | 23 => 0x14c
  | 24 => 0x14d
  | 25 => 0xa4c
  | 26 => 0xa4d
  | 27 => 0x134c
  | 28 => 0x134d
  | 29 => 0x198c
  | 30 => 0x198d
  | 31 => 0x20c
  | 32 => 0x20d
  | 33 => 0x140c
  | 34 => 0xb0c
  | 35 => 0xb0d
  | 36 => 0x140d
  | 37 => 0x154c
  | 38 => 0x154d
  | 39 => 0x2cc
  | 40 => 0x2cd
  | 41 => 0x14cc
  | 42 => 0xbcc
  | 43 => 0xbcd
  | 44 => 0x14cd
  | 45 => 0x19cc
  | 46 => 0x19cd
  | 47 => 0x44c
  | 48 => 0x44d
  | 49 => 0xd4c
  | 50 => 0xd4d
  | 51 => 0x164c
  | 52 => 0x164d
  | 53 => 0x1a0c
  | 54 => 0x1a0d
  | 55 => 0x94054
  | 56 => 0x94055
  | 57 => 0xbd394
  | 58 => 0x138954
  | 59 => 0x95394
  | 60 => 0x95395
  | 61 => 0x954d4
  | 62 => 0xbc954
  | 63 => 0xbc955
  | 64 => 0x94bd4
  | 65 => 0x14c954
  | 66 => 0x14c955
  | 67 => 0x14c9
  | 68 => 0x2c9
  | 69 => 0x139254
  | 70 => 0x125394
  | 71 => 0x125395
  | 72 => 0x449
  | 73 => 0x1649
  | 74 => 0x138bd4
  | 75 => 0xbd395
  | 76 => 0x14d394
  | 77 => 0x1394d4
  | 78 => 0xb0994
  | 79 => 0xb0995
  | 80 => 0x98b14
  | 81 => 0xb0e
  | 82 => 0x154994
  | 83 => 0x154995
  | 84 => 0x99554
  | 85 => 0x154e
  | 86 => 0xd4994
  | 87 => 0xd4995
  | 88 => 0x98d54
  | 89 => 0x164994
  | 90 => 0x164995
  | 91 => 0x99654
  | 92 => 0x14b
  | 93 => 0x134b
  | 94 => 0xa0b
  | 95 => 0xb1514
  | 96 => 0xb1515
  | 97 => 0x150b14
  | 98 => 0xbcb
  | 99 => 0x19cb
  | 100 => 0xd5514
  | 101 => 0x150d54
  | 102 => 0xd5515
  | 103 => 0x14c154
  | 104 => 0x154d4
  | 105 => 0x154d5
  | 106 => 0x164154
  | 107 => 0x15654
  | 108 => 0x15655
  | 109 => 0xbca54
  | 110 => 0xa4bd4
  | 111 => 0xbca55
  | 112 => 0x19ca54
  | 113 => 0xa59d4
  | 114 => 0x19ca55
  | 115 => 0x2d354
  | 116 => 0x1342d4
  | 117 => 0x1342d5
  | 118 => 0x14d354
  | 119 => 0x1354d4
  | 120 => 0x1354d5
  | 121 => 0x45354
  | 122 => 0x134454
  | 123 => 0x134455
  | 124 => 0x165354
  | 125 => 0x135654
  | 126 => 0x135655
  | 127 => 0xbd994
  | 128 => 0x198bd4
  | 129 => 0xbd995
  | 130 => 0xb0214
  | 131 => 0xb0215
  | 132 => 0x140b14
  | 133 => 0x140b15
  | 134 => 0xb1414
  | 135 => 0xb1415
  | 136 => 0x44b14
  | 137 => 0x44b15
  | 138 => 0xb0454
  | 139 => 0xb0455
  | 140 => 0x1a0b14
  | 141 => 0x1a0b15
  | 142 => 0xb1a14
  | 143 => 0xb1a15
  | 144 => 0x148b
  | 145 => 0x155414
  | 146 => 0x155415
  | 147 => 0x1a1554
  | 148 => 0x155a14
  | 149 => 0x1a1555
  | 150 => 0x155a15
  | 151 => 0xbc2d4
  | 152 => 0x2cbd4
  | 153 => 0xbc2d5
  | 154 => 0x14cbd4
  | 155 => 0xbd4d4
  | 156 => 0xbd4d5
  | 157 => 0x44bd4
  | 158 => 0xbc454
  | 159 => 0xbc455
  | 160 => 0x164bd4
  | 161 => 0xbd654
  | 162 => 0xbd655
  | 163 => 0x19d4d5
  | 164 => 0x19d4d4
  | 165 => 0x14d9d4
  | 166 => 0x1659d4
  | 167 => 0x19d654
  | 168 => 0x19d655
  | 169 => 0x4954
  | 170 => 0x18c9
  | 171 => 0xe89
  | 172 => 0x1a49
  | 173 => 0xec9
  | 174 => 0xe8b
  | 175 => 0x5994
  | 176 => 0xe8e
  | 177 => 0x18ce
  | 178 => 0xecd
  | 179 => 0x1a4d
  | 180 => 0xe82d1
  | 181 => 0xe94d1
  | 182 => 0x18cb
  | 183 => 0xecb
  | 184 => 0x1a4b
  | 185 => 0xe8451
  | 186 => 0xe9651
  | 187 => 0x129515
  | 188 => 0x1289d5
  | 189 => 0x28b
  | 190 => 0x1049
  | 191 => 0x15394
  | 192 => 0x15054
  | 193 => 0x14a14
  | 194 => 0x14ed5
  | 195 => 0xb1a55
  | 196 => 0xb0ed5
  | 197 => 0xb1455
  | 198 => 0xe8ed1
  | 199 => 0xece91
  | 200 => 0xece93
  | 201 => 0xed289dd
  | 202 => 0x10414a1c
  | 203 => 0xa01505c
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 64
  | 7 => 2156
  | 6 => 4773
  | 5 => 3159
  | 4 => 362
  | 3 => 17
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
  | 8 => packedAt gbK8 (1811+((h/21+packedAt gbK8 (1664+(h % 21)*7) 7) % 101)*7) 7
  | 7 => packedAt gbK7 (88388+((h/718+packedAt gbK7 (79772+(h % 718)*12) 12) % 3130)*13) 13
  | 6 => packedAt gbK6 (249787+((h/1591+packedAt gbK6 (229104+(h % 1591)*13) 13) % 6930)*14) 14
  | 5 => packedAt gbK5 (199017+((h/1053+packedAt gbK5 (186381+(h % 1053)*12) 12) % 3791)*13) 13
  | 4 => packedAt gbK4 (26420+((h/120+packedAt gbK4 (25340+(h % 120)*9) 9) % 435)*10) 10
  | 3 => packedAt gbK3 (1407+((h/5+packedAt gbK3 (1377+(h % 5)*6) 6) % 37)*6) 6
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x1fe3ffe70c3f8e03818e0707ffc8611f36443f
  | 1 => 0xe1fc70180fc3f003fff007f83fd186e44878cf
  | 2 => 0x1ff801ff003fffc01fff800382618f88f8f0c
  | 3 => 0xfe00001ffffc000001ffffffc0381f00f00ff0
  | 4 => 0x1ffffffffffe000000003fe000fff000
  | 5 => 0xffffffe00000000000000000003fffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x22090c304068228888211018a802009164415
  | 1 => 0x20c4210800411011251022501500826408184a
  | 2 => 0x16902491001a49805a4b010a18208b80a8d0c
  | 3 => 0x54000414aaa80040104944a600381500e002a0
  | 4 => 0x10000896cf32496258004023023d6000f56000
  | 5 => 0x99924f0082200180600180c4043fdfd6000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfefefeeafefcfe88fefefeeafefcfe88fefefeeafefcfe88fefefeeafefcfe88fefefeeafefcfe88fefefeeafefcfe88fefefeeafefcfe88fefefeeafefcfe88, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36414
namespace PEqualNP.Outside.L_meta_36414
open PEqualNP.Outside.L_meta_36414.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 4 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 13 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 13 := bs0_4_0
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
theorem bs3_2_0 : Interval s3Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 3 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 29 := block_range (n:=29) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 29 := bs3_3_0
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
theorem bs3_4_448 : Interval s3Atlas 4 448 25 := block_range (n:=25) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 473 := (concat (concat (concat bs3_4_0 (concat bs3_4_32 bs3_4_64)) (concat (concat bs3_4_96 bs3_4_128) (concat bs3_4_160 bs3_4_192))) (concat (concat (concat bs3_4_224 bs3_4_256) (concat bs3_4_288 bs3_4_320)) (concat (concat bs3_4_352 bs3_4_384) (concat bs3_4_416 bs3_4_448))))
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
theorem bs3_5_608 : Interval s3Atlas 5 608 24 := block_range (n:=24) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 632 := (concat (concat (concat (concat bs3_5_0 bs3_5_32) (concat bs3_5_64 (concat bs3_5_96 bs3_5_128))) (concat (concat bs3_5_160 bs3_5_192) (concat bs3_5_224 (concat bs3_5_256 bs3_5_288)))) (concat (concat (concat bs3_5_320 bs3_5_352) (concat bs3_5_384 (concat bs3_5_416 bs3_5_448))) (concat (concat bs3_5_480 bs3_5_512) (concat bs3_5_544 (concat bs3_5_576 bs3_5_608)))))
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
theorem bs4_2_0 : Interval s4Atlas 2 0 15 := block_range (n:=15) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 15 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_32 : Interval s4Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_64 : Interval s4Atlas 3 64 4 := block_range (n:=4) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 68 := (concat bs4_3_0 (concat bs4_3_32 bs4_3_64))
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
theorem bs4_4_384 : Interval s4Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_416 : Interval s4Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_448 : Interval s4Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_480 : Interval s4Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_512 : Interval s4Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_544 : Interval s4Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_576 : Interval s4Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_608 : Interval s4Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_640 : Interval s4Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_672 : Interval s4Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_704 : Interval s4Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_736 : Interval s4Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_768 : Interval s4Atlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_800 : Interval s4Atlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_832 : Interval s4Atlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_864 : Interval s4Atlas 4 864 30 := block_range (n:=30) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 894 := (concat (concat (concat (concat bs4_4_0 (concat bs4_4_32 bs4_4_64)) (concat (concat bs4_4_96 bs4_4_128) (concat bs4_4_160 bs4_4_192))) (concat (concat bs4_4_224 (concat bs4_4_256 bs4_4_288)) (concat (concat bs4_4_320 bs4_4_352) (concat bs4_4_384 bs4_4_416)))) (concat (concat (concat bs4_4_448 (concat bs4_4_480 bs4_4_512)) (concat (concat bs4_4_544 bs4_4_576) (concat bs4_4_608 bs4_4_640))) (concat (concat bs4_4_672 (concat bs4_4_704 bs4_4_736)) (concat (concat bs4_4_768 bs4_4_800) (concat bs4_4_832 bs4_4_864)))))
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
theorem bs4_5_608 : Interval s4Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_640 : Interval s4Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_672 : Interval s4Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_704 : Interval s4Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_736 : Interval s4Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_768 : Interval s4Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_800 : Interval s4Atlas 5 800 20 := block_range (n:=20) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 820 := (concat (concat (concat (concat bs4_5_0 (concat bs4_5_32 bs4_5_64)) (concat bs4_5_96 (concat bs4_5_128 bs4_5_160))) (concat (concat bs4_5_192 (concat bs4_5_224 bs4_5_256)) (concat (concat bs4_5_288 bs4_5_320) (concat bs4_5_352 bs4_5_384)))) (concat (concat (concat bs4_5_416 (concat bs4_5_448 bs4_5_480)) (concat bs4_5_512 (concat bs4_5_544 bs4_5_576))) (concat (concat bs4_5_608 (concat bs4_5_640 bs4_5_672)) (concat (concat bs4_5_704 bs4_5_736) (concat bs4_5_768 bs4_5_800)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_32 : Interval s4Atlas 6 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 44 := (concat bs4_6_0 bs4_6_32)
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
theorem bs5_4_0 : Interval s5Atlas 4 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 4 := bs5_4_0
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
theorem bgb_3_0 : Interval gbAtlas 3 0 17 := block_range (n:=17) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 17 := bgb_3_0
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
theorem bgb_4_192 : Interval gbAtlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_224 : Interval gbAtlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_256 : Interval gbAtlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_288 : Interval gbAtlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_320 : Interval gbAtlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_352 : Interval gbAtlas 4 352 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 362 := (concat (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat bgb_4_96 (concat bgb_4_128 bgb_4_160))) (concat (concat bgb_4_192 (concat bgb_4_224 bgb_4_256)) (concat bgb_4_288 (concat bgb_4_320 bgb_4_352))))
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
theorem bgb_5_3136 : Interval gbAtlas 5 3136 23 := block_range (n:=23) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 3159 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat bgb_5_288 (concat bgb_5_320 bgb_5_352)))) (concat (concat (concat bgb_5_384 (concat bgb_5_416 bgb_5_448)) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))) (concat (concat bgb_5_576 (concat bgb_5_608 bgb_5_640)) (concat bgb_5_672 (concat bgb_5_704 bgb_5_736))))) (concat (concat (concat (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928))) (concat (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)))) (concat (concat (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)) (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312))) (concat (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)) (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 bgb_5_1536)))))) (concat (concat (concat (concat (concat bgb_5_1568 (concat bgb_5_1600 bgb_5_1632)) (concat bgb_5_1664 (concat bgb_5_1696 bgb_5_1728))) (concat (concat bgb_5_1760 (concat bgb_5_1792 bgb_5_1824)) (concat bgb_5_1856 (concat bgb_5_1888 bgb_5_1920)))) (concat (concat (concat bgb_5_1952 (concat bgb_5_1984 bgb_5_2016)) (concat bgb_5_2048 (concat bgb_5_2080 bgb_5_2112))) (concat (concat bgb_5_2144 (concat bgb_5_2176 bgb_5_2208)) (concat (concat bgb_5_2240 bgb_5_2272) (concat bgb_5_2304 bgb_5_2336))))) (concat (concat (concat (concat bgb_5_2368 (concat bgb_5_2400 bgb_5_2432)) (concat bgb_5_2464 (concat bgb_5_2496 bgb_5_2528))) (concat (concat bgb_5_2560 (concat bgb_5_2592 bgb_5_2624)) (concat bgb_5_2656 (concat bgb_5_2688 bgb_5_2720)))) (concat (concat (concat bgb_5_2752 (concat bgb_5_2784 bgb_5_2816)) (concat bgb_5_2848 (concat bgb_5_2880 bgb_5_2912))) (concat (concat bgb_5_2944 (concat bgb_5_2976 bgb_5_3008)) (concat (concat bgb_5_3040 bgb_5_3072) (concat bgb_5_3104 bgb_5_3136)))))))
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
theorem bgb_6_4768 : Interval gbAtlas 6 4768 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 4773 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)))) (concat (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)) (concat (concat bgb_6_416 bgb_6_448) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))))) (concat (concat (concat (concat bgb_6_576 bgb_6_608) (concat bgb_6_640 bgb_6_672)) (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 (concat bgb_6_800 bgb_6_832)))) (concat (concat (concat bgb_6_864 bgb_6_896) (concat bgb_6_928 (concat bgb_6_960 bgb_6_992))) (concat (concat bgb_6_1024 bgb_6_1056) (concat bgb_6_1088 (concat bgb_6_1120 bgb_6_1152)))))) (concat (concat (concat (concat (concat bgb_6_1184 bgb_6_1216) (concat bgb_6_1248 bgb_6_1280)) (concat (concat bgb_6_1312 bgb_6_1344) (concat bgb_6_1376 (concat bgb_6_1408 bgb_6_1440)))) (concat (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 (concat bgb_6_1568 bgb_6_1600))) (concat (concat bgb_6_1632 bgb_6_1664) (concat bgb_6_1696 (concat bgb_6_1728 bgb_6_1760))))) (concat (concat (concat (concat bgb_6_1792 bgb_6_1824) (concat bgb_6_1856 bgb_6_1888)) (concat (concat bgb_6_1920 bgb_6_1952) (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048)))) (concat (concat (concat bgb_6_2080 bgb_6_2112) (concat bgb_6_2144 (concat bgb_6_2176 bgb_6_2208))) (concat (concat bgb_6_2240 bgb_6_2272) (concat bgb_6_2304 (concat bgb_6_2336 bgb_6_2368))))))) (concat (concat (concat (concat (concat (concat bgb_6_2400 bgb_6_2432) (concat bgb_6_2464 bgb_6_2496)) (concat (concat bgb_6_2528 bgb_6_2560) (concat bgb_6_2592 (concat bgb_6_2624 bgb_6_2656)))) (concat (concat (concat bgb_6_2688 bgb_6_2720) (concat bgb_6_2752 bgb_6_2784)) (concat (concat bgb_6_2816 bgb_6_2848) (concat bgb_6_2880 (concat bgb_6_2912 bgb_6_2944))))) (concat (concat (concat (concat bgb_6_2976 bgb_6_3008) (concat bgb_6_3040 bgb_6_3072)) (concat (concat bgb_6_3104 bgb_6_3136) (concat bgb_6_3168 (concat bgb_6_3200 bgb_6_3232)))) (concat (concat (concat bgb_6_3264 bgb_6_3296) (concat bgb_6_3328 (concat bgb_6_3360 bgb_6_3392))) (concat (concat bgb_6_3424 bgb_6_3456) (concat bgb_6_3488 (concat bgb_6_3520 bgb_6_3552)))))) (concat (concat (concat (concat (concat bgb_6_3584 bgb_6_3616) (concat bgb_6_3648 bgb_6_3680)) (concat (concat bgb_6_3712 bgb_6_3744) (concat bgb_6_3776 (concat bgb_6_3808 bgb_6_3840)))) (concat (concat (concat bgb_6_3872 bgb_6_3904) (concat bgb_6_3936 (concat bgb_6_3968 bgb_6_4000))) (concat (concat bgb_6_4032 bgb_6_4064) (concat bgb_6_4096 (concat bgb_6_4128 bgb_6_4160))))) (concat (concat (concat (concat bgb_6_4192 bgb_6_4224) (concat bgb_6_4256 bgb_6_4288)) (concat (concat bgb_6_4320 bgb_6_4352) (concat bgb_6_4384 (concat bgb_6_4416 bgb_6_4448)))) (concat (concat (concat bgb_6_4480 bgb_6_4512) (concat bgb_6_4544 (concat bgb_6_4576 bgb_6_4608))) (concat (concat bgb_6_4640 bgb_6_4672) (concat bgb_6_4704 (concat bgb_6_4736 bgb_6_4768))))))))
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
theorem bgb_7_2144 : Interval gbAtlas 7 2144 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2156 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 (concat bgb_7_480 bgb_7_512))))) (concat (concat (concat (concat bgb_7_544 bgb_7_576) (concat bgb_7_608 bgb_7_640)) (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 bgb_7_768))) (concat (concat (concat bgb_7_800 bgb_7_832) (concat bgb_7_864 bgb_7_896)) (concat (concat bgb_7_928 bgb_7_960) (concat bgb_7_992 (concat bgb_7_1024 bgb_7_1056)))))) (concat (concat (concat (concat (concat bgb_7_1088 bgb_7_1120) (concat bgb_7_1152 bgb_7_1184)) (concat (concat bgb_7_1216 bgb_7_1248) (concat bgb_7_1280 bgb_7_1312))) (concat (concat (concat bgb_7_1344 bgb_7_1376) (concat bgb_7_1408 bgb_7_1440)) (concat (concat bgb_7_1472 bgb_7_1504) (concat bgb_7_1536 (concat bgb_7_1568 bgb_7_1600))))) (concat (concat (concat (concat bgb_7_1632 bgb_7_1664) (concat bgb_7_1696 bgb_7_1728)) (concat (concat bgb_7_1760 bgb_7_1792) (concat bgb_7_1824 bgb_7_1856))) (concat (concat (concat bgb_7_1888 bgb_7_1920) (concat bgb_7_1952 bgb_7_1984)) (concat (concat bgb_7_2016 bgb_7_2048) (concat bgb_7_2080 (concat bgb_7_2112 bgb_7_2144)))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 5 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 16, 20),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 6 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfefefeeafefcfe88fefefeeafefcfe88fefefeeafefcfe88fefefeeafefcfe88fefefeeafefcfe88fefefeeafefcfe88fefefeeafefcfe88fefefeeafefcfe88
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4278124266 * 2 ^ 32 + 4277993096) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36414.Model.Repr at out
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

def mono : List Gate := [⟨.or,[3,4]⟩,⟨.and,[1,6]⟩,⟨.or,[2,7]⟩,⟨.or,[3,5]⟩,⟨.or,[0,1]⟩,⟨.or,[1,9]⟩,⟨.and,[5,10]⟩,⟨.or,[6,12]⟩,⟨.and,[8,13]⟩,⟨.and,[0,11]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124266 * 2 ^ 32 + 4277993096) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124266 * 2 ^ 32 + 4277993096) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36414

open PEqualNP.Outside.L_meta_36414 in
theorem PEqualNP.Outside.L_meta_36414 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124266 * 2 ^ 32 + 4277993096) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124266 * 2 ^ 32 + 4277993096) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
