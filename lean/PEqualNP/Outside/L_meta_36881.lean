import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, children closed at the parent by
-- restriction pools (closeChild of the model), and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36881.Model
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


end PEqualNP.Outside.L_meta_36881.Model

namespace PEqualNP.Outside.L_meta_36881
open PEqualNP.Outside.L_meta_36881.Model
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Atlas := Nat × List Decor × Sig × (Nat → Nat) × (Nat → Nat → Nat) ×
  (Nat → Nat → Nat) × (Nat → Nat → Nat) × List BoundPool

def top (g : Atlas) := g.1
def first (g : Atlas) := g.2.1
def target (g : Atlas) := g.2.2.1
def count (g : Atlas) := g.2.2.2.1
def record (g : Atlas) := g.2.2.2.2.1
def tip (g : Atlas) := g.2.2.2.2.2.1
def locate (g : Atlas) := g.2.2.2.2.2.2.1
def apools (g : Atlas) := g.2.2.2.2.2.2.2
def items (g : Atlas) (k i : Nat) : List Decor :=
  let d := top g-k
  let v := record g k i
  selectLive (v >>> (10*d)) (decodeBank d v (first g))
def vals (g : Atlas) (k i : Nat) := (items g k i).map Prod.fst
def roots (g : Atlas) := (first g).map Prod.fst

def SBf (j : Nat) : Nat := [6, 7, 6, 5, 5, 8].getD j 0

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
      testAll (k,ws.length,ws,preCov true ws,apools g,links g (k-1)) ws)

def Ready (g : Atlas) (r s : Fin 152 → Row) :=
  properPairs (target g) r s ∧ (∀ p ∈ apools g, ValidPool true (roots g) (target g) p) ∧
    (∀ a ∈ first g, faithful r s a) ∧
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
        exact decode_faithful _ _ _ _ _ ready.2.2.1 _ ((selectLive_sub _ _).subset ha)
      · exact ready.2.1
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
      exact poolCut_sound (ready.2.2.2 k i hi hn) _ he h.1.1 hc

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

end PEqualNP.Outside.L_meta_36881

namespace PEqualNP.Outside.L_meta_36881
open PEqualNP.Outside.L_meta_36881.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x302000520000010dc32bc43be43bf40bc42cc32bd40ec32be42bc41de32be41ef32
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0xa0170000100129430100c6196818c32907186420e3d5032a7294658e430cb1864a06390832c62186534515031884194714d40c62a0651e5390658a4a04b94a41
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x80083194325028661d503283d9432907043214540
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 13
  | 3 => 16
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
  | 5 => 2*((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/18+packedAt s0K4 (208+(h % 18)*4) 4) % 13)
  | 3 => 2*((h/26+packedAt s0K3 (432+(h % 26)*4) 4) % 16)
  | 2 => 2*((h/8+packedAt s0K2 (152+(h % 8)*2) 2) % 4)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xfffffffffffffffff81fffffffffffff87ffff
  | 2 => 0x1fffffffe07fffffffe07ffffe03fffff8fe3f
  | 3 => 0xe01fe03fff80fe01ffff83e03ffc0fc07f33cc
  | 4 => 0xffe0003fffff0001fffffc003ffff0007fc3f0
  | 5 => 0xffffffc000000001ffffffffc00000007ffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x2424228a241224a0500594aa4ac514550354d5
  | 2 => 0x949451443244948a96029549422aaaa38aa2a
  | 3 => 0x5d1189a6890e906b3aaa826627688f035d334c
  | 4 => 0x919d163912481d8dccd34c1839b3c20c6ec3b0
  | 5 => 0x1e1e183e1c70e1f1f71c739f01c30c3077fc00
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcc0c0c0ccc0c0c0fcc0c0c0ccc0c0c0fcc0c0c0ccc0c0c0fcc0c0c0ccc0c0c0fcc0c0c0ccc0c0c0fcc0c0c0ccc0c0c0fcc0c0c0ccc0c0c0fcc0c0c0ccc0c0c0, s0N, s0R, (fun _ _ => 0), s0I, []⟩
end PEqualNP.Outside.L_meta_36881
namespace PEqualNP.Outside.L_meta_36881
open PEqualNP.Outside.L_meta_36881.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x900010708100000004000000e1000c144000000000d0c21c0040341002000000193106146ff31fc31fd40ff41fc40be43be42bf40fd21fd32fd43ff42fe20fc32fc41fe21fc43ff40fc30ff20fe40fd10bc42fe31fd20ff10fc20fd31fe42fe30be41ff43bd40fe43fc21fe32fd41ff32ff21fc10bc43fd42ff30fe41fd30bc41fc42fe10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x80008004003c00440008006c001004001c04041ca45400300474040884002000100000102c1424b514a400101400d09000200024000400041400181400d01801e01800a0082000000c0400002c00180410100024041c0870000004f40c08040003388718734c8329f2a6433f54c435ca520ddd4540ba28a815c5348278a898cf947409f2a6659f535033aa7216ed41409f29887765190e78a8904f153109ea80873c544433887995b94a43da20c633d509065ca520cf94a43cf29c839d5390638a6a04b94a439f2a041e5210867aa9204f94a42d6214653c540ca3ca720e714d409e2a2655d53c867ca3215794f21da20c433e5488278a890d7d4d20aea98216d5290658a4a04f952329eaa0216d5290edaa518cf94a419f29c853e519075ca521cfd5132da20c213f54482bca6104f550209e2a063b4414867ca5a04d94643afa9a813f540c6daa598cf553329a28a81ac42486bca6086bd4940cf298875e5390adca4084fd5330af29c43b4414c6eaa2186b10b219e28a816c524c2eaa3215b149109faa641ac428827ea8885bd49109f2a46175510827ca6215714d10d629281765190adaa4086d546429f298836e520c2eca2184794e429eaa643b55190e7aa9085d94732aea9c4377514c278a4a05b548309f2a6633e541027ea890e794e429e29a813d54cc67ca420cf94f40bba8a41b4515027aa918cf95210db28c876e52cc75aa520cf552309f29c873e539067aa910edd4540db28c85765108278a9986710d31b7a92613e5210adca520ed10410d7290855d53082b8a6a04fd50329eaa4656e528c67ca2216710c30b7a9281ac424ca78a810cf54243d6a94875d539067ca321d794e419f2a4633f544c6eaa321cf94443b6292819c43cc6baa72157d4d109ea80853e511067aa1214f950109e2a641365190b6ca220cf948439f2a06176518cbaa6218cf552209ea80833d540c2eaa3195d547329f2a4433f540867ea8985d14520ba28a613c544c35884106710d32
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x3000a1c0013b44000001008b0210e810000000001408d140039700045140014010465c707c5d4c515022e62d5032c594d5190a3661d5021a558e511072454484218b98b54087255210631c554e5190b155310621c994a5190e346154042c354c420830d5394a41a358e5210b2752145408d98754cc30c43548308d9865310a3661d5320c514c515030c53149408b98b54cc30c544c8328d987540cb255294643c9548410421c6355220a958a51107244254632c514f515021c63540428b98b540c6956194c438798f540cb1553104108718d501072452145408b1895010e1e63d51218b189548c28d6294c43c9109510822e629444387594430c22e6294c418d98652d021e63d50318798f54c832452d45408798f54c42366194f408798e521062c62540418b98b54c431443547328d987544ca2d6510820c510d510c314544c4318d594410422e62d51318718d54842346155220c99495190f0e5354a418798e5110a3461540438b98a51d021e6394740c310d52cc6366194843c354c42c86346155230c314f525023661d50318b18954842a56194842c3d4c525030e5394a418b98a53d031653946428798e52d021e63d5021
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 186
  | 3 => 84
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
  | 6 => 2*((h/1+packedAt s1K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/51+packedAt s1K5 (768+(h % 51)*6) 6) % 48)
  | 4 => 2*((h/97+packedAt s1K4 (5022+(h % 97)*8) 8) % 186)
  | 3 => 2*((h/42+packedAt s1K3 (3192+(h % 42)*7) 7) % 84)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfffffffffffffffe07ffffffffffffff87ffff
  | 2 => 0xfc1ffe07e07e07fff8783c1fe0f83e0ffa4e93
  | 3 => 0xffe0fff8007ff81fff803fe0ff003ff07c731c
  | 4 => 0xffffff80001fffffc000ffffc0007f83e0
  | 5 => 0xffff00000000001fffffffff000000007ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x40002410010000001104821010a0284009425
  | 2 => 0xa94664324aa4ae8e582a151a68d0b42b3a4a92
  | 3 => 0x30caa890d349a2b6aa842748ba4139615c6318
  | 4 => 0xa294d1249a0d34db34ce8210dce590426f03c0
  | 5 => 0xc318e1c71c71c71dc7773b9c1086218c77fc00
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaaaaa0aaaaaaa0faaaaaa0aaaaaaa0faaaaaa0aaaaaaa0faaaaaa0aaaaaaa0faaaaaa0aaaaaaa0faaaaaa0aaaaaaa0faaaaaa0aaaaaaa0faaaaaa0aaaaaaa0, s1N, s1R, (fun _ _ => 0), s1I, []⟩
end PEqualNP.Outside.L_meta_36881
namespace PEqualNP.Outside.L_meta_36881
open PEqualNP.Outside.L_meta_36881.Model
def s2K5 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xc0000040240118000601e910000f843f4c3e107f30fc21f8cbe997f21fe65f0cbf187f20fc63f887f98fd31fa41fc43e087c30fa21f0c7e90fe20
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x24524000000100204004e20009100d00008000102d90430d5310c6d50632b541ccabd09309d43c86710d209c43442790c20cd320ca790e219d43886b50810af42442d90420b541082790f21ad428c6d90632b4414c2b10930ae42042750c20e521086b50830ac42442750c10ae428c6b50b319e43042d50430b441482b90b31ae420c2d90732b7414c2dd05209f434427d0d20
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 24
  | 3 => 39
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (i*4) 4
  | 4 => packedAt s2K4 (i*15) 15
  | 3 => packedAt s2K3 (i*26) 26
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s2K5 (4+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/22+packedAt s2K4 (360+(h % 22)*5) 5) % 24)
  | 3 => 2*((h/27+packedAt s2K3 (1014+(h % 27)*6) 6) % 39)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffbff7fffe3ffff1ff
  | 1 => 0xffffffffffffffffffffffd5f8e73fc71c7e93
  | 3 => 0xe6ff07cff81f8f1c
  | 4 => 0xf8fff80fffe00fe0
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff4010000009040025
  | 1 => 0x2a264a4642496692
  | 3 => 0x1942d41a90932b18
  | 4 => 0x78486ad24c24dc0
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 27 s2Pos s2Neg, 0xeeaaaa88eeaaaa88eeaaaa88eeaaaa88eeaaaa88eeaaaa88eeaaaa88eeaaaa88eeaaaa88eeaaaa88eeaaaa88eeaaaa88eeaaaa88eeaaaa88eeaaaa88eeaaaa88, s2N, s2R, (fun _ _ => 0), s2I, []⟩
end PEqualNP.Outside.L_meta_36881
namespace PEqualNP.Outside.L_meta_36881
open PEqualNP.Outside.L_meta_36881.Model
def s3K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x4001802e98dc30be6578c2f98dd32
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x300095410c25507328d42cc6350830
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (i*4) 4
  | 3 => packedAt s3K3 (i*15) 15
  | 2 => packedAt s3K2 (i*26) 26
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt s3K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/9+packedAt s3K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt s3K2 (104+(h % 8)*2) 2) % 4)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff7fcfc7ff8f3cf
  | 1 => 0xffffffffffffffffffffffedf99f3f8e3f3d33
  | 2 => 0x76fe1fcff03fce3c
  | 4 => 0x78ffe00fffc00fc0
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa010010012080045
  | 1 => 0x1224284484922512
  | 2 => 0x941501921248a28
  | 4 => 0x7851aae4986af80
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 23 s3Pos s3Neg, 0xeaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8, s3N, s3R, (fun _ _ => 0), s3I, []⟩
end PEqualNP.Outside.L_meta_36881
namespace PEqualNP.Outside.L_meta_36881
open PEqualNP.Outside.L_meta_36881.Model
def s4K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x1122e995f32be6378c2e185d31
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x310008d420c25504308d42cc6550732
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (i*4) 4
  | 3 => packedAt s4K3 (i*15) 15
  | 2 => packedAt s4K2 (i*26) 26
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt s4K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/9+packedAt s4K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/15+packedAt s4K2 (104+(h % 15)*2) 2) % 4)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff7fcfc7ff8f3cf
  | 1 => 0xffffffffffffffffffffffedf99f3f8e3f3d33
  | 2 => 0x76fe1fcff03fce3c
  | 3 => 0x78ffe00fffc00fc0
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa010010012080045
  | 1 => 0x1224284484922512
  | 2 => 0x941501921248a28
  | 3 => 0x7851aae4986af80
  | _ => 0
def s4Atlas : Atlas := ⟨4,rawDecor 15 s4Pos s4Neg, 0xeae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8, s4N, s4R, (fun _ _ => 0), s4I, []⟩
end PEqualNP.Outside.L_meta_36881
namespace PEqualNP.Outside.L_meta_36881
open PEqualNP.Outside.L_meta_36881.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x500900308100001b00708004a0c61000400410c0004000044005fd10ff31ff32fc42fc32fe42fc43ff41fd41ff20fd32fe41ff21ff42ff10df32ff30fd30fd40fd42fe20fe10fe32dd32bf42fe43fe31ff40fe21fd20bd42fd43fd21fc40fc10fc20fc30fc41fd31fe40ff43fe30fc31fc21
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x465bd54086fca9907b50920be29e43bd54c86faa7a06f50a32bf280657c524c75a8490770c630ef98e61be54cc7daa598fd4c710bf2a6617d54906fea9994f55032f790e417d540cbec6218ef90640bf28887f710043dca4205754e41bea8e61dd53d07ee82a0db54830bf288837d53103ba87985754c42beaa0435d53c82fca4885f54430de29a85df321079c84996f14f42dfa1481bf43106faa221fd54430be29283bf420cb7ca918d754c209f2a641dc42ccb9a6510f710e30bf29843dd32cc2fca8995f94240e6996417d54c837a84a05fd4d21af298857d500c6fea498efd0b30ee99221ef4290b7c87205f94331be282657e528c6fea5886fd4342bf29c437d52cc67aa810f754f20ee99043f7108437ca8195f54a40beaa4637d520c77ca8105f15220efa18617e518c7be62987bc8621dea14633e54083ba6498f74cb40ef21863dd320cafca2185fd49309eaa6417e52842fca8104f55231bfa8265bd42d07ba64105f94030be29c41dd434c37e84885f54041df2a6417d51c837aa6a16fd0b40eea8e65f6510c2fca020ef10640dfa1043f521c42fca6105fd4e10beaa461bf40102fca721ef94142efa1e65dd32842fca120df14e10bfaa2417c5250efca6905f54331f721085f531443f62088774c810ee29a215d538ca7ca8196f55320be28a657d51d02faa3187bd4910fa88021bf420837a84187350932ef218877d51882faa2215fd4540f729087df32c437ea8885f54341fba0c83ee52042fea6085b94810ef99481dd324c37e8498df94232bfa9e217d528437a84905f94f10bf2a085dd514cb7ca6a16fd0930dfa8a857f54082fea898fb54840dfa10217e548c3ec43885f54f10dea16657d54c431a84994f95042beaa0637e53107b8a999774ca20bf28e657c5350b7e85087790932df21a85bd42102baa790df94c43be2a6417c54cc67ca990f7cc832bf2a6435c53443ec20885fd5210bea80437f54486f8a690df95032bfaa221bd425075ea4a15714d40ee996636f524437e82a07ed0240ee996417c5150f7a8520df15021ef18a633f544437886a16fd0a42bea9c857e51102daa421efd0b20bf2a087bf42882faa8885f94e42efa1c617d51903be6410ef50831bf29485bf42c877e87a0778c932ef28265df300c3ec63887d50441b6a9683f9401037ea0a17750d32dfa1663bd4310efca320df55120faa8881fb10842faa6905f14542bea8687bd41503bca720db94830afa9a817d54cc37a87a17bc8520efa8e65ed4210b7aa7a17b08420bea90617f53443b8a8996f50e41bfa9841df32cc2f8a29877cc910ef28665fa300c2fca121fdcc531af29e41dd32486faa3215f54742dea16437e53907baa1996f90d43bea96217f52443ea4288774ca21bf28463f551082f8a990fd48421bea9821bd428c2f8a818df54732
  | 1 => 0xe5390b7ea8987754c21dea14817d5310b7c80a05fd5221dfa9a857d508877a84196fd0441efa8265dd54ccafaa5a05f54a43ee994837d52106fca410774ca30cea1887dc504cafaa7085f15010bf298637e5110afca62177cc920dea1e81de5390afea9185f94421de282857d518caf8a0a0df14131de28685ed5210f7a8220efd0831f7296637e52c43d8a4885f54420baa88617d5490fbaa790fb8cb20be298215e53906faa6887710d32eea98857551103b8a29977d0d31afa9a21bc43102fea810f754c10f6a16415d530437e85185fd4542ee990817e508875a859077d0932bf28865bd42083dca4185f55220bf2a4637d539037a8410fe48110be2a265df320c37a84886f95321dea1661de434cb7887a17d90510f710a43bf4310ef8a0a1df54043f690041be41102faa510fb4ca21ef996837d54043bc63186f55010bfaa6437e52d037e8520df54e32cfa12653e548c7b862185fd5032bea8865bd42d03f240106fd08409eaa0217e5190ad8a4885f54342bf284857e508c2fea7105f94843f6a12657e528c378a8885f94832dea8e857d52102faa019734c821f719443bd424c3da8510df14d40dea12637c53087be64a0ef90c40aea9e837d5490b7c87a15f94743dea10217e52cc6eca2187b94b41deaa0417c520435a8510dfd5331fc980617f53c877ca91977d5332bfa9c43dc424cafaa790ef55232f7a12857e53d0afea9905fd5030f6a1465bf43907be8798df94a41be2a461bd42cc6faa8985f15131f7212417c53443ba6420ef50a20bf28685ad428cafea4a07754132beaa041ee20483f2a010df14d41deaa0617d54903f661187bc8421fd200817d50c87f241085f15110bf28863df4350e7aa8106f10440bf29687bd5150b7c84a15f94740dea1421bf4210afea9885d944409e2a221be5150bbe65185f94a40bfaa265dc430c2fea4a0df95210bf28841ef324cbbe6418ef55032fb90a43bf42106f8a710f790e31ef99643dd31cc2fca7085f95131be2a0617d508c6fca890df54042bf2a663df434cafaa121dfd4121fd90241ad424cb7a85907dc8621bf28c61bf41d02fca7905f55332dea1a853e54cc6f8a6107714332be28a817f53502fea9107b48520ee996217c540cafca021df54743ef994837f50506daa598f794c10bf290637d51102fca321f710f32bea8c875e53042f8a58877d0b32af29e43de531033e859977cc840beaa2657c52443bea1995fd4d20bfa8a657d528c6fca018efd0f42bea8485ed32482fea918df95041bca80437d528837a8510f74ca40bf290437e53102fca3a15f55131bfaa4657c50487bca3997754c40af29e83de43ccb7a8490df54e21de28e85bd424cafaa520ef50740dfa1c877c54c43baa6105f95220bfa8a61bf42c437887205f15020dea1a81dd314c3dc64905f94c32f799
  | 2 => 0xe8000340300001059620300002011004000280023c2f000210780505c1e000044ec0c018000140d0280206c000503c03c0002c0104400014016201b1884e0100002c0016fbca7a0fd88510bea9843df32d03ec4210f3d4932ef99041bd50d0bba84997754e42bf28c817e52042f8a5085794c40dfa12657e52cc39a649077d0e43beaa663df324c6fea9986fd0921beaa443df318c7f22008774c030bf29061de514cafea6a15f94321baa88417c53c83f660986fd0a21cea12657e51042bca6197b90821ef99021be54042fca5194f55321bfa82877e54043ba87995f95310bea9c417d52cc3ba8718ef55231ef29e41bd431077e85195fd4520fb288413e540437e81205f54910bea8465df324c3d843106fd4942dfa14637c548c6faa7a0df95221ef2a6653d5490bba64a07b54810bf286877c54887bc85995f94841dea0081fa20442daa40877cca10bf29c817e518827aa998f7d5132fd280437d5210ebaa62077cc230ee99463f541c42f8a99977cca20f6990657e501027ca8185f15130bea8483ef20082dca5a0ef94342eea18637d52d07be6598f794f21ef298436e52102fea098fd8c510bfa9a83fa2008278a8985f14520be2a421dd310c6faa5186fd0940be2a4657e53486fca8185f95110bf2a241df32c82f8a0a16f94f42bf28683ee320cbdaa4187d94440ef29885bd4210bbe6510ef15130beaa6437e5010afaa8187755132ef992817e50ccbba6590fe84010bd28043df32486fca8987714d40bb28841bc5150b7a8420fd90441dfa8e857c54cc3b88698df14f10ee990617c524c2faa620df94720f6908433d540c2fca6185f54e31eea1665bd54cc77887a0dfd4943f6990437d52d0efaa308774cb41ee992417e51887bca6105fd4f20ef182616e5210ebca610df54332ef99463df514caf8a6907b90a32bf28c657c54487bc87987dcc631bf29e83bf41906fca6087b88420fd10421ee32086fca1105f94f21bf2a081ef20883bea4996fd0830f6a10437e500877e84906fd0d42f721265de544cb5a8410fed0140f721641bf42ccabca6105f95021bfa9843de434c2faa4086f54142dfa16837e5290fba64a0f7d4d40bf28e61df310c6fca818f714732df28e85bc43507f641105f94210ef994657f5150f3a85997d4c431faa0a217d53d0b7c87a0ef50b10fb20e217d53487baa720db94b31bfaa0637f544c2fca9196f90541dfa12837e53883da43905f54e30df2a0437d548cbda65906f950309f2a0437e52d06fca4204f95232bfaa021bf43502fea0a17b54b41bf29e817f52843bc62185fd48109eaa4656d52102faa9085f54e41be292813f544c2faa7905754c21ee21e637c544837c86a0df55121f710c417e50083bea6886fd4f42aea9c85dd4310fdc8510df95332bea98417e53442fca4215f94010ee990635
  | 3 => 0x100477000000ec0003c070a00002000000010301c0202710803108021643100c9501802040051705700c4701c050040004c01018081780000c15014bf05425014020cc060042b0280000802054240040a04401084260100b00808038020b40b000010248241405018200680906c060440c2bc0b0180f000021b00706ce60080904c0403041094070000201401048460d8000000101402074030080407c00020040949700880028000180c00c08100270340600002014453bc1a2b01b00400264001e4000000001401048061f4010080207c090102e00000014000080100c341685702408040005a4110a400118000041e018091100400c1a010401e8011b006034090883600c5202813178010300101803004050001801c4f0843c0501114c0201c090e4100247505401004c508c0010f2601402000000000401c0001c280
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x2530423d6414e10e3509324423e6414a108f99252443553294430e3509325074c52cc9109d587540825f65cca41c758c544c23d6494b10abd95428cb4d53480209b988540c71e53d0a428f588544431d54cc830c7d4f425032e64548408f99353c865e63948219758e544874d52cc030ab58853d0b2e52508409d584530825d6314a10cb50a518ca3d6494431c7151434c31e544c810c755054cca5d63148109758e54c432e5494810d3988535034d524c030d358d52d065c65cc910c754f42d065d6394a40cb992520431e54ccb20d318f52443565394420c794d42d078d424c8319bd89544425f6355220cb591520423f6454d10b358e32483595394021cb195428866f654c832f14ca21c427a60150219798e544427765440109b98853502766114143d354e520425f6254e419b98a53906776550441d3d4b324423d64949109b189534423c64542219b588548427465485108f99742443c73248421e350932d033542944209d98454042766114c209d984504ca9e64143328fd954310fa94248110c7551320871d53d081097d89530829d64141329d98754ccb1d5454c20d394932903355150040cbd95428871d544c820a759331cc32d5494b319798f5150a3c6454e10d354d4210b1f544c910b35885350355518c4309798e548877221540219798c540838d424cb20c795253c865d6394b10c795153086cd6390b20d354a310c355514c030ab58f5250a7561d5030cb590524438d424cb108f597420838f6550932cb952520c25d6294c40a798c50d0a5e63d50218f993520429f6454132c755253c825e6314a10dc546200825e6394742e3509324c31e5450e31e3509328c6cd63c85209798e52d066f65480209b58a544423d65d0830c754d42102b56114342ea50b204834f544c920c794d420830d4354843d3549328425d6314940c758e548c66d629523197595320423e641493097997325023e64141318f593520438e43509329798c504873742944309b58a53c434e524cb41c7153534425d6314142a718d50d0b573294440e350b328865f654c431b358a539063c6454630ab5835250b2f5250940c7553430c25d63d5320cb98a540871d54cca318fd9153882cd62cc431cd546411038f424ca21cb990524431e54ccb21b3588434c76552544408f997435025d6394b418f992520cb2f5250931b3d89544ca3d65d0821c714e405034e5394b41d3d8f524432e5250b3197995324438d424ca30c794d439065f654c8208fd91518c29e648c4308f197424c25f6354041c7d53324c23f6550b319b588540c23d6414910c754f420869c644c030e3d4b424cb2d62151309d584540c33942540218fd89540423e6494a108fd954210b2d42d4132d5cc951083655108420a3592424ca3e64947309758c540865c654c940cb951520423d6494820
  | 1 => 0x434d524cb4197597329066f6254630c754d429071d5410f319718d519034e52ccb41e350b32c825f6355210d398d52cc65e6314b10c794f420838f424cb20e3595424ca9d63d4542a759351ccb1e5494f20cb59252cc63e6494732c7551320cb4d53508219758e528434e63548409b98b530435551cc0309758e52043555344010cd55151082756114142c750e5110e3c64549109798f540838d435093297d8d518825f654c810d5cca510c25d62d4d408b58a548c6756114e208f592520c32d52d0b4197d95300c34f524c931ad5865350b2d5408420c754f421023d6494831d394932cc754538c510a7592424ca5e6314941cbd95424831d54cc820cb55152cc6d4614c9319e583530878e6550932cb54d424832d52d00408f59052c425d65cc8109798e520838d424cb30ce95150086766114e20cb949420434d524cb409d195414432d5454810cb59152cc72e5454830b558450cca5e6315120cd5445150a5e6314810c754f42c823f65500409798e54c42cd6210f31a7992514cb2d544cb20c794f429065c635404197997434cb6652544309798f54c872e52d0b319b98a524425f654c8329b588504c63f65d08308fd89540c27b654c030ea50a500863e64d4532c718d540c31c53d05409758c54c878d43948439e980530863e6494820cb949428c3355110440cb149425069d63d0641e3151424ca5d63149418f58a540423d6414931cb50a51087556114d108f994435063e6414e10f14ca21443ab6050920dac85500871c5414d10d355132c829e648c5318f99353c42e96008620c7151314c23d64d4c10b3986424ca3d6494d109719532442cd62cc7308f997415034e524c8309758c54083365494420e3d81424cb1d5350b218fd95420438d61509328f99052c423e64145209758f548872d52d0b409b988540434e6394b418f58b544c29c635004097594430c2ad64c8520cb508514caaf655082197595321034d544ca21cb54942cc76852881109798c514834f654c821d3551324832e5450b20cb54942cc23e6414e20cb549420c2b561d4f42e3509320872c52509318f590534825e6314c219b988540cb8f5450932a7d954310f2d548cb20cb94b420c31c53d09109e596100431e53d08429e58053087573254440b3593524cace65909329758c540423d64d4c20a799251ccb8d424c8309e580540866e65149108f994544c34d6394b41cb553200827b6550040d3549321072d5250810c7952530834d53948408f191500c71c53d0d40ab592328863e6414c209b5885050e3d64d4f20c754c43d063e6494821f24c950087656114910b3195424cb5553c4010cb95252cc63d65950309b58b54cc74d5390b20d5544310c26d6295131ce552500863d65d0810cb90d521034e5354b41c754c53d0b34549051097195434ca6e6215330c795
  | 2 => 0x6210f41d3d51320871c5450c31d354b320c6ae6290d42cb14942c43c7614ca2197d95329065e6315321c754d401024d6214d40c7d50438c2cd62d5332cbd50524432d5250a30d9549510c26e62d5331ab58b41502cd63909209758c544831e544c832cbd4d420866d62152308f992520434e534c82197596530423e6415010e3d91424ca5d6294f419d9845050a9d6494732cbd4d42c82ad6210c409b588538438f6250932cb591520c34c654c920d954b100438e544c821c7550310c3a76150a21a758c5050a5e63d532097997314c25d63948409bd89519023d6494821ab593218872c4354b41c7553320871c63553319758e521074e524cb40a758f415032e5454b31cbd95420872d52d0b31cb54d420865d654ca419d185544825d65cc84097d8d50d0a9c6454132ced09500863c64543329b98b540c31e544cb3197d8d524427b654802097d89531031d53d0b21cbd53524438d424c931d394d52042d46154132a7d8d5050b8f424c8218fd9742cc70d544cb209718d50d0a9e6390640cd951510c34e524c840b5587320c66d62d45438f596540874d5354840b3d9532c831d5494c21ad98450d0a5d63145209e980540c6cd6215332add855050b1e5454c208f592534874c4354b31c7552310c31e544c830d398c52442ad62d0641d3549320432e52508209718d544433554c4010d394e521026e62152309b596420878d42cc821d398e520425f65ccb41c7951320825e6315220cbd95424ca9d6490c43a798f5150a3d65904409d984530426d62d5010c755153c838d424c921c7951328c72d52d0830d9545200831c5450d32cb193524425e6510932d34ca510874f5314910e3509320823d6595020cb54d428871d5494c108f197424425c63551209b98a54c431c544c9309758f54c423f6550821b598450ccb394294021a719150cca3d65d0b319b98b540432d52d0810cb195424823e6494a308f590504ca3d6414930d394d320cb4d538842097596530863e65d0930f24c920443553294420cd552510c23d6295030e350b514ca6d6295310d554e510823e64d4d21c7550544ca9d6314342c7551320423e6414d20d310d520c23f6454d20d64c9500871e53d0b41c795332042cd63c8621c7551300c31e5490e31c755132cc73742944209d584548823e6414c218fd95431065e63d4810c794d421034d6214d40cb949428425e6315210cb552520431f54cc9109b588505071d5410d329b58a539065e6315320a7990504cb4e63548108fd97428c69d648c932cb59252042ad62952319798c524425e6590d308fd91538432d42542219758c52c429d6394742cd509510c31d5350820c754c431032d4214520c750d5210f1d43540439799453442ad6210e40c794d420434d524ca40f24cb204834f53d4910cb991520423d6494a10f24c9208
  | 3 => 0x821d3d0d520c32d54480208f592528c32c43548408f990504cb36545442097195434c3665294440e3509325026e6215030d354e52d074e4354843d3d95324835551147329798c530834d52cc810d314c524429d6390942cb592520c36551884208f596540cb8d6050932c714d425034e53548409d984540825d65cc8208f990520435a53540219798e51d025d6395221a7592514ca77654c431c7953320c2ad648c821b5584504cb4d3254221ab58b53d0aae6210d42c755132c878d424ca41d398a530872f52509109b596320874e524ca10d64ca500863e6494e21e350a514cb1e54cca318f589540826e62152109e195204425d6394a41c794d42c871c54cc930c755043ccb1d5310440cbd4942c423c6454d20b5586544ca3c65509109b988505063e6494a31cb54b421025e631414297d8d544431e5454f2097d97321025c63542219b18954443c53288421c7553320436a4254021e3195424cbe22188110e3509324838f63509329b98a53442cd6210e30d5cca51082cd63c8720c7151324427661d5030d394e520431e53d0840d9549100426e6214e10c7553328ca766115030cb58a548c65e63d5031a7d9150cca3d6494b30c754d4210b553254430c7553300c23d6494732c755332cc65d658c430b3185424ca756195132e394d42c831d53904409758f520432d5350b209b997214823e64948308f990530425e6314141d354b32d065d6294c10b5d85504ca9e63904408f191538838d4214132cd50a511031c5350540c755343cc74d63548109798c540ca5e6510d31c754f429063c6454d109758e52083555394440a798f51d0a6e6214c20d594d510834d32145208f595420431f54d4d10d394d32c823f6550a31e350d5210e3e6414931cdd09510c26f65508429759532d063d6414121c794f4204355511453297597320872d54948309799532503355444010b3987524cb8d4294132cb98a548c74e524c810c7553320cb4f524c9308f593534866d6588420ad98753d0a5e6394d10d314f5244354435443097588534425f654c840cd509510834e65909329798e52c434d5350b20b398b434cb1d5454f21d3d51328874e6294e42b3988424cb1e53d0e41e350a324cb2d52d0841cb549429038c4350932a7990424ca3d64d4f219798e524433643544409b588544c25e63d51219b195424cb1e5350832f24ca500874e524ca30cb94b420438e5350821ab592420865e63d52219798e52906b66194d42d3149325071d53d08209758e544431c54cc530a758f411071c5350d42d3d95328874c524c931d398a53906ad648cb209758e544c66d6214d408f994544423d6550a31c7953318c66e6215130d6cc9500866e6294f108f593530867b65440109d987530825e63d5310d398e52102cd63908219358a539078d544cb208f99253c42ad
  | 4 => 0x3d81424cacd6210c309798e529031d5410c30cb99252cc69e648c630f2181324825d6394b40cb54942843553254420e350932106776154d20c7153324431c548c130d5cc9510c27960d50219e983530871e53d0b218f990540cb6952840109b58b530436652944308f590520438d424c840c7d51324c32e5450842f8485204435653944408fd91508869c6354142c7953320865d65ccb41d54ca511038c6050932e3d49424cb4f524c9419d984548826e6295131e9185428872d5250040d554d510838d5350b209e580540c65d6314141ce952500865d63d5321d5d0d510c29f6250c43d654d50086d561d5332a758f51d0acd638c8219d185534829f6354342cbd0d5210f3742944408f993530832e5250b41e318d424caad62151309bd89534434e524c841e350b324834d53908428f992530c7374254420b558e41442af6254d428f59053c874d524ca30d394b32043645288510cb551320878f435093297588535031f5414d109719732502cf654c8219798c540866c654c9208f99353c831e53d08329d587530831f53509109b9885050e5c6354620ab58b411065e6394810d314932c432e5250b30a7d854310e6d6215331b5986544ca6e6215020b358e428863d62d5110cb99152d071d5310f429d984548c27a60d5021d554d511032942540219b596520431e53d0641ab59321c834d6294e418f58a54cc7715148020e3509320ca3e6415020ad5845050b2d5454830d3549328c71e5454f218f58a548c71e5454c108f990540c34d6314910ea181424823d6494a31c7550434c63d65d0a319718d548825d6590c31cb54a411034f4354b31a7992324ca3e6494431d3551320873542544409798e52d029e63947428f992544c33b4294021ba580210838e544cb209d984520431e5350b2097d9532d06756115020c754c5350a3d6494c319798e521066e6214131c715143ccacd63c8421da485500865d6315220cb98a548ca9d63945428b588544c31d5390f41d354b32cc65d6394742e3509514cb1e54cc832c354d42c834d53c80208f992520c63e64d4e218f596540432f5250941e3981424cb8d42d41329798f540cb694254021e3d85424ca5f63551308f592520438d5350821e3d8942cca3d64948328f59251cc23f6454332d3949320832c52509109b189519037121540219b58a534425d62d4d109798f540434d52cc830d3549321031c5350d4097d8953042e56190821c7953320833551d0040c755132c82d66114132cb50a51c825e631494097597430c32f64d4910c7551530866d6295121d354b32cc31e53508219758c524434e52cc840da580524431e54ccb318f592538863f6454910d398a53c832d548c821b558e41c423d6550b31e3509329038d424cb31b358a544ca3e6550910a7593514ca3e6494b31cb509500871e544c
  | 5 => 0x524423d6414520c794d4210b8d424c810c7551530432e6215130cbd9542c83344354440d358d521025d63152108f990524438c6150932d354d52d07c4614ca21d594d511023f625533197d8d508865f6254f419b189518c25e63948409718d548423d6414c109b19542483553254440c7952530863f6550832c714d424432c65509328f593538866d62d5030d954a510c25c6354910cb50d5210f1f6550c439798e52842ad648c920b3582424ca756114132d358e520431e53d0b20c7953328ca5d63947408f590538827a60148109dd95210869d64cc4318fd89548c63d6590c40d3149324423d65d0832cb549429071d5494f21ad185425072e6494830e3985424ca3e6494b10ab58b41d03a94248210a798e4250a9e63945428f191518831f5350940cdd09511026d6214c10c754f401029e639054197996424ca7661951328f59252cc674654c510cb548411025e65cc910cd952510c31e544cb20cb552210825e65d0d31d398d520c38d424cb21cb551320cb4d3254021ea509500876551c8020cbd4d428869e64d4732b3583524cb2c54d49109bd95210872c52d0910c754d42d063d6550830cd54451d0a3e6495110c715143cc23e6494b30d3d9532c82ce6210d32d398d5210e3e64d4c219d584548c2b661141429798c53043cb604c920c754f4290a9e6314142cd55251083355454430ab592424ca6e62d45439758f5150a3f65508209d5845050f1d54ccb208f990540875b3294021a7993514ca5f6354640d34ca51c826e6215331e3509328825e63951219b988530425e63150309758f544878d42145328f99053c86e5618c821c755332c87693254021a7593314c25d6254c20a71814310ece6550932cb949420c66e6295231c754d420425d6594c20d3d49324426e6214810c354d42087655294440ab59242482b5648c710a7593318c74d4354843c714f425031d544c8308f992534423e6414121ab593210872e4354b41cb509508cb2e6295320d354b32103a5428871097d95320866d62153308fd91518823f6550441c754e431031d53508219b588540c65f635512097d954310f6a3254021c7152434c34f524cb10d398d52d06b46154142ab588435072d548c832cbd4d424823d6414a10c794f420865d63948219758e52443a74248421e3508424cb2f52d09108f993530429d6414332b398e424cb1d53d0842cb951420865f6550c31c7552530823f65508308fd91500c63d64d4f108fd97420426e6295110cb94942902af6550b20a758f41d023d6414c219758a539072e5250832ce551500865e63150109b58a53486cd6490932d9949511031d544ca31cb991520c38d424cb41c3551320865d6315320e3509328871e544cb218f99053c834d53084208f59053083354294430d3d5132c832e645484397d97320438f424c920b
  | 6 => 0x8741002c000500020c8270290120000a8090022e00089976002c000461ae000010120344600300201203c0a8df0020080000d3521940700a00e018010003b80000000700656c020021a20a017800080008031be00a0000387104001c010060100001b80302408c020080900100000201a034010000a001c3880b01201c1d803052154000bb0b20000c0040383e401000556014018020560000980506e0540380006c10c268f402c02c1d02e002000058d80261581603600e0044583a0820080bb760081f802834084050318130280002c81900a0cc030040141c0008050000040300107a31400000006020108190ec018148001de00c0e8030507003680002c14c5d82c03a03c0e89a00038c0080e0001740100103a08416004002000000ed00e050b2afd02c010098060000800282705e010270320020cc00000002010002b80a2f943c81b00a0980000b086020031b79200000000100404c1500d04e0242a00b03400c2201a058014010020000d80900200a0000302802402c088013ea108330911320000180c0480000000014c0380980409a078070213d000c0003d01a010848000020040007c0160000400004405c06002002050138df12c0800084e07a7280002306e004000110562c00d80204e1b00000b0000140382601427c060b90360240400a02a0940000100412804a0b0c80080381a09206c0d0400840040480f0000002d01e03e1100280101a0e4008000160001402b026050578950001d8038834282a0010060080c4198010c0400060001e0014000030000001604403e01c3d05f02a0500202a0000404900d0080041300c0020e802000028004008000140080e0000004040680007c0c00d03de355132087a542884218f59053c832e6454b31cd584544425d63d5010ab58a5350b4d6394840d24c9500867561d5332cb549420c6b5648c510c794d429065d6314121ad58742106ae61d49428f590504c74d53548109758f540823e6550930b598754ccb4d520c430b358b314c38d424ca109dd85544825d63d50219d987540832f6550a32e950a214423d6494f10b358b318c74c654ca218f593514ca6d62150108fd89540832e5450a32d354e420863e6494d218f588544c31f53d0910d694e500872e5250830c754d42c836952440108f195424c38d4254132cb150
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x9950d725513208286b94a6a168383995424c940e1284994a010e49635805244286b98caa1241511c5544c920a1eeaa12641050d7414932c4382a126528841435ca5350e41b08e2a1264a0e0d7458a539071432a849022183d8d4254221a2ee2a1ca221e0d644c851483062a2c598a614add54254021a1ae92926598c2c7654d4248216b94c9a9e210b5ca64d4d21e14a8992a010c4d7218d5484391a1242a8043c250b3254021d0a8430a6498d0d74949320c286b90a999261525cf2154021a32e02a28618f0b424c950086c338ccaa126543dc94354843a1ae529e8520d0d7314942c4306aa2c42a665435d65350821a1ae429c80a050f75509320c382a126528881435ca54cca31e12a6a14a010e0d655093204382a126528861835516210d31a1ae42a2648848d7298e4190286bae8499043235d261d4932a1ae9292641052671d95424cb06b9ac52a463071d9544c030b08e2b028499561718c95008647bb2842826583191524c03085ae4322a70850d7214d435024ab88c0a18878354d6210f41e826510aa010d0d72152434c306b22c7290218359542cc821c1ac6b14a918d0d74d95328870632a8499221435ca5490e31c52a8b00421060e655093244286baa8499021835516210f31e12a8992a010d0d7214f4150286b98a4a1283435c8548c130b0ae3b2a849950d7294f4190782a12a228a65235cb6150c43a4ae3322a421e0d5358853d0a46b94c918c61435cf6550a21a52e9192a010e0c5358b4150307b2a8499081d0cc92154021a1ae9292640868542185504cb24a9ac010841131d9544c920a1ae7292842050f7650d5210e86ba0a499221705c4604c92083eecaa4621850d729513204226b94c7aa243435d6544c821c1ca6b168320d8771581424ca86b98a4a122123dcd60d4942a1cebb0a849950d739494290330b0ac029221439d5424c910a1ae42a6629850d7218d540c286b94a6a1021c25513294021a1ae7292841048f74583524ca86b90a8a1e61835d16214d4091ae431a8020629645805244306b28caa126585991518c430a92e1aa26410c4d7298e51d0306b22c6a902123dd942d453291ae531c822058571181424ca86b94a998c63921953248110a1ae529a8520d0d72951328c687baa84996638395162cc631a1ae42a28618f0a535095008686b90a7a1a81525ce4254021c1cc6a94822052970d4d4208686b94a6a1081435d2524ca30a1ae429a82a05247154d42482a5baa64a80438358d421452091ae43028621f05424c9510830631aa4a0081435c85350940b42e2302849048d7298e415060ebb4a998c6383d95424c810c1ea8b10871850d7295132cc687b8a86a9087319c66550932a1ae52a28718e0e73588544c20ebb0a998a61a15096114132a1eeaa1aa421c8d72191300c226b94c7aa621511d53288510
  | 1 => 0x21084800020200023802000a012b0101aa110700002922000003001a000132025a1204022000153007310103530301021e000008040009030000050000130505410208000204030b04023200083800030118080b4b1600140400000001071d000100030f060b0a0001070d1006002d36070500071a19c18caa1a849950d72151434c286baa84994638518d5150040c2cc6a8c822052974c8550086923aa8510a21515c66354843c1ce6b14a918c8d72992310c390a1442a804383d913254221a18e0a1aa421d0d74149324c626b90c6a8083a150a6114132b0ae332a849960d63588544c2863aa8499221c25093254021c1ec9b1ea48850d72151324c306a9ac421881839d16214d40a1ae832a649050d739494204306b22c629221835cd6215130c1ecaa12641050f7550932043073a2c529c83435c86355331a8ae421aa21848d739875250b0a322a2980610b5ca6494730e0a84992a22048d72992314c616b90c8a8063439d5424c930e12a6a12a010f05424c9510c307322a518861619c46050932a1ae529e8720d0d749493284286b90a898a61435ce5250a10d0a85b0aa099561719095008686b90a7a1281495c84354440b0ce3b2a849950d72951320c306b2a8499483435c85350910c1aa8b10861860f6550932d06873a8c0a1265435ce5250b41d0ac230a84
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x7060010010080d8715162cc53080d87991528c430a058218d5150040a058298d5190440a05819cd6215130a05819d16214d4080d8795162cc631a05819d16294e41a05819cd6295231a0582991518c430a0582191514c030905811c1435484380d87191524c03090581dd94354843
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 890
  | 4 => 1340
  | 3 => 228
  | 2 => 14
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
  | 7 => 2*((h/1+packedAt s5K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/35+packedAt s5K6 (704+(h % 35)*6) 6) % 44)
  | 5 => 2*((h/310+packedAt s5K5 (24030+(h % 310)*10) 10) % 890)
  | 4 => 2*((h/453+packedAt s5K4 (50920+(h % 453)*11) 11) % 1340)
  | 3 => 2*((h/118+packedAt s5K3 (11172+(h % 118)*8) 8) % 228)
  | 2 => 2*((h/11+packedAt s5K2 (840+(h % 11)*4) 4) % 14)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfe1ffff0ffff87f83f0fc3ffe1fff83f44f3cf
  | 1 => 0x3fe1e1ff0f0ff87fc7f0fc387e1c3fc7bb4d33
  | 2 => 0x3ffe01fff00fff8ff800ffc07fe03ff8c38e3c
  | 3 => 0xc00001fffff0000fffff00007fffc000fc0fc0
  | 4 => 0xfffffe000000000fffffffff80000000fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x2000010000008000001004800240800001045
  | 1 => 0x84484222241500814310441122089286194512
  | 2 => 0x2884954442aa441a9888aa8255412530c28a28
  | 3 => 0xa1d55988aa83552cedaa220479938192ec0f80
  | 4 => 0x3119910ecccc664f36ccf32711020624f7e000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xeeeaeae8eeeaeae8eeeaeae8eeeaeae8eeeaeae8eeeaeae8eeeaeae8eeeaeae8eeeaeae8eeeaeae8eeeaeae8eeeaeae8eeeaeae8eeeaeae8eeeaeae8eeeaeae8, s5N, s5R, (fun _ _ => 0), s5I, []⟩
end PEqualNP.Outside.L_meta_36881
namespace PEqualNP.Outside.L_meta_36881
open PEqualNP.Outside.L_meta_36881.Model
def q2K8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def q2K7 : Nat → Nat
  | 0 => 0x3031000400404c000b1ce09e0040801c0543200fc42fe10fc41fc20fd31fd32ff30ff21ff10fc40fc32ff31fe20fc43fc31fc21fe30ff42fd30fe31fc30fd43fe43ff43fe42ff32fd40fe21fd42ff40ff20ff41fd21fe40fe32fe41fc10fd10fd41fd20
  | _ => 0
def q2K6 : Nat → Nat
  | 0 => 0x63fc42d06faa021ff54520bea9c63fd32483fe6518ff14241fb10a21fd4350beca2107fd0f10fe90c617f53083fa84995f15220fe292877e5210bfca5a1ff14341ffa02817e53082f8a2907fd0a30fea9c41fe42107fe8690ff88510bf290417d52cc6fea8987f94943ff212653d540c3f883907fd0020ff29e83fc520c7be62987bc8220ff19041ff10843da4210ff8c940fe21681fe544cbfa6210de94021ff20441fc52d03fe6590df55321be29a85fc21c82faa890ff0c910fe28685fc5090ffe82907f0c540ff98221fc31083fe64987fd0a42bea88617f53c43fca898fb94810fe21063ff540c3faa5a1ff10932baa88817d5190bf880107fd0921df2a041ff51103fa64a07f50d40ffa1641fc42103de43907f10610fe29021fd43082fca621ffd4121ffaa643fd4310bfe43207f90c41fe18621ff31c43f8a0a17f94620fb20e21ff5250ffa6290fd50441bf28021ff40483fc64907fd0f42ff20e21fe43087fe81186fd0e43de21a85fd41c43fea1217fd5210ff28265ff54c83fc8490ff50810ff29e41fa50087fa43907f50a31fea0881fe52842f8a710ff10120fe18a41ff420c2faa1a0ff8ca30faa0e21fd54842fea2a07f94243ffa0e41fe438cbf843087f94143bf2a4657e530c6fca220fd4c431ffa8e877e500cbfca598ffd4a10be29a437e508c3faa120ff94343fea1a417c53883f8a3a07f8c630fe18c61ff32883fca0a17f14542fea1261ff53d02faa8885f15032ff20883fe42d03f881187f50e30ff21e83fc43c86fca720fd90441ffa9081ff40c83faa998ffcc421ff208437f540c7fc87a07f54042ffa1663fa20083fca018ff08430fe98881fe518c3fc659057d4d40bfa9287fc5150ffc80887f48610fe992637e54443fc85197f50010bfaa241fc20043fa6218ff10a31ffa1483df32cc3fc62a07f90831fe21021fd42c86bca6087f8c420bf29021ff52cc7f863907f4cb20ffa0c21ff43d03fea6a05fd4543fea1a637f540c3fa87907f90840fe206417f54042faa920ff50e42ffa9a85fd51082faa3207fcc521fea9a21fd41107ee8320f7cc832ffa1881fc424c3faa2207f95330faa8841fe50507fe87197f94d10fea86837e53902faa8985f94830bfa8a65ff41cc7faa4087f50130bf28043fd30083f420085f15021ffa18637c524c6bca610ff50421fe29083ff410c3fe81087f4ca10fe90021fd54ccbfc62907fd4543ffa1a657d53083eaa2207fd0d43ff218817e51d0e7ca8087f8ca10fe20421ff425077c87207f90c31fe28465fd42883faa0a17f10d10fe18c217d54086faa818f794c21fe2a043ff32443bc64997fcc740ff18021fe50086faa998df94742ff98c63fe53503fea098ff54d42fea0a43ff520c7f8a9185b54840ff21a877e50d0ffe80186f50842ffa8683fd43843fc83a07f8c531
  | 1 => 0xf41903f8a0997f95232bea8083fd320cbfe8698ff90d21bf29865fe5190bfea1196fd0b40ff98a41fd41083f860905fd5021ff99083fd41502f8a910ff94d21ff20a417c54cc3f8a2215fd4e10bfaa643ff524c3f8a720df14c20ff21c85ff53487bc6298ff54830ff18c43fc42507fc42987fcc630ffaa043fd310c3fca2a1ff8ca40fe98c21fe300c3fe6410cf55232ffa0481fc414c7dc65905b94810ff10821ff42ccbbc86987fc8210ff21421fd53503da65906fd0740efa9a81fd42c43f86518ffd4732bea8663fc51d0bf8a7887f90f20fea80837d500cafca7087fcc010fe28043fe51c83f88690ff0c640fea9841e521087fc63985f14810fe99481fe40103faa690fdcc531be2a261fd50887faa6207fd0641fe21e835d53082fea6906f55030fea0a41fe42cc7fc8298ff14f20fea1c81ff31c82dca4187fcc921fea9663fc30c83faa5a07fd4142beaa485fd418c3fe8721df14131be2a063df434cbdaa4085f14132ff28e81fe41c83fea8907f54c10ff286437f548cbfea190ff54a41ff996837c5250ff864087f15010ef98863fc43d03fca3996f95231ffa1e63fd42107f8a8887f54c41bf29485fe43cc7fe60987fd0531ff21c217d53107fe8618778c130fda0281fc324c3fca021df94c40bf29a41fe430c3faa2187f10b10faa8861fc20c42f8a610df94730ff294637c54843fe8720ef50f40fe20a81fd414c7fca4187fd0942fe29e817c53c83fe65a07f10c31ff98c21ff320c6faa7a15f54620bea8e41fe52903fea421ff90941bf2a265fe5210ffa83907f0c210ff99465fc210837887207fd4443fea12437d54903faa8107f54c42fea18877e54487fc43107f90610ee99663fc54ccbf8a021ffc8730fd88421ff30883f280207f90821fe28a81fe51083f886985f54a43bea9083fc410c3fa41887fd5231fea8687ff324cbf88420ff90010ff20e637f5150bf8a610ffd4f42ff98861fe524c3fe84217f8c640fe29263ff43507fe83187f90430ffa8885fc21503f8a321ff8c310be2a641fc218c3fea5207fd4e21ffa8e85dd314c2faa4087f14f21ffaa661fc42087ee4310df94241fea0c21fd53d07fe4310ffd0940fe19441ff42082faa7207f15310bfa82437f548c2faa5107fd0540feaa463fd53d0bfa42a05f94f42bfa9c41fe52443faa2197f4c710fe20a41fd21483fca910df94f41ff202617f54083fca3a1ffd0a10ff29281ee20483f8a8997f10731fea16817d520c3f88718ffd4f10fe21465ff520c3fe84907f50840be28a87fc21483ea63887f90b10ff2a241ff52d07fa42107f54730be2a621fd41cc6eaa2187fd5232fe21243ff500c7fa63a07f50831ee98061fd410c3fe41887f10c10bf29661ff32043de42905fd4931fe19643fe51483fe82105f54843fea8283fd53886faa2207fd4530bf28
  | 2 => 0xfec43887f50a30ffaa221ff544cbf887087f94a41ffa86637d528427aa810dfd4940bfaa065ff30c43de84a17f94d20df21881ef328cbf88798ef90d43be29e437d54c43fa20087f14640fe2a243ff43106fca4207750c43ee21a65ff32843ea20087f8c510bea8465fe5190efca210ffd4941fea0c81f631443f88310ffd0621de21e83fb20483f8a620ff10d32deaa0437d52903fa80907f54640ef29c83fe53903bca6205f54b30fe28263f621087f884907fd5020ffaa663fc43907fa8498ff14732feaa461f710843da43907f48020ffa9263fe4250bfe43107f0cb10fe10e617e530c3fe6598ff50b20ff10843fd32886baa720ff10730b6a9021fd30443fea110fe54021fea0461fd50cc7f8a7a15f14930ff18041ef21886fea0a1ffd4e42ff10a43fe54c87fc83185f55131ffa1443fe53843f885187f55321ff90a21bd41d02fca5197f14830ff98a63f920843f8a3217f90830fe19683fd5150bfe85985f54c10fe29a857e54c867ca918cf55020ffa1a857e528c6faa3195f95331be2a0217f54ccbf86420db54830ffa9461bf544c2fca810ff10b20fe21a83fd31503f8a190ffcc941fe988417d53d07f8a020ff54720fea1421fc54c83fc84a07f90d42ff21041fc424c7fc81887f50320fe190437f53c82f8a6907fc8020ef99261fc53903f8a1997f90842ffaa461fe30483faa2a07f14031ff21461ff43083fc86107f10b31fea0061fe54087fa43987f90d31bf2a065ff420cafca8107f14a41ffa0e617d53c83fe86a07b94830ffa9687fe204437e8220dfd4941ffa1885fe54c42faa7107fd5221fe28a417d5390afea918ff8ca21fea16637e5010bf681207fd0f20ff28c81fd54cc3fa63187f88740fea1061fe43502fca3107b48520fea1483fd31483fca8087f0c921bf28081fd508cbfca6107f08210ff296817e508cbf8a1217f10640ff21241ff51902faa6205f54021ff90241fc43c43fc86217f50210ffa0661ff51503fc82a07f8cb30fd20081fd54042fca520ffcc840fe18c43fe30c82fca8187f10a10f7a1485fe52102faa5a07f50f30ff98841fc21903fc42205f15132ffa98417d53443f8a110df94d10fea94217d51d0ff865a07f0c730bf28665fd43887f884187f54021fd98261ff43482faa918ffcc540ffa14817d53487fca790ff50821fea94877e50883f860107f4cb30fea8a65fd53c43faa9907f10330beaa665fe320cafca9887f90420ffa1c61ff53c86faa1997f90931dfa1683fc418c3dc64907b4c920fe98e41fd20842fca9907f54543bf28c87fc5310afaa610df94e43fe21883ff5050ffc86907f14c10ff21641fd21902fea690ff0c840be29e21fd430cbf86418ff94241fe292617f54487f88610ff8c931ffa9221fc528c3f887a15794e41fea0621ff4390bf8a2205f54f10ff18421f
  | 3 => 0xa8907f14331fe29e83fe40082faa3087dc8521bfaa443fc328c3fea8987f10510fea9c83fc53483f885207f14443bf28485fe420cb7e82a07fcc320ffa9843fe42cc3fc65107fd0f30ee98863be41506fca8987f94b30fea1c415d5390bfea020ffd0721ffa0441fc544c3fea0217fd0e21fe196417f53c87fca6085f15020ffa98217c53503f86498ff94342fe288617e5110bfaa118ff14a43fe10a21fe31043f8a118dfd4530fea8a615d53103fa86185f94f21fe18c417e50d0bbca6107b90920feaa265fe21843fc8710ff8c530fe29a43ff42443fe6310ffd4e40bf28643fc408827ea8987f90120ffa86657e520c7fe43a07f4cb21ff20461fc52902fca9087f14620ff19643fd32883faa321ff54e40ff2a063fc4310bfc8310ff0c721fe21841ff430cafaa221ff14143fe29c43fd50c87f8a9197f4c010ffa9e41fc52cc7fe61087fc8440dea0081fe43cc2baa610f74cb30bf28683fe52c42faa2217f48510dfa1485fd5250fea428877d0e30ff10861fe51103ba8798774c832dea1a81ff32503f8a4887fcc830fb28881ee320cbf8a6887fd0510ff99041fc42ccbfaa9107fd5310fe194217d5090ff88698ff90a40ff98e61fd5390bfaa7905f94a30fe19663fc52c42fea4887f90320bea9e81ff300c3fea6a0ff14c20ff21c81fd210c2f8a8885f94030bf29621fe41cc3f460187f14632beaa641fc54c86fca3217fd0931fe21a41fc320c3fa84a05fd5310efa1a63ed320cbf220085f94720ffa80653e548caf8a5885fd5131eea9843fe500cbfe80887f54743bea8e65fd504c7f886207f10e20fea0c43dd53083fea9107fd0e40bf2a021ff32483fc64886f15130fe21c61ff528c6faa8197f54d20ff100217f544caf8a898ef90f42fe19483ed520c3f862885f95330fe2a065fc51083fc63107f94e41ff2a641f920083fea3217f54b10bea8483dd53102faa8087f10110fea1a21fe520c6fca7887f94941ff99461fd41cc3fa84107fd4542ff2a663fd32443faa6a0ffc8410ffa9487fd5010ff884a07f54931ff20421fe53c43f887217fd4630af29841ff500877a8220ff50842fe290817d50d0bfa64107f10420fea9087ff4310ff887907f90f10ff18e437c54487faa4887f94c41fe98441df4390ff8a2985f54e41ff28263ff324c7fe65906fd0f40bea9621ff319037c87a0ff0c941bf29c85fe50d07be65195f94910ffa90837e510cbfc8520ff90b32eea9821ef324cbfea720ffccb10ff200617f524c3fca110ff50941ff20c81fc430c3faa7a05f14c10bca8043fd518cbfe42987f10820bf29681df43cc7faa1a17f95030fe29463fd400837aa9197f15210be29c21df430c3faa9887fd0e10af29881ff53843fea6905fd4d41fea1241bf42507fca7107f88710dfa0c83fc548c7f887196f95232fd10221fe431
  | 4 => 0xfd8c710be28a81fc43ccafea098ffd0431fea1a43fe524c6f8a0a17fd0d10fe99243fc54cc3f886195f94431bea8463fc538837a82a05fd5110bf28c65fd540c3fe82207f8cb40fea1e83fd438cbfa85197f8c521ffa8c65ff320cbb887187f8c421bf298217e50842fea6087f94232ee21a637d510cbfc20886f10f42ff28a65fe548c7faa090ff10410fe98621fd540cafea6a07f10631be2a461bf40903f8a5a0fd84110ff21a217e53086faa2107f0c740ff218657c514cbfca5187f14032fe99681ff40103fc6418ff94b41fe282437d50887fa8390ffd4a41bfaa441fc21043fa85a0df54e30baa8841fe43907fc42a07f10a41fea1e81ff42043fc64207ecc230fe99483ff31443f860887f54941fea1443fe43507fa8618ff94c21ff19265ff43d07fea9997f10e40fe18881ff52503da84217f10530bea9081fe41443fa64207f14730ef99263f641443fc64a0ff4c831be28a85fd434cbfc82a0ff50c40bea94837e53107faa420fec4110ee21e63fd42cc2faa9195f94b31feaa2217d528c3faa0997f48410ff90a43fc214c3fe84985f54742f6a12413c544c3fea5987f15131ff99481fd500cbfc6598ff95210ef98c63dd324c6fca7105794e42feaa443fe53886fea6a17fd0410ff10621fe54443fc8510ff94730dfa1085fc51c83fca890f7d0f32ffa0c637d518c3faa890ff88420fea10657d53842fca6217790c43ff20a43ff50907faa610fd50510fea0a21fd51d0bf88510df95230fea8487ff544c7fe8610df94a43bf29043ff210877886207f48530bf28e81dc53503b886185fd5330ff90e21fc42cc3fa81987f54332ff2a6657d52d06fca7a05f94020f721641ff30083fe85107fd0010ef996637d540c3f883106f90140beaa2656e52103fc64087f8c740fe29881ff414c2faa8905f15331be28a61fe518caeca2207f94c40ff28665fe328c6fea710ff8c440dfa0081ff51c83f864a07f0c410bf28881ed20083f8a2197f4ca31fe19041fc21883fa86087f88520bf2a063fe310c7fea021fd8c431fe20021ed42c837aa8107fd4620fe20e43fe5350af8a5087f10832fea8485ff52043fa85207f4c810fea0081fd438c7faa898ffcc120ffa02617d548c3fca7217b88521ff10c617e5110ffc87187f4ca30f7290817e54887dc84215fd4c21ff19261fe21c837a85a0dfd4520fe98c815d53043fa8790ffd4c40be2a465fe42d06faa3987f54b41fe20261ff308c3f8a7217f0c530be29281ff534437e84a07f54930fe90c41fc435037aa918ff54a31fe99261ff42c87fe20887f14b30fea9081fd548cbf8a2997f50d30bea9c43ff53107fa6310ff0c920fea9e43ff510c37c86a0ff4c730bf29683ff41883fc80a07f14630ff2a041fc53842f8a918ff95220ff28085fe53d03de40107f94231fe21a85bd42d02f8
  | 5 => 0xb32bf28c617d5310bfea1a15f55020ffaa2437d51d03faa4a07f94443ff2a261bf4310ffea818ffc8540fe10e21ff540cbf240887f50910fea0e817e548c6fea0997fd0e31ff21261ff51083f8a4a0ff88730df2a0617d52d0ffe86085f94641ffa84637f54843fe6520ffd4643ffa9621f6510c3fca2185f94621ffa8865fc42c87fa61907e88210fea8c617e52843fc63087f50431fe90e217d500c7fea2997f88120fe28687fe43042fca8907710f32ffa9c41fe5150bfc20085f54831beaa4217e5410b3a8621ff14940ff18441fd540c7fc8718ff50d41fe99283fc41086fea5087f55120f790843f521c43f8a8187f50f32fe19443fe548c2fca3205fd4b10ff28a61ff434c3fe8420f794e42fe206217c52443ee6318dfd5320bea9e43ff41106fca7905f95131bea9443ff41c42fca690df14d10ff98821fe510cbfc8318ffc8520beaa661fc32cc3f860087f94d41fe98421fe434c37c84a17fd4343ffa0a43ff5310bfe8410df95041bea8687fe310c3faa0a1f7cc230ff20821fd31882faa321f7d0d43ee99261ff32cc3fe81885f94243eea1a61ff218c3f8a9107f50110ff21643f521087fe41105f95220ff28e85fc20443fc85107f94121fe28283fc42442fca3997f94841bf29083ff21c83daa4207754e41bfa82837e51083ba63987f8cb10ff98a617c53507baa7217f48421bb28841fd300c3f8a0217fd4141fe2a041fe21903fca4084f95021fea9c21fe414c3fa6420ef10d41fe18e217c54c87faa3a07f4c721df2a0437d54887fe8210df94043ffa8a41fd52903bca6087fd0e20ffa1683fd43c437c86a17f50410bf2a0817e5410ffc81987f4cb10fe2a241fe5110bfa8318ff10740ff98c41fc53502fea4087fd5010fe902217e520cbfc6420ef50c43fe29087fe43c87fca521df14143ff29e85bd42506f8a8184f95020bf284817e518c6f8a4a0ef95010fe19481ff53d077e86a05f15332ff10421fc21d02faa7197f10431bea9a41ff43c87fc87107fd4730ffa8487fe30443f8a818ff10440beaa487ff52d02fca198ff8c821ff21e857d5090afaa190ff50530ffa1681fd500c7fa8620f7cc030bf28083fc43cc2f8a0a0ffc8430fea8c85fc31086fca9997f14d41ffa1465fc21103bc87985f94e21fe29421ff420c7faa8987f10e21fa98a21fc30883fe43087fcca21fea1843fc54cc67ca8187fd0840fe99043ff424cafca421ff4c510ff20c41bd54043fa87a15f54910bf28861fd21d02b8a6a07f94242ff21221fd5110af8a090dd94430ff90221df31cc3faa418df54a31ff2a065fe324867aa918ff94041beaa4417e508c7fe6390fdc4010ffa8265ff41d03fe87997f0c521fe2a443fc51d0ff8a5a1ffd0a31ff880217e52903fa42207f8cb41fe99683fe31c42fea998ff50620ff21e657d5010bfc8390
  | 6 => 0x81d0905424080196c0000180f000038008160062a0000130020100992702c0280434a0480028c01c0384a8011200140101180e0050e8021896c60fc1a00100000c2181f00cd580000300e018213810160000056d002058130006d40140640c01e024000965b60000f82b0252f0820110580040204600a0040000000a00d1200d2aa7b8008030000b0cf0020240040f803920020018000109c4020000000202edaf026044030320000b9bd078056ce00000800200c128300140ac0180703c000140320324ac003f500000c1280003a0221400700a0ac0201b00693a02074000000000020140100000913c2e80280a0000104b80001410c488000222a400002034001a504205e424000010b40404500b0000314880000d4640b11a2180680582b00018c8d86f0101d8008000860382280e00003c1700f00201c0480000805e0c868a02000008120060340b8030040280200a00200001801ba80641803a0000100b80160c0000100c0e40f400d230080000080057601406aa10180017b81b01a004f280a00404c3101205a018188140020000d8061dc09c07b6103204403019000000003e9044088fe8005f86ec0000003c000028010040241380f036fb0000070100300b8396aa00400000060000000051340e00000604c03001c5455e0d400008000010bc8061ae001e68530000840c8159831dc0180a0023309957f0160000003b002044052930000181e018030100041348a202848086010000030ac04c0240180102200800815028040051c400202000cb303c2301700d02e034218080099400280626a001ca0012f203c0000400c14c1080002d00c018261100480c00d0016ac030000200044e0000000012e437004070a380b0420006300e02c034078040144200840d01c06c0f80805a05c0000b0060040100c03200c208034c41593880105608006801098018f880003004001002110014002e71de014061cf176000030154720319482109801c0d0180340162b00400007c1500000200c0f8130060080001e03402c00000286004000050a401c080020060400300000200830001002b8402513184031aabc78584fc3380000a000280000020000f81100000c1206604e04c0603200e0180000e2200022083c0a202c0c00205c0000002410603aa2b0f00e00010058000128148045c2168000060040240000001202ffca198df942219eaa021bd42503fc86997f54620ff19061fd54087fa60907f54732ff98863fd320c3f880187f8ca41fea1c83ff42c43f862187f94c42fd904417f53443fe62207f8c720fe98821ff41507fc60987f94540fc98061fe42043ee82a0df94410ff20863fd43cc7fa6598df94b43ff90021fd40883f88290ff10710bfa8285fe428c7fc82207f88020fe98a61fd5110ffea3a07f54b30fea9461fc42883fe42107f50
  | 7 => 0x100035c00c760032440928b03400400045bb584e1d8040700040000101c1e81100601002c0d
  | _ => 0
def q2K5 : Nat → Nat
  | 0 => 0xb420c2f561148439f596411033e54d0b109f58a51d027d6315020cf981540425e6314c21dbd9552042bd648cb31cfd50434436e52c8420be980324435f6554c209758e51d0b3e6055232d75974390f7a5288020dbd0e520c35f54d0c30f5987434c6ed62d4643be98042d036d5250a409f58e529076e52d0430d7d86531035e53544209f988520437852482109b988548437751944439f594218c27c65d0d20d754e43083775194720bb98a408827e64d45329f99353442ed6448720bd98632c436e6494830e758c544c33e61d5130bbd8f21482dd6390a41d79524310f3e544c810e750c4390a7d6494e10bb9885110f3c6295030f598e411077a4194021af992328876d54480209f982529067d61949109fd94211036e52c8010b758f529067d65d0430cf55153043652154021d7d0e50cc73c54505109f5925308775514c440d7d0c504cbd5324c510cf95141482fa60cc730be98231c43b551d0740c755253087763254420af98f409033d5490c21af992319027e65101109fd9742c437651484309fd97210c2ee62cc120af58243d067f6154b40af59232c436d6215210cf552510c27f6550030d754c30882be64144209f583540cabd6490540dd546300c2f66108310cfd89548c67e6315220af992325073c5490130db54830042f960108209f58e544827f65d0f20af98e415076d52c8440be580319027c6590a10cf95043ccabd64084308f99353c433e5414830db988540ca7f654c4319f996210c27c6014d10af99021482dd6390840cf153404827c6054a319f19743882dc648c5319f59053c827e6395210d394d521027e6094432db192520c27e64940209f98c53082de60ccb30cf15143487b65494420de54050d0efa60084409f984540c2dd6390730d7d4e415027f658c421cfd91540c73d54904309f19442c439c5390d42ded425050f3f4354243db94a328c27d6295330d754e31103ac4394840dbd4a52102f661d0d31b798e41083555394420d718a530836c6394830d754e438839f6250c43b798f424ca3d6414c21db90d520427f6254243ee58341d027d6195320be580315033c5410910b758c5190ade63909319f994434c33d5448020cfd8a548c76c63948409f59742cc27f6454f10cf95140082f461481109f994400c33e54d0831cf550540833d54902209fd954310e7e6315130ee58343d025e63150309f59631082f66190b10d718953082f76150a31cf191538833f54950209f59630042bd61d0e43d758f54486fa608c9309f996404427e6295010db94b31102df6350040bed8121842766114e20ed952510c2ed6290d20cfd9153442f661109319d587530827e6510a10f6983438c2bf6448640e715143cc27e6294331d554f1004375510c4309f195325027e650c920cf950210c27c6454831e9551210876e528ca40
  | 1 => 0x435e53108209f98b53842f56110330b7d8d408435d6314b10cf98e540c27e658c910dd987520427d60548109f58e51d027d63d5021d7d53438c3cd320cb30afd91329037b50940329d587540837451d0520bdd855050b3d6414b109f984540427d65d0c109fd9542442f561150309ed9540103f22148110d7152434c2f860505409fd95310c36f53c8220dbd4a529033c5490930af590308435f53cc921cf58e548c73e54d4021db948420c2ee6210621d7d4d32c867e64942219fd95430833d54cc820bbd89314873f6454e20b798c21c437432944309758f52042dc644c030d795332cc33d54d4231db549200427e65cc720d754f210836d6295132cf10e50d0b7b5094132af590214827c6550d21db548510c3766194f10bb98a308839d4310c21d758e511067e6590b109f194400836d5250a419f58f505079e5310c40cf990540c6ef6548020bb58a43ccabd648c440bdd95310c6dd644c730dd94e310c67f6155030dd947310827f654c110af582435067765504419f997311035e53d4840ee951100427f6054a43b758f214c27f6154243e7d4e4350f3d5415131bb98a544c76d5290a41d794932cc35f4314143cb552520439e43103309fd9743c867e650c930cf953210876d5294440db181520427d6294643e750c4350b5f5394c419fd9521102de63150209f984530875d53d0840db948421067e658c920db98e52103765190640db5485250f3e5490020be181418433f61952329fd8554c827d65080109f98a548c2fb604c920af59021d027c62551309d98754cca7d650c8409f994404c27c6510f10cfd5254842ed6290421b758f540867f6254e41bd9845050f755188020bb18121c835e53cc440f9cc521087e65348421bd58a31c43d6324c4319f99642482f7614ca419f99632043766294440b798d214c27c65cc910af99353c427c6590e20be181318c376518c4109fd8953106f76550441dd14e31443f24188110bb58a300839d4310d10cf953430c37a6014c20cf953410c27f6550d219f596410873e5410410af590325033d54c8421db9885050ef76154132db58a534876d5214a439f18d50d06f46150d31b758a4310f5c6294c40f948421c433c5490d2097d8d52442f661148439f592538867e65109419f98e51d02de6310310b758e411027d6550b30db54b210437561d4a10af590514835c5350d42cf55043886dd63d50109f58e540875f5394f21bb588404835d53cc6409f597211027f650c420d714d515027f6154810cf993520436d5214840dbd91520c3754394430d794f43083e932481109f595414867d6588640be98343d02f960cc430d7d4f324835e53d0420af5844350a7f65cc841b7990430c39d43140439f594400c27c6054443eb94b42d02f76154940cf153420ca7e650c620e714e405035d530c020db54
  | 2 => 0x6255110cf951508ca7d64d4132dd552510827c6550f20bb189504c6f6610c831d755043ccb5f6554e41dd90d510c23d6414c10af191304437661953109fd815110af56348510b758e418427e6294410d7d4e530427c6590c21d755043cc63d64149109f98650d0a7d65d0b31af59050486fb6048510db54b32102fa60cc6109f99442486776154d20bd5845050bf220841109f59642cc33e5490d32b798c511033d5490030ded42500c6be6408420cf99052043d66390710db988540867f6454331dd99251082bd64908429f197428435f5394f41af992310873c54085309f597434427f62543319fd8d548827d65d0620d7991530833d540c4109f99253c827f6550730d7d91530427f654c520af99020443746494420dd987538873e5490f31b7d85434c33c5410e309f98a500436e52c8310be98021503e76548421b758c5010b5f53d0e20be580510ca7c64547309f59530482dd64cc530d794d328833e5450430bed81428835e6054c209fd9442c427e6494820e710d329027f6548740cf94d42d033c6055021cf951428c6f86050640cf191534437a60152209fd95418c2dd6390940dd101511039f54cc530b7593324c36e520cb41d715153082fa6010f30e795153042de6390a41cf081540837661d5332b798c5190a7c6454b109f19531c833e5490820db58b548875e5310c10dd987548867d6510c319f195328435c530c540b758c424c27d6394042cf151424c3ad4210b20d798b535035f6494c219f98a524427e6508640bbd914210abe648c510d754d200827c65508319fd94420c76d52d08419fd9743083b54350441bd584420867e6590c209fd8951d0eee62d5030d714d324837a5450040cf18a54087ce53548109f58a544833e54cc821cf98b544c3ad54c80208f191524437a60d4c20bd986408427d6194c40d794d41082dc6354540af18d40102dd6390a10cf55340cc32e5454810cf58a540c33d52d0641db94a210c2f96588210b798c530427c6054841c754d401027e6015030db54842d075f6354e20db14b204435e534c0109fd96430c3796094d10cf182548c75e5388420bd584424427c6510c10f9549511036e5250430db54b42cc63e6415010cf55142882f76250710b758f52102de6390b30bd987540837551d0030b7994535027d6590620be98041882be644cb409f994428c73e5410830d7996434c33d5450030fac8520082de6390840e750d5110e7d61d5230db94b32cc36f52d0910ded81534827f6550720bb58b40c82ee62142439f590524c35c53cc510eb50b41c829e6390942af59231cc27f658c0209f58a501075e5494c20dd589511027e6394d21ebd89425036d63948409f986530827d6550720d794f321073f5450921b758f42cc3f14148110d794c434867e64944219fd815190f7950143329f592534
  | 3 => 0x932af990518827e6515131bdd85424c7ac4350920db94a31042f5618c821ddd45214827d64d4f20d7591530427561152309f595404837a6354021fa549300c36f5294a43ded425050b5e53d0c32e750f5210ebd6290541bd58e104433e43d4941cf553438835d530cb21f5d0d510c27d60d53319f99441487e552440109f58853c436d6214c10db552520c27e6394442af59232c82de6388530de0c550086f56488510dd947200823f6454e10d794d43042bd648c540d754f320832e5454830cf953520c2be64d4830f9951210867e6394b41f6d8d40102ef6048020bd185428879d4310c42d7991530437953540219f59642843f2518c030afd8543d02dd63d5320bd58442d075e538ca41bdd8931442de64cc9319f58c528435d530c410f698243cc35f54d0d319f58b54cc27f6354b10ed951210875e6054e42bd586324435f6355220d7989531035e63d53319f58a53843755150620b798c42cc73e6494730b798f509067c65cc520dd584540825f6355110db98b53c873d54d0620f9d8921c425d6314142b718d408c3766394440cf95331042f561840109fd94420879c43cc440dac85500867e6215031cf953100427e62150209f58c54c42bd648c610bd185439079c53509409f59432902bd64ccb409f19540442bd64cc740ee181425027d6314940f514d314437a6154021cfd53414873f54d0d21d754f328827c6510e219fd8d500873d54d0831db988530433e6095232dd54621882ed62100209f58251ccb6f52949109fd855390a7f6355131dd989510c33c4394341d7d4e40503b754507109f18d548875f6194e42de980540835f5394e429f59353c426d62150109f98e52c436d62d4e21ddd46518cb3d6355010d794e31c433d5494830db54b32042de63d5021be980219033e6155030d7182530827e6590420cf552420cb9d54cca32b758e429039c5450d309f58c544833d54cc821cf95342103776494420d354e520427f6254c20ded4250486be64cc740af59353c835d534c440de540504c67d6510a109f1895190edd63d5020af592425067e63d5030af5924310f743054430cf55243cc27f6590f10cfd5142cc76f5294830d714f32c833d54d4632dd54451cc3756114142eb50941c835f6114d40cfd53418873d548c0109f99543887796094910be9804310376510c4409f992518cb9d5454c20db98a53c82ed62d0f42bb5924210b3e5414c20dd146214837463944409f995430437a54900409f194328427f6508410dbd95521027d6094642ddd51510c36d524c430e750c43d06dd61d0d32bdd8532843b44350710b758443cca7e64d4c20bd982314439e5450c43cf952210c33e5450820cf95021082ee62103209718d544837551904409f995414c2bf62507409f992530875e5348410f654d500873e6055021cf553500866c
  | 4 => 0x7185530827d65885409f582524427561141439f597320833e5490710d798c54042bd6494d21cf550210c36d5290430cf551418833d5415120cfd51414873e5410a31b718d54443d7434c710bd584200435d54d0e30fc945200837661152309f98053886f960885209f994420cb3c5410930a7d894310f7561151109f98c505079d4310e21d7d4d42502df6150c439798c514827e6510940dd54441d033d54144209fd95218c37b60551309f98c54c42df63501109b588538435d5314242dd544511027e650c521cf551420c33e62550109f994214c2f96090c30dd944410c2de6390620db986521035d6394842d794c5090b755150040cf55243ccb3d54d0010dd989511027c65d0c21cf14e40502f562884219f98f514827e63d4540de5405090edd63d4b41bd58a21442f96014841b758c420cabe64485409f982528c67f654c540db98e5204376534c431d7d0d51ccb6d5214941d794c32042ec6250721d7d9153086bd640c1109f185530827c654c6409fd89534835e5494c219f19432c435c53d01409f99643c836d5210030ded5150086f5610c120cf10d511035c2054c209f98f54086dd6310330cfd51418879c4350932afd8d42d02de6390d31be98221c439d4394443e714f435027c6510f20bb98850906bd648c640de90a50087cd53c80209f98f52502dd6390540d994a5110374534c510db54a328c35d534c610bdd9141106ef624c320dd945310433e43d4543e7d4e4350abd6414321bb58a31482f56190e41bd584408436e6154840d7153324c37a5048010dd55310042f96010440bbd9532c833e5454c20b758c51482bd6414e109f195438827d6094743b758d21cc2f96008630f948421c827f6255331cf953430833e54d0420cfd5043482f56115220bd996414427e65cc110e790e40cc33d5490f31d754c43c867e61d4d409f592500c27d650c821af99251cc27d6294010b798e52d06ed648cb20be18141442ed6214630cf953428827e6095032cfd95540c27e6315120d7d4e42502f66110230e750c43506de63909409f99353043e45148520cf94d42d067c6454d21ddd46510ca7e6094831d754e300427f6510431be181218433e5490431b718d424cbba5494021d75865390a7d6395121cf153434c2dd638c530dd4ca510c27e6194f20af990530433d5490830cf951510833f6295010d7d815390a7e6194c42cfd5254c836e62d5030d718753502ee62d0c21cf953418c67e6214d409f994434433e53d0f40af590210827d6194d21bd98732486dd6390640cf9524310b3e54d0e31b798e428433c6055010ebd4a4250abc64ccb419fd97329073e53d0740d794d52102ed62906219f18052443e521c8110ddd4d10042f461509419fd9543106f86050d40cf550540c36d52cc0309fd8d52d075e6054e41cf153414c33f5450
  | 5 => 0x21d033e5490f21d758f54c827c6550130bd58454082ed6390b20e7953300c2de6314910dd58754ccb3c5450d32b758e410873e54108209f597219027c6355110cf552320836e5394810dd5445110aed6214331d594e511037462544409f587540cb6e6354810be98021cc36f524c931cf94d41d039f434c740d754c310879c5350540d7552530867f6548420d754f400427561d53329f98b540c67c6254e409f584535027f63551309f994434867d6510430cf552428c73d540c010dd98752c427f65cc810bb597208835d538c7109f594438827f6355320bd984540cadd6314420dd546401027d6510f10d7d92530833c62952329f996218c33f4154241dd547210c2ee6210d20d754e32d067c65d0f219f595204433c54d4530d794f31482dd6390510cf951410833c53d0941db949420c79e6150c43b718d400c2766114c10e7192531027d658c840d7ccb514c36f6255121dd19521442fa60cc5109fd89530427d6014d41f914d21086fa60104109e580540873f5450210dd54721c82bd60905419f595404c3f15150040b7d8931cc2f661d0110cf18a548c67f6550130cf986548c6de62d0f32db58a544867f65cca40d754c318873e54884209f594314833d60952319f988514c33d5490c109f994200427e65d0910db548200427e63d5210f54c4314c3ce52cc0309f988548433f6455330be58032cc27e6510530be98042083f06088510be98242c836f6254810d710d518c27c65508109f99732907756394420b798e51502fa60140219f595428c67e6314940af59032d06dd6390821af99321d033e5450631f9d4d210875e53cc620af19332507e551c8720d714e43503b95494021d758f54c873e54d0a21d7d4e535073f54d0d32afd9132d06be64cc8419fd8950d0f7960d4f10bdd85429067f654ca40cfd4e4350b7661d4c219fd9542106be64d46329f99353c42de6315021d754e429073d5415031de50a50086ed63c8520db54a510c27d6414c21c754c43d075f538c9109f98f544433c5450530b7586304c36e5248630bd587320c67c6550f21d794c43886bd64947328f59353c87d931cc1309f98253106fa60148319f995438436e52d08109f99432842dd6394542dd94731cc35f5350d429f98e50d07b55490710f5d0f314c67d658cb41d7101531027c60551319f59543487da5384010cf550518caf661cc3109fd95200437443544209f18950106dd63909109f997420c2de6390a409f19530482fa6008510d798c50486ef6250721cf152214c33e54140219f59542842f56110d21bb98843c873f540c530bb588505076e52486409f1915304375514c0209f5865090fe55448421cf550520c36d5248310be980438427c6354b10db94a420c7b55494430d7d4c21502f560d06419f9825190edf654cb319fd96211036c6194830d
  | 6 => 0x3cd424c832db54a321033c43d4542af98643d076e524c410db54852cc2f66088510bd984420867d6295231bd584300827e63d5120dd94721102fa60ccb309f59442442f6610c310cfd9543d03d5434c431be181439036c63948109fd91508cbaf5450920b798e424427e61942329f99621cc3f231c41109fd9641c827d6394b10bb98b31c835e6294c10de980540c7796014f10cf58a540427e61951209f5805150edd6310631de90d500875d5314420cf18e540433d6255030be580431035d53d0f40cf95140c436c52d0910cf55220082bd640c941db54b42d035e65d0d32b758e42d07f15190040b798f5190a7f6510430db98b530836d52500309fd95430c33c5450d31b758c524437642544409f997434c77b4194021ded0e500876d6394810d798c52c42bf644c941de54050c867d658c020cf552518ca7d6550d20fad81214836e51487209f995320427d6194d10de94a20442bd648c4219fd8151d0a7f65485309f59442cc75d5390c109f994325073d6395020d7981530875c6154c21cfd52548c67d61149409e58053087e121540219f98a5010f6d5214b40b798c505073e54c80109f59642042f96015031cf15143cc3ad52d0040cfd5342cc37651904109f98354cc67c654c921cf14d425027c61551209f181520c67d6094a43cf55321043bb42d0140b718d504867f65ccb10bb588308427e6550b10cf551428c7745354440cfd82548cb6f64548109fd91528c33e6295021b7d95300c2ed6210d21dd50d510835d63d52219fd9153c876e528c440e790d42cc37661d5010b798f54487b541d0110eb9524210af561d03109f596414c35d65d0e309f997428c27c65080109f993504872c4354840af99050c876d5214810d714f215035f53d0540cf553430c3f361440109fd9152042ee6214141e7151324c33d54140219fd9621cc33f6115130f9d4921c427d6395130cf58e54042f661100309f197438875e6394842cf553410c27f6454620f354d521027d6314141dd584538833d54108329b58b54042bd6190140cf59053086ed620c720cf55252042ed62d4743ebd8942d075f654cb31db54852c427e65d0d32d798c53086fa6010530cf95232086f96010f309fd8d54c427e61d51209f99630442be6110d419f9865210f5d5350a419f58f548875e544cb31af593508c67d6014d42bb98b4310abe648c621dd94740102ed62d4f41bd984540c35f5454c21cfd53420caf5610ca41dd18d51082f4614c310ded95500875f5394c219f980540873e6415320dd58454cc79e6410d32ddcc9510c39f53d0940e714f415027e6114930e710d32d067e6394841af590500cb6d6215230db14e52042bd644c9409f980544c73d54106219f588544c33d64d4c20dd90e51102dd6308630f398e42c835f6550f30fcd86204427e6315021be580
  | 7 => 0x414c109f997438867d6550531d754e320827e6590e209bd954210b5d65cca329fd96311033d5415210ed50441c43e66348421af99443506be64d4231db14920843d4534c710db54b51102ed638c832dd946219027f6510d10f6181434c2dc63541419f98c548875f32542329f58c5488375510c730b758e42886f9600ca10db192521035e538c440f694d100427d6414910b7988434cabc6454e10be980434433d54151109f58c52442fb604c630d794d31c877a2194021af59231443765148630a7992324cb9e43d0730d794c431073c51d0540cf98154083d853d01409f98c520427d6494232af98c43102df6354940b758f548876d5494810d798f54cc35d53940219f99742c435f5350540ded425090adf614cb30cf15342c87e631484219f98f528433d5450430cf593534867f6255120bb58840882ef6250320db988524436e52d0840d794f30c427c6255110cfd53424c6dd6308740dd54451c83f26188210e7552530435f32d4131d754f210435d530c0109fd81544c67e65d0430f6181314c2ec6250420b758e4210a5d63d5321d754c509077452944409f58254cc71d6315130dd544211035e5310410d7d0e50ccb7a60d4a109f58b505076d528c8109f58253106f66110120b758e4250ade6310530e7590535033d548c821db94e32482be64d4810be583218427d6510e10d7d4e215035f6354e21e710d42cc73d54904319f197325067d6590821be58a204427f6544010bb5834290b7661d4c109f58a518c2de61d0d31cf145415027c6055021dd509511027c64549109f98853482de6314442dd584540cb5d5314440b798e544873d5488430bd98443487785288210e710d32507ea42c81209f593524439e5310d429fd95210c3795014041cf55340c82f66110910ddd4d510827d60d4543bb98854043b64350510d754e52042fa6014843cfd5254ccb6e5454810d754d401027e63d4941db14e32482f76150a109d98454882ee6210f32ded4250d0ef661d0d10bb98a43c833c6195010d754f419067e6415010af99021882bd64d4420bd584404433e5454810bb98b41c836c6094810de980540c2ee6214640af992328c2bd648ca31eb90d52102dd6310210fa50b20482f6618c010eb9514210b5a5354021ebd49425073f5414930dd94741d02dc6350b31dd94631083743254420d7d4c425027d6510931b718d404835f5394f40f34c832086be6510d42d794d32043d960ccb30cf550420c27e6094e21b798e42086f46154930dd947310c36e524ca319f596320875d53d4a41af990504cb6f6255132cf54c43903d8604c9309f58c54c867d654c910be580210c2de6314021cf551200433f54d0130af990508c67f6254041bd587438c6de63909429758f54042f860485109f98e52842bf60500409f98c524435e5350c309fd97410c
  | 8 => 0x30fad81424827d6294243e799043cc67c6254f41e710f41cc6f9608ca30f654e401035d5388020db988528427f6454831dd547411035d53d0f42de996204435e53d0840d794f50907d65354420d710c504c73d64d4f21db94840042be64146329f99721442df654c431be580329027d6414d21d7d4c43842f561d4b43bd587434c76e5454830b798e41487d561d0d31d718a53906dd6394b40b758e324c73d5410a31bd58643443785494021bd18131c427f6508740bd584504cb2d54548309f98c525076d52908309f58253d0a7c654c841db547208835d5314d408fd91524433c6454d20d754c531067c6154032b7583434c73f54c8530d758f544cb3d54d0a32d754c4310b5e5394a41cfd95548c63f65508429f58e544cb6e520c4309f59743c42de644cb319f58654cc27e6194a43be58043842dd63084309f992534833f5490d30dd94421c833d54cc810af99232d031e5454c10cf553520c35e6154c219fd8154442be60d0e43b758e415077865481109f98b540ca3f65500409e58354087e652884219f98f50487f141881109fd9543103775110520dd984548835e6314d209f58a53443cd324c720de545200827d6590720e7d4d43d023e64141329f988544427c6254f40ded4250d06be6414332d394d520435f6354e10af191534835c53cc940d71855390a5e6314c109e983530867e6550f10af181415027f6510010b798f540835d52cc6319f98c540433c6255231af99351082bd62d0d40d715131cc37a6394021bdd85328875e53d0e42ddd0a51082de6390b41d7d4e53c42df6350932cf951421067e60948439ed95200825d6315210be580424c33d6414e20db185520435d5390c21b758e418867c6550730dd98754c43f22188110bd986200436d52880109f98f54c877753c4210bd98442d067e6115120bb988310867c6154a43e710f424c6be6414810cf553418c6be6190d41af590218836e52cc010bd987204435e538c421cf55142442f860509209fd9543c42ee620c621d754d509067e6014910cf553428c27e654ca109fd8953d035d5348010af990315027c6590d10ddd8d51102ed60d09429fd9531d037b5284010bb9885050edc644c931cf950408827e6494030eb992320cbd95350040be580325036d64948109fd8d5110a3d64141219f980540c6dd6314141d7d4d30843746294440db54a400c2f661cc8419f18d50086dd6390941cf14f41502bf644c030d754c42907795014221dd945419035d5390040d758c520427d6494f20cf55243c835e53cc421bbd89410837b2154021cfd8f544c2ed6210c32edd8541d027c65108109f196320427d64946309f58854043784294021cf14f435027d63145409fd97218c2de6390530de506500873d64145209f997219027d6588730db94a20082be60d0f40cf553438c67d6
  | 9 => 0xd8132882bd640c5409fd855210f5d5314c40e754f4290b3f60d5130bb58a308827e61953309f983525067e60d5232cf95231043d6538c431e750c5210f6f54c82209f58e51882dd6308520de982518837b32540219fd8554482f66110020fc4c7104435f5310d10d794f31043d7634c510d794e43843cd32cc320b758c40442bd6010f42cfd5040cc2be64d4e21cf95240103655244010de5405050add6394742bbd8d424827e6550f21dbd8e521039f6350040cfd50414827e61d4943f954a510c2dd6210d31f354b32cc75e5350e419fd8552d0f5f5310d20be582414835d53cc8109f19443c879c54d0d32d794f10042be648c830bd584431075d5314f42dd10951102bd6494532dbd92520c35d63d5231cfd8d548ca7e654c5409f592520c23d64141319f594325067d658c940cfd51524c27d658c9419d984540cb6e528c820bdd85325067e6394b409f588544427f63547209f5825190e7f654c821b798e42886ef62545408f590530835f534c1109fd9432443da538c0309f58a51103355454420b7d89434c3b643d0541cf952300c3796014b10db548210c2be6110f41f34c832887753254420af991315027e6494b10af58b41d02f96090b20ddd0d511027f6454e109f18954cc75f534c120d794f420873e62952319f58e54c827e6510d40bb18953442ee62d47439f99432c4374510c520cf951520c33f6055231cf550200427c64548309f195214c35d53c8421cf95142c427d6590e10d794e32c835e538c0209f98a51d0f3e5490e32cf185540876d5250830cfd51408c27f6510832cf99054c871c5450d309fd96400827d65cca10cf151420cb6e524c440db58853842dc63500209f197325036e62150319f197215027f654c6409f98b54cc2bf644c1209f982548873c5350540d754e421033d54506319f597410867d6510421ded81534427c6154b309fd9543c835e6214d40be980540cbf36050510cf153404435e538c210bb58830442de6390410d71815390a7e65cc930d794d32887ce538cb20e7153314c35c5354940d798c54086bd64c85409f59421043765184010af58342d075f53145409f58a54842766115230d754f31c875d5394241db94a41042dc604c5309fd97319027d6015032af99251cca7d6194840dd94a51102f661d0f41db949328c37732944409798c52843c553484219fd95324436e528c030f354f4290a7d6214e109fd97418c3b554440109f992530836e6054840af592318873e540c430fad8920082f56190c21dd94521882de63c8730bb988540c2ee62d4f41e790d41cc27d6510c21d7d8d534867e6194e209f995424c27e61d5220ebd89425075f5394f42de580524427e650c540d794c310827e63d5310b798f428c75e6294c40e75894310e7d6494221f9d09210873d5490b21db949329033c61151
  | 10 => 0x44c27e6495121e7553300c3ad6290d42af99232483776394420db54b410c33c6355030afd91504873f54cc9309fd81530877b5244010dbd0d520c35c6454c219f594318836f2154221d794f400835c54cc832b758f509067c6550d309f59441082f661d0c21f394d210867d62d4d40ddd8a511027c6154243d7d4e5350b6551c8020cf55352043e86048520bdd85438c67c6355010db94a10042bd64485409f189540433e5490220dd984530826e6214131e7d0d400c33f6455310ed551210867d6394a40cf55043c433e5410c219f189531035e534c440d7d8d53c436e52d0030be58032442f661ccb31b758643cc2bf644c440cf95241886e76548421af58342506f6610c320ee95240103e85248210be580210839d4310c31af18143502fa608cb209f19532506ee6210330bd58432086be6414432fa181324827e650cb4197597430c3752154021e710f319035e6254c20ddd4731482dc6350630be980310c27d61d53209f596421027f6550c32cfd87544c2fa6090520f394f4290af960cc830d7d90535027f6550431bb58d21c82bd61d09408f99052c436d5214a10dbd95210867e6195232af990325027e6590e10af990210427d64d4e20d754e41102be64085309fd895190ebf6250f40d754f328877751944309f195311033d5410c20de58354cc2bd648c931d754c200435e538cb41e795243cc35c6194c219f584538835d3254331db588548873e5450831b798c50907745490710eb58843d0b1d5410c308f59253486f6618c931cfd91548c79c43507319d587540c36f5294b319f996434835d534c640b758c41cc36d5248630e7d0d408c2f5610c9109f19541486f965cc2309f58b514c36d5354840dd98454086dd65cc230af99232c873e4354b419f993524c2fa6090c30cfd51514c2f960c8510af590200427d6194f429f996404c35e530ca41d754c43d063e6414c10ddd46510831d544c0309b588548c3746550510cfd52304c2f76348710db54a328c73e6415221dd991510c39e53d0a42cf55130082de63949419f59731502f76148310f3d4932cc27f65d0d209fd9642c43763254430db949510c2f965c4210db98b540427c6154b43db591520436f6554830bd98732c43755110420dd54451d037b63540219f59353c875e530c210d754c211033c5490d10db151520c2756114132dd94531082de6390941b7d894310ebe6414830d754f30c436d5214830d794d320c27d65506208f593530827d6550810b758c54086dd6310b319f191500cb766354430de983540c27e6095321f358e42c82de63087209fd96320827f6255130f554d100427c6254231b758f414c2ed6215030b798c40c83d4324c4319f58b540427e60152329f5835250e6d6215210d754d421036d5214831ee95140103755188440dbd4a525033c5410e20be
  | 11 => 0xde6390230dd546318c3f22144010af5874310f3e5490f30bd984431067e6414f20bd185504cabd64d4b31d794d5190af56110f31be980540867c6550d20af18142d035d53cc8219fd91534876d6454830cf550408c35d53d4810ddd91510827f6254d21db58853886ee6214830db041520427e6115130cf90d529036d524c010cf55042c867d658c740bb18941882f960cc920af590210427f6454332cf94f4290b3d5450c20d754c53d07ac5250941d795143cc2f965840109f18154cc75c538c520db94b42d067c6154c42bd59241106bd64085309f582510ca5e63d53209f98252cc67d6054c10db548420c27d65d0c21b7997324c6f56110f10af99052c436e5290010bd98642906bf644c020dbd51200827d6494a319f189540c33e5490a31d7d4d434873c540c5308f99053842ee62907209f58b548435e5390c209f59743c836e5290440bb58b43086f6618ca31cf552418c7766494430cf550520433c6155231bb58b41c867e6394242bed81415027c6154b40af99053883555354420db585520c35e65d0d319f993504c67e6508510bb58632c827c6255310cf95340cc35c6454c10bb5885110f5d65d0f32d7d8d53c8776658c510bd58a41c43ad42d0320db90e520c3ba4390040e7150438c35f6254c109fd8153906bd648cb309f996219035c54cc431d754f431027d654c521d754f41102df6354142fc94620082f6610cb21be580434427c65d0b109f5875350b6c4354840b75974390ebe6290f42d714d31442f560d0541dd94730083775190540dbd89534433f6455132bed81324c33e52d0b419fd9631c827e61d41329f59421cc33e4394040d79825390b9d4310e30e7d53434c7d44394430dbd4a32506d563907109f9825190b5d54d0d319f597430c6f66195132cf951210867d6294043bed81418427f6254341ddd4b108433e54544309f992530cb6c5494810d758f54087765490510bb988521035e534c421af992320c6ed62101309fd8d544835d53d0d21d7994535035d53d40219f98353042ed6210010bd185435067d6294341d7580535027d6014532b7d8d42cc63d64d4e21cf953400c3f121540219f98f520427e65cc520dd586544427e6414f10d794e310c75c6194e42d75825390a7d6214540af99221503d4614c931cf953420436d5214a41bb98b43886dc6348630cfd52544867c6550e21cf952420ca7c6155230cf54b40903e53148421de582544427d61141429f59431d03565394420bd58430882ef648c920de540500cb6d5214a30f554e511036f5294931bb58841086746548510cf95253042f86148210db14a32507d6514c030cf10d521027e6015321d7584535027c62553309f59542cc6f96088620de942200433d54d0721af58f41d033d5448420cf59353c435d6314520db949400423d6590c40cfd915
  | 12 => 0xd4931af990530827e6510f10f594d310c73e544c410db94832cc27c6254341be98041c435c6355110d758e54487775194640af99050cc75e53904409f59640082ee628c720dbd48424433f54d4930d714f525033e64d4f10be58342d033d5390f419f99541483ad4210940d794d329079e54d0c309f99432042dd6394540d714f30442766195132d75915390a7c6354420ed947401035e53c8010fc907104435d5310c209f58a539027c6254730db94b42cc73e540c8219f58c540873f5495110bdd95210877b6548210b7992324ca7c6590e10cf552320427d64d4520cf185540827d65d0420db50d52103d5310c7109f59732903ea60c87209fd91510cb3e4314142d7d4d515039f544c530f594e210867e62d41319f5805150b5c538c940dd146314c27f658c810cf18d540833d6414c10b5185324c6dd63144429f585520433d5410c219f59743842f76150941cf952300833d5448421cf98e540875e51cc730db58a54482f560cc631de983548439c434c440cfd9554042de6308730bb98242c836d5248410d794f210836c43548109fd8d5010abe6310d42bd587424873d54d4c209fd9543c877551cc4209e983540876c5208530d754d300831c544c930bb988501073d540c820bdd85434c7796014f209f59521d036d6214141dd94641082f764887109f997438426e6214143d7186530827e65905109f98054cc6be61d0b41b7d8132cc67e65d0540db94b210c2f76150a219fd95420827f6154c429f59542c42f56190d41bb58a430cb5c6254c21af59232907b66190d419f98b548c67c6254e41b758e51d02b5648c710b7d8d418c33f42d4141be580518cafb6050d30af992318c27c654cb10d798c548435d5310840b798c424c75d538cb20d754c32d07b55150040cf55141c873c548c1309fd9532c427d6508440b758c511037950141419f58b548c6be64d4d21b758c200433e540c420de580530867d6294430dbd4d520433e5414c10b758c21082ef62506209f594430427c6454b31ded42508c7756194d10bd58420c436d5250430bd58640042fb6050640bb58b41482fa600c520cf95140c833d64d4810e7550434cb6d5288430ddd53100427f61552329f994300425c63549109fd96410427c63551219d987540c37b5094243de58354c833e6494b31dd944400827d63942219f593524c67f65508429f98650cca7f6590910b7597328cb3e54d0a30ed951510827e65cc5219f58e500427d6094f219b988538427d61940439f98a50d073e5450c21d794c300836f5494830d7d4e53c836f6194830f9945200827c65d0f20f394d521035d63151309f99454442be64d4732f948421cc27c63151309f993538427c650c810cf551420c67e64949109f59251087cd538cb209f590514cb5f530c910bbd89544427e6590b30cf952430c2
  | 13 => 0x9f98e510427e6395021d754d430827d6414e21de98353086f66108210dd59631c435c52cc9309fd94420436e5208410d7d5043cc66e6215010b7996434c2ce62d0d32d79514310f6e62d4c219f18554cca7f6154d21dd94541042be61d0941d754e320433e5450a21db551520c35e6194c209f597420433c54d0130be185204436d52ccb41d71825390a3e64d4810f658331cc27c6155030be980204427d6494b10bb988424827f6254730bbd8d21482ef614cb209f98b540871d5494c10e7d914310f5f53cc710db996424833c54d0921d7953320ca7d65cc720d7951530433551d00409f99250087b454507109f195420c27f6454910d794d30c827d6590410d758c54082de6310b30db949420433d5488010db549328c27e61d4c209f590514c35e5390421b798c519027c6054e419f195410827e6094f41bd584540cbf35084110f654e50087b643944409fd9540103765188410c7550434ca7e6414132db948511027e6510b109f59350487db604c5309f59732d039f43cc940b718d210c2ee62143319f590504867e65c85209f98252d06bd6414630cf953210c2fa60d0840b758c520427f6454a319f994414c67e6314540bb58841886fa600c830d758c540876d4354810db94910042de6394740db18252102bd6010c40d7147314c27f6510c31bb98b51102be640c1209f595319031c5350d40bd984504ca7f6154830d799253042f8604ca309f597325076d520c840e750c43d035d5350e20be983434c27e6115320db949401027d6194c20d714e434867d6590430cf551520c2de63103309f189519027e65d0810cf95142882de6308440b718d410c2bf63505409fd9541087e92148020bd5845010f3f6455232cf549411067e61d5010d754b308c27c6454a30cf55143086f5610c941bb189438ca7d6355030dd8ca51102de63d0b30af992320827d6194830dd58754c875c5494c20d798f54087775194542cf95341102de63904419d18553482df64ccb30db588538835c6094c10d794c43d03ce538c832db54842107bb5090140eb90d42c836e5248420af99032d075e53cc4309f580548875e5354810b798c531035e5348020bb988408427a6015032db54842cc7cf4394830be980424c3ad4210a419f98b5050f7965c8220db94a42043ae54c8421d714f32c867f658cb109f99743c87755148640de54050087e652c40109f983540833f5495030d554d511033e43d4943cf551438427e62d4c219f597428c76d5248440bb98830482bf6454530d754c520433e5450840d719253042ee6214630d794d321076f5354840bed95300c3755114532bb988414835c5390d41f9905210875d5348420e79814310f7b6544010bdd9121c435d5388440af592321039d43d0130af590510827d6314542d794f32842de6314221cfd5240cc35f43
  | 14 => 0x89505073e54d4a319f58f52506f7648c710d714d308827d64d4c20d795132cc33d544c820fc58241c4375514c6309f99543487765190020be9805110b9d5350040d7d8d53c82bd6414632dbd52520435f6214d40dd10d510c2f9600c430db549511034d524c030af99051c82f96008620bdd85439075e53cc820e710d31902f960d09209f586544cb5e5310f41db94a428433e5410010d914921c43b942d01409f19151ccb9f5350940d794c511035f534c921dbc8550086dd6010e30cf952438c75f5410d329798e544876f5248210e795043ccb6d5214841f9484215033d5490230d794d31882f561d0d109f98b514c35d530c8209f98e54c827d6414131d754e200435e5350040d7d4e435067e6294243cf951411027d65508319f59542443786354021bd185544833e6415232ddd0a510c2ed6490920f9484211027d6215210b758a43cc27d6414c20f948520c427c6154f20af191514c35e53d0f10dd55151083e652544309f994310833c5490d30cfd51420caf565d0641b7d8d408c37953940219f590524c73d548c0309f59532c42f5610c010b798f414c23e6414c21d798c50506fb6550040e794f43d035e548c130b358e424839d4310f21dd545300c35e63d5030bed85100435d6510f31d754c500876e5490b20d7d0f514ca7f6510030be58221043783194021f948421843b54110631dd54910042de63102109f596400427c6214d208f990520435c5450d30da485500879f6550c43cf150434827d658c440d7953324c6dc6350220e71814310f9f6450d30d7594438c33f42544429f99742507365494420d758c540425e63d5031db54852d07cf634c9209f597314827f6454b10d794e439027c658cb10eb553210873f63952319f99443842756115220d7d4d324837461551209f196328425c63552109d98454082bf644c640fa94940102df644c930cf95343882de63d01309f18d540833c5454530bdd8530c42bd648c940cf95340083755114542bd98241c433e54d0620d794c43c83645248510dbd8652102be6415030bd98443cc73e54cc010de8c950087d531cc110bd592104427c61550209f982521073f6555232db54832042f4614c810cf9524310e5e63d5221dd945400835d53cc9109f5865310b3c5350941d7d4e539037763944409f9835350b3e6414121db94a401027e60d5321cf990548427f6355010bbd85210877561d5331bd98440882dd6394940dd584530827c650c540cf952431073e5490b20cfd85540833d65d0e439f99632103ae5490b20cf550320875f530c540cfd5254cc39d5494c209f19150886f86050a209f992528c39d4310c309fd95300833d540c4309f19532906be648c740cf150524c2bd648ca109f99430082ed62d0c42bed81414435d6394b41ddd52510837863940219fd9632442f66110f1
  | 15 => 0x8867e60d5121cf95321082ee6210110ed99231c42f66114a30db54d200827f6550a31bd98642443775108540bed8d300c3e45248710eb14942d027d60d52219f99250cc6fa60909409f596414836e5208710b758c50c867c654c540af592524c6de63907319f580548c67d6194a30d754c529076d524c840cf550540cabe640c020b758e418c3e52108640ded4250d0a7e650c5109f9825110e7e61141439f98f540427e6214131bd58642c427e6414b10b7d93314c33e5410421d5547300c33f5450b30cf182540867c6550510dbd4a528433f62d5130f3d4a324ca5e6394742e750e5010f3c43d4941eb508420867e6194f40bb58e20482f560cc531dd145314c39d4310d209f588534427e6494630cf189540427f6510e10ab98a4350b756115220af99231c867d6394642cf551510c36d5148020bd58442c867d62944439f58252d06de6510d31d754e32086fa6090a10f694d401027e6515120bd987424873d6255010cf55041c427e6414d209f596430866f6548020dbd4f200833e5450620b798c530833c54c85309fd8153d0abd640cb40de983540827e6494e20db94942843cd52cc030eb15142482f76150110dd984530433e54cc830fc98241c433e5494c209f98a519027e6394821bdd85544836d6590b209f595329073d5410420d7550430c27f658cb40dd54720083756294440af98c435067f61550208f99353c87ad648c920c7153314c27d658c640be983210835e53900409f594414c27e61d53309f986540c27c6355220d718a5390b5d61d4d40bb988300825e6315020cf953431037a534c030be582320827e60d4f21db94b41043ce53c80209f592534867f6590d21bb988548437a6015021d7551300c2de6308540af990325073e5490c20b798e41c433e540c0209f98b530837a6015230bd18540c42fa60d04409f597420c33e544c8219f990530427c6550f10dd545210c35d5314642bd9845050a7e6215231bd587430873e54d0b32b758e420c7766114142b758e410c79d53d0641cf590520427d65cc8419f588548c33d6590f42b79824310e7d6590431be181314c3b654544309f191500c67e6115021af590518836c5394840f354b32cc27c6254e10db95142c833e5490410dbd0e52042f76550710d7d81530867f6154c40de546200827e60d48109f98b540833f5495221cf989540c27e6394640cf950434cade6308610ee582439027f6510c20af992310c35f6354c209f980525073f64551219fd81548cb355444010d7582530863e6414910d310d520c3e95284010d714c43883766054440b7d8d410c36c52885309fd9441c82dd6390a30d794d31482ed6290520de983548827d658ca419d984504cb796014520be980218c2bd648ca40cf185548cabc644c030b7982434c2f4614c921cf55043cc36e52cc830bbd
  | 16 => 0xe5494c21bd986324435d534c8209f58f525025d6314b109f98254ccaf8604c9209f997404835e5390840f954a21c437b5094041d7d4f40503ae43d0942d794c32d079d6050c43db549320435d5310f20dd50a510836d5210440cf989540875e6395330bd58632c875e53146429f988538427f654c940d7952434c27d6588740ed18542506de6390030dd0c9510c3bb41d0140e750d40cc33c6355010be980528c79c4350931e7592324cb5d534ca20f3d0d32c827d65d09319f596428c6bd648c910f3149324c27d6095110dd98a510c2f66108110db94a21086f561d0841dd54e51103e64248421b798e428c2de6314121e750c43ccafb6048520cf951200827d61d41429fd9421cc33e64948328f990540867e61d49309f994410c37661141439fd94319027d65cc020ded95401027e65cca40b758e42d033e60552319fd9152cc67f6054f219798c5050b6e524c8209f994211027c6550d31f694e401033c62550209f18d511027f6155220be982429036e5250410be98021d027e65d0940fa909208436d65d0a429f99053843f15148020be181438c2ef64c8720b758c218823d6414b10cf990540827d60d53329f191528c79d63905419f58654882ed6214c419fd91518c27f6154e40b718d424c67d6550f21bb592204836e52084409f992500c76e534c9209fd89519027e6510d329f992544c6bd648c630d714f308427d65884109f195424cb6d5290a109b58b540c2ef62505218f596540833c54549309f58953083ae648cb20bd58743d07cc534cb209f986540cabd6010e409f595318833e5410c429b98b54cc67e6294c10db58a544c67c6454231c754f40103746454420ee58342d033e6414e10cf981540c3f160887109f19443486f96090620bd9845010ebf6150c43d798c54cc6f565c8621d714d32c833f54d07309f18550d0a7d64d4e219d987540835e530cb209f59740082be648c520afd9130882dd6315020cf54b41d027d65cc421d718d548837642944209f18d528433e54d07209fd81540ca7d63d53109f19442442f66190821ed953318c73d5410f32cfd9541d035e538c410d798f540427e6214d10bb58a400835553440109f580544caed6210f20cf552430cadd6110d32d714f32506bd648c431b758f5090b7a6014e20cf594439033d5410f319f59632843af6250b40d759743cc6f66190f10db14d324835d6494c109fd81520c75d6314141db94942103754354430dd58754082ef6448520e7d4f43502f9600c520b798f54c82ed62140419fd94430c33e6415331bb189414873d65d0a42d794f324439f53d0540b798c219027d6590c40d714f304827e63940429fd96218c26f6548421cf15142c86ed6214440bd98450d0b364354440db948420427d65909309f594410c65e63d5121ebd914210a7e65d0d20cf55342
  | 17 => 0x87109f98354cca796584010d694e500875e538c621d754e4390775510c440af59052c431f5410e30cfd53434c67e6550d10af59231d027f6454420d7d0d5190f3d54cc4209f98854cc33e54cca319f997320427d61d4e209f19521cc33d54c8430b798c214435f53cc941dd98e51082dc6354940dd58454c867e658c5219f58e510435e53d0f21db94a21042f56114332cf95043c86bd64083109f195424c37761551209f99641c82ec60509209f58c540433d5415130edd0941c433d54d0520bb98232c836e5354840bb189515027d658c810d7d95300c27d63d5320d794c21102dd628c531b758e420c35c54cca329f197420437651cc0309f596434427e6494d109f99532442fa60084309f992544cabd644c540cf952400437661d4f109fd89511033d6414132bd587531033e5494c21f9981210866d62141319f9835150ade61ccb319fd9643c836c5210910dd15141c42f66110130bbd8542c836f43948409f597420c7ea6090b20cf58e548cb3e5410b209f994314c36e52d0440cf95141c823e64d4d21dbd48214c35c544c930ed504414c6f960d0440cf55043043765248421d798c54cc27c6510c21cf55353042be648ca20cf985540435d53104209f99532506ee62d0d20be586100439d4310c209f59442083365494430bd984314435e6314f10cfd5141cc35e53cca40cf553400c33f41540419b588540c6f56114a40d714e51503e95244010d7d9531cc2bc6448440d994a510c3e76148720f9509210875d5390e42bb18940c827d6590e209f19743043bb43d0140d794d42102f96014c429758f54082f965d02409f580540876d62d53328f590514827c65487409fd94438876f6548720dbd89528426c6550920db149424c67d6194342fa50920842f5648c710d794e42087755190630bd584408c32d54c80209f59432d02de63101109fd85500cb5d53d0c419fd9150c86dc63500109f58354486df6350030cf552430c2f6618c821f948421443756494420cf0c1540c3ad54548109f996414833d544c010de983538835e43540439fd8552cc27f650c620d7594430c2fa60d0610d7d4f314437950141329fd95310867e6494f21cf04154042fa6090620cfd4c4350b5e6194c219f582544c2dd6390740f8486500867e65908109fd95410836d5250a10f994a511027f6255030b7991300c33e5484010bd58a31443745394420be980320827c6115110c754e43102de6410d329f9885050f6d6354840cf550410876d52104109f996424cb9d6390942af593520c2bd648c8219f98353887ba60d0f40cfd91540c33e6415010f34c8320c73e5450010ebd0d4210bad54cca329f18950d0f5f5390d40dd944210833f54d0531c755153082dc6350130f9d8d210877751947329f997414c73d5450a329fd94428435d53d0f10ee181415039
  | 18 => 0xbb588538433e5450e109f58c50486fa60085209fd9542cc2f66194d42d794f431033d5494c219f993520436c6054830d755253043e74348421cf552438c6f661909419f98c530875e53d0440dd14921442dd6388530cf99742506dd6390721d754c32c82dd63d4420af59643d073d54d4a31cfd86540c35c6294c10ed58443d067e6194a40dd546310836d62d4c10d74cb514c27d6294231be58042c836d658cb20bb58840c425d6594c20db54a420c75c6355210af99121d03775194743db54b311033d4154041bd58742c436d520c430db94a211037754c42109f98053507d7324c7109f58f544835c5350d40bb58b530427d65906309fd8d508867f64547309f9875050edf654c8329b58b54cc79e63909429f58b544427c650c940dd946410c27d60d5132cf551430435d5410d32cf952408c27f6254630f5d4d314427d650c720d714b324c7cc434c920af992310836e528c841dd947410837654505109f98453082df654c730b798e41c82de62d0d32af59352042bf6454e10db988538439c544c530d754c430434d53c8020f354d52042de63908319f195314875d534c7219f18553882f561d4830be580214c3755114620cf553438cabd640c120db948421035e5350821cf54b411067c6354841cf553418c2bc644c020b7d8d52443775150540dec8650086f762505109f59742442fa60909109f191510cbd65394440f394b32cc6bc64549309f19541c827e6115332dd944400c2dd644c930f34c9304833d54d0e30be583328827e65d0a10db54842d03765148440be98031882bd648cb41dd54f10043774394420be983310c33d6494d21be58021043e9608cb20ed952411076e5288710cfd85540c2dd6390b21cfd51414c6de6390b40cf186540c39e6410d31bb588509075e63d5320f9485500877a60d5230d754d30043f2514c0309f580530867e6315030e710f414c67d61d4d209f597424c3755394420cfd8e540835c1054c10dd10e511029f6550c43b758e410c36f6354810d795331cc37751945329f5875250e3f6454d109f58854cc3746054440cf151408435e6314c10db588540427e60d49319f58650d0f9d5494c219fd8d520427e6294343d798253082de6314c21dd991510833e54cc8209f98e50d0ade644c931bd98643cc67d64d4d20eb508428867e6215010cfd91540cbeb5248210e7553430c33e54cc421cf54941d033e54102309f595321035f53cc521d794f420427f65d0830d714d215027f61551219f195434427e60d4c20d754d30c82bd63d0940cf15041483776554420d994951103b941d0140cf551210427f654cb419f997434c33f5494930bb988430caf66110010b758c52c426d65948109f185520c27c61553309f58e52106ef644c920dd54451483db438c030bb98b54cc67f65487309fd8152d06be640
  | 19 => 0xd5090b5e6194c10cfd50434c27e64149109b98b540c2f96090940de982528427e6590530d799253083b954840109fd9742042ee62d0320be582410427d61d5120b798c548833f4354043dd0ca51102f66110b21cf94942d075d53cc420d7d85530836f5290940dd14921c42bd6010f41bd584400c2ee6214341af59050ccadd63c8730be582318c2f5610c8319f596214c33e5450810ed59231c43e44248421cf986548cb3e54084109f594434827d6394720cf582540875f3254032d754d430435e5388020af593510c27e6414c21cf58d540867c6254c109f99250c86bd648c9419fd8550d0a7f6055221f358e4210b5e5310840d754c5390be76248510db549420c7795014242bb98830882bd6414c21eed53304c25d6314810dd945410827d6550a30be98043d02f96090a10bb98a4390b7b6494021cf993538867c6355320cf551418c3ea42481109fd97318827e6414931b758c20c439c4350531c7d954310f5c53d0d109f58b544c35f54d0f329f58353c873c54d0932d718553102bd648c721db54a32902f661d48409f18d5010b764354440b798d21cc2bc6454910cf952434873e548c8309f990520427f6354910d794e32082f661d0841afd91300435e53d0c21af592328873e5444010d754f318833f54d0210be58341842ee620c520d714c32502dd6390520ddd4e511035d524c030bb588310879d4354043e795153083756588710af58742d036e62d53209f19741483f141c4110cf550320436d52cc410af994544c27f6154c10ded4250cc73f6355010b758c424c73e5454231b798e420c3784354021bd586308433d54cc4218f993530863d6494732d794d500875653544409f58e500875d5348410cf953508ca7f6154c209f99632902bd6010d42dd952510827d6510c20dd59710043753254430db54a300c2f960d0c40cfd53424827f6354041af99332906ee6210d21d794e4390b5c6114d409f996428c67c6510e109d584540c2bc6454e209f98653d0a7e65d0c218f99252cc3f221c4110cf550428cb5d32d4131d754c311036e6094810dd50e511027f65cc4409f58e51d0a7f650c8409f584548cb5f5394d409f9865010f5e534c410db98a544c7744294420db549328c6be6415020db54b10043d4514c730f914521c835d5310e21d798953042bd64d4a31f390d320cabd6408710a71814310e7e64d4910cf551414833e6355021dc88550086f96010630ed95310043ae54c80209f98e534433d54153309fd9732d037561d4e10bb586424827c63546209fd9643086f56388710ed10d414433e6355030db588548827c6354720f8485204427f658cb41bbd89438cbac4354840f9d91210875f6354c10dd984538867e6215131b7d8d40483d732cc5319fd96430cbd66390510cf952420427e6115132edd5141442f561d0b31
  | 20 => 0x2df63551109f98e5210376518c630af59321d02bd6414720dd986544cb3d62151309fd9743c427d654ca40b758c408c3db508c1309f596424c75d63d51319f59432906ed6214640d754c5350777518c5309f99641486df6350020cf55320082f86048520da54a100425d63145209f58652d03783254021d79895390abd640c020af590520433e5490c31d754c32043b66110f41cfd52540436d52d0030fac8550086fa608ca10d7151310c67e6315032f594f419075e54cc631ded8152442dd6314241cf54d401036e6154830d7d8d544c23c6454d10d7153314c2f7654c710cf550548875f5354940d754d210867d654c7209d195314427f6548421cfd5342c873e5450a30be982410435e5388421ed10f415067f64546329f98e548865e6590d30db592520c35e504c030f34c8324835e53d0c42d7d855390af96090a40d354e521036f52085409fd81518cadd6310b30d798f540c6f96010740b719332cc75e53d04219f595430876f52509409f996214c27f6510a30cf99353c86de63d5321dd547401033e6414c10bb98a430877565d0641d798453502dd6390b32decca50086df6350931d7d4f215027e64d4f219f98053486f561cc921d798c524435e53cc0109f997324c7cd6210f32cf153424c73e61550209f58a540c67d6014d21dd54721103765150030bd58e31442dc6354142b758c214c33d5410f20af59231483e860509209f597210c27f6548020af590504c67e6510510be980430c27f658ca419fd97418827d6095031d7d4e53483ba6090e40d794f43d0aed6290220cf552428cbeb21c8120bb189544436f524c941b798e52d02bd6414910d754c430876f52c87109fd95420875c534c621de48550086756115020db98b54c867d6114f20dd152414435e53108219fd8d50907b554cc631db149325067e60d4c219f59253482bc6448640cf54740903cc43cc932b7181324c27e65cc920cf990530876d5254430d7d0d528c27d6094442af98e4250b7960d5310db597208827f65508309f997414833d54cc8309f58f520433e6415032d794d411027c6054a41cfd51214c33e4354742bd984308427e62946439f583540877b50940219f994304427d6590820dd544410c33e6415130edd91411075d5314f10d794f430c67e62d5210dd551100427d65486309f19152cc2ee60c8520db991520427e65d0931cf552434caf661d0f21d9145214833f5450220dd987540c6ed62d5331af990308835e6314a10fa50920443db53d01409f996325067f6510020fc546300c2be640c740ed551510c3774254420b758e424827d6194d20af98e43102de6390b219f59432042dd6308410dbd4a214c27d6590c32d7d8953102be6290d429f98a540c27d6494910dbd8954443cf624c930d798c53886fa60d0510cf15342cc2f961c81209f18
  | 21 => 0x54480209f181531067d60d4e21b758e41082de6390631db0c1520c39d6150c439fd9641082be6414520fcd81214425e6315210ddd9541106f661d0b109f58c5050b3e6494b30be980310427e65cc940bd58430c435e53504219f58453083f121940219f99721d02de63d4742de94610042dd6314221dd58453442f96088710bd98753d0a7f6054c429f98a53443785248110dd54531083b541105409f99743443f061481109f990540873f6555021edd9141c433d544c810db553200833e54cca329f185529027d62d5030b7d81324c6ed62103209fd96320875d514c030bd987530839d4310e20eb952520423e6414e20fa58242c837652944309f98c54c836f54548309f592510436d65cca32d7981531033f540c930be980434833d5490f21d794531cc25e6314121d7d4f325025e6314b10cfd51404427d658c831d714d325027c6550430af99021c827f65d08319f99643886bd644cb40d7152530867d61951309f99441cc33e5490f109f98754c827d6414b10d794b32cc73f52d0540db90d520c27d6588440af592310c35f4354a439f58f544435d5350c219f185544ca7d654cb40bb98b30c827e65d0b319f99543c835e6094c40cf58a548c6f96014a41db14e32c82dd6314720db54852cc76f5294b30cf18d540877764944309f1815110b3d54153109f59654082de6310631f9d89210873e639501097d8d548433c52d09409fd8154c876f5294b10de50d500876c6254d10bbd8f21c835e54cc930db54b32cc27f6454221d794e41043e651c8720dd984538827e6510540cf95340c433d5490621d794f31c835d53d00409f58e521035c4394030db58b548827c63551209f992510827e6510920b758e420827c6355021d7d80535023d6414a10cf950438cabd6190f42d5d0d510c3776554440f3d49324c3756114f21be58342882fa6008420f698332cc35e53100109fd8d540867f6548540de58353c833e5454632afd95401027f6510420d758c524439d4310e32cf90d51902bd6010d41b759332cc2be6494d21cf50b50506f560c85219fd9741c827f658c6209f19643c42df6150f30d754e30843d7434c5109fd95320c6de6390920dd946400c33f6355021cf950510827e6294f41bed81314c2bf6550441db94b320c75e63d5032b758b314c2bd64cc841cf953430435f6355230cf95341042f561101209f59253c427f6454b30d7d95320cafa6014432db54e520427e6494810bd98730443766254420d7cc951cc2dd63d4440dd14951102be648c8109fd9632106ee6214043d758c5050a7d6095021d710d52cc75e6315332b7582324cabe64cc940cfd0950d07ae5250040afd9153882be648c930bb58a43c827d6395220f654e10042dd6314142cfd51434c2f96014443cf153324c2dd64cc7309fd8554cc3755114443d794e211
  | 22 => 0x440d714f31c427e6510431bd58450d0f776155121bb58b531027d62d4e10b798c51082de60cc530cfd49415036e520c410b758c54842dd60ccb31dd984548c7d55348421af992318835e65cc9309f1895010e7d654c4409fd94410435d6395130d754f200827f6354640cf551508c67e65d08319f596520435c514c530bb988500c6de6314b10b7d9543cc2ed620c621b758043ccb6c61548409fd8954842df648c130f9d05210867d65c8410af592215027f650ca409fd9530483765248710be580318833f5490e10d714c525027e65d09329f597318837652544409fd94300427e60944429f99252842dd63d0b32af191308833d4254442bd984414436f52949419fd9721cc2f56114e20d7d50438c3773254440e7153434c7765494430ee551100427d63943219fd81544863e6494732e7d4e405027f65d0d10bd58740443e454484219f58054c865f654c832d594d51082f661d0b319798f540835e6294e41af592310827f65cc910cfd5254c867f64540329f58a540433e5450e329fd9443042be60d09409f99442cc67d60d5231dd144214c3355494430d7d8d544c73e548c820d7985539073f4254242af58b43d02df63552209f59051482bc60507408f99052842be65d0540f3d0d520c36d52c8430cf152324c35e6094e41cf952328c73d5454232d798e52d06f96090910dd90a510c33e5450410e718d540c33c43940409f980548c7775194442b758c400c36d52c80109f99632c435f60d4d40cf550548c76e6215232bb189434ca7f61543329f592500427d60149419dd95310c67d62d4131cf550410435e534c430cf95053087ce534c8329f59253c87765288510e794d40102bd6408720bd5865350a7e6394020ded4250907d563904419fd8152042ed6088521dd4ca511033c4354b41d794c31c42f76150d41cf95353086ee62141319f997418c3cd53c8421de90e500867c654cb409f987534835c43548309d984540c2f4614c110cf952210427e6394d20b798e42cca7f6550b319f196314835c53105408f997435036e5210b31bb5885010ef960d05108fd9541106f6658c510ded42505067e60d52219f5865210ede6388730b798f41cc75d53cca41cf55054cc67d6494c209f195424827d6214131e7d0f408c35d5390c409fd855010aed6214031eb98843d0a7d650c8419fd96319033e54d0e309f588540c75f64d4d40b7997314c374538c710b7d8d515027f6590e21ebd4942d027e62d5331de949208433d54cca31bd987531033e54d0630db94941102ed644c920d7551530827d6395010d794e320cbd7634c4319fd8d54442f56190f219f58854cc67d63d4542ded81544437651c87209f99643487795014143cf150434427e60d50329f594418c27d6094742d710d510c3756114a10cf950420433f6355231bd586430c7b9
  | 23 => 0xb949210c2be60d0c43b7d8d5050776514c6309f997324427c64548109fd815110edd63146409fd8d52d033d6255231de580540ca7d6590f20bb588510c3d953440109f992510c377514c5309fd85540cbf16188210cf153414867d64d4b10af5974290a7f65501109fd9732d077551cc430cf95043cc27d654cb419f987538835d5314d21b7181434c3695244010cf10d529033e5410c30bb593214827f63551219d98454042fa6010b209f583544c6f8604ca209f997410836f52c8510bb58b31c86be648c9219f5835350af6610c110bb18950506f5610cb21be582314837551100209f99252cc27f6155110de105500867e650c421cfd5242443f151880209f18d54c87f12148110b798c52842bd6590c40b758c404835d5390e10f9545200835d5314840db981520c2ee6214430d754c308433c5410330f554731cc33d5414c21af99131d039f6350d40be98232442be640c010bd58720c433d5310f41f54c431cc27c650c421cf951300c27d6114930db94e32c839d5454c10d754d328867f6454d10d754b31cc35c53d0d209f98a54842de6390c309f588544c7776354420ddd85544435f534c710b758f5190a7e6015010d794c430835e534c020dd14a510c37a6014810fc181214427f6154e20d715253043f1608c710dd984540c67e63145209f58353506f56110020db588544835d6094e41bbd89514c35d5310410bb98b438cb6e528c0109f18154cca7e61141428f596540433c5450230af58b4390e7e6394a41af18542d073d5494420bdd8e21c42bd640c740fa58321c833f6455220d718d54cc76c4394830dd50a510c3766114b10d7547308c32d5454810be580320c2de6308010cf182548cb5c53d0e10ee10e401039e54cc6319f595418c27d62d5331b758e300c35f5410c30af992320cb3a54540219f59443c83765108430bed8121882df6550c43cf950508ca7d63951109fd9741082df6450c439f185521027e60151219f994434c73f6455332fc18620442f96015021af191504ca7c6454420af19130483ea5248020dd54730083655294440d794d400427c65d0e109f98251ccaf76544010d794f429075c43943319fd95438867e6094c42afd894310eee620c0108f99252cc67d658c820cf181548cb6f528854097594430c33e5488020b798c434c2be648c431bd58450d0b6e524c0309f195424c6ed620c120ddd465150efa6015031f398e4210b766354420af592435027d6294241be58043d02ed62d0521d754f21102f9608c9309f595410c33e62550209f596540867e64d4d21d794c510835f544c030d794d438435c6054c40d794e10042f661148309f196414c3f12044010cfd9542d02de6390820bd18141c42be6414032bb98a438875d534c8109f59642442ed62d4440cf990544caf960105209f99253043765110
  | 24 => 0x40c427d658c4309fd96428c76f65508429fd81521075f534c220de54050486f56188010db54832d06f6610cb31b7193308c27e6114810d794d43082ee62904219f58054ccbd55354440af59121d027d654c7409f19542c42bf6550740cfd50414c27d6494021c7151314c39f43d0030f598732cc67d6194a43d754c31c433e64d4c21db949429079e5390e409f994420c2bd6414e20e710f428c23d64d4810dd945310c3da53540219f9875050b5d6194c20be983320c2ed62105209f98a54cc27c6548430dd14521483cc524cb30dbd9252042f96014c219f597310823e6414131d7186539077a3294021cf553310427f6590831db54b320c36f52509319f99743c83e66448421b758e428cb6d4394830d754d32086ed60cca32db586520c37a5144010b798e51d0a7d65108319fd8553c837651d04309f189500c63c6454d20db549219027c61542429f98a51cc37b654c030eb95121086bc6150941cf10c5050b3f6454d20be980411035f6550c439f58f50486ed62152109f594328435c53cc5409f58252cc75d6294e419f18152d06f76384110bd98432c427f6590820cf152524c27e6214f10f694d300c27e6395220dd94631883d563907109f588535075f53d4940bd18121c43d6414c431dd545418c27c64543319f993530874d5354810dd54741d033d54c4010d7d4f32c833d63552329f98b540c2ec604c920cf952310866d62d4c10cf153434867c650c910db5885050ebe6390d42cf551428867d64947329758e52d067c60546439f195414c2f96010c3097596530435d530c821af99252cc6dc6050c43bb58b304833f5490520dd941100435f538c940bb58b314827e6294e40af59740903765490441dd597318c67f6254241cf952434c75e6315031d7945310c76f52481109f980524c7ad4250120cf951210c2dc63503109fd95438427e60d50219f582521067c6354840cf985548cabc644c4409fd85544c27e65ccb40de54050cc67d6510c32eb952520c33f5490e30dd546218c39d5310f41b758f544875f5394d21be58a200833d548c830cf552430c73d548c420d7581539073f6550040cf94b42d035d53cc720af983415027f6254f41ed50540c427c6454a10cfd53408c3765394440eb10d42c827e654c940d794d210827d6315221dd591510833f544c9309f98a53c427e61d5021bd59121c436c6454810afd91534835c53cc621d7151320ca7e62d41419f58054cc67e6294031b7d8d544833e53d0842ed504414427f6055120f690f304c36e5290a419f992544825f654c030dd546410827e6414e219f98652103796015320af99032d036f52909319f18d5110a7d6195131fc181314427e6215230cf952430cb5c6214d409fd9642cc36d62d5010d7d4e314827d6394420d794e40042bc644c8409f18152cc7d95348020d
  | 25 => 0x27e65c8440cfd954210b775194530d7192530876e4394810de18650087793254021d794d100427d6494c30afd8d4310f5e53508109f59632d027d6414d10cf99054cca7f654c521cf952508c67f6510d21e714d43d033e4314143af5974390e7d6294410d754c410876d52c8640dd545400827d6588630cf950320c27c6454d10cfd53414435e61d4d409f984535035d53cc410d759153907eb60c8520bb597328ca3d6494730eed8143502f960087109f98e518827d61d4c20b798c41cc36d528c410cf997425027c61540429f596431073d6414131dd946210c36e52d0b408f994544c33d548c421e7d4d415037565c8621d758f54042be648c932bd18542487ae52d0b41bb988540c73d5490d21edd0d411073e54d0821d794c32083b654504419fd95424ca7d658c540cf182540c3766114f10d758a531039c6454c409f197430833d63151309fd9431d03756114e10d7982530875d53944409f992530c67e65085409f592530433e54506309f984538836d52c8310bd584208427d6394242ddd4a511027c6510c20db182520c2dd6390a20cf55342c427c6550620d754f100427d6394a10ddd5151082fa6014a41de94d500876e520c830de540508cb5f5394c209f98e54083ad54484219f997319027c6590e21cf553420827d6590d21dd10a510c36e520c440bb588300835f61d4d40de59620843795284010ed10e51102dd60d0e309f996434c75f654cb308f593530875d5394420d794e420427d6214530be5805110a7f650c8419f99742cc3755148620ddd46511035d53504409f996315027c654c620bb58a31c83e552544309fd855290e7d6014931fa94a401027c6550520cf951430c35e6314e209f58f540433f54d0f30ce55150087d653c40109fd9641cc2f96010d20af99221d027e62d4543dd945318831d4354043d754e521035e6314f21d754f321039d4310d309f994214839d4310c10be5805190b5f6294c40af18143d027f65109109f597414835d538ca41af990528c27e65d0730af590308827d61d4940db94842d073d5150040db988548c2f561cc841d7d4c438837651cc4409f58f54c86ed62d0d209f987530873f54951209fd95400426e6215230ed504410875f6254e419fd97428c33c5450521d7d955390b3d5450a30cfd52544c33d6015130cf153524c2df6350220bd58430c833d5415321bd185420436d528c440cfd51404835e6314810cfd52324c33c6055030edd854250774534c710db94b400436e6215320af5824350f6e62d5020af990504873c5450921d798c540c2f661142329f98e529027f6154a30dd987548c67e6548530b7580430c3745494430bd181314427e6015032ddd0e510c27a6014c21b798e414c67865481109f9865390a7e61d4f20a7992314c71e5454c21b758c410c67c65d0910bd984
  | 26 => 0x3d4443e790f424c3ad4210b40cf95243c82bf6550842dd8c9511033e5410c20cf55132087e541484219e580540c67f6055031db94d52043e752485108f59052042bc644c640be181324c27e6494720db54852d0ef9600c820b718131cc37b5494021ed54740103755190020bd587521027d63152109f986540827d65085309f588548c75e54cc431b758e52506ef6550b20d794f434867e6314c10cf95340c83e76048421af592318835d53d0f21d7182530867e6215032be982318c27f65d0d21db94b210433e65d0540afd9130c437960150219b588540c33c5410d309fd9442083d6538c7108f992534873e544c020cf15240cc35d6394740fa18321483d7614c931cfd50424427d6590c20eed81415027e6590930af592328c2be6408010dd586544c67e6095132f90c5210873f6355020dd946300835e530c440bd98453082dd6390620de980540427d60d5031fa8cb204827e6494620bb988538433e5410e319f58653c827d6294f41dd591510c2f960c84209f18153c867c60552319f19443483cf634c832f954d210866e6215030bd984521027d61950329f58a51d0e7f62551219f592518827e6414e209f58653d035f534c510d719253083b442504419fd8d50d0af76350710ee153304c2f56114830d754f32843db32cc1309f194424c35c6194c40b798e525027e6194b30d714d434873d6355231db54b42102be6414630bb98851102f763485109f98a501067e63d4142cf553428435e534ca10af992314c27d65d0c20d794c430caf76148110b798c324c35f53cc210c754c43d0ade6390a32db54b32cc6be648c410cd10d51103d44354430cf984544c2f661cc9109f993534827e6294e419f59053483763154031bb98843c835f5410d31af99232106f9600c410db548524c2be65d0940b798c51c82de63907309f582534867c6354740cf4c0544c3b542507109f98e52042bc644c010e7d93535037b63940219f984534435f6355120af992524c67e6094e41d718953043af6450920db548528c67e6588440e750c434876d2154021ded42508875d538c420d714d435067d6414a109fd95310433d548ca319f195404833c6255021bdd9131c433f54d07109f586500ca7d6394821dd946418c27d6510821dbd4a52906bd648c831db94830042fa60cc9209f99631d02be6414e109f195428c67d65d0530bb98a31086fa60d4c21dd944310827e6395321f5545300c33d63d5130be583540867f6550530d794c21042bc644ca409f996325027c6154343b758c400833e5410c41db988504c75e6394740bd584539031d5410d31bb58a21086ec624c120db18d52102bf6454910dd987540867d6195020cf15142cc6f96014c41d7d8d54842df644c530f34cb314823d6494b30dbd4b324437b3154021dd945410c2ad648c920cd9515108
  | 27 => 0x20d794d320835f5494c21cf951310873e5350f409fd9431c836d6215031dd5445150e7d60d5321cf951438c72e5494810d7d4f30482ef6350b20cf982540835c54ccb319fd94310867f6550430bd58443443755294440fad42204833e54942329f980548875f43d45439f586529027f6550a10cf18e540c33c5450d30cf99054cc36e524c830d7d4f304427f6548110eb592320cadf6250f30cfd0b515025d6594c21cfd51434875d54d0f31dd552510c2de6308630db14d520427d6094e21bb58b43886dd6395121cf553200433f5450920d7d92530427e65cc840cf95342443d443cc531ee952300c35d54d0f32bd98630842f665885109fd96434835e63d48109f18153886dc64cc030d758b535027f65cc420d794f43042f56110220f510d31c427c65909109f194300433d54d4420cf95243886f562905109f594324437454505109f58a54c433e51d0740cfd5141c436e524c841d794d43902dd60d0e43afd8542502bf6350740bd98453903ea528c030d799153102ed6448520bb98821482dc6350320be58042103746394430af593530435d53d0c42bb988408c2f860486209f596210827e6414a10b558e414427e6314a10db94b401027d6094e41dd94641882dd63152209f5825210f3e54142319f98754cca7c60550329f593514cb5e53d0410e750c430cb6e5290a30b758c21c435f6094e41bdd8a10443d7614c5309fd9443c433d5450e20d754f420833d6590f41bd58732cc76e5248010b758c50d073e5448420d7550438c36e62d4c10d3149324c67d61151309f9805350a5d6394b40f54c530c435d534c910e7d0d325037552c4210bb98a418879e6310f42d794c31086dd63902309f592530c76e5290a40cf59053083e754484219f99543482de63102309f181544879d54d0e30d7951324c775518c640cfd52544c75c5490f30cf58b544c2ef6548720bd584528c27d6550e20af98e43506ef6550842b7592304c2de6390a209fd85544c7e52108630bdd8d310c76f5294b41cfd51414439d54cc631d7d95530863e64948329f993524c75e6394441d758c504875f3154031cf553530873d544c420ed90d51103655294430d710d51ccaf960907109f587540835e544c730bd58732c42de63d4a419fd9541106be6414a31d7d4d314867d6095121cf951530435c524c9309f997435035d6294c109f982548c67e65cc921c714f42502be648c521d714f324863d6595021cb549401027d65d0820bed8142502dd61cc9309f98a53842f961c8220d7d82530867960d4c219fd9642086de6390440d7d52530427f6454830ed909411067e6294c40c7551530873d54d0821db54b420435f3254632cfd53314c33e6195030af590520c6ee62d4c10ddd4a510c2dd63d05318f99053082ed63c87209f5845250ede61cc931cf151214c39d4
  | 28 => 0xd9443c827c654c5209f99353882f96010a10be58021c827f6508010d754d318833e540c8209f185540ca7f6054b319f992508c67e6590120d758e51d0bcc534c9209fd89548c77751c8540bb58b404827f654ca10db549310436d528c830bdd91214435f5310d409f59421903ac43d0942f554e31c436c6194840f54c4314435d53c8010db58d520433e5410430cf151424c73d5410c309f181530875e53d0040dd546310c27d65d0431d718a53087745354420e794c43d073c54d0b319f58652d0ebe6408730dd509510827c658c940dd192511035e5350410f3d8932cc6dd63d0731dd54421082de6390610cf551310867e65cca10cf990548c6be648cb319f595320435d63d52309f992538433e5494a319f585530427e64940109f592530ca7e6014532af590300436c6194810b7d8d400427f6454a10cf150324c3ad5494830cf950328c6ef63881209f194410c6df6350130be58b108439e5410d31c7953318c76c5290931db14b208433f5450931db94b218435e5388410bd58420442ee6210030ddd85534873f54d0b209d185544833f6455230cf551300c36d524ca409758f544873c6255030ee552200835e53ccb10b7d89320caee628c621d794c410827d65108329fd9532d02de63d4242bdd92214433d54cc020cf990514827f6550c31af99232c439c4310230de14a204427d6094831cf15142cc37960d4c21b758f420c6dd65d0f329f98e510877752c4010c7553300c36d54548109f58e52042bd648cb40de951500867c6550e109f99631483ad42d0520d754f310873d6494b319f9865010b6e5210430d714d32c867f6550e209f596540427c6550a10ddd51100437b5094042db14b214436e6215010bb588504c76e4394840db189544433f6295030e710f420c36f6254910be980438827d6294e419fd9532082dd63d0730cf951320c2b5648c5109f996424879f43ccb40e7d52304c27f6454031e714d435027c654c810dd947400827f6154d20de54910042dd60d0c30bd98450d0f5e5310810edd45415027e6195230af993500877751d0520cf95143082f661103209f592528435f5350d41cfd9154887ce5394810dd909510827f6054c419f99252cc74e53948409f98b548c2ee65909209f996424c6be64d4b31bb996324827e64947329fd94320433f5390d41db949428c2de63d08319fd9742cc67f6550440db549311035e6315032c794f41906fb6050a40cfd8c544c27f62550209fd8d540836e5148421dd584548427f6254e10be98241c43b654907109fd95320c2de6314840cf151424cb3d64d4c10bd185328c6df614c431cf55152042f561d0f21bb181214827c6054843cf15342483775194630bd98643906f661ccb41d7591530867d65ccb10af58e40502ef6250d32f5d4531cc27d658c910db949429031d5494c
  | 29 => 0x29073c54d0d32d754c43d035c4394332fcd81314427e65d0f10d7985531027c6255210be58e300c27e6194e40d754c534433c63950209f592520427d61141439f595211027f65c8740d798553082f5638c431b798c400c27e6510630af590500c7eb5248110d754c439067d65d0e219fd94329076e5208010d7151314c27f6354a419f597400c2f66108510d714d32486ee6210120db988540833c5450220b758e424867d6510e219f99731442fa60d0b40b758f404c39d5390c40dd592510c31d5454c109f19643c833d5494231fa94a20083792194021cf90c50507ad42505209f195418c35d5394a419f596421067e65d07209f191534826e6214c20bd58730c42ed620c220cf952410879f43cc540af993508cb5d6394b409f59251c836c5290940b758e410435e6194c40d7597430c2dd6390530cf55241c42f7614c8109f1815290f5d6590f30de55150086be65d0941dd4c5500c75c6094c409798c548827e65d0e20b758e400c2f96010620b5987434c7e64348421dd18a510c2bc644cb41cf59252cc26f6254d10bb58840cc27d6508430fc881100427d65cc84097d95310c73d42543419f98e50c86f661cca21b798c21d027f6550520d794e500875d538c8409fd96418827c6454f109f98e54c427f6154a40bd9845310b9d43d4043b7983324c25e6314c209fd8153482f56110f41cf585540839c6150c43d754c539027e6510520dd144414836e6094830db94920c427d6548730cf552410833e548c010af5864350b9e5310d419f597430c35d53d4420dd94e510833d5490e32af5824250a7c6054732af99021102bd648c830f5947300c2fa60146429f59443c86776544010d7d81539067f658c420d7d4d215036e6214141dd944300835d5310e42b7990434c67d658c410cf551210c27e658c510db58552103ad42109209f992520c75d5390e40dd545319027e6590c21f9949100433f5450d32afd91504c7775188520bb58850d0e7f6590a10de10e500875d534c4209f18d52d06f66188210d794d324433e641512197d954310e7d60d4542b718d524427e658c841db94b21102dd62d0f31be98031c43764394420e714e43506de6390540be980214c35d5354810bd98642c867d62d4c10b758e424c33d54100209f997428c7d5310c421f9486500867e6494821d794f318427e6550e20cf95043cc75c53d45409fd96321031d5310c408f19153882de6110f31f948421d027e65909109f99442cc2f66190010dd146415039d53d0040db94b32042dd6390810bb58850d07ad5448020ed952210867f6550831cf950310433e6510d41be980210435d6194c40d7d4e515035f6355110db149204433f6395010cf94541d035e53d0e21de94a20842dc614cb31cf953530827d60d52329fd89510c2dc63552109f597218c36c52c87109f
  | 30 => 0x3d54904219f984544436c64548309f594414839c43d0b32cf550320c2dd644c5309f58e5110abe640c310cf187544c2bf61504419f592508c6dc648c932cf593530875e53cc420ddd44214c35d5314d42dd10951082bd648c5309f593534427d650c540cf982540875f53cc621d7153324c6dd60d0f32f698331cc35d43540439f597430cabd6408440db548400439d43d03309f586544429e6390541a718d401036e6214f21db94b310c39e43101309f98e51c827e65108319fd96328436e6214b10de59740903755114743d794d31c82de6314620f34c8324c27d6214d40b798e42042de6110d31dbd4921c437a6014c219fd8d50d06de6314810de50e500875d6494c21dd544510c27e6515130dd18e510839f5490d30dd54d51102ed62880209f986500cb5e53c8440e754f43d02f96014a31cf15342c835e534ca40cf185540c3e52108430dd98754082bd648c9209f18553d0abd648cb21b798c20c42f56110e21bd584530835d5350e429f9825290f9d5410f329f586540c27c6015110af59021cc2be6210f42e795253083745494420bb98830c43e56448421f654e200827d65108109f593530876c52cc910dd99621443ad52d0b40cf153414c77565c4210f9949210867d64d41319f19643043715148020e750c431067e650c931dd94431cc36e6295320b798c210c36c5208540bdd85304427d650c410dbd4a52d02f660905109f59742c427d650c440db149425039d4354843d715332cc27f650ca109fd81544c35c6254e41f398843ccaf7614c9219f582534427d6215310fac85208435f43546309f990534867e6550810ddd9531c427c64540219f99620442bd6210f41d7186530425e6394740db54a321076d5290440ad986435067f6550620be582318827d6294c40fc98231c427e6294c41cf153434c67d6494730b758c40882dd63905219f196424c27d65cc810af592310437853540219f9865090a7e6094d21d754e5090a7d64d4a10bd597318c67c63549109fd85548c2ec624c721dd94521903af5250940db54b218427d62d5031ddd09510c27c6054743bd98632c867d64d4810d7d4d435027e61d5230d794e43087b55488421dd54731cc2fa60d50219f196324433d5450c309fd8d51083766054420bd984434427d60d4d21cfd5142c873f4254042bdd89210879f63d5130d7997314c27d65d0720bd987520c35e5454c21bed89200833c52d0941cf550408423e6415030af99252cc33c52509409f98f54c837651c8420db54b300427e6095331bd592414427f6054b43db14d32c837743544209f99443882bf644c320dd54d510835e5450d30db94a511036c4054840d714e525027e62151309758c54083c65348421cf15341cc39d4310d32b7193324c67f6054c10d754f50906f56390710e7d4e435067d61d5232bd5864
  | 31 => 0xd0930bb588408427c6054742be580424427c6590b10bbd9232c82f56114c40ddd4651483d5324c7109f19542cc67e65d0c20cf14d435027f6454732b798e41902df64cc730cf151414c75e6314d10f9949511037462944209f58c544436d520cb30bd58642442f5611084197d8d548827e6414c20db948320c73d5450e31d754c32906de6390421cf54940102bd6210d41bd98752d0f6d5290a30dd54a510c2bd644c740dd98652c43e75148520bd98443d067c65cca10dd946311036c528c9309f195321035c524c931dd14421502ed62d0e329dd85544835e5350a419f992534867f65104219f98e54487776254430d754e410827c6454f209f99642cc6de6308520e7953438c3e921c8120d714c314827d6590a30af99232c826d6214141af99353082fa60d07409fd8151ccade6394542dd147314837661d4c20b7997324c2bc644c941cf552528c67d65cca41d7d8d530867f6550931d758f540833e54106319fd89508c6de63905109f19732c42f66114a40bb5884310b9f6450f309fd815210f6e5208210f9149214433f6015130af191504c6dd63087209f990514c39d5310d42cf989548cb3c54d0f309f99443887744354440cf150414c2de63d0531dd98453086de6390921e798c4310374654c510d754f32c42be6408540dd547410823e64141219f584548c35c6054e41bd18520c43b55494420b798e424c35d5310f42dd546419036f6254d20a75924310f6d6215332bd185404427d65d0730db94b32102f962c41109f596400c27d6215030dd545410833e5410d21d754f511027e650ca40dd94e314433d5450310cf95132083765148020b798c54042dd6390832cf98a540c3755188420f9485204439c4390230dd54451d0b5e538c220cf9944350b5d65cc631cf15141cc27f658c4109f189510c27e6295110fac86500879f644c030af593538867b654c030bd584548c2f561101309f984530433c6195021d7551530877832940219f98a540c6de63d03309f988540c35d53cc020d798c54882be6408610cf151324c33d5450020bdd92314425d63d5021b758f424c2f56110010de992500867d65106209f596210c39c4310030b798c404827f6550020f354d20082f5644c710cf953310c27d6590730f9484214827e60150209f99641cc36f5294810d7550434c75c538c540bbd8930483cd6390920d754c400833d548c4109758e51d039e54cca32d794f210877654544209f59252cc2ed648c920cf951328c75f534c941bd9875290f3d54d0b329f98a510c33e54d00109f592520835d53cc841bb98843d0af4614c9319fd81544cb5e63d51219f19443883e46048421af592314873f6455020db54a410427c65d0930d794e429067c6510d10d714d32507b651d0740fc486204435f530c940af590208435d6510f329f59541083
  | 32 => 0xd798f54886dc6350a30e7d53434cb6d52500109f990524c35f5454c20afd9332d076c6354810cf54e43d0ade63d0730f398b434cabd6414430db14a215025e6394b41af59353486ed62d0720bb98b540436d5290040d754e318875c6154e419f18d52043e651c80208f990540827c6590f219fd97428c7796094d209f5865390a7e65c86309f582530867c65100109fd97211039d4310f31d754931cc2dd6314a409d5845050b7551cc0309758c52843774294440cf950430c7754354440f3909320ca7c6355210eb54b42d07f1514c030af590215033e54c84109f994424c27d6055010ee552300c35e53948409fd96300427c654cb41bb588539035e53cc8409f990504c6bd61d0d40bb58e424827e6294231e7992314c75e53d0c41cf950518ca7f6510e20d74c9500cb5c53cc5219f584544837950143429f594434867e63d5221d794e5090af960cc730cf953428427e63d50319fd97219035e6254c21db54a100433e5250b40be98332882f66190c21cd951510c2df644cb309f185528c33e54948109f195430427e65100209fd81510cb3d5490d319f98b53506fa60108408f992510c79d4310f10cf550328c75d5350e41bd584521035d5354a41d758c548c73d54d0810d798c538433f6455320af59021842756114e20d9d95210876d5250a30b7583324c7796584010bbd95320cbd960d0e30d794c521027e65c8110d754f31482f960d0e30dd944310c2be6408640f9487500875d53cca409f98454882ee62d4c40af58f42d023e6495130cf550508c73e53508429f98f52c427d6550f20dd58652442de648c5319fd8553d0a7d6414f219f98f54487cd434c832b7d8d514835c53d0940dd885500875d5314c219f994404835d538c4109fd8954042fa60d0c40d798f54c42ee62d0d32db991521027e6494832cf153408437a3154021cfd9154443e92154021bd986434435e5350e42af592411073d54152329f597420873f5495230ded4d500875e5394440b718d41cc75c534c710ddd46518827e6510620db548511035c6094e41bb588508c73d54cca32db94d32c82be6414c21dd95241c42f86050d30b798f52d063f6454e20cf552530433e5410420af99052443665254430bb98840083773294420db549401036f54c8020f54cb314c73d5410e319f98254086f56190821ed992314427e65887409f984534833e540c0109f98c540c6be6414021d794d529067e62145439f19532442fa60d0920be982314833c4354742cf590528427d6510b309f1895110f3f5410e10cf152414833e5490c10dd545211033e64d4f20cf550434caf96010e209f9805250f3d54900209f99731083d653544409f593524c27c6548640d7d825390a7f6254043db988520427d64148109fd96420ca7d62d4d41d794f30c833e62950109f98a54c427e65
  | 33 => 0x86534875d538c421d794e32c867e63942219798c50506ee620c920db14d52102f9608c410cfd89540c27e6194d209f189511027e65d0130be98042842dd63909329f580544c75e53c80209fd8550d0f6e658c9209f594428c27c6550a30d7d4c41503786494021cfd5243882be6414221d7d0c504c6dd63100109fd8154cc79e6310e409f18153d06f9608c530fc485100427d63d4540d754c43486ed6290d42d794f320c67e6590a30d7592530839f5450f309f98c540827f65d0e20af59020442dd63101309fd95424c3e95290040b758d214c3cd5348421cf186548ca3d64d4c10bd58d21c42bc644c310cf99054442ee620c320db588504c67d6394342be98321c827c6254f10d7997324c67d6550d109f59642c431c5390140f5505310c6ee6210720bd58753082fa608ca30be58232c837932940219f99630482ef6548421cfd5254c42f76150810d794e43882f964900409f996418c27e61d5132af992524c36d5290010bd98450cca7e62145409f58e511027e6590a10f554e510827f6590430d794f319027d61d5220be58031c427e63d5220f9484210835d534c720cf55043c86be63d0b41dd0c9511037b42540219f98f540cb3e5410f10af59021902dd6010d329fd8554ccaec6254530bed81435033f5495032be58343d02de6310020e790e404c26e62141419f980544435c6454c209f98a518c35f3254432de58d500876c43548309fd95434435d5314f409d584540cb5e53142419f58b548c35d53d08109f196430835e53cc821af191514835e53d0e419f592520cb755110030bd58442c433e5410832d7d4f43842f4614ca41d754d40082ee62d0721c7951530835d6054e42be580520c73e54480109fd94418c3e92008210d7951320cb3e6414a109f58a544875e6494c21f354e521039c4350a309f59732d075f534c940bd592314435c6254c40cf55242083765188630d7d95530436f6154830bb189310827c6454c209fd8d5090b3d544c830d714f308833f54d0220be583318433d5490210db54820842ed620c0109f992544435e53d0641ddd95310c73d5414c10d7583535027e64d4530b798243cc27d650c010db549300c26e62d4c10af590528c79f5310e40d7951324c36e5494810dd951411067d6014f21db151520425e63d5021fac85204434d52cc0309758e54486ed6290e42bd586408436e528c8109fd954048376518c030be9805310b775354440d7552530833c5490e10cf10d519027d63d4910bb98b31c867c6354321d654d50087e732484219f196420427e62d4d40d794f50086f96010530be58041043e95250040f398e42482ed620c5209f58a548c27d6094f419f59421502dd6308210b798e420cabd648c820db548524435e53d4a41cf58154087e75188521d798a53082f66110e21bd9845090af6611442
  | 34 => 0x823d6595030bdd8931c425f63551309f99641883e552c4010cfd0951d02bd6290f41de10650086f66114c40e710f418c3775194730cf55142842f5618cb10f5cc9314435f53d0d209f196214c36e62d5021bd587424427d65cc7409fd85524427e60d4d21bdd92104427e65c8430bdd81100439e6410e30dbd95320caf4614ca10bd98231c433f548c530db54a42043765150620d7551530427e658c4409f990540c27e6494c309f99742483cf634cb20b718d548835f53d0d109f98253c876d4354830bb98b314827f6548410b7d89314c2fa60908209f984548c35f43d4943cf55054c827c65105209f19631503ce524c030cf590524427e6115232dd94441d035e5310a41db14721482ed62101109f98253d0a7e60d45329f583530873e54d44309f18152d0efa60885209f984525037651d0030cf992534873c54cc530f594d210867d62d51319f596310875e6194e419f997430436d52cc831b798e415067d63951319f597324427e6494f10dd945418c27e6514d20dd946218827e62951309f99441083755344010db98b540cb5d5348440eb951520c35d5314c42d7d4e5310b5d54cc0309f988530833f6095021ddd8a510c27d62947309f58a50cc7e85248110afd9542d033c6095020db94a420823d6414e209f194400c33e54946329fd8153887795014231d7d92539067f6054a41af99231c42de63d4440de98950086be6408510d754f5190a7e60946329f191538836e62d4f20b798f42ccb7551904309f99432906f76150921d394e520433c5450120bbd8d21c837451505409f9974350b3e5490821cf550548839c5310e409f597434867d6494032cfd52548835f5314940d7153318c6ed62d4430bd9845010abe6415021bed914010376534c5109f988540873e6415120cf951420867e6095031b758e421073e64d4d219fd815390af76154d209f59432d067f6254d10ddd9541c42de6390621b798f548867f6055231dd18251083766115221cf953310833c6454e10ee98342d035d534ca41d754d5090afb6050e40ddd85534827e63d4910d74c951cc3755114530bbd8940482f661d5332bb583324cabd64d4021b718d544827d61d4930d754c431027e6510720d798c5050b3d5414c209f59421d02dd6314242d754c530436e52d44309f994534427f6255132cf551310439c4390030b798c5050ade63d4810be58243cc3746254430d794d509073d5408420d794c30882766114143b798c521075c534c5409f58e548427e61153309f5885150ede6308420cf551420833d5410430e710f32102be64083109f98e51d0b3d5450b10db94a20042ee62d0520cb149425067c6454720bb98a434833e54cc631ddd95510c39e5494c109f994430435d5390020cf181540839f54cc930edd09414427e60d4d41db549210c2df6350731dd5
  | 35 => 0xa6588110cf55040042df6350310cf550418c73e5490f329f580538877551147329f996214439d4310f20db98854c873e62952329d98753083756115030d754f30c82bd6488740eb90e521035e5354242f954a51102f960cc5109f194300837532544409f5805250e7d6195120d758c548c377510c5209f986520c2be64cc540de583540876d5208410cf950200436d5290840b718d40102f66110841b758c20443766115032cf950430cb5e53d4642cf95150086ef64881209fd9642cc67d6395321cf553430827f6454e20af992514ca7d6494420cfd5340443e52114021db98152042dd63d40219f99432d036e5210b40fa4cb204827d6115320e798c4350abd64d4f21d7589539075e538c010af590528431c5350940cf953430873e54d0421dd5845050ede6390932dd981510c37451c85309f996414c73d54503309fd96200427f6354620cf55142086de63140429f184524427c6254c419f59440082ed6188120ed50441d03b742d0541bb58a41c835f5394e419f99421d027c6055321eb508428cb6e528c840cfd53424c35f5394e20dd94521042bf6454d109f9805150b6d5250810d754c534833d5454c20e7950430c27d63d50209f59743c87755150030cfd91544c67d6095321f9581210876d520c830cf553410833d5390c409f582548cabe64141319f58e548879e4350930cf990504cb6c6550920dbd4b208436d5244010d754d310427e6094742e754c43d0a7f6550a30f694e50087775494430c715143cc27d62550209f584544ca7e6414121be98032c827e6215120cf55054486be644c940bd584308437753c4010d714e4350b1d54d0c30d794932cc75d53d0f41f34c9314827d6494e20f948720c433d54cc010d7195434c37643944309f59631c82bd64085109758c505067d61953329f586539033d5454420d7cc5508c67d6194332db94b32cc73c43141419f586500425e65d0d32d754e42082dc6350330bd986435067f6454720ed951100437751946439fd9441882f56388510bb588530427d6314b109f58a50d0eed62cc521f558443cc6ec6050b209f18550ccb7661148109f984540cb5d6254c10db94942082f561d50209e98052042bd62d0c43bd5875290f5e530c410dd54f108435d53d0821af597419075e524c832d7d8d544caf564887109f195215039e544c030af99332d036f52485109f99432503ae52d0040cf54f401027d6094443e7152304c27d63940419758f548873e6295020d758153086be640c320af593329073e54cc810db98853c827f6054a31f310e520c2be63d09419f987525035d5314e21af990508ca7e65885409f98c5050b5c43d4931af992328c6ee6214c10bb58a430873f6395232db548211027e6315110b358e42c83da53480209718d544436e528ca10db181521033d544ca31db94120
  | 36 => 0x47429f197214c35e534c3109758c548833d54d0c21d754d310873d54d0421b758e42cc77864540219798f540cabe6414a109fd8d540c3f23148110fc88550086dd6390710af593325033f54d0431dbd4a324c3e63248421db151424827e6414532bd984304833d54884209f5845350a7c654ca40f6d81434c27e6014c21af19130c82756195132d798f54082df614c930e7550434c6f661d0310cf15341c42f561d0b419f19542443756590710cf95221087ea32482109fd8d528425e63148109f98053c86ed62141439f185544c2ef6448720db98b54cc67e6550c21cf55141083af5450b20db54832cc76e52d44409f98b544c7796394021bb98a535067f65904219f586548cb6d53c80209f1855210fad648cb20cf15142483cd32cc120cf59251cc2dd644cb309fd8d50c867e65d0d41d758f520435d5350820cf950420876f5454810dbd48324435c53cc920af98342d035d530c840afd954310f3d5490e21dd58d511027f6254e40be58021cc27c6548510cfd52434439d648c531decc650086dd6490c43db54a328427e65100109f99742487e463484219fd9742cc27e6590c10d754d438435e6154e42d794e510835d53cc010d7d8d524435c63551209f197434867e60947439bd95320cb7551104409f58a530435f52cc530f650f304c27e63944209f994324867d650cb10b758043cc76c528c9319f58e50082f66114440bd984548c33c62552329f584504ca7f650c820afd8941502dd6390b10db54b411033d54d0e10e794f401033e5410d31cfd9554082ed6290e21bb988408836f6255120ed58643506dd6490d309fd94420c2de6315210cf592520cb612154021cfd51314c33d5454021af58a435077651c8430cf553418436d51c8020cfd50438c2de6314520d794c500867c6548110d754c53082fa6008710dd8ca51082dd63d09329f588505073d54904109f58a53d027e64948309f99443083755190030de983538433e54102109fd95325073d5410820d798f54c873d42d4540cf951424425e6315021bb597218867f6510b31f5d0e510c36c5490920d7d4f315033e54d0a329b58a544c73d54cc430cf186540835c5390540d7588535027d6095032db54f208827f654c8419f18153d0af561909419f58b5050ebf6454930e710d418c3e92008110bd98440cc27f6254f10de94e500873d5410c31d7d4f32c86de6390841b7d8d548435d5308420ded425010f5e54cc530be181318435e544c4319f58b5150e5e63149109f194325067d61d5030dd18d511039c4350830d754c53c873c2155021af59030c42f661d0c4197997434c76e5288210bd987320c73d6494732ed592314435e52ccb30d7597308c2bd64d4232db94e320cb7460544309f99631c833d54151329fd8d511027e6590430b718d420c3756354420bd984510c2f
  | 37 => 0xd7989539079c644c0309f189509075e53d44409f196424c73f6550c439f99250ccb3e5350c439f58a544c27e6415020cf553318c76f53948109f58a540c27c6054632cf95043887cc524c931db5485210e7e6590d329f5964310ade6314a40d74c5500c76d5210810de980530433d54840109f1815310af661d0910bd984538827e62d4c109f188544833f63950219f592520c775510c420bd98432906bd6090f429f997404436c4394810db98b548cb6e524c010dd94d511033d5410821d7d4d32c82de6310220ed50740c437a41540219fd9643c867e65151219f595210c36d5210840cf950410c6be64d4c21bb588548c35d52cc030cfd8954042be64140319f595420c2dc63502109f596430c2ee6214e40dbd85521033d54506109f994428c35d5354440bd58754ccb6d5250440af59231c433f54cc130e710f410c2f96090d409fd94430ca7c6590d21dd58753c86f96090e40bd587428875c538c9109f59730043f25184010dd951510c36551480209f994420427c6590d20d754f410833e5450421db8c9500cb355454430fad89208427d6590b31e7990430c3764254430b7597318c67f65cca109798c540433d5410d219f99731503796015031db54a208433c54d0230cf952310c39c5490d30f3d4d32c827e65d0d21bb988520433c6454910db54b42d073d65d0240d794e320873e43943429f587544c27e6495130db54a211039e5390c40d754f43082bc6050c43bd5845310a7c6255231fa54a300c2bd648ca209f59250cc67f6590e10c714f435035d53904109b98a544c65e63d53219f987540c27f6590c10f598443cc75e6154c10af59251cc35e63951219d19541442dd61d0f32bb189318833e54c8020ed50441c8776514c440ddd89511027f6054f41bd984500cb5e538c420d794f40042dd6314021cf95242cc67c6354642db586521027d6510930b798c501067c62547409fd85508ca3d6414e10bd584430c6fa608c620d7d8553102f96008440dd544519033e5450c409f994434837561141329f196414833e54d4810bb58d214827e6395010d754d510823e64d4e21e79524310f9e6310f41cf550430caf56114232d798a530875d52cc4319f19531082dd63907319f59053c42dd63887309f195414c77651880209f597214c35e538c8409f98e544827d6494020af590528c2be6410940cf985540871c53d0540dc54620082dd63d5321d794c43c427f6155010e710f32902bd64cc540db94a310c27d61d4f20b758e310c6df6350a309758c524435d5310010db54b41043765254430bed95100435c43d4532af997435027d6510a319f99053c875c6154c10db55320882fa6010910dbd0d520427d6594c209f98e524433f5450b20afd85435035e53cca20e790f414c36f4354840af99231c827c6055232f3d89324c67c635
  | 38 => 0x50cc6dd63148419f98454083ac5450b20d794e300c35d53840109fd855090b6f6354840db94b32d075e5394241cf55242cc77661150309f994544cabf64cc941bd185428c6bf6454132f5145314c33d5490010db54821c42de63d5010cf152438c36c5490b209f988505075e53d0820e710d42ccb6e6215210f618d40102dd6308440f6d8d300c39c4350430d7d5343cc7d553884219f593530435e5394810d754d410827e60d4543db94b421067c6154d20d7585531027f6508640d7d925390a7e60d5010b758e41106f8604c5109798e52d027d6494432cf953420c27d63d41429f59521902fa60d0a20eb551520c27e61d4c109f587544ca7e65509109f596314827d62d45409f181510cb766115010be582420827c6054e42d714e405027f6154d10cfd52414c27c6454332dd545419027e6394021d758c548839f6350f40dd94540103655254440cf581548cb3d4254042cf585548ca3d64944319f1855390a7c6254630cf149425067d6494a30e798c435075e5310f21db94b420c2dd6308730cf59353c835d5388420af99321503ea5288210dd509510c2f561103109f58252d0e7f65906309f18553d037551084309f99732506dd62d0d31be181425027f65d0a10ddcca510c27d63d4b109f99732d067e61d4d42dd54621902dc6350b32d754d321033e54107108f59353487764154041cf950528c75e5454c20ed90d41c42ee62905209f582548c6f66110210eb50b404825e63d53109fd85521033f5494530d794d318436f6394810c714d41502ee62143439f986544cb5e530c010e790d414c2ed628c421d754c420827e6590f10b798e42cc76c5290941bb586324827e6590d30ee951200827d64d4e10db549410427e6095121cfd9154c867d6294640dbd4a528c775518c020b798f214c35d6154e429f98e52082de6308620cfd8654082bd6510e40cfd50404c35e53d0f409f585540427d6510b10cf551410867e6550c20dd98d51102ee62d0f20de98352042f66088710f3d8932cc2f66110b10b758c504867c6454e21cfd51410c67f6590c31db94921042dc614c9318f590504ca7f6510f219f18d54c42ef624c721d798c53c827c64543219f59632106f661d0f10cf15141c433d5415010d794c318875d4014d409f994534873e64150218f990514833f54145309f58b534433e5450e20d7181530873d5490821ddd95210873a5494021db54a21042bc6454d10cf551400435e5390c10ce55250086bf6050b419f995428427f6550c42bd58430442de6390b10cf55221086bd6494b309f58c520427e650c9109f586508ca7f6548640f9484218833e5414810be58341d027e6114910af18d42d075e6094c10dd151510c27e6494431af992324c67d6114d20edd91414433c62d51309fd97424436e6454830db19532482f46050510
  | 39 => 0x427e60153329f18951d0f7551d0020cf952200433f5490d20af99232102f56114032bb988400427d654c841e7d4d435027f6355210b7586434c27c6354b40ddd46515035f5394e219f59632c427e61d51309fd9432d02bf64545209f980530435d6254c40d714f43883ad52500409f596540c3793154021cf952510827d65d0010dbd9542c823e64d4f209f582528c6fa608c820bd58720442fa6090f309f98f5150a6c6254d109f18d50907b54150110b7d8d420c39d5390e409f994435076c5248510dd547410c36d5214931b798c50c876e5450842bb98a314835e53d0f41db94832042ed6190b20b718132cc36d4254042ddd0d510c27f64540219f18d508867d6510830de582544c36c6494810de58054cc35c6054c10af590504ca7d6115220d754d328427e6590831d794d20043f25150040b7586324ca7d6510410cf553510c2dd6310530bd98720c435d5310f10db15142c827d6094e42bd586544cbb75190541bdd8e21443796454021cf55142ccb7563944409fd8d544caf66110c319f195434cb5f54d0d32b798e434cb3e5414430be98021c827e60d5030d754c538827d6414e20b758c518837b6548020d758f54c43bb60509409f194410876f52949309f597410436c6154830fa8c920443d8438c030af592514c37551145409f59721cc2bf6350940bd98742d079c6395030db99721482fa6014443cf95341cc7775254440cf58d540827d6590c31db548410c3765190040bb588531036d524c841b758e324c33e4394341eb90d424827e6195130bb982424826c654c9209f993504cb6f5250941d354d52102bc63509419f994424cabe60d0740d710c504cb3d51d0040afd81425067d6015031af99232cc33d54150219f99632d07cc434cb20d7151530427f6590431f9191210867c65d0530b7d8d40c836e42540429fd94300837551146329f58c51482dd62cc730d754d30c435f6194c20cf99251ccade63d5310bbd9132c83776548710ddd85544c67d60d4931cf59050486ee6214c40ded4250c87765450710be18142902de6310a32bd98430083bb644c0309fd895110e7d65d0a30d754d400435e6054c109f58a544c67d6590832de980540cade6314242d754e410867f6454f209f58e540833f54d0120e750c438c73c5450b20af59030c8375518c620d754c41102f96008610cf952408427f6054d10d798c534867e6115031cf952320427f6550410db948510c27d6395310af9884350a7f6254031db9524210b3e5410f20ed10d51103db604c9309f597325033d54d42329fd9743087cd324c320db54e52102fa6010630e7d0d31502ed6288520db50e52042df654cb30d794f210426e62d5010db149425067d61d41439f992510cb7a5494021d794f43c82ed6294d41db58b54cc67e62153319f98a54cc67d6595032af59
  | 40 => 0x6588010cf550438cb5f62d4d40dd54421c833f5450d31cf188544c36e6154810b798e410c7764354420cf99353043ad4350842fcd82214427e65cc120dd10e51082de6314341be982310433d5444010cf586540833e5410b31be580215039f434cb40af59231c837853940219f597200427f6354841af592324c27f658c7409fd96210427f654ca41dd546210c2f96090540cf551518cb6d52cc430b75834350eef624c420be980521073f54953319f197424c73d54508109f98453c835f54cc230cfd82548c6ee65c85209f59543c42dd6308610bd98432442dd6315010af59252cc6f66108010f394e52103cf534c920af592320437562544309f59543887764294440de980548427d6094c42bd181214427e6214c219fd91508c6f561d5030e7153324c27f6510730d714d42502ec6250e42cf59643103cd62d0d329f583514cb6e5248440dd945300833e64151319fd9741cc37b53940219f597434833e548c420bd185325075f53d4540d758f548caf661d0a219f191508cb766115310de980538427c6155232cf95242c873e54d4632f558e41442be64d4c10db58a53482f960d4c21bb58830c435f4394243cf951310c2bd6490040dbd4d20082be648ca41cf992510c7ea5284010d7553430c27f60546429f191518cadc63501109f983544ca7e6114132bb58b434cafa600c7309f194414c3b561d0b41bd58643cc6de63104319f59250ccaf4614ca21b798f50087eb62481109fd91510c3b943d0140bbd85324835f6554c40cfd51404c27e650c720e7550430c3f25144010ee980431039d4310f429f58a500c63f6454d209798f52042f96010710d794f510837453944409f597311039e6410f3297d8d544827e6590d10bbd89504c67e65081108f59252cc67c6508540d7d95310c76c5248710bd591214435e534c420b758e42c827f65886409f98c504867e650c4409f59643887745254430db949310c2f561142439f185508ca7e650c520cfd4c43507e95288210dd54731103795494021e7551300c27c65cc810b758e41c825d6315021bd58643c42f56110a31ed553100435f534c621fc946401034f43548309f98c548427c6354a41cf182540433d6155030dbd4a425073c548c530f958d21086f960ccb309f58252906bf644c210db10e52102dd6190c439f997414871e5494c10d7547300c37a6014a10dd587540c27c65d0d109fd8553d035e6510d32cf55242042bf6550f40bb988404c2bd6494930e750e5210e7e6314b10be580219027e61d4810db94921842ee620c720eb149425033e4354440be5805210ff13148110cfd5143cc33e6395020cf951528c6bd6414830cf98d540827d6094d209fd94310427f6354840c718d540c23c6454e10af58443d0b5c539094097195434c33e6414131d795332cc75d5390010ed151414
  | 41 => 0x130bed8131842ec624c521cfd52404c35d5350810cf550528c75d53d4242b7d93324c2fb6548020bd58432cc67f6154043e750c5110ef46150931cf55042cc75d534c520cf584544c2f86548110dd984504cade6308530fa949300c27e6294241dd5445190b3e54cc0309f18d50d0a7d63d4a109f597319027e6315121b798c210436d5248610bb1894350abe648ca10fa48520842bd6090c40b799332cc6f5610cb10d754f311035d5344010dbd4e521037551c8420cf986540835d53d0f20bd58440c827c6354640ee951300c33d5415332bb9884310b7a52480209f189544c6de6390630f5d8d31c427a60150219f18554c82be6494530afd8542d03746494430af590508c6f66190c319f997318827d6295331f64cb304c39c43cc941d754e5190afa6090540cf982548c76f52948439f1895090f1e54cca32ed992310c76e52cc030d7d4e525035d53d4840e754c431035e5314a41cf18a540827e61d5020cfd52544cabd648c921be58241902dd638c8329f98f54082dc6350531be98041d035e5310c40d7591530827d6510c30cf94f42d02df604c0309f58a54443da5388020d794f300837751947409fd94428c67d6494431bd9845090fd65344010cf993530836f5294b43bd586328c67f6590c209f994321027e6395110b798c400427f6510b309fd95311027c6550c20db50e52102ed62cc320f910d21086766114c20af993510c3755254440d714c215027d61d41329f98252d0f5d63152329f99443c83b76150540dd94521083e652887109b588530435f54cc030cf153424c36d5288710dd50a511033d54d07319f987540c77a42540219b5885050e7c6054642f34c832c836e6214c21af990520c67d6494031cb54b401027e654cb10db148324431c548c1309f596329027d65d0e20f554f10042fa6088620b798e42c827f65887409f5865090a7c6454430be58231c435e5390c30db94b219033f5495232d794f320433e5450731de983530436e52c8630f9484210435e6394b40bd5845010a7c6154043d754e420427f6255031b7597430c33f6155232bb98321c827f65cc720f9484214c2de63101309f58e520826e6214c10d954b10042de60cc730cb952520c23e6494730f590d310c75c5450f30bd984404439c43ccb419f593514c2be60d0d40cf55021043f121c4110cf597419075c544cb31e794f419067d6550c20b758c40c42ee62142319f993514831e53d0a42cf593538873e5450a109f586548c33e65d0d409fd95318833d54d0a20be580540ca7f654c810cf953421075d5314f209f98b53c4375510c020e7d854310f3d5450320dc485500873f54d0921dd109510c2de6210f32cf550410c67d6095332db982521027f654c8329fd94210c2dd6308540be982314c36c524c930dd94d51083ba54540219f594310827d
  | 42 => 0xf99232903ea608cb20db54d520435e5348421ddd4e510827d61d5332dbd4a521067d6115332bb98a43cca7e6494232eb552520433e6414e20de54050d06fa6014c41af58b415033e5450b32be98031502df6350b32b798f521027e6095232cfd91548435c4354a30b798c424c27d654c4209f181534873d5390e40be986208433f54d09329f181540c67d6594c109f58e52d075e53cca219f98053083774394440f950d210867e658ca41d794c43d0aee62d0f429f19743c433e54d07219f59643c435f538c5409f9835250f5e5350c40cf952410c35d5314e41bb59132c836e6354840cf55242c82fa60906409f99732106de63d4420db948410433e6155231fa486500867f65086309fd9531c82f76350510af990510c3b75150740de540500c6dd6314840e798e415075e6314520d754f318427e658c420be980530877965cc230d7d5043ccb7554544309dd95210879e5410d32cf15140443eb604c920db94a510c39e5454c21dd8ca510c27e6414d10be982435033e54d0e10f554f419067e60145438fd954310e7d6194b30cf953418433e63550109f99721502dd628c130cf552310c3746094440bb58a318873d5450e309f592518cb5d5350e40f6cc7304c2de63d0930de991500875f530c520cf90f5150b3d5450731d794c430c67e6295231b798c314c32e4354840bd98432087b54250510d794e41082f96010a309f996420c33e5410030d7d4e53843755148020bdd9131443ad5490b20cfd52424c36e51c8720afd894210b776154d10cfd9154cc67e60d5031cfd95411073e54d0820cf550548c3b45150740bb58843c876e5290430d794d32c433d6195030d794c32c873d53d0240cf153410c73d60d5130cf55343043b95454021cf553410427f654c0309f590538433d5450e32dd151510827d6095131bd987540c3755150430d714c434435c53d05409f993538875e53484409f596410827e63946429fd8954c435c53d0d40d794c430876e524c810de085500867c6354a409fd8154ccb6f5294a30db986520427d6590f21dd50e510837b5094131f394d200833f54d0b319fd8d51d0a7e6510d42cfd9542d07655254430af990425067e6114d42b758f51d0b6e520c840b758c219027e658c620e750c434c6dc6050f30d794c400837a60d5021fc905204433c6395021cfd91540427d64944309bd89544433d6414e10dd987540c2ee62d44309f99732c435c534c110f54c431c877964940219f596318827f654c4209f98652d0e7f6550832ddd49510c3794254021db948400c2bd64d4632d754c210427e6295131dd18151083d561ccb31e714f425035c534c521af59643d0abe648c940dd586544867e61952209f58a5348375514c620f5d46314c73e54d0a31d794c200439c6250c43ee181435027d63d52109f18950cc67e62d5
  | 43 => 0x438833f6055232be582328433e544c420cf951418427f650cb10dd5445190edd60d0d329f982544c67f6354a40bed81424827d64d4d21bd59710842dd6314a41e7d51434c27d6590831d794e439073e54d4c10b758a434c3d4434c510bb988308433d5454a31ddcc9510833e5454c219e980540c76e5254440e7d814310e7e6415031b7d8d218c39f43cc740cf55230082756114c20d7085530865d6314121d79865390b7551906209f19442842ed620c320d758c528435f6294c10af590510ca7f65cc840cf9535108355514c030fc8c6204435e6394742cf553420c2dd6308510ddd47214c2bd64d4c209f992500caf96010b40be983218435f6454c20cfd52540c67f6454c10cf950430433d4354043c7152434c33f6215130fc482104437b4154021cf551410433f6455120cf151410c6bf6550b419b9885204376538c7109fd89548c27e62d5010ded0d50087da6010c30cf95130042fb6548210d715132cc3765108440dd10a511035e53d4242be980319027d6394421bed8b108433e5410b219fd9731d037561d4c20d7553434caf56284110f3d0d324827f6454c21eb95152042be648c531d758553083795014043de58352c433e62552319f98a51102ed6210f42e710f424cadd6390631cf552210433e540c421d754f430439d4310f30f90c9210875e530c840dd587548427e63942419f99432106be6415010dbd4a5250ef6610c2209f58b54c43765288421cf153408835c6254e429fd8d548875d53d0410d654e50086ed65d0a429f99352c42dd6394b419f58f514835e5350c21cf94f42d06f561cc910f54c530443b661d0b41d754d5190a7d6115032bd5845090a7e658c921d7d4e4350b6d62150309f99443c867f6510c219f595404435e53d4810d794d31902df6354121cf50951d035f53cc220bbd9321482df63505319fd95414873d5410810f394b32cc35d5310c41cfd50214c2dc6354520af59351cca7d6414132bb98a4350a7d6494321dd991511035c5388540cf99052c427e64145209f189540c73e6095030eb992324833e5050040cb551200833d540c4209fd9432d06bd61909429fd9542042f46154940af593530867f6454c20b758e428c6de630c931cf151314c2bf644c1109f994424433e5490842af590530836e6215030b798e41d02fa600cb309ed95100435e5394642d794c4310bb554544209f597418c27e6094c21cf952510c2dd63d4810cf950418873f54509309f597320875f5394c40dd584524427d61951219f595424cbea52440109fd9640042de63908429f594325035f5454c109f5865010a7d6394241cf186548c6ed638c9209f58a53c43776454430d714c425027f654c010d798f54ccaf56110931cf550508cb743294420bb588434827d6095120d754e42086fa6010520de8c6500877651d0440a
  | 44 => 0x36f52c8110ddd4651d0bb45150540ee952200825e63d50109f99353c83ae6290d42eb50940c83b8644c030cf953300837652887109fd97430436e52c4010e7d50438c25c6355220db94a400c27d650c020de505500867f6254c40af592320cbae54cca32cf54c43d0b7a2154021d7cc950cc73e5490441b7993308c2ec604cb20be58031cc2be648c730cf55031086f960c8720bb98b414867f6054910cf153304c2ed6215031bd984548833e6195021cf951400c27c6508530b798e41c87cd524c030db94d320cb6d520c410cf550408833e6415310fa485204427d6394910bd987438c67c6155220b798e428c73f54d0d30d754e32c875d5350410cf951428cb3d54144309f18453442fb604c510cf95140cc31e5494c20be98221042ed6210f32ddd49100427d6550c10cf15242443795014241bb588540435f4354830d754d321067e658cb409f18154886df644c730af58a40502ed6210230cf55153087742054420f594e51082ee608c9209f9845250f766115020eb508421073e6414c20cf592510c73f54d05309f596530875c530c910d754d50086be648c9109f59252086bd64140219f58a53106ef6150920dd98251102f66110a31bd586324c67d63151219f99431d03bb64500409fd94311036d5214a40cf988544c35d53884109f99421cc27e6590f21dd94921442de6510d329f992510437452885109fd95434835f524c530bb98b31487784254021cf990548835e53cc8309f195324833d5410d31bd185534827c6550b30d510d510c3d551cc030cfd095190bb96010c40e750c43906be640c210bdd85524c33e5450721f9547200827c6354041b758c40c833d6095232af58f41503756195132e7992324ca7d6590c109f58653882ed64c8720d794d400827d60151219f997414427f6055021af582439037761549109f181544cade6314342de597108427d6494b319f189534427c6510931bd587420c67c654c110eb508424cb5d53d0a42ded0a500873e5448410d794c520439d5490f30af99353c837464544309f98854c42bd6414c10cf152438835d5310810db54b510c27e63d4141bb98a300827e6508430d794c320867c6550c21b7582314c6f561d0c41e750c431027d6510d10dbd4a324c7796015310b798e410c35d5354840db98d520c3e76148520bd18542907ce53c8421cfd52540876e52500309f582518cb765150440ed50b415067f654c840db54831103766094420cf952428ca7f6550840d754d32c42ec62501209f194420cb6f6254b10e7551530875d53d0e219f987548cbe75148720db588534835f5494c20bb98a400827e6094e429fd8d54c873f6055021b798c208433d60552319f58753502be6408630a7191300c35c544c931d714d415036e524ca109f986528c3cd5394810afd89435033f64549109fd96
  | 45 => 0x390d21d794d321035e53d0a42bed81438c3793194021e750d404c35d538c020af18142502ee6214c41dd94441083ba60d0740dbd49324c36c5494830d794f31c86f561cc110bd1855050aed62d0f20cf952500873d52d00409f19153843555394440d7d0e500c27f6590830bdd9521c427e6214c10d798a5390af960d0d309f594310873e540c810fcd85204425d63d5310cf952520c35c6494c40dbd4a520c69f6150c439f59742842fa600c940ded81544827d6394b40bd58753d0b5c62d4d40dd54b100437541540419fd9542c42dd6010d31af592324ca7f6550c21cfd50438827d6314941cfd52214c2f960d0840fa4c920843cf524c931bd18542843d7614c7309f196325067d650c640cf55042c823d64d4f109f995424c76d52c86309f58e519033e5410020d714d308427e658c6409f98654ccb6c5148520cf153418873c6295010be58032c83753294420de151500867d6394341be986204435c6054c209f596420c2de61d0f319f980544cb795014042af99021d035f534c540bd98643c867e654c5209f185531039c63500409d9845050add6310a32cf952418c77554c4210db548320c67c6550921be98032842bd6414221cf551310c27d6294d21db149324c77a538c0309fd91534835d6395131de983540435d54cc2308f993530827d61d5330cf14f425033d54d0310eb95120082f5618c010f54c730c427c6454630cf553428c73f6454e109f597215033c5490530cf98654042fa6014632e79894310e7d6115020cfd50424c35e544c530ed592310c75c5310d20b798e414836e528ca31d718d540c3d96090f30d714d304827e6315321d794e32042fb604ca309f994424c67e65d05309f197315035f53d0940cd55251082f561882109f596320c33d54d0020d754e308827c650c520bb58841c836d528c010b758732cc3cf43cc932c755043cca7e6514910db948411033e54900309f997214c33c5494530b758f428c71d5410f31b798c420cb5e5354440af992311027e650c1209f987540cabd64086309f58454cc27e6394440afd91211027e6014d10e790f42cc37451c8540dd946319035d530c4209f595438433e6515130af98f401035e5494c109f994430873d61d5130d754f43086bd6490940be9824390375518c440f554d510835d53d04219f597310436e524c8409f988535075d6395132db94b31043775194642dd946211039e5410f31bd58642c86f6610c9419e580540cb3e5450c109f582548867e6494730cf150438433c5410130d754d420867e62d4d10cf181548c75f6354d109f59532843cc4354830dd185534835e53900209f584540c2ef624c620db952424827c6548630cf185540434d5348020d714c515027e6194243cf55341c82be648c821dd14a21c42be64d4a31f34c8328c67d63d5220cf150514c
  | 46 => 0x20d794d420827c6588540af1913084376514c0309fd95430439d4310e40af99232d076d52d0010af590508ca7d6590d20cf153414427f6590a309fd8954cc23d6494832be983438c2be6410d40af58743d035f43544309f59721d027d63d5121db949420c35e5350e209f597420ca7661148109fd81540427e6415032d794e420826e6215031bb988410871c54cc9309f996328431e5494c219fd8954442de63081109758f54c827d6550730e794c43d0b3e54d0520f5d45314c35e54cca329f58c54c82be64084309f994218c2ee6215230f594731cc2bd6090d42bd583218873e6414910ee551300c36e64948109fd8951d02ee62d01209f98b51502ec624c320ddd95100427e65d0620bb988304439d5410f31d754f42906b46150941be980428c27e6394041dd94d31c43cd32cc7208f993530436f6548020d7d0d52cc6ed62d5010d7994434c6ed6295131cf90d52102ed62d5030ab59232c836e5494830db58b53882f7614c931e750c438436d65c8621be98321442bf644c840d798c540827d60152329f98650d0f3e5490830cf94f419075e534c8219f58b53c43f131881109f994319035c54cc7309f583525067c6255230fc98221c42fa600ca409f99352842dd63905319f19153c87e532484219fd9642043e44148421d754d41087f060505109f992538867f6155132d758c548427e6194b40be582324435e5310440db94e52102dd63d5310dd982510c3774254440e710f42cc73e5490c21cf550300836d52d0040bed8b104433e53d04418f59353c833d5450720db4c9500cb9d5310d41cfd91540867f6255131bb98a430cb3d5494c20b7993300c33554c4010cfd53514c37862940219f98a5110f5c548c1309fd8151d0f755114432d7549310c73e6415030b758c50d0a7e65485409f191518839d4310d40bbd8d320cb6d5214940b798c529075d5388421cf982540433e64152309f195314427e62947409fd81534873d5490f109f582544cadf6348430cb552520c27f6454e21d794e20043ba5484010ed945401033e54d0e32bdd85328c67f650c8219fd96210c36e52908309f99731d027c6154e40cf945411077551486309f594400427f6590d10be59720883a65448421af59232107d7534c710dbd9532c836d62d5030af99353c875c5310e10cf953508c6dc644cb319f58a544cb755114630d718d54ccb3d6195232cf552430835d5314e10bb5885090e6e6215020cf952410827e6314542db951424835e5490f309f588530427f6510d209f99441086f561cca21bd185438c75d53108219fd9743886ee62d46439f98e50042bc6454121db54932842f561d0f10dd945319027f65d0e109f986531036e520cb31cf951438c2dd6390931cfd51414c2dd65d0f31bb58b31c83796095120ded42508caf56390510b758c501075f5
  | 47 => 0x14006002c0f50010012001000f00021a0006801300bc57f006400603a401201200000004010001404b032003e001401d0000009002402e005c000000000a000000000040000620007004c00b00740570d80007000c000000403a0008000000000101f00030020048007402000080180008014006c000001000302d00000020011001400300e800b04d000100bc003000003204c003c069001a0014418009010a076c00004640b80004005000c001042c00d00000ac000c00001580120af0004012402e00380d1004c00000b0000002003a005400a0018001028808f009000900040000080383040c001000403101ec00802b4000000416b148400000ec03f0034001078c0400064009000008600002704324008000000c0008455012000000101c9032c0500e5c045006400409600010044001000000002f40240000022001c0000004006004c002001000600141ae008800203dc00308480031ecc028001400002d00470128010000000100000010008075000006f0200047001c000000c002024c23504a0011004000b00740130ff000d00280080048008000000600bc007031c00d00c8000000001c0095e8b00000080008011008800f001c0070050042000400200d413a00001aa0000000000870a00080f502b4000004002d0014063000000f00000000100001001800307000c900b01840000021000408d03dc20200140000000000000c044000001800040420000000b958a210873e52508429f997314c33d54100309f59441c836f6254d21cf951420c27f6550531cf54c431035d3254432bb588400c3746094430cf58e54086be6408210dd58a510c3d96010c30fc88650086dd6210f31dd996414435d53d0020af992315033e53504419fd8d5190a7d6510730b758c528427e60d5231b758f40cc35e6314c209f992528c67d654c110d799153086dd6390b309f98654c827e62d51109f5885050ebd64d4f109f195211033c54501309fd8d51d035c5454c21de949204437b6454021bb98840c433d54d09109f983544c6f5644c5109f98b54c43744394430af592314c79c434c840bd987420c65d6315010db54a310c35f6354d20b7594438c27f6590030f994a510c35d534ca40dd549510c2f561ccb41d794c210833d54c8420dd584548c33d54cc0309f19153086df6350330bbd894390a7d6595031d718d524436e6214c209f19531d03355150040db986520c2be648c6109f98052042be640c110bdd8540c435e53104219f98a53d02ef6250d42bd984540836d5290a40af99041503755114420d7d8a539077b5094332cf151418873e5410a32db90d52102ef6254d10cf552500875e534c8319f99721cc2f56114143d7d4e534433d5494232d794f32906dd60d0f31e7d51324c36e52084309fd9632902f6610c010ebd9142c827d650c8
  | 48 => 0x6b000000000080020168002028801e00000010068004003000100580080000005000000300040000004009000000000b800300b8018000800d0198007001000b003c0030078000149c0000118000000400a000001700000620040001006400003840010000001408c0020000002000c00d00e00220010000004c000000c0850398008003c01c02c40130190037002000400100000010019026000200100090000000001401a000c1d4000087c03e400008e0000003401b001c046000892000ac04e020800400d401c000c0c7000c00c003c006003800000040060158093018000200000010018019000000001140970760003003c0b20000002005c027002c0010000003001002403a40020000050005802d00f001d002c00500040080000015004c001002c00a00004d7000000002c40012a74024000001400180040000008013c0000004008004402d0000004002800100b88730004000008c0c8087c042019c3aa0060010070000d00180d40154000004000232f01f30008008005c00d028400d0c5c46c00203f600c009080d800200140000060033009400200a4004005c00701bc00000000db0008004005802c0000012000c000000800400000030010014000802d054c01100281340b4803f0064007000c019010c0630010023002c0550068002018c00c00680040008009000000000ec016005007c00a006c001c000000001800a801100cc009000801600a400a178800d01440440310005000001a008401100900070000004000c0091f1804300040010008000002800101b00080004000000000c001c00e0000017049c000000400d004800203f403e00340050014001002823c0000055001001700380c602b408d014808a0008012005c001001000000cc00200000000058061000001200f8005001400f020002200000390060028000002400a000000000000b30023021c00000fc0000010000006404d006c038000c0b30348000028802300340240154002000c00200c408601100000030003013001c000c0280d7c0020000005000c0100004000000801317e0005000401c0020016000403100c000200080a700a8001001c00f031003b002c02b00640280074017004c005001c023016800709bc000144800000140130290001109000b000001300c000004f800400200c300d4003005807c00f00000008030002401b00142e300100b700001600024000000809e005c00f00840c60000027000005700080000148003000c00e0154000014804600000ba000000400d000a000046000040000000008001801400600220018035005800c03200031c3c011001800900b0000006403b058c00700140080008028010c01400740080234002000c1ab08740030038016002800002b0029021c007008400000bc019000000a002001c01c067d00
  | 49 => 0x38032000c027002800d0434087003c00001c802f000000c00540030168000001000600040100048032000400f087c02101a001300705700450095009c01d000c000014c00a08f0000001c00000c899f002800d000c000000c00f00000150060000000000a0000000006c02f04bc062009c38010a001001a00a401cc003018801500082d60174035000c0090068027002800404f800b01c00000060006000c0020740003000c00000000b401800050000000015800600301ed0000aa10050003005003000cc00200a00010270009001002300540001a3800a009c005007401700680130770081001c00500080620010132000002600000770004009002c0700168068000800600000010004005000d502023804a000400006ac00800240a200040020000050007806100442de002c4460004003000c06c000001f01780000050008000801d000802e002c026049c00411e4000000802d051400003c0035005400c003819a002400100a800100541410001d9b017c05b007803500d000023480b8004403c0004004002c05900000031ce00190000002003002c0058002085800b0000008003000300f00010054000027c004003c00f0000000000800002c400823780070004039001800f0068000001c000064c038003800302a002c001000b2d1800400b48d50d2843a0054016002400208b000001b80000e5001600000020000127004c062003400001f001611b003802f40090000056006000400000260dfc008021c000027800000000027d54008000000610d4003001400071e40230010051018400b0194052006402100f0023000405d000400101e4001004c0060014013000c080002c011000000800000010078001001000000040080050035050400c001400f02503d4007c003036000c000c00a001c07a594020b0008014033c00a0018012034401d001c162003008d021c0b26120000005400b041800900040000004004043002b011c066000001903d0002005402600680030050042039002801ec00e005400f000000d22dc00002000e7005c0330004142009400a009c0000054038007c00210000000030008000803600083b0002000600081b8001800000080140000007096c0b3002c02b00240200004000000401f00703ec00040080000001001c00401a8044043401c0064004151c00a00841cf00080120754000001c178007c0b100240a802c803e0128000005c0000108017000c0838310059000400c00680140000041012441b00640b9027c2c000ac0190014135004800201f8074004c02200ac0800000088071c030004932a0004000000001d0000087000005b0004003008800000009f0001c00902200160384105004400001dc02a04bc022032412f000000000440003a4408258c812b008c041010000b0018000007400000000
  | 50 => 0x21c0000064003002000800f8000000000000480010000001001801d000c0040000153000000b001c012000402d0000001006804d004c00801f80010090000000000600b8001012000708a00b400200490008007005c02100300500018003002801600581c30028014000003b00d403d0014000096c038000c0020018010000401a008c040009005e011c02f0064011032000002400040000006262400302c80000000018001c0b00000053019c00601e800d00c4001005002c000000f014c0440054274004c000020400007702a6000005000280040000d60018401600280130098000002c022000c00200000090e94024021c00b02a400b010800000100000028011015400604a407f0020000004c00000080140108006002006301b4000000001e0018003000801b001c1f50000b050038004000402203c4015026005e001c05500c404d00100140138054000802702c80260e14165000c026000c020002c00a000c02f002c1e8019c6260000006000c00004f02d2002001d009c01e0174028002800101ec01b0118020004800100000040000002008000000002d20058000000c0310008001000000500f8000004c025008401900080450028000000400300881fe00181d700f027b06b800c000808100080f203e000a00f421600048a60000026000007a0074009000000201a80010000051000000f0660041021c032005021d00c802b00ac002001c003004000300d001b0000033000800000300790968000000c01f06f8001000000000381be025c01e0024001002800600a801000e80090078002001400c005400000b80b40004070004400100ec09100541320010007005c00700040fa0000074004400601c8010001000001b0002015000e000806800a40090004005000065d00100140084000011805000f001d002c0dc0360004000c02101b000800c4011002c00d00104c400680400015c420000006001806212ac000000c00800640040014024000c00d00205fc062002a0000009000000c017c0040044001001c030000800001e803a0000008000400002f80010074af50008000000004500440d800040070000009019809e00000080030003002005c07800010000054004809a0180014024c02d01fc02d01e4020002c004008c001000c000002801d0008000007000000c80060000002006014101ac0180014008001400d01500120130000018000c146000907cc151002400d0078004107c05d00041d8000004100100210008009023400100e80062c74006000006900bc08f0038000039c042002c01801340090028003000c25d04641c400ac00a0070001001400000d80120040001000401a005412f000414a02e4001000000000001fb00240de004417c0028013006c0020038002001c014617c00b000002d000400501fc0240
  | 51 => 0x36c08b0070004000002b00240c5000400c00540070290055004846a00000130000003002c09d00ec0003f6816d0034000017c006000c001014c079001001506b8016001800001883e60114000010c00e011000401040400018000000806e0081a0800bc00206740110190005022c840010c0000038005011013d0040001026000000080950008004000003e00340f000200340008044003c008001402820a00000000001001000200a00210004019002401c0000000006800e00083eb00000000004030115801000f80020050c4900340140018000005801101dc00702a40010004000000095900280000bf4048000c02500a8000001c002102000203cc0100000001002c0b5000000000040050070000000018e04a904800880010008001005800902a804300c8003000c0060af40040018001004c0020044038002400100400ea002400311a4004001c03e001400100e4000008805c00b800000d000f000400f0018002000004e001c00100088aa001c026000c01001a401a1640017009001100240000004378054400700500040014007001400401d80010024008002c00d000001000a004900480030010003004000e00089e9005404a000000a00000160628010003401f00480160f0408803c8070000000400a8000001c00305d000000440130898034002400c003400c00648230008015002c01f005c000001cb870270000005022b000400000540050000082000800c058807d002405f082400b02bc00001980070004009034803300000a3137c00c001000a00480130040001001001f00540010000000000099100b8000006c000001000200500cb04f400300000410000004001800400940190214009000c000001001c016000202e0054002c019001800000e8049000000b00000240008091008c018000000b00d4000001c024001c0100020025009c00000400000000002000000c0040028010804a00dc13d010800700040a5000c67f000c0070018018081004000080100004000001800a0060004000000f0090afb011000d00040c4000005d001c0060084008002801803c000200d800e255000c00065d900140b3002c01000100010004059003800000ac01306cc0050034008008800000000470008003001400701cc04f011c40406f8031000000e006407e08e402e000007200ac000000000203c8025003000900002db00000eb00700270051f0119740d0000c000000001c005c00e0000000001c00000e8019000400b000001400580370c8401900e8000000800d000809200200eb008c06c0e8800100140050000000003402e02200000f2000523f80010020000000c05300000060008056001807401bc1950054000009c06f011000102481c1000400f0138001000000203c0016002402400c00ed00080a11e7008907a8c0a0008
  | 52 => 0x90494013001c05514c4125000032200b405c205c02c00d002d00f402e000800000280860038000005451e000000200640030008b85001005c00d000000180120058000000438200540010010001060000a00d000300d8000002851d001400000bc0090000004000c00000c40010000002000410905c000800000650060007134c06813a404800d400b00140000328002001c05902900fd056013c0044009000403601200030040053002c000007c00a0180000000000100580971c7404300100000004561002c00003b800d000c00e00fc012003000300000070044209011c00c00e8039000c02802d00f107580130024000001001b000000104380c50000007004402c006800a011000001dc0120020004008c00c00e0069075431f00fc002017c00d0000004016400000e00012a34005000800400240030024020002004a2250193028000e00180ad01e400418b000000100320000007007402f0000000000000a00c00070258001097c05c0034000013c004000c0b700f8006000800d006001b010c02d05c40004d54006000002002ec097011001300081da0014349004800500ac0720134000000400b0140000006c08b01680e40298000000000b00000170e280170004000001c005032401c017009f001000b000000205b0000000c22c00e401100100010008000001c00201d000000041a90124015000801a000003b0a0c00305a802c00640020074052020400d000800300140070174000000c5700058001007000900c000600f00b056a40590154248015801300b8000000005600f0005010000102a8092005c00300200090dec00100ac0af007c01d00ac044032c000000000a001000a00040d0003000100180b000d000500c8001006801e01bc02a01940000020006002c01d0020007001c00c0100000001000006400000000003000800700a8006000001a0590002000c046000000001280530188007002c00100840010014017000004b00001aa001c001001400d6eac007000c0010068016016421f000c00103d0003000000100041810024000000000a000001d000c008282801700100b20004002001001a03140060064004002c0000038000003c02704bc01f00d8011016c04c0124009003802000006c20014001000000c000004400000120d540000048001000403300040190000046000000f00000110038002000000013a8005009402a000400103d000f006001900a0197004c01f0168005000406300102070041022007001a0300000004c02d006c01a006800300b8005002002a000c000008c00000b8000000452c0014007001400901883320048000001c028000018100000280094037101000400140000004000001c00a006800000e8013000002401b41820028090029400100440200080001002c3c6026802f0004001
  | 53 => 0x190001002014f29600090004002110005a00141000098003001c004052c000000803f00280060174021026000a00087bf0004001001814e006000003080010048001008800100380010038033003c00e0008184015c0ce0000020002c006000400a000400000440020b4400001e80012ad4002007800a0014000006002a003c0000094043000000d0038000000000000300e6000800603d800804bc00c005803500600000018013000c12b029802700180480034049004401a0bc800f07bc00000000670000011000038900183d304440000014070011401b000800e00300020000047000000000000000584001000006f000000200040000044006002400200e40090298002005c023000c01100900020048001001002c009400f148c00e004c000049c0021688024038800a00100001340000027800a0be0008049800c000
  | _ => 0
def q2K4 : Nat → Nat
  | 0 => 0x1861d6510f32506b2392a228a614b5d05394810cacc7308a81065663944400838731886a9081331c96110d32a9ce4304a720e5a63580540872ca9cc010881c955252c4010a3ce7aa6859061e6454e31c4237390c0aa663179cf659082087cec2a2810851e75d0f315022ebacc72082147dc56315130c3cca29e82a061d64192530868f3a4c4a9841175ce6590420a3ce9a9e659047b755822104237bb2a429461475d06114d40ce0ca90a408863554d85438c69aba0c52886187992538c431a3ae730aa91951d741825390b0eb24a7190214d9d05254430a74e9a84a010d3671d51414c3d0aa24328043875954310c308ece2302a89943e74195320428eb9ca821a651bdd952144308bae732c42205667118152102aab9ec8a8841d858d2154021c3cc9318a610d1d7398a548c62f3b2a6a00210f9d26294d10c3ca8b1ea21043e74d9521cc2373b6a6a90218b1516210d208bae630aa42069a6358043103a329aa588021535cb5410f319ccec29a4210c7571195428c30eaa6c098061c3551320c821c6ac8a8c621070f53149425025aba4c399683659cf5450710e2ca8a9aa21045e7614d31c421fbb2a919463175ce6510010c6ac9308a610c7775584400c2d8ba46310221a510f614c941c9ac7310a50863a54583530872ca9cc021081871526390910e8887292a21845d75d8d420c29ab88a921c41175d953080108bae7314a98847571196430828e3a2a629a41591c5635481087aed2a4842151e73985540429aba0c5288419358e62150208bae6302a890e555398430042a7390c0a98431b9db535484087ae8300a68873254546200822fb9ac12a04317dda5390410caca6b0ea42046e721944004237390ca18021d154e5294440e2aa928a601854d73d89520428eba0a621c2147dd54310c109ccec28a4390571700c9510c37032a42902218e9915014021a6ae2310a89865b6594d200821ebb2a9190410f5d3658c820c3aa8b18a81062d64948210c28e39aa9a12218b991520c0108eeeab0880105e170151210868eba4c3298418d591518c620a3ce8082a60851e74d8d53c822fb9ac9a9421335cf6448520a74e9a9ca010e9b6418d401032d31cc02a04387951631442087ae9328640845e76151530432b31aa3208418d951610c010c3ec831aa90847b70595434871caa2c02a0651bdda5210010a3eeaa188690c5e73d94400432b31ac22a663c99515148020c5aa9310801051e749855304338b0ac0292219358d5290410bc4e1aa24210e1d6494f520424f386caa18879c9856014b108ece3b2e859843e74d96310831b322a2108814d5d64394440b8ce63024210c6e72996410c2adb9ac928043171cd6550110c6ecaaa2200853a7408550086b539082a804347dd95310f42c9ca731060086656118652103b13b242a80431b9c8650c540
  | 1 => 0x410870f322a629821599c85494430a72e0310a89865963980520428eba4c2a9821d454d51900408f0eab04848845e7654d401031ab24c3a98218755263084208bcea3266498e3954580210c21ebb6a821c418b551620c0208eeeca88a39068c63549401031b322a228861a650d6014443aace2304a6204e57690d210872d29cc0108418b55162102208dae432a83187165454f1004326a9cc5a888196596538401087ae9b2e639053674d8d5108237390ca21843595cb5194430a3ee6b02a810d6675484214c364b1a4010221b84856008420e4aa8a92200870d5454f21087b1a1242a8043c35534354830c6ca8b0e8610c6e72194434438b39886a88818b191524c0108baec2a664985727018a5110392ba0a290a411b5d66210030c3cc8b18a2906a964480208428eba886a08616c5c35450710ccac530ea99946e7218153d072731ac42a421875954310c21bc2e4302828861d54580430c31caa2c0298431e5c06510c218dae4302a898f1771550434c70f2a2c6108214e5c054d04318bce7b28422043d76952310862eb9ccba0e414d9d06054420c6aa930c8618d7275182214430fba6ca98061471cd5450520ccac4b08a91845d769524310f8621aa4988814b9d3625481087ae9b2843986e121580214c32ab1ac2282850fdd9548c430cc8c5b0aa88847676149214434ab88c0a1887699d232484218ece232a860863954582410430eaa4c7a8841471d54310d10a3ae7312a80845f7558c400430eb18c6aa0419698d601503187eeab246210dc673991210870eb22a7a88418755263148108daed290801852d74149208430eb22c7a9021999895114440c3aca21a65a0c3d74194214c22fbb2a629e81785c46050920ac8ea908429858e73d9142c831aaa0c2a1463785c632481108dce532e8218569759491004346a1ac428887569c36354c21c9ae7314a898f4573149214422eb98c0a96838d5926114e20c5ac4314a918c767119442042a6b90c0a98215c9c46354021a9ce5aa4a60851e7398a54083172a2c4200414d5d35194420a38eaa18869064e639485110393b2ca8908438dd506154930c9cc8a96601846f76548528c69b38ea92a665875944350b31938e8b2e611875253546200822eb9cc5a8a81395ca6190c2187ae9b2c639061e6510f428c2abbaa8698863a5191514c030a6ae22a2841956672181511021eba4ca18021595c86054430ec08290aa010e5a6358052c4332a92c229461d194d5148020938eca1aa021c5e731855010b82aa2a6908431d5c46054c42e4ca8a92a218665625445110ea6b98a5992219358e5290430c9cc7290422066562544519028e3a2a7994411b5da5490842ab4e7aa4a010d2e74d4d5204317322c42a021c354d4210821c3ca8b1c8318e2d64588504c62f39ecb212219398e5290810cccc530ea8
  | 2 => 0x42902211d9c46510d20c3ac8a98a70864e6354a420c637394cba18214b9d061548108daed294401045c7558c21502d23a2c090843565cf5094021aaae62a2a21064c5358b314868fbaac4a1887875506350731c9ac7316a990c3d7610e50d0a8fb9acba04819594d61100108bae7308a88843f76550540c22f39cc9a8243c55904354430e8aa690ea010e6952980211030eaa2c021e659554e6190010a5ae8304a40876152945100430eb18a7a12819694d60084109d2e4302830851e74d4e53c865ab8cc9190838b593528c941b1ae529886a15357408151082373b0a8a12419554e61100108dae432a622062e64948211023abacc3a18431d5d6610c0208bce632c85086555398420042c6b94a821a63391c96110d21a6ae9a9e200861d5458c4004334b12a028463539c86194e41c3ee7b2a802065553584300830f324a719641d898d215402187eecaa0a11955571d905350386a1887290814e9d06354021aaae7212a21861f6418d54482a7396a6992819398d5208430c6aa930c40085367590d41c430eb24a6280439558e5108430d1ae43028621f0d5354b40102a6b9880a908187991538cb218baeca9c8410c3e74185508cab938086a88810f9d6644c940c3ac929e6520e1e6458c5404237bb2a429661ca5515284010a3eeaa188618c8d721814310f2731ca420021785c4604c920ab2e6314a010e1d5498e42c823abb4a220041179cc6055121c38cb21a849854d72d8d530430eaa2c6204210f5d36588730e2887a12a2186546510d314428eba6c229a81d854b61440108baeb31c8520e1e5498e420821ebb4a821a430f5d954084308eaeb30c8610e4d53988509068eba4c3298210f5d261d4132a5ae9a9e401056a72192500869b388c12a0618b553624c420a3ce9a9ca710d1e73d9154042aab98a398a41255c46050c438bce6328840862d6498b53082a7396c829a81595c46054840acce5a8ca3a1d1e73181540823cb80ca212638dd936154d20a9aeba1aa4185e3714c9208430f322c629621745c3514c730a5ae4302a80851d7498a530870f320a790a818714c6050540c3acaaa6651961d6410c504c61ebb4a919463475d54310f20a6ce9a8ca39955473589510c316aa2c521843d454d2044010aaae7aa620084b675986435070eaa4c6100210f5d061149108deeab10600846d72d9731d028e3b2a6a00819c54560cc4308bae7316a0a0c3e74195210c31cb24c0298430fdd5648c4208eae3328861055571188535028eb9ca821e21995896114e209acec29a638845d73d96428432bb1aa2a00614b5d061948109cae430282884d57318121c432729ac4200418d5935194532caca7308a2206c93258032c828e3a2a698c21475ce5410c20a3ae5aa0871866552586300423ab88caa18411d5c66590830b2ee2a9886a0ea562504
  | 3 => 0xd66348421a6ce9a8ca21046d72181548c72aa9ac229c819354e62d0f20c3cc9298a010d597390550086a6b90a9988639554d618c821c58c4a12a3a0659539805308726b1ac428283179d7644c930c3cca21e652054d7214c43842d2ba46490843d85495190040a6ae8292a218655611865390af0b8ea4904219598d61d50208bce7b2c858851e7494932cc29b38ec62a261871cf6550040a6ae22a0871061d6410f514cb2b31ac22a42117dd95314440a9ae6302a4207155454d210872ca9cc028c858b5526210030a6ce9194a21853471589548c6b2b96a9288611d9d8534c71087ce9328600852d74185520c386a1886a9061871cd6414132caaa6b08611053674d46510c28f3aa8621c41179ce6588440c5ca9310a4185e375486500861fbb4a9190611b9c86510530c3aa931ea40863564544211023b388ca21841aa591608cb20c6cc8b08a09965663544210830e2a2c7a12658755163148108f6eca80a1994d573d9221c421ebb4a818021475d25310f21c98c6a92841843e74185500cba2a9aa4a88814d5d35254430a72e810aa010f4a53c8550086a6392a699221c310d525043087ae8302a690e3564544510838729aa4a0081175da5308440b4ae931a4210e1f7458c5050aab388c0a9c831b9c865d0e10c3cc8aa6601843e7418d500863b3b0a6a8841ca5c04354840caceb30e8698e6562984540428e39aa9a0c21559c66054e41c58c9292601843d76952320822e39acb10a8117dcd6494221cd2c5306a60862d6494a3290338b0aa028485c5151414c431cacc6b08a71045d7694e320ca973b0a4a1283355ce61d011087eecaa0a998e1d751814310e1fbb2a820e210f5d6648ca31a76e8b1ca010d5873592500863d380ca21821599c46054830cccc4b0ea81062d5458a3008236b90c0aa663475cc5410e20d3287300a421e2d54988310868f39ea8a1643479ce6295010c3ac929c620846e75d8f214830eaa4c720843699d23148421a74e030ca918d587050d5010f86aa2a790041c59c454cc530c68c9b0aa48845f73593514823aba8c2990211b1c9654c640a3eeaa18862155a73186500862f398cb216211d5c4645403295ae8302429045f7654c509072ab1ac22a461559c46094c20c74a9300a31943e74997310822ebb6a821c61995952108640a38e8a98a71061d6415131cc22e39ac928643c955251c8020838ecaa2601845d739942004316aa4c521e419658e60d5021bc6e498c408845f7654c535031aaa2c2200610f9d06014d10cccc4b08a790e1d7518d4010338a8ac0288878e552600841087aecaa462105c9739092044393aa24210a61599c45354840acae22a4a41846d72d9741cc38729886a908187d506350220d2887b0a8498ccd7398b404821f3a0ca212218714d62d0d40ec2a4a8a60186666254440082f1ba2
  | 4 => 0x5ac8a90a418e356458452442a73aec499263479d26254c40a3aea21a841851d73182548cb2ab1aa320881475d0534c21087ce832c648866662984540830e39ac829c418715163d0530cd4c4b00a818ce471588434868eb9cc82a243c5d91514c0308f2ed2a4802061c73590504c66ab88c0a188793d8c625511087ae9b2e658851d731514088236b94ca188811ddd951100208dae5b2e868861f7654f401032aa9ac2184211d9c6650c840c98c6a92421871443544400c296392a9a1221c59525354420aaae7a96200846c7259540442b33aec490a21539ca544cb30ac8e4a8a422045c7694d401031caa2c1a98430f5d06054e2199ae5b2662986576554d100424eba0c09926117dd95314c42c3aa9318421871a5494d500861fbb2a8280439954a610c010c98c4992a39861c5498f414c3b138aa4880214d5c45450220ae2e2212a010e3a54580210c2cb3a6c698a21471d15314e10a5ce830ca41846e721815310716aa2c4200210fdd95410f30c3eecaa6601864e6394b5110236b94ca20021879d854cc530ae4e3a1aa010d727118e50086c7b92a621a85335cf64c872087aeb324621047a70194438868fbaac0a1887479ce6255020e8aa8a9a4210d3575951100421f3a6cb19221535cb5394c408bae63288210c5e7398a548422f398cb212211d1c5654ca40aaae3aa2601861e6454f510829ab88c52a4650fdd95415330878e8b02a6085a870509404828fbaa8621843471d15350c21caac728c820845d7654c211031aaa2c3a90618795263100208bae7b2c8210d4e73185520422e3b2a699221591c552484408dae532a860843d74d94218c22f3b0a698c439c54560d0440c5aa8b10810849d7690c404c2b5390c7280439614e600c540ca8c6a8a801846e721815190f0f322c6282432b5d363c87208d8eab10869052e7294d42d031caa4c0190414b5c85490e3087ce932840085e1734852044370b0a4010421395c46050b20f82a690aa010f0e54d0d520c2973a020a90218b5926214a10e1887a9264a0d707158d50086b8b8084a8881359d8514c730e52a8a94601864e6398850506ad380c329c830f1d165c8530ccca4b08600865563944210821f3a0c4a88619354e6214810c9e86b10a098c5e7614d4348637390c0a8887595ca51084308f4e032a6420ee121580211038ab88a7a0a818b9915208430c3ca931c821843d76952310c346b208699641875526390430caac7288422061e5458f428c61eba4c329c410fdda5408430c9ca6b10611043d7690c5050b1b2a2c2200615c9c2325442087eecaa4641859673d91414421f3b4a8a1c41171d95350020a6ce8312a22043d7498653c8332b12a2180410f9d2658c420caac728c831851e7590d424c31d322c0292219598d6114a1087ee8b1ea29063664984538822ebb08728663595
  | 5 => 0x843d741953284386aa2a5980610f9d6648c530a9ae6296410851f72550430c21fbb4a9188618d951610c0208eeeca88a2904cd721814310eab388c129c85871526390530e32a8a9a401062d6494821103b1b8a42a80430f5d0605483193ce9b1a421861d6510c400c237bb2a4294219398d52908408deed29060085c673905210862eb9ecba1221c314f6250940ec26290aa010c3e74d94218c3932a2a588021d154d51c8020c38cbb22869866562546300832731ac52a243175cc60550218deeca90a5a1d4e72181539070f2a4c629843d154e52c4010a3eeaa18879056571d51200832aa98c2994431d1d56110d10c6c86b08a0a155a7390a500863abacc220061471d9544c030a6ce9a9ca21055973151500861fbb2a82a0418b9926214c2087eecaa0a918ee121580218832ab1aa3200619994a61144309cceda9a4210d1c73552408432729cc42002117dd95314d20f0ca8a9a4210c3d765523108739b2aa2a00818759253d442099ae6302859073254545401023b3b6a4a8881c89512154021e2ec6a8a802045d7399421103b1a9a42a80439358e5208410ca886b08a09952e74182520432ab1ac3aa041c550c43544208bce63288210e3954980518ca96b94a821463d094d2154021c38c8a9a422063554d85420431b322a2288413c5c4604ca208eae232c87105d17318520442aa3aa6498e210f9d0650c91087ae9b2c648845d739865448272b88c0992414b5c86055231c3ac9298400843d74196320431d2a4c029463d89cd2154021c68a8b08809861c54d85324c2aab8ea9a1e65b848560087408bce632c840866762545310828f3aec6a1a810fdda548c420c9ca6b10a120c5f7654c210832aa9cc22988187dd95310c40c6acb324638861e64d4e325030e2a4c621261595c853544408f4e03288790d1d73952434872cb1ac029221cc551514c030caca6b08a42058e721814310e1ebb2a9190219398e621501087eed2a0420853671d51410c657ba2c71024133dcd6488120ac8e4b1aa21047676151414423b38ccb990818d9915108420e4ecaaa24210c5f7654c535070eb2a86218215a9c06194830c5ca9310600849d721814310ea7baa86990658d5526115020acae2a90420865663984548829d3a0c728043599c85394440c3ac8a9c6520e656298453886a7398c329081175da5314021a38e0aa0869961c5498f404c3a3292a298061179ce6508440acae3a9aa42063764945300c22ebacc620041595c36548421a6ce2302a919477715954244334b14c02a0631e9c0650c941e54a990aa010de17014d2108637bb2a4292611e9c26550c21e8ca7294a22073141105500872ab1cc22a0419cd95514c0309d4ec292410843f7655042cc63ab88ca990811b5ca6590430caac7308a80861e6590e404c335292c0190618e551600c410c
  | 6 => 0x14c24fbb2a621a85175cc6510910c3ccba9e86a045e73d964108332a94c3200211bdd952100309e2e2302849051e7550c434428f3a4a599663c35515354810c38a9b0a869853674d49510c21f3a6cb188218b9925214430caecaa9a4210da5748c521086a6b90c129c835c9c03254420a3ae6302a80861e7614d425024eba0c098a610f1d1654c1108bae7b2e858864d63548200422eb9ecb10e81475cc62d513087aec21ca1a0e65529844004332a94c21002147dd95410c30a9ce5a9ca60852d7590d52103172a4c4200619a9496010840e8aa6a92200864d6354a420423d380cb19021d254d2154021c3cc929c641955671d92530868eb9cc52a0419394d620c010ccac530ea81861d5498c530862eb9ccaa10210f9d365cc910c9ac7a90429845d7694c511021f3a0c0a9063555cc605442087eeab24641045f7654c53842733b4869084347dc95410d32cacc7308a81845d73d96410428eba6c6a9843479d36354f21a3ae829e871043e7498653c8338b0ac02a0659358e52904408baed298420863654984508cae4b8086992419998a6115230ba0e098a608843f765503008317b2aa890041875925314810c6ca8b088410d6575484210c32d31cc1aa04387190635491087ce9b28421864e6358854ccaacb86a9298434d9c462151308bae732e858856a7010d520c29cba0c5280430f1d16094c21a3ee6b04a810d2e72d52540430fb2a8621861d89d12154021ec24210aa010c7b765405090eb938c84a8043535cc5494810c6cc930ea61076231485500871d322c028a41179cf6510020c6ac8a88601045e76d4d515021fbb4a81804187191534c440a3ee4a98862063664584540cb862a6c4992611ddd95114730e2887992a22066962540500c61ebacc918821a590d6110130c6cc8b0ca690d6472545210c326a9ac429c211b5da5210010a38e6aa6870862f64d89534432b31cc3aa04117dd85308540a3ce9314a6086e362482104421eba4cb98e418d591518c630c3ac631aa810d647254521902a6b96a821861871d953500408b8ecaa2601855571d51530829cba6a1280434b5d36354810bc2e1a9a4210e1e6454e32c829b3a465288818b5516214c10c6ac2308a89861e6454e320822fbaac0218619694e60084408bce6302a321655535845090aa739ea5296832d5c26190d418bce7316a2a055970153310c6ccb86a6a1e818b59262d4c10dc242b0042087615248110042aab88c0a9841355cc6050510a6ce9194a21043c74595304831b2a2c22046195991514c030c38c9a9a611051e7394741d021fbb2a821a630f9d26194c20c3aa831a841861e5498f500869aba4652886193d8d5250010c3cc8a98400862f54d89514c28f3a6c6a98411b9cb65d0730acae5aa6200852e7414d520430eaa4c7210211d9c46055232ec0a490c408
  | 7 => 0x42026187552631001087ee8b2c429846e721953110256ba4c4192410f9d6648c930c3cc9298420843f76550548830f2a4c7208218718f6255030c72a9300641845e73194215029a3a2c6a8881c51d15394440a6ae8304a21045d73194428423ab8ecb21a43475cf611513087eed2a46210e1c63181540c25b38ec999683c310d5250830c70a9300829866652984400c2a6392c2a9c858e1516008530c3ac8322a60870e5354b4010326a9ec4a1c859358d5290430a5ce4302a81849e7615143cc34ca1ac021c212b5d0604cb20c58cb21a849045c73592508870f320a7192811edd9501423287ced2a2601851e739855408326b1ca5210619354e620c0208beeca98659061d6458c5284338a8cc0108618dd526110130ccac4312a21855970153320cb0f322a71884187d91534c0208eaed288801851e74d8d530861ebb4a920883879516390a31a3ee6b04a91953970184544c346a1cc4288879554e6188010c3ca9318421862d54d894108296b90c12a0211ddd95114530e1aa929e40106656218a510c2b2392a290c619998a510c02087ce8328601062d6414a324c6a739ec9290218d992518c420e5284212a010e1d6494c308830e326a898061c85512154021caac6a88801856672d465190f34a92c1a1081d254d52840108bce6302a3a149f7650c5210f17324a5190211d5c46055032a5ae8182a41865563d44214c22eb98c8a8043745ce4188110c58c8a92422043d7695053086cb388c0a188799d952108430b4ce83024210e4d6354a42843a221aa4a88611b9c865d0c208f6eca80a198e4d63988540861fbb2a82a26371dcd6048421c3ca8b18421043d741953204316b22c4298210f9d0650c520c5aa9310a21861d5418d42ccba929a42a8043879cd6590c40c9ac6a90410863764945300831b2a2c3a9061d89092154021c3aa931c8310e1e5458e428ca3abb6a788021175da5308420c6ea8b08819876341485500870f324a718e21471cd6155030e2cc821aa2185397414e50086373b6a8a90218b90d6214141caac7308a910751538855008637bb2a410e21355cf6448510d18c9292601845e76d51530422f39cca200410f5d36548530bc2e518a408869864d8d300c23d384cb218431ddd95114632e8aa728a401045f7694c2104316b22a4108611bdd95214941c9ec729280185977150e5110f0eaa0c6908619559553d0641c3ac8b18a5885b1748c7104430f326a718a811b5c8645403187cec2a2879865553d8532906aa3aa62982218e5965484010caca6b08601061e76152304c23ab88cba18410f5d664084208bceb31c84a047a7099443086ad398a8a80432d5d261ccb10938ed29a802061c64d4d30843a4b8086a90611e9d85354021c9ca7316a22065563984548c70eb1c8628285c554e4354440c3ac9318a70861c5498e2
  | 8 => 0x8524cb30caac6a88a31043e75193325069ab8086a888187d954310e108dcec2a2859056471548525021eba4cb908614b5ca5490d31caac730ea910e4d5358853903b038242a80431b5c86510f10ae4e2192a010e2f6494930043b0ba242a8043535c34354830a6ae22a6811065653584308431aaa4c228465179ce61950208bee6b02a80843f7655042c868eb9cc52a0438b10d6214141c3aca21e8598d3674d8d511030eb2ca9a18610f5d3658c410a3ae9312a610c3e741943004317324c5a9821179ce6590810c6ecb28a802066765549100428ebaa86218434d9c76395021f0aa8a9a4210e695298241042ab38ea8a984195d8f6155120e4c86a92a22049e73987425071ab2ac918e219318d5250010e1887a928498c3d74d8d510830f2a4c721643171cd6548110ec4c890aa010d2d72151408c32ab1aa320c410f9d0658cb108bae7b2880104b471588435064e3b2a6a00814b9d64350920c5ac9310a61052c72585540830e29ec4a1a818759653d0641e4aa8908421047571194438821eba0c4a84638d98d51d0040c3cc929ea2105a67414d21086a6b96c829a810f9da5450520c3cc9298a40845f7654c530870fb2e86a00619598d61d503087cebb1a84a043f76952310428f39ea8a0c43725c3534cb2087aebb2242204d57398742442373b0a699641b44c5600c710a6eeaa1a8220c6e7219531902acb98c8a8043599c7549483087ce830aa5184cd7218131cc2373b6a8a90619ad965250040ac8e2b22a40861c5458c414c326a9ac4288819318d5250430bc6e4a0c40887195494d500861f3b0a8a1641475cc54d0220a6ae9194a22051d73950434861eba4cb990214d5c45490e30acae229ca42061d6454e3208296b90a821c619c9856014c21c38a831a811076176485500871ab22a2108418d9516110010cb6cb29a20084d571d9332cc29b3a0c0a88618b5526290020ce4a2b00421863954980528c69aba46528841c35525394810a70e8b1ca010c6d72996311028f3a0c0a98210fdd163d4910acce5a9aa22061c5458f42cc33828ac010a81175cf64547208baeb318420851e74d4d3248733312c3aa643745cc6188110c3ccbaa4869851e73989540c2b3388c129061cc9512154021c74a8b00420865a63580514822eb98c4a8483275c76550c43a3ae6310a89868e4358840cc32b29ac321c83d854921440108dee4b2a608853571153420cac7b9286a90875a9c06154830e2886a8e821871443545418c332b10a220a41179cc65506208eae3b2e859843d76950518ca96b90c12a4638b191524c440cb2a7300420849e74991300c23b38ecba1a414e5c354950218ece332a8610655639875408236bb2a4180219998a6114143c3ecbb1a8020554754c931442973a060a90619594d61080108bcec2a2869853a70d0d5090f162a4c
  | 9 => 0x8a8302649862c54189514c28eb98c12a021555c46054c40ad6ea90ca010d4e73d4a521028fba2cb984615a5c04354840a3ae92988710c6f72595434429aba0c4a8861175ce6215120a9ae7b22a40854e73101521032a322a398061475ce5410f20cb6a6b0042a07474354a510c23abb4a218041539c86094c40c3aec2a2649870c43549428c25ab88c0a1281875944350430caec6a8a802061f54580438c256b90c0a0a81595c45454830caaa630a8520e4c7258c5244316b24a5190210f9d0605463287ae832a431851f71550434ca36b90c0a8e870f1d163943218dce430aa021c3d74d9632c42cd386a821c61339d662d0d32a3ceba1e64a043c75592324c30eb18c72a043879d8544c930a38e6aa2831071454d85314c30eb1c8628283871526310530c3aa6b0087a0d4d7214d3084237394c7a82830f5db548c53087cecaa2601861d6314e405021f3b2a8980418d5506150a21e2886a8a632045f7654c400430eb2887a1061175cc6014910e2aa821aa21861d5458e410828eba020a98219998a6115030ae2e0212a21043e74d95314869ab8ea92a0418d550614c810aace7a92a22061e6414f315028f3a6a798c431d5db54c401087eecaa4620864d535884004237394ca218218e552600c410878eab24629851c7550c434c26a38ac721263719cc5348421c6aa8b0860084d571181434c333314c229841d85c05248710cc8a4b0e408852d74d4a520428e3a2a698c41995895110030c5ec8a92422047576d4b1004335b2ca498061555cf52544408f4e0328640862c64549300c316b24c429c21695d36348421d4ac8908a010d557594d100423a3aac221221475d66250c43c3cc829c62a052e72181540861eba4cb996218d9916114910a3ce9b2a659854d7294c329070ebb0a720281c518d51500408eceda9a200863664544300821f3b4a89804199d955148020a5ae9a94a4187616448550087a8a9aa290041171cd64d4520c72a8b04841062e6494a310423b388caa18411b9d854548308dae5328600845d7694c5090aa7390a9298218755263d4021a74e8314a010e5663584540822ebb4a7210410f5d36354810cb2a7300a010c6f76548520c23cb80ca21a431d9db535442095cec29285a052e72182548c62eb9ecb210412d5d0604c510b34e02a087187465354951102ab398a92884199d9521084108bae6302a2214cd73d9121c82ab398a5288819598d6115032a9ae4308a6a064d53988531030e2a4c610a614b5d36394810a3ae7b0ca91953671181540c30eb20a9182619558d5190420e4ca8a8e401045d73994400830eb24a6180211d1d561d0910a3ce7aa68590e1d64192530430f2a2c720843175d66390810c9cc7310a608634435845050b0f322a7a8043475d25310c31acce4304a22061e6414e215021ebb6a919261339d
  | 10 => 0x67251580210828eba0a7984419694e6014642e1ca8a9a401056572d4f100428eba0c0a9843d8d952154021dc242b00432063554984300830eb22a62982187991538c840ccac5308a818c5d731855090a9b38ec8aa6659654d6008420f0a8621a4210c5d73993504868f39ec8aa041c59515394420a9ce6304a420634645453008296b94c82a2639358d52084408bce732e840866662546400821eba4ca990218714f61509408f6eca80a02147a76d51500862fbb2a720821171cd65c8540a3ce7b22a98866662944400c38aaa68728861999896114e10c6ac8a88a21845f7359721502ab39c84a886187990530c940878ed2a2600851e73182540874aa1ac2280878b1c96414910c72c9300a60843f76552310868eb9ec52a4638759443d09318ecec29243886666258453082a7394a8992618ed97644c0308f6eca80a0a155970d0e5090f0f322a718c43999896115032caaa6b08801052d74182520c21ebb2a918861875926314520a5ce5aa28598ed13158031cc2aab8ea9298418b9526210010f84a690aa010d1c7454d430824eb9cc890a8187d91534c440caac6b08a4885957194c43506aab9c84a88819c9456008440ab2e7212a010c5e7398654c821eba4c529821179cf6454b108deeca90a520d5571182531030eb1886282850f5d0650c020c72a8b00641047671196430428f39cc32a061355c4604c9309cae4302638861e6458c5284334a92c120821c99d05148520ec0c890aa010c3d74d94300832ab2cc720e219c54560146328dce4328878856a7218d500863cb80c4a88879554f61508108dee4b2a808861d5418d410c21fba2ca18a411b9db5348020b62e918a408851e74d4e530832731aa4290219398d6214e10c3ec8a9a422051e7590f424c316aa2c42a02147dc54354043c3cc929c64106566394641083a529aa498061a650d6010f308baec21ca01845d7598e410822eb98ca908819958a61d4c10cd6a4b0042a062d65508420868e3aa86a02610f1d1650c910c5ca9310a21849e74d8d218c2a6b96a898061c31d25354840a3ae9a9ca6085957114c439030f3288798c815c5c63254021a5ae8296410858f7250e5210e2fb9ac928021c5d4c5150540c3aa8b1c821847970197430870e2a0c6a0421479d26254c10ccec4a8a821047676151510822ebaec6a0861595c851085408ece232c64087465354720083a529aa488021a350d6214043acae5a8ca22046e72194438422f3b0a8a9841179cc6550420c3cc829e64a076075485204428f39ca4a16812d5d06048510c3ac8b18a48864c535884348327b1ec4aa22187590538c940c5cc8a90400862d62189548c7b0a9a42a8043471c15410f31a3ae930ca610e1d6594e4310237394c9a8263555c75394c40ccaa4b08a52061d5418d40c422ebb6a618a41c354e4394840c3
  | 11 => 0x861ebacc9190210f5da541481099ae7316819056571d4d200822f3b4a898e61475d25310f20a3ce7b22a990e1d5458c54043a2a92a29806187992530c010a6ae22a0871853671d5254082b8b8484a88419654d6014a41c98c6312a88861f6418d544432731ca520821275db5310e408beecaa0861865653586430869b38cc0aa4630fdd16094c21cd2a5300420862d54588508c70f324c62a043a510d61ccb418f2e032a8610c5e73d9642086acb80c429a81cc5512154021e28e6aa2a21845e75d93314c32ab1aa2288858799263150108beeab1c841047a7019543086abb9aa9884216c5d06148110c98ca992629066952580520c726b1aa428881175cc6510520c9ac7310a91961f6494d3008363b2aa690843cc9515148020c70e9b2a601851d73182540861e3a2c7280214d9c46095232a3ae7314a8084797694e300c3b1a1a42a80438718d6155030aaaeba1ca2185367118254083b12a242a80439358d5210010ce2c3300a5084cd72181434c30f2a4c6108218d15161d0921e52a990aa010c5e7319742842b3396a8a8861d85512154021c5ec8a92622045f7654c534878a21aa320061335c262d0d32a3ce92a2649845d7399542c438aa9886a88811d5da5184010c3ea831a809872554d4d210863b38ecb996819954a618801087eeab1e83a051d71d50438c24eba6ca98e6195595310c421c5aa8b10a81845d73195410831632886a12418d5516110230e1ca8a96601869943580434823a38aca21a419318e5250030d4cc8908a010c5e73d9721d029b38cc6aa043179cc6510520aceeab224210e6662587540c30fb1886a8c81179cc6510910ad0e4b22a010e2d6494a32843b1b9a42a8043535c86054c408dae5b2c86885717190d500868fbaa86218834b9d0605483087eecaa0810851e73d51420caad386a7298438d592518c44087ae9314a70845d73994410870e31aa6a00811d9c4635404293ae630284a051d7510f420c30f322c62a043c554d515004087eecaa0600845c73581540430eb22a7188414b5c85410930ad4e520aa010c767119432042a739ea8a90214b9cb5450832c3aa8b06861851d7398554086abb9a84a88614e9d23294021ccac4a88a21843d74d97324432b31aa32006187d946350040b1ce9b1a64907155454f100429cb86c8aa043875925308410b52e9196409062e5498830082aab8ec6a98419354d6214c10c3aa8b18420866962980530430eb20a798a818d592518c640c9cc6a90400847575185420422ebb0a998a611b9ca658c440b4ce82a24210c767198f5050a3b3b0a4a8881591c96454420c3aa8b1c8518c767119532903a938086a88610f5d6648c821c3cc829862a069663d464150734b2ca50802117dda5390440a38e8b04a610e3564946310830a31aa2a00811d9c46590c208bae7b22a588
  | 12 => 0x980611d9c46590e20acce22a4a41866b52580214c30eb24a71904199d952108630e92a6a92802045e731954204386a9887290811d5da5288421cb4a6b00862055671d52530821f3a0c4a8c610fdd954153108bae7b2a8290d2d75951200821f3a4ca188430f5d6640c010c3ec621aa52046c7558b434821f3a0c0a9c431e5c26510c21c3ca8b18810854e721825390ba329a43a8043d494d5148020c9ac7290801843e74180524430eb1887a8a85555c46054e42a5ae52a08698d1e74d4e530432aa9ec2a1c8347dd54310c208eeeca88a3a146d72197430431d2a4c1a98438ed526008530c6aa8b0c800853a748c65008696b90a9a04618b95262d4c10c6ac8b08a7085e170d4521c830eb1887a9283175da5314642c58c8312a6885e172181314429ab88a8a0461551c56254e418eae2328869061e5418d40c432b31aa220061d154a51cc0308eeeca88a22164d63548520438b3a086a8861c6552534c030c38a730686a045d73d9152042b2b8ea529081355cc6148110c6ac930ea40843d749943008392aa4a528861475cf6455020c6ac230ca91962d6494a310428fb9ac12a463175cc6590910d1ce43028621d4e73d91520428f39ea8a1a43179cc6510b10a9ce7b12a4085c57318121086a6b98c12908187192504c030a3ae6302a810f165410d510c33432a42902218e9926014c21c3cc8a9c622056571948210c24eb9cc890e8187553635002093ae931a429866952583320c25bba2c7082210f5da5414c20ad4e030aa420474755843244333292c220021359c6644cb3187ee8b2a6090654635454010335292c010e219c1962148110a3ce930ca610c5d7694e42043a3398a290a418b9916294d21a38e8a9a648872554484210c22f39cc52a2211e9c06590c21c6aa8b08a81856471549219030f326a719221c3dc95410d328ecebb24428845d7694c2004364b1ac1216411d5c663d4142c3acaa18870845f73592500868f3a6a798a431d9c46550810a3ce7aa28290c3e76951300432c29ac010a811d9c76590d20c5ac8a94652068e63d4a4250a373aec990a4187590544c530c3aa8b1c8210d6672182510c39221aa4a88819a98a601503195ae8302439057270189510c28e39aa8a1c419598e5108430c3aec2a6649854d73d4a5210332b14c22a461785c64248110ccaa5308a21861d5498e410c63b388c0a9e8595d8c6154d20ae0e2b22a010e1c6550c4348738b0cc02a065559c46054e42f44a890aa010e655218520c42a7398c2a90619358d62d501087ae932c640843d749943108637394ca188811b5c86054c41a5ce9a94a41863664984504ca2f39ecb208210f5d0650ca10ae4ea30c408862e545883004335292c0108211e5c0654c841c3cc929c621055973d51500876331a43a8043351c56210d318ecec2a2a2187475454d21
  | 13 => 0x63d4121a98e6b0aa418635645875308256ba4c598a411b5d95210010b2ae7b228220de170d4921c431b2a2c2200412b5c860507408bae632e850846e72195430422ebb6a621c419a549600c410c3ac8a9ea010e1d64d0c504ca9d3a6a6a80438d5926114810c58c8a92642045f73594414822f39cc52a621475d54310c108bce6300a48865a6398053087a329a421082147dd16094c21c9ec6a92801863a54580210838621aa4994810f5d36354720c3ac6218a0a0e3554584540831b324a210861179db5454c20b1ce421e85995367414d510832ab1cc22a461279c36150c43c38a931c829051d7494c43c437090ac010e219598d61d53328beeab1c801849d7318141502b2b96a6a88819358d5214a10c3ca931c821043f7458e50c8717322a428861175cf65086408dae432c860870d539494010316b22c429c210f9d0650ca108dae532c860861e64553308c31a38ac828a4196dcf65500408dcec2a2a40852d740415204317322a4290619554e6110821c38c8a9a64205d170d4d31c42aabac64988632b5d36348520aaae7a8ca22061f5458c404c30fb2aa6a00818b18d5250040a3ae1b2a8621e2f5458a544c70eb24c7a9021d1dd5534842187eecaa08690c3e75991315030e3b2a8980619c5866015030a3ceb21880985667510d210870eaa2c62a0430fdd95414632c9ac4310a6a064d654c8320871db2ca888021395c66290c21ae2e021aa21855571151320ca1eba4c329a414e5d23294021caaa730e878857271192500878aaa4a688021595d65244010c38c9a9a609043e76551300432731cc5aa021555cc5294440caecaa8a601846d72194430421fbb2a8288410f5da4314141aaae62a4a21054d72d52530422eb98cba1021595c45208540c3ec821aa518695435845210f1cb22c1a984387192534c010c3ac9318a090d69720c5500870f324a7a90210fdd95415332ce4c2b00a818c3f76550530430f322c62a441b8485600861095ae532262a043e74995320429cba0c3280439554e61d4840a6ae2304a91945d7614e4250334a92c0290878d5526110020c6ca8b08400853474544514828eba040a9841955846114d40a3ae7312a81051f7655043ccb27a9ac529a8387551639082087ce9b2e639061e6498c540829cba6a6a804387591538c840ccca5308a22070e5494d520430eb2a8621c419354e62100208dae432a632066565484218c31aaa4c2288410f9d06054f21caac6b08a81051e739895404326b2ac7216418d5915114630e2a8621ca21871743545400c2b9baa42a8043565c343141438bce63284008571700c95108392a92a2a008187151618c1308bae7b2c840862e6454a321022ebb4a629021879516390430c6cc8b08a9105547154f3148334b14c02a0619998a5110020c5aa8312621053671182548c746322a4
  | 14 => 0xec2a26598e1c64d8d5348296ba0a49022187d906355220c38c8a9a618843e74181510ca3bbb2a228e878d9916115030c9aa6b16a2205c5739052108732b12c3aa061595c86054440c6ac8b08a71045e73d95215029aba6c6a88411b5c86054f41c9cc6a94840845f73593524422f3b6a8980610f9d06154830b1ae42988720729549492008237bb2a429487a310d62100308bae7b2c8410e1d5498c5408738b0aa02846587594434c440e2aa8a9c4210e3554984530823ab8ccb2184187990534c94087eecaa0420865563546418c30e2a0c0a1e611d9c46510c10c68a830aa4986347159251ccab2b8ea9900414d5d35244010c9ec7292802054c7254d32c4316aa4c4180210fdd95415320a5ce5aa4a998e5553185320428eb9ea92a021b258d2008210e28a9a8a629869463545401022f39cca208439354d620c020c5ac929040085c97390920842ab398c528861175cc6015110c3ea831a810847870595434863cbb6a50802117dd95314810aceeab1a4210c5f7654c5290733312c22a0418b59654cca328bae732c840863a54580410430f328a998a610f5d26194c20c3cc8b1ea40855a70d51530863cbb4a51004127dd95310d41cc8c4a8a621043e76151434c726a9ac4284830f5d3658c420e1886a96841867261583540862fbaac7210219954a6110030a58eaa1280904d570987434c6d33a6c690843179cc6254640cb2a6b00a62166662984530431aaa2c220441479d54310d20aace2310a6a069b64181434c32731ac5aa0614bdd54350842c5cc8a94622061d6414f215028e3aa87a0261171cd64d4a10c72a8b00a818d5970184535030e2a2c720a61879916314910ccaa5b0a840866562944300828f39cc32a0219554d610c010e4ca890ea010e1e5458c428cb0eb20c8a9843559cf5194420c6ca8b0ea61051d74181530428eb98c0aa4658b9516210210e2886a8a622064e63988540c22fbb2a629c858e5516090c30a6ae8302a21851d749855390a8f3a6a6a1a43479cc6095010a58e8b0aa4205a575951210861fbb2a8108410fdd95415032c5ca9310a60854f73553208838b29c86a8881879526390a32cacc7308a80847671197438821eba6cb1904393194434c920cd2a5b0a200861c5498c314c297ba2a7904418bd516210130a3aea21880184b57118142d023ab88c6a80858d5916114132accec28a429065a63540500864eb8ec4a18878e99160d4c21c3cc829c648845e73189509062f39cca200218e551600c8308dae53288608572718c95008717324c429c211d1d56448510c3ac8a98a21058e74d4d32c83273b0a4992638714d61d0940a58e4b02a810e7351580214c22f39ec8a8841271cd65d02408b8e6b2a809051d7395043c861f3a6ca180419598e5108420c38a931e429851e73d5254c430fbb2a821a630f9d2
  | 15 => 0x5663586544861f3b4a8a06610f9da5450e10c3ca931c8518d4c7254f324430f2a4c62982187591538c440a3ee2a9887a16367598643507b1b2a4290221555c45310e20acce3aa2a41843f7655041886b3390a8a88618e55260d4c21e2ac621aa22054e73182520421fbb4a9190212d1c5648c941e2ce229e82a064e63548521022eb9ecb2084187d954310c21a58e4b0aa91953671181540823bbb2a228a85475ce61151308deeab10801865563986544ca3abaec2990211b9cb6510010878ecaa2601066562584538428e3a2a798a41171cd6095021c6ac928c631055573081510821fba2cb90a61875944350932b1ae42a0871867151980211023b38cca21841555ce4254420c5ca8b10879964d53588308821eba0c2a9461879d854cc930a5ae5b1ca918e1e6454c2108237390c0a8e87875516010d31c9aa7b12621056671d4a520c30f2a2c7210438d9925108440a9ce62a4a40846e72997311032731ca4108211b1c96510d10ec4c290aa010d3475509414421eba4cb18841275cc6050b40f0ca929a4210c9f7650c5010eb338ea6a90811b5ca64d413187eecaa0a818e5a53580210830a322a298061569ce4194021c3ea931c84987165310d511031b324a210841871516190d30a3cec29a86a045d7654c400821eba6cb90e615c1d52188110c3aa6b04862056572944211023bb8acaa1a410fdd564080108dae432c870865763545410c2ad39ea8a80439c9856015021b60e0a0a80887154310e5110316b24c4290218b59152148308bceb31842a045d7694e429071d2a4c029843c554d51d004093ae23028621d1f7550c430cb0f2a4c721663555c75394c208bce7328400872a54549100428f3a4a8a1a61479d35390d21cb2a6b00422061d6494e3108316b22c429c41471d1530c210ac8ea90a40884e776487500863b3b0a8a0e214d9d64350510c5aa8b10a818e4d63d4a424c70eb22a629843479cf5495320e2a8621ca21043d7695030082b938084a88818e9916014b10ac8e2a92431863754d85524c22f39ec8a9021475d053d0e10ad2e520aa010c5d7654e410421fbb2a8100218b590528c941c3cc9a9842a043f76550548432bb1aa2a00410f5da5490c43e4aa8a96200854c72585530832b29ac2284850f9d06054b318bae7b28422047671997420c297390c22a261175d66308420a5ce529a85a0e576318554482aab9ea8a88410f9d36354b10e2ca929ca21045f73595418831b21ac228287d89c95148020ccac5308a91049c7650e5010e37396cb21a210fdd95415130e1aa8a9a4210d1c70550434c61f3a0ca98c419354d62d0c2187ae8312a31843f76950300421ebacc8100216c5c35150740c9ac6a94841861f7654c43d0786aa087290618b592528ca30caca6b0880105567118153082acb80c529c850f9d854549308bc
  | 16 => 0x422fb9acb10a81879526390832c6aa930ea6106695298221043863a2a6a9081539cc6054810c9ca6b10a220477755864004316b2aa9994659354e62d0c2187aec2a4649851d74989530831aaa4c2200618b95162d0e328e8eab0e868861c54983314c26ab9cc3a0621475ce6195232caca7308a12146f7654852d022fbb2a629841c350c4394810c9cc6a90800843f76550530828eba887a0861471d1534ca10a3ae9298860861d6454c300822ebb68628263479d36354f1087ae8312a018f4743949510c2ab39ea8a8841479d26154c20e18e6aa4a4184e57118132c838621aa4200610f5d6640c020a3ce930ca60861d5498c510823ab8ccb19081335cc6048520c6ac9288601070f64549300c316aa2c42a4214d5d05354420c5ec8312a88851e73d51424861fba2c7280431d9c46550e20c3ac9318a71064d53588308423b388caa1061535c85454c109ccec2a24210c7571194430826b3a8c299263c5551514c030a3ae9a9ca610d1e75d0d315022eb9eca10821395c86050710aace6314a21045e73d9421d03a929c42a80434d1c5545072087ce9b2c640861e5498f428c71aaa2c321843879916315020cceca90842206576594d210878b29aa2a00812b5d262cc120cb0a730486a045e76d51530868ebaca8218610fdd95414a31a3ce928a6218e3564944210c333312c22a421c9dd55448421e48a8908429845e731855090b2ca9ac1a1881479ce52d0b40c3ac829a64a061d5498e428cb0eb98c8a9c21179ce61d4940bc2e1aa24210c6e72995430431aaa4c2288618e5955484010e1886a92642070d53508429062f39cc32a4410f5db5410e308bae6328840843d74181530872aa9ac229c41535cb54d0f318ecec29aa22051d7550c430823ab8ecb21a418b591528c840cb0e7b2a802062e435885050f0f322a628841479cf54504319cae33168610e4d5358a300821f3a0c4a8063179ce6195120cb2c6a80a010e3464185534832ab1aa21086117dcd64943218dae4300a88851c73551428832ab08c2a9c859ad95524c0308dae432a870864d6354a428c326a9ac42084317dd95308410a6ae8304a21866562584540c2373b0a4904219318d52500308bce7b28432055671182539061fbb2a82a465959d4614c931a72e918ca010c6e72d97434431b324c229021991d92154021e1886a9665a0c3d76d504244316b24a41042117dd56308420c58c9b12a48851e7394942d070e324a6986418799443d0630c3cc929c642063554584530822fbb2a7210438755363500308ece332c841846d7694830043932a4a528861d19cc524871093eeca18a221dd1739071044317b2aa4a00819318e5250040a3ae7312a918e1e6414d215021eba0cb990218bd8a62d5130a5ce5b22a80843d74197328422eb9eca100218b9926214c108beeca9c82106
  | 17 => 0xe81475d25310c32a72e831ca010e3554d81100422fbaac721043479d353cc710c9ecaa9a4210e1d6510f311028f39ea9a10659658e6015020c9aa7310a42055571d53430c21f3b6a8a9261179d85354540c3ac8a98611051e73d5341c430e2a0c098a61d81d92154021c3aea322601862d6454852842a7396c929c831d9c4654c8408bae632a8508559701515308636b90cba1c210f5d9540c020a74e829ca010c5e739885448317322a519083475d54310e21c3cc8a9c640851c7355054443172a2c418041175d663080108eae232a8418636645845384236b90ca180210f9d85450220c3cc929c62204b574984314422ebb4a629081595c45208530cacc7308a0a1659539804110237396ca180218795263d4420c70a9306869862d6494a3208327322a4980611ddd95114420cccc4b0ea610536748c9510c32bb1aa290861879926314c10a3ae9b0ca72143d74194300422fbb2a610021539c86114d40a5ae121aa4204e870591324829b38ec8aa0619554d61900108f6eca80a020e34545844344256b84c521a85479d251cc730c9acaa9e852145f7694c21102b2b96a8a8861c955121d4021cd6cb2922008476711895010f26b1aa5200610fdd1650c91087ae8312a21861f5498c404c30eb24c6290219394e6210020dc2c390e409056572101511022fbaac7208439358d621501095ae532263a046d72d9743486cb39ec8a0e218d9526114430ec6e090aa010e3554584540cb2a31aa2a00418b59162d4c108ece232e640852e72182540c24f3a4c3996631d5c46054843c6aa8b08800855673189510c31caa2c010821179ce65d0b108eceda9aa22043d741953108316b24a428861175cf6590b10ccaa4b08a41843e76951438c23b388ca21c419398d5290440c3cc829842a065465d0d314430eaa4c7208219558e61d5010c38a9318869861c53983415033930ac1a98438715163d09308eee2b2a648843d7498f50486ad380a8a9843555cc6094440cd2a4b00422064c63d89544429b38ca6a0e818d552618c010ccca4b08400872954549300c32ab1ca3208618b59252d4430aaae229862a045d7319641482b2b8ea929061175da5390821c6aa930c878845d73d9521503333b6ca90843d8dd5219402187eecaa0a990d387050d5010f0eb2686282634b9ca6055232a3ae830ea6a076065485204432cb1ac029621c99512108430c6aa93086410c7671996321028eb9ea92a0438b9925208410e2ca8a8a601852e72d5342cc62eb98c4a88818b5516290020ce4a2b00822047b76540504870eaa2c7210614d5c454d023087ce9328640846f76548524c6f0ba242902213c5c4604c9208b8e6b24a010c3d7419431482e2b98a89084347dd56150c43c3ca8b1c820849f7650e5210f0fbb286a80879998a6115010a5ce5b22a998cb574987304
  | 18 => 0x5104308f6eca80a098e956410d314421f3a6ca10821d154d2154021aaae6302a22054c73591520c28ebacc2a1887475cc5410d20c3ca9b1a801846d72d9643486e8b9c8290221475d25310c21a38e8b02a610c3e76151514c2ab38ea7298810fdd954151208bae6312a32051e74181530862eb98ca100211d9db5454430f0aa929a4210d4c754c9304821fbaac919021531c9534ca41dc242b00439855675d0d3144266b9cc5a0a418b1954250720c3ecb29a80205e270d4d210872729ac418041535c853d0e10c6ac9288422063564944210830e32a86a026187d91534c840ec06290aa010e3464945300c2ab39c84a88818b9916214e208bce6312a020e695258231043162a2c4206611d9d76388510c5ac8a94622066652584208438ba1aa3a006199549610c010c6aa9b0a8518f0d6310d521021e3a2c728041569ce42540218bced29a800845f7654e420421e3a2c7a8a41475d26214d40a3ee4aa08798d4d73d52520430e2a4c121a6187d5263905208f4eda92200847475586434428e39aa8a0c21175da5314a41a6ae9a9aa21054d73186521032731ca4200614b5cb5495010c76caaa2601855671151530832ca9ac028c85c95515348421c3ac829a42a063954980530870eaa0c6a00611d5c765d0f20c3ac82a6639843f7654f4010392a92a3a0081c5191514c030c6ecb2a24210d4d73041520432b29cc2100210f9d363547208beeab1e8418d6a7290d5008727b2ca498061179cc6454021caca730880087325488550086aab88a6984419a54a600c410ccaa430a64087195454e500870ebb6a821c6117dcd6510910ec6a890aa010f1754145314c32b29cc3a908187592538c840c3acaa9e8320e39649805308326b1cc42a421c39515394810c9ac4312a720e94644c530442b3388a729081555c46094c20bc6ea90aa010e1e5458c408823cb80caa10630f5d06054b31c9ca6b14872151e74d8d534871caa4c010841479d35394c21c3ac9298a21043e76151420cb33312c22a64387dcd6414132a9cec2926498d567318a5110316b24a418021875526390b31cc8c5b0aa68852e74186521021e3a2ca994218795163d4810ca8c7b0aa48843f74595204429b3a0c128861175d66390821cd2a4b00a420c6e72197430430fb2ec8980618ed95544802093ae8302659874a53485500874631ca4a0081175db5310e10a9ae5a9ca60861f76550434cb32b08c329061175d95310010b2ce9b1a63884747159543483b1292a2900418d5915114432a3ce7aa4a910c5f7655043ccaaab98c4a88818714d6190140a3ce9296659845c7694d400831b322c229c4159dd560484218bee6b2a432046d7694e320caa7398c329021c354e52d0040a3cec2a2879861d5458c400822f398c0aa043479ce6255021c3aa9318a6105957194c4350a4eb98c0a
  | 19 => 0x7316a0a0e2d549884004316aa4c5180418759053cc940c5aa8b10801051f7254c43d072ca9ac0210411d9c765d0f208ece2302a521d1d73d88544c32729cc42902117dd563100208ece332e861059571150438c32b31aa228841595c85494430c9ac6a90420845d73181529079538086a90810f5d36508010e2ea6a0882a051c7054c43d0ac73a6c6996418d9526110030cae86b08a0a1e1c5358b41502b3baa4210881535cb6494e41c3aa8b1c8018656635845050a37bb2a429683d194951cc030b1ce7aa2859070c4354b410c22ebacc7210414b9d06154830a38e8a9c610861e5458e420c26ab98c0a0e21479d36354e21c3ac8b18a40851d73181548c72b31ca2108814b5d35394810ae2e1192a21056671151520c22f398ca90c81c395153c8020c3cc8a9860105557318251082b2b8ea790041599d8524851087cec2a28218c3e76151434ca2fbb2a6298810f9d66448540caac728c832045d7318154c86b2bacc890843475cc6055020a6aeb21aa22061d5458f5108332b12a32004187590538c54087ce9b2c631062d5418941c870eb22a7a9021535c8544c431a3ceb21c809864f6554d200831b324a2180419a54a600843087ae9b28420861e6498c514822f3b2a6a0041569cc6294021a3ae829e61086556558e41c4334a94c0208819a54a608c410a3ae730aa810566720c1510c23b38ecb21e41569cc6454021c3cc9318a408671619835408332b14c3a9c4317dda5308010a3ae9314a60861d6419253082b238aa4908611bdd95214943e2aa8a9aa2107255454a510c28f39cc2aa061c995121084108bae632a840845d7694c510830f322a718821179ce6550b10ec2a510a200859771550434c68eba4c4a982187d954310c2087ee8b00a690e1f6454d300430fbb2a8218619654d608c410878e8b2a64885a9748c9204428fb8aa621881d154e525444099ae5b2663985727190d5008726b1aa4200618d991518c430c5ac9a9042a0564725445150335312c1aa043719cc5448421c3aa931c8518de37348520443b090aa0280434b9cb6315130e8aa6a94a22062e64588540c21f3a4cb908614b5d06054810aaae3aa6601861c54d8943cc32d29cc0280430f9d261d4930c3ec629a82a045d7654e41083273acc5a1a65175ce6550d2196ae830a408861e5498c5008770b1443882219358d52d44408bae6302a420ce972181314421f3a4ca10861999d8524871087ae9b28600843e7498b514c30eb22a6184211d9c46054b43c6ec8a8a60184b67198f425077090ac010861339d8534cb20c72c9300a40872554545200828e39aa8a184195191514c030c3aa8b18a21043d76950510c29cb80a8a10654d9d02054420c5ac8a90a5187c1324c52044317322c429c210fdd95410b20e2ae22a6629845e73d96410863ab88ca192811b5ca6
  | 20 => 0xd6394a410438621aa5988810f9d265cc720c9aa6b146210cd570185324c70eaa4c610821539ca6454c21e8ce629242884b574d8e21442b2b90a7288811b1c96550630a5ae829aa40851f7655043cc6b8b8c84a80439694e6014a418bae7b2e839064d63948210c21fbb2a9188414d9d062944308beeab18420845c73595418830eaa4c721643cc5522044010a3ce9a9e6490d36741825108338a8ac010e419398d5208440e2ca6a8e802052e74d4a52cc716aa0c4a08410f5d6648c421a38e6aa0a91055673d9251083b021242a80438d191514c440c5cc9310a40861e6454e3108786aa4a498061179d8534c220c3aa6b0087a164d6398b54082a6b98a8a9021c65515344010aace6202a22063a5498050086e239ac0908439cd955148020c9ca6b10610864f53189515022fb9acaa122195d4f6154940a9ce5aa2a60859571950434c636b90c2a8087355cf6448710caac6a88801061f64d8d524431aaa6c2990212d5d36348510d2a87308a021d1f72550434c64eba6ca99661655ce4250441e328621ca010e4d63d4a425072d29ac01088139dd9211402193eeca1aa221d1e73d52540862ebaec6908612b5c86050d40c68cb21a828845d7398654c822fbaac72082187d516308530cae86b08a09954d73149204430e3a6ca980610f9d365c8730cb6cbb1a802043d76952320868f398c0aa021879915308440c3ac829842a056571d4e521029b38ea92a061635ca5410d32caecb29a200851d7510e400c21fbb2a82a4439c58550140428bce732c8210667659452008326a9cc4180218d55261148308bce6300a88861c5458d214c2cc38287280871b9cb65cc74087ae832a631051e74d4f32c861eba6ca90e61175d95390421ae4e0212a21043f75593321071a322a29088117dd563904208dae4302a720e5563946410830e326c6a9c41559c46294e42a38e6aa6829047b7654050c8716b24a410821475d54310f218bce7b2e858862e54588408830eb18c72a021175da538c03093aed218819861e6454e320872729ac5a88810f5d0658c520a5cebb1284a0e1e6494c510828eb9ec8aa043561cd6454021c38c929a618855673d915108326b1aa4290819c5866014c2087eecaa4641061e76151434c3b129a42a80430f5d0605463287aecaa4641843f76150214c2b938884a80434d5d23254430c5cc8b16a60843e74d96320821e3b2a898061179cc6054a41c72c8b00a610e1d6454e320425ab88c0a1a81175cc6154a4087aed2a0a518f455354b100430f324a6108414b5c85490e10c3aa8b18a90861d6454c2108316b26a5292631e5c26590c21c72c8b00a58843f7459531882ab39840a88411d5c4654ca40a3ae8304a720e5963583540870fbb2a898061171d56390940a68e2b02a810c7a70196420428f3a4c5298412b5c86050c438bce
  | 21 => 0x30e326c6a9c21175d95390820c6acaa088210e7151583210830eb9cc9a9a430fdd95415121c5aa9b02401049f7650e5110e36bacc521843879926314121a5ce9b1aa42061d6414c325031aaa2c2204214e5c0629523287ae9316a098c7b76540509068eba4c229a81471cd6095021c72a9300421846d729973110237b92ca21a218b991528c810c3ca831a801852e74d4e52042a7398c0a9081875d8548c1308deeca90a48863554584520c30e39ac929a439354e6214440b8ae72124210d2c745485244237390cb2182187152630c930a72e829aa010c7571997430823abacc2200410f9d26294e10c3cc8b18a40843e74d9631c8326322a598061471d54310e20c58e4b24a598e1e6494c200421ebb0a918a619398d5214440ae2e021aa22054d73185520438a39ca8a886199149610c910878e8b1ca010c5e75d91314c326b1ca5214811b9d85248710ccaa4b0c800845f7694e41086d33a4c690843875516310030cd2a4b00621874553484210829cb80a8a08630f5d06054432aa8ea98e6088477765445150297390c12a0438ed96544c0308beeca9c8210e1d6415132cc23ab88c0a968787591538c821c9acb31c859045f735954284316aa2c418843a518d4150110c9aa63126390e1c6454d3008394aa242a8043539cb6494c21c6ca9308a41845e7694d438430e2a0c6a04619398d6214141caac6a88a21055970151310c716aa4c5a9821359d661d0d318baeb318422061d5498e4208386aa086a9061471d153cc610c38a7b1282a049d7418131cc3e0a9a4328043535cf5294810ec0a690aa010e1e5458c500869b388c0aa0439654d6010440ec26490aa010eb14158041d023cb80ca21c43995846154830c3ac829c42a061e6498c52c42f1380a6908438d952610c010ce2a3300421062d545883004317b22a4990814d5c65490d32c5cc9290600864f63189534430e32c86a0a61c314f5250940c38c8a9a619064d5398a400822eb9cc52a421995896114143c9e86b10a0a1e596554e1004398aa442a80439cd965150040c6ecaaa24210c6e72195438423bb8aca21a411ddd95114642a3ae9314a61061f64151314c28ebaca8980610f5d06054f21ccac4a88a31868c63509404831b324c22a0414e9c34354043878e8b00a690c5c7359521902e4b98a4904211d5c5650c01087ce8312a118d1c7650d5010f32b14c3aa021875966410c308deeca90a421e6562987548870eaa4c62a021d1d4d2108540c3ac9298601054e731855210352b20c890843595c86094440a38e6aa2870863454984404c30eb24a718881c35c854cc9308bcec2a26218e964358440cc30e2a2c7212618b9926215010c74c9300a40871a5454e500870e2a2c790a610f5d9540c010ae4e2322a010d1e73d9154c82b9380c5288618d192514c020a38e6aa2860864
  | 22 => 0x618ed94644c030a5ae4304a81861d63d80544c30eaa2c721043879d85350d40cb6ca31a802061c54983324c30f2a6c6a00211b9c86454031aace2302a62066565484211038baa26218a618d5516108010a3ceb21e829861e5458e410828fbb2a821a652b5d262cc72087eecaa0421865553d81100422f39eca90e818bd965448020e34a8a9a802043e74d95214c31db2aa8880210f5d06154032b30e0a1a809870d5494d520431b3a8c2a12831b9c86510c20a5ae830ca41863554185328c6a6b90c129881475d253d0d21a3aeaa188690e2d64548510c30eb22a7188214d5d642504418dae432a860866552984520c23b3b0a4a88614b5d06054830caaa7308a42063764185534832731cc42a4210f5d365084308f4e0328840861f73590504c716b2cc919641991895150420e4aa9292200862e7598a4350b8aaa4a3980618d591518c430c3aec2a6629851f7258c544c22ebacc8980610f5d06054a318dae5b28600845d73184524430e39ac829c210f9d3650801095ae9b1a439061e76151314c25aba0c098e214d1c554d0520c3cc829c629045f76550434ca1eba0ca188434b1d542d0120a38e6aa6851062c64949300428eb9cc32a041171cd6494020a58e4aa0a8884b67614541d029ab88c0aa041c3d4d4210940a3ce9a9ca78851c73589540c29b3a0a5288619654d60084108bae6302a3a17155390e511028f39ca5a16834b9d06094830ccac4a88801061c54181434c22fbb4a721043d81cd2154021a5ce9a94a40851c7454c30882aab8086a886147dd95410d31ec48290aa010e1d64d4e534874a324a298061475cc5490e10c5cc8a90422043d76d5041482c6b94a621a83879964310130aace22a4a61074653549100428f39ca2a0e81d89c1524401087aed2a0400846e72196430832b31ac22a44117dda5390820a6ce9b1ca210665629845388354a12c021641c99515294430bc6e2a12410861e5458f500870eaa4c628043171cd64d4910c9aa7b12821065553584400431bb22a290881539c86054c40c9ec6a92841874743549510c327b14c5a9a8199d886154d20a9ce4304a610e1e5498c21082aab9880a8881875935308540c6aa8b0c4008569721055008738a8ac0108614b5d64394840c3aa831a801074553947200822f398ca214218b1536254530e1a8621aa42052e72182548ca1ebb4a8298211b9cb6590f10c3ac631ca81043e7499732c422fb9ac02a243559c46094c21caac6b08a5086c76594d210872ca9ac029843b8185214821087cec2a28590e2c64d895344398aa2a31004117dd95310d219aae730e858843d74194324432b31aa3208619554e618c010a3ce7b2a85a045f7654c521031aaa4c22a06187dd95410f31a9ae5aa686184777654451cca36b90ca20021569c06294e428bceb31c82a043d765502004
  | 23 => 0x10d21aaae7214a21847475584434866ab98c090a218b5516210030c3cc9298601055673909510822f3b0a6a92811edd950142428eae232884986a964480204430e2a0c6a0261669c05310e408bce632e840863954580310c2b3396a7288818b5526215010a5ae8296408846d72195410c2b3390a6a888147dd16054c218bae632c84086395498050086aab9ea88802193d9653480208b8e6b288488477765445110e1fbb2a82a0219394d620c421aaceba1a638851e74d4d32c828f39ec8aa043c598c4354440a38e8a9a6510595748c9310c70f324a7a80431b5ca65d0c10c3ac8a98422061c53587435032d31ac1aa0430f5d262d4530c3ca8b18400856571d51520c38aaa4a6a884199989518c020ab4e7a84a010e2d54988530423a3aac898a21591d5210854096ae230287a051f7550c43c430eb24a7a80430f9d85450621caac6a88422061e5458e420428eb9ca821a63ac5056010710a6ce2314a91952e7218154043a8a9aa2a00815a9c06194840e54a890aa010c3d74185508ca5aba0c090e21175db5308540c6ca9308400861c54d8d404c296b90a821c214d9d363944408bae6328800843d76d5040cc28fba2c129c83e85512154021cb4a730042087165454d1004296ba6c4a902117dd95314e20938ecaa260186e121580218c32731aa5a88818dd8661d5130ec46490aa010c5d7694c434863dbb2a0280439514f6154940c5cc8a94620849f7650f5010e1eba0ca19021c31cd5454830b52e1a9285a074453484215022f39ecaa0a43c310d529003087ce8302a39947676d51100422fbb2a629c818e9516010820c5aa8b148210e5b5318143503172a2c5a9821479d06054c20c3aec29e84a046d7694a210861fba2c7280218d9926114c108beeca98a21061f6314d425031aaa0c2a10210f5d66408410cb0a730064a056675484215022e3aac720a819a5496010440c6ca8b08a41861d7614f415022e39aca10a814b9d36394840d4ecb2a24210e1d5498c400832729cc4290811e9c06510c218eae3b2e65a055673d46511030e2a6c4a1a610f1d1650c520e62e021aa220669525805290716b24c4298438718d51500408dae4328829861d6494c308421fbb2a9190438bd91524c0108dce432c870854c7254c534432bb1ca2a0061559c6544c5308f0eab0084884e67614921c4332b12a2288810f5d7644c4408beeca986310d2e72181548cba529aa508021275cb6550c43c3ac9298421064c53189515022fbb4a721021a310d621023087cedaa2a29861f5418d4044237bb2a429281479d06094c21b1ae7b22842154d7214f308421ebb4a9190219a58a60d5010b8ae7aa24210c5f7655043cc78a3a4a6a8881479cf54d0921aace7a94a22051e74989530868e3a2a6a1c21475ce6215130c9cc6a94801866852580214c32731aa521
  | 24 => 0x2948498e2d5498b510c28e39aa8204410f5d265cc420c9aa7310800870f43549400c2d33a6a6908438b9916215230c3aa931c841855973186500870eb22a610021599ca5248510ca8a6b08868845f7654c2110316b24c4298211ddd9510c0208f4e032a8418d3571950434cb932a242108410f5d06054732c3ac9318a5084d57118143cc26ab8cc721063d1d9553484218beeab18841953475505404429aba0a528861539ca54cc931cccc4a88801861e5498e410c63cb84caa18438e95260084309aae2302659855571153320cb17324a5a8861ca5515244010c3acb29e852156b75485500861fbb4a9190438b591528ca10c5ac8a96a21853574d4a510c332a94c2290819a58950142418d8eab22649061c53983425022f39ecb210219654d60108408dce431aa020ed16358241c439321aa52888117ddb53085408e8eab0c848871554d0d510c22eb9ccb908811ddd95114620958e4b0886a163a64580540cb2aa9cc2180411ddd95114640caaa6b0e8610e1d54d8d420c30e32e86992819558e61d4810c3ecaa18871055973906500861f3a4c429a41ac591608c710ab4e1aa4a610d1c7454e438432b322a3980619354e62104218eeeab08601072a54549401028f39ea9a0c43875516314021c3ca8b1880186556354451102e2b9cc8908439398d521003087eecaa464086656218a511032621ac4282636a5c35450b2093aedaa0871845d7654c210432ca9cc0208218b992528c43087ce9b28600851e74d4e534861e3b4a8980411d1d56348510e8ca6a94a22053574d4d100421e3a2cb10a61c3d51320c930a5ae42a281084b671d9332506a7394c0a9c858dd91514c440c38a8b14869865563584548833232a42902210f5d0650cb108bae6328858843e74994300821e3a2ca10a6117dcd64940208bce7314a80861d6510d420c3872a086a90614b5cb63151308bce6328648856a72d0d50086b23aa43902214d9c46055231c3cc829a62a04757119443c83873a086a9061d254d5290040c3ca931c8410f626248550086aab8ea821e65179cc6054442caac728c831061e6454c530821fba2c728041b158c6348421a38eaa18870876270545200822fbaac999661d194e5254440a3ae9312a720d5973085500863abaec2a1021695d3534842187ce8302a610d1c7454f32443a538086a9061475cf6455010c5ac8a94640845d73d9641c821eba6cb18c411d5c6650c8408bced2a2659852d72151410c70e320a698441c990e5254440c72c8a80a018e2f64949300c22e39aca20a411d9c46510f20ab2e1b1aa610e1c76553300c21fbaac9194631ddd95114740ce2a2b00a21956572182510c30e2a2c710a61179cc6055221ec28290aa010c7b7654050886a6b98c2a9081559cf5494420c3ea8b1ca890e346510d414428eb98a821a21475d253
  | 25 => 0x6498753886acb98a92804387dd26590d30a3ae930ca72143f74581530430eb2aa7a14851b5c8650c540caaa7308a12153571d91540c2ab398c0a88411b5cb6590f108bae730ea0a163564546319028e38286a80879354d6214c4099ceda1a649065463945400c3a329a42108418d99161d4c20cb2c6a80a02163a54580518ca8eb98a821c21555d74354430c6cc9308a6104767118154cca8e382a821e65175d84394332c3cc8a98a610c7671191500cb2b31aa220041535d653480208bae7b2e43a045d7694c400822ebb2a7210219518f6155120c6ac9308a09976152545401030eb2e87a0061879925308440cacc6a8842186e362487104421fbaac8108419359653d0a4287cec2a2838851d73989540870eb22a6290218dd96544401099ae630243907515388110043b0b80a490a218e15260109308bce7b2c43a043f76550410c69b3a464a88811d9c46055032c38c929a60104b571991325032731ac5aa0219cd96514c0308f6eca80a01961d64153314c2c6ba6c69906547dc55410f32a3ee2aa08698e4d63d4a525061e3a2c7a94215a5c04354830cd4c4b00a810d3a748c9500864f39ec8908810f9da5450910f4284a0a4088571710c9500870eb20a9996619694d600c410c6aa930ea41843e74d9621cc237bb2a4180218b5915208440caaa7b0a640851c7054c43d0656ba4c5986419658d6014520c3cc929c65a0e1e6494e32906aab9ea9288418758c53d0540a3ee8b02a720d4d72181539069cb80a9a106595d8e51500208f0eab00869043e75d8d415031b324c22a0619594d610ca41c3aa9318a60845f7654c5390726b1cc428283355cf6488510cb4c6b00a48865a53580529070f2a0c6a0021179ce651081096ae030a84a0c5d7694c509063cb80ca192834e1d163540218eaed2a48220d1e7498a5310333294c2180218759443ccb41c3aa931c80184ad7218143d0334b2aa5080210f5d26294d10e34a929ca010e2d54d89438cb0eb24c6298431e9d854540218bced29a871051c73551428438621aa5a1663535cf5448020c9ca6b1080085367118a548c6aa38aa498e61539ca544cb31a3ce9a9a6310e1d6454e310868fba2c129c85a510d61d0b31cd2c5300a808763314855008727b2aa4980614b9cb6395231d8cc6908a010e5761987535021fba2c728443879526310a32ce4c2b00a81963554d85328c732292c2212214d1d5425071087aed2a0a118e2e5498852042a6b96a998061c510d5150430c72c8a80a01962e54988508c71aaa2c2180419998961d4f21c3cc8a9c65a0c777159532902d4ba0a4904218b9516214231aaae7a94a22047b765405050e2e3b4a6a00214ddd153c42108beecaa661184e9721814144387aa0a4992618b5516214430c9aa6312621047b76540508c733312c32a2638b595648cb20c9ac6
  | 26 => 0x8f3a4c3298418dd516110130a9ce430ca72161d6410f524c6ab38ec929c850f5d06354021ae0ea90a40887147454d511022f39ecb214210f9d26294f10c9ec7292800855473509510c21f3a4c5a82631bdd95214840acce3a94a521c75711815290f0eaa4c7210431bdd95210010a5ae029284a0c3d74988534838aaa4a7880214b9d05394810ccaa5b02200861f5498e414c23bbaac3100219358e6295131a9ce5a9ca7a0d997010c400c28eba0a621c418b591528c4108bced29a629051d7414c434822f3b4a6a004187dd95410f32e2aa728a802051f71550430c3b0a92a3180619a5496088410c3ca931c8310d55711825390a2fbaac610021475cc5450210aace3a9a62a051c7454e308832cb1cc02a021179d85454c21b90e0992609064e6358854042ab38ec6a9841171cd6550a1087ae9b2a6290e5a535805190b2ba98c2a9281b84866014021e4aa9292a21864e63588530430eaa2c7a90218e99260d4c2193eeca1aa421e1e5458c408c237390c029a21d154d21084408dae4302a221c6c7558a434828eb9cc32a043a3993528c932caaa7308a210715435445110ea7390c129821a650e6014443a3ce7314a81854e75d0d32c8317322c42a421179cc6054841d4ecaaa24210e2e5458b430870eb24c629821d154951cc030c38a931a42985367414e51082e339ea8908431edd950140438f2e030aa421d34744c9511032d31ac02a065275cf6550b40acae3290422043d749942004370b0a4010221d44c43154021aaae7a92200845d7654e42102b4b9686a80438d18d5150040ec28690aa010d8f72550434cb38b0aa0280658b9516210030c3aa8b1c820853571d8e548cacaba6c6988638755163084208daeb3168610e6552584400423ab88c4a80879554d6114c40878eab20429843d76d50438422ebb6a720a814b9d36354810e36e0a1aa021d1f7550c43c862fbb4a720841a999121d4021cccec292428853a741865008734a92c010821479cc60950209aae630a418868d439885010ea7396c6a98219358d5290440a5ce531aa810e35645845284297396c8aa0611edd95014031caec728a802064e6354a4104334a92c010e218d951611423287ce9308a68864d535883004326b1ca410881359db434c5108bce6302a5a0e1f6550c430421eba6cb190218715163d0531c3ac9318a58843f74595304431c2a4c010a61555ce4294420c3aebb2a8621e6562984540c334a94c0188619954a618c01087aec21ca02053a70d52540869ab88c0aa465595c83054430b52e8292408870d54549300c2ad398c928043555c45454c20cb6caa9a802043d74196324423ab88c0a9e851d5c665d0830a6ae828e829045d73d9521d022ebacc7208430f1d16548110dc242b004390477765445190f1cb24c1a98431b5c86055031c3ca831a8190635
  | 27 => 0x21471d16254c40e82a690aa010e1c5458b314c392aa2a3900410f9d85450230a72e831aa010f63634855008696b96c8aa0210f9d06548630aace7b22a21846f7558a400823d3b0a490421275cb6150c43a6ae9192a22053574d4b10042973a0c0a9021c61c143540438f0eab00648847571d97434839221aa5288811b9ca6510430c3aa931c838849d7498d21cc21f3a0c0a94638b5526290c21a3ce730ca810e54639454008266b9cc5a0e419554e6114c20c58a8b1080984ae7598a4350b172a4c5a88618edd3654c030acae2304a41851e74d4d314870f2a4c7210619694d600c820c3ac929c6520e66529844004237394ca200214d5c66415132acae5aa2200865b6554d100422fbb4a721081565c05494c218bce6328801061e6454c520423bbb2a2288818b592528c430e1aa8a9ca40845e73d9151c821fbb2a8204619358e5208010ccec430aa89068c644c9304831d2a2c0294638718d6255030d2886b088018745539491004326b1ca521021cc551518c030aace7b24a2184cd7218143cc30eb20c8a9841871d16314142c3aa931c84195c970d4932cc21fbb2a82a2659358d5208430e4ca8a92200866565484210c22f3aec999261639cf6450920c3ecaaa2601851c7454d430430f324c6294218d5526190c21e9264192a010c5f76550434c70e326a698221171cd6015121c6ca930ea41855973192500862ebb6a7212810fdd16508530c38a7b0a86a045d73d96424432aa9ac210021475d66410c30e2ca9a1aa2187495394920082a7390c0a9c858d9916114c20c58caa1282906565358430882ad380a929843875915314c20d8ac6908a010d1d759814310f0f322a6108215a5ca3154021a5ceb21a859047671197430430eb22c628a418d991518c44087aed2a4802046f76548521069cb84862828717dd9530c220c18c8a92601845c7654d400432632a6498e410f5d85408530c6ca930860104b67615141c4316aa4c5218650f1d9544c01093ce730e85a0e3664544210c21fbb2a829021569cc5494021a3ce7aa4a81062e545884108727b1aa4a08612d5c46050c43a3ce6302a810c5f7654c500861fba2ca994219a9496008430ccca4b08801861d6454c5008734292c010a811bdd95208210c3ca9318a40865553d85429063b388cb210219394e6214440bc2e510a408843d76d50214c23b388cba10214d5d05394420c3cca2a6649845d7319642c431b2a2c2204210f9d0658c520c3ca931c8318e1f6510e400c31daa2c010a611d9c46510c21a68e8b12a22046e76d51200832731ca5208619358e5214440c9ac4314a720e5553586200431ab08c2aa465a59c46050c43c3aa9318801853571182540c28fb9286a808717dd95314d10a9ceba1a649061c63981540c30f324c7a90218798d53d0240c3aca21a64205727018951102
  | 28 => 0xc7309aae3b26649862d64548200428eba6c429a819518e51500408deeca90a418e71515805190ab938064a8861551c5534c520a3ae7aa4a8107465348550087862a284990658798d53d0040e4aa8908420846d72194438428e39aa8a1221479cf54951218f4e032e8610f1554547300c29d380c52a465479d02154c21a6ae9a9ca21045f735942150392a94a2a00814d5c46095020caac6a88421061d6494c211030f322c62a421479cf6455221c6cc8b08a50861e6494e31887162a2c5a0a43175d8530854096ae930e648845d7398a544421f3a6c6a90211b9d85354810c9ec6a9242185657114d521031d2a4c0108214d5c754950308f4e0312a221c6f75588400430f2a6c6a00418d1536154930d1c86b10809870c54d49324c3a4a9e42a8043359c6644c931e8886a94a21861c5458c424c21ebb2a9188219558e5110030c38c7b0aa81865653984521032b29cc2180411b5cb6510010aa8e6b22a2185567314951102b33b0a490e218b9516210230a3ae6304a81051e73d53414861f3b0a8a16634d5d03054430cccc4a88a21861d6454c300421fbb2a8290611b5ca63d4141caaa7308801045d731815190b35312c02a0659a54a6010410ec6c890aa010d2e72d52540c236bacc420021179d85450f30c9aa7310a6085697290d500872729cc428483879516310010a3ce7314a810e1e6498c530821f3a6cb19043555c453d0e20e28a7b0a82a049e7614d43d028e39ac0aa043c65525394021c98a7b12a2a063954980310c393292a2a0081179cc6055321a6ae3b18a89861c64d8d524421fbb2a82a461471d153cc620a76e8b1aa010e1e5418d40cc29aba0c0a88418759654cc631a3ce730ca81054d75909320ca8f3a4c2a9881471d16154c40e4887292a22063554584508ca1e3b4a8980614d5c76455020c3ea8b1881986555318542043b121a42a80430f9d2654cb108bceb31a429872a5454a1004237baac51804117dd9530c21087aed2a0a41863765545401031aaa2c318021559c46054c21a3aeba1a801864f53d89515030e2a2c6202618d95161d0e31a3ae8316a6a047571181548ca5b3a8c2a12831b5c86354041a3ce7aa4a80861f739974350362b1a43a80431d9c664d4132a98e4b02a610d1e73985540863d380c2a9087875915314e20aace3a9ca7a163954580518ca96ba0c2a90214d9d352944308d8e4b2a868845f73595404428e39aa9a0c4193d96534842193ae7b2a83a045d7654e4110387b1aa4a00810fdd95410d3287ce9b2c65885c97390b2048386a1aa4290878b9926214131ad4e021aa4205567118a539063d3b4a2880218b951621443087eecaa0a8887155310e51103b03a242a80438799253cca4187aed2a0a010f0d544c8328c68eb9ca821821475d06094c10cd2a4b00a518d1d73950430870f2a4c6100
  | 29 => 0x1aa218655535844208716aa2c5a88618d9526110020cacc6a8c822063654987530822eb9ccba1021179d8534cb218beeab18422045d73994420430eaa2c6108618715263d09308bae7b2843a066776485500870e322a49806117dd95390a41a3ee6b02a9194b57199132d032731ac42a44156dcd64540218ece232e86106c93258032cc22fbaac620863d854a2044010c9cc6a90420851e7494932cc78739886a90818b992528c440ea2e021aa21861e5458c418c68f39ea8a1641c35534394830c5ac8a90a4084797099743086b938086a88618b59262d4f218eee2b2a851861c64545300c38aaa2a728841279db43500308bce7b2e848871a5454d500870f3b0a6a0a818bd5262101308eeeca88a21869664d46314c68f3a4a499065719ce4248421c5ea8b108198655535845308296392a8a1621179cc6550a10a9ae02926498c3c7458f52442cab88c0a18879518d514843087ce832a650874573145214828fb9ac0aa4639958961152108bae7b22a2106676594910042b938484a884187d526390910c3aa9b1a821874953549100432b31cc2290210f5d26114d10c5cc8a94641870d6410d520c28e3a2a6a1c411ddd95114532ccaa5b0a640851e74985530863a3aac319221c99d05248710e32a8a9c401070d5454d200830f2a2c721041535cc52c8110a3ae9b1aa60862d64548208430e3a2c6282838d5926114c20c5cc8a96a21870c7454e521029d386c8aa043595cb5394440c6ac930ea61056571182521030f2a4c7a9021879516314810e4aa928a401062e64588540c71aaa2c22a4418d5516190821cd6caa92802072654949510c326b1aa429481475d36294e41a9ce42a2a60851d73986540422f39cca208414e9d23154021a72e030ca918e3664584540831b2a4c2288419318e5250010a72e9192a010f6032485500870eb1ac02a261669c35310e40c9ac7310a91855671d9053502b2b88c0a90611e1d5608c9108d8eab108690f0d5390d5210237390caa0861535c8530c940c3cc8a98a010e3a64580540868f3a4c5298434b9d06154840cccec28a429043f76d50214c334b12a0280830f5da548c8308f2e0b28420853475507404438621aa5990810fdd5640c010cb2a6b00820851d74d8d5308387a1aa5a00611bdd95214810c38a931c84985347154941d032632e8699241c510d3254440878e8b2a431861e6494e3208726b1ca410421cc5525144010d36c630286a061d5458c548830e2a0c6a02219594d610c8218bcec29a659052d721534084326b1ca5214211d5c56510010a3ae8310a6a063664584548c30eaa2c021e63335c8604c530c9cc6b16a998d1d73182548c6aabac82988638e992601502187aed2a4621051f745815390b0e320a698221179ce6115110aaae7214a22051c7454f32843872a2a498061559c6544
  | 30 => 0x21895110326b1cc42a0218e9916015031cb2a7300841055671d4e530823d3b0a4902215c5c74354021a5ae9a9a401056671d4e521022ebacc6200218b99252080108bae7b28800861e7615143cc317b2ca4a00818d552610c01087ae932a658865563944400829a38aa82a2418755163d40218bcec29a61087155410e510c23b388c0a9c859554d6114840a6ce3b22a8104e5711814248398aa2a2900418714d62901408bae730ea4a062d54588548c31caa2c0294631d9db5244010c3cc929c6210d3674d4d5108326322a4980610f5d66408430a6ce9192a2104cd73d93214828f3a4a898a618d1936154d20cacc6b08a48856671182521032731ca4108611b5d6620c010b62e830c408843e74d8d510829b3a0c5288419654e6014a41ec0c690aa010c3f7459532442ab398c128881785ca4148110caca7308a21043d76950210c30faa4c610a618e9916014c21ce2c3300a810539748c5500863d3b6a6a80438b592528c840b1ae43028621db17010d41443b0a1242a8043179cc6154a40ea2a690aa010e3564546311022f398cb20a419958a5110030ce2a2b00422061d6550c430834a31ca2a00819554d61d48408bae630aa02165963540501063b388c0a98850fdda5408010ce2a2b00a22145d7319642842733b6a890843565c0544c832cccc4b08a0a1e65525845210e2fbb2a629e438759153084108bae7328821061d5418d40c831d2a2c021861c995121540218bee6b2a408876372485500863bbb2a228a87599c75294840acae3a94a41845d7694c4004335312c1a98432b5d363c8520c3ca931c838855a73905500872ab1cc22a0430f5d26588430e18c6a9280204f171181428823b3b6a4a8861479d9544c030c3ecb2a2601843d76950510828f3a6a729e411d5c46550e20c6ac928c631870c64549300c297396a8a1261a3590434c92096ae930e618861f64151324c236b96cba1e21555c45494c20ad4e418aa010c3d74994210c2b3baa4210861539cf6454830dc2c5104208861c64d8d534421eba4ca18841a318d4250320b52e021a84905a77458121087b1bb242a80434d5c24354440a5ce4304a80862d54988300828f39ec8aa243655c65410d328bce730ea0a176374485500871ab22c229841475ce6155010a9ae430ca720e6562986544cb17322c4282631d9c465109309cceda1a4210e1d6498c524423bbaac318021955ce61951328eae3b2e8690f1453d45415022fbb2a620041475d26154c218baed29c6218e5953582320823cb80ca21e431d5c465d0e20ca8a630aa4a051e74081530821fbaac8180419354d6290020caca6b08600862d54988540c22f398ca90881539cc5454810c3ac8b18a090e9943580434421f3a4cb108611d5c460551328bcec2a2641961d6414c315032ab1ea328a858bd965448421e2a862
  | 31 => 0x6b22a519061879526390b208f4e03288498e2e6454a310c21eba0cb194218755063503308bae6328801043d7695021083172a2c429821995846154840938ed2a2601870c73951520c32731ca410021559cc6094420caac6a8c821856a721915008636b90ca21a210fdd5648c821ca8c630aa8904e576d0d210861fbb2a8284638b5886215130ec08690aa010e2f54189514c317b22a4980619558e6114810c3aa931c8318e1e5498e420422fbb2a6298831edd9501413287eecaa081105557318a511032da9cc010a819318f625491087ae8300a48861f65191300c28f3a6ca98e61665c35450f30ec6c4a8a401051c735524088335b2aa48802187151628c130caaa6b08a621669625405010e66b98c0a1241d194d2108440e8ae6292438871654547300c23ab88c0a9c858b9915214810aa8e2b12a60852d72d91540c326b1ac42a4210f5d3658ca10c5ec8312a6885c97314920442acb86a8a98431b9c86015110c3eeca9887a170e72153324c22e39ac9280219518d5150430a5ae430ca918d1c735534284237bb2a4296218d1516110330c3cedb2a8621d597390a500861fba2ca90c611bdd9521444093eecaa08698c5e76d4d525028f3ae8699281535c86094c10a38e8a9a62906c5624c4310868e3a2a721c4117dd95314f4287eeab24620847970196430868eba0a698441539ca544c931a38e6aa28610d3574d8e510832b31ac22a061879915410c30c3ca93188318e1c5418d404822ebb4a720821471d15314d10ce4c3300a819694644c530c430eb24c62984187592538c82187aeb324641061d76151314c28eba0c0a9c8317dd95314f20ec2e690aa010e1e6454c3004317322a41082117dd95314f10a5ce5aa2859861c5498c404c332b14c22a4430fdd56408410cb2a7300421061d65553318c6a6b9ec92902187552631502087cec2a28690c3d765502104333312c3aa663a650d6010f40acaea908422065b6594d40103b1baa42a80434d9d03054430c3ca831a801043e74194310863b388ca1928187153624c530a5ae021aa42066662584548c3e129a432804347dd95310f41c6acb2a66318c6e72181548c6aa39aa228a4196d955348020a3ce7b2a83a045c735954244237390caa0c618318d5250040e2886a12a21847875580434421f3acc810a619554c614ca41b8ae7b224210f0d4310d520432731cc4290211b9ca6590c10a3ae930aa61046f72595418c31ab24a3188211ddd95110030c6ca9308a61066552586200422fb9acaa0241a959121d4021c3aa9b1a421845d7319541883172a2c4200219cd965148020c9cc6b10a81861d6510d414c61f3a0ca10a61c399043548308bae732e8210655539845110237390c0a9c831b9cb65d0f10e2aa728e802045e7399741c833928ac018861475cc54d0210c3aca21e64206656
  | 32 => 0x1535cf5454810a3aeaa18878861e5498c510832c29cc010a81aa5096010b40e4aa528e8020695439845210e4fbb287a90878e5516008420ccaa5308a22064d6394a428c38a39aa928861599cb5494430e32a8a9aa010e4d6354a42103b199242a80434d1c5545052087ce832e650854d731815204326a9cc518041c39c853d0940f44a890ca010c7571995430821f3a0ca98841535cb5454c1087ae832a42185a57414d210861f3a4c329c411ddd95114432c3ac631aa80862d5458b53042aab98a4a8881a650d601484387aed2a4620861c6454d300422f39ecba0e41565c06194e4187eecaa0a2185557114f308830f2a2c6108619954961148408bce6328800864d53588531071b2a2c221e635a9d460c8520d2ac821a63886376454530083872a2a6a9021c354c4354840cd4a4b0042205557318a510830eaa4c7208418799153d48108baed2a66498c3c7458e5088716b26a519263b848560085408bce6308a48852e72181548c726b1aa5214818bd955448421e64e021aa22061c6414d30842aa38aa629a41559ce42944308bce7b2c83906366454631082cbb8a86a8887175ce6295010a74e829aa010d5671991530861f3a4c5298219358d5214841c5ac8a90600845e73189511029b3a0c4a886193d8d5250040c9cc7294822043d74194200428ebae87a00610f5d26550d21c38c9aa661184b57418520c42b2b90a8a88619358e5210010ce2c2a80a021d3571181540c28eba0c12984117dd95314c10a38e6aa6871066962580540c71caa2c02a0434b1d163548408eae332e642056471548524c2aab9ec92884187590544c930e62a8902200865653984400824f386c4a188799989510c020a38e6aa0a90851e74d4d31c430fba2c628283875516310230c6ca8b08a61061d54d8d4004392ba0a490a2117dd953908208e8eab0e648866952580410429ab88a820a618b9d85250941ec0a890aa010d557118a5390a2eb9cc32a4418b9925208430caea6b0ca6a152e7418652042a6b98a4904216a5d23248210c38eca1aa021e6562584548830e32e8698a8117dd95314f41e8aa6a8a401049e73d912190332a90c2a10210fdd563d0b40aaae1a1aa21845e7399741082b3396a3288819c14560085308beeca98638845d73195219031731aa5a00819394d6290c21ca8a6b0e6490f6151c852008386b90a7a128117dda53100108baed29c821063564544518823dbb2a0286839598e6114c20e1a8621ca41851e74d8d53042b338ea529687539cf5494810ccac5308a608751535462008274b90c098c218e5526015021d2886b088118655635445190332a92c210421395c8604c510cd4c4b00a610c6e7614d521032ab1ac22a4219698d6014c2187ce930ea09954d721525304332a92c2100218d5926114c1087ae9b1aa58852d72181540c31
  | 33 => 0x12095ae8302649066575d95210870f32a8621a438b5926214131c38c6a928020751539451004392aa242a80430f9d26194d20a3ae9314a720d5970d4e530869cba6a728043539cb5394c408beecaa6601845e73995420430fb20c6a9221a69916010c3087ae9b2c6210c3d76950210433032a429022117dd95314242e1aa9296601857375486500861e3b2a8a1221559cc5454420aa8e2a9a639075253545300c21fbb4a9190410f9d2650c4208dee4b2a632061c54587324c22ebb686282650f5d26294f108beeca986590d2d7494b42cc732b14a2200418d551610c821e32e02a28798476711815210eaa38ac0a984317dd564cc730c3ca9318a61070d5494d200830f2a4c6200219598d5114440c38c829a609054c735485244316b22a519461395ca61d0c21a3ae9318a690d657510d210878aa9a82208431e9c265d0c21c5aa8b10811861c64551300c317322c4298218dd906155120e32a8a9c200855a7308550086ab398c0a888117dda53100208e8e2b2a851865663544211031d2a2c0298431bdd95214b31a58e4aa2848854c754cb3048236392ca98221479d3534cb2193eecaa0869961c54d8543cc21fba2c7a9421c354d5250040c38a630284a063654584428c62f39ccb908810f5da5414232a58e4aa28518e39645405008696ba6a6a9021559cc6254440ad4e518aa010c767119532042aab8ec929c854b9c8619523287eeab204218537744c9511030f324a7190218b55262148308deeca90a52061c5458f41cc31a322a2980619598d6114c2087ce832c650846e72181544c6373b0a699241539cf5294810a6ae9a8ca2184d7735921044326b1cc429021479d06094c108beeca98a3214d57398742cc697396c72a043d154d2108410caaa6b0c60085987050d5010eab39ea328e851d9c46550a30e2aa8a9a200863554986400428f3a4a298e619554e61d0c218bae6302a910c5f7654c538861f3a0ca196210f9d265cc810acae428842986355458440083172a2c5a88611d9db5454420aaae7a8ca21047571994420c28eb9ca821c430fdd95410832a3ae9a9ca6106355498420042a7398c3290611b5d762504208f4e03288690e556594f419071aaa2c3a9841995952108410a3ceca9a802064e6398854082573b0a8a16411b5ca65d0430c72c8b00a29061d5458c200430eb20a698a81595cb534401087ce832c640849e74987324c61ebb2a9190439354c6250420c5cc9310a81845e7318552102acb9ea9280431d5da538c431ce6a2b0042a0636545844088236bb4a428861599d76148520acce4202a22061c5458f404c29aba464a88411b9ca650c010c6aa9308800864d6314a425068f3b0a8a1a61479d64350530c3aa8b1c840845d7614e415022f39eca10021475d02154c21c9aa6b108010565759812108636b90c029a2
  | 34 => 0x2a99955571d50430c23ab8cc9a8265c550c43544408dce4302a818c3e74d96310870eaa2c6204410f5d7644c840c72c8b00a4886946350540c438ca1886a80434d9d0629444087ae832c658862d6494a3110362992c219043359c664cc931ca8e2b18a29068c644c930c832ab1cc228285475d66310c40c9aa7b02401045e7694d324430fb24a698021d1d965348421a3ce7aa4a990c5f7654c5350b93292a3a00819398d6215031c6aa8b08a91851d7418253086d2ba0c090843c394e4354840caecb28a601852d7414b42443933a0a490a219698e6014810c9ac7294841043e7419432042f1380a8908439358e52d4440c3aa831a800849f7650f5110e1eba4c3a9261479d06094c20cceca908432064d63588548c30eb24a71884399989611503087eecaa0a810c7671996430828ebb6a821c614b9d36394810a9aeba1ca41846e7219543082ad38486a80875a1c963540218ece3328841861d64153324c28eba4a6218419c58660d4c20acce5a8ca21872554549510c32631aa4a00811b5c86054643cb2a6b00a620e3565553318c716aa4c4284634b5c86115130acce4302a21845e73d96418832731aa520861479cf54d0431c5ac8a90420861e6454e3290678382c898a214b5cb5495030c74a9300421063564544210c28eba0a621a2199588510c5208f2ed28c200862d6454a310c28fbaa8621c43535ce52ccb41c5aa9310a40843f76550530872b31ca2200610f9d06508010a3ae8302a72163b65951200828eb98c3aa2614d1c56255010e8aa528a601847b76540505070f324c629221475d06054c20e4ae8292438861e6514f425023ab8aca100219558d5190640ccaa4b08801853671d8e548cb8aaa262188430f9d3650873087ae830aa4184b574d8e21c42cb3a6a698e2117dd56390a41ccac5308a0a1c3e741815348726b1ac42a441535cc61948108eae3b2c87905d17010d31442ab39c85288818dd516195132c3aa8b00869961e5458c400822eb98ca10a811b5da5214440a3ce7aa68690c7776544518c3b0b80a290a410f1d1654c620a9ae6304a4086a542584420870eb2887a0861871516308530a9ae021aa41854e72181530424f3b686a0461175ce619502096ae9b1a438845d73d9641882ab39c8528841539cc1054810a3ce7aa2838843e74184524431ab26a210a81539cf6494830c3ae6322a71054d73d53200832cb1cc02a04387d506350120cd0cb90a408847b7654050d0e3dbb2a028685175cc62540418dce4328860845d76d4c324430eb2086282650f9d2658c810c3cc929c6590d3671d5141cc21f3a6cb194214d9c46095021a3ae6aa0861866952580210c23d380ca21841471cd5410210e1ca929ca4087155494e510838d386a821c611d9d8534c5108baed29c8210d1e7550c438438a21aa398881471cd5415
  | 35 => 0x120d8000000000211d00dd0b041003003c00d401e0190408544008004015800000020900000e00000000000000012fcf000000400000500701a400a049000020001200700000300300020008354006001000008002203900a01740321fa00100100020000000000728004009004004200100e80300522710008040030018015800004a00981b874c01205b03405b402213a00080082c2cb1047800000414e03c014800016f004809400600c9f6000400000501e000000e0ce049866c00403c00182000060110928000002008000002c1e2002000000407a00e01a0000022008000802c00605e0138250500006000116c004003000800000e01906a000401400000005de5de5130158000060001027804c0000000000044000007014813401a0015d88004048012000800403802800300a000e0a500002b4000009008000800a041000080432402105d800009802b01a0150a2c00001e00000085a500e801c00a02100001ac03200500b80200da002065006c0860000028054000000007808c006046005003c016008009806800002700a809806c02500080480080c6000023c04a046009000402a0bb6aa800800800300b804006400000080040c205006b860002a00100000200022b90000000076000005136c144000198000000000e0020060006008000063403c007000809033005707a877c0000080020000002013000800400601901b06fc000005007801001c003061802800e26a00181c80002d214d80240ba00500003540002400010000004028008015000800a11f000005000609c800c15800100300100620000a3001000000800c85a8010114000858c00603600500c00000a400200182be2b3002264407e60f000806000000500180000040400060000006003000801c00604200200128dc0000028d2800800100800e4058104044803803000100300580100370068538010002005ae3c0fa016018804447801100682cc1ec000009008c0b200500e905004e004011803829801b19f000000200004e00e010c0000258000014000030000407400300e800c00002100009dc006283000000403600000593b410408001580090720000250044bec00101600a4066017000000000600000182d800000501780000e80b462d001c04400100080a402d56600204640000110010120000009000000005800000180d401201b029800035801700780004fc001c3cc929c620864d6398b5404236baec49884187993538c5208bce7b28420861d65953328cb1daa0c0a1a61a650d6010e20a5ce430ca918c3e74197320421f3a6cb99621475cc6115130b8ce7b224210e1e5498e410870f3a2cba186187d904354630cb2c6b00a810d1e75d91434c28c38286a8087479d26194c40a5ae42a68218d1d73152438828fbb2a621881715d653484218eae230
  | 36 => 0x21819c00801f00901cc32000100880a80000070098048230006016037c0040042ca800800a00000680000040003320000034000034000401e0d00049124008002008804c00007500900a4002000000806800009a073000c01c218000003002e02000d01b8002000153807402a004000001402a24a00d807800231700600000540030000020032019003823812c02c00003e405a00d004025027e12a00c007c00200508203b400005b00281ec0a0000000037c0ac576000002805c06d00b80640000bf00a003403e14303100e400000803b056802c00005000d8012000000001800202000202800e02cf0030514000000000006c00400c0000060000bfe00f0098038031004808400001f050001801c000000000005e3f1011800000204997d0000000003002001800400101880046800e500400ac0082340730008000002028002c0020d5039010c3fa0065ad00280020d118511e801e00e0338eb0012493016001000006a009000000200000a8564034000002000c00800000d801000e0570008830372006008010c078011123804000001608c80640001d843b007c029619003803005001b00f800011c005933071c09401300284e000407900a025401a03700600000ac02c000802802c05600a8004012120008002c1a2001006803003000100c800408a0000028004004043009802c04a00000180040320000060000008025000005004a00029a002c10809600f809801a04c3af800006800f01180500f40000b8004004002f0b800002d6005005000800a00100080380440035fe0014000000000004c0ca07f048800400209700401568ce0bb467001c00402204e00204e20c10430250136003042005406600310180508f60080030184010038024800c0081b8000801857209b027807406600100305cc000010006003c31608901100280000010108010000003000000c14400f024801807803f00080280002440028000002000003003c00801900080000ae00515600040ae0bf17200840020000000008338009011009c164021000006039c02a000093022800003c850002600c0008404006008000001801c157002000003ab4e800006402000c00a005800000106e000000000200a800400c00500200141cc0e1002000803c002006801c01226004e806c008027016829457a04700f000c03200016980040340080c8aa2800e0000050004aac051001003801800000000140560020031358024015007804001800400280d000c01300205c003c00006f8888010040006006000405200f801000200714380001900060008f000800000018020006041002002005a000000811804a00f03e00000ae02f0b5013000000e006800000a000005800401403b001002c00000a0038c8801c007001800001400200013003080000a18a980a800200700240
  | 37 => 0x31202e035043007201a001907006c00000c830400c64100c806000003d1db001003a01100002ec02e007119000c0800000018004b7c01600800ac00002403f8018000014002039000a017004819016401803104a80000f11fb0f4c0600cd0240400000000009821c02a049000810c00a0f6002009800400000000f027e0090028060000085000009407e00001b58d400206c0004cac0ac029000000402a00704d000000000900d03840002b3000007c00000605a01c84dc0010008014002009000800400e01c003804404a00101a801000601d00000b809e003015804001a00601783c005e00a00180c809801701401f0004009002002c04201200d08780320010058518000000002809802400000800080180010110100000009000004800400006c808802000400680f8022010000002c00600801a010403400f11c803001400000f02340040e202c802009003400405883e2028000cf4c26e00000c0398022065005000000a320012000400a0020100004002009154801000401001c000c00a00e000800800201400d80001421bf13a801c0080190050054022000004004400403e00481d400800c000016402a00200000dc0021a7004800c0120070064d040380010000008000000019800401001b09600440020c000e00359a004104f01c40000060088040000015009185000605800b0008010004000000400006a000800c000005050095803e001066801800e07903980140320011be000001e009000012c19801600980440420ec001000400040500b00dc0d800c00e00501ea01c00b00d0024009000000c06e025000800c0040580d600241ea01f0be80042c250e00100040e800602601e000600f183801c01c0010580398002000000006c04e001015000887432b0e6001801000203e000002c012080802010c008004003048c00500080c400200d012000091200847184e80ca00402d122804a03b00400180ca00501e8030012229000020400000800080000d401c004835010e00700503fc002006000003800607e008000c20c00f00001483e8005005800400000000400100ee01000c948c02a0010e100007b60094cc001c00204000001040143f905081d4050001068810c000008022002400a008019815809205e002804800c003028809001c09900003180040000020004014002005002800001f001807c0d01a5000000002c058008002405a00d000001800600d001805400c00e00f8f0000801200188d401c00300002f038800b0120014000119000003846a030004803c006009002800005401d0028010000007000016000600c000007c02a003000800004e01000080702460000320004076000020000401818f000805004608e00880841e000200700701be000042800000003900000000100260ec80000920000048c6c0040110
  | 38 => 0x49e00000b801800c00905d800000c00600001b409600802d01144d40010060074000026001851000034b04d85dc000045006003448a01f01a81bc00c00900102fc0000150083af002a038005000806402001180040aa000000040800402100002d400400100480229b4213001005800402e00186d41d800a01200001600760000000012130012007c01a45600a000430600200101a400a002000025c00802d00080f400e0e10020038006000000000c00401c00c007498401700080080ac14200180840080080148070044aab015003c0a2002057000c00007d0a781662a00080ee003806e068025000800c00100383d8730000142800401a00600001080420000250028d5eac5000039803405b00000a401e09409c001005a005002803c00c004002810c07400210c00ac7b4001000019c
  | _ => 0
def q2K3 : Nat → Nat
  | 0 => 0x14150110a62854856008530b4283909215402190d821d54310e10c14545c46050d30d41724c431540218e1801c56210d21a1486951514c03081e879954310d21e40534856008540d42735c05148520d12735c04354440e05535096110821b22841c1215402181d87150604c530a0c8654d5250040e42534856008420a18805516010f32a61821456008530d21745c05248510a8880590434c920c49625c06214d40a188054d6010f41b22849cd2154021b2284dcd2154021c45725846114d40b42831c1215402181d87150604c930a1486552514c030d22744842154021d22745c05248510c14545c46050f30a0d821506350230a1a85d8c6050d40c19655c04310030d0a735c04354840a61819496008430e22544856008410b208458d2154021c25725846115130960875912154021a61854856008430a18805516010f31c0c545c8604c5309a1811c14250120c89645c0434c920b2284d4d2154021915811d54310e20e22544856008430a14835516115220d21745c05148520a0d82990534c540c14635c46055030a1486551514c0308d1801c56210d31b42831512154021e09435496014843b4283d51215402196187d0d2154021a148454d6114e2096287151215402181c87591530c210c14645c4534c220a15819d854cc930d23755512154021961829c64354021b05859515348421b4183dd12154021a14835516110220b0980151424c832925859d36348421a18805516010d31a0c835516215210989821c14394043c51615c06114d40e21644855014021991831c14150110e21544856008420b228418d215402181d87190534c21081d871526348530989831c142501208e1821c1644c510c0d759c86050c43a188054d6010f42d12745c04354430c0f76dc95410d32a188550d6010d10a1686d0d5150030909821c14354043d05745cc524871081c875954310e20e05544c9610c821b42839d12154021b218418d2154021f014310d2154021d41734842154021b21849cd2154021d057550c4348421a188550d6010e10c1a861c14354043991841c1314c110a18805516010d3281f87d974350030e42534856008410a0c835516210220a0c8454d620c220c45625c46214d40a19859916010c3081d87190534c220d21545c35348421f015454d219402190d821c15410f31c0c75191324c120a168590d6110130b40835d92154021a148454d610c210d41735c05148520c14645c7544c030949821c143540438c9801c96110d32e04435895110030c15755c46050c43b41831c12154021f015454d2154021c19769c35410e30c1a765c05450f30d22745c05248710c85725c46050c439618790d2154021a1a85d906050d30b238458d2154021a0c8454d6214e109c183dd12148110b098010d5210030a1483551611021091a861c14354043
  | 1 => 0xc0c535c86050540d41735c05248710a15811506350230d437554d2154021b42831912154021e41534856008410a0c86552524c030b41839052154021d21725044154021b22848c92154021a0d821506350210d05745cc5148520d12811c14354043e41634855014021e11435456014443a918010d61100309628790d215402181c87591530c220e04639495150040918805d54310d219a184dcd2148110e42534856008440a1581990534c940c88641c1324c120a15811506350220c0c635c860550309608758d2154021b218414d2154021b22841d92154021a19801954310d21d21745c05248710b43835d92154021c86725c46050c43d41731cd2154021b4183d512154021d21425c44254021a898010d6210030991811c1439404389581dd94354843a61811496008530a1683d915148440b42839052154021a0c8694d5250040e22644855014021b41831912154021895811d94394043a0c86551524c030a188550d6010d20a63854856008440e23544856008530a0e83d915248440915811c15410f32961829c74354021911811c14354043b0582151414c4319628718d2154021e41534856008440d0a745c04354830e415348560084209628714d2154021989841c1324c120e04435496110030b22848c52154021e43534856008540c147518d4150110c1475191314c1109c1821c1314c11090d821c15310f41a148454d610c220c29625c06215130945859cf6448421f025494d2154021d21741d1215402196287d0d2154021a61854856008440a0c8654e5250040b43835912154021915811c15310f42e05435496114843b118010d5110030961819ca4354021c88631c14250120d41325c43254021989821c14354043a0e86d0d5250030a63854856008430d41735c05248510a61815496008410c0c645c8534c21090d821c15410d31a188550d6010e20a618294560084309a1821c1415011088d82dd9435444381c875954310e10c0c7518d4250120962871912154021d42735c05248710c90641c1314c110e05435895114443c0d755c86050c43a1684d8d514843090d821c14354043b228414d2154021b1180151414c4318a9801c96110d42c31615c06115130a0c8454d620c210d21744842154021d05745cc5248510b20845d92154021c0c645cb544c030e0463549515004081e869d9544c030a0c85590434c920b0581151424c832e05535894110421b41831d92154021d0a821c14354043a258615121085309c1811c1324c120b21841c12154021e42634855014021e0554589310c421991811c14350130c14545c4604c930b4283dd12154021b11811c143540438b1801c56210d41951811c14354043a148654d5150040e20544856008530931811c14354043d09821c14354043b40835912154021e056454d21d4021c90631c
  | 2 => 0x83600000001e1301054040019008000a0001c1c110a8000211000140661018200c0610084040e0101c3e010ba6018010001004090180400020387802020180804050b058002c04800100001000003c018081c1c010081e090181826220b00800010010838a001804160102000040e000552007000180016008b0660a0507808b7010002e1903018000201800447f00028181213000000c008201405b41839092154021a1485590434c510a61821456008540e21544856008430961819cb4354021b4180d5153484218e1811c1644c920b21848c92154021a61819496008440a61811496008540b2184dcd2154021a0e8590d6210130b2184d4d2154021b41839d12154021915811c14354043e0464949514c030c25625c46215130c15759c46050c43a0e84d8d5248430b41831512154021c85729c46050c43e055458d21d4021961809d44348421989821c14350130b23845d92154021a458614d2108540915811c15410d32e22544856008420f015494d2154021a0c835516210210c14535c46050940c0c545c86050d30a62854856008540d42735c05248510b42831d92154021e046454a514c030929821c14354043a148654e5150040c91645c0434c510a0d829d854cc530b21841d92154021991811c14354043c0c545c86050f30a148694d5150040e21544856008410a198598d6010c40d11811c14354043919821c14354043b09821c1435404388d821d94394043a9080590434c510d42734842154021b21848c5215402181f875536348430f025454d2154021d22745c05148520e046354a5150040919811c14354043e0464549514c0308e1801c96110d21a0c86951524c030a6182945600844
  | _ => 0
def q2K2 : Nat → Nat
  | 0 => 0xda1388a018000114188064608704c53044241324402a6b0087a0c82648805516010f31c4031b0238284a024120992215435804384242322402a6b0087a14a064480590434c920a044aac8b8086992418806360870505404424232242a86b008710580640435895110030c403230238264982416019010d52584400c250324402c821a6288482648805516010d31848cc0c83826298221211912015458043cca8212ab22e021a6288640609811c14354043c80c150238286a808708998190704c93048320504c08e0a1aa021c84644805516010d32
  | _ => 0
def q2N (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 40
  | 6 => 1870
  | 5 => 10236
  | 4 => 5876
  | 3 => 335
  | 2 => 23
  | _ => 0
def q2R (k i : Nat) : Nat :=
  match k with
  | 8 => packedAt q2K8 (i*5) 5
  | 7 => packedAt q2K7 (i*16) 16
  | 6 => packedAt q2K6 (i*27) 27
  | 5 => packedAt q2K5 (i*38) 38
  | 4 => packedAt q2K4 (i*49) 49
  | 3 => packedAt q2K3 (i*60) 60
  | 2 => packedAt q2K2 (i*71) 71
  | _ => 0
def q2I (k h : Nat) : Nat :=
  match k with
  | 8 => 2*((h/1+packedAt q2K8 (5+(h % 1)*1) 1) % 1)
  | 7 => 2*((h/27+packedAt q2K7 (640+(h % 27)*6) 6) % 40)
  | 6 => 2*((h/651+packedAt q2K6 (50490+(h % 651)*11) 11) % 1870)
  | 5 => 2*((h/3412+packedAt q2K5 (388968+(h % 3412)*14) 14) % 10236)
  | 4 => 2*((h/1986+packedAt q2K4 (287924+(h % 1986)*13) 13) % 5876)
  | 3 => 2*((h/139+packedAt q2K3 (20100+(h % 139)*9) 9) % 335)
  | 2 => 2*((h/14+packedAt q2K2 (1633+(h % 14)*5) 5) % 23)
  | _ => 0
def q2Pos : Nat → Bits
  | 0 => 0xe3fe1fffc3fffc7e0e38f8fff1fff07e04f3cf
  | 1 => 0xfc1fe1e3fc3c7f8ff03f1f1c3e387f8e3b4d33
  | 2 => 0x1ffe03ffc07ff1ffc01fe03fc07ff1c38e3c
  | 3 => 0xffe00003ffff8001ffffe0003fff8001fc0fc0
  | 4 => 0xfffffffc00000001ffffffffc0000001fff000
  | _ => 0
def q2Neg : Nat → Bits
  | 0 => 0x20020000400000800000202400481000001045
  | 1 => 0x414448448890a810501909089211250c194512
  | 2 => 0x1a88848911095002a640124124824a60c28a28
  | 3 => 0x88c1d55222a819253aaa4002392703256c0f80
  | 4 => 0x131119803b326249cd349c9380040c49b7e000
  | _ => 0
def q2Atlas : Atlas := ⟨8,rawDecor 31 q2Pos q2Neg, 0xfeeaeae8feeaeae8feeaeae8feeaeae8feeaeae8feeaeae8feeaeae8feeaeae8feeaeae8feeaeae8feeaeae8feeaeae8feeaeae8feeaeae8feeaeae8feeaeae8, q2N, q2R, (fun _ _ => 0), q2I, []⟩
end PEqualNP.Outside.L_meta_36881
namespace PEqualNP.Outside.L_meta_36881
open PEqualNP.Outside.L_meta_36881.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 9 => packedAt gbK9 (i*15) 6
  | _ => 0
def gbH (k i : Nat) : Nat :=
  match k with
  | 9 => gbHint (packedAt gbK9 (i*15+6) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 9 => 2*((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 1)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x3ff83f01fc0ffff81ffff80ffc04f3cf44f3cf
  | 1 => 0xc1ffc7fe0ff0781fe0f03ff07c3b4d33bb4d33
  | 2 => 0xfe0ff8000fff801fff003fff83c38e3cc38e3c
  | 3 => 0xffffff000001fffffc00003fc0fc0fc0fc0
  | 4 => 0xfffffffffffe00000000003fff000fff000
  | 5 => 0xfff00000000000000000000003ffffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x210000010008a000114080420001045001045
  | 1 => 0x41a143620510504a20a092a058194512194512
  | 2 => 0xb40a98108aad00955a01254b01c28a28c28a28
  | 3 => 0x108cedb5a084011f9ccb80610aec0f80ec0f80
  | 4 => 0x210f36d9cfce65c1080201821377e000f7e000
  | 5 => 0x39c000e103084606108c060c63bfffff000000
  | _ => 0
def gbRaw : List Sig := (rawDecor 63 gbPos gbNeg).map Prod.fst
def gbPools : List BoundPool := [(0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333, 7, 0, gbRaw),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff, 8, 0, gbRaw),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 9, 0, gbRaw)]
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeae8eeeaeae8feeaeae8eeeaeae8feeaeae8eeeaeae8feeaeae8eeeaeae8feeaeae8eeeaeae8feeaeae8eeeaeae8feeaeae8eeeaeae8feeaeae8eeeaeae8, gbN, gbR, gbH, gbI, gbPools⟩
end PEqualNP.Outside.L_meta_36881
namespace PEqualNP.Outside.L_meta_36881
open PEqualNP.Outside.L_meta_36881.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 4 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 16 := block_range (n:=16) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 16 := bs0_3_0
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
theorem bs1_3_0 : Interval s1Atlas 3 0 84 := block_range (n:=84) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 84 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_96 : Interval s1Atlas 4 96 90 := block_range (n:=90) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 186 := (concat bs1_4_0 bs1_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 48 := block_range (n:=48) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 48 := bs1_5_0
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
theorem bs2_3_0 : Interval s2Atlas 3 0 39 := block_range (n:=39) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 39 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 24 := bs2_4_0
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
theorem bs3_2_0 : Interval s3Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 4 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 6 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 1 := bs3_4_0
theorem alls3 : ∀ k ≤ 4, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_0 : Interval s4Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 4 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 6 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 1 := bs4_4_0
theorem alls4 : ∀ k ≤ 4, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_2 i (by omega) hi
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 14 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_96 : Interval s5Atlas 3 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_192 : Interval s5Atlas 3 192 36 := block_range (n:=36) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 228 := (concat bs5_3_0 (concat bs5_3_96 bs5_3_192))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_96 : Interval s5Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_192 : Interval s5Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_288 : Interval s5Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_384 : Interval s5Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_480 : Interval s5Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_576 : Interval s5Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_672 : Interval s5Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_768 : Interval s5Atlas 4 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_864 : Interval s5Atlas 4 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_960 : Interval s5Atlas 4 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1056 : Interval s5Atlas 4 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1152 : Interval s5Atlas 4 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1248 : Interval s5Atlas 4 1248 92 := block_range (n:=92) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 1340 := (concat (concat (concat bs5_4_0 (concat bs5_4_96 bs5_4_192)) (concat (concat bs5_4_288 bs5_4_384) (concat bs5_4_480 bs5_4_576))) (concat (concat bs5_4_672 (concat bs5_4_768 bs5_4_864)) (concat (concat bs5_4_960 bs5_4_1056) (concat bs5_4_1152 bs5_4_1248))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_96 : Interval s5Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_192 : Interval s5Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_288 : Interval s5Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_384 : Interval s5Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_480 : Interval s5Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_576 : Interval s5Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_672 : Interval s5Atlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_768 : Interval s5Atlas 5 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_864 : Interval s5Atlas 5 864 26 := block_range (n:=26) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 890 := (concat (concat (concat bs5_5_0 bs5_5_96) (concat bs5_5_192 (concat bs5_5_288 bs5_5_384))) (concat (concat bs5_5_480 bs5_5_576) (concat bs5_5_672 (concat bs5_5_768 bs5_5_864))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 44 := bs5_6_0
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
theorem bq2_2_0 : Interval q2Atlas 2 0 23 := block_range (n:=23) (by decide +kernel)
theorem allq2_2 : Interval q2Atlas 2 0 23 := bq2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_3_0 : Interval q2Atlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_3_96 : Interval q2Atlas 3 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_3_192 : Interval q2Atlas 3 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_3_288 : Interval q2Atlas 3 288 47 := block_range (n:=47) (by decide +kernel)
theorem allq2_3 : Interval q2Atlas 3 0 335 := (concat (concat bq2_3_0 bq2_3_96) (concat bq2_3_192 bq2_3_288))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_0 : Interval q2Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_96 : Interval q2Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_192 : Interval q2Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_288 : Interval q2Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_384 : Interval q2Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_480 : Interval q2Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_576 : Interval q2Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_672 : Interval q2Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_768 : Interval q2Atlas 4 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_864 : Interval q2Atlas 4 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_960 : Interval q2Atlas 4 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_1056 : Interval q2Atlas 4 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_1152 : Interval q2Atlas 4 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_1248 : Interval q2Atlas 4 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_1344 : Interval q2Atlas 4 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_1440 : Interval q2Atlas 4 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_1536 : Interval q2Atlas 4 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_1632 : Interval q2Atlas 4 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_1728 : Interval q2Atlas 4 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_1824 : Interval q2Atlas 4 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_1920 : Interval q2Atlas 4 1920 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_2016 : Interval q2Atlas 4 2016 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_2112 : Interval q2Atlas 4 2112 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_2208 : Interval q2Atlas 4 2208 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_2304 : Interval q2Atlas 4 2304 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_2400 : Interval q2Atlas 4 2400 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_2496 : Interval q2Atlas 4 2496 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_2592 : Interval q2Atlas 4 2592 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_2688 : Interval q2Atlas 4 2688 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_2784 : Interval q2Atlas 4 2784 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_2880 : Interval q2Atlas 4 2880 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_2976 : Interval q2Atlas 4 2976 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_3072 : Interval q2Atlas 4 3072 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_3168 : Interval q2Atlas 4 3168 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_3264 : Interval q2Atlas 4 3264 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_3360 : Interval q2Atlas 4 3360 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_3456 : Interval q2Atlas 4 3456 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_3552 : Interval q2Atlas 4 3552 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_3648 : Interval q2Atlas 4 3648 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_3744 : Interval q2Atlas 4 3744 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_3840 : Interval q2Atlas 4 3840 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_3936 : Interval q2Atlas 4 3936 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_4032 : Interval q2Atlas 4 4032 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_4128 : Interval q2Atlas 4 4128 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_4224 : Interval q2Atlas 4 4224 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_4320 : Interval q2Atlas 4 4320 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_4416 : Interval q2Atlas 4 4416 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_4512 : Interval q2Atlas 4 4512 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_4608 : Interval q2Atlas 4 4608 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_4704 : Interval q2Atlas 4 4704 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_4800 : Interval q2Atlas 4 4800 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_4896 : Interval q2Atlas 4 4896 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_4992 : Interval q2Atlas 4 4992 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_5088 : Interval q2Atlas 4 5088 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_5184 : Interval q2Atlas 4 5184 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_5280 : Interval q2Atlas 4 5280 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_5376 : Interval q2Atlas 4 5376 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_5472 : Interval q2Atlas 4 5472 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_5568 : Interval q2Atlas 4 5568 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_5664 : Interval q2Atlas 4 5664 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_5760 : Interval q2Atlas 4 5760 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_5856 : Interval q2Atlas 4 5856 20 := block_range (n:=20) (by decide +kernel)
theorem allq2_4 : Interval q2Atlas 4 0 5876 := (concat (concat (concat (concat (concat bq2_4_0 (concat bq2_4_96 bq2_4_192)) (concat (concat bq2_4_288 bq2_4_384) (concat bq2_4_480 bq2_4_576))) (concat (concat (concat bq2_4_672 bq2_4_768) (concat bq2_4_864 bq2_4_960)) (concat (concat bq2_4_1056 bq2_4_1152) (concat bq2_4_1248 bq2_4_1344)))) (concat (concat (concat (concat bq2_4_1440 bq2_4_1536) (concat bq2_4_1632 bq2_4_1728)) (concat (concat bq2_4_1824 bq2_4_1920) (concat bq2_4_2016 bq2_4_2112))) (concat (concat (concat bq2_4_2208 bq2_4_2304) (concat bq2_4_2400 bq2_4_2496)) (concat (concat bq2_4_2592 bq2_4_2688) (concat bq2_4_2784 bq2_4_2880))))) (concat (concat (concat (concat bq2_4_2976 (concat bq2_4_3072 bq2_4_3168)) (concat (concat bq2_4_3264 bq2_4_3360) (concat bq2_4_3456 bq2_4_3552))) (concat (concat (concat bq2_4_3648 bq2_4_3744) (concat bq2_4_3840 bq2_4_3936)) (concat (concat bq2_4_4032 bq2_4_4128) (concat bq2_4_4224 bq2_4_4320)))) (concat (concat (concat (concat bq2_4_4416 bq2_4_4512) (concat bq2_4_4608 bq2_4_4704)) (concat (concat bq2_4_4800 bq2_4_4896) (concat bq2_4_4992 bq2_4_5088))) (concat (concat (concat bq2_4_5184 bq2_4_5280) (concat bq2_4_5376 bq2_4_5472)) (concat (concat bq2_4_5568 bq2_4_5664) (concat bq2_4_5760 bq2_4_5856))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_0 : Interval q2Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_96 : Interval q2Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_192 : Interval q2Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_288 : Interval q2Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_384 : Interval q2Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_480 : Interval q2Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_576 : Interval q2Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_672 : Interval q2Atlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_768 : Interval q2Atlas 5 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_864 : Interval q2Atlas 5 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_960 : Interval q2Atlas 5 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_1056 : Interval q2Atlas 5 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_1152 : Interval q2Atlas 5 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_1248 : Interval q2Atlas 5 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_1344 : Interval q2Atlas 5 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_1440 : Interval q2Atlas 5 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_1536 : Interval q2Atlas 5 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_1632 : Interval q2Atlas 5 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_1728 : Interval q2Atlas 5 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_1824 : Interval q2Atlas 5 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_1920 : Interval q2Atlas 5 1920 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_2016 : Interval q2Atlas 5 2016 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_2112 : Interval q2Atlas 5 2112 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_2208 : Interval q2Atlas 5 2208 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_2304 : Interval q2Atlas 5 2304 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_2400 : Interval q2Atlas 5 2400 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_2496 : Interval q2Atlas 5 2496 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_2592 : Interval q2Atlas 5 2592 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_2688 : Interval q2Atlas 5 2688 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_2784 : Interval q2Atlas 5 2784 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_2880 : Interval q2Atlas 5 2880 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_2976 : Interval q2Atlas 5 2976 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_3072 : Interval q2Atlas 5 3072 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_3168 : Interval q2Atlas 5 3168 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_3264 : Interval q2Atlas 5 3264 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_3360 : Interval q2Atlas 5 3360 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_3456 : Interval q2Atlas 5 3456 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_3552 : Interval q2Atlas 5 3552 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_3648 : Interval q2Atlas 5 3648 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_3744 : Interval q2Atlas 5 3744 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_3840 : Interval q2Atlas 5 3840 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_3936 : Interval q2Atlas 5 3936 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_4032 : Interval q2Atlas 5 4032 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_4128 : Interval q2Atlas 5 4128 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_4224 : Interval q2Atlas 5 4224 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_4320 : Interval q2Atlas 5 4320 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_4416 : Interval q2Atlas 5 4416 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_4512 : Interval q2Atlas 5 4512 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_4608 : Interval q2Atlas 5 4608 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_4704 : Interval q2Atlas 5 4704 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_4800 : Interval q2Atlas 5 4800 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_4896 : Interval q2Atlas 5 4896 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_4992 : Interval q2Atlas 5 4992 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_5088 : Interval q2Atlas 5 5088 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_5184 : Interval q2Atlas 5 5184 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_5280 : Interval q2Atlas 5 5280 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_5376 : Interval q2Atlas 5 5376 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_5472 : Interval q2Atlas 5 5472 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_5568 : Interval q2Atlas 5 5568 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_5664 : Interval q2Atlas 5 5664 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_5760 : Interval q2Atlas 5 5760 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_5856 : Interval q2Atlas 5 5856 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_5952 : Interval q2Atlas 5 5952 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_6048 : Interval q2Atlas 5 6048 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_6144 : Interval q2Atlas 5 6144 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_6240 : Interval q2Atlas 5 6240 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_6336 : Interval q2Atlas 5 6336 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_6432 : Interval q2Atlas 5 6432 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_6528 : Interval q2Atlas 5 6528 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_6624 : Interval q2Atlas 5 6624 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_6720 : Interval q2Atlas 5 6720 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_6816 : Interval q2Atlas 5 6816 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_6912 : Interval q2Atlas 5 6912 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_7008 : Interval q2Atlas 5 7008 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_7104 : Interval q2Atlas 5 7104 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_7200 : Interval q2Atlas 5 7200 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_7296 : Interval q2Atlas 5 7296 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_7392 : Interval q2Atlas 5 7392 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_7488 : Interval q2Atlas 5 7488 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_7584 : Interval q2Atlas 5 7584 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_7680 : Interval q2Atlas 5 7680 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_7776 : Interval q2Atlas 5 7776 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_7872 : Interval q2Atlas 5 7872 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_7968 : Interval q2Atlas 5 7968 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_8064 : Interval q2Atlas 5 8064 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_8160 : Interval q2Atlas 5 8160 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_8256 : Interval q2Atlas 5 8256 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_8352 : Interval q2Atlas 5 8352 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_8448 : Interval q2Atlas 5 8448 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_8544 : Interval q2Atlas 5 8544 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_8640 : Interval q2Atlas 5 8640 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_8736 : Interval q2Atlas 5 8736 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_8832 : Interval q2Atlas 5 8832 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_8928 : Interval q2Atlas 5 8928 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_9024 : Interval q2Atlas 5 9024 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_9120 : Interval q2Atlas 5 9120 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_9216 : Interval q2Atlas 5 9216 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_9312 : Interval q2Atlas 5 9312 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_9408 : Interval q2Atlas 5 9408 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_9504 : Interval q2Atlas 5 9504 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_9600 : Interval q2Atlas 5 9600 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_9696 : Interval q2Atlas 5 9696 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_9792 : Interval q2Atlas 5 9792 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_9888 : Interval q2Atlas 5 9888 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_9984 : Interval q2Atlas 5 9984 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_10080 : Interval q2Atlas 5 10080 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_10176 : Interval q2Atlas 5 10176 60 := block_range (n:=60) (by decide +kernel)
theorem allq2_5 : Interval q2Atlas 5 0 10236 := (concat (concat (concat (concat (concat (concat bq2_5_0 (concat bq2_5_96 bq2_5_192)) (concat bq2_5_288 (concat bq2_5_384 bq2_5_480))) (concat (concat bq2_5_576 (concat bq2_5_672 bq2_5_768)) (concat (concat bq2_5_864 bq2_5_960) (concat bq2_5_1056 bq2_5_1152)))) (concat (concat (concat bq2_5_1248 (concat bq2_5_1344 bq2_5_1440)) (concat bq2_5_1536 (concat bq2_5_1632 bq2_5_1728))) (concat (concat bq2_5_1824 (concat bq2_5_1920 bq2_5_2016)) (concat (concat bq2_5_2112 bq2_5_2208) (concat bq2_5_2304 bq2_5_2400))))) (concat (concat (concat (concat bq2_5_2496 (concat bq2_5_2592 bq2_5_2688)) (concat bq2_5_2784 (concat bq2_5_2880 bq2_5_2976))) (concat (concat bq2_5_3072 (concat bq2_5_3168 bq2_5_3264)) (concat (concat bq2_5_3360 bq2_5_3456) (concat bq2_5_3552 bq2_5_3648)))) (concat (concat (concat bq2_5_3744 (concat bq2_5_3840 bq2_5_3936)) (concat (concat bq2_5_4032 bq2_5_4128) (concat bq2_5_4224 bq2_5_4320))) (concat (concat bq2_5_4416 (concat bq2_5_4512 bq2_5_4608)) (concat (concat bq2_5_4704 bq2_5_4800) (concat bq2_5_4896 bq2_5_4992)))))) (concat (concat (concat (concat (concat bq2_5_5088 (concat bq2_5_5184 bq2_5_5280)) (concat bq2_5_5376 (concat bq2_5_5472 bq2_5_5568))) (concat (concat bq2_5_5664 (concat bq2_5_5760 bq2_5_5856)) (concat (concat bq2_5_5952 bq2_5_6048) (concat bq2_5_6144 bq2_5_6240)))) (concat (concat (concat bq2_5_6336 (concat bq2_5_6432 bq2_5_6528)) (concat (concat bq2_5_6624 bq2_5_6720) (concat bq2_5_6816 bq2_5_6912))) (concat (concat bq2_5_7008 (concat bq2_5_7104 bq2_5_7200)) (concat (concat bq2_5_7296 bq2_5_7392) (concat bq2_5_7488 bq2_5_7584))))) (concat (concat (concat (concat bq2_5_7680 (concat bq2_5_7776 bq2_5_7872)) (concat bq2_5_7968 (concat bq2_5_8064 bq2_5_8160))) (concat (concat bq2_5_8256 (concat bq2_5_8352 bq2_5_8448)) (concat (concat bq2_5_8544 bq2_5_8640) (concat bq2_5_8736 bq2_5_8832)))) (concat (concat (concat bq2_5_8928 (concat bq2_5_9024 bq2_5_9120)) (concat (concat bq2_5_9216 bq2_5_9312) (concat bq2_5_9408 bq2_5_9504))) (concat (concat bq2_5_9600 (concat bq2_5_9696 bq2_5_9792)) (concat (concat bq2_5_9888 bq2_5_9984) (concat bq2_5_10080 bq2_5_10176)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_6_0 : Interval q2Atlas 6 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_6_96 : Interval q2Atlas 6 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_6_192 : Interval q2Atlas 6 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_6_288 : Interval q2Atlas 6 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_6_384 : Interval q2Atlas 6 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_6_480 : Interval q2Atlas 6 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_6_576 : Interval q2Atlas 6 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_6_672 : Interval q2Atlas 6 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_6_768 : Interval q2Atlas 6 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_6_864 : Interval q2Atlas 6 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_6_960 : Interval q2Atlas 6 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_6_1056 : Interval q2Atlas 6 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_6_1152 : Interval q2Atlas 6 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_6_1248 : Interval q2Atlas 6 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_6_1344 : Interval q2Atlas 6 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_6_1440 : Interval q2Atlas 6 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_6_1536 : Interval q2Atlas 6 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_6_1632 : Interval q2Atlas 6 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_6_1728 : Interval q2Atlas 6 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_6_1824 : Interval q2Atlas 6 1824 46 := block_range (n:=46) (by decide +kernel)
theorem allq2_6 : Interval q2Atlas 6 0 1870 := (concat (concat (concat (concat bq2_6_0 bq2_6_96) (concat bq2_6_192 (concat bq2_6_288 bq2_6_384))) (concat (concat bq2_6_480 bq2_6_576) (concat bq2_6_672 (concat bq2_6_768 bq2_6_864)))) (concat (concat (concat bq2_6_960 bq2_6_1056) (concat bq2_6_1152 (concat bq2_6_1248 bq2_6_1344))) (concat (concat bq2_6_1440 bq2_6_1536) (concat bq2_6_1632 (concat bq2_6_1728 bq2_6_1824)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_7_0 : Interval q2Atlas 7 0 40 := block_range (n:=40) (by decide +kernel)
theorem allq2_7 : Interval q2Atlas 7 0 40 := bq2_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_8_0 : Interval q2Atlas 8 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq2_8 : Interval q2Atlas 8 0 1 := bq2_8_0
theorem allq2 : ∀ k ≤ 8, ∀ i < count q2Atlas k, checkRow q2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq2_2 i (by omega) hi
  · exact allq2_3 i (by omega) hi
  · exact allq2_4 i (by omega) hi
  · exact allq2_5 i (by omega) hi
  · exact allq2_6 i (by omega) hi
  · exact allq2_7 i (by omega) hi
  · exact allq2_8 i (by omega) hi
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
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
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 28, 60)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 28, 60)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 5 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq2 (cert : Complete q2Atlas) : Lower true (roots q2Atlas) (target q2Atlas) 9 := by
  have ready : Ready q2Atlas (asRow q2Pos) (asRow q2Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) (pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact pv
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 28, 60)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeae8eeeaeae8feeaeae8eeeaeae8feeaeae8eeeaeae8feeaeae8eeeaeae8feeaeae8eeeaeae8feeaeae8eeeaeae8feeaeae8eeeaeae8feeaeae8eeeaeae8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certq2 : Complete q2Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) (SBf 2) :=
    slice_correct (ms:=fixRows 36 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have s3 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 3 zero)) (SBf 3) :=
    slice_correct (ms:=fixRows 40 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
  have s4 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 4 zero)) (SBf 4) :=
    slice_correct (ms:=fixRows 48 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds4 certs4)
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
  have q0 : Slice true (roots gbAtlas) (target gbAtlas) (0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333 : Sig) 7 :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have q1 : Slice true (roots gbAtlas) (target gbAtlas) (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff : Sig) 8 :=
    slice_correct (ms:=fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds5 certs5)
  have q2 : Slice true (roots gbAtlas) (target gbAtlas) (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000 : Sig) 9 :=
    slice_correct (ms:=fixRows 0 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq2 certq2)
  have pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p :=
    List.forall_iff_forall_mem.1 (show List.Forall (fun p => ValidPool true (roots gbAtlas) (target gbAtlas) p) gbPools from ⟨build_valid q0 [] rfl, build_valid q1 [] rfl, build_valid q2 [] rfl⟩)
  have low := boundgb certgb allCuts pv
  have lift := lift_ok (u:=true) (ms:=fixRows 0 0) (raw:=fullRoots) (T:=fullWord) (xs:=[]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 0 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276808424 * 2 ^ 32 + 4008372968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36881.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,1]⟩,⟨.or,[1,4]⟩,⟨.and,[2,5]⟩,⟨.or,[0,4]⟩,⟨.and,[3,9]⟩,⟨.or,[6,8]⟩,⟨.and,[2,6]⟩,⟨.and,[0,7]⟩,⟨.or,[10,13]⟩,⟨.or,[12,14]⟩,⟨.and,[11,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808424 * 2 ^ 32 + 4008372968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808424 * 2 ^ 32 + 4008372968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36881

open PEqualNP.Outside.L_meta_36881 in
theorem PEqualNP.Outside.L_meta_36881 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808424 * 2 ^ 32 + 4008372968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808424 * 2 ^ 32 + 4008372968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allq2 allgb)
