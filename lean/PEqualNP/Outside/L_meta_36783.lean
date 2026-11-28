import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, children closed at the parent by
-- restriction pools (closeChild of the model), and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36783.Model
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


end PEqualNP.Outside.L_meta_36783.Model

namespace PEqualNP.Outside.L_meta_36783
open PEqualNP.Outside.L_meta_36783.Model
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

def SBf (j : Nat) : Nat := [4, 6, 8, 8, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36783

namespace PEqualNP.Outside.L_meta_36783
open PEqualNP.Outside.L_meta_36783.Model
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
  | 3 => 2*((h/1+packedAt s0K3 (5+(h % 1)*1) 1) % 1)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xfff01fffe03ffffffc07ff81ffe07ffff38e3f
  | 3 => 0xfffe01fffc03fc07ff81ffe07ff81f01cf3cc
  | 4 => 0xf000001fffffc0007fffe00007fffe001f03f0
  | 5 => 0xffffffe0000000007ffffffff80000001ffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x12108144220484901058a2a288a8a2154534d5
  | 2 => 0xa4aa528a51a9292a2e055511554455aa928a2a
  | 3 => 0x88c954d294a3b20aceac19d4467511c0d8d34c
  | 4 => 0xce8d9b1d193223b377367061879e78831f03b0
  | 5 => 0xf0e1c1e1e3c3c3c7bc79e79e418610c1fec00
  | _ => 0
def s0Atlas : Atlas := ⟨3,rawDecor 62 s0Pos s0Neg, 0xccc0ccc0ccc0c0c0ccc0ccc0ccc0c0c0ccc0ccc0ccc0c0c0ccc0ccc0ccc0c0c0ccc0ccc0ccc0c0c0ccc0ccc0ccc0c0c0ccc0ccc0ccc0c0c0ccc0ccc0ccc0c0c0, s0N, s0R, (fun _ _ => 0), s0I, []⟩
end PEqualNP.Outside.L_meta_36783
namespace PEqualNP.Outside.L_meta_36783
open PEqualNP.Outside.L_meta_36783.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x221000000ccbc40dc30ec20f610df32f621bd42be40f410de30bf42dd32ee20f521
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x1a5424878a6490e350932
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 14
  | 3 => 3
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
  | 4 => 2*((h/11+packedAt s1K4 (224+(h % 11)*4) 4) % 14)
  | 3 => 2*((h/8+packedAt s1K3 (81+(h % 8)*2) 2) % 3)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0x3f807ffe01fffc0f03f83f07ff07fe0289e7c
  | 3 => 0x3fff80fffe03fffffc003ff83ff83fff0e38f
  | 4 => 0xfc00000fffffc000fffffc0003fffc003f03f0
  | 5 => 0xfffffff000000000fffffffffc0000003ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x808504022420480014584508450842a832cb5
  | 2 => 0x595534a651d4a915782aa2b46ab46b41a8965c
  | 3 => 0xa264a52a9491b234baa0432d232d239530c30a
  | 4 => 0x3346c6cd191923a6dcf36a0843ce71063d03e0
  | 5 => 0xc387070e1e1e3c38ef3c73ce720842183ef800
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xaaaaaaa0aaa0aa00aaaaaaa0aaa0aa00aaaaaaa0aaa0aa00aaaaaaa0aaa0aa00aaaaaaa0aaa0aa00aaaaaaa0aaa0aa00aaaaaaa0aaa0aa00aaaaaaa0aaa0aa00, s1N, s1R, (fun _ _ => 0), s1I, []⟩
end PEqualNP.Outside.L_meta_36783
namespace PEqualNP.Outside.L_meta_36783
open PEqualNP.Outside.L_meta_36783.Model
def s2K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K6 : Nat → Nat
  | 0 => 0x210604000900024710004124300400240008d001fe30fd21fe43ff10fc30fe40fc31fd41fc40fc32fd43fc41ff41fe21fc43fe32ff32fd32fe20fd20fc42fd40ff42fd30fc20fc21ff30ff31fd31fd10ff40fe31fc10ff43fe41fe42ff20ff21fe10fd42
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x8617d548c3bca620fdcc631bf288437c54482f8a790cf15120bfaa4437d51083da401077d0e32bea8c21dd32cc37ea898df14a10bf280217e53086faa620fdc8410ee21e61bd540cafea9905f54b31be2a4217e544437a84215f54242dfa1085be54043ec20885f94d20bf2a2637c53c83b86598df94f20bf2a0877d54842fca9985f14132bea8c857c5050af8a898fe48020dfa1c81df5350b7aa9187d88510deaa0413f544cbbca7a07710c32de2a2417d548c6faa998df14e20dfa0c83be41102faa5a05f54910bea90837e50882fca190df54c20de2a221bf42906fca198fb50842faa88413c544cafca9995f95331bf28e857d52842faa3a15fd4d42bf2a265f421042baa710ef10c42bea90637e50ccafca710dfd4530bfaa0415c5350afca3204f95230bf29821df53442fca2084f95221bfaa265de53042faa7907948421fb88421bd43902faa010df55243bea8e81be42903bc8798dfd4e21f790843df320cbbca710f74c832bf2a6217e5190af8a810f78c932ee21c65dd430c3ec43885f14c21dfa08837d54ccaf8a9905f14532afa9a83bc42506fca6187b94810bf29e837e5410778a898df94243ef196637e53d02faa190df95230bfaa2637e51d02f8a9186fd0240ef98061fa40102f8a6a05f94c31bf2a4417c5150ff681205f94240bfa9c21bc41102fca910fdcc531bf2a243de530837ca990df94840f710841de318c2fca620fdc8521bf294637e51d0efaa118df94d21fd98461dc53506fca0214f55010bea8c413f54442e8a2905f94e40bfaa2437e508cafca5a0df54c42be29a21de43ccafaa6885f14c10de218837f534827aa9985f54332df2a461bc43906faa3205fd4931bfa8287bf41503bc8621fe500409f2a021df328cad8a4885f14d41fd982617c544cbde43907d48421dfa1083de314c6fca5a06f50040efa1a87de434cbf620885f95040faa0883ed52043f621085f94a32eea98857f54442faa3187d14520beaa0215f5350afea4a0df54840ef182617e5290efca9195f94c32beaa6617e520c6baa6107b08620beaa2617e500c6fca8085f14d21be282637c54083b864186f90541ee18c617e53c42eca2106f90e41af29c437e548c6fca621dfd5230af298217d538cafca6885f54241df21683bf42502fea8085f15231dea14837d54882fca721df14542bf28c43be540cafca12177d0e31be2a065de320c2faa8185754c42bfaa661be54cc3ee4310df54d21bea88653e54c87baa710dfd4d40f6908437d508cafaa6905b94810bfa82437e54086faa5206f50841f790a41df434c3ba6218f750e30fda0281dd314c37e87a0dfd4810be29263be54886faa1a1ef10d40dfa18813d540cb7a84a05f54a30be292217f54087bc86184f95020f7904417d540caf8a9985f54e42be29621df53483bca790dfd5310
  | 1 => 0xf54ccaf8a818df94341bea8e65f641107be61185f15220bf28c657d53c86fea0a15f94230bf2a643f510042f8a6105fd4543dfa1887dd434c6fca118f7cc631fd90441f421842fca9905f95020af298837d54482faa2217794c42f710a437c54042fea6087b88120bea88617e510837e85215fd4a10de214817d518cafaa910ef50f42be29c217e51102fca8187794e40bf288833f544827ca8197e8c030ef98863f621086faa9907754c41b7a92217c54cc6fea4985f54221ef98a617d52d07de4310df95210fba0a837e53082fea8187754f40bfaa2417d51102faa7205fd4d10bea9e85df328c6faa6085f94b31fc980617e539077c86a1df54b30eea98417d5290fda42907754c10bfa8a85dc438c6faa898fdc4010bfa9281bf544cb7ea8906f90640bf28041bd54cc3eca2105f15321bfaa2617f514837e86a0df94b10bea9021bf4350af8a910efd0e43bea9843bc4390afca5985794f21ee99463bd4310fbe879877cc930bfaa4637c505077e83a05fd4f10fd90241bf42d02faa7887e84010dfa00817c52506f8a78877cc831bfa8a65f910043b865185f14540df212855c53482fea610df94820bf28c617c5250efca2215f94843bea94437f530827aa8105fd5331bfaa065ec21082fea990fd48510ee29a215d53902faa8105f94b43bfa9e415e5310a7aa818f70c931bf28e417d52d0e7ca818ef90941f7210857d544caeaa2106f90e42bfa82657e510c2fca7107bcc932deaa4437e52906faa321d754f21bf29481bd43506faa018f714d20bf280437c5050ef8a9994f15110ee99261bd4350afca1a1f710d30bf29e85ee21883ba6418df95032be2a2437e528427ea898df55031f6990653d54c87bc8698f710c31bea9441de438c3ec6218df55110be28a617c54c42f8a9195fd5220de2a265dc5350afaa890f750c43bf280817e51906faa0215f54c40f7a1285bc41903ba8798f78ca30beaa0437d520c2bea6885f94732bea8087f521c42fea7105f94431bf2a0857d52907bc62187b8c832bfa92217d53886fca020df95031bea9e81df53506faa990d754c10ef98e61df430cbee8320ef10f40dea0e81ef328cafea2a05f14d42bea86637d5210f7c86215f54a31be2a2217e5210afca0185794c20bf280657d54902f8a090df94241f7900417d548cafca321ef90140bf284437d50d0af8a710ef95020fd100417e518c73a8621df54b10deaa0633d548c3bc6498f754e40bf29461dd43ccafaa1a0ef50b40bfa82837d50106faa7185fd4d41de216837d5090fea6218df94443eea1a65ef52442fca4885f94832bf29083bc42102f8a4a05754f40df2a0633e54cc3be65985f54730bfa8263dd300c37c87a05f14810bf28c417e5390afaa7084f15131bea9c637d53907be8721df54e20bf28865bd54042f8a8985fd5232ee18
  | 2 => 0x78040cc020980000c06000000b00026c000880c01410099d12480a0000000800030050280610c00090010401a07c0602407000580116304000000000045d088000000000400008cd00418050030144f2b4000000b1500f0000b01c13104003e4000402d1a8010280000001018160100d4fc560040022000000000000a2a40a074040182500018014090040000800020d7088750001706c0b0005f1bc1501c2003801000130000e6ccaf08c080040200c030006408400300a01380545c037f40005c00018042a44581c4101814001ef64dc90082f038120001d0280e09404000000440819c0e00c000206302803058010f8000000001c0600c540000100803154000000300c030002c00c1e05c0300c0112802004071040405c1c15c040042608402000010703004c000e80201c0e0dc180e4320000608008170030140b02805012faa0195f94043bf29c217e50d0abca7205f95130be28a41dd31cc3ee43085dd4520dfaa221be43106fea790df55241beaa6217d5490b7a8220df94830ae29a837e52086faa3a1df14930efa18635c53442fca5215f94f21aea98835e53d02bea6905f14d20bfa9287ef4290b7c86a05fd5031f690e41bf43d0af8a8186f50f41bf28e617d51c837aa990f754f21f629221bd431037c84205fd4d21bea8887bd41502fca4085f94c42bf284216d52042fea5885fd5210bea9e837e53102fca8907dd45209eaa4437
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x6520431d6315132d9544210823d64940308f994544825e6314c1097d8d544425e6315121a7191328c66f654c83297d8d528423f65508419d987548ca5d658c8308f593520431c548c9329d587540827561d4c2097996434ca3c6454d209b588530426f6254d109d584530831d5390c419758c540832f54149109798f52c423d64149308f990530829d640c6309798c530831e5350e40c754f421071d544c8319b98a524423f65504419b588540429d63104408f590514c31e5390a408fd91534425e6394642d354e520425e6394d20d954b210425d6394b10c754e43d031c548c931cb552520429c63504418f99053c863d6494b108f590530866e6214c10c754d411075453145209d584540c23e65d0d41cdd50514823f6454d2197d8d524425d6395110a718d42d023e64944219798f548865d63d52218f592534826d6295110c7550434c23f6454b318fd9151ccb1c5450d31c714c425063e64150328f592528c65e650c9319b588540c2756194d208f596540c67a6014c219d987530825e63150319718d544831c54d4d1097d8d544c69c6350842c795153c863e64d4e109718d544423d64943319d587548ca6e62d52319718d544869c6350a41c715053442e765484219ed95300c26f62551108f990504863d64141218f590538871e5494f219758e510863d64948218f590530425e639442197997434c25f63544409b189544423f6550c408f593538871e548ca30c7551310c71f5414d108f59053c825d6394720c7952530423e6414f20c7950328c23e6414d21c7d53534432e54548109718d54c831d53d04418f992524431c5414d209718d528425e6315221a7590310c25e6514d109d996214423d64d4c109758c525031c5490d328f992544c66e62148109798e534431d63952309dd85524431d5494e21c758c544c63f6454f209758c528431d54ccb3097997314c25f63547428f596540823e64145309d185534829c6350540c7151430c23f645483097d8d54482756115020d9547200829c6250c439dd95411065f63546208f593538831d54d0c318f191534863d6414d2197d95430c23d64949109bd954210a3f6454231a719131cc31d43544438fd95401023d64943328f59053c863d6590c42a758c425065c6354b419798c528431d5454c109798c515029c6150c439798f548431f5410e32c7553320cb6451485208f19153c425f63553209798c540cb1c53d0d41d914a214425e6590d31d954b100429f6050c438f992534827b6544010c754d41d029d64cc23097596530429d6490c4397d95300c31d54cc4318f590520425d6315121c7d53534823c6454732cd951510831d53d0842a758c419029c644c530cd15351482e462440108f990520423e6510d408f592530c2e460484219798f54043355454420d394d520426d62d5010
  | 1 => 0x431d5454e219d594210423d6494720c7d50534826d6294d1097195434c65d63d52109758c54c823f6550c439b98854cc71d54d0c32c754c43d03645248710d394e520423d6414a108f990528433754d45209718d540863e6415031c714e415071d5410c319e18154486766115030c755153c865d6594c20c718d540ca5d63148109b98b530431e53106408f997415025d6395210c7152434c71c53d0d429798e529069d64cc0309b189534425f654c4319798e544425d63946429bd89544c34f53149109d986534823e6494c30a7992304c31e548c6308f990524c31e5454c108f593530831c5350d42c7951538873454145209758e50d0a5e63150109798c540871e5450e308f592538825f654c831d9485500865d6590c30a759032cc63c6454910a7590320c25f654c83297d8d540871f5410e319798f54c871e540c630d314c524431e5490e308f992544827b65480208f592518ca5e63141219d1855448277654c431c754d421063e6494a319d98454cca3c64542318f993520425d63943418fd91508cb5453d45209d185544c27661951209798c54c426e62d501097594430ca3e64951329dd95210872c54d49108f99352c423f6454c2197d8d544ca9c63507409dd8553483655188420d5d4c514825e63952208f592534426e62951109758f548826f6548421c7553320c74d53548108f990540432d54548109758c54c87645248510c755253c871d544cb309ed81534865e63148109798c540831d544c8329758e520865d63d53219758c548872f54d49109758e524425e63d50208f593538431d5494c2097994534825c6550d329b994524426d65884209798e50d0b1e5494e218fd91500865e63d48108f99252c42e56288421d9d48218423c6454f20c755253043645284110a719132cc25f63540218f19152cc764518812097d954310e5e65cc9308f99250cca7661d50209758e544c23e6494720c7150324c63e6510941c750e5010e3e6494e109d98453082786054d21a7191324c31c5450f319798e52c425c63542428f992538825c63540218f596431065f63548408f191528425c63548409798e520866e6215010d594e510825c63546209758c54c431e5494c208f191534423e65151318f59352c431c5450d32c718d54cc25d63d48109e580530871d5390c4297596310c23e64d4e209e58054087565354420c754d4210a5d6314121a718d421066e6294d109b58b548c63c64542328f992520869c644c8319758e544823e65151329d597210423e6414f109718d54c431c63550319bd95200826d6215331d9584524431e5310a409e980540863d6414c20c794f439023d6590840cb150524431d5350b40c7153534826e62150308fd954210b646154810d9549100425d63145409798f540c25d63d50108f990538863c64540219b59
  | 2 => 0x4500080102823028770300301439000247815a07059000e807817274230001103c020700c0000201c0a224160f5bd010010ac77004020303000036010000940d0240106486000074a403031a70181331c000340800c3c1080f15c000110e088150a0120009c0fc000000200403048071a4c6044200b04a0e00800c17000090301f02c19224154500002c1c110350140100000044231ac0306c4505c090380a000000083d0500d2f40c028095c80043ce3008530581202087304e91381604c0f0180e0cc010088b0201801431024020443c06c06005bd0040b0000800820000000180204a5c6354440a758c42d071d5310c418f99250cc71d5454c208f592538423d65950109ed95401031c5390941a7191320ca9d63d024097594430c67661150209718d51d0a7561153329798e50d071d53d0b408f59053c431c5350d41c755043cc35753d4520c715143cca3d64944218f997425023e64940309ed81544865f6354b418f990530863d6595032a7191310c71e53d0240d9548210429d640ca308f992518ca3c6454c218fd91524431d53d07408f9974350b1c548c531cd552510832e5494810d3d4f524433654944209718d524425d65d0c318f990540823e6494d109798e548425d63d4b108f191510c23e64d4c20b9185200834c53d49108f99353c865d63150109798e51c827761551209798e524425e6315320d9d95210863e64d4e218f990530426d62d4c10c7550430ca6e65c85209d195214431d544c730a758c429026c625513097d8d5090b6551480208f992544425f63542419d586544825e63149408fd915348277615513097597430ca5e63951209718d509071e5390640d554d510825d6315021c7951530829d631084097d8d54c425f63551218fd91528425e63d52209798c54c869d63d0040c755343cc29e6390140c7953308c23d65904408fd91510c25d63952208f191518831d54cc7308fd91518829c6350940d9147214825d6394a418f59353c86776544010a7590324c65e6510d30c714e4250b1d5310c42d554e51082796584010c750d5210f1f6550c439758f540823f6454f109d984520429f6550c438f993530423c64548308f994544
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xc003c00000400000e020000001431c94354843a36e0a1ca021d147150d5110e0e3b2a899063071d9544cb3083aec2a06498c6476549100420e3b2a898e61071d9544c431a18e4aa0869851571151430c287396a821c63071d9544c832a2ce3aa087195157115143cca0ebb4a998461451c55410d30a1ae42a28798c1d76950318c20ebb4a819461435c85450c30
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 666
  | 4 => 551
  | 3 => 21
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s2K7 (i*5) 5
  | 6 => packedAt s2K6 (i*16) 16
  | 5 => packedAt s2K5 (i*27) 27
  | 4 => packedAt s2K4 (i*38) 38
  | 3 => packedAt s2K3 (i*49) 49
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 7 => 2*((h/1+packedAt s2K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/27+packedAt s2K6 (640+(h % 27)*6) 6) % 40)
  | 5 => 2*((h/257+packedAt s2K5 (17982+(h % 257)*10) 10) % 666)
  | 4 => 2*((h/183+packedAt s2K4 (20938+(h % 183)*10) 10) % 551)
  | 3 => 2*((h/21+packedAt s2K3 (1029+(h % 21)*5) 5) % 21)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffc1fffffff03ffff83ffc1fffffcf8f1ff
  | 1 => 0xf03fffe07ffc3ffc1f07fc3ffe1fc0ff473e73
  | 3 => 0xffc0ffff81ffc3ffe007ffc3ffe1ff0387cf9c
  | 4 => 0xfffffe0003fffff80003fffe0003f80fe0
  | 5 => 0xffff0000000003fffffffffc00000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x8104044410480000a5090044802254501850a5
  | 1 => 0x248a48832490612c0a42a429521482a9432652
  | 3 => 0x429291090d2206554084ca8265412a0a858b18
  | 4 => 0x6b2ce252483aab9a73d06223b9980c33e80de0
  | 5 => 0x8c30c39c71c333e39ce77330311030c3f6f000
  | _ => 0
def s2Atlas : Atlas := ⟨7,rawDecor 59 s2Pos s2Neg, 0xeeaaee88ee88aa88eeaaee88ee88aa88eeaaee88ee88aa88eeaaee88ee88aa88eeaaee88ee88aa88eeaaee88ee88aa88eeaaee88ee88aa88eeaaee88ee88aa88, s2N, s2R, (fun _ _ => 0), s2I, []⟩
end PEqualNP.Outside.L_meta_36783
namespace PEqualNP.Outside.L_meta_36783
open PEqualNP.Outside.L_meta_36783.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x640018b00009519b08001701d550496250fe20dd31fe32fc40fc30de30fd20fd41fc42bd41bc40fc41fe42fe41fc20ff41fd42ff21fe40fc32fe30fe21ff40fd10fd31fc43be40ff10fd32fc21ff31fd21df31ff32fc10fd40fe43dc30ff30fe31fc31fe10ff20fd43ff42bf41fd30ff43
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x881bd32103be8398ef90d43bf29881de540c3be62905f94c31ee988419d31102fea610df15110de29283df43cc77ca32077d4331fd98261be43902f8a2997e48210cea0e637d518cbbaa3185f94f41bf29865bf42903bca610f74c830bea9c41bd4310ebaa218774c521bfaa643fb20882f8a2a1f794c10bf29c21df53502fea49877d0b31df21c85dd42cc6bea6905f14f20af298217c53c877c822067d0430efa1c87be535077c80107714b31be2a6433c50506f8a9185fd5121df99683bd54042fca621cf55010de206615d5310afea918f754f20dea0c43dc324c77884a0df94040eea98835c53843b88798f78c630eea1a63bd21903ba62986f10010bfaa621de53c82fea8986f95310ef186417e5310bbca0185f54440df10881dc544c6faa3a1df55120dfa0c617e508827ea8905f94c20dfa0843be42d07bc84186f50f42ee196639e400c2f8a9904f94240fb98a63bd5408778a1a0ef0ca40bea9443fa20082faa9907790f31de29881bd43902fca2205f55021df20261ee4210afea710efd48409eaa063df528c2faa7905fd4142df212857d54ccafca0196f50610ef99061dc408c3dc4290df54c41ef29883dd530877a65a0df94a32bea90617d510cb7e842177cc420efa1a87fa5008778842077cc521fd98461bd32902fca118df94d21fb08221bc404427ca81977cc530dfaa2619f414c77887214f95041beaa4877d54cc6faa7185fd4143be2a263ef52442fca4205f54720af29843be50d06fca919778c932be29281de53886f8a2a1774c421be29221df540c3bc8498df15132eea1e63dc53502faa3a17754f10ef20861bd41c87baa998ef95320bf29483dd318c37e8320ef086409eaa443bf53d06f8a8985754c21ee218657d538437e85217754c42dea9e837c53086fca620df54241dea0a817d54442fca598df54b10dfa0e61df324c7be60186f90230bf28485dd4310fb883185bd4910be28a61bd521037a8310778c310de2a261dc318c37ca0a0f74c931afa9c215e53d03bca5185f15231bea8e61ef21086fca9986f10210df994817f514cafea5084f15132bf28c43de30483bca598efd0410af28461dd53d03b860087754e41bea9e21dd548c2f8a2905f94241ee2a061be52506fca9087794f10be2a6217e53c82f8a9085fd4b10de290817f54cc2fca4215f94b30bea8c85bd418c7be87186750630bf28887df52cc7be83185fd4543bf28e657d5390bd843105f54e21bf29e21f721842f8a4085f94030ae29a857f544c73a63206fd5132dea9a839f41cc7bc8298d754e41bfaa6413c54443ba63986fd0510fda0481de510c3b860885f95030df90881bc53902faa7197750a30dea948177514837e80205f95310bfa9e21de42cc77a80205f54d20aea8c61dc538437ca918f7cc421ef996635d538c77c83205fd4d10
  | 1 => 0xd5190ef8a0a14fd5110ef29061dd319037a84205f55241afa9a21be319027ca818df15332aea9821bf54442f8a788770c320de19283dd31103bc60885f946429e2a2417e5410afca418f7d4d10ee988617c53487da84216f50d42df19481be53102fea810df14e10ef98e81bf311037a82985794e41dfa98813d540cb7886205fd4520bfa98417d52cc37e8298dfd4542bf280637e54ccb7aa9986fd0720bea8c61ed21086bca618df94c21bf290417e5190efca421fb88420dfa08837e50106f8a6a0dfd5221beaa463bf41c43b88218770c310bf28c817e51d03b862186f90030eea1061f641106faa6215f54841df21881de41cc77aa0a0df94d20bf28863bd418c37ea9086fd0f41bf284617d53486faa910f754931efa90617c505077ca2205f54b41bf29c85f6310c7be86185f94a31ee29263bd511033e62206f50740fda0281bf31902faa80877d0d31ef988617f53842f8a6a16f10020faa08835f535037a86205fd5020efa08613d519037e86a1770c120fa10821bf41482faa020fb4c8329eaa6217d5210f3a82185f94332df20621dd31c837864206f94e40bf28643de308427aa9986f48440df21283f621087b8a6a15f54732ef98c63bd41087ee4290df94a30ae28263dd520c2fca1207dd0541dea16837e540cafea710774c710be2a0637d530873a8298df95132bf2a643ef21c83be87195f54b40bf28e615f5350b7887a0dfd5220bfa928774514837c81907710c30de202617e520ca7ea8994f55241beaa063df218c3be86196fd0c43dfa0e637e5390378a6a0df54221ef98881fb104437863205f94810de20c81bd325067ea908774c520de294813e548c7b887196f55320be282437e54483bc6598ef94840fba8a417d510837e8721f7d0531bf29e817d538c6faa5085f54031efa1061dd408c378a5a0d794331bf290617e50887bc611077d5131dfa08417f50506fca3a1f750931f790a41de430c2faa8105f54a20eea9461ef208837e85a0efd0f42ef200617d54842fca2085f94631bf280857f54ccb7e87205f54d10beaa243dd53887f240886f90120dfa0c817d52443ba42185f54343beaa4656c52443e843086f90541bf2a0877f525077a83987dc8410ee180415d53d03bea3187b14910af29c43df514c73880185f54032ef98863df328cb7c84207bcc932dea1481dc434c6b8a6a06f90a40ee20e637c53883ea20085f94d10beaa461df548c37e8290df54232de10881bd41043f621085fd5120be28287df31c43ee6318df54c20beaa441f940102fca820f7d0230eea0c61bc408c2f8a6886f10e40bf28043bd43d06fca721f694030ef21a63bf53507b8a5186fcc840ee19061f5310c6faa1216f0cb41dea0a217e53882f8a91977d0931bf29221be540cbba86185f55242dfa0a615c53483ba6018778ca30dfa8
  | 2 => 0xc3b88498dfd4540bf284877e529027ca9984f55231bf28e85de304c37aa910f714430df218857d50ccb7aa918df94620eea1c61bc53d07aea298ef95330bd280437e53d0bbca498dfd4d41bfa92217e510c2fca021f70ca30be2a241df310437e8390df14131ef908613c544c37e82a07d14520ef99065bc429037c64a0fb48020f790c437f54443f420087e90040bfa9a85dd540c2faa3105f94342eea1e65dd318437ea1a0f70c220efaa663dd320cbba80187b48520bf2a441ef4250afca1196f8c840bf296879d4310efea998fdd0641bea94637c54cc37e8310df54231be29263bf41883bea6a15f94630dea12837e5290bbe62886f50441ee98e43f710042fca5a0f78c931beaa065dd510c37a8298ef95021bfa8263bd41c82fca198f790630df20421df504c77ea7206f14640dfa8283be31103b88298ef50710bf2a041bd540cbf260185f54a43de20061dd504c7bc85185714d10dfa18817d521037aa3205f94720dea0863bf52507ba6218fbcca32be2a04179500873e83185fd4810ee10c617c54086fca3196f95221be282657e500437e83a07795131fa908437d54c43ba62a07794331bfaa0217d53d03be80187710b31bf29c435e5310af8a5086fd0d41aea9883dd410c3ba6310efd4541ee98c417c53503b8a6905754f209f2a621bf2190278a9086f50521bea90217d50d0778622077cca30bea8c81bd414837ca0205f94a43bfa9e437d52cc7b8a4187790c43dfa08637c54cc7b8a688774ca30af298837e54486f8a49877cc610df202817d54cc2f8a6906f4c6409f2a0213e50d077ca818f7d4430dfa8c817c54486f8a2a05f54442df20441de518c37ca8086f88640fd10221f92008378822077d4931bf29043b751506faa790ef4c440eea0a63dd31d037e8318df55321de206417d540c2fea8997788630bea9461de53d03dc43105f54021ee28663dc210c2fca898ef50731fd180617d54902fca210fb94810bf29821df308c3bca9185754f10de21a83bf40903baa898dfd4d20bf2a663dc54cc6f8a6085f95110bf2a463de310c2fea9085f94020de20621df31c83be6390e790230ef298855e500c3ee21085fd4940bea96877d510c2faa418df54740efa9a413e54086fea7906fd5120b729021dd41cc6fca22177cc540df21a83dd52cc6fca2196f550319f2a4433e54c83b8a3185f94b10af29e41ee20483be63206fd0941eea9821de30042fea498efd0440bfa8a61be53d06faa6206f50640dfa0861dc400c3be6310ef50420bfaa461bd52d06f8a8085f94343ef98c417d539077ea5205f14e21de20241de504c7bc64187b08420ee21461de314c6fca8207795331dfa1081fa20842fca790df15221bf29681be32d06f8a5886e94040de2a4217d544c6baa710ef50d41ef29c837c53082faa121d794f10f7a14857
  | 3 => 0xa802818148080582c15840000160000403800002a8000020e82a008902b0121481803800b902005804062921c0000001600030008363b82600f880380e0180000048040977604a0482202974008003b016060002e8083801a01802040000a07801bc81e8002a008000084880a0700a1600e010000e000110105e806020000000a8083e0000a0805631002020186d8062d13e00010098560095eae810090431280c008560200218c48da91c990262a0145b132010e00780001800a30222f8006a0240180600000008540402b3700e088000c46a0404e01a6204800980000011a00040001ea00070000242d2ee14800281b200244030600b2640a8280f00000800000000000ecf03e030661082400010073fa0d558108020e80c0c06608028218c025802013b4000060492a020000a028320a647006b289e070195b8400027c00802080021180a0282a3f9220d000000000100a000080101c0281a0e210028000001c4da200580601808383e803800008b44a90a08882050020580c000ed0e0020a956200761e00601812100000203206810718e4ae146150a0010013c9a00782a0004607804241663c8000e87800012026f151209eaa641bc544cadaa4087750d32ee988217d53042faa198df54a40ef98c61dc438c2faa190ef90330f6a90217e548c3bea7085f94341dea9c817e540c778a888770c210de20441ee320cafca9905f95010df296837e50842fea8185f94e41be29283bc42d07b884185fd4c10ef10861dd31442fea0995f54f42ee99663dc548c2faa7206f90010fc88021bf418437aa6204f544409f280817d544cbbe63985f94441bea8887de438c27aa810ef55310eea86637e530c3be85187714131fb90c437e52106faa7a0fe54021bf2a0437e51083bc87996f50842df294817e544c2faa520df14943df21e837f540c77886217790230ef180417f540cbbc86995fd4d21f7900417d5010a7ea8985f94641bfaa465be404433881186f14141dea8683bc51103f640905fd4d40bf294217c540cafca910efd4b41be2a061bd525073e63205fd4121be2a441bf32506faa021df54342dea0881ed21c82faa8985f54610dea0861dd218
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0xa534423c654c84097994304831d5110030c7d50534425d6395110c7150308425e63150329758f504871e54cc4109758e548825f654c832c794d439031d5310c428f195329031d54d0c328f1915384397614c640add85525074d520cb31a798c42902cd62153318f59641102cf62541318f191508c66e65c8520c7547410c26d65884208f59353c825e63d4142a798c425065d6395130a7d8d505071f544c510d554731cc32c5210110c7d06500c23f6454910d354a300425f6355110ad987325063f65507209798e510869e6010030a7d8d401031e53506219b18953442766114c20a798341cc69e6388640c7d5030842796014c218f990530831f54cc530ae18141c835b635402197597310865c6550d31d6cc5500865d63150208f99053c82cf6255131a7191320c25e6394a409798c5150a756194d20c795331cc31d5454f10e64c6501031d5494c1097195434cb2c52d05109798c53042cd62d5230c7151314431d540c010a7993300c25e6094c42c755131c825c6014d10a758c425063e6494e20a7593308c2cd6215030c794e400432c54d491097181531065d61d4d209e583548ca7b654c030c754d411069d6310640c795030c82ae6214f41c794d410435463d45208f592510cad8604c440a7592410c25f6154f40d618e500869f644cb31d598c514823e6494431a759052cc71d51cc6408f59432d069d6414630d618d500871d5454c218f996211031d6315132c755253c423e658c640ab988511025d65d0030a798e529029d63d0240e550531c42ce6214430c7153534425d6510a308f592510431c544c5209758c54c823d64949109798e51c82ba6014440d3949310431d514c4408f99053887716014520a7d8d521023d6590c42b6d81210c31e548c0108f593530871c54cc610c754d41d023d6414c21c714d435069c635004097997314823c6454321cbd535244275611502097d95424c69e6414830c7d5353442b56114f418f594329023e6494d108fd91520c2ce62d5230c7d4c408425e65105319e181544c69d64149318f592528431d53100108f99352c431f3194040d354d520431c548c932a718d52d06746155120a7992310c23c6550530c7553320cb98400c0109e983548ca756114c20ced91500865d6394642b6580218c27a6014810c7951310863d65d0431d314f52442d661148309798e510825e6394620c7951538876552c8410ae181535063e6414f10a7983418c2b66114840979835350a5d6394a4097994418c2d8604c720cb54842d06b56194d419798e51d025e6315321a758c511031d5110230c7551538866e6295110c7d53318425f6354021c7150534831f53d0610cd584548425e63150208f99052c42776154d20d5d45314c25d63145408f587544823d650c840c7553310431d53d0410c795253086776550441
  | 1 => 0xc25c6354341975875350a3e650c840ce192500865d6194c42a7181418c2d860549318f59253482786054d21a798e511029e640c6308f58654c823d6590010d514c51482ce62146308f982548c66e62150308f59352c423f6454231d654e50086b96008640a7d91320c26f6550842c7d52304825d63944409e195204431d5314c40a7d91300c23c64543328f993538829e63d43419798e548425c6354840a7593300c31d43940438f19150886d761551319758e518823e65151329798e544825e65084308f191500cb55514c420ad584521025d6510630c795153c423d61d5130a7993504c7394154021d5945310831c5490d329799442cc65f6550c438f593520423d6115130d3149314431d5310f4197996410c29e6414630a7d854310f1e540c010ad58453102ba60d48408f992524423e6494730d5d4731482ba60d0610b6d81544c6f160086108fd91500c65d6394420c7153314c25d6588430a798c52102ba60d051097d8d50d069e6314b418fd91538423e6494e10c7952530423e65151309759442cc65c6550a30a798c311025f6354910a7592528c34f528c1109758e51042ba6008440c7552530871d544c421a7592318c34d5394810d5d4f51482da60d5030c7951438c23e64d48108f997414429f6454931d3548524c75551cc4308f18154086ad62144408fd94400423e655053097d855310a3f6550421ae181211034d52cc41097d9731c829f63508408f592538431d5390310c7d4c404831d5410d3197d95310c71d5494f2097d8553c82ba60146408fd95410c65f6354b41c754d41c42d960084309758e51d0b1e53d043197197315025d63d52209718d52842b56190210ab98b50d063f6155032cdd93514831f53d0520a7983410c25e6394410ced06500863d65d0720a7593528c35551504308f996404c2ad62d43418f59053c865c6355121d3d4c524431e5390310a758f52903345110120ae980531025c63549109719542cc65d6394640cb548525069c63549419798e52442ce62150308f982540869f6350b418fd96400425e63d5221e5945311023d6115132a7d954310f1e53507108f980544423f654ca408fd95401025e6510a30e5d85311023d6595010c755331cc23e64d4e219e59610042da6014a308f992530c395414c721b6980548c31d544c621cd147414831e544c621cd547411029d6394640d5d46304826d6215030ba580218823c64540318f585540427661951208f597410866e6214c10d9185520429e640ca30e6100304823f64542328f992520825e650c1108f191508ca3e6414931d558c514823d64145208f990514c3366414520c7152304c23c6454d21b358b50cc69d6190030d5545210c25d6394720c7150534425f65cc740c754c53d075b6394021c7940400c23e6495132e5d47414c71d5494e219b58
  | 2 => 0x6394a10c795153c83c830480209758e510865d658c010a7181410c29e60cc640a798c42d069e6488630c794c40c431e53d0621c754f41c425e658c110a75924310e3e6590120c75473110277615491097996414c63d65084409758c544871d544c710d394b310423e6495130b6983314431d4194331ab98b539025d6314542b5984540c2da60144308f992510c25e6510931ab588531023c60151108f990514834f520c110a798e519029f6354b419798f540c63e650c941b6181544c71c54cc5208f982540c69c63543419d586544833751505208f994404829e63906409718d544429d648c430a798c519031e53d07109e980530863e6415032d5d44304836b2154021c7953310c6d5618c010a7990310c23e650c640a798e415065d6194f40a718d505071d53d0740b698331842ae62146408f191534823d650c4409798e51d0a3d64d4e21d3548320c25e63d501097596530871c54d4d208f99440442d661d09319798f540865d6395120a758e21902d761549318fd85540432d5454810cd545410c39a6010230c754d418866d6594810aed81211033a5494021c7152304425d6314810c7d5230443345414520c7953310869e63108409e983540872d52900109798c540423f65507309d18553483645148520a758c219023d6494732a7992528c25c6054c21d5545311031c5350d42cb549410425e6394640a798e211026d62d5230a71814310f976150630c755230c83593194021c754d410863c64540219758c514831f54cc5209798c52c425e6588630d694e500871d5310c40cb150524425c63543429759731c832f54149109ed81534869d63d43418f592530c25f63542418f59350486ad62d4e408f994404c29d611023097994420c25e65cc5309718d501063e6494a10c7151430c25e6590630a7992518c29c6050731da54a100429d6310840c715143cc69d6314840d5546410c29d6310a4097d95420c29c644c030d394a300431f54d4d20a6181410c29d631044097994218c29e6494430a7590324c71e53100108f992534829c6454b318f99432d069e6090030a799032cc63c6550520da549100425e6094c21a7191320cb54514c520c7152304823d658c440c750d5210eb56114b419798c51482b8604c4408f197414829e640c830ad584400434f52cc510c795131c423d64d4131cdd5051482bb604c4408f990540431c63550329758f520423c6454d10a7990410c23e64d4f10c7553318c63d64d4c10d3548300439a5090030c7551310c75a60940309b58854cc74c53149108f594219029e6408630d394d520426e62d5230ae983539029d63d0040a758c42d079551504309798c548871e53d0410a758e529023e65d0520ae980539025d65086309718d548432d5210840c754f411065e63153209dd95210863d6588440e6506500
  | 3 => 0xc20cb949410431e544c730c714e404423c64549109758f548865c63542219758c52c425d6394442b558454cc6ba60d4a408f59052c431c53505109758553042ad6214f41ad58440842766115332b6d81410c31d5390c42ce980548425d658c43097d8d540833464d4520b5586524c65e6394a10e9505210863e641502197d95310871f5495230e6980400c23f65504108f99353c825e6014d428f990530429d63944408f59053c823c6055032b3588510c23e6414c21c7150304431f540c110e6d81410c31f544c6109798e5190a6e62d4c108f590524c65f654c720d314a304425d6590c308fd9532d063d6510010c755030c823f61553308f181548c735514c440e5545311025e6314c21ad58753d069e63d02409718d509065d6590430c7551310439a50100309798f54c826f6254d10c794d41086ae6214c40b5584300425f6354a108f592518cb1e5350740e5d85410c25f6354221a7990210c25f654c41097594430ca3e6494732c74c6501034f5294a30a7590218c25d654c740a7584400c25e6395220a798c219025d6395210a718d429029d64905318f195325065e63d5310a7990524c74e5394810cb951520431c5390942b9189100429c6454931a798f505065e6394d20c7953318879b4194030a718d425071e544c720d3948300433551504208f993530425d650c0108f996219029c644c93197994534431c540c1208f590514c31d5415331ae580211031c539012097d95300c2796015021e5505310869c604c640a718d521023d6414e218f592510c72d5214b419d984540c23c6454b3197d8d5448395414c5109e583540871d41141319758e51d026f65484218f19153c86da6014830cd546311023d65d0730cbd4a404423d6494a3097594420c33561d52108f994311025e63d4141b3588518c23e6415031c714d414826e6514910a759350cc63d6494e208fd954310eb561d4b41ae181418426c6255131c7151434ca7b65480208fd9153442cc6254131c754d4210b595354021b6181318431f54cc510da14a20443355150640ced05500869d6488630c7d4e404432f5250510b9185200823e65d0d42a7990510c2b56194941ae18141cc29d641483097982531071f5350510b6982420c25f635432197997434c65d63d53209798c520431c54cc5109e983530865d6194f2097195315023e649462097d8d548425d6394820b6181314431d5310310ae18141443386454021c755331c829d63906409d58454ccb5a6014e10cb548521031f540c1208f597410431d53903208fd91528429d63905418f587544ca3e6015132cdd46404823e6414532c7d50438cb1d5350720ced92500865f654c7408f593504ca9f6454b31a7d8d50d07976150731a7992314c65c6550931b6983528c39761505319ed95401023e6414f218f593538825d
  | 4 => 0xfd95325067960d4c21a758c525065f658c0108fd91534865e65cc5409798c515033a6094040cbd48404431d544c73097d8d52102af6254141ae98232102d56195131d314830443365150430c7d4c404425e63d52208f997414c35451cc520c7d04504c7e3214821097587535032e5250a409d984540829d6314b41c7551530431c5350540c714f414831d539001097596530423e6494632c7d4e408429c64548308f592510869d64144309bd95200826d62d5010d9147214831d548c310c7d4d418432f52d0510a758e411027b6055121b6d81524c71d5350410a758c519029d640cb31c754c40c829e63d4a408f992510ca5e63d41218f996404423e64944218fd9741c83692154021c7d0650cc65d63150109759731d02ad62146408fd95321026c6255110a719150cc65f6354242c7d4f41442bb6054941c754f419063c6454a10c7150538429d64d4131c795331c425e65cc5109798c540c71e544c410a7191504c63d64947309758c525065c654c5208f993504ca3d6414f10975845350b986050430c7546408c31d51506308f99454442ac6254141a7983311025e63948209e98054087575314520b6983548c2ba60d4c408fd91530829e63106409718d544831d53d0720e6d81311025e6315021a7993528c31e5390320cd546211025f6354041b398b50cc71e53504418f59251882d5618c210cdd44404825e6510430c794d41c825d63d5010b398854cc71d5410f31a7983414c65d6510430c795253c823c65d0530a7d9150cc6d561d09318f592534427761551208f586540ca9e6390440cdd4541502da60086309758c548871f5414e10b6983520c35a5354021c714e405025d63d5021c7550430cb1e5494e218f992544423e6494a309dd95310c75931540218f191530825d63d4b10d314b31442af6254d418fd9152cc65c63543219798f520423e64946308f997415029d6388440c7d4e4050298604c440c7553318865f650c010a7592510c31c5350610d5545318c25f6355130cdd47414823e65086408f592520825e63d4b108f982548865d6510c30c714e408425d6315321d698353843365450441a7592210c23d650c9418f982540cb2d5210010c794f41907965150430a7d91324c69e6314440a7590328c31e548c310a7992210c29d6308440b6181210c26d6214c10ae980529034d5214b31a7592518c25d6114d20d5146304832d54948108f99254482d56114b318f195414431f544c5309798e534425f6355121c7553310863d6494420c7551320cb3954940219b988520429f6354941c7d4e539025f6354342c7151318431d5415131c7545319023e658c4409798e5110a5e654c520e6cc6501031d53d0621cb94a400423e651512097594210c23f6454332c754f410865d6588630a7590318c32d52d04108f99251c823d6414
  | 5 => 0x414829d6190230ce551500871c5450d31c795253c423d6550720c754f4210b1c548c2108f584544823f64543218f596540ca9f64548309d594210423e65505209dd95100431f5414d20d3149324c65d6510931c5545311023c645433197181538863e6414810d594531103356414520cd14640483355148440c7552300423f61553208f992510431e5454c10b3189544c69d648c531ad586400433451505208f590520434f524c5108f592518c2766194d209798253907556114e10c714f4350b1e544c4318f596540c63f64542218f59353c429f6454131b5584520c25d63d41418fd91534823f64540218f596540871f548c210cd153514831d4354443e5d45414c63e649442097181539065e63149419b98a534434e524ca30b6983510c26f654c83297596418c32e5210010a718d4210a3f645403297980534429d63d4141c714f41842f06148210c7d4f415025e6590d32a7993308c2b561cc941c714c40442da60084308f19532d063d658c640c714f415029e631494197195314429c644ca308f59541cc25d654c720c7546400c2d8604c420ae980521023d6588640c7942400c31f5410e308f590530425e658c120d5d8f51482b860549419ed95100431d5415030ae181410831e548c320c7506500c31f6550c4397d8d5010b1d54cc431b5584540c31e54cc63197982538871d51504309718d540823f6454331d5587538432c5250941cb94b410423f6454f219ed81544c63e64d41318f59251c82d5610c210add85535066e6294910c714f4144354510c120d3d4f524425f6550b3197995315033754d45209b98854cc7365150420c755331c429e6308440cb14a4044357514c5208f590534869d640c830a798f401023e650ca40ba580210825d63150218f191520c32c525051097d95428c25e6315310c7151314c25d63d5310b6980540c25d63d4142a799350cc71e53d0740c7d4d415023d6494430a758e311031e53d0421aed8153506d960908309718d5010b1e540c310d914a104429e640c931c7153538429e648c6309758e52442ac6254d41b558754cc69c6350840b558752cc69d640c430ce9835484398604c440ce951500865e65884309798e544425f6550030c795153087a840480209b98854042786055121ae58232102ba60d4440a799052cc63e6508440ae983519031f54d4e108f993504876451881209758c54c435453d4520e610030c431d5314d41a7990414c74d524c410a7181311023d64145328f181540c73551d0740d6cc650086b66114c408f181548872e5494810c5545410c25c6354b419bd89544c65c65cc520b6181410c34d52148309bd89544431c53101209b58b530425c63553219718d5090a9c6350b418f990534863e60d51328fd954210a5e631512197195420c23e64d4c21a7590210c2da60d46308
  | 6 => 0xd0000041600101800c110350020140480a038071568000e4038008ba00a024010060c40000e00c004004068210ca03c14000014000028022a86bc0000904802c098020000c00000d008054000000202dc0000000012c000020aa0c4000000020000007216c6f8008000160780a0000320007a83020a00c0780008e16c088020180140280b0420581780301002c1d801030000548190100181701100201c02800012000010420320600700c01800c009a20b01e05181842612c0d80d0040010f809000198008020860b8030060a80580880502400c0300200a0800282a1781dc0780a01604c05000018144059bf1700bc000000960000100115e0340601b004244008850ba000010c80040000080a0000b00181000099000034028188000010220084a8000000480004901e04c320000000580c0030a200000007006010088470000388800a000084068040040000881700610c2e003000000018290180340c02a006480270a30165f4068000be5741f0000000000080004801c0687a0000d01f8220001e00c8050201800180001020c1880100a0000000c01a004008140340000a8190020001281001000c020000084980080b06e0003000008001007000048000000020882901400b13a028000020022640086502e04c238020320000187e0be0600001000e0081800004a10c0582e2dc04c0b0000000dc00017000000001dc010010050070000380100707a0000081c024000ac00612c0180001c0980000426a43e0cc0000033c01c000180120000681a0026ec00063000044a080d008000000030ca010000080000040080000e6300200b0000000680d0006080080000200c01265024000018070000000c00d01c18c020000ba0580780f00e0501b00b03001c0381f002048000170120000005c008004000000000140000a0320581d0150540240083503e0040080700c0000400102c0e86180000e0040203b12c0525f6154c10a798c411029c6250c43c755153c823d6195330ae181410c31e5310320b6980518c398400c2209b58a54443c531484219b98b540425e6514d20c7547418c29f644ca30c7d5131482ba60086409798e511026d6215010971815310be02188210c794d410c65d6114d40da580524429c644cb31d594d310c739419402197d8d544ca9c6050531c7d52304c23d650c6409759731042756115030c794f41c825f6355321c715143cca3f65d0730a7d8d429031e54cc720b618131d031e53d04419718d500871d540c310d5546210c25d65d0c32c7d4e404832f5294a40c7550430c29f6350941c714c408423f6550441c7d4d
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x4b0a8005a0404c801800021008019600980005a24080068c001000400022041121a08b800606f2a0010785c18c629284a0e3151181311024c382c710881865446050430c34a6302839050d72151430c21c382ca19283c85052154021c30a6302828861951181311028ab88a8a1e6585d51610c210c1aa6b10a62050e72d52548c348a88c0a086183591520cb31a30e0aa08698d90705053144286392a821a6386950604c720c1ac6a90a5a0f1151d81410c348a08c098a21855855110030c22a2302622061151181410c286392a629a83455c6544c720a30e0a98a6a0d0e74d4a528c28ab8ca6a0e81c4547604c440a2ee2a1aa221ec0610c12008287396a729c81451d5414c510e12a4200600862552584521024d386c6a9081835516215331ca2a2302821860c64149324c748b0880180214a1c152149419c4ed90a410851a70d50438cb12a92c220021155c46550830c2ea6b08810851571151430c3822928298a21439cb5410e30c2aa6b08a62060d54588540c38828880182418358d5214840c50a4302828850c74548524c70aaa2c2180218554d6110010c90a4302628850c72550544c728a88c098881439cf5294a40930e0b1ca22061854181318430cb288018021455c65350720c62a2302821843571195321022c382ca21263261c16488430a30e0a1ca021e4552584300430631ca4a1481461c14114131a2ae32a26398614655053144349288c0a0861c4544604c440d24a230262206a0611012008388a88c0a0861645c4400c010c18c92926518618541813144306b1aa421683a4544604c440e228298aa010e1551181410c306b1aa421081255c66414931a90e0a90a498d1870550544c60e3b2a8990658558d5188440a18e6a90a4a0c9870592510c30aa88c098881855915188430a1ae42a28798e4552584520c24ab8cc6292838354d6214f41c1ac8a90a598e0d64548520c3a098a42a8043269c36454830c30a6302830860d64548320c28cba88018021855516115030
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x1006000000000010a1181950604c720e0152584400c010c1175584400c010d00521c1414c510d01525c4400c010a108058d5188440c11655c4400c010e0052504604c510a10805915188430a118194c6050720
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 48
  | 5 => 1017
  | 4 => 1345
  | 3 => 112
  | 2 => 10
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
  | 7 => 2*((h/1+packedAt s3K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/23+packedAt s3K6 (768+(h % 23)*6) 6) % 48)
  | 5 => 2*((h/346+packedAt s3K5 (27459+(h % 346)*10) 10) % 1017)
  | 4 => 2*((h/511+packedAt s3K4 (51110+(h % 511)*11) 11) % 1345)
  | 3 => 2*((h/51+packedAt s3K3 (5488+(h % 51)*7) 7) % 112)
  | 2 => 2*((h/17+packedAt s3K2 (600+(h % 17)*4) 4) % 10)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffff81ffff83f07ffff83ffc1ffc0fcf9f3f3
  | 1 => 0xf07fffe0fffffff81f07fc3ffe1fffff463c7f
  | 2 => 0xff81ffff03ffc3ffe007ffc3ffe1ff0387cf9c
  | 4 => 0x1fffffc0003fffff80003fffe0003f80fe0
  | 5 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x210c08c42890400165098044c022425818d1b1
  | 1 => 0x44109102412221280a422429121494a1422446
  | 2 => 0xa22522481a440652a084ca8265412a0a854a98
  | 4 => 0xcb59c4929076ab9cd3d06223b9980c33e80f60
  | 5 => 0xc61871ce38733e71ce77330311030c3f7b000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xeaeae8e8e8e8c8c8eaeae8e8e8e8c8c8eaeae8e8e8e8c8c8eaeae8e8e8e8c8c8eaeae8e8e8e8c8c8eaeae8e8e8e8c8c8eaeae8e8e8e8c8c8eaeae8e8e8e8c8c8, s3N, s3R, (fun _ _ => 0), s3I, []⟩
end PEqualNP.Outside.L_meta_36783
namespace PEqualNP.Outside.L_meta_36783
open PEqualNP.Outside.L_meta_36783.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x2d80410000001802000801c9001000000240082ff42ff32ff31fe31ff41fe30fd30fc43fc41ff43fd40fe42fc30fc32fc31ff20fd21ff40fc42fe32fc10fd10fd42fe21fd20fe10fe41fc20fd31fd43ff10ff21fc40ff30fd41fc21fe20fe40fd32fe43
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x2175510c2fca3105f54c20be2a4417e50886f8a9985f15310ef21e657f54487f641105f95331bf288857e54442fca0195f54d20eea1a657e50842fca7105f54342bfa8a41df43cc77e84206fd0f42be298217e5310f7ca918df14e20bea9e83dd31cc27ca918efd0a42bf280853f544c2fca3217e88210bf286877d540cbda659077cca32fd100415f53442fea2985f55120ee99065ef324cafca8107794f20bfaa061fb304c2f8a4a0efd0540be2a041de318c2fca4205f14d40ef21887ed21c83de84905f14520dfa1a857f505077aa8195f94c10eea1e65bc42d02fca1a15f94e21bf288417e53107da84995f54643bfa9e437c5250f7aa998df54321bf29c85bf41107ee6298cf15130ef29843bd548c6faa5986f10d41f7a12857d510caf8a5086f95021df21e837c505067aa918df54f40dea1081df318c6fca7207d4c510be296217f548cbbea6885fd4d20bf28481ef21886fea810fb48020bea9e436c52443b8a6a05fd5331be28a855e53087ba60187e4c030f721465bd43502f8a8085f94842be292817e500c2daa4087710d31fda04817f5350bee4290df94f41f7a16417d51c82faa120ef90e42bfa9a217e51102faa5207dc4210df212857e518c6fea498cfd5121f790041dc318c2fea9085f95232bfaa6417e528c6faa7205f14d42bf29e85df320cbba64186f10e429f2a0657c53086fea2a15f54043be2a061dd4310efca1215fd4941bea8485bf41907d88410df14d20f790a417f504cbd8a4886f15132bf28465be4350efca8195f55241bea90877e51d0b7886207e50040be29a437e52842faa8185b54b31bf2a4637e50d06f8a918df55232bea8083bf544cb7e84215f14121bfa9e217d538867aa9905f55330aea98437d5390afca310f7d0d31bf29863df300c2f8a0a15f54610bf2a0437e53086fea610df14f10f729021ee320cb7ca8185f94f40dea10855e53906f8a710cf95331bf294857d50d06fea7105f94641ef98863dd53042dea4887dc4010de20c81ed520c2faa6887d88421fd902417d518c2fea4a05f15132dea1c837c54086faa4205f14d41df21c817c548cafea99877cc830bea80855d5310bdc849977d0d43f6a9663ed52902f8a898fe48210b7290617e52d0edca5205f95131f790e41f920082faa9106fd0740be2a6637f54c86f8a4985fd5031bf29a41f641106faa4885f54f10bf2a0617f548c6faa910df94d21beaa2217c52043dca421dfd4e21bea9463ec42886fca721ef95331bf2a4217d520c6fca9995f54642be2a6417d54cc6f8a498df55240bf28e417e54486fea5887bd4910de21885ec21882faa5085f54e20de208817d53d0aeca2187d84110bea8e857d51102fca418df54420ef18a637c52442fca020fbd0a42fba0c837d5110b78a890df95010bea9883bf4390efca3a06f50540
  | 1 => 0xc544c2dca598df94432ef29c837e544c2faa8105f94a30dea1283bf43106fea7905f55321beaa043bd41106fca820df54e10b7290877d50cc67aa8185f94d10bfaa263f521086faa110df94b10bf2a6417e51d0fbe65187754f20ee99461df430c3ba6218df94441dfa0481fa40103d8a4a0df94031f7296633d540cbda6510df94821dfaa261fa100437e86a07b88620bd280437c514c37c86a0df54032dea1e857e53842fca790df54243bf28c81df314c3ea20085f54f20bea96637d53042faa420fb10b20bf2a621f5510c37a80205f95321bea9a43ed32086fca9185f54b41bf28843be41507dc6510df54e41bea9c617d5490efaa010df54c40f6a90877c514cafaa3a06f50d429f2a0617d51ccafca5206f55010bf28c87bc43d06fca7904fd5132f7a1043df308c2f8a2a05fd5221beaa6217f514caf8a7905f54b40bfa8263dd32cc6fea9185f14f21f6a1085fa300c2fca910db54830bfa9c217e5010efca5985f94a32fb98c637f524437c84a05f94241bf2a0817d544877ca8197ecc230deaa0437f5150efca010cf55220f7a92833c544cbf4a010dfd4930bf290617d52906bea6a05b14941ef18861be431037c8420efd0a40bf29483f5310c77884a05f54a43f7994657e5448278a8887b48421faa0883ee204827ca8087d4c710dea18877d528837a85205f14543bfa82857e530c3f240886f15110fb18a217d500c7dc65907794c109f2a4417d5110efaa118df94040bea98437c504cadaa5205f943219eaa043f9500877e8720df94431bfa9a437e52042bca6215f94841f7192413f54443be63985f550319e2a2437d52887be6598dfd4540bf290417c53843f680a07bc8220f610841de434cb7a83a05f14131bfa98417e50882faa918ef90140ee21c617c54c86b8a6885f14143de214837e508c2daa421df95031de21c817f54883b88798cf55010bfaa2617e52cc6fea090ef10841bf284637d518cafea6a05f15130bf298657f540cbb862186f90440bea9687dd314c2faa5185f94243bf286657e5410a7ca810fd94430be298417e5290edea4a0df94632bf29e21dd539077ea8885f94b40fba0a837d52c437e87a06f90a41aea9e417e50042fea5085714d40df218857e5210e7ca9905f54343f6990657c540c7da85195fd4d41beaa4857e510c2faa8986f55030efa1c617f54483dca4186fd5121bf2a265bd54c83ec6218ef90b40ee29a217e51042fca198f78c932dfa1283df324c7bea6a0774c931bfaa0217c540cafea4a1df94c42bfaa6217d520c2fea6085794c10fd882217e5410f7aa9106f50c41f721085de5310bbe8721efd0c43f690a41ef21086faa9905f54232dfa0081ee21082fea8107b4c9209eaa663ef42886faa3a1df15332bf29683dd530877ca9107b54810be29a217e518c3ee4310df54620fc88
  | 2 => 0x528000c81529c994a01e03c75018011542e038070c5350000e1505b09c257000601c010ac03000000ec400180a0d8d42e82504ca001c4e07402000133440c010042603b0040609c301540003c520c41766405028e0008220000201c020d4c70e807454380000900cc705400030004e00100004028011400207c1e004050001f108020000100004298110802c000055000b0001c075c262c0f00034044001a4000083301000004211281c49807000280400004c0f02800000112e824000000000c4380a01dfb0d800000030b002000130ec34018001701e2f00b0282f060780fc15064010480f0e001018200380e01000494991dc0b67400108080a0100d0090182701c1a004030680300c0002805010030040003803028001f80429c1cbfa9021fa20442f8a8885fd5110bf29841be41902faa2187b8c821be2a443bd43d03baa6215f54332bf29c837e54882faa3985f54810bea8c817d54842dca4087b10920bfaa2657d544c6fca0105754c10ee218617e5110efca4885f54c42beaa021bf42d07bc60985f94732beaa265fb10842f8a890df54e32aea9c837e51cc2fea9995e54021be2a461bd42d06f8a9085f15120fb18e217e53103dc4290df55332bea9c637f5050f7ca8087b94a40df2a6417e520cafca9985f55230af29e41b
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x3540866f65480208f990534834c53d4910c754f4210a3d64d4f20da8c950086776154d208f994544cb2e5290640ba580218825d63d50108f994425025c63552108f191534872c54d49109b58a539071d63151328f990540c25e63153219758f54c429c644c8308fd91518ca6d62153308fd91534863d6494d109798e524423d6414d20ab588431023e64d4a108f59643102ae62901408f592520823e6414931c754c4310a3f6454b30ab19132c827865481109e580530871c5310940b3588438c23f64549108f596540863c6454f219e980540c66d658c8219798f54c425c6550d32a798e411023e64d4e209b189544423e65151219798e529026e62141318f99353c427561d53328f191510823e649423297d8d544431c5490d329d185544831c53505408f990530863e6510d419b588504c65c63540418fd9150cca3d64145209798c525066d6214e109b98a53c432c54909329d984540c26e6294e418f191534825e6314c219758c514823d65904409e580540863e6414c20d354d520425d6314b10ab5884310a3d65908419758e51d0b2c5488521a7992310c23e64951109b988535026e6294910d3d4c524425f63551209798e53442776544010cb50d5210e6f62547439b189511031d5454f20ab191214823f6454831ab18941d031e5454c10d394d320874d6394a408fd91534423c64548319b588530426c6254d109bd89544c65f6355130c714e425026e62d4c109b98b548c26c654c9209b58a50d0e5f6354221d5546310c23d6494f109b58b548c29c644ca30cb952218831c54d4d109d587540c25f654c0308f990504c63d6414e209759653086ae6488120d354e520434e6214d40cd552510c29e6390640ab189411065d6594c108f990520432e4394a4097d8d501065d63951109ed81544c63d64d4c1097594430c26c62546308fd91510832d6215132a758c429063e6515110c714f415034e534cb209b58a53c436952440108fd91534834d6294e419bd89544863d6414c21ab5884390a77654c4319798c540827a6014c21cb18954c823e6414e10ab588435071d54ccb31c7551320c34e5354810d398a53c826e65149108f19150cca5e6314c10a7191300c23f6454630a7992318c27960d50219b98a544434e6294e419b98a50d071f54d4d10d5cc9510c2ac6448720c794f439067661d5030ab191320866e6214c20c714f435031e5494c10d398c525072e54548108f191500c66d62153319b195424cb3a54540218f99250c87665254430b358c428863d6494a10d394932cc66d65948109798e544432c52509419798e520826d6214d40ab58843d072c4314941c7153314c23d6414c108f992530c66e6215330b3588434c65e6394a10cb952520427b6054d219b98a534423d6414c208f592530c66e65d0920cd952510c2786055131
  | 1 => 0xcb5953940218f990538836852881109bd8954442756115020cb552520426d621503097994534432d54548109d58453083684254021cb94b429025e63150109ed95200831c6355331d350d5210f1e5454c219e583530871c5390140d358c52506ac64484219d584540c2766114c20d54c9510c23d6414f218f59353c423e6494a308f191524432d548c821b358c42c823c6454e108f593538823d65950329bd89534431d544cb319758e524426c62553108f99251cca3d6494431cb950218825f63543429d984540832d54548308f592528c23d65950109798c540872e54548309758c520426e62d5020d398a530871d54d0c30a7992314c63d6414f20d390d5210f6960149109798c54c82ad6210e408f997435023c64546328fd91538426f62546309718d544827a60148108f990514836952840108f992520823d6414810d3949320c25e63150328f992544865d6315010a798e415071e5390a41cb55342c823f6550840d554f100432d54d0821c718d540c23f6454b10a758c42d034d6214d408f590504c76b42540219e980540863e6494910ab191324823e6494d10d5547300c32c4394a40d354d4210a3e64150219bd9521086e8604c9209b18951d0e7761551209718d5244354538c5108fd9153c874c5314910ab191328871d5494c219b58a534426e62150328f191530823c6454d10d694d500863d64d48109798f540c63e6414c108f191518c26d6294341c794d439065c6354221c7150534426d62d50309758c54c869d631084197596310c26e6215031b358843cc71e53d0641da485500863e64d4f20d5544310c26c6255131cb150524436652944309b98b540c32d5454b31cb189540865f6354910c755343cc6ac62505408f99053c823e64940208f994544c2cd6210c308f59251cc25e63d52218f592524426e6214e109b988540c2cd63108219bd954210a3e6495130cbd0d5210f1d544c832cb55252cc71f5414d10c755253c823c6454b10cbd50524432d54948308f993520425d6394a408f992538872d544c8219b58b540431d54cc8309d984530435953540219b98b54cc7365454430cb95252cc7355454430cb55132c826d62150318f993530863e6494f109b988530425e63d5320da4c9500865e63d48109b58a534865f63552108f5964310a3d64d4c21c7953318c63e64d4c109b58a544431e5454f208f191508871c544c530cb90c525065d6315021cbd53524426e6215331d9549510c32e5494830d5d0d510c25c63551108f993538863d64942329d185534823d6494e219dd95210867b65500409758e51d023e65d0941c7551530866e62d52109798c520425e6314b109798e51d038e43909328f19152cc26d62d4c109b98b540431d5350842ce95250087556114d10ce552500872d548cb20a719132cc63d64149319e98
  | 2 => 0xbc0701427004270200000c2e10c0002c5301804108050a4380080b30c0e07c000140007c2e0000002c0a000090001b1b80400c03324270013f0004d08c00054180780300c0000403008050043701839000070141405c8c008470584c0440d270000a0000cc000040101c2100807000060000e1640007c000040009c4a17c3e02c3e3e80201808000391d00d0442004c660840b008b40302d018010483e00013758090547305c8345000114000341c000080941704492050100181d0208807c22088bb09c00158a80180814c1c00c0003000068080ac320100d0281200c051623d64d4e219e983548cb4d53908429bd8954c423e6414f219d98754cca3f64540318fd954310e3f65504419e580540c72e54c822097d95320ca5e63d50219d195314432c52d0941c7553320ca3f655084297d95310c71d5454c10a758c425034e5394810cb94b409023e64150109d584538832d548c832c714d435034f53d4910b5185324c65d63d5021dac85500867b654c030b358c424827765504419758e52843395454021cb948419025e65d0d319758c54c82786054d219b997214823f6550c418f59251ccb5a5394021d5545300c26d65108219758c540823d64943218f593528436552944309b98a50d0e6f62544409b588540425e65cc5309b58b548423e64951328f992534866f654c832d398e529025e63d5010cb14a415067965840109e983530863e65d0d429758f520423d6494d219b58b54cc71d5390c428f596540c23e6494431cb95152cc63f64542219798e51d0b8d43509328f590538432d544c832c7152304c25d6394820c795253c835443544308f99251cc25e6314520a718d401026e62150109758f54c823e6414b109718d50d0a7b65440109b596210825d631494197d954310e3d6414b10c7952530866e62148108f997415032e5250a40c794c429069c644c9319d98453882e960084208fd91530831d5494c108fd95401023e6494a109758f548863e64150328f592500835553440109e583548
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x200080402d4000300001600004000018314c6250540c54a8b004310514744c9510c20e3b2a8996634a1d13254021c18a731480a050d7214d4350286b90c6aa663435cc6255021a1ae431aa81841c76551320c30a322a2980614a1d12154021a1ae629284a0d0d7318954c82163b2a89904385991518c430c1cc629482a0d0d73949429030731ca520c81515c84354430a1ae529a8720d49731095008706b1ac42a2650b1d9544cb20
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x80d8798c529054180d8798e529064080d8714c625054080d8714e6290140
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 664
  | 4 => 539
  | 3 => 25
  | 2 => 4
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
  | 6 => 2*((h/27+packedAt s4K6 (640+(h % 27)*6) 6) % 40)
  | 5 => 2*((h/228+packedAt s4K5 (17928+(h % 228)*10) 10) % 664)
  | 4 => 2*((h/179+packedAt s4K4 (20482+(h % 179)*10) 10) % 539)
  | 3 => 2*((h/29+packedAt s4K3 (1225+(h % 29)*5) 5) % 25)
  | 2 => 2*((h/1+packedAt s4K2 (240+(h % 1)*2) 2) % 4)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x81fff83ffffe1e0ff87f87fe1fffe07d19f3f3
  | 1 => 0xfe1fffc1f87ffff07f87f87fe1c0fffee63c9f
  | 2 => 0xffe0fffe007fe3ff8007ff8ffe00ff8307cf1c
  | 3 => 0xffffff8003fffff8000fffff0003f80fe0
  | 5 => 0xffff0000000003fffffffff000000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xa402088850102002900980920252212808d131
  | 1 => 0x884110480a400502882082420844a50622486
  | 2 => 0x144aa290354906a58444d50b540a950b054b18
  | 3 => 0x5954c425240d4b394d50440d992c0613b00ec0
  | 5 => 0x61988739c67193ce7667664110301863dfb000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xeee8eee8eac8eac8eee8eee8eac8eac8eee8eee8eac8eac8eee8eee8eac8eac8eee8eee8eac8eac8eee8eee8eac8eac8eee8eee8eac8eac8eee8eee8eac8eac8, s4N, s4R, (fun _ _ => 0), s4I, []⟩
end PEqualNP.Outside.L_meta_36783
namespace PEqualNP.Outside.L_meta_36783
open PEqualNP.Outside.L_meta_36783.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x3031000400404c000b1ce09e0040801c0543200fc42fe10fc41fc20fd31fd32ff30ff21ff10fc40fc32ff31fe20fc43fc31fc21fe30ff42fd30fe31fc30fd43fe43ff43fe42ff32fd40fe21fd42ff40ff20ff41fd21fe40fe32fe41fc10fd10fd41fd20
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x4217d5090afca0105f94021f7904417d5290ef8a6a17b948109f2a641bc41103f640907b88521bf28665f7314c77aa918df54d21dea188775510c3be8721efd0740be296217f548cafaa7205f54b43bfaa643ec2108278a890df15310ee99065f631c42faa520fe4c030dfa1a815d53042fea2907e84010ef99461be411037a87a15f55220eea9e417c53483dc65905f55241bf288817d53106fca3a1df94f41deaa065bc42d02faa9995f15221ee18c617e544c6fea890df14f10bfa8a857e520cb7c8520f70c4309e2a2657e508c7be64186fd0e43dfa1a857e5290afaa3107d54430beaa6617e541077e8621df94e219faa265bd54882fca7215f54430bf29843bd41502fca6216fd5130bea9c21ec42c83de4210cf95032bfaa021be42106faa1a15f54341beaa263de304c2fca7905f54042bf298417e50d067aa918df14d21bf286856d52cc6fca7887d90441bfa82857d5110efaa8195f94b43be28a65ed32c82f8a8987b88420bf28c417d510cbba60185fd4f21bf2a443bf415037e87a15f54a309faa2217d54043bca6216f15121bfaa641ef21886fca018df55132bea8c657e54082fea8195f55240bf28483de53042faa6215794e41df21a83be54087da64195f54321bf2a4637d53c82f8a6a07d8c510dfa00817d5190afca621dfd4f10bf288637c530837ea8885f948419eaa6637d520c3be6498df14c109eaa6417e52cc2fea4885f15031bfaa043df438c3daa4085f54a20ee988637e52042f8a0a1db94b31dea12837e544c37c87a0df54221be292217d5490a7ca810ef95331ef21a657c54c86faa2215f94830be29c43df430c2fca2085f94240de20c817d54c86f4a010f754c42be2a6657c53c83f440885f54742bfa94217e508cb7a85a0df14121af29885be548c6fca721df54243fca0081bc43506faa3997e94021bf2a061bc42502fca9195f14520ee98a617c54cc2fea8107b88120bf2a2657f54ccafea498df14810df20c81be4310afca790df95010bea8063bc43d06faa3a05fd5231bea96817f544c2fea2a1efd0941bf280877c540c3ee21086f90c40b7a92837d500877a84216f90b40ee29a81f521086fea6087bd0b20fda04817e500c2dca5205fd4d41be2a4637f504cbdc64905f94630bf2a0857f53842fca310fb50a32bea94817e5290efca421fbd0942bea9843fb308c2fca02177cc230bf294837e52d03baa6087d50441ef21887f621086fca6905f94443bf298837c5150afaa8885f94720bfa9287bf42d06fca9985794f20f6992417d51842f8a098ef10c42bea9683f531c42baa7906f50040bf28461dd53906faa4885f94842bea8083ec21882fca0195f14132efa1a63bc43102fca818fe88210f6212417e54c42bca610f794c21ef98061dd320c27aa8197750f32fba0c835d5310afaa118cfd5121
  | 1 => 0xe42503f2a010df94640fb08221ee52902fca6205f94910bfa9a21de318c37a8720df94d21beaa2617d52103dc43105f94040fa98a2176510c37c872177d4d40f699043de310c2f8a498df55120bea8065be54c82f8a4987b10821bca8043df314c3ee6318fb8ca21bf28021ec525077e84205f94343bea9c635d53086fca890df54331ee98e617f544c6fca1214f95010be2a641be4250bde40107710e309f2a0617c54082fea9885f54c20ee992637e53043be64195f94220ee218617c54442daa4187754c21fb288617e51d02fea098df54241f721265ef42482fea9087b908429faa261ed52cc6fca7205fd4d20bf28c637e510c2dea4886f10e42dfa18837c52843f241085b94830be28a617e52102d8a4887dd0541fd884217d508cadca4087d44010beaa243df43cc77c80a05f95321bfa9021ed520c3f480205f94243bea9e217f534877ca8187b14910bf29e817f52503f240105f54f41bf290437c54042fca5a0fe8c030f790e41be43902fca9907b4ca21bea9c83ec42886fca1085f54831dea1e817e51ccb7aa998df15131be29287bf4290af8a9195f94a30f7a9221bd42902fea2987dc8521bf29e85df328cbbc6298df54b31df2a065ee52cc6faa3a1d7d4d40bf298657d52c42faa8105f94432f7290617f5050ef8a890fdc8621f690a413e54cc6f8a0a0ef50441bfaa2653e54882fca2105f15230ae29a217d5390afea8185f947429eaa0617e520c7de8410dfd5221de21c817c53882fca320db54a40fd90441dc434c7f660985f15132beaa4877e548437aa99057d4d10bea98217d5010fdca421df55230bfa9e417d53d02fca220df94642bf2a6657f54cc77e8220df54420deaa0217e540cb7c82a0f790f32bf298637d50ccbba86997714d10bf296637e53443de85215f54e30bf29421bf41906faa918df54a31be2a0437d53102faa818f7d4d10ef98e617c525037aa8185f94b10dfa1481ef324cb7e87a05f546439eaa043bd54086faa719778c932dfaa2657c54883788420dfd5110bf2a461ee320cad8a4a0df54841bf2a221bc42907ba6598dfd5220bf28083ed21086fea4985f14543af298217d51cc3de65196f15132f6900417d51902f8a998df14f21f7a14437f54cc37a86a05f94a31fa98863bc544c2faa5987b54843b6a90217d54c42fca4105f55320bf28c657d548cafaa998cf15110bea86877e51cc2fea4a0df14142fda0281be4350efca821df95021be28a817d53c86faa7105f14d41bea9c437f51502fca5205fd5230bf298617f54482fea090df94e41de2a221f910042faa2206f95010b7290875d53906faa6905fd4141bf28643de53c83b88798ef50d42bfa9c417c53086fea710fb54a40eea18877e528cb7a83a05fd4c20f7a92836d5210efaa7a15f95040ef98c637e5110bde42905f94e20bea9
  | 2 => 0x5f00c04010020100400c0114c0802402004000000b010310140000402030000201d0003d0380000c110140502434070110040109c0a00848000210540d0502600802004080081a01814018000000908403000340e0010002b0000700800000000000401c200000402c001e003020010181b0152102c060000d2d80001c00028000a40002c040300c1040005c070040200c0d034000000c158cc00c000002a044050782f00800000a108043000000180005c0501012004011c0e3008bd0101c0003e04020008002840505c000081200400000070001a038130040301c37098070382d02004004001b000000021840a068002240e0080504c0006c0302810054020040e1340e01400000060340000c020c000184030080d0001b0fc670000c030000d4a0000021004c0100a00009014e20181b00077008020580c02c11030190040e02800000110081a00c0100c820001a03c0102c000d81700002bf2a441be54883da84995f953319e2a261ed21c82faa9087b50842beaa0617d52886faa6886fd08429eaa0217d518c3f24088774ca30dfa0481bd421027aa9107e88020bf288437e53843bca720df54843bfa9a817d52042f8a8907b8c821bea8e41bf439067ca918df14941dea18837f52c42f8a6887b90a32fd882217c54842fea29977cc431bfa9843df32cc6fca110dfd4d42fb880217c53842fca321df95120ae29a81bf54486fea818fd8c431efa1a877c540cafaa910df55021bf28663b
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x5210863d64d4e21ba580210823c6454b109b98a54442ae62901409718d544825f6550c439d185544826c625463097d95310c72e54948108fd9153c863f6550040cb55232c831f5414d109bd89544425d63d5221d354d4210b5553c40109718d544423d659044097d95320ca3e65151328f990540c2ac644c821cd951510c25d63d5310b5185324c63c6454c209718d508872c6255021c7152304c26d6294d21d5d0d510c32d548c8329bd95320caac644cb208f992544c27a60148109ed95401023c6454d109b988540c65f6355210ce552500865e63145209bd8951d0f1c53d0540b358c42c833554944308f191510829c644c8308f99251cc35953940218f992544426e6294d10c7553320ca3d6590c409b988535032e4394a409e181534863e6414e1097994534426d6294f108f993538832f54d49109d98754ccaac6448520c7952530863f6550c41c7552530432e54086208f19153c865d63d5320cb95252cc67a6015031cb552320871c6355030ab588435067661d5030dac8550087685288110d358a539065c6354041d354e4210a5e6315010d3d4c524423d6494d21cb150524425e63d50319b18951d0e6e6215032cbd0d5210f2c5250941c7951530423e6414810c7552530865f63551109e980530866e62d4c109798c53086766115020cb10c525072d43548439b98a50d0f5732544309dd95310c66d629434397997314c31c54cc530ab5884310a6f65480208f59250c863d64d4c21cb14b425066c654c920cb152424ca3c6454e10cb94b409026e6215010d9549510c32e5454b319798f54086ad6210e428f596540426f6254d10b358c424823e6414b108f99251cca3d6494732d354d520423f6454332c7152434ca756114e20c714d435032e54c82209b58854cc71d54d0f31cb14a415066f62551319b98a539065f63542218fd954210a5e63d53209b588540431c535054097d8d5448355514c030c714f435036652944308f19150cca3e6415032ab189411072d5454b31c7150534434e534c8219798e51d025f6355130c7553430c23e64951219758c54c865e63d52218f593538834d53948108fd91534871d63151329b98b540c2ac644c9208f596540871e53d0641c755153086796014c21a7992314c63e6510d4197596310c2776154d20ab191328865e63150328f993530863d6494820c714e425032d5494b319b58b548c26e62d5020cb152214863f64540319d984530827a60150218f990530425d6315021cb153524425e6314c10a718d401025c6550d328f990540863d6595032a719132cc65e6314810d3d4f524423d6414f21dad09500865f654c0308f19152cc23e65151308f59353c431e5454c218f993520423e64d4f208fd91520c63e64d4a108f596421067561d5030c7553320c26e6214c108f59251cc2ae6488120
  | 1 => 0xc63f6454b309798e524426f62546309758e529026e65c85208f992530c74e43548439e983530863f64549108f997435026f6254440a758c42107695244010d394d520426f65484219b58b530426c62551319b98b548426d62d5010c7d53534436552944309d984538823f6550c43cb10e529031c544c5308f990534826e65149108f9974350a786055131cd551510c2776550441ab18941d031d53508428f592510c63d65950308f5964310a7960d52328f592530c63e64150108f59253886ad6210e40ba181324823d64141318fd91518c26e6215331c714c425034e534cb209758e51d0a3c6454910ce951500865e6395110d398a53086756114c209758f540863e6494f10d694e500871e5494f20d394e520434d6394a408f590514826d65948109b588504c63d6414e20cb94b429023e64d4c10c755153c823d6414f209b58a50d063d6414e109b98b548c31d544c830a798e419029d6310a419b98854cc25d6315010c7551530436952840108f19150886746154d209758e544426c62553109798c54c823c6454d209b588538431c5390140d5547300c38e43909329718d548423e6414f21cb55342c827a60d5232d314f524425e63150209b98b54cc63e64943218f992510c69d63109409b58b548429e648c6309e583530863e6494a309ed95200829e63904409758e52842cd6310821cb951520c25e65d0d318f191500c63f65508408f992524426e62148109d984540c2cd6210e308f994544425d6314941b3588434c65f63549109798c525063f6454b108f992534865d63148109758f540432d62151329798c54c866c62551109b58a544426c65509329758e520823f6454d209b588540c67b6055131a7191300c36960149109b988530825f63543429d584540c23d64148109e195204432e52106408fd91530831d5390c42d9949510c3595354021ce551500863e6494e21ba580218825d6394740ab191210865e63d53109b189534432f5414910c7953318c71e5310a419d984530427960150219b98a53c431c54d4d1097594430c27b65440109798f520423e64d4e218f99454487544354430cb949429025f63540419758c52c426e62943418f990514827960150319798e529023f65504419b58854cc25c63549108f191518c34e524c830b358843cc754538c5108fd91534425e63947429b988540c32e5290640d398a53c8355510c4309ed95300c33a5494021c755132cc72d54948308f590530865d6594c10cb951520423c64548318f59353c825d63150209d58754cca6c62544409b594420865d6394910d394932cc72d54d0821c795153c825d6314520a758c42d034e6394a40ab19121c836842540219b596320874e6294e418f99353c423e65d0941ab58843d063e6494a10a7191324c74d6214d408f592528436932540219dd9
  | 2 => 0x78320881a024030dc0404c9e000050003f228000000027407100010f436000021d004008000042d5bc040780f0002801c0006000008010000a000050000701c03000000640402c0a01c6e06404010000046c0080002007078000080108c02058030082f0040c10c000080300c141e4060181f00000044211a40512c0100022000010040000015010000100302001318010002e0000802c0700c02011270040a0140500095050030bc0705c5d004ce028000000001c0b0248800061104e1040011083a0e00500c08004790fc08148002707117403004080000000167040090001c06404014020f4090000c1c0100300111c030240002c260f00a0103005c0004c010001e1987c0003b008050304300406000010080306c290000100800304160600801e3d6494d109b58b540c26f62553109b588540c274654c5108f990538831d5310c429798c54086ad6210c40d398c525066d6588420d358c525065d6315320d5546310c25e6394a10cb551520c26e62949108f592508cacd6310a219718d50d0b1d544c8329dd85544832e54948309b588530429c644ca309b988538423e6510940c755253c823d6494f109e59610042ac6250540cb55132c823e6414c208f992544ca6f65508429b588535033654944309e983540863e64149318f593528423d64d48108f590534825d63d48108f990504c71d54ccb31c794f439063d6494020a798e415066d6294e418f191518cb2c62553208f592524432d544c832d350d5210e5d6594c218fd91518cb555344010cb551520423e64940208f990530863d64d4c10cb551320876921540218fd91508878d4350932c794d439063d6414c20d54c9510c29e648c4308f191534863d6494a309e583540865e63d50108f590530423e65d05408f992534426e65d09209bd89544871d53d08429b98b540423e64948208f59052c432e4314941d314c524426e6214131da8c9500871e5390a419798c52c423f6454e10cb552520423e6414f209798e53442cd6210c30c7952530435a53540219798e52083556114d109ed81534863e64942328fd91510834e6214d40cb952218831c63553319b58a534427765440108f590524c67561150209b58b54c
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0xa140000181a01800292c185191514c030a1ae6312a810e0e6394a4190286b90a6a1a81435ca5350e41c1cc629482a0d0d73149425060e3b2a899663451d13254430a1ae431aa998e2a545802188286b9ca4a1481071d9544c830c1ac6b10a89960c531894150286b90c6aa0614a1d12154021a1ae6312a9905457210d510c2a4b9884a80438314e6290140c2cc8a8c621842c7655132c82943a264a80430b1d9544c821
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x2880d8714c625054080d8714e629014080d8798c529054180d8798e5290640
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 664
  | 4 => 539
  | 3 => 25
  | 2 => 4
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
  | 6 => 2*((h/27+packedAt s5K6 (640+(h % 27)*6) 6) % 40)
  | 5 => 2*((h/277+packedAt s5K5 (17928+(h % 277)*10) 10) % 664)
  | 4 => 2*((h/235+packedAt s5K4 (20482+(h % 235)*10) 10) % 539)
  | 3 => 2*((h/22+packedAt s5K3 (1225+(h % 22)*5) 5) % 25)
  | 2 => 2*((h/8+packedAt s5K2 (240+(h % 8)*2) 2) % 4)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x81fff83ffffe1e0ff87f87fe1fffe07d19f3f3
  | 1 => 0xfe1fffc1f87ffff07f87f87fe1c0fffee63c9f
  | 2 => 0xffe0fffe007fe3ff8007ff8ffe00ff8307cf1c
  | 3 => 0xffffff8003fffff8000fffff0003f80fe0
  | 4 => 0xffff0000000003fffffffff000000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xa402088850102002900980920252212808d131
  | 1 => 0x884110480a400502882082420844a50622486
  | 2 => 0x144aa290354906a58444d50b540a950b054b18
  | 3 => 0x5954c425240d4b394d50440d992c0613b00ec0
  | 4 => 0x61988739c67193ce7667664110301863dfb000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xeee8eac8eee8eac8eee8eac8eee8eac8eee8eac8eee8eac8eee8eac8eee8eac8eee8eac8eee8eac8eee8eac8eee8eac8eee8eac8eee8eac8eee8eac8eee8eac8, s5N, s5R, (fun _ _ => 0), s5I, []⟩
end PEqualNP.Outside.L_meta_36783
namespace PEqualNP.Outside.L_meta_36783
open PEqualNP.Outside.L_meta_36783.Model
def q4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def q4K4 : Nat → Nat
  | 0 => 0x2030250200010002bd43cd32bf41bd41bc40df32be40bf43ee32bf42ed32dd32bd42
  | _ => 0
def q4K3 : Nat → Nat
  | 0 => 0x10e00105200a6a9c658e544ca6aa220634ca40c6a12658f424ca5aa5a0e3d0d3296a90811d531031a642063551328ea9e838d434cb1a65a0e34c941
  | _ => 0
def q4K2 : Nat → Nat
  | 0 => 0x10c00000c14c9511028561951328359532d060d654c840
  | _ => 0
def q4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 13
  | 3 => 16
  | 2 => 4
  | _ => 0
def q4R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt q4K5 (i*5) 5
  | 4 => packedAt q4K4 (i*16) 16
  | 3 => packedAt q4K3 (i*27) 27
  | 2 => packedAt q4K2 (i*38) 38
  | _ => 0
def q4I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt q4K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/25+packedAt q4K4 (208+(h % 25)*4) 4) % 13)
  | 3 => 2*((h/12+packedAt q4K3 (432+(h % 12)*4) 4) % 16)
  | 2 => 2*((h/22+packedAt q4K2 (152+(h % 22)*2) 2) % 4)
  | _ => 0
def q4Pos : Nat → Bits
  | 0 => 0x7fc7fff87f0ff0ff0f87e1ffe1fc3f0fa4f4cf
  | 1 => 0x87f870ff8ff0ff0ff1f87e1c3e1fc7f1db4b33
  | 2 => 0x7ff80fff000fff1fe007fe03fe007fe638c3c
  | 3 => 0xf80000ffffff0001ffff80003ffff8007c0fc0
  | 5 => 0xffffff0000000001ffffffffc00000007ff000
  | _ => 0
def q4Neg : Nat → Bits
  | 0 => 0x400008001001000000802400240100001045
  | 1 => 0x20820111040140102088220882090241094112
  | 2 => 0x55112aa222aaa88356445541354094ac628c28
  | 3 => 0x14354cc44a882aa59b5511023992b024740e80
  | 5 => 0x662668876cccccc9ede67993910320c97fe000
  | _ => 0
def q4Atlas : Atlas := ⟨5,rawDecor 47 q4Pos q4Neg, 0xeeeaeeeaeee8eee8eeeaeeeaeee8eee8eeeaeeeaeee8eee8eeeaeeeaeee8eee8eeeaeeeaeee8eee8eeeaeeeaeee8eee8eeeaeeeaeee8eee8eeeaeeeaeee8eee8, q4N, q4R, (fun _ _ => 0), q4I, []⟩
end PEqualNP.Outside.L_meta_36783
namespace PEqualNP.Outside.L_meta_36783
open PEqualNP.Outside.L_meta_36783.Model
def q6K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def q6K4 : Nat → Nat
  | 0 => 0x200006030000004000be40bf41cd32bf43dd32ee32bd41bf42bc40ed32df32bd43bd42
  | _ => 0
def q6K3 : Nat → Nat
  | 0 => 0x117f0840040c7a1a658e544ca3aa7a0e35513296a968335511029aa7196350d32c6994818d321023aa6206350932c7a12652d521031a64a0e34cb41
  | _ => 0
def q6K2 : Nat → Nat
  | 0 => 0x18359532d07053254440a1586544ca0d654c840
  | _ => 0
def q6N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 13
  | 3 => 16
  | 2 => 4
  | _ => 0
def q6R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt q6K5 (i*5) 5
  | 4 => packedAt q6K4 (i*16) 16
  | 3 => packedAt q6K3 (i*27) 27
  | 2 => packedAt q6K2 (i*38) 38
  | _ => 0
def q6I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt q6K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/18+packedAt q6K4 (208+(h % 18)*4) 4) % 13)
  | 3 => 2*((h/12+packedAt q6K3 (432+(h % 12)*4) 4) % 16)
  | 2 => 2*((h/15+packedAt q6K2 (152+(h % 15)*2) 2) % 4)
  | _ => 0
def q6Pos : Nat → Bits
  | 0 => 0x7fc7fff87f0ff0ff0f87e1ffe1fc3f0fa4f4cf
  | 1 => 0x87f870ff8ff0ff0ff1f87e1c3e1fc7f1db4b33
  | 2 => 0x7ff80fff000fff1fe007fe03fe007fe638c3c
  | 3 => 0xf80000ffffff0001ffff80003ffff8007c0fc0
  | 4 => 0xffffff0000000001ffffffffc00000007ff000
  | _ => 0
def q6Neg : Nat → Bits
  | 0 => 0x400008001001000000802400240100001045
  | 1 => 0x20820111040140102088220882090241094112
  | 2 => 0x55112aa222aaa88356445541354094ac628c28
  | 3 => 0x14354cc44a882aa59b5511023992b024740e80
  | 4 => 0x662668876cccccc9ede67993910320c97fe000
  | _ => 0
def q6Atlas : Atlas := ⟨5,rawDecor 31 q6Pos q6Neg, 0xeeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8, q6N, q6R, (fun _ _ => 0), q6I, []⟩
end PEqualNP.Outside.L_meta_36783
namespace PEqualNP.Outside.L_meta_36783
open PEqualNP.Outside.L_meta_36783.Model
def q7K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q7K3 : Nat → Nat
  | 0 => 0x8000500002f98ef21da43e842e98f910
  | _ => 0
def q7K2 : Nat → Nat
  | 0 => 0x344c510e12144314c521
  | _ => 0
def q7N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
  | _ => 0
def q7R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q7K4 (i*4) 4
  | 3 => packedAt q7K3 (i*15) 15
  | 2 => packedAt q7K2 (i*26) 26
  | _ => 0
def q7I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q7K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/16+packedAt q7K3 (90+(h % 16)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q7K2 (78+(h % 8)*2) 2) % 3)
  | _ => 0
def q7Pos : Nat → Bits
  | 2 => 0xbea673b7606e
  | 3 => 0xffffffffffffffffffffffffffff3bbc3bbc93
  | 4 => 0xdfc3cfc3c31c
  | 5 => 0xeffc0ffc03e0
  | _ => 0
def q7Neg : Nat → Bits
  | 2 => 0x424880910426
  | 3 => 0x0
  | 4 => 0x241415020918
  | 5 => 0x18016a2012c0
  | _ => 0
def q7Atlas : Atlas := ⟨4,rawDecor 60 q7Pos q7Neg, 0xfffffff0fff0ff00fffffff0fff0ff00fffffff0fff0ff00fffffff0fff0ff00fffffff0fff0ff00fffffff0fff0ff00fffffff0fff0ff00fffffff0fff0ff00, q7N, q7R, (fun _ _ => 0), q7I, []⟩
end PEqualNP.Outside.L_meta_36783
namespace PEqualNP.Outside.L_meta_36783
open PEqualNP.Outside.L_meta_36783.Model
def q8K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q8K3 : Nat → Nat
  | 0 => 0x5000076906f20be61dc42e987510
  | _ => 0
def q8K2 : Nat → Nat
  | 0 => 0x40324c120e12044344c110
  | _ => 0
def q8N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
  | _ => 0
def q8R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q8K4 (i*4) 4
  | 3 => packedAt q8K3 (i*15) 15
  | 2 => packedAt q8K2 (i*26) 26
  | _ => 0
def q8I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q8K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/16+packedAt q8K3 (90+(h % 16)*3) 3) % 6)
  | 2 => 2*((h/15+packedAt q8K2 (78+(h % 15)*2) 2) % 3)
  | _ => 0
def q8Pos : Nat → Bits
  | 1 => 0xfffffffffffffffffffffffffffeaef1b77c27
  | 2 => 0xbf333e3ba0da
  | 4 => 0xdfc3cfc3c31c
  | 5 => 0xeffc0ffc03e0
  | _ => 0
def q8Neg : Nat → Bits
  | 1 => 0x0
  | 2 => 0x42444211044a
  | 4 => 0x241814820914
  | 5 => 0x1801a92012a0
  | _ => 0
def q8Atlas : Atlas := ⟨4,rawDecor 54 q8Pos q8Neg, 0xfffffcfcfcfcccccfffffcfcfcfcccccfffffcfcfcfcccccfffffcfcfcfcccccfffffcfcfcfcccccfffffcfcfcfcccccfffffcfcfcfcccccfffffcfcfcfccccc, q8N, q8R, (fun _ _ => 0), q8I, []⟩
end PEqualNP.Outside.L_meta_36783
namespace PEqualNP.Outside.L_meta_36783
open PEqualNP.Outside.L_meta_36783.Model
def q9K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q9K3 : Nat → Nat
  | 0 => 0x30003b085e30d84170c37107410
  | _ => 0
def q9K2 : Nat → Nat
  | 0 => 0x200340c010c830083808010
  | _ => 0
def q9N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
  | _ => 0
def q9R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q9K4 (i*4) 4
  | 3 => packedAt q9K3 (i*15) 15
  | 2 => packedAt q9K2 (i*26) 26
  | _ => 0
def q9I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q9K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/9+packedAt q9K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q9K2 (78+(h % 8)*2) 2) % 3)
  | _ => 0
def q9Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffbf0fffc3fe3f
  | 4 => 0xffffffffffffffffffffffffffdff0fffc3fc7
  | 5 => 0xefff0fffc3f8
  | _ => 0
def q9Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffff012222c444db
  | 2 => 0xffffffffffffffffffffffffff42e44562aa2d
  | 4 => 0x244e89aa3346
  | 5 => 0x1888ee3323b0
  | _ => 0
def q9Atlas : Atlas := ⟨4,rawDecor 53 q9Pos q9Neg, 0xaaaaa0a0a0a00000aaaaa0a0a0a00000aaaaa0a0a0a00000aaaaa0a0a0a00000aaaaa0a0a0a00000aaaaa0a0a0a00000aaaaa0a0a0a00000aaaaa0a0a0a00000, q9N, q9R, (fun _ _ => 0), q9I, []⟩
end PEqualNP.Outside.L_meta_36783
namespace PEqualNP.Outside.L_meta_36783
open PEqualNP.Outside.L_meta_36783.Model
def q10K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q10K3 : Nat → Nat
  | 0 => 0x40206e985e31bc6570cae18df30
  | _ => 0
def q10K2 : Nat → Nat
  | 0 => 0x40096418ca390a318c424c2510530
  | _ => 0
def q10N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def q10R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q10K4 (i*4) 4
  | 3 => packedAt q10K3 (i*15) 15
  | 2 => packedAt q10K2 (i*26) 26
  | _ => 0
def q10I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q10K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/9+packedAt q10K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q10K2 (104+(h % 8)*2) 2) % 4)
  | _ => 0
def q10Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff3ffff1ffff1ff
  | 1 => 0xffffffffffffffffffffffedfc7f3fe3f0fe73
  | 3 => 0x76ff8fcffc7f0f9c
  | 5 => 0x78fff00fff800fe0
  | _ => 0
def q10Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa0180202049440a5
  | 1 => 0x122324452122a652
  | 3 => 0x9416819484a2b18
  | 5 => 0x78a4eae920ccde0
  | _ => 0
def q10Atlas : Atlas := ⟨4,rawDecor 43 q10Pos q10Neg, 0xee88ee88aa88aa88ee88ee88aa88aa88ee88ee88aa88aa88ee88ee88aa88aa88ee88ee88aa88aa88ee88ee88aa88aa88ee88ee88aa88aa88ee88ee88aa88aa88, q10N, q10R, (fun _ _ => 0), q10I, []⟩
end PEqualNP.Outside.L_meta_36783
namespace PEqualNP.Outside.L_meta_36783
open PEqualNP.Outside.L_meta_36783.Model
def q11K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q11K3 : Nat → Nat
  | 0 => 0x8002c02f98dd31bc6170c2f995d32
  | _ => 0
def q11K2 : Nat → Nat
  | 0 => 0x9541cca350b3195410c2350830
  | _ => 0
def q11N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def q11R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q11K4 (i*4) 4
  | 3 => packedAt q11K3 (i*15) 15
  | 2 => packedAt q11K2 (i*26) 26
  | _ => 0
def q11I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q11K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/9+packedAt q11K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q11K2 (104+(h % 8)*2) 2) % 4)
  | _ => 0
def q11Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff7fcfc7ff8f3cf
  | 1 => 0xffffffffffffffffffffffedf99f3f8e3f3d33
  | 3 => 0x76fe1fcff03fce3c
  | 5 => 0x78ffe00fffc00fc0
  | _ => 0
def q11Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa010010012080045
  | 1 => 0x1224284484922512
  | 3 => 0x941501921248a28
  | 5 => 0x7851aae4986af80
  | _ => 0
def q11Atlas : Atlas := ⟨4,rawDecor 43 q11Pos q11Neg, 0xeeaaeeaaee88ee88eeaaeeaaee88ee88eeaaeeaaee88ee88eeaaeeaaee88ee88eeaaeeaaee88ee88eeaaeeaaee88ee88eeaaeeaaee88ee88eeaaeeaaee88ee88, q11N, q11R, (fun _ _ => 0), q11I, []⟩
end PEqualNP.Outside.L_meta_36783
namespace PEqualNP.Outside.L_meta_36783
open PEqualNP.Outside.L_meta_36783.Model
def q12K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q12K3 : Nat → Nat
  | 0 => 0x120000af195c32ba6170c6f18df30
  | _ => 0
def q12K2 : Nat → Nat
  | 0 => 0x40008c424c25906328e428c6510530
  | _ => 0
def q12N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def q12R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q12K4 (i*4) 4
  | 3 => packedAt q12K3 (i*15) 15
  | 2 => packedAt q12K2 (i*26) 26
  | _ => 0
def q12I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q12K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/9+packedAt q12K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q12K2 (104+(h % 8)*2) 2) % 4)
  | _ => 0
def q12Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff3ffff1ffff1ff
  | 1 => 0xffffffffffffffffffffffedfc7f3fe3f0fe73
  | 3 => 0x76ff8fcffc7f0f9c
  | 4 => 0x78fff00fff800fe0
  | _ => 0
def q12Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa0180202049440a5
  | 1 => 0x122324452122a652
  | 3 => 0x9416819484a2b18
  | 4 => 0x78a4eae920ccde0
  | _ => 0
def q12Atlas : Atlas := ⟨4,rawDecor 27 q12Pos q12Neg, 0xee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88, q12N, q12R, (fun _ _ => 0), q12I, []⟩
end PEqualNP.Outside.L_meta_36783
namespace PEqualNP.Outside.L_meta_36783
open PEqualNP.Outside.L_meta_36783.Model
def q13K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q13K3 : Nat → Nat
  | 0 => 0x810902e995d31b8617cc6f185f32
  | _ => 0
def q13K2 : Nat → Nat
  | 0 => 0x9541cca5504308d420c2350b31
  | _ => 0
def q13N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def q13R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q13K4 (i*4) 4
  | 3 => packedAt q13K3 (i*15) 15
  | 2 => packedAt q13K2 (i*26) 26
  | _ => 0
def q13I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q13K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/9+packedAt q13K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/1+packedAt q13K2 (104+(h % 1)*2) 2) % 4)
  | _ => 0
def q13Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff7fcfc7ff8f3cf
  | 1 => 0xffffffffffffffffffffffedf99f3f8e3f3d33
  | 3 => 0x76fe1fcff03fce3c
  | 4 => 0x78ffe00fffc00fc0
  | _ => 0
def q13Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa010010012080045
  | 1 => 0x1224284484922512
  | 3 => 0x941501921248a28
  | 4 => 0x7851aae4986af80
  | _ => 0
def q13Atlas : Atlas := ⟨4,rawDecor 27 q13Pos q13Neg, 0xeeaaee88eeaaee88eeaaee88eeaaee88eeaaee88eeaaee88eeaaee88eeaaee88eeaaee88eeaaee88eeaaee88eeaaee88eeaaee88eeaaee88eeaaee88eeaaee88, q13N, q13R, (fun _ _ => 0), q13I, []⟩
end PEqualNP.Outside.L_meta_36783
namespace PEqualNP.Outside.L_meta_36783
open PEqualNP.Outside.L_meta_36783.Model
def q14K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q14K3 : Nat → Nat
  | 0 => 0x10000ae98df31bc6170c2f195c32
  | _ => 0
def q14K2 : Nat → Nat
  | 0 => 0x8c424c66101318e428c2690232
  | _ => 0
def q14N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def q14R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q14K4 (i*4) 4
  | 3 => packedAt q14K3 (i*15) 15
  | 2 => packedAt q14K2 (i*26) 26
  | _ => 0
def q14I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q14K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/16+packedAt q14K3 (90+(h % 16)*3) 3) % 6)
  | 2 => 2*((h/15+packedAt q14K2 (104+(h % 15)*2) 2) % 4)
  | _ => 0
def q14Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffddf1ff3f1ff0f3f3
  | 1 => 0xffffffffffffffffffffffeffe7fffe3fffc7f
  | 2 => 0x76ff8fcffc7f0f9c
  | 5 => 0x78fff00fff800fe0
  | _ => 0
def q14Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa21c2243049261b1
  | 1 => 0x1021040421248446
  | 2 => 0x9446819484a2a98
  | 5 => 0x7894eae920ccf60
  | _ => 0
def q14Atlas : Atlas := ⟨4,rawDecor 39 q14Pos q14Neg, 0xe8e8e8e8c8c8c8c8e8e8e8e8c8c8c8c8e8e8e8e8c8c8c8c8e8e8e8e8c8c8c8c8e8e8e8e8c8c8c8c8e8e8e8e8c8c8c8c8e8e8e8e8c8c8c8c8e8e8e8e8c8c8c8c8, q14N, q14R, (fun _ _ => 0), q14I, []⟩
end PEqualNP.Outside.L_meta_36783
namespace PEqualNP.Outside.L_meta_36783
open PEqualNP.Outside.L_meta_36783.Model
def q15K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q15K3 : Nat → Nat
  | 0 => 0x86000ae98dc30be657cc6e995e30
  | _ => 0
def q15K2 : Nat → Nat
  | 0 => 0x200009541cca350b3195410c2350830
  | _ => 0
def q15N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def q15R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q15K4 (i*4) 4
  | 3 => packedAt q15K3 (i*15) 15
  | 2 => packedAt q15K2 (i*26) 26
  | _ => 0
def q15I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q15K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/9+packedAt q15K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/15+packedAt q15K2 (104+(h % 15)*2) 2) % 4)
  | _ => 0
def q15Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff7fcfc7ff8f3cf
  | 1 => 0xffffffffffffffffffffffedf99f3f8e3f3d33
  | 2 => 0x76fe1fcff03fce3c
  | 5 => 0x78ffe00fffc00fc0
  | _ => 0
def q15Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa010010012080045
  | 1 => 0x1224284484922512
  | 2 => 0x941501921248a28
  | 5 => 0x7851aae4986af80
  | _ => 0
def q15Atlas : Atlas := ⟨4,rawDecor 39 q15Pos q15Neg, 0xeaeaeaeae8e8e8e8eaeaeaeae8e8e8e8eaeaeaeae8e8e8e8eaeaeaeae8e8e8e8eaeaeaeae8e8e8e8eaeaeaeae8e8e8e8eaeaeaeae8e8e8e8eaeaeaeae8e8e8e8, q15N, q15R, (fun _ _ => 0), q15I, []⟩
end PEqualNP.Outside.L_meta_36783
namespace PEqualNP.Outside.L_meta_36783
open PEqualNP.Outside.L_meta_36783.Model
def q16K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q16K3 : Nat → Nat
  | 0 => 0x8001882e195c30bc6578c2f98dd31
  | _ => 0
def q16K2 : Nat → Nat
  | 0 => 0x4e008e428c26902328c424c6610131
  | _ => 0
def q16N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def q16R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q16K4 (i*4) 4
  | 3 => packedAt q16K3 (i*15) 15
  | 2 => packedAt q16K2 (i*26) 26
  | _ => 0
def q16I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q16K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/9+packedAt q16K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q16K2 (104+(h % 8)*2) 2) % 4)
  | _ => 0
def q16Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffddf1ff3f1ff0f3f3
  | 1 => 0xffffffffffffffffffffffeffe7fffe3fffc7f
  | 2 => 0x76ff8fcffc7f0f9c
  | 4 => 0x78fff00fff800fe0
  | _ => 0
def q16Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa21c2243049261b1
  | 1 => 0x1021040421248446
  | 2 => 0x9446819484a2a98
  | 4 => 0x7894eae920ccf60
  | _ => 0
def q16Atlas : Atlas := ⟨4,rawDecor 23 q16Pos q16Neg, 0xe8e8c8c8e8e8c8c8e8e8c8c8e8e8c8c8e8e8c8c8e8e8c8c8e8e8c8c8e8e8c8c8e8e8c8c8e8e8c8c8e8e8c8c8e8e8c8c8e8e8c8c8e8e8c8c8e8e8c8c8e8e8c8c8, q16N, q16R, (fun _ _ => 0), q16I, []⟩
end PEqualNP.Outside.L_meta_36783
namespace PEqualNP.Outside.L_meta_36783
open PEqualNP.Outside.L_meta_36783.Model
def q17K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q17K3 : Nat → Nat
  | 0 => 0x4001802e98dc30be6578c2f98dd32
  | _ => 0
def q17K2 : Nat → Nat
  | 0 => 0x300095410c25507328d42cc6350830
  | _ => 0
def q17N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def q17R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q17K4 (i*4) 4
  | 3 => packedAt q17K3 (i*15) 15
  | 2 => packedAt q17K2 (i*26) 26
  | _ => 0
def q17I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q17K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/9+packedAt q17K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q17K2 (104+(h % 8)*2) 2) % 4)
  | _ => 0
def q17Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff7fcfc7ff8f3cf
  | 1 => 0xffffffffffffffffffffffedf99f3f8e3f3d33
  | 2 => 0x76fe1fcff03fce3c
  | 4 => 0x78ffe00fffc00fc0
  | _ => 0
def q17Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa010010012080045
  | 1 => 0x1224284484922512
  | 2 => 0x941501921248a28
  | 4 => 0x7851aae4986af80
  | _ => 0
def q17Atlas : Atlas := ⟨4,rawDecor 23 q17Pos q17Neg, 0xeaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8, q17N, q17R, (fun _ _ => 0), q17I, []⟩
end PEqualNP.Outside.L_meta_36783
namespace PEqualNP.Outside.L_meta_36783
open PEqualNP.Outside.L_meta_36783.Model
def q18K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q18N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q18R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q18K3 (i*4) 4
  | _ => 0
def q18I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q18K3 (4+(h % 1)*1) 1) % 1)
  | _ => 0
def q18Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffbfcffcf8fff873f3
  | 1 => 0xffffffffffffffffffffffdff39fff1c3ffc9f
  | 2 => 0xebfc1f3fe03f8f1c
  | 3 => 0xf3ffe03fffc00fe0
  | _ => 0
def q18Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff4061010824892131
  | 1 => 0x2088281109124486
  | 2 => 0x1523506a42a52b18
  | 3 => 0xe0a1ab493064ec0
  | _ => 0
def q18Atlas : Atlas := ⟨3,rawDecor 15 q18Pos q18Neg, 0xeac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8, q18N, q18R, (fun _ _ => 0), q18I, []⟩
end PEqualNP.Outside.L_meta_36783
namespace PEqualNP.Outside.L_meta_36783
open PEqualNP.Outside.L_meta_36783.Model
def q19K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q19K3 : Nat → Nat
  | 0 => 0x40046d32ba6534caf996e32
  | _ => 0
def q19K2 : Nat → Nat
  | 0 => 0x2350e32
  | _ => 0
def q19N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
  | _ => 0
def q19R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q19K4 (i*4) 4
  | 3 => packedAt q19K3 (i*15) 15
  | 2 => packedAt q19K2 (i*26) 26
  | _ => 0
def q19I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q19K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/8+packedAt q19K3 (75+(h % 8)*3) 3) % 5)
  | 2 => 2*((h/1+packedAt q19K2 (26+(h % 1)*1) 1) % 1)
  | _ => 0
def q19Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffbfdcf3e3f3e74cf
  | 1 => 0xfffffffffffffffffffffffdfef3cfc7cf9b33
  | 2 => 0xebf03f3f80fec3c
  | 3 => 0xf3ffc03fff00fc0
  | _ => 0
def q19Neg : Nat → Bits
  | 0 => 0xfffffffffffffffffffffff404104009020045
  | 1 => 0x208041042040112
  | 2 => 0x150aa0690a94c28
  | 3 => 0xe082ab24a14e80
  | _ => 0
def q19Atlas : Atlas := ⟨4,rawDecor 15 q19Pos q19Neg, 0xeee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8, q19N, q19R, (fun _ _ => 0), q19I, []⟩
end PEqualNP.Outside.L_meta_36783
namespace PEqualNP.Outside.L_meta_36783
open PEqualNP.Outside.L_meta_36783.Model
def q20K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q20K3 : Nat → Nat
  | 0 => 0x40046d32ba6534caf996e32
  | _ => 0
def q20K2 : Nat → Nat
  | 0 => 0x2350e32
  | _ => 0
def q20N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
  | _ => 0
def q20R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q20K4 (i*4) 4
  | 3 => packedAt q20K3 (i*15) 15
  | 2 => packedAt q20K2 (i*26) 26
  | _ => 0
def q20I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q20K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/8+packedAt q20K3 (75+(h % 8)*3) 3) % 5)
  | 2 => 2*((h/1+packedAt q20K2 (26+(h % 1)*1) 1) % 1)
  | _ => 0
def q20Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffbfdcf3e3f3e74cf
  | 1 => 0xfffffffffffffffffffffffdfef3cfc7cf9b33
  | 2 => 0xebf03f3f80fec3c
  | 3 => 0xf3ffc03fff00fc0
  | _ => 0
def q20Neg : Nat → Bits
  | 0 => 0xfffffffffffffffffffffff404104009020045
  | 1 => 0x208041042040112
  | 2 => 0x150aa0690a94c28
  | 3 => 0xe082ab24a14e80
  | _ => 0
def q20Atlas : Atlas := ⟨4,rawDecor 15 q20Pos q20Neg, 0xeee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8, q20N, q20R, (fun _ _ => 0), q20I, []⟩
end PEqualNP.Outside.L_meta_36783
namespace PEqualNP.Outside.L_meta_36783
open PEqualNP.Outside.L_meta_36783.Model
def q21K3 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def q21N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q21R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q21K3 (i*3) 3
  | _ => 0
def q21I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q21K3 (3+(h % 1)*1) 1) % 1)
  | _ => 0
def q21Pos : Nat → Bits
  | 2 => 0xffffffffffffffffffffffffffffffffffbecf
  | 4 => 0xffffffffffffffffffffffffffffffffffdf73
  | 5 => 0xefbc
  | _ => 0
def q21Neg : Nat → Bits
  | 2 => 0xffffffffffffffffffffffffffffffffff4205
  | 4 => 0x2412
  | 5 => 0x1828
  | _ => 0
def q21Atlas : Atlas := ⟨3,rawDecor 52 q21Pos q21Neg, 0xfffff0f0f0f00000fffff0f0f0f00000fffff0f0f0f00000fffff0f0f0f00000fffff0f0f0f00000fffff0f0f0f00000fffff0f0f0f00000fffff0f0f0f00000, q21N, q21R, (fun _ _ => 0), q21I, []⟩
end PEqualNP.Outside.L_meta_36783
namespace PEqualNP.Outside.L_meta_36783
open PEqualNP.Outside.L_meta_36783.Model
def q22K3 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def q22N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q22R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q22K3 (i*3) 3
  | _ => 0
def q22I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q22K3 (3+(h % 1)*1) 1) % 1)
  | _ => 0
def q22Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffbecf
  | 1 => 0xffffffffffffffffffffffffffffffffffdf73
  | 3 => 0xefbc
  | _ => 0
def q22Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffff4205
  | 1 => 0x2412
  | 3 => 0x1828
  | _ => 0
def q22Atlas : Atlas := ⟨3,rawDecor 11 q22Pos q22Neg, 0xee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88, q22N, q22R, (fun _ _ => 0), q22I, []⟩
end PEqualNP.Outside.L_meta_36783
namespace PEqualNP.Outside.L_meta_36783
open PEqualNP.Outside.L_meta_36783.Model
def q23K3 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def q23N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q23R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q23K3 (i*3) 3
  | _ => 0
def q23I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q23K3 (3+(h % 1)*1) 1) % 1)
  | _ => 0
def q23Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffbecf
  | 1 => 0xffffffffffffffffffffffffffffffffffdf73
  | 3 => 0xefbc
  | _ => 0
def q23Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffff4205
  | 1 => 0x2412
  | 3 => 0x1828
  | _ => 0
def q23Atlas : Atlas := ⟨3,rawDecor 11 q23Pos q23Neg, 0xee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88, q23N, q23R, (fun _ _ => 0), q23I, []⟩
end PEqualNP.Outside.L_meta_36783
namespace PEqualNP.Outside.L_meta_36783
open PEqualNP.Outside.L_meta_36783.Model
def q24K3 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def q24N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q24R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q24K3 (i*3) 3
  | _ => 0
def q24I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q24K3 (3+(h % 1)*1) 1) % 1)
  | _ => 0
def q24Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffbecf
  | 1 => 0xffffffffffffffffffffffffffffffffffdf73
  | 2 => 0xefbc
  | _ => 0
def q24Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffff4205
  | 1 => 0x2412
  | 2 => 0x1828
  | _ => 0
def q24Atlas : Atlas := ⟨3,rawDecor 7 q24Pos q24Neg, 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8, q24N, q24R, (fun _ _ => 0), q24I, []⟩
end PEqualNP.Outside.L_meta_36783
namespace PEqualNP.Outside.L_meta_36783
open PEqualNP.Outside.L_meta_36783.Model
def q25K3 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def q25N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q25R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q25K3 (i*3) 3
  | _ => 0
def q25I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q25K3 (3+(h % 1)*1) 1) % 1)
  | _ => 0
def q25Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffbecf
  | 1 => 0xffffffffffffffffffffffffffffffffffdf73
  | 2 => 0xefbc
  | _ => 0
def q25Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffff4205
  | 1 => 0x2412
  | 2 => 0x1828
  | _ => 0
def q25Atlas : Atlas := ⟨3,rawDecor 7 q25Pos q25Neg, 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8, q25N, q25R, (fun _ _ => 0), q25I, []⟩
end PEqualNP.Outside.L_meta_36783
namespace PEqualNP.Outside.L_meta_36783
open PEqualNP.Outside.L_meta_36783.Model
def gbK10 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK9 : Nat → Nat
  | 0 => 0x40984202cc0000447007f50801fd50007f8c001fd30007f50001fe41007f44001fd52007f88401fd31007f54401fd41007f04001fd53007f8c401fe10007f55001fd32007f48401fe51007fc4001fd43007f94001fe40007f48001fe20
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x2a2015ff18a300e7fea09084ffc404c03dfe2844200bf59520007fa830800fff5304001fe302a800ef99231007d8c488003fd4188401feaa46000ff4c910005fecb188a3ff514c8016fb1a2000bf18143007faca9886ffc5448419ffa9e2000ff90650007fa82a80037f65440017fb242000ff50510005f8c299003ff6544001fea9c4000ff54d210fffca498827ff5484009fe1022000ff50b10117f88518803ff648c0017f30c60009f596310d7f88690843fc5488021fe20c4000ffd9521005fec808002fd6390401fea0ca011ffd4e200b7fe83180037e5054001ffb2c6012ff109300077aa920002fe6088401fb18e2000bf591310c77c8720002fd648800ffe104200eff195200eff8a91081bfc5044001fea882000fb54932007faa2a0002fd65880017fb0aa800fbd8910005fec0a1803fd319401dffa8a4000df54e51007fa42a808ffc408c4017eb0c2000bf5931003ffc85080a3fc654c837fe20a4200ff98121007fc8090003ff6188001bf28ca00fff10e20006fccb18807fc4204045fe2946200ff50931007faa69006bff3148449ffa946224ff99631007dc4090003fd614c8017eb102000bfd9121007faa388003bf6444001ff2824000ef59010007fac898803ff6448001fea8c6211ffd4620007fa6508003fd658c4017fb024200ff5971009ffe829802bfc42c4005fe2002000fb4ca21005f8c0a1047ff508804dbf29aa200bf982510fffe4298843fe6488001feaa46201ff14810047f8c908027fc5084001df20a821aff18d21007fc4088002fd6550801fea844000fb48520005f8c2a8003f71004007ffa90201eff99621005facaa1803fd3254447ffa0c6200ff48650097f8a49802ffc40c4001ff28c801cffd4521007ec2088003fe50880017eb24620aff14b100077aa8a1003ed6204001fea8a6000bf59121007f8c299002ff6054801fc8802000f78c6300d7f86090802fd628c001feaa02000ff48640057fcc5880037d5354837ff3224200ffd8154006faa6a8003fd2144001ef1826000ff50a10005fcc008002ff62c4001ff3026416ff95230077fea69009ffc404c801feaa26000df54a50017fe8208033fe65c4001fea8a4200ef50d4208ff8cb10003fb10440017eb0ca027ff151320fff8a498803fe509001fff98c4017ffd523000ffcc408002ff6388401ffb2a640cffd5310007faa988003be405000bfe2a22000ffd8121007fec890803fd43040017fb126200ffd8d21005fecb18003dd434c801fea922013ff191300e7f8ca90802fd65c4017ffa0e2000bfd962013ffcc899073ff5348401bf28aa200bf5912007ff86110003dc6344001feb226400ff54e21005fcc32807ffc424c401feaa26400af59010007fc4328003ff60504017fb1a4000ff50f10005facb10802ff6354801fd8842000ff18141
  | 1 => 0x3bc644c035fe18a4200bfd95100d7f8a6908037d65040017fb10200fff18e20007ba6498803fd62c400ffe2142000df99410005fec299017ff41440013fb2a201dffd0e2107ff86310002ff6250001ff1002000ff59410005fac928803fd21040017eb2a6400ffd8132007fec498002ff6154c37fe32242009fd953004ffea508003fc6188001ff2828000ff9862007ffca71006bfe53484017fb1aa008ff102100077aa8a089fff404c801feb2c4210ff19220097f8c498002fd62440017eb2c2000ff58e20007f8c099002ff6304049ffa8c6203ff99410117fcc51885fff518c001ff2046007ff14a10005fecb2080bfc5404001fb8842021ff995310bff8cb18003fe20c40017fb128612ffc8530007faa518802ff654c443fe2826213ff1513007ff8a710003fd5184001dfb226004ff18910005fac588003f531440017eb2a4200bf181320effca910857ff218c045ff2946215ff14a300057ec888003fd414c4017fb2c8000bf1855302ffe8688002ff6550c017fb026400ef50e41007da8499003fd428c017fe2a62000ff55210005f8c0a8803fd4384033bf29ca000bfd9520005feca98003fe40880017eb1e2005ff95110005facb20003fe614c83dffaa44225ef90d41007faa408002bf644c011ffa0c2000df551510a7fea29803bfc50480017fb028200ff54930007da6490002fd6404039ff32a4200bfd9150005fec298003fd4148401ff20a4200ff8c650005fac52881ffc6284001ff20c4000ffd9220004faca08007fe5204025ff2926000bf58620007fca2a0803fe6190001ffb122000bf18540007fac910003fd6048401ff18c8000ff54b100a7fea498003fd53040017fb1a4200ff54f10007fecb08003fd3148419ffa96201cff14121057fca588047fc5088001ff2826000ffd9520005f8c290003be6404001fea926200ff50620007faa318003fe50c40017eb282000bf58a31047fe850808bff218c401feb2a4200ef50a40007fca008002ff6150c01fe98c4000ffd8151005facaa0002fc6155001ff2002006ffd5110007fca310002ff6350011ffa1c2000ff59231005fac928002fc6054c11ff2a42000ff4ca40067fea388002fd644c0017e30a8400ff5881013ff88299002ff6050801fea146200bf596300aff88518002ff65484017fb224000ff90130147fea09905fff528c001dea0a8001ff8c810107f8a898843ff4088007ffa882000bfd9231057fe4388002ff6154009ff2122000bf59230005fec508003fd3254043ffa8a6200bf58a1002ffe848802bfe32c40017fb126000ff90310006facb18807ff2104001ff28a4200bf59531007fec518003fd3294001feb262000bf5921013ff8c899077fe648841bfe2a24005ff191100b7f88118003fd6188001fea126000bfd8520005f8c298003fd42040017eb
  | 2 => 0x10005fec2a9003fd5448027ff2a26000bfd9130005fac520802fd6550451ff32a6407ff94a10017fca808003fd5148001feb026400ff4ca51005fec6a8803fd32500017e30a8627ff9513200778c888003ff6388001fea0c6000ef906400077ac918803f92044001ffb142000bfd9610087f8811001bff53440017fb12a006ffd4510117fc8518803fd624c409ff1922003ffd50100bff8a11808fff428c429ffaa26000bf1815405ffca988003fd4388001ffb0a640dffd0520005fec0aa04fff424c005ff3202000bf181520fffcc498803fd4348051fe28a6401ff90810007fa8290002fd6294001fea8c4000ff54e10007fa8690802fd654c0017fb1c2000bf986400a7f8ca980037c654c001feaa44000bfd9152007faa890803ff6484001ff2842000ff50910007f44088002ff6550401f73102010ffd0620017fe840802bfe42c4035ff982421aff90d21005bac60803fff30880017eb182000bf58d1005ffcc98806fff4148445fe104621dff10221007fa632004bfe424c001ffb2c4028ffd5132006faa4a883ffe4388001fea044000ff58d21007fc611002fff42c4001fe90a6000bf58251005f8c098847fe6588037ffa024200bfd8910007fa6408003fd61940017fb22621fff08131007fc8108003dd534c81dffaa24000ff18554006faa8a9003de314c4017fb282000df54550005fec899037ff4348001fe90c6000fe482100077a86a0027ff51840017fb244000fd8c510006faa8a9803fd418c449fe2846216ff1523003ffc6508002fc6048401fea946001ff080100effe8310803fd4104001fe9962000ff59010005fec6a0803fe508c025fe1026000bfd815103ffe4308002ff6254401ff30ca023ff9923104ff8cb08002ff6254c01fea8c4220ff95131027f88488002fd6384001dea128200ffd8554005fac5200037c6544021ffa1c401bffd0d2110ffea89882bfc20c4001fd1042005ff10110005dec488002ff6355013ffa9c2004ff14910007ea2008003fd5488401feb244200df5525001ff8a008002fe60840017eb222000ff54640005fac720002ff6150829fe282600dff1912008ff8a310003fd2150001fea0a600dff95120005fac728002fd65904015eb246200dfd9530067f8a18801bff52440017eb1a4000bf58e20007fec888003dd314c001feb2a6400ff50710005fec8a9802fe6104001fe9948200bfd8941007fa8710803de6304039ffaa24200bfd8d10037f8ca88002ff6550047fe2a46200bfd954208ffea910003ff644c801fea8a2000bf986200e7f8a2908a3fc504c8017fb02a61bff95121007faa88807ffe424c401ff18a4200ffd9530107fe8498803fd6190001ff18c4010ff952200affca518003fd21c40017fb1a8400ff4c941007fa6110003fd628c401fe3024200ff50d100d7fcc69080
  | 3 => 0xc0400c0f00800000100cc0507c05020110ac11009390149c02c2961c283e815014210040f0b515000070b0010040b3640406c0a1180f0000302c0200015704710143a0c419000010000401c00008960dc021a00f004270000100c1307c0305c100002c004150fc010000e02800000054482c0144c0041b0254800401068020b8050b87c42410014050a8041105c0804a160060000e61c0b0045d35c000382c47cf421c05001620001e004241580c02c00020020a004054940109a394c004404040090242803cb51ec52000180103445c280100600c0b09c000709f0005f0e001008010084606c30000040000214c5917c010000002003038150940c084010340100452134030800a01800100001b4180b0030081703000018640003e01006098020f402270a60040007c05164aa04c0203c0002800024150d02b00011fe2a42000ff48610005fec710083ff414c4017fb12a827ffd0532007faa320857fe428c001feb224200bfd9110005f8c0a080bff430403dffa8c4200bfd9532007f4200805bff428c047ff2a46200bf98231005fec8a8803fd65880017eb2c6220ff10131007fc4320003df63440017fb1e2020ff99131005fac710813fe5244001ffb226000fb88620007fc4108003ee2148401fea9a2000bb58810005fac118803fd5150409ff90a2000fd4c710007bac608003dd328c0017eb048200bfd931010ffea498803fd514c4017f304820bffd0f10005f8c2a9003fd50900017fb026200bfd8540005fec918002fd61900017fb2e2000ef55143005fac910837fc40480017eb1a421bff10121127fea918802ff6588401ff282201effd4e210b7f8c918003fd528401fff31c4000bf58e51005fac318002fd6088401fe302a200bf59132007faa898857fc208c0017fb244200ff901
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0xf74d8a10036ff51586500063f65d91100d6ff5358d2119ff65484110006fd42582310afde3298132007fa5088210006fe6518532065fc75903100069f6418d10007f94244010005ff7155010004ee7618910006ec705881000f7c5254810005ff7650810005fc7055132006dc40d8d10007ef744c920006fe5418530006fc54d8e10006bf64d8930035fe758811002dff7455110006fc7458620006fe6498620006ff43d89101dffa7588110007bd4250410056fc4298410006ec40588101dffb5488110004bd74d8f101bffb54c4110035fc75d911034ef521185320677f5154b10005fc7054a100d6dc634851023ffa748821013ebc6459132016fe6459010005fd73d9521005fc70486400077d72d95300fefd3258d2107fdc6358e20006df6388110006ed5458810045fe7488210006fe54d8121006fd75d8d21027ec6250910006fc649813225ff7524c7102c6fd4218132395f771589310077f4219510006fd6348650007dd634c620015fe745941002fbc72191100aefe4258a30006fe545863016ffa5484010007ef7458810006ef6250510005fc7650620006fd65d8d21004fd72181540069c6418d10116ff42d8e21004fd7318151005fd72d963007fde5398132006fc5258d1001f7f52544100063f6519110004fd72d8c1005fbf4155310006fd6518532025fe72d9110356ff42d85320066f65d8910007f554c4010004fd72181510feff4258e21387de544c931027de324c910007f5548c710005ff7454710005ff7250510065fc7550b100debf4158a41006cc63d8910007dc4298c10005fc7654a10005ff7155121007df5418d10007dc704c931006ec75d8910317de544ca30157f65444010005ff7150d21006fd6458810006fd75d8a10004fe7648550207f6548c510006ed6288010047bc6455210006fe7458a31006ff4298630006fe4258f10006fd7358640005ff72590100d6ff5358a310377f54d9510006ff425823134efe52185320d6dc6358d2113dbc7459532005fd7548510005fc7054a31006fd3258650005ff7259410007dd4358532005fc7058d210adfe7290230006fd73d8554004fd76886403b67f52d8554007dc704ca30006df5458c10006df54d8d10006fc6458620004fe70d8553004fc7059543005fc705481002ebf41d9110057f721d8121005fd7588210005ff7650931004fc764c95102dfc744c910005fd7590210006fc42d8f1000efc5218121116fd3258a31006ff5458e102e7dc524c530006fd6598620006fc54d8d21006fa70d8a10015fe7488010055fe7294310004bd74d8810007f56118532006fc54d8c10005ff7655220387de744c931006fd6458620026fd5258620004fc7059621025fc72941100477e5455210005df7150d322c7dc32181320067d52181510aefd6250a30055fe7254f10
  | 1 => 0x4010004fc764c941047bf4150a10007dc5458c10006fd42986301d7f84088110006fe75d8532007ed524cb10007cd434ca21006df72d8d1003efe764851011ebf42d8d410feff52d893104f7f5294210005ff7255230006fe65581320afce524ca30004fc7650530007dd4318532025fc72d9110006ff5158d210a77c52d9530006fc5458c10004dd73d9641096fc20d8930026ff6254910007be52590100ffee425853201f7f5294010007bd5450910004ff725825101f7f7499410096ff2158e20005ff7655131004bd74d8e21006fc65d89300d6ff4358a31006ed6248650096ff52d8930356fd73d8532006fc4258d100067f654851039cfe76945412aeff52d8132005ff7254c10006fd5298231004fd768c620007f954c4110006fe54d89100e77c65545210077c74d9510007df714c931064ff7654410006fe6558d21006ff65d8d211467e654c810047f74150610065fc7558b10007bd4250610307dc548c63000efe421852004dfc7548610005fe70d9132006fd6558132006ef71d89100fff72158d21004be7619110006fd5458e10007df714ca3004f7f54d9610047bf435521032f3c5418154096fe5258e200077e4259410005bd74d9620006fd52d813101dfc7558810056fe3258b10004ff76553100077f6555110005ff7590310007dd5418d10007ed754c92007efd6350e20005ff71552100debf41d91210077f74d9510377dc548c531007ec54d8910006fe7558810007ec5458810005ff7254e10057bc4250b102e7dc424c53014ffa4244010097f72148530006fe54d8131006ff64581320ffde624c9311277f528c650007bd5450710057ec4250b10047bf42d9210025fc7250510005ff7548510006dd5458c10006fe65d8e20007ed4258532005ff7448610007dd638c220006ff54d8e20036fe7058650006dc4058c10006fe5458620006fe4258231357dc32d853202fbe54505101eff7424c510005fd7690620007dd53d8532006fd54d8d202cfdc428c1301277f5254631006ff71d8e2000dfe7259010006ff4358620096fe5258d2002fbc405091000eff4258810007fb75882100047f7558221005ff7155231057f8209862023ffb418821000efd4218520356f621d853209f3c5455130006dd54d8d10005fd764c620006ff54d8d2103f7c5254a100063d6559010004fd73181542c6fe4218132007f554c42100047f7558e10006d563c4010085be7418620004bf7459532096dd3258e20005ff7255110007be755901004f7f5254610006ff54d8c1003ff820882100077d6550810005fd70d8554006bd644c81001dfc7548410006ff64d8a1005fbe6450b10007de42d8d10005ff7448410006fd52d8530017f74150410006dd6388010005fc7654a30004f77158d20007f9518821005dfe7454710005ff7650e20006f
  | 2 => 0x6fc40d8e2002efc40586400069e6458c10006fe6458532006fc5018121007df5458c10004fc7655220006ae645881000eec5258810005fd729013007edc3058e200477c5455210026fd5258221297ee7548520006ff5458c10005f87048610007dd435813203dfe72d92100aefc52d8d200077f6555210005ff75508100adfc7250630327df3118132334ff7654240116fd6254a31026fd625491002ebe54586400377e74195100fdfc7259531026fe3258620006fc65d8a30005fc7050521005bd748c620006ac64d8910005fd74d8910115fc7259631005fd7190220116fd42d8e212aefa20d8132004dd73d901000efe4258810004df73589100077e4219510004bf7458221007bd72d9130005fe765511003eff21d8a10094fd73d8e20004fe70d8542116fe42d8e21006fe5458a31005ff7150930006ff5158a3102efd545861017ff452c4010047bf4250e10267f4528c7100e77c75486500fefe4258e21004fd764ca41005ff7359521006ff54d8d10006fd54d8e20006fc65d862000efc4218121045fe749421030fdf548c630006fd764ca50004fe768c620005fd71d91320067e64996310e67c6548530005ef7250620007ef54d8910006ff42d8f1003efa6088010004ff715954302fbc54d9110007f97388210356fe42d8532006ff5258f100e57c7558121005fd7448710006fd6498132017be6455010006fe4218131004fe70d9521007df7358931006fe7648550006fd54d8d210377f5454510007df52d8d10004fd71d9130006fd54d8c10004ff7655121006ff54d8e10006fe4298630006fd71d89300d7dc6358d2100eff4218520005ff7159620006fe5498231006fe764c941007bc75d9110006fe6558121007ef5458810004ef7259510056fe6258b10007fa6018121006fc40d8d210dfbc6450d21087bc6459220006fc5458b100047d75d8142007d7714c931006ff631812103ffb52482101475c6554d321c7f854481100d6ff4358d21006fc755862003efe52d8a10005ff76551320077c6550910087bf43592200177c5455010005ff7654e2000efd6250810006fd7458e20005ff7654d210adff728c2201467e65d9532006ff65181320fefd5258d21027f72158121056ff6254b100aefc62d8a30004fd71d9620006fd43d8a100047d75d8f10005fd744c910006fc6558e20005ff7250531004fd7298630004ed72d9410007bc5299231004fd7218153006fe6558810007f9418821002fbc751911005dfc7494310004fc70595320277e5254910007f95488110005ff7154930006fe54d8530005fd7650810006fc6558532356fd42d8532005ff7255131005ff7250630005fc7054620116fe20d8d21007dd5398532017bf4250c100fefd4258e2102dfc74d95100ffce524c931006fc7558e20006ff6254530015fe749
  | 3 => 0xe7454c10087be6490220006fe75d8e20004bd7418550006fe545822103efe5298221005fd76548102efdf424c53005fef4250b1019ff45484110007bd4290110006ff625053002fbf7519110006ff6598532047bc54552100b7bf429023004f7c5054a10006fc54d8d10005fd7550d10006fe5458910007ed54d89100367f51d9510005fc7058532007dd548c630006fc75d8a10006ff65d853207eff5358e2000eff5218520006fd764c810006fd6348640006dc5258c102d7df428c13001dfc7550410005fe7650a100047d769941008d7e75d9220007fb648821001f7f52594100077d535481001dfe7559010006ad649881000efe52d8810006fc54586302c6fc2018132047be549021003ff42198121025fc725451004dfe75d92100377c52d951001dfe7550410005ff7654931006fd7258640006fc5418530006fd711815403fec5254a10086bc40d894000fee625081008f7c50596202c6fd721813201eff7654710007bf6450a10006f76198620387dc744c931317dc744ca30006fe74d8e201aff852c41100047d7518131026ef21d8910007bd43508101e7f6424c510006df6390110096fc7058e20387dc544c931006be6599231006bf6448510006fc54d81210dfbf41d9121006ff7558e200afee529813215ffb5244010006ff5258231007bf54d9110007ed5458810007fa70d8a102a7ee754c92034fee42185320077d5454510017be5490010005ff7550a1009fbc6450930096fd2158e200067d6550410004fc7650550006fd5318121006ed43d8910006fe5458d21017bc5455010006fe54d8b1009fbd7219130006ed6290010006ff5458b1016ff85484010116df32d8d2108e7c6588110005ff7459410006fc5258e10007dd644c9310047d75d8e211177c5254a312c6ff5218132007bc72d9110026ee52d89100057f754c2201457c75581321277c5054a31006fc54d8e201cffb544811001f7c5054810006fe7418121006fd6418121006fd6118132007ef7588120006dc65d8d10056ff42984100067f654c910217f452c4210015fe7458810006fd54d8e10207f4548c510317dc544ca3037fdf548c531006fd4218131005ff7550710157f45444010005fd75d8a100aeff5258a30004ef7258d1003ffb71882100debc644851003dfa70186200377f549411007fdf3158e203a73c54d855408e7c50d8950006fd63d8620004bf7458910006dc52d8d10007be72d91100a77e721953005efe64593100a77c655493000fec5254810066fe76941100b7bc4050a30005ff7155132004ff764ca500047f755913202fbf429011011ebc4059231006fe6458a31005fc7050b1008e7c6559620007ed4218532027ee524c910006ef6248510006ff41d893001f7e74994100377f52551100d5dc73581210fdfc7250531007df4298c10
  | 4 => 0x8640397de43d8532006fc54d8530006fc6598620004fd7218131116ff52d8e2100eff5258810007f8705051004fbf5455210006fd6458b10005ff7254610027bc425091002ff84090110006ff54d81210377f5154910007f94388210006fc5498231006fe5418532056fd4298410006ff4118132006fe7518121006ff53d8a10057be4250b10005fc704ca5002efd76903102c6fd7318132096fd5258d20025fe72551100077e74d95100d7dc305853201dfc758801004dfe7590210006fe7458b10006ff5418530006ff6294130006fd74d8d210feff5258e21006fc4258e10006fd5458b100aefc52d8e20356ff52d8532007bc5299010007bc7259231007f15144010006ff421813113ebf41d9132007de6350810217f442c4210006fc4058b10026fc62d891038fdf544c931005ff748831031fdf544ca30006ff7158d21006fe6418532006ff5298630267f4428c710005ff744ca10005fd754c810007fa4088110064fe7694110056fe5298620006fc6558132006ff521813103ff9218821009ebe7619130116fc52d8d2103efe5258a10005f97094620005df735812100dff7554810006fc764c9510057d75d9220006ff4258d10004fc764c950006fc6518532006fc52d8c10097ee4258132007f95448110006fc54d8131007ed74d8910006dc42d8d10006ff5158e20217fa52c4210006fc54d8910177fb5484010006fd7558d21005fd755081004dfe7550610005ff745491003efe52d852002fbe5450d10006fe70d8d210066e6598810007ef744ca21096fd3258e20004fd711813220ff7548c510006fe741813204dfc75506100077f725941000eec425881001fbf5455010005ff7259631007be72d9130096ff7258e20004bd7418552006ed624ca500077d5354a10005ff76551212a7ec754c9200fefe625893105dfc744871000eff71181210377f5354910056fd628831003eff624ca10005ff7550d10007bf75d9110005f8705051015ff754440100afdc624ca30067df5354f10026fc52586100677f5254f1028fee54485200077d549411001dfe7550810007ef6488620107bf424c64001dfe7590010006fd65d8121007fa70d8a30027f85288110007bd5450f10006af64d891013f9f4050d32007dd5458c10006fd73d8910004fc7059541005ff7254410006cd6358810006fd5458c1027fee7488120357df31d8532007bd4350a10005ff7254631004fd764cb101467f51d9532327de43181320063f651913000eff4218121007dd534cb10026fe32d8910006fc65186201dff86588110005ff744c810007dd548c53117ff442c401000fee749881034efd5218532006ff764ca51006fd54d8d10007ed7588120005fc704c951025fc7255110007dc5218d10006ff6350b1002fbc64551100057f7154d52006dd6390010015f
  | 5 => 0x36fdc528c531005fd7550a10057ee3254b10006ff54d8530005ff7354a100e67c50d9521116fc42d8d21006ef624c910006fc7058a31005ff7350a10006bf644c910006ff43d8a102ffdc528c630006ff54586302cfde428c130006fe5458d200067d6548410006fe65d8132006fc42d8c10006fc52d8d10056f5219862001ff75154410006fd5458630006fc64d8a10006ff755864003eff6254a100067e6558810006fd54d812100fec5258810025fe7254d10006ff5498231007bf64551100067d5258650006ec5058810045fe7454a10026fe2058620095fe7290130005ff7454510065fe7558b10005fc704c941006ff54d89100fdfc725513100fec74988100677f5259710006fd64d862029fee544c920045fe7454e1001e7f5418151005ff7154e2002dfc74d8910007f9548401000efc2058810006fc5458a31007dd744c931005fd72943101f7f7524c510356fc20d8532006e9628401002fbf4155110006fc6458e20005ff7459710006ef53d8910027f842881100adfc7255230006ff7458d2101ff85094010006fe645813231fdc654ca3004dfe7550a10006fd65593100677f5454b10007cd524c93108e7f515962013ebc644c9100067c65d89300067f6590130006fd625441002dfe7454510035fc755091029fee744c920006ee75d8910007f5548c510007f55444010006fd65d8132006bd645881003ff72198121117df32d8d21347ee658852100dfc7254c10007dd544c931007f25044010007cd524ca30016bf7659010005f77158132367ee754ca2100dfe7250c100677f5355310004ff7358b1003ffb21882100065e6598c1004dfc75882100fdfc7254531056fe4298410006df634c52105dfc7454710007bd6454810007f87048610006fe42d8f10006ff54d813105dfe7448710006fc52d8e10006ed75d8910005ff7350810007f8705461003ef521d85200063d65992312aefe52d8132005bf74581210047d7518540247f87588210317dc404ca30005df7348630015fe7454810004fe70d8532116fe3258a31006fe65586200ffdd324c6200077e745941005efe7690110006fc641812101f7d7499410005fd754ca10005ff714c9510aefc42d8d20006ff51d8a10004fc765462013fbc6459132007d5324c710006ff6390220107bc4050931007e5618862002dfe74d951003efe5298010096fd5258e20025fe72941100fefe3258d21006fe7558e20004fc7648540006dc74d8d101a7f75484110007db6388110005ff765522102efc7058640007dc4218d10007de4298c10397f531d8532006ff75d8d21006cf6318910006ff545862001dfe754c810007f5424c51003ffa5288210006dc4258c10005ff76546200069d6498c101aff842c411034ff52118532094ff7258d20006fc65d8a10005fc7054640005ff734
  | 6 => 0xe6458a31056fe76881100bf7f5154a30005ff7154a10006fc42d8e1003ff93288210006ef6254910006ff54d8b10007ef6588620007dd744ca30004fd72d81430adfc72546301dff85088110006ff64d8132007ed524c910005bf744c220004ff764ca41004ff7158e200073d54546400057c7055152006fe54d8a10006ef42588100aeff42d8d20004fc7648630096fe52d8930004ed72d8c10005bd7498532007dd43d81320077d5454b10004fd768c640056fc5258b10187f742c4010005ff7350521004bd74d81520fefe624c650006fd54d8910027f85248110006fc5458221005fd73d8620006ff52d8f10006ff7158e20045fc7454a100057c7054d520065c65d8d10006dd6354c100ffde3258532006fc40d8910007ed7548520006ff74d893002fbe72191100adfe729423000dfe7259410005ff7355310006fc5458910006fc764c94107efd43d8930005ff7558810006ed6458810006fc74d853210f7f515493100dfe7254410006ff5458a3126ff7428c710006fd3218141007dd434ca102adff764c220007fb7388110096ff62485300ffbc425093104dfc75d8a10006fe641812100dfc7250c1000cff7648710007f14144010006fd6458931007bc52d9110006fd6458e20005bf7459532007dc5258c10006fc5258c10005f9708c6200afdd328c2200057d758c620006ff41588100067d65592310afbc4250a30005ff725053003dfc7254e102c5fa70d8e20007dd654c931005bc7050d42004fc7654630006fe4258d10005ff7154810007bd5450510026ff6288110006fc6458532017be5459010006fc7558810004fd72d8154006dc50d8d10005ff7154a310fff42158d21046fc64d9210027ec4250910005ff7354810027ec52d8910005ff754cb100d7de53585320d6ed3258a3110f7f52595310df3c5455121005ff7255130036fc7058650004fd76946200077c42d9510006ef51d891007eff4358e20004fd7218543006df6354d10006ff41d8532006fc5458620006dc5058c10004fd729865003dfe7250e10035fc7590110007dd424c53024ff6524c71001cff765471004ff85094210004bd741813104ff7515461000efe421812128fec54485202c4fe70d8e20006fd6294010007bc5219110006fe5458e20005ff7590110004fc76551200067e6499410005fc7059532015fc7454810027e86288110026fc4258610004fd7118154006fd5458620016ff7118141007dd434c810007f55484110004fc7648550047bc4055210007dd544ca30007bf5219130006fe6598121006d56344010006fc54d8b10006ed5358810357f621d8532017bc4055010007ed7218121007dd428c13001f7e6554810006fd541853004dfe754ca10006fc64d86201277e6554a31004fc70592312e7de424c530005ff714ca50006fd6350910
  | 7 => 0x8d21006fd73588101fff4528c510004fe764c951004fc7655110004ff7655131116fd71d8d210077f42d951007eff6354e20006fd7458810006fc52586300077e42d9530006ff7458650006ee54d8910005fd748801005fbf43553100ce5e5358e50006ff4258e100a67e70d9530006fe70d8554006fd5458a31006fc4058a31167f8528401005f7e5455310006ff5458221005fd7550410007786588110006fd735865013faf41509320377f72195100d6df31d8d2108d7e758c620006fd64d8d21007dc4258c10005fa709462001dfc754c810247fb518821000cfd72d8810006fe5258f10095fe72d91300d6ff6354d2111fbe6450a31017df4350c10006fc4258c10087be64d9220006ff75d8e200077f7459410006fc5418532007ed424ca10247f86588210055fe725931014ff45244010005ff7650a31005fd72d9110006de7258c10006fd6558121005fd7290210006ff6558d21004fd768c6500063e6599231005fc7055310006df4258c10027ed7518910006f77158d2100fee424c810005fd74943100073d5494240007f9538811003efd52982211b7fb42c4110006fc50d8e20354ff7158d21006ff73d8910056ff5298410006fd74d8910006fc42d8d10006fc7458d21004fd769464036fdc428c5310afdc524ca30006fd6250410006fd54d8131006fe75d8d21007ef725862001dfe7548410006fc64186202affa20d81320077f6550930115fd728c62009fbc42d9130007df634c521006fd5498231117f7218c521005fc7650a1003ffa5248210006ff65d8121005ff714c941007f77158d21005fd744851007ede63d8e2001dfc7550c10007df7348630006fc50d8d21006bd655923111f3c5455231006fd751812100ff72148410027ec42d8910007ed658862001efc50181512ffdc428c630006fe71181541477e65d9532006dd6458c10007df5298c10006ff7558d2100eff625481003dfe72546100057f7559132005ff75593100067f65d9130095fc7250530006dd634ca41297ef544852009fbc4050930005ff7355220006fd6290310006ee7558810005f8705461021ff742c4210007ed424c810007dd73d8a3002fbf7219110247fb53882100047f7558910006fd6418620007ed754ca210fefe52d8931004bd7418520006be6599010006fc7648540007f27188210006df42d8d1000fec4258810096ff21d8930006fd628c640007ec74d891002dfc749411011fbd7299231006fd6558d21005fd72d9130005fd7290010007ed5298132065fe7559310007f76158620004ed72d901033fee54885210377d741951003dfc7250e100173c5455010004bd74d9410004fd71d8e2009ebe70d9130006fd764ca41006dd634cb100047f7558241004ff7258640004fd73d85520aefc42d8e20006ef43d8910095fe72d9530006b
  | 8 => 0x6fd5458910006fd651813221ffa54c4210047be5450a1002fef4250910006fd721814129fec744c920006fe525823107eff53d8930006fc764c9500afdc424ca30006fc4058d210677f5254710005ff7150a31047bc6450a10006fc5458d20007ee74d8910085be74d9620287ec7588120005fd71181320057f7558121006fd6498620045fc7488210007f542c4210006df635091000efd52982102c6ff2118132005dc7050d32006fd72586500aeff42d8e2014ffa524401005dfe7488310007bd5490210006ff54185320067c641953017ff642c4010004fd764c640006fc65d8910005ff71508103373c54d8154017bf435081001f7f5454c1013f3c5455132006fc52d8131006ff42d8c10267f6428c710004fc7059132004fd73d891034cfe768c52123ff8748821003dfe72d9610015fc7458810006fc7558d21005fd73d922003efe32d8a10006ff5258d1003ff95288210004ef725911000eff52181210057d758c640006fd6558810004fd7218143004bf74582510077d72594102c6fe5218132005ff7250c10007f9748821023ffb438821003efd52980100473c5455210004fd711814223ff86488210006fc6498620007f561186201477f51d9532005fc7054b10326fd431813229fec544c920027f52158620326ed7218132086bf41592200e77c50d9521007ed54485200677f5155310005ff75505102afee42d8132004fd7690650005fd72d95300aefd42d8d20007f13188110005fd7588310006fd7558640006fd74d8a10006fc65d8132006bd648801004dfc75d9210006fd5458d2134fde32185322f7df524c530027fb428811005fbf4150b10006ff641813209fbf4290130006fc5218530006fd54d8530006fd6458532005dd73186200377f5254d10056fc4258b10007f542c4010006fe54d8810006ee65588102c6fd2118132006fd6318121005ef7255221006ff6558121006de6298c1004dfc754ca10027f84248110017bc7599010056fd5298620017be5450810006fc7648550197f452841100067d654c8100affb20d8e20005fd7550610007f5428c710025ff7250910087bc4059220005fc7055220047df4350e10006bf65d9130004fd7218141007bd5490010005fd7590310015fc7488010007ed42d813203efd6254a10367ec754ca21007dd32902300066c6518910005ff75883102dfdf528c130007f952c4210006ff7258650007df4218d1004dfc7550e10006fc641853207edc30d8930006fc405862002dfe74d8910006fe7058d212b7ee6488620006fc75d8e20005fc7050910006ff764ca500debf4358a41007dd324c64005fbf42507100fdfd724c62003ff72148610006fb6098121006bd5458640006fc74d8e20006fb6098132057f82088310004ff7648640056fc52d8121047bf4350a10006ff545
  | 9 => 0xd525461003dfc72d9210006df65d8d10006ff411812100dfe725041004dfe7550e1009fbf42d9130007bd72d9110006fe529863033fec5488521006fd6418532004ff7258e100afde704ca30005ff7155220006fe52181310d7df31d8d2102dfc7448510006fc5458d21006ff54589101affa42c4110004fc7059121006fe54d8132006ff42d8d10007f57190210027f9428811002fbd7219110006fd7558810006fd7518141007f57188210005fc7050a30007ef7548520005fe70d8532007f5618c620006ff65d8a10005ef7254521005f972c4210006ff64d8e20005fc7050931006bc6519130004fe764ca10007f76158532006fc64d8d21355ff7158d21006fc5058b10026fc42586200677f5294310006df63d8910026ee32d891001f7c5055010006fc7558b10006dc6218d10095fc7254530006fc54d8a102a7ef544c920007f57188010197f44284110006fd7358620006ff64d853235fee544ca210047d75d9010006de4258c10006ff42d8e10027be4250910006fe64d8132007dd5398132006ff6290110006fe7058810046fe5498010016bc4059010004fd721853000eee4258810006fc4218530006ff51d8930004fd7298640096fe3258e20007fb748811023ffa5488210005fc7654e20004ff7654640006fe6458b10167f84284010005ff715531003fee424ca10065fc7548710007f5524c71000eff764871011fbc4259231055fc7259310006fc7558a310077f6550910006ff74d8d2105ff74150710006fe4258e10006f5614c640006dd63508100d6de6348410006ed6250810006fc4258630017bd7599010006fd655893100ef52118520015ff7555010056fc42d8121006fc52d8530007dc635091001dfe7550c100077d5254410007f571d9610006fd54d8b10005ff7488110005ff7150a10005ff7254f10097de325813208e7e6588010045fe744ca1005dfe7459710007dd534c910006fe75d8a1000fef7498810037df5354d10015fe744c810005fc7050d21005fc7054e20096fc62d89300074d5354932006fe651813205fbe5459310007f942c41100fedd3258e210aefe42d8d20006fc7648630006fc5298231006fe5458a10007bd5450d10017bc5459010007bd4250710006de42d8d100057f7155152005ff7448710006fd5458221027ed74189101fff4428c5100078d4350932004fc7058a31005fd72941102c6f92018132006dd3218131006ff735864035fee744ca21045fe74d961014ff44244010006de6558c1000efe6258810007f5719001000efe521852001e7f7159410006fe5498221006fe54d8520006fc7518132005ff7358620006fe7458810026fc52d8910006fc64581320577c5254b100ffdc424c931036fc65d95100077e5259410005ff7250e102aefd52d8132006fd6350a10006fc5458e20
  | 10 => 0x81101277c5259631006fe7458d2134fee52185320e67f5158a51007fb6098121007f55148710096fe2058e200063e6599010006ff5458e202c6fd3218132006fd41181210dfbf43d9121007fa7688110026ee7618910006fc42d8530006fd64581320a77f5154930326ff5318132097bc4250930396fd43d8532056ff4258b1002fbf42d9110056fc52d8b10007bf75590100feff6254931006ff54d8a10006ff6358620005fd7198132045fc7454e100077d5294210006fd624c6500b7bc6450a301477c754c951006ff73181410047d7518542006fe65d8620026fd7688310007ed744c920004fd7318121005dd728c6300077d5454e10116ee3258a31005fc7055120004fd72d8543006ec54d8910027fb424811000dfc7290010005fd729423002fbc42d9110006fe65d8532004fb7644010006fe42d8c100ffdc524c93105f7c5455310096fd32d8930005ef72551200367f54586502c7fa2018132004fc7655210006ff5458d20116fe42d8d21006fc4298231007de52d8d10007ef42d8910006df634c950005fa7090620005df73551310377f5454910005ff7454e1001f7c7299410015fc7459410007db704ca3000efc20181210fefc5258d21015fc7454c10005ff7355120096ff625493003dfe7290210005fd728c6400377f535511003dfe7250610005ff7558b10005df735523034dfe768c521025ff7450910006fd7418132257f6544c710004fc7059131356fe52d8532017be75990100aefe5258a3005fbf4250f1004dfe7548610017be6450810006ff73d8a1000eff2158810006ed73d891002dfe744851032cfe769414007eff43d8930026fc42d891007edc6388110006fc64d8a30006ff764ca4105dfe7494310006fd65985320aefd42d8e2002dfc745451038fdc504c931007df4258c10004ff7358810027fa4288110007bf5459010007de704c93100efd42181210077d5454c10006ff4258c10005fd7194240005fd748821013fbf41d9132355f77158d21004fe764853000efe52588100077d5294010006ff649853231fdc504ca30307df428c630356ff21d8532116fe52d8e21007dd4318132006fd65d8532004ef7259541006ff7648640005ff7259131006fd6458a31006fd5118121116ff42d8d21096fe7058e20027f971881100a77f52d9530006ff7458620377df428c531116fd42d8d21007d5324c510005ff7454c10006ff6350810006fc42d8131006fe549862000dfe72900100077e42d9510006fd435881013fbc744ca40007ef4258810006fe6558e20004fc7650630006fd764cb10004bd74d8c1004f7c5055210006ff6418121007de4218d10006fd6190220006fd7458650007ee7558810116fe628c640006fd5358b1000efd6248410006fd5418532095fc7255130006df7358d21006fc74d89100077
  | 11 => 0xfefc4258d21007bd4350b100065d6598c10006fe52d8f10007dd6350810396f631d8532005fc7059121006fe7558a310063f65d9130006fd6558b100afdc3298132006fc54d85201bffb52c4110007ed42581320067d5418151006ff4258630006ff75d8a100677c5054b10006df635451016ffb42840101267c505963103efd52d8520006fc6518132017bf4255010006ff6598132005fe7654910005bd7418620006dc20d8d10006ef54d8910027fb20586202c7ee4218132006fe54d8931056fc42d8b10007dd428c531006fc7518121006fd5358620006df64d8d10004fd7648640005f7714ca10007bf529923121ff854c4210157f74244010006fe74d89100fefe5258e21007dd43985320047f7558630116fc5258a31007ef6250910006fc50d8910016be5418141005ff7355110387dc404c931006ff5258e10006ed625441005fbc5455310005fd71d8154227f752c42100077e725941003eff7688010207f7428c510006fc54982210aefd6254a30006df634c940005fe70d9521004fe70d91210ffdf424c931005fc7650a30004fe769062000fee3250810006ff635091000eec2058810006fe54d8930006ff6350a10005ff7650620004fd72d8141007ed65885210afdf424ca3004f7f5454e10006ff65d9210004ed72d9640006fe64d8d21007bd6455010006fd711813202fbe7519110005fe7650910007dd428c630057ec5254b10005ff745881005fbe5490310006fe6598532006ff5118132006fc6518121006df52d8d10007ef65885210067d5458650006ad6458810006fe42d8e101477c754ca50005ff7150e20006dc64d8d10116fc4258a3101fef525481003ffa3288210004fd764c650006fd6354b10004ff7258630005fd7348640005ff754c910007ed42181320067f6588110006fd5458e201267f52d8d51006fc7418132005dd728c5311277e7299631006fd64d8121006fc4058e20007ed625081003dfc72902100077f72d95101476c505493200cfc7058810006ff6598121005ff7550b10095fe7294130026fc525822100dfa70d86200aefe42d8e20026fc5258910007f5515071008e7e65d96200047d75185201467c6559532006fe7518132004ed7218131006ef5258810026fc52586200aeff52d8d20005fc7048650005fd739422003ff95248210005fd74d8a10006fc54d8810004fd71181530063d6559231004fc7654520277f7528c710026fd4258610006fc7458a31004fd72d8153347ef5488521007fb65881100ffee52585321e7f6524c5100377f5155110217f642c4210006fd5458d20004dd73d9410006fa70d8e20027ee325491018ff752c40100e67f5358a51007ed544c920004fd71d9220006fc5058620004df7359110005f7714c8100066d6598810007df63549100047f7559110027fb628
  | 12 => 0xc40d8a10056fe5298410006fd6198132004ff7159132005fd7590110006ff54d8520006df41d8d10026ff42d8910115fc7259231006bd6458a31007ed5258532026fc4258910005fd7548610056fe4258b10015ff7455010026fc4258221006fd5258231007fb6488110005fd7550b10005fd7194220027f8208811002f7e5455110116ff52d8d21327ed72181320077c4219530007bf5299010007ed42d85320067c65d891000efd5218520006ff51d8532027ec62549100065e6558c10007f97588110006ff52d8c10027fa4248110005ff76553100047d75d8c1013ebe64d9132045fc744ca100367e76195100d6ff7358d21005fd7588110027fa7058620006ff42d8131006ef4158810007be42d91100077d72d9510026f62158620007f54148710005fc7055110004fe7694620006ef6288110006df6394110006fc54d813235fec744ca21025ff7254910005fd7494110056fd6250b10006fe764863019ff74284110065fe75903100077d6554810097dd3258e20006ed6248640004fe70d85521d7f86488110007de5298c10005ff75881100ddbe748c521065fe7550b10036fc5058650006fc64d8930005ff7654a31356fd72d8532007fb7588110005ff7255010027fb528811003dfc7294210005ff7254710006f5614c6200047d75d8810047bf4255210005ff7250410007bf64509100067d65588102bfec6588620007f95244010004fd7648650005ff725063105dfe7454f102ffde428c63003fee3250a10006ed6294010007de4258c10004fc7655121006ff7558810006fd6598121006ff5358810005ff7155120046fc5498010006fe764c951006fe5458f10396ff53d8532004ff7655221326ff4318132007fb6588210006fe42d8d10004fe764854023ff854882100e67c6559521005ff7255231027f94248110005fd754841008d7c754c220004ff725865027fec7488120006ff54d8810006dd6354410026ff425862000dfc7294010065fc75507100377d7219510005fc765091004dfe75d8a10097ee525813235fec544ca21006fe6518620007df6358d21007de54d8d10055fc7259710017bc729901000efd624c810036fd7694310015fc744c81001f7e655501034efc5218532005fd7654b10007ed5488521116fd72d8d212c6fd5218132006fd54d8a10325fa70d8a300077d5354b10006f96244010004fe764c91000fee4258810007ed748812011fbf4259231007df5218d10007fb6098132006fd6350810027ee42d89100066e6558810065fe75507100069d6458c1002fbc6450910006fd6558a3122ffa5448210004fc7648530005ff73545210377f52d951036fde428c531006ef624c9510077d5454910006fd74d8532006fc5458a10016fc549821004fef5254a10355fe7618532005ed7294220006df5258c10
  | 13 => 0x8e10006fe5258d1002ebf4258640047be5450610006ff5458a10006fd61546400ffde424c931167fa4284010055fc7254f1000eff21181210d6fd6354d21005ff7354b10026fd4258620006fd639022005dfe7454b10007f5428411003dfc725061000fef7598810006ff6458620006ff4358810006df6350510007d8704ca30006fc75d8d21004ff7655220014ff7650710006fd5498221247fb5488210007fa50881100bf7c6554a30004fd764ca510debc4058a41096df3258e2000efd62548100377c6554910006fd4318121006fe70d8532006fd7648640006fd421853014ff64244010004fd73d85540ffdd424c93102fbf4150910006fd6458d21005ff7350b10006ff54d813200ef92018121007bc52590100a67e76195300065f65d8d10107be6450931006fe5418520007cd534c92000efe5218121116fc20d8d210077e5459410396ff43d8532005ff7559010005fd768c620005d4714c931004dd7318520006fd54d88100afde424ca30006fe7648540026fe705862034efc4218532006ed625041007fde439813202ebe70d9110056fd42d8121006ff5498620006fc75d89300fefd5258e212e7de524c530356fd52d8532005fc7650e20005fe70d9121005fc7054910005fd73d9121006fd42586302cfde528c13000ffa2018121046ff5498010005ff754841004dfe7588210006ff6354620006fd5298630157fa5444010096fc5258e20016ff7650710007f94284010005fc7655230007fa70d8620065fe754cb10247fa7588210006fe4258c100aefc20d8e20087be6450620006dd634c650017be5450410007bd54508100063c651913000dfc7250410006df4158c100067f6590110004fe70d8d21006fe5458231006fd70d8554367ef544ca211267f765963100efd2118121006fe5458a302afde32d8132117ee429853204f7f52d9610005dd7394230115fc7250631006ff421853011fbc4050a31257f4544c710007f54244010006fe641813203fde324ca10005fd72d9510006bf6488110007f5428c510006fc5058d21004fd7690620006fd65d8e20006fe5418132006fc64d8121006ff4298231007ee5418910005fd7390220006fc65d8532007f55150510006df7358e20096fc5258d20007ef74d8910006fe6598620317dc644ca300d6fd5358a3102fbf435511027fee5488120096fe32d8930006fe70d8a10006ff75d8930006dd63940100afdd424ca30006fc74d8d21006ed54d8910006ff5158810027ef7518910005ff7250610006ff65d8e20016fc4018141056ff42d8121006fc5058a31227fb54c42100aeff52d8e20007ed4298532005fd754cb10004fc764ca10004fd72d815100fde324c810005ff744cb10006fd53d8910006dc2058c10006ec7558810004ff7159220005fd731812101dfe7588010006f
  | 14 => 0x65fc7588310006fd42d85300aff820d8e20006fd54d8132006fe54181310067d71d9530006cc6318910047bf42902100debe644841023ff84088210035fc75d8910006dd7258c10026fd71d8910007d86388110005e8704c9200066f6518910007bf7259231096fc4258e20006ed65588100dfbc744864022ff85448210007bf52d91100077c4299631055fc7250f100377f5294110006fd7158e20005ff7154b10006fe7558b10096fc4258d20007dd434cb10006fe54588100077b6588110006fe6558b10046fd5498010006fd619424025ff7544c71007fdc3058e20007f95488210005fc76552200067c6419510006ff62902101d7fa7488110005fc7050620007df754c93103f7e5254a10006ee7058810357f521d8532006ff41d8d21004dd7698c10007df5258c100047d75d9231006ff41d8e20007df754ca30006ff7358650004bd74d9620007ed544ca210fff8204c6200077e72d9510004ff7648650007ef75d8910006ff5258c10005fd744ca10006ff6118132007bd6455310005fc7655121004ff725824105dfc7458b10006fc54d8931005ff7355221017bf7599010005fc7055131005fc765093005dfc7454b10007ed5218532006ce6398810007f5524c5100feff4258d21007bf72d9110056ff42d8b10006ff64d8d21006fc74d8a10007ed744ca21005fc7055221034fd7694310006fe64985320e77c6559521007bf521911013dbe74985320aff8208c22001f7f5454410005fd7655310006dd634c620005ff7155110007bd4250510007bc7259010006ec40d8910197f642841102c7f92018132006fc7458810006fe64d8532006dd63504102c7dc3018132006fd42d8131006ed73588100b7bf4250630006fd5458a10006fd5498620017bf4290010006fe7558620006fd6458121005fe768c620006ff639422011fbf428c640006dd638c22037fdf528c531007ef52d8910006fe6558a31006fe4218530006ff65d8a30006fd7558e20107bf4250531006fe64d8121017bc4050810004de7618d10005fd7650b10004fc7655132005fc705093030fdf528c630047bc4050a10005fe7654a10004fc7650620006ff52d8d10006ef73d8910006ed7458810005ff7448510006fe764ca10016fd549821007edc6358e2003efc52d8a1000f7e5254810004fd72d81310377f5254510006fc76485301fff6428c510006ff549822104efc65d9610005ff7348650005fc7655210006ff42d8530006fe7648530006ed74d8910006fe64d8e20067f85094310006fc5498620006fd75d8e20006f5614c650005fd744c810007ed7448520007f954c4210006bd64546311d7fb418811002fbf4250510004ed7698810006fe7558d210277c52549100063e6559231007bd5450a10116ff4258a31007ef5258810005ff7548610006ff52d
  | 15 => 0xc7055230237fb5448210056ff6250b10007f551485100ffdf524c931007e7714ca210acff72d8d20006fc7458e20006de63588102b7ec64886201467c50d9532026fe42586200aedd32d8d20007dd714ca300adfe72d923027fec5488120005fe7655210006ff531812100dfc7254410006ff6350521006bc6519110065fe75487100067d6558a310afdf524ca300067f655053005cfe769011000ff9201812105fbc40553100077d6554b1005fbf4350b100077c429941010f7f5254531006ff65d8910115fc725463128fec7448520004ff7159620065fc7550f10356ff73d8532057f72148710006ff7458e20067f75154710006fe425863001cfc7059410005bd748c650005ff72552100047f7559121005f870485100ff7c5254931056fc2058b10114ff7358d2103fee524ca10007bd755901004f7f5255210006ff54d89310367e70d951002f7c5455110006fc6458d21006ef629011000efc52d8810047be54d9210007f5544c710007dc54d8d10006fe5498630116fd6250a31004fd721855403efc42d8a10007ed6488620026ff62509100077f42195300067d6588010006dd7458c101eff6544c510006fd72d8554006fd7458a310077d5454410397f631d8532007f7714c8100debc40d9121006ff6354b10007ed424cb100bf7f5254630007ed5258132007f7619862002dfe74881100057d7598532006ff6350620007fa6018132005fd7290310006fe42d8530004bf7458e10007dd5358532007ec7558810006fc64d8132086bc648811002cfd76903100ffdc3258532007f9738811005f3c5455310006fe54d8532004fd764ca4002dfe74941100debc6459121007f95188110056ff5258b10066fe6559710006fc5458a300047f7558d20004df7359540006ff7518141025fb724811002fbf4250d10006fc54d8930004fe70d85541475c5154d32025fe72d9510005f9709062004f7f5454610006ec65d8910006ff54d8930006ee7458810006fd4298231005fc7054541004fd71d953207fdf3198132026ff425822100fee6254810005fc7054931006ff71d893000eef7658810006fd64d8132006ff74d8e20026ec52d8910004bf7458630027ec7418910006fc5458f1002ff74150510005ff7458b10006ff7418132026ff4258910006ff63545210077c7459410005fc7054a30006fc65d8d2111ebf7159231035fc754851000fee524c810005ff7254d10017bc4259010055fe7250f1007eed32d89302c6fe3218132006ff7218141005fd7294130006fe42d813101f7f5494010026fe42d8910045fc74d961008f7c6559620107bf415093101f7f52550100b7bf4150a30006ed624ca40027fb5248110007f94188110027ee7418910055fe7254710004fd764c62000ff42118121005ff7650b10006fe54d8e21006fe5458e21
  | 16 => 0x4810287ef5488120017f8409001000dfc7259010007bd435091000fbc425081000dfe7255010027f82058620017bf729901004f7f5354a10117bc4250a31006df21d8d10005f87050610006ff7358620006fc50d8a1003ff8528821003efc52980100077d54942100ffdc204c931006ff6558620006fc541852008d7e7518620005ff7250f1028fee74485201457c75591320af7c5254a3000eee5258810006dd6348410004fd7118143006fe764c910004fd7218553006fd65586200065c6518d1008f7f5359620006fe75d89302c7de3218132006fc40d893004f7f54942100377c5054910026ec42d8910057f52198620005ff7550e1007edf3158e20006f76198532006ff76486500afdc204ca3002fbc54551101477c655953208e7f51d895000eef7158810047be5450e10006fe54d8f100077d6550a31006fe6458810006fe6458d21006bd4258640006ff4158b1003dfc725521000efe3258810026ff525862005fbe5450b1017ff652c40100fefe4258d21327fa3018132007ec75d891038fde654c931007bd4290210006df6350d10007bd5490310027ec5254910326f9301813205dfc7488310005dd7390230006ff63d86200069f64d8d10056fc52986200bf7f52d9630004fd72d8554005fd7550e10005ff7454810005fc7654620006fd54d893003efc5258a10006ff5458a3002fbe5490110007f870506100aefe52d8d20006ff521853010f7f524c650086bf41d894012cbd7699231006ed435881007eff7358e20007dd3254531007ec5418910005ff7155221056ff52d812100efc5298210056fe42d8b10006ff5458f10004fd7218550006ff6398121356fe32d8532006fc641813203dfc7254610004fc764c91003efc52d8520056fd5298410006ff5258630006df634851001f7f53548100bf7f5294230004fd71d9120217f852c4210006ec74d8910005ff71552300077d5494010006cf63d8910005fd7550710006fc6458121005ff7550910004fc7654530007dd32546300cc7e7619530005ff7359220007ee549881034eff421853203efc5298221027ec7518910005fd7550c10005ff715513100efd3218121057ee424cb10157f85444010006dc72d8d10006fc5058e200069c64d8d10006fc5458231327de5318132087be6450e20005ff7550c10177fb5284010006fd62547100fefd4258d21007de635481008e7f53d895000dfc7255010006ed6248410017be5450c100077d5454610006ff74d8910007f7714ca10387de644c931005ff7350620067bf54553100873c5455220007df54d8d10116fe4258a31004fd71d964005fdf4350f1015ff75244010004df7358221006fc5418132004bf7458d10004fc7654540086bc6459220007fb7188110065fc754cb10007bd429001020ff7528c510006ed7558810005f
  | 17 => 0xaefd21d8e20004f47158d200067e6558a31005fd701855413f9c4150d32035fe7590110006bc64d8930006ff6498132007b86488110006ec50d8910006bf6454530006fc649853203efc4258a10006fe5258e1003ffb20d8620005fd75d91100377c7419510006fd75d8532006fd6194220006ff7458810006dc75d8d102b7ee54886200073d54506500677c5055310007f87054510006ff5298231006fd6250710006fc75d8532027fa5288110065fe7550f100057f7559121115ff7358d2134efd42185320073d5454541006ff6558532005fc705452124ff4524c7100077d525471003efc42d8520006af641891008f7e6554e20004fc764c94003dfe7294210006fe74d8a1000efc4298210007f87048510007f54148510006ff6254510007ed64885210a77d7219530004fd72d8553005fc7655130006ff65d8930006ff52d8530017bf42590100d6df3158a31006fd6354910006fe6458620217f842c4210026fc20d8910006df2158c10006ff64d8910004ef7258630005ff7254510006fc545881003dfe7254e10017bf4155010007dd739813203fbc4250a10006de6258c10006ff5418520397de53d8532005ff7454410047f8409021013ebe644c81004f7f5154a1001f7f5459410005fd72d9610006fd5458f10027f92188110006fc764ca1004f7c6554a1000efd5218121006fc64d8910387df414c931006ff54582310dfbc40d9121096ff4258e2001dfc75508100063d659901008e7c5059620005ff744c910006fd6154620006ff5418132006fc54d8532006fd53d8a10026ff52d891000fee7598810006fc5458e2105efe549841002dfe7454d10006ac6418910015fe7454410006ff4318121006df74d8d10357df73d8532006fd6498121317df414ca3008f7f5159620027ef7418910006fc549863001efd7118151004ff7358640006ff75181321a7f75284110007fa70d9610006fd7318151006fe6458121006fc5418131004ff764ca40004bf7458d2015ffb544401003dfe7255210035fc7550510007de5218d10007dd324c650006de5258c10026fe425891013fbe64d9132045fc74d8a10007f954482100077f4299631026fd4258221006fd74181510fdfc7259131005ff7150b1000dfe7294010006fd54d893105dfe744cb10007dd528c1301affa52c4110007dd54d8d10007ed7458810007cd534ca21287ee7588120116fe628c650005ff7159132035fe7550510007ef5418910004bf7459521005ff7454a10006bd541814101f7c5459410007dd32942300677f5454f1000efc42d8810006ff52d8131007dd524c530007eb6288110007df654ca300077e4259631006fd72181511277f5154a31006dd6350c10005ff7650d21026fd625091000dfe7254c10006dd6558c10006ff75d8910097fb2058e2001f7f515
  | 18 => 0xe7290310006ff41d89100063c6519110006fe52d8e10006bf6494130006fd62546310067d6550631006fd7458d2102fbc4055110006df53d8d10007ed5418910007f23188110004fd731814200ff72118121396ed72d8532096fd4258d20006fd5418132004ff7654620025fc7254d10007ed524c810005ff7454610056ff52d8b100feff5258d21025fe7250d10097f8204c220005ff7590210005ff7354910006ff73588100077d5294310005ff7158e20006fd5418520006ff6294110007ed7558810006fc74d8930006ff64d8121004ff7159542005ff73509100066c65d8910006df634c910005fe70d8d21357de32d8532096fc52d89300077d655501005fbe6455310006ef7558810006fe74d8532004ff72582310077f4299410117de3298532005fc7655132006ff5458810006fc65d8e2005dfc7454f10006fe655893102dfe7454910006bd71d9110116fc2058a3110f7c505493101f7e72994100066d6558810006ef535881001f7f72994100d6fd7358a31006ff54d853209fbf4250530007dd3250531006fe6518121006ed53d89102aefc42d81320067c705963104dfc75902100067d6590010005fc7650d2106f3c545512001e7f5218151006ff75181210aeff21d8e20006ff6458e20006fe5458d10006fd614864013ebc40d9132007f95444010116ff5258a31035fe754c910096ff4258d20116ff21d8d21007bd5450410006ed624c81000fec4250810007dd3250630004ff7650650006fe6458931005ef7250521006fe5418121116dd32d8d21006e96244010006fd6418132006fd5458a30006ff5498630006fc65d8121006ff65d9110005fd71181541dff87588110006fd7558a3103efc62d8a10005bf7459521005fe70185540bf7c5054a3003ff842882100067f65485300aefe52d8e20055fe72507101eff4544c5100077d5454f10004ff7358650005fd765501003efc4298010006fd764ca51116fd52d8e21006ff7318121006fd7558620006fc401813234efe4218532006fe52d8c10006df75d8d10005ff7590010045fe74546102efde544c5300d7df315853201f7c749941007eff6350e20007ed5488120006de7458c10005fd7550910006ff4158620007de5498c1003eff42d8a10007ee7458810007f9438811013fbc744c94113f9c6450d32035fc7588110006df634ca100077d5354910007fa70d9210037bf5455110005fd754c910035fe7550910006ff7458a31006de52d8d10004fe764c940006ff7558b10006fd65590100d6ff6350d21007d4714c931005fd7694620007be52990101457e75985320077e52d951004dfc7550a10005ff7359121006dd7558c10006fc64d8532005ff7454f10056fc4298620054fd7298410007bb6488110027fb21881102d7de548c13001dfc7590010006ee74d8910
  | 19 => 0x8141007bd75d91100077e6550810006df5158c10006fd5458810035fe75d89100377c65551100ffce424c931007e8704c9200e67e65d9521004fe70d953202dfc74549100a77f5254530057ee3250b10006ff6250510007dd4398132007be5219110007f5528c710005f57190010025fc7250d100afce424ca30006fd54d8e2100efc7058810006fc4058810006ff5118121006ff4158a31005ff715491003ff85248210005ef7254620007f552c4010006fd649853201efe655941003eff4298221006fd764ca40067ef5254b10006fd764865003eff6250a10007ed524ca10007be4259010007cd424c931005ff7654b10006dc63d8910005df7350630006fc40d853202eff41586402ffde528c630006fd54d8532006dd634c640006fc5258f10006ff5418131006fd5458e21006df51d8d10006fd64d853209fbf4150930006fd74d8e20005fd71d953200eff42d8810006bd6454410006fd5418131006fd5498630005bd748c521007dd434c910005fc70551302b7ec5488620007f220841100067f65d8910006fc75d8910006fd73181410e67f51d9521026ff5258221005fd728c650096fe4258e2000efd6288010006fe52d8d10247f850882100debc644853032ebf4218154007be52d9130027ee52d891033fec6488521007ed52d8132006f96018132005fd75d8910005fd71d9620024fd71d8910006df624c530117f421d8d21026ff5258910005fd74484100d6dc30d8d21096ee32d8930005df7350531006fd635862007efd6354e20017be72990101f7f7544c5100047d75d9220006df628c130056fa20d8121007dc52d8d10026fc2058620006fc54d8f10007cd424ca300063c65d9110356fe20d8532007fb7388210006ff64d86200065d6558c10095ff724c220006fd54d852002efc64d9110006ff65185320d7de4358532006fd6354521006df5358c1005dfc745971000fee525881013fac6450932006ef51588100677e6554b101277f5259631006fc649812124ff4424c710006fd6294310096fe4258d20005fd7488310005ff72545311365e53d8d5103fec4250a1002fbd751911000fec7598810007dd5318532015fc7494010006ef42d89100fefc52d89310fefc2058d21004ff715953201f7d7299410006ff629013000dfc725941007fde63d8e20005ff7254630007fa408821007ede63880100e67c6548510006dd634c810037f85094110217f652c4210004df7359510007bc7559010267f6528c710055fc7290310047bf4155210026fe4258221096fd4258e202c5fe70d8e20007bd5450610006fc54d8e21116fe52d8d21025ff75549100377f7419510007ec549881000fed75988100677f5459710005fc7050e20006fd545823109ebf41d91300377c7219510037f75154510006fe659813202cfd71d9110055f
  | 20 => 0x6fc6558d21007f952c4110327f93018132006fd75d89302bfef548862002fbf4350910005fd74d9610005fc704ca4003eff429801001eff511815101f7c52594100afdd3248630035fe7548510117ee5298532006ff741815103dfc72d9610005ff725071014ff85244010007dc63549100077f65549100ffdd324c521006df4358c1001e7c5059410005fc7059132006ef6250910006ff6418620187f654c401003ffb4288210007df744c93103eff42d852026ff6548c7102d7dc548c130035fc7550d10006fd3258640006dd3258630006ff71d891003ff84248210006dd635481000fed7498810027f72148510006f571d8a10004ff7655010045fc7494210006fc764c9100a77f5294130007df744ca30016bf7159010004fc7655130007bf6455210004ff764c8100fefc42d89312bfee6588620006fc5258231357ee52d85320977c5254930006fc7058d2105dfc744cb10045fe74d8a10006fd6150620007f5544c51001f7f5254c101dffb5188110006ff7218151007ef7448520006fe42982310047f7558d100ffdd714c931056ff2158b10006ec7458810006fd615065005fbf425931001dfe7558810006ff54d8e2134eff5218532007ed424c910006fd5218131056ff42986200b7bf42d92301477c50d95322c6fc521813207eff53d8e20004fd73d8a1003eff4258a100067d71d9510005fd72901100077e4299410006ff54d8f10006ff6458d21006fd659813233fee6488521056fe5258b10006bd6494010007dd535813202f3c5455110006ff5458e21005fc76551200c4be7619130005f57190210006df43d8d1003efc429822100dff725081003efe42d8a10007f552c4210006ef624c941006ff4158d21005ff71551300aefd32d8e200d6ff53d8d21004fe764c950006fd4358b102aefc52d8132027fa5248110055fc7294310004fc7059521087bf4159220005fa708c6200067c7059410005ff7550410006fe6498121004fc70592210dfbc6459121007ef54988100077d6555310006df6354910027f93288110006ae6498810005fd7448610007dc5498c102acff764c220005fc7050a3121ffb42c421005efc5498410005fc7059521117dd32d8d2105fbf4255310004fd73d8542116fe6258a31054fe7688110006fd3218151006ff7118132024ff7258910056fa7688110007be52d9110005fc7050810007ef754c9200063e6559010116fd32d8d21006fd71d8a10006ef4358810006f5618c640005fd7348650005fd71d8e2036fde528c53100efe3218121005f87054510056fd6248710056fe42d8121096fc42d89301347d7699631004ff764cb10025fe7254510006ed6254810007bd6450810005ff7259531007f95388210007de5258c101dffb5388110006fe5258c100aefd52d8d20005fc7054930004fd731
  | 21 => 0xf544c53038fde754c93103efd42d8520006fe525863032cfe70d9640007fb7488210096ff5258e20007ed54886202dfdf548c13000efd429821007edf31d893004fdf5354e10004ff73586202c6fc4218132005ff74882100aefd52d8e200afdf214ca300077e54d9510007de5418d10005ff7250d100e77c6554d2100efe42d88100077c72d95100067d6559010007f942c421011fbe7299231006fd435862007efd53d8930006fc529863005fbe545071005fbc4050b10005fd7294210005ff7548710007dd534ca10006fd65181211b7fa54c4110005fc7654910004fd71d9520006de5458c10007bd5450b10257f7424c71031fde754ca30007f24044010006fe521853005cff7650410006ff6354810005ff7354620006ff7458b10007be645481013dbc745813200fbe4250810006fd54d8f100adfe72d96300e77f51d9521006fd6250631007be525923102fbe5450910055fe7259710004fd71d893001dfc7559010005ff7359620056fe52d8121004ff7655231047ef4250a100067f65d9110086be64d922002dfc7488110007f571d9210007f761985320063c65d9130005fe764c620006ff75d8532057de324cb10006fd7558b101d7f87488110026fd21586201467c654c9100a67f51d9530006ff64986202efdc544c530006fc70d85320afee4298132005ff7154931005fd7548710007dd754c931007ef7558810096ff5258d20004fc70595420067f65d8930006be645881012ebd3259231026fd52586101d7fb4388110167fa5284010026ee42d891003efd42982210057d758c5210ffdf214c93121ff654c4210015fc744841001fdf5354c10005fd75d9210007dd754ca301fff6528c510006fc50d8930007ed5498810006ff764ca40006ed71d8910004fd721854005eff7650410006fc5458d10027f9528811013fac4050932006ff6558132005ff7488010065fe7588310006fd635052105eff5498410006ff51d8d21005fd7488110006de54d8d10006fd6354a1003ff86288210006fd73d8a10007bd5450c1014ff6524401000eff6250810005fe71d8154006fc4258f10005fc7050a10007dd534c810006fd7458b10007f97488110007ed75d89100aefc5258a30297ec75485200ffde524c931114fd72d8d21005fd7294010057fa20d8121004fd72d8f10005bc7055142035fc754c910006fd628c65000efc52185202aeff42d8132006ff51d8e20027ee424c91007eff73d8930005fd7550510006fc5418121005ff75506100afde524ca30006fe54d8d20007df5498c10006ee5458810035fe75d9110005df7154d3202fdf4350d100e77f53d9521005fe70d8554117f721d8d21007ed4298132006ff7418121007dc42d8d100069e6498c10017ef4250810005ff7259710034fd71d9510006f5611853204f7f5254e10
  | 22 => 0x801011ebf765923105fbf4290310045fc745461009fbe7219130007ed5218132006fe52d853003ffa4288210006ff64d8930006f72118530006ee645881000eee3258810006ff625461008f7e65d9620006fe70d8e20035fe7550d10006fd7318121005f57188010006ff64581210377c5055110007f571940100077d7459410007ed6254810007fa70d8e200d7dc30d8d21006fe764c940005fd73d962003efc20d8a10006bc7059010006ef75d8910056fe42986203ae7f5218154007f97188210007bd5490110026ff21d891003ff820d8620006fc6558121006fe5298231086bc4059220005bf7458132006fe65d8d210077d52545100a77c5054930006fe6458e20006fe6498132006bf64485300677f5454710006fc764c940006bf65d911003ff94288210006fc70d8d21006ff6518121006ff5358b10006fd6558e20006fd65d862001f7f5454810006f96018121004fe70d9132006fe54d8c10096ff42d893005dfe7458b10005ff725531002efe7058640006ef74d8910004bd74d9631217fa42c421003efe4258a1002dff75551100ef3c5455221006ff64d8a3003eff52d8a1001f7f5355010006fe52d813105efd54984100577e5254b10006fd74d8930005fd7398121006fd7358b10006fd6290010026fe52d8910006fc64d8e20006bf64d8910005ff714ca4003efd4298010005fd71d922003efe42d8520056fd624cb10006ff6354a100ce7d32d9530005fd744cb10085be748c620006fd624c640007dd5498c100fff7214c521006fd43d8910004fc7059531015fe7448410006ff5458d10005f471581321d7fa5488110006fd6398121004fc765052000dff7450810015fc74544100077c42594100077c7259631006ef65d8910006fe7458620004bf7459510026fa2058221005ed7290220005fd7290230005f972c41100377e72195100367f5258650006ff6558e201073c5455131007dd53d8132006fc6558620004dd73d8810025fc72d9510026fe5258620026f52158620004fd71d9230006fd7458620006fd635462003efe42982210ddbc7459521005ff71509100e67c5058a51006ce6358810006f56118620006ff541812103fbe4250a100e57c7559121026ff6248510006ff74d853200efc5258810007bd6450b1014ff842440103a6bf42d855402dfe744c9100fcfd764c521007ee75d8910056fd4298620097f82058e20096fc2058e20006fc7458b100077f6554a1003efd6250a100377f5454d10026ff2158620055fc7250710016fd7118141007bf5259010006fc4258231007e870485200e77e65d9521006fc5218131006fc6598132004ff7258d10116fc52d8e21006fd64d8e200fefc5258e21006fe5458e10004bd7699010045fc7448610006bc64d8910197f65284110006cd6398810007bd5450e102f7d
  | 23 => 0x5ff754ca10007df7358532006f721d8530005fc7055121005ff71509310d6fd4358a31056fd6254b10005ff7655231005dc7054d32027f95248110006ff6294210026fd32586201277d7299631026ee70d891031fdf514ca30006ec5458810006fc52d8f100077d5454810006ef64d891008f7e65546202afee52d813224ff6424c710007ee54588100aeff4258a30006fc54d8d20116ff2158a312aefd42d8132065fc7559310005fc70506500057f7558132007f57194210007ef754ca211367d32596310077c72594100fdfd724c521005fc7654d21005ff7150a302c7df73181322c7ee5218132007cd434c9202c6ff7318132006ff731815104f7c655521001eff71181510067f6550510004fc7058d2104f7f5155210116fc42d8e21005ff7355010006bd71d9130006fd5458d10326fd5318132007bf645491002dfc7454d10086bf43d8940006ff4258f10005ff7159532187f454c4010115fc7255231006de7558c1026ff4548c71003fee3254a10006ff7558a3101e7f7659410005f5718821000efc42588100077c4219510006de6458c103a4ff7159541025fe7250510006ff4158e200077d52941100e57e758c521005ff7655010006fe74d8930006fd7318154057ee524cb10005ff7254530006ef52d8910007bc6454910006de3258c100065f6518d10006fe54d8e10054ff7648410007dd6354810006ec64d8910005ff7454d10007dd548c130006fd6354810004ff7655132007f17188210006fd54181210677f5255310007ec7458810006fe64d862000efc42185200debe64d9121007bf6454930005ff754c810006f5618c620006fe54d8e20025fe7290110006ff7258640006fc7418121007f5424c7100077d5454d10006dd6358810006fc4018121004fe764c941007be75d91100d6de63d8d2103ffb4248210007df42d8d10005fc7654930004fd71d9530356fc42d85323a4ff7654641017bd72990100fefc4258e21006fd7218154006bc7059231007bf7259010007f77158931006ef745881004f7f5454a10006fc4218131007bc5219130397ed72d8532115fd728c521006fc4298630006fd5118141005ff7259231007dd544c530006ff65d8620005bf7155142006ff5158b10007f57198121005fd72d9210004fe70d8543005fd72d92301e7f4524c510005ff7154d21004fd764ca5001f7f51550100aff72148630007dd528c531006de32d8d10004f776440100d6ff43d8d21006fd71d8e20045fe7448610006fd6148650007ef62549100feff42d8931006fd639422004f7f535521000fee325481000dfe70d8620004fc76552300aefc4258a30005fe7118154005ff7154a30005ff7355121006fe54d8d21007dd528c630006bd6559010006ff6354910016bf4218141005bf7150d420677e655531003efe429
  | 24 => 0xf421813203eff5258a10006fe5458b10006fe764c950117f8208c620006ff54d8d20005fc7055010107bf4259131005ff7588010027ee3250910007df6358e200077f4259410005ff7454b10005ff7654810006fe6418620004fd764c810006ff6598620007bd72590100ddbc7458121006dd634ca51037ef5254910056ff5298620157fb42440100047f7559130005fd7588010006ef62941100c6bd32d9130007f5528c510006fc505881000efd7118121026fe5258221006bd4218141006fe65585320e67e654841007eff43d8e20006f96284010006ff764c8100677f5354b10007f9601812118ff754c40101b7f854c411002fbe54d9110006ff6198132056fc5298410006ff53d89100077d5494310007f5614c620277f7548c7100afdd524ca300feff6250931086be6488010005fd7494010007dc5418d10006ff6518620006fe75d8910007be7259010005fc70552310a67f5258e50017bf4250410005ff7550f10006dc62d8d1011fbf425063100dff7254810006dc5458c10006fc50d8532006fd655853207dde7318620024fd768831007fdc30981321267f7159631006bf6454510007ed52d8532026ff624c910347ec6588521227fb52c4210007de5458c100077d74d9510116fe32d8d211e7f4424c510006fe5458c10006ff7558620007ed529853205fbe5450f10006ff764cb1009ebf4258e40007dc5298c10006fe7058a31055fc72553100077d5454a10006fc5458e10004fd7118152005fa7688110006f5618c650005f57194010027f62158620006fc659812138fdc754c931006fd7518132006ff65d8132007bd4290310026fc7058620005fe70d9532007f9601813213fbc40d9132005fd7550f10004fc70596310feff2158d21004fd7688650016ff4118141005fc7054d21006fe74d8d21116fe5258a3131fdc754ca300677f5494310006ff64585321475f5054d32096ff62509300057d7518620005ff735521010f7e6554931007df644ca30007ef6488521007dd43d853221ff454c4210006ff649812100ff82018620007f571d8a10357ee42d8532005fe7694620116ff71d8d21004fd71d9132005fc7655110007ee54d8910397dc30d8532006ff41d8a10027fa3288110006fd75d89100077e72d9530006ff7358b10006fc5018132055fc725471003eff5298221006fe7458e20006bd6448410006fd6518620377de548c5310fefe5258d21025fc7290110097df3258e20307de548c6300047e7619510006dc54d8d1008f7e6594220356fc52d8532006ff5358620006fc6598532004fd731815202ebe7619110006fe54d8d10005fe769062000eff52d8810004fd71d96300d6fd6350d21005ff7259310006ff4358b10085bc744c22038fdf514c9310b73c5455230056fe52d8b100077d5454710006ef6254510
  | 25 => 0x80050038060000021000032406a01e0000394032021000000400400000100b0006000007001c05c000001802400000000000000a8009036003000c00610f800c000017000816003c1870078500006001000934000000706c01bc008007004002800001f2a6844c1780930388028030006008803002001d018800003e00f041801000005008b804808a000000000808803100c003c14a02a000800c00002500281840540270968018002014002000404000000302bc0000a7003011000001b000800007e1500590000002044018016c00601501580300081a200000ac01800100080042800451ec8460206046004001400400601500dc19400f002000c02800c009814017a017004802c02800904580040720bc04d008d0ec00000e81f002600400083183d402600f0018046018008803400c011008851c0c602e000801c29005200008c804801106a000401000d00882d0058005011000001006a000800006c00000306d412617c00080ac1720a3000817800a000000005803e010044800c000035028000800400200e875802000f00c95244be003003000401a0120028014026011021800002800c0ab838400201a001027400201100000480100290ed8e2000800200d806019c0000c6002007200100181a800614f011003866400401300140700090068000018025003021400602a02d000809a00d0108c30002000005000400e00d0020ec800000100000080060000000044062002013002400000a317de744ca30056ff7648410006ff64185322cfdc528c13003ffa42482100d7de63d8d21007ef74881200dfbe64d912111fbf4150a31006fd5218530007f55284110027f86288110017bf4150810006bf649411005ff84090310014fc7059010007dd5318132006fd7418121006ff51d8910227f754c4210007f97588210006fd52586300ffdd524c9310dfbc645052103cff7688010005fd7494210066ff7654410006fd5358810007bd6454a31006fd6350b101d7f85488110096fe42d8930005fc7055210006ff625061003ff9424821002efc54586101476c6554932005ff75882101c7fa5448110047bf4250610027ee7518910004bf745953002fbf425511003eff52980100aefe32d8e20004ff76506202aefe42d81320177e545501003ffb528821003eff52d8520006fd6350620006ef54588100fefe42d89310377c54d95100fefe624c64039f3c5418554007df6350910056fd52d8121026fe5258910005f57194210396fd53d853200ff820880101476f5154932005fd74d9510005df7354531006ef7358810004ff764ca51055fe7255310005df7354630006ef41d8910005ff7159220006fe65d8121017bf4355010005fd75900100077f7259631007f55244010006ff5158620116fd52d8d21007f952840100d6dc3058a312c6f
  | 26 => 0x180f400a0000f7000ce500160000008010006046877006c006000001403600000b8054000022018000000002a01f821c012009000008400000003f800000000f0350008000028000000007e019000000804400503202fc002009000000800001005e00e400006100a803807e000000805801c01701601900000000a3047800201a02e000003214d138000400000b002009c00200007f000000a00b011820405a1ef0000108000001014800401c016005000000c017013803c00001d003112807e0000148f6400600100400500ae006026001400e003024002427c0550ef000418c0590008000ebe0000238174006000000800015000101e800001c052053028800001807f00000120be0050004016010000001c03e04a0038010000035001900c00a08b03200ac03c01002900880ea106002800406800000e80e400415d001010006c000002814800a00205c80000040b400a80080080ef00e00001340060000000010000001013c0000000008014052128001801403c02603881a80020000010038010001008800800002108922d000002300e000897800002e801000002d0020b8000a01e0980004116025002809c0ce000007800000e014000000000c38d187812000002f00e803c0b401001b00240a6004002000046e1a0009012400e03c00181c801000100003142fe002000001c01c0001bf000802e00b00780440aa01100403f402a00200101d00180000030008010000096002004a09700d80f814201d0b5006400c00000b000002a001005023c01c0000000000004000016802801203200480c8030045000010c00401c000001800200a01d000407a0060000018052000000002404800007c0030012069000000801208d00300000820d403701a807e00b003801000600d0018bf00f600001a803400002d050800800402400600380500210010014016002000000001c001000000401a000000000000208600f00000540120188008046062002803c00800800b00300320310020214000208021801c002001001815016200500301d000000000180180240060028824006005038967c03e00005000180c000104400b400000401180c002a1f101a061801600b00082440b2000001004832e23b035800006005203d800800a0000cf80240040630d180e001410406d8008004000000803407603f065806800637202d81780020180038074000001005804805400002301fc05a0000130000002049019800800000500500582ec02d10d00340100240040038002662002144001a001002800003014a0ae000c3c2000000032002802500080700840050390048000018200815401000202381d814066f03e803005000000f00003584ea0a3000000619f00400000820000c3000404e01c01e033000000001b002c07600002180bc00a0bd00080000
  | 27 => 0x200e00000fa029020800800012604a004c000176001000001a032003802000e0000348058020004003800000c00303f800407c03d007800000200100982ec024004099007c128130000002c02403d00201580040430010bd800003306f800001600001c015400610e019000800013302380f000c00800000c021800a002001800600200000040ce0b8007077415001600000500240010bc846c00000100c80040000cb0010294004491022002c86a000004000001e005000008403c05501a00540040050058044044001000001400808a001038c00e0010ba025c170182004804007a003000800004403000000140f200902d017c10e01e005001c00e000011801802c0ae0cf000c00001a0018004018001002800004c00e004800004a00a000800005200005b804401037600b000003000b06e838c00205d00b824802c00200480280022f0097005820601f01a809400c00e019801814a0030170058036149003800002400000e80881740d00058014000081000801801c005000064413e21f00180041c401b0310020000000006800400404e000000000801402e80241320080028160026075094008401a00b00000840040cb0068058016000029001002801c003024002c00718f800801600701704982840df00000200060170000064152000008015000c00f00e800802405200180000500f9004002000c05101a81942f802802a002402600f0e1039c01e0300018050060000000800405800405e800016601a114000c00800c000006800e01200e8024000012002000800a0ae04580a000c06b00484b00340010a503d8002015000037800e0110000e1401a00602400b414801500480300000bd01c95f400009d010002000200200d800001200309f000001600e01801a0002000001800000a0c6029000402600001e088800200604b80880800320100b0c474092005000000002d000800000628f042829801e00100000080180060112d380100000490290004176013801401215c00680f800e00000381d8020000000825c18a04302680440000340010024026000012a8a000800000000000600a309381d004a002000011c0000351
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xed840d8e4044001d5ec8aa6c488003a7d0f4258c100956e43286b0264009f7815d5420407f9eae3b1cc0908029fe1564585320056fc38a4b182000a7d85108614c0013bb06382a89928f75dcf61585320063fa92ec98ca000aee8715162040018faea3aac5880032fd0876506300066fb1ee2a122000a7e859d3624c0019deebb148088003a7d0963900100066eba6c690a2000e5d8558d52040031f90ea88c0908265f215744ca10006ecbaee09946004aed871436244061e68a8aa62008003a75d25458c100073732ae8b102000eac429d162040019eee6b8ec5080033be15721813100766ba4c6b102000add83d4b63440019bf06bb26310003a75915458c100056ec326498c8000e6e845956204001d9cc6b12840803f37dc9638c2200065f43cc8b14628eeea52580604c8019f485bb22008003972126558c1003e76396c4a0c2000cdc7558e20040018fecaba6c488002bba0354d89100047ec38a430a6000c7f759d4604c801cbaa8b1aa408002b760f51d8e20005c640286a126400cf686dc532840015db05a8ec508003371d863549100056ec16a3b1a2000ced84dc9618c001cd8eba92c408002d7a144258c10006773aec4a122000e5f52d8d534406b9f6c53b44088003b31d463189100055ec20cab0a6400db9541c14144001d5b0a326c4880023f61b715513200774422c50802000aed82d0460484015eb02320c3100033dd537158d200047f438a1b1220009ed821c1538800157d093aec508002dd60442195100078faa4a9b1a2000a7d8299265040015bb0faa2c6080023f60c765462000756322a9b1220008fe87909608c4459dcc4b9463280027ea0371552100073732ac4a102000e9f5495363440013ef02baa6508002b760c54185303e774292c50802000ced72508614c001d5cc8b12a40804abba0b41d8930004eec38a53182000ade8414b6344109be302382830823af6a036358e200047f43ecab024200a7e85108614c001d9ae931cc40800a3f21d6559010006f42a0e09924000ecc54d8f62440017d704a8c4108003371cb63505100047ec30e0a126200cbf749d3634841137908baa4308003975516354c1000677aa2e43026200aed83dd162040019bc65bb26408002bbe1175588100057ac0881b1420008fd861c1548c4cfb58c9b928290802af219545051000677b16e2a922000abd84d956188001d5b0eb22c4082433e5ce70d8e200071faa4a8b1e2000ade8598963040019bb0e292c608003b35cd53588100053fc2ac930a6400ece54d8c62440014fd0a324c099002bb6087558e200072f32884b182000ade851d36344001d98ea31ec4880038fd5254d813200677b1ae52044000add82d056304001cdaa9b12a4880025f61c42994100047ec3881b1a4200add8390b63841217b307300c0990033b1d76288110
  | 1 => 0xd083a8c099002f360b644ca300072eb2ac6a102007cee72d8a5084001c7aa82a2c710003ab553435881035ed63a2e89944200add8210363440151fd0e202c588002bba1d53d89100055ec20cb30a6469adc8654c614c8015db04206c508003ab9d154588100071eaa0a8b182000cdf75d8d32440019dae4216c60802a3fa1e6458b1000566c1ce9b122000ec862d8e2044001dd708b122008002b7e1a4258c100056ec1ce8b1a4200de6521c5604c8019b8a9b9ac488002af61075d8d2133dd6422cb10a4200cdf7458d62040099d8e4b0a8310003a79d34258c1000767292c6b102000ead749516204001d5b09b128488003379cb63901100074fb1a84a0a2000a7d8610a658c4019d8eab14800801f3b9cb629021000576c3aa9b1220009bd84dd620c40015dd0a3a6c488002b761065d8d1000576432a83122000ade86d0b63440d59d8c5b8a64a08032f61270d85420053ec28e83024200add8390963c40019bac6b948008003ab10b64d89100047ec36e89962081d7b521c151440019f50c3828288003ab90a64588100055ec24ebb1420008fe871096344001c7ea92a2c408006bb20b545881000676b92c52062000cf571d84604c801d5ca8b128408002b6a0072d8d1000676bb2a49902000cef825d92190001d9c65b9ec4880032fdd274586200074e3a2a9b1a20008fe87103634840f6dd05b2aa5080039bdd751d89100074e326a5b1a2000cbc641c16448401d9e86a1ac4080033ba137258d1000576c14a9b122000ade87d0b63440078feecaa2a388002bbe1d43d89100072f42884b182000e3e8259564040019bcebb1a428800337a1b734863000677b96c4a8a6000cdf7558d21040015f50dbac4088003b398b4298c100076ba12c68802000cdd831d9218c0015db04282c690802f6201754ca30035bd404e5b2a2001cef7458942040018fd0f32ac518803b3dd163988100072f424cab182000aef8754d6204001d9ee5296c688003379d5635081000757c38c9b122000afa86dce208400173d08292c6081c2e7211754c9310056f424eab182000aec855cd620402b5dd0432ec5180038fd5254185200065eba0e9b142000ecd7518c62440019daeab124208002bb61c545881000576c14eab146200add839d163881479eee7b8ac690802bb60454d89100047ec08e0b226400e5e6555163040013f10ea0c41080039760865d8d100066fa92e630a4000ade80d5163040015dd0b3a2c4080123f61f65d891000f73b8ac49082000ecf4258d42040019dae5b148088002bb21574588100047f406ecaa26400f715494110040019bce9b1ca088002afe195450c1000cf6412eaa082004aee82d936244001cb8eba96c6880039b197625491000677baec490a2000aef825516204001d3b0ab22c608003975965458c1000577c1ae8b102000
  | 2 => 0x2761891000773b2ac310c4000ecc62d8d42440015f501212c1188033b61d62900100056f434a9b1a2012aee82d4563880019daa8b96c6080038f21d65590100056ec2e87b1a2000aed829d56348401d3ee92a6c68818be3191424ca3000767baec63122000e5f8219763440099dce5b12a288002b7219544c5300047ec16ecaa62000cf77650910040015f501292c1188023f61c54d81320066fbaac71002004aef871036244001e3ea92a0c688003371c963940102b6d7326e4a0c4000cee425d93204001c7ea92a2c1108031fd4a70d85540072faa2c6a982000d3c545c76055001bd70a3826490002b7e0d7558e2000778b8ce1b142000ece5258d32040198f8eab2ac988002b760c5058d210056e43ca5b1a2000e6f54d895244001cbecba16c6880029f60a64996310071eb28e4b202000bd8805d1328c001a78a8b88c0aa0039b9d752d8910007662a0c7b122000cee54dc9634400187eecaa2832801efaa0b648821000576c16a3b0a64009de8710b63440015bd0b392c6080039ba1674d8910004eec1ce3b02a800f715254510040a9e98eaa9a64900032f21171181522c56ec18ea3026400aed82d4561880013bb0e292c6080033b153725863000676b10e090c8000eda76d8e20441515bf06b08c0990023f61f41d89300056ec1ceab1a420cc7f7655151040015bb06206c299003b56044058c1000757424ebb122000af581152618c149baa8438a6498802bea0064d81210074fc2ac8b182000ed45458f10040011fd0f212c318002b761642d8d1000766b126498ca0009dc874c9518c00157d093aac7100038f59564553100053f42ec9b0c4000eac875916204001d5a87a16c488002bbe1e54d8910006f4428e09924000e6d82d97624c00197ae83a6c488003b395063189100056ec24eab182000e9f6494b63440015bd0c31a84880023fa18704c95100576c1683b1a4200aee849d562040019dae4b14a0080023fa1c50586200056ec3c84b182000adc8694b63440019db0fb128288003a719252d8d100057742ee3b122000e5f54d4763440011ff0cbaa65880023fa1f511813200737210cbb122000abd84d976388001d3ec9a96c6880033bdd76288110005aec188432a20008fd8799461880019eca5b8ac6900033bdc8525863002e9e3a2a8a8a2000f8d43508604c801d5e85b1480880023f60f72586500066f396c72822000c7f521d9518c0015bb022a2c608002b7e0d7458e2000577c12a8b0442008fc874c86054401cdea8a9ec4880133ba1f62941100047ec10eca8c6000cef84dc9618c003cdd0ba92c408162bba0b511813200677290ec9922000e6c521d762440016bb0a212c608002b760a5458c1000737aa2c4a882000b6d851d162040015b90e2a6c688002aba1275d8910006eb3a0e29926200ced72948604c40157
  | 3 => 0x4b026404aec8254f62440015dd09b9ac4080038fd9572d911002677392c32844004aee82d5362440d59dcc5b8a6528003abdd274d89100065fba4c8b162000bd7815d5324c401daac6b0a63100038f5505418530005d7c22ea9924000aef8714162040019eb0fb0cc3100023f61870551320056f4368431a2000cf752dc563480015bf06aa0c098803375d9434c8100074ec22c6a102000ecc52d8f62440015bb063aec6909f3ba109628401000766a12643026200aee809516204003adce4a94a00823fba60a70d8e20007a6a9aa49942004aec8250f6244001d9ca4292c608003b3dd763d8910004fac08e0a146200aed82d04604c8019dae5a90c0988027e201755061000576c1ec4a922004cee725864088001cdea5b14a0880038fd9472d91100071eaa0a9b024200ee850d8a50440035dd04a1ac4080cfcd15154841100072fb2ec6a922000cde7258d510409fe58a8aa440900172f5d9549031000757422c4a0820008fd821d9548c0019bf06bb264080039b60865d891035677316e29948000a7e85109618c00137b0e292c8080023fa1c549823100d77414cab102000a7e8519360484f1de70ca8a20080035d54971940100053e42ac9b026400ced829c36155001bac65b8ac0990030fdd9545464000757b26a9b122000cee74d8952440015bd0d296c688003ab55162900100056e438a5b1a2000e5d5414363440017b500216c6880038fd5174181510047ec08e0b2a6400abe84149618c0014fb0a3a2c69088abb2096558a3100576c3aa8b102000a9d8414963040019bce9b1a648800397d4963940100066f438a4b182000abe8694b644c0019eacbb8ac0990063fa1f41588100065eba0e9b0a6400ecd63d4962040013eb02382a4080afdcd5250440100057742ee7b122000aef845d762440a7e58a8aa2649000397d5163548100053f428853046200eae54d8941440014fb0bb26c3100331f9d9529411000d77410a830a4000a7e851d162c40015b908102c608003b35ca5258c1000756326a9b122000e5d8510963040015dd0a202c4080023fe1973486400055f420a53046200be982dd22044001cdaca2a2c408227ab99364886200074eb26a8b182000ade84d496304001e5aa82a0c4880027b60a70d855405d9e422caaa62000ece8258d42040019beea3aec688002bb21f43588100056e412a9b1a2000adf8755163040015bf06bb264080033b58870508100056ec36a4b182000ced7558941040017e70b20220080027b60b7154e200074fa12c6a182000adc848cb63440013df0eaa2651081a5fa1c4219510004dfc22ea9922000ece6298d5204001cdb0532ac408002b761020d8d10006763aac4a102000add8599163040017d305b244108003baa1870485200053ec2ee9b142000a7e8510b604c455b6ca8b8c80080033ba1
  | 4 => 0x3040015f5003a6c7100023f61e641853200576c10ebb142000e6d7519762440019dceabaac408003ba551628401000577400eab102000af7815d561880d55b90ca9ec299003c75505458c1000757290c9b122000ade8414963040019dced2a0c488003ba95162440100076bc0ae4b182000aed82d0f62440015db04202c310002cf61272d95300053ec2885b026200ecd74d8f6244001d3ea92a2c608003a7d0842d8d1002676396c4a0a20009ed82dd64084001a7ee93a2ca08002bde0554185200076d3b0c71022000e5f6590b6344001d5ee9a12c4080023f61b714ca403eef9382c230c4000abe84d9563880013d90eaa2651098f579d7754ca300055e422eab1a4200cee52dd93204001dcaa4b08c299003b558d71880100047e402e3b2a6400cf721dc56388001e5ea92a4c408002bb60b51d8e200057c402863024200abd84d9461880015bb08286c6880033714b735891000576c1ca8b102000df1619c231880019b8e4b1aa608002b760c40d8e200ae76396c6a0c4000e3e8759564040015bb06292c118806bba08405881003d77410cbb1420008fe86dd532440192fd0bba44188002afa1075181210047f438a9b1a4000c7f759d562c40019ef0eb0c6310002b761075d8d100056e42c65b1a20009f581dd220040019df09b92c6880038f95175181410066e2a6e6b0442008fd8794b63040015bb0d212c6080127d60670d8d2102d9f426caaa22000e9c4258d42040015bb053aac608002b760c52181310066e392c6a1820008fe87d9160484015dd0e202c408002b7a1464d8d10005e6c16ca994601faee8214163484011fb0f320c3100029fa1764586200059ec20e4b2c6200cef735892190001d590fb26c488003b61416394010007573acc8b102000ecc74d8f62440015f70eb00c0908032fa10765062000764310c71022004e6f75d8952440015bb0e212c6080039720a6558c100047dc3ac030264009be80dc54350801cd904b2ac5188023fe1d32586400072eaa0a9b1a2000ece6290a63040ab5dd042a6c09900b2fdd94250710004f7c12eaa0a2000ed563dc532040011fd01b8acaa1803abd5254d89100071f394cb3202000abd841956048401d9ca8b1cc4080abecd0a4044010006e7b9264a8c60008fe874c961900011fb0f216c608002b7a1372d8d100056ec326498ca000abe8419760484013f5013b463100039bdd450d89100fd77414c8b126200ade82d516304001c7ccb322a408002b76172158c100047f43ea2b1c4000aee85d936244001f1a86a1264880033ba1d625481034d6e4328630a64009de8714b6344001d3b0b322c608006bba1d65588100074f2a2c6a082000ed56354910040015bd0f216c688003379d163548100057ac0ccb30c4000e5e65d5163040019bec7b928688002af61065981210aee7b9aa
  | 5 => 0x8002b760b4358c1000576432e890a4000ead64d0962040151f90eb128388002be201541813102577c38cbb122000e9d54d0b63440015db04206c71029375d08714c9310056ec18843026200aee849c162040e36b90aba264988033b5d36248510005afc2ae89946000afa80dd0604c801cbf0932ac608002af610751813200677b96c4a0a6000cef62dc54244001cdecba16c488002b7e19324c6400065fbb6e4b202000e9c8559163040015eb033b242980573b9cb63902200071faa4a9b1a4000e5e659496304001cbea8286c6880033b588704ca400053ec28c8b0a6400aed849c162040019bce5b1a8288002bb61854588100057642e87b122000c7f525cc6054401d3f09b1a84880023f60c76551200047f43ec8b026400ecc5218f62440011bd0e216c688003aba0a6458a310fee639264a8a6200bda801086344001cbea5a8ec688002b721743d8d100066f3aec71022000cdc7258d41040019dee6b12840801b4f1d554505100056ec26ebb1a2000de8741c132480015ef02b24c3100031fdd66558b10004fdc3aa31022000aef82551628c001d98c431a84880023f61c54181320074f324a8b182000aed82d4762440014fb0a212c3180234f1d15454a1000736a9ea5b122000aef8715362440015d90ab9ec488002bba1352d89100063fbaceab0c4000c7f7659552040019bce8ba2c6080033bd5172d8c100074eaa2c6a10200097d85dd220c40015d90aa1ac4080033e1c04058d2100757c3cc8b102001aec825916204001d5d0e326c488002cf61472590100053f43085b2a2000e3e6490a6504001cdac4a94a00802a7721d534cb100065fbb6e4b246200dcf724c9418c0015db04206c2992afb9909611853200757296c9b122000abf845d563484015df0aa1ac408003975535158c1005676392c4a0e2000ecf7518c62440019dd0eb128408002b760f41d85320063f3b2e5b2a60059be84dd620440019bee9b1a42880023fa1e52982310076b212c68802000af58114163484019dd08b90c098802ee61375881100056fc3e84b182000a7d85d91618800537908baa64080039719454d8d100056e43885b1a20008fe871916048401c3ea92a6c688002b7a105458c1000576c24ebb122000e6c75595620400173b06292c8080023f61c5458d210053f428e9b0a6400afa80995604c801cdea4b12a2080029f614429823100736baea6b102000e9e8559163040011fb0f216c098802bb61d43588100053f428c83026400cef72549608c401cd90bb12a28800397d4f63549100072f292c6a902000adf8790963040011fd0e32ac099003b39d16398810054fa43a8290e20008fd87148604c4019bf0eb1a63100039b55351d8910006763b6c4a922000cde74d8d2144005a7ce8aa4a0080073b1c9625441000677212e7b122000e9d649496
  | 6 => 0x547fc3ac52862004cee72d8a504400137f08baa4208002be201645812141ef8402e32842000cec85dc9618c0011fd0dbac40880033de1d6118620007a6a9aa5b0264009fb8750620440015bb063aec7100033b90a764c9100055f430e5b222000aee861d362440019b8a8b9ec4080033b5d1624c810007663a0c7b122000adc845d5630400167b09396ca880033b9d9524c9100073732e84b102000ece63d096204001d9cc4b1a8408003b3dd6639881000756aa286b102000ced54dc9618c0017cb033a6c48800397d5054d8d1015fb9a94a08802000cef75d8932440015eb03a96c298003b6101639001028ed63a2e890a4004cee72d8a4044001dd501b8ec4880325f2157650b1000577c34a8b102000af581100604840d8faeca94a1880023fa1870549100071ec16cbb222000ced85dc9618c0015bb03a16c688012fa20941881100066f3a2c72802000aed841976244001cdaa9a92c4080033dd9471581320061e2a6ecaa02000add839d7624c001c7aa82a6c5882235b9957294220007363aaa9b122000cdd7458d210400d8f8eab0a8328003a75935258c10005bd400e5b2a2000e5f8419763440014fd0bb26c710003371d363881100065e326e6b224200e3f54951628c001f8a8438a64988032fdd27458810054ee43a869962000c7d751d7624c0015bb06212c1188031f21571181540057d406e9b1420129dd839c3644c929f94a5b82651829bab1d3624c9413556e43287b0a6400cef735895204001daac6b8c80080033b9d3629411027dd7426eb1024000eac64d4b62440019ba64bb26310002bba1f53588100056ec10ebb1a20008fd861c1434851d5bd01b9ac710002b760f5258c1000577438a0b102000add83d44604c8012ff0aba242081cbf160b714c93100ed639284a082001aec8250460484017cb03b244310002bb20154588100066eb1ee2a102000ecd7598e6204123b3e84b9c811804abba0850d893000767ba8c7b1220008fd871516188001b6a84b8c80080063f21d6254410317c7a0a849946000add82d456304001cd8a4b2ac40800337dd3634c91000576c1ea5b122000e5f5258d5304001c7aa82a6c2900031fddb7259631006773aec490a20008fd871536388401cd908b2ac408002bb60b4158e200056f424c4b1820009dd811c1434c8035dd042a2c4080031fa14765462002676c3ec52022000aed82d4562c402b9dce5b1ca1100023f618705493100577c12c6a122000ade8694863440018fea4bb46328003ba10362901100076a292c78802000c7f765955404001e5ea92a6c4880027721d32545310066ec1ce1b0a6400af8805d563484019eca838ac6900029f2156458d2100772a96c330a6400cdf645cc61880011fb0e2a2c518806bb2085458810366b63aaea99442008fe87153614c001d3d05b26c68
  | 7 => 0xde75d8f62440011fb07bb2a310002af6105258231054f6412ecaa62000cde545cc61480019bce5b1aa688002bb21f43d89100072faa6a2b18201adcd7254e614c8013ef02baa6408003ba589424401000576c0ca8b102000add83153624c00157b08290c09880337e1f63509100066ec1ce1b0aa600de8751c13248001d5ae9a16c4880038f55151181410067bb20e2b026400ead54d8942440016bb06214ca08003b355363d8910004fac08e0a946200a7e86108654c001c7d0532cc8080029f21954941101ef9a2a2a898a2000a7d8519260484017ab02296c68800237a1c52d8d100065ec38c9b126000e3e84d976444001dd50c38264900029f61464581210065ec38c9b122000aee86953624400597f0eb22c408002bb60840d8910007572a684b102000e6c87197624400157b093aac310002bba1e54d89100071e2a2cab202000aef8750d62040019bce4b1ca0080029fa167458e200056fc3ea4b182000eeb5458a10040091fb0fb26c4880023fa1e42d8e100057bc0aa430a6000e9f42d8d41440019df04b88c0aa1aeeb211754ca210066e396c72022000eaf6250941440019b8a5b9ac110802b76084058c10004dec38a43226000add83d076388001f92a438265180029f61a425963105677392c52862000cbd75d936244001d9ee8b1ac4080037c544704851000737aa6a3b122004aee8215160884015bb063aac4080027d6047050d2131fa7a8aa49946000cef755894204055f64a8a0a2008002bbe1d54588100071e43ecbb222000eeb8558a10040015db04202c58800337dd5634c8100066f392c7200200097e80dc553548011fd0eb12a2080029fa1474d8d210066fc1ae2302a600adc85d0d630400157b04328c888003374cb7158e200047fc32eaa162000ced7294b63040015df02aa2c4080023fa1b7154e2000577426a2b102000e6d651d162040011fd0e2a6c5080029f61764d8e200066fb18e0a922006c7d87d9764440031f90eb1282080033b5d1629401000736c3acab102000c7e76d9542440011fd0fb1a8310003ba9db628811034e6e43a64b0c6000cbf749d060484012ff0aba26508002bd60773d8a100053fc3aa4302a204aef87d9762440091fb0eb0ca110003379d563484100047ec30e0a946200beb8255120840019bee8b1a6408003abd9352d89100074eb1a84a082000b9d831c96404001c7d0fb2ec888002bba1674d89100047ec1eec90ca000cef74d893244001cbccba92c6080023fe197348650006f4aa0e09924000e3d651c9648c4011ff04b98c0aa002b721742d8d100067643ac52002015adc8654e604c8035eb023a8c090802b761351d8d1000572c08a0b102000ecc42d8f6244001cbd0432ec6880033d5087158d2026f9a2a2a918e2000ead541516204001d5f0b322c4080023fa02764c9410
  | 8 => 0x84b1e2008002bbe0943d89100047fc0ae4302a600e6e82995628c4019dee4b128208003378c97318121014de422ea9082000add8110963040015bb073a6c4880038f55054586300056fc1aa9b1a2000add839d9328400171f02a1a84990033b5cb52d8c10005eac08a431a2000e5e841976344001cb90832ec68829375548714c9310072fc22cab182000e2f549536244001d3ec92a6c6880033b1d162544100057d406ebb142005d3c74551534400157f08b2cc299002b72095458c100047ec10eca8a6000ecd7350d6204001878a83b2a89094b5b1d5754852000e77310e090ca000b9d8414a63040011fb063b2a88802e3fa18705454100767b1a849922000adc848c963040093f30f28440880027e6087054510006f3296e2b0264008fd83dd954484035db023aac4080029fe1d541815100766ba0c7b122000add840816304001d5ac8b12a4080035e55070546100063fbacea3024200e3d8259564040015db0bb8ec488003b3d4a52d8d100057743a87b1220008ff865d132040015bb03aa6c688002bbe0575d89100067c2a6ec8802000aed85d0f62440095db0e32ec488003f45cd318811002cfa43aa2a0a2000add85d0d6304001d9f06b1264080032f1db645091000577c3ea3b122015adc8650e604c8019daebb9ec4880033b21f62545100047ec16e6b0c8000e9e85d9363440015bb0b196c6880023f61f5158e2000e77310e090c8000e6f65d8952440014fb0a326c099002b76185258c1000576c10a9b1c4200ecd4358932040015db04200c0908038f59772590100071e43acab246200e5c6514b63440015db08286c488002dba1674d89100069e2a0ecaa26001dae7250a40040019dac6b9481100039b55050d89100047ec30e0aa44200e9e6458d4204001c7aa82a6c7108023f61b71548104b75ba12c298c8000ece528cb63440019baecb1a84080023f61f51d8930004dec38a53202000eae54d05620400157b083aac40802abb2096558b100074e324a9b1a2000e6d5358952040298fb0fb2ec498002af6107558a3100677ba2c51002000cdc42dcd62440017b100b8a6518002bb20174588100071eaa0a93044200e9d54d0763440459d8e5b1a8290802b761321d8d10007373aecbb122000aef8254d62040014fd0a216c608002bb60b51181210071fc3ecbb222000cef72909608c4011f90fb1282980033d99071581320059f420e4b282000e3d54152608c4033dd05bac8008012bb20954d89100056ec2c84b182000eaf7495362440012fb02382a6a9002afa1052d8c1000676baae7b122000e5d65d09630400f5dd05b2ec508003ab1d341d89100047f438a1b0a6400ee98458910040016eb02216ca88002bb61d53d891000736296ebb122000e3d54153604c4015bb0d31a84081435b9d775881200069eaa0e0a8c8000c
  | 9 => 0x63c40100155f43acab202000cee74d8921440015bb0bb26c688002afa1375d8a100056f400a9b1a20a4dd6421c5324c401d5c84b22c408003bc5c7609812100736412cab102000add84c8563040015bd0daa6c688003e350d429853200767a1485b1a2000e3f54951628c527f948438265180033bd5372586300053fc2ac9b026400e5d5414163040015bb06294c318002e760e72d91100053ec2ec830c4000e6c4259562040015bb02216c6880023f60476551320053f428c8b1a4200e5d54151630406de70a8aa620880033b5d77358810006773a6c49922000b75819cb65440015f50db9c4088002f5e0d544c71000576c10a1b126000eae641516204001cdc85b2ec4880023fa1870551100056f42464b182000aed84d4d62040b19d8c438264a0a42bee0960181320055f430a43222000deb541c1324800157d093aac310012faa0274d891000577c12e8b1a4247f385455220840015bb0c2a4c6080029fa17641862000576c3e86b102000ade85d0b634405f7e501b0cc3101afe31d1434ca210047ec38a830a6000a7c86551524400fad8e4a92a308002b7e0d5458e210065f322e7b244009d3c7555142840019bcc8b98c310003b320b63509100057ac088530c60008ff8759461880095d905a9ec48800e5f215744c81000767b9ae6b1020008fd831d941880011ff04bb46320002b760c52d8d100056ec1cec9922000be58115062440013f100baa8608002b7e0d764cb100073742ac5280201fdcd7350a614c8055790eb2ac8080038f594525901000577428c9b122000cdd321d9218c001f8a8499263880023761c4258c100073732ac4a902000e3c8459564040015dd09b9ec488002fc60775882100071eaa0a8b1a4200cde7650d32440011f90cbaa85080032fe1171181540055f424cbb0c4000e5f5214363440019baa9b9ac488002bb21f54588100076729264b0c6000aae841d562040013db05b8a869096bc7151548c1300076731ac4a90207ceea5258a10040011ff04b9ec2aa0029f2195454d101ddbd42ee91022000ade821936344001f8a85b8a64988033b5c9521853000766210c7b122000cdf72d8d4244001cdea9a92c408002bba1254588100063f42cec992a200cef72109618c001b9ee499282988039bdd7525881000736baea5b122000e3f549516348001d98c5a16c688002f9e05754ca210057c402cab0242008fe86dd121440c5f1880a1265180f3f1949324c51000677ba8ebb122000add8414163040019dd0fb12a288002afa10655853200d7741682b102004aec82d0f62440011fd0e202c310003379d1634c8100047f438a0b1462009df874ca508c0019ee85bb22008002b760a7458c100047f438a9b0a6401aee87d0562040015bf0a216c6880038fd9452d911000576c16a3b1a42008fd87d4562c4001da8
  | 10 => 0xb122022aec82591628c401d38c8a1ec29918fd3141524ca300055ec26cab1c4000dcf724c9514c4019db05386c2a9002b760c42d8d100066e216e6b044200aef825d162040015d90ea9ec488003e350d42585320066fba2c69082000ead54d0b6244001c7aa82a4c310002b760e74d893000775a92c50802000e3d5458541940015bb0532ac6080023f61c54d8131365b642ae89944200abe849d76244001cbacab1aa4080029f616745862000736b2aa8b102000cf7865c640040015df0caa44310002bb21c5458810006773aec51022000e3c6594864440019baebb1a8488002bba1675588100056f420a1b1a2000ade859d16304001cbea6b1aa40800337dc872d8d10116e7b9a84b0a6400ade82dd7634400167b08392ca08003aba0b64d8910006f53a8e09924000a7e8510963840018ff0ab88c0aa0133b9cb625051000737a96a3b122000add85d0b6344001bb6ebb8265180033b5c9628c6500066f3a2c69082000df1719c3658400157d08292c708003ec50941440100065e3b6c8aa220008fc87d89514c0459dcc5b9a43280027e201754c81000676b948430a6000cdd75d8d43440011fd0e216c708002bb201755881003f74316e31022000ece4298d6204001db0c5b1c4088002bb60b51181320056ec3084b182004eae84d0b62440019dee8b12a208003b3d0a4258c100066fc1aec98c8000cdf75d8d4144001d3e84212c608002afa106558d210074f412c8b18207cdf1811c12184001c7d05b2ec8981c7579d7754c9310fd77416a2b1a4200e3d5458551900019b8c9b9ac0908027be1d544852000576c14eab162000aed8215362c40015f5003a8c090803375d17258c100547e43acab162000af8804c86054401cdaa82a6c488002afa107558d210074eba684b1820008fd811c1655083f5d904b22c498803a755040d8d100071fc16cbb222000aee84dd562040014f90aba2c58802a6f21d5450b100fd76412cab126200ade8590b63440015db04206c69081b4f9d554901100055f430a5b222000e5d54d8d51440159dce4b1481880033bdd362485100056e42c64b182000cdd63dc94304001d9ca8b1ac4080023fa18705513200766aa0c7b122000cdc525cf620402b5dd042a6c6900039b19454d8910416dba12e32042000ade8014b63440011fb07386c2aa00f1fe1d65590100066e3a6c6a922000c7c855d92194001a7ae83a6ca880023f60f7648640005bd40485b2a200cc7c7559562c40015bb07296c6880033ba1f625051003d76412a8b142000b7985dd220440019dce8b12a208002b7a1232d8d100055fc22cab0a6400add8394963040014fb0a216c608002d760c42d951000677b92c4a882000aed821d7624c001cdea7b12a4880039b1d754d8910496afa92e7284600a9ec825d541c40015db0e2a6c488003b5551
  | 11 => 0x88401d9d04b1aa4080032f19070591320063eba8eab1c4000add8315163840019dee5a12c6880027ea037150a1056e7b3b2c230a6400c7d751d7614c8019eae5908c298002b760a6458c100065f424e1b0aa800cee7458a20040015bb063a2c518802bb60a75d8d2104e9e3aaa8a1c2000adc8795363440017d305b2c410800337d5373589100053742ce9b12201f9dc87595324c4011fb0e2a4c310003371d1638801000766316c6a922000cbf769915204001cb8ca216c6880265f2157448610005f4402e890a4000a7e8510963c40013d90eaa44090003b3d5363d89100074fba685b1a2000aee87d536244001d58e8206c4880023f21d32586502c677310e0994a001cec875895104055e68a8aa22008003ab5d3415881000736baecbb122000ced751d5620400d8fccab8ca120003abdd2745881000677426e4b0c6022aee82991628c4019eeeca922008002bb608401813242ebdaa0e0a8c2000e3c54d976444001d3aa9a12c6081c3e3d05424c9310076b90ec690a20009bd8714a648c4019f0a5bb22008003b550d61185320074e326c6a1220008fd86dd64004001c7b04328c8980271f9d765d8a100053f42cc9b0c4000abe84d9661880018feeb3aec710002bea0365d81320047f438a9b1a4200e3f54950614c8011ff0eb20c0908033bdca525863000756bacc8b102000e6f5414362440011fb0db8aa808002b760e74586202c677310e09948000e6f841976244001d98c5a10c6880027ea0371549100053ec3684b282000abe8414963c4001cbea8282c6080035d55171942100066f196e6b0c4000eae421d36244001cdb08b2ac408002bb60675588100047ec0eecaa44000e2d5415162040015bb063a8c090802bb21c40588100047fc3ec52022000abe849956188001d5b05b26c498012bba0953d891000d7643ea2b102000aed81d0b6244001cbea5a8ac608002afe1954504100055e422ca30a6400e6e4299562040015bb06214c3180029fa1442d85300056f438a9b1a2015aee82151628c0019bceab1c4008003379c963504100056f426ebb1a2000ade8618d5244001d9ee9b1ec488003cd551515071001cbf438853282000aef8655262040019db0eb12a4080039be17625451011677316e690c8000abe8414b614c0011ff04bb263200033b1d3628811000797aa4a8b102000add84d4b63440015eb03b28c2990026f613758811000773a0ac4a082000aed85d9362440018fea4b88c0aa002bba1b54d89100066ea12e630a40008ff8759061880015bb03296c6880037c504704851000576c10e9b142000abd8419460484015d90eaa6c488002af2116558132007563acc8b102000cbe849c361548011fb0e216c788002bd60774d8a1000736aa6a6b102003c7c75595640400197cecb96c8880033b951721813100737290eb
  | 12 => 0x21b7c883714ca1000774a12c03026400add83d04604c801c7884b2ac8080023f61c5058a310076731684b182000ed86218e20440015db05a8ac710003b3e0b6350910004bf43884b2820008fd87d456204001d9d073a6c4880033ba1d62544100063e32ee6b2a42008ff87d8a50440455dd04202c5188031fdd675d8910325ed43ee099460018fe87d4562040011f90cbaa86880023f61c4258f100066e3aec72022000add8314b63c4001cbea9b1aa288002b72174258c1000737414cab102000eae75591620400179b073aec488003b3d5063d89100074f2a6c6a122000cdd839d932440099dd0fb1480880033bdcb52586300067742cec3122000b5f855d1324c401cbeca2a6c6880023fa187054d210057c402a5b026200ced755cd6204001d5ce9b26c488002b76135158c1045e7ab92c298c400ad6e7254a50c40011f90cba26488002b56042058c100057d400ebb1c4058fcb731c132480039d90eb1282080038fd5254d8a1000737baaa9b122000ed75458f1004001d5e85b1282880037a5d4704c92000676c22e5b182000a7d8510963840011fb0e202c690822cfa1365552100047f43ecab0c4000c7d65dc9648c401d58a5322c4080033b1d162940100056e42c85b1a2000abd82194644c0014fb0d392ca080023fa1c5458a310074ec14c8b1820008fe86dc5544c0015db09a8ec488002bbe0961486400056ec18a4b1a201acdd72d8d3148401d9aa4990c09891eeea137588210004fc402e8990202df38545521004001c7885b2ec888006bba17525881009577416a3b126000cdf74d8d42440019f0e0282c690802bba1274588100247ec3881b122000adf8255363440155dd05322c588003d354d524c81000576c10a0b102000e3d54153624c0031fd01b8ac9100023f61e5258f100074eaa682b1820008fe8715160884019aae6b08c310002bb2116558810156dba12e32002000abd8419763484019d8eab1282080033bd887054910005d6c26eb10240008fd86dc54388001cdceaa9ac4080029f61a74594100066ebaae4b182000aec85d0b62440011fb0e294c3180023f219744ca100070faa4a8b182000ece831d56204001d9ca5b1ec488003b31d163988100073d3b0cb1022000ade8494b63440155d904b22c5881f7bc981718801000577c1aebb1220008fd87d0562c40011fb0e206c2990033d9537158d200074fb26c6a122006a7c854c961940019baebb1a4288002b76167258c1000737c12cab102000add85dcb63440019db0ab90c098803b3152639881000757a0ac4a102000eae7419362440efde70ca0a2008002b76074258c100047ec38a9b182000cde7258d53040011fd0f296c68804b3b1c963506204bf4fa12c698c8000e5d659096304001d5ca8202c4080039ba0865d891000577c12c290ca000cdd54dcd60
  | 13 => 0x65fba4e8b146200af581194614c8015db03aa6c488002b7a0242d8d1000576c1682b1a4200e9d8414b6344001d5aa9a0ec488003bad0962440100547f438a0b1620008fd8715163040019bd0eb1a840800397d4852d8d100067642ee4b1a2000aef8355362440015db09baec488003a755343d8d1000672b16e29902000e6e8719762440019ea85b8ac6900039b95154588100047ec3c8430a6000cde72d8d4344001d5ec92a6c4880023f61f41181320053fc2ac8b024200e6e84197624400f2f90eaa2a508003375d7635051000767b1ea5b122000e6e659d162040011ff0e990c0a08036e5507050610007673a4c6b102000ee7715c762440255dd042a2c690012bba0275d89100053ec2884b1e2000cec7650932440015bf0a212c6080037c54470505100056ec24a5b1a2000cde52dcd6244101b74a838282880033de05764c6200056ec1884b1a2000cef87d8951440015db042a6c498803a7a1464d8d1000767ba0c7b122000e9c8299163040156d904b2aa5880033b61572d8c100071eaa0a9b1262008fe8790b614c0019deeb3aac408003b358d625081038fa7a8aa49926200abe849d7624c0013db05bac8008002b761072d8d100066f43ac6a902000a7e859916188001cbb05b2ec6880037add470485201c79c2a2a89022000e9d649516304001d5d0bb26c4880026f6127654a100063ec38cbb122000aec8750d62040015bb0b192c6080023fa1c54d89300071fb2ec8aa22000e3f549516244001c7d05b2ec888003b5e0d614c6500056f43485b1a2000cdc425cf620400157d0932ec7100031f5d475d8910006f2a10e2b026400e6f5158952040093f100ba44088002bba135358810004eec18e0a946000e6d65d5162040011f90fb1aa310002b76077358e2000737baacab102000ecd831d562040015bf0c212c6080033dd937158132007673acc6b102000aee80dd162040015db0e202c4080039bd53535881011676392c4a8c6200ced72d8a5084001d3e84b1a8208003ab19254d89100056f42885b1a2000cdf635ca50440011fb03bb265280039be1e655881000766ba2c73102000abd841d562c4001d9ce5212c6080029fa1442d8e100063eba8ea3026400ed45458d1004001d9885b1a84881a2db21564885210069e2a6ecaa44000cdc7258e400400157b08294c318002b7e0d7558d210055f420a5b1c2000e6c5219762440014fb0a216c298002bba1d53588100067ba10e2b1a4000e3c8259564040019d909b92c3180029f61474d8d210066eb2ae630c40009ed821c154484095d9052a6c4880039bd5054d89100047ec0ce1b2a6400e9c6450e604c801d58e9322c408003b318a42d8d100055ec20a5b1a2058adc8654c604c8015dd0fa1ec4880038f55054d8c1000757c3ac8b102000cdd631c152040019ec85bb22008
  | 14 => 0xf5495263040f5be50f20220080031f99576548100072fa90a0b182000eaf74d0762440b15b90ca18c0990039721365d8d100071fc12cab2020008fd839c361508011fd0e2a2c5080033d993715813200577400a9b122000ecd8258d42040014fd0a3a2c690802b760f74d8d210056ec2885b1a2000af5811526188001c7ea92a6c2990033719773581210047f43881b122000adf8459563040015bb072a6c6880023f61b744c8100072faa0a8b182000a7c875496194001dd708b142008006bb208505881000773a8ac4a882000e5e8259563040015bb09196c688057ba18b7388110005cec1ce5b226000cee7558941040011fb0f290c298002b760e42181310056ec18a9b026400aec845d5620400157d083aac5880029fa176458e20005bd4008432a2000e6c655d36244001d5ce92a2c4080031f2157118142005cfc22ea9946000a7e85dd363880014f90ab22c0990031f5d475d8e200071faa4a8b0c4015aee82d97628c0259dce4b1c81100025f61c421953042ebda90e0a8c20049f8805d62044001cbd09b2ec688003a7553639011000577c12c6a922002d3c745515204001d9ca431ec488002bb6084058e200056fc1aa8b182000cdf54dcd60884015bb03aa2c6080033bdd962508100069e2a4e3b02a800e6d87d97624400197aecb22a40815f5b99772546200066eaa2e7b102000e6c6554a614c825b9ae6a14c099002bea0052982310057642880b102000cdf631c1424400197ae83a2c710002bd60475d8a1000757a12e430282049f5819c365484015bf0c9926328002afe11655812100676b92643028200abd82d9764440015ef02a10c2980038f61d655901009677392c72844000ead841d562040019baebb1ec488003a79934258c100076b292c78802000ade851036344001d9ac6a126408002bb617415881000576c24cab102000ade801496304001cd8ca3a6c488002b76126258c100055fc22cb3024200ecd7458d6204001d38e92a6c688003b3d4a5258c103178e2a2a89946000eda80dcd63880016bd0a216c68820f5dd5171942100047ec1eecaa02000e6f5214362440015db05a9ac408012bba0864d891005cde422ea99620008fd87108604c401c7ea92a0c098802e7a1052d8d100071faa4a8b0462008fe8758951c40019bee4b1a8408003b318863549100056ec10cbb1a2000af581dd7614c8018fb0b386c2aa0038f59564550100056f404a5b1a2000e5f84d9763440c3abea5b9aa3180032f5d074d893000576c10e8b1c4000cdc75d8d4244001cd90832ec488002fa20175485200072f32ca8b1820008fd8710b6304001d5904b22c408002af21165d85320076729464b182000a7d851906048417a7ce8aa4a1880038f60a659923100672b12e31002000af880595604c8151ff0cb8ca110002bb60c755881000
  | 15 => 0x4b2ac4080039755163544100056ec2e84b1820009dd83dc5528c00137f08baa4388002bb2115358810004bfc2ae89902000dd8205cc61880015bd0b212c608002af21165981215456fc1ae23026400e9d85d9363440019dee5212c688002b7a1321d8d10004f6c10e0a0c4000cf5521c56348001e9aa6a92c099002afa1265186200047f438a9b122000add8755163040015db0fa9ac408003a75504058c100053ec28c9b1a4201aee84d0962040171f90eb2ac988002bbe1153588100065fba4e8b162000cdc7458d5204001c7eeab2ac808002bb60e74d8910006772a2e5b182000ced75d8942440019b8eca9a6488002bba1050d89100047f438a8b1a4000cdd734c860504151fd0c38282908023f61b7348650014df438a53202000aee87551620401fdb100b1c6110002bb60b41d89300072fb28a5b1a20009f581dd620840015eb033a2c310002b7a005458c100056f41081b1a2007aee821036284001d9cc4b1aa4080037554c7158132056d639284a0e2002cbc7459162040011fb0db8a8408003371db6350910024fa43a8290a201aed581d8d314840b978e8b0aa3200029f6176458e2000576c2a87b122000cbd741d16188001a78a83b2a890813baa1b62881100055ec20a4b1a2000aed84d4b62440015eb022a2c318006bb60774588100066fc1ae23026400aef845cf6244001c7aa82a2c7080033be1172d8c100155e422cab202000ead7410162040015dd0c2a0c4880023f61c54d81210067ac0cec994205df1c54551314c0019bac8b98c3100033b1d1624c8100065f424ec9928200e3d7455161940015df06baac408002bba1742d89100047f43885b0a6000ced7558a200400b57d09b2ec8880234f1d15454610004bfc2ae890e20008fb875806048401baae838a64988039719754d8d10034bf42ee91022000eac74d0f624400157b0c294c9188031f59774588100056f42e84b182000a7f855926048401cdeebaa6c488002bb61742d89100066fb9a64b0c80008fd87908604c401cdaa9b12a2880029f61674d8a100055e432a8a12200bcbe7655240440013bd0e992831800337d4b73589102c56ec18e83026470f8c40509324c4019dae4a10c098803b3d4d535881000676b92c32844000e6e87d976244001cdca4b2ac408003b39885298c1000577424cab102000cec74d8952440015b90faa6c6880023fa00764c9410056ec18a4b182000cf842dd91004001cbeeaaa6c6880033b58b714ca50007e2a90e2992626aadd831d3614c8014fd0a322c299003ab90974588100063e3b6caa9220008fe8758d21940015bb06216c7880029f61442d8e1000d77410a0b102000cf787584614c8031f90ea08c090807abdd1625081000756202c4a102000a7e85192614c801cdb0b3a6c488003ab95343588100056f404a9b1a2000f1
  | 16 => 0x2181540247ec38a0b0c40009ed821c1544c80157b09b2cc310002bb60f425881000757b26c4a122000add8194963040019dceab148008002bba1f43588100074eaa6c6a1a200097d85dd22044001bceebb8a651082a7ba0b75903100056ec34c6a9020008fd8710a618c0011fb07bb2a910003abd51545881002e5ec3ec9b122000abc84596604c855f6684a0a20080038fd9772d91100057ac0881b1a4200aed8595162040015ef02ba2c6908039b59752588100047fc1ae2302a400e3f549536388001d5d09b128488002bba1474588100072e32aa9b1a2000c7f759d563484019dae83a6c4880039b10865d89100057c402c8b026498eb7425863190009dcee3b1242880023fe09731814100d77414a8b102000b5e851086344001d9b073aec4880033ea0076486300057d400ea3026400cdf73d8d5244001cd8eba9ec488003ab21664588100071ec3ecbb222000ee96254910040019b8ebb1a8688003ab55040d89100056ec10c9b1a20008fd821d9418c001b7284382828806b735c943985320056ec1ca4b0c6000e3d65d516404001d3ac8b1a8408002bb60774d89100047ec3ca5b1e2000e6d8558a50040019bca5b9ac11080337dcf6350910024ee43aa69922000cbf425da3190001c7ecbaa6c8880033b5cd62486400059ec2ce5b2260009bf845d53284001d3d05322c60800397d8d529411000d7741686b102000cef755cf62440011ff0eb28c2990034fdd675d911000577c30a8b102005abf87d976444001d58c9b128488003b390932181310066fbaec6a1a2000cdd7558d420400b1fb0fb2ec888002b7a105058c10285b742ee91024000ead82193624c0051f90ea88c0a0a93f1908714c9310071fb2ec8aa42000cfa809da31880015df04baac6908023f61c4218530007663148431a2000cf765dc5604c8019deebb128288003f154f714ca2100677bb2849902000aed87d476244001d9aa7b126488003ab95162900100066ebaac6a182040f3454552314400d8fcebb2ec8881a6bba08541853200756214c8b102000add83d456348401da8a4b1a200800337dd563504100072fa96c6a8a2000cfb7655110040015ef02b24c299002b76135258c1005c7fc32e32848000cdd73d8c60484019ee423b24298002b7a0a6458c100076631ea5b122000e5f82d97634400157908b2ac090802b360c7458810004fac0eeb2042000dea851c1324800159b073aec4880038f55054d85300066eb9a64302a29ce5f5258d31940016bb0a216c688003ab55162504100047ec3ca5b026200cdc72d8d51440014fd0b326c710003b5d4963c401000756426c52022000e6f5495162040017d305ba44108002bd604505881003e76396c4a8c2000add82dd7634400157d09baec7100033b21172181310057742ee8b102000e6d82197624c0035d90
  | 17 => 0x102000cdd74d8d32440015df0ba1ac4081ab3b18b714c9513557741081b0a6400a7c85590614c801d5ac82a2c4080038fd5254d89100647fc3ac32844000e3f6594b6444001d5e86b1284081e7ba9096244010005d6c20eab1020008f787584614c8018feeb3aec69080337a1c4258c1000677baee7b122000abd8419760484011f90fb1a8310002b7a125258c1000eb6392a4a882000bba8014864440014fb0a322c099002afa1065d81320072f42ac6a902000dd4541c5324c4019d8ebb148088003a755054d8d1000737aa6c4a8a20009de874c9518c0011fb0eb1463200172f99171902200066e3b0c6a122000e5d54d4b63440019dae8b1440080033b5cb62901300056f4348431a2000abd84197604c801dd4a8b142008002bbe0975588104af563a2c490c8000add83100604c801cdeca2a6c488003f250b704ca300054f420a5b1a2000cef75dcd62040014bd0a216c6880033b1d5624c810005cec18e4b246200e5d755516304001db500396c688012bba08405862004cbf42ceca142000abe8414b604c40173d08290c688003ab9536250910024ee43a869922000eaf42d05620400179b063aac408003b3d0d43d89100065fbb2c8a102000e9c64d0b63440015bd042a6c688003378c9764c81000767b1aa49922004aec82d53624400557908a88c0a080337d5173d88100056fc12a8b182000aef8655162040019baeab1a4208002bb61954588100053fc32a92802000e3d541506148001cbd08b2ac6080023fa1f51d89300056e432a9b1a2000e6e75d4562040015b90ab92c6080033b5d173d891041ebba92e32842000cbd7419362440455dd05a0ac5188033b9d5624c810005aec1ce5b2a2000adc805536344001daf06b0a63100133bdd362509100074e426c6a122000b6d85dd220480013f100baa87880029f2195454a100056ec1884b182006c7c7558521940015dd01baac4080027b608705522000767292c69962001aee82551620400197cedb22a4880033bdc9625063100757322a8b10200adae7250a40c40019dec6b94a1100023f20172d85540047fc12ec98ca000add83148614c001a78a9bb2a918803b5c85634841000576c10a830a4000cef765895204001d9cc5212c608002cfa1272d95100066fa12e630a4000ad4864c931440015eb023aec299003e350d424ca100057742e82b102000aef8255362440015bd0c296c688002bea0065d8121005b7c2ae89944200e5e6558d42040cfe58a8aa44290802b721442d8d1000576422e7b122000e9e6458d52040e3e98a0a926498802bb61773d89100067b210e2b1a4000e3d84d9764440019daebb1242880023fa1e4258e1000736282c4a90208ccdd7258d3188001d3b04b22c6080039b94b75d89100067642ae43026200af880508604c4015bb062a6c7108023fe0d7
  | 18 => 0xc8099d8e4b0aa3100023f60476551200072fbaea9b1a20009fa809d931880015db05b1a84080029f61664586200047f436e89942000ced75d894144001cb8cba96c688012bba0943d8910004fdc3aa31042000aed83dd7624400157b0d294c8080033b5d373d89100057d404853046200cdd635ca5004001d9ee9b18c488003b654d601813200767216c69922000cdf75dcb634400157b0832ac099003b310963508100057d40084b046200cbc64dc5644c8015bb09b96c6880023fa1870509100072fa90a4b182000ced7258a50c4001d5d0a326c488002bb60875d89100074e322863026400cfb54dd910040015df04aa2c5080027d604705512100757216e9b122000aec855c762440192f90aba26588003a795342d8d10005aec288431a2000e9d54d0d63040019bf07bb26408006bba0b5358810007572a286b102000afa86dd220440255dd0432ec49800337d97735812100576c3ea8b102000ecc5498d6204001d5ee8206c4880039b60b65d89100056ec24a4b18206afc783dc532884015d908b9ac408003ab1d143d89100047ec3ac52062000c7f52dcd61940015df0ab22c40800337dd763509100055ec20a4b1820018fe879956204001d3cc9212c6080038fe1d65590100065fba4e83026400ece6210a6304001cbea8b1aa2080023be0971181540063f32ae3b2c4000b6f855d121480013bd0e9928298802bd607641853200766296c6a922000aec8655221484019b8eab1c800800337dd9534c8100fee6b9aa530a6400ade829d1630401137d09bac41080038f596525901002576c38c9b122000ade84d47634400177500296c8880039b99454588100047ec38a1b0a6401aec87d056204001cb8cb296c688002bb60854d81320074f410c9b1a2000cef72589518c4015b90b212c608002bb21c54d89100066fba2c6a102000a7c85593614c801d5e85b92c3200023fa1c54d8e10007a6a9aa430a6400cee8758a40040015bf02aa6c688002bb61f515881000766416c6a922001eea7058a2004001d3ca8b1a8408002bd607641862002e5f43ec9b122001aee87d45620400157b08296c788002b761774d8d10007e2a926498e2000ced72d8a5044001c7ea92a2c588002bea0374181210074fb2685b1a2000aed83d5162040011ff06bb243200139ba1752d89100073632aa9b122000ead74d0d6204001bd10838264900027b60b7150e200066fbb4c6a102000e3d54153638400157d083aac4080029fa1674d8a100056e43485b1a2000e3f655cb644c0011fb0f292c60800f4f1d5545081000737a9ea4b102000cec7458921040014fd0b320c3100031fdda6550810005dcc26eb1042000aef845cd6204001f8aa5b8a64988027be0975506100066e3aec7b122000ead54d0f62440014fb0b326c310056bba0b64d8a3000576c24eab
  | 19 => 0x23fe1d6418532004df438a5b222000e5d65151630400157b093aec4980027ee1d41882100057742a86b102000afa8094a608c4019ee85b8ac6900039e9db65881100055fc22cbb026400e6c7599562040014fd0c3a6ca880038fd5254986300066ea92e630a4000aed811d762440015dd012a6c488002b72195418d1000677ba8eab102000ecf7354f62440015eb02202c69088abba0a6558a31007c6a1a85b026400af78154b614c0014ff0ab20c0908033ba177258d1000676b968430262009f8875462044001d5cc9aa2c4080033b58870486500072ec14cab182000ade8094963040093790eaa28488003b355263988100056f430a431a20229df835c7644c8013bb06382a498802b760e42d8d100052ec2885b1a2000cdc7558d42040099db0fb14a088002bb61d43d8910005f8c0ec91042000eaf7599162040015db0fa1ec488056bba0840d8e2000767baac73102007be8825062084001d9ca5b1a65080063fa03715962000576c1eeab1020008fe861c13250401d9ce9b1ec488002bba1c75588100047ec38a830a6400cbf749d363880019baeab1a8208003ab58942900100047ec3cca30a6400af88050b604c401c7ecba96c888002f960675d891000677296e6b102000ecc7290b6344001ee2a8a8a2008003abe096458810007572a0a8b102000aef871516204093f8c8499263880038f5505458f100066f392c6a182000ecd63d096204001cdea4b90c0a8803374ca70d8d21116e7b9aa4b0a6415aee82193628c0015dd0a2a2c4080039b5d55358810004fc402e890a20008ff835c460508015d90fa8ec488012bb20174d89100073642ac4a902000c7e655cf6588001d3ca9a0ec688163f2e0c704c92000576c2ce9b122000ced859d862440011fb0e292c788003a76105258c100acef43ec89946000cdf74d8e20440255dd05b2ec4980023fa1c52d8e100057742881b122000e5f6510b6344013a78eaaa28308297f190b714c93100772c08a0b1020009dd83dc5548c0015bd0a212c6080033b60a70d854200677ba2c4a902000add848c96304001c78eab2ac80800f1f19470545410acef43eca9946000add82dd363440011fd0db8aa9180033bd8870509100067d102e230264008fc8758d418800175b093aec4880023f60476552200078eaa0a9b1a2000bcf82591324c4011fb0e990c0a88038fd5254d881031fa632aa499460008fe87101628c401c7ea92a6c688012bb20175d891027ed73a6e910240008fe87d95614c8019bca4b9ec408002ebe1175485200056ec10e9b1a2000a7e8690b654c0014fd0da16ca88002b760654d8d1002e5ebb2852062000c7d751d561880019bae9b1ca0880039be1365d8910006763aec4a122000a7d851d3614c801d9aeab1cc408002bba17435881000576c14e8b1a42008ff87594604
  | 20 => 0x373a8a0b102000add8114b63440019deeab9ac408002afe0965590100053f42ce9b122000ed55458d10040019dee4992c320003ab61764d89100047f43c84b1a20008fe87191614c801d9a84992c3180127b20975505100057ac0cc930a6400abd841d7614c801de501b0cc310003ba58942840100053ec3484b282000eac5259162040011ff0cbaa42081bf57d4b73545310067a2a6ec8802000add8414b63440015df0eaa6c488002b761353d8d100057643aa6b102000adf869496304001cdb0f32ac4080032fdd9645501000768b1ca08802000af58119461880019beed31aa4080029fe1954548100057643ca8b102000b7a8010b65440019dee93a2c4080023f61c5458f10007e2a126498a2000add82d9363440014f90ab24c0990023fa1b75485100071faa4a8b1420008fd811d9544c001cdacbba2c4080039b14b65d89100047fc0ae6302a800e6e84d9762440019d8edb128488002af61052185300077542ac48802000bd7835513144001d9ca9b1ec488003b38cb635091000676c2ee4b1a2000aed819d362440011fb0db8a6528003b31d663588100067d296ec8802002cbe641c14188001bca85b8ac09902a7d21d51487100072e42ec6a922000ade821d76344001b9ae49948118002b7a025458c1000576c10a0b146200ed763dc532840015bb072a2c608002b76144258c100056ec18e830242008fe87d95604c801cbec6a9aa48802e3fe1d41181210074eaa2c72002000aed82d516204001d9aeb31ac4080033bdc932586500055fc22ca3024200eae82d93624c0011ef0eb08c31000e5f2157448410006bca90e0a8a2000adc87d4b634402b9d8e5b1aa310003379d85418d100071faa4a8b1c4270f1c54551324c4015bb06202c690802bb61440588100072fb2aa9b1a2000e6c65d5362440019df0bb92c318002bb608545881000576c28e8b1020008fe8715163880014ff0caa2a608002bb60b5158d210072faa6a5b1a2000af581d08614c0019dca9b92c318002bb61d5358810004bf406e2aa2a400abd84dd76388001d58eab22c408002b760c74d8e200056f40484b182000e3d5415162040198fcecaa4a0880026f6047050d420053ec28c830a6400e5d75d5163040015bd05a0ec6880035d551719401000676c10eca0c4007aee82d076284001bd4a838264900023fa1b715513200756baac8b102000be982dd620440015d90ba0ac40800397a0b65d8d10004f6c16e2aa24200eac82591628c4015bb0b312c6080034f55070545410659e42ac8aa62000c7d751d763484035d90f32ac40800337d8f72505100047fc1ae4302a200ced8758a50040155d904aa6c588002bb60e54d89100055ec20eab1a4200aef8710162040013f70eb00c099003ab19142985320056f42880b18201fcec7258d4148401da884b1a20080
  | 21 => 0x819d163484015dd09b8ec488002b760c4218530055d6412c8a1620008fe86dc5428c00157b0932ec31008ab721953985320047ec38a830242008fe8758d4188001c7ce532cc918802bea0364d813200577406a4b10200197c8755152040019b8e9b1aa28800f1f21d655881000f74402c51002000e5f5258d51040013b90e9928318002bb61371d89100469e3a2a8a9c2000cde329d932440014fb0a326c090802b960440588100047e43a643028200ead4358942040015bb0a3a6c6880026fa1c52590100079aaa2a2a0a2000c7f759d7624c0014ff0ab20c2990029fe1564d8d2100576c10e9b122000ecf82d8d52440019b8e4b1aa208003ab9d464d89100056ec18a4b0c6000aee87951620403f9dcc4b9a432802b3b1c96254710007563a2c8b102000e6f52d8951440013eb02382a908002b721b54d8d1005e5fbb2a8a082000aec8550f62440015dd0fa9ec48807f3b98973486400047ec3c84b1820008fe8710963840019dee7b12a488002afa126558e200063ebb2caa102000cdf74d8d51440019dee6b124328002e76105258c100047ec14e1b0aa600e6e651d162040019dee7b128488002bb6084058d210047ec30e0aa242009f8805d132c40011fd0e2a0c09904b3b1cb62505300057d406ebb1c4000eae5299162040019bc84b98c290003a719242d8d10005f8c0ecb1042000e6c65dd36244001cd8a532ac408003379d3635451000766294c6b102000e6f6254a50440018feedb92ca08002b760c52982310047fc1ae5b0aa843f385455310840074f90a990c0a88033ea00764ca1000537428e8b102000af581109618c001d3f05322c60800337dd372d8d100056ec28e5b1a2000aef86d5162040015dd01a12c408002bba1c50d891002d5e42264b0c8000f4d5354b614c801c78c832a8488003a79d15458c100053e42ae8b1a4200ee98458a10040011f90cbaa82880031f61670d8552005cfc22ea9926200e6e85d8952440015bb0e292c6080023fa1c5458d100047ec3880b1620009bd8714864440039deeab12a40807ef3209654c93100767ba0c631220009ef825c640880019f4403b264880029fa1764986200047fc32e518ca000eaf421016204001c7acbb92c918802af610651853200677b96c4a8c2001aee82d45620401737908bb2a58814f6b1d1744c9200056ec18a5b026200eae85991620400197ae83a2c4080027e60870546100066f3a2c6b102000e9f64d8d5244001dd508b122008002b7a1062d8d100071faa4a830242009fb8758060484013bb0e210c6880033b5d5629001000774a92c03026400cdf63dc9534403f79904b2264988133b1cb62545100066f3aac6b102000e5f75d4b6344001d5b08b1480080029f61664d8e20005f9c2a8288020abed632584614c8011fd0e216c6880033bdcb6250610007
  | 22 => 0x3a2c408003abe1362901100066f3a6c71022000adc8055163040017e30aa0a2008003b31d663988100072eb28a4b182004aee82d0561880c5f18e8a126518002b76185458c1000576c16e9b1c4000ade8215163040018faea3a8c090803b650d601813238fa732aa499262009ed821c143484015db083aac408002bba1470588100074eb2684b182072bd6871c5324c4011f90e992c3200033b5d3624c91000737416cbb126000af880553604c4019d90fb12a4880039bd9474d89100076b2a2c788020008fd87153624c001d5aa82a6c4880029fa1872d951009774312e71022006b3e85d9154440019dee4a12c318002b7a1365d8d100074fa0ec6a12201fadc8654d614c8014fb0bb24c3100033b949764c81000736aa6a5b12202bd77545c65004001cdeeba9ec488003b8589514401029fc63a2869924000cec7654932440015db0daa2c4080033b21d629401000d76412a230242079f9879422084001d5b05322c5188033dc8676485300071faa4a8b1a2000abd82996648c4015db05a8ec498003ab9d342d89100056ec1885b026280dbb421c141440016bb06392cb188032fdd564588100074eaa2c6a182000adc8695363440013bb07b8a85180033ad887048510004f6c16eb2062000ee586dc532884013df0eaa264900033d59071581320056ec0ea5b1a2000eac64d0b62440011f90eb1aa310002bbe1543d8910006f5ba8e099240008fd8710b604c401d9ce9b18c4880038f597525901000f67b9ac499020008fd8714163484015d90caa6c4880033b1d562484100055e422ca3024200cdf7358d61880916f50bba441080027760f71549310078eaa0a831a20008fe87150604840157908b28c099002b7e195498c1000736aa2c52802000b9d83148644c001dae83b1a82880931f21d6558a310055ec34a4b246200cdf7558d4304001a78a8b86c2aa006bba08401812100756c24ebb122008abe84d976484001cdca432ec488002bb20154d89100056e412c8b182000afa80dd460485277b706b00c099002afe1165d8d210066fb9ac6a902004aec8215362440011fd0e296c688012bba0854d89100067da96ec8802000de5521c5604c8019bee6b1a8408003371d56350c100047f43ac690c8000ecd63589520400197e84bb2632026f9dd49614c6500056f410cbb1a20079f987d9220840a375908baa42900039758d529401000577c2ae6b102007bae82d914284001cbb04b2ac60800397d4a52d8d100065fba4c8b102000ecf5498e6204057ee6a8a8a20080232f9d364d8a1002576c3ecbb122000aec8559162040019bca9b9ac4880033bdc961506200047ec3e82b102000ade821016304001d5ae8a1ac4080023fa0376551310072eaa6a7b1a2000cdd831d9518c0019bea4b9ec408003ab55143d8910007a6a9aa49962000af5
  | 23 => 0x4871000736b12a4a882002d3c7455151040035dd0f32ac40800337d4b735822100c7f43cc8b102000aef87d536244001978c93b28488002b7e055458c1000767314a53182000cef745cf6244001c7acb392c808003379db635491002e5e3a2c290c8000bba8094b64440013bb0638285180033d90b7158d200047fc32e518c80008fd87994604c8019e8a5bb220080039761365d8d1011577410a0b146200ade84c8563040015b90a212c6080033b908764c9100057bc0acb30c4000a7e859916388001d9ec7b128488002bbe1d53d891000766c12c6a902000cec54dc96344001f62a92022008003371d363941100074fc2cc8b1820008fd871096304001d98a9b18c4880039b59654588100073632ea5b122000e9c64d8d52440019bac9b9ac09082abba084058b1000676b94843026200af581dd3614c8019eb0f908c298002af6106558d2100676baac49902000e5d75d496304009adce4a94a088003b5d5163440100066ec3ac6a102000adf855d163040011fd0e32ac0908037554f715813200577426a3b122000aed821d3624c0015db042a2c1108033bdd762509100056fc1aa8b0c6000ced74d8a5044133d58e8b126520003972116558c100047f436ea9942000cef825c4605480d8faecaa4a188002bb61a54588100056fc34a8b182000aee84dd7624400153d08292c608002bea0374d8e200066eba2c699020008fd821d95484001cdb0932ac4080274f9d554902100074e3a685b1a2000ece4258d62040014fb0b320c310003a75505458c10007373a8eab10208feda639c363880015bb07a0ac690802af2117558b100072eaa6a4b182000cdc75d8d41440015790caa2850808ab721943985320053f4348432a206aaee82d07614c817a78e8aa2a588003aba0864d891000576c16e9b122000b6d859d3624400177500396c8880023f61e42d8f1000767b9485b1a2000a5e85109630400157f0eaa0c0a084b735cd529813200796aa0a93102000cef741d362440011fb05386c2a1802bbe0554d89100071eaa0a8b0442008ff874c86054401cbccba12c608002b760850d8d100066e32ae630c4000add83109618c0014fb0a326c2991fb3d58b714c8100071fb2ce5b222000aed8214362840095df0fb26c48800337a1c52d8d1000677b16e2992a200ecd6354932040011fd0e2a2c31000397d9754d8d10005bcc2ee91042023cbc87591628c401d5cc9a92c408002bb60c54588100074f2a081b1a2000c7e859c361550018feeb32ac4080033bdc9615462000767192e6b102000ade829d56304001b6aa8b8c8108003b39d063d891000757b2685b1220009f7815d132840015d90eaa2c408002bb60f74d89100056ec24e4b182029cf5625c620040015bb063a6c6908023fa1b7590110007672a0c7b122000add8310a608c4015db0d
  | 24 => 0x2000cdf7458e20040015db0f2a6c488002bb61075d89100056ec1cebb122000a7d8610965040011ff0e992c3280033d5db714c8100047ec3cca3024200cec74d8951440015bd083aec6880039b10a655881000676b92a43026200cdd631c14204001a78a8bb2a808002bb61373d8910005f8402a2a0a2000e6c529d562040014f90caa2a2880023fa1e52582310071faa4a8b182000abd8414a608c4011fb0e202c518802bb60b74d8a10007662a2c73102000add8795163040013eb03bac80080023fa1b74881100066f2a6e6b0442009bf845d532040015bb02292c6081b3d31d5534ca210057643ea7b122000e6f5458a5004001bb501b9a4318003375d163940100053fc2ac9b0a64008fe8714b614c0013f3043828288002bbe0953d89100056ec1ca4b1e2000c7d75197624411ddd484b00c0990029f6147458a3154eecb9ec130264008fe861c143484018faea3aac69080337dd563508100056ec0ca8b182000cdc74d8f62440015db05a0ac4080033bdd56290010007573a682b102000eaf74d0f62440019dee9b1440880039b5d751588100072f2a2a9b1a2000c7e859c361508011ff0eb28c090802b7a1353d8d100063fc2ae2302a400eae841d562040011ff0cbaa840801e3f2197488210004eec1ee2aa26200cf552dc56348001d9ce8318c4881627ea03735862000767212c69902000add831516348001cbea3b1aa488002bb60654d891000676b16e2a902000ead741d36244001d5884b22c40808b3b1cb63545210074fb2485b1a2000afa801d0604c80f1fb0fb2ec5081ef7ca1e5044010007662a0c63122000e5f54d4f6344001d5ca9a0ec4880033b588704ca5009677396c528260009f787584614c801d3ca9a12c6080039b54f62549100aee639264a0c6000a7e85193604c8097d104a8c4088002bb60854d8d2000766292c6a902000ecd43d8932440c9f93043826518003371d9434c91000737424cab102000e3d5415363480015eb02282c5188032fa1e6458810006f3210e2b026407aee82d9362840015db09baac408002af21165d8d210056f43085b1a20008fc865d5324400137b09bac41080023f61b754c81000577c3ea7b122000abd84197614c82b5dd05a0ec710002af612655862000677b1ee4a0c4000e6c42d9762440013eb03bac40080037a9d0704c9200fd6e43286b0a64008fc865d532840013d90eaa26490003379977358121006ea3a0e29926200cdf835c46050c013df04b8ca110002b7a135158c101157741081b1a4200cbf749d3624c0015b90c2a6c68800337d8f72545100065fba4e9b122000ced84dc96344001c7d04328c8980037550c715813200796aa0a9b122000eaf43d096204001c7ea92a6c690802bb60840d893000536c2ce9b1220008ed829c36155001d5ca9a16c48802e6f21175
  | 25 => 0xa775908baa64900033b9d562508100056f432a9b1a2000ed56350b10040015b90a106c6880023fa1c5258e100072f32ac6a9020048fd87d8a4044001f1a86a126408003ab2116250810007a6a9aa53026400ade84197634400557908990c0a09633b188704c9510056f41682b182000e9e54d0f6344001d3b04326c688002b7e097558c102b7962a2a910c4000cde75d8d4144001c7aeaaa2c320002b760b65d8d100055ec34eab2020048fd871436244001d5b0ab22c4080023f61c5058b10007742a2c48802000aed84d4f62440019dac6b94a110003b38c963508100076ba8ec6a8a209ae6c7558921940015f501b26c090803b858941440100056ec18a1b0a6400cbe765cb644c0017cb03b2c431002abba0b4158b100066eb1ee4a082000add851936344001c7ea92a2c710002e760c52d9110004fd406e2a94206bf2c5455132884011ff0cbaa82080032f21176486400047ec38a9b1a4200aee841c162040019b8e8b1aa208002afe195450810007b8a94a08802000eaf4258a40040019dee4b1283880039719654d8d1003c7ec3ec9b1420008fe8714963440011fb0e990c0a08033758f7254c1000736424cab102000adc851036344001cdaa8b12a4080033bdd9524c8100071f32ca53202000d3c54dd954040011fd0e292c318003ab5915458810006763aac51002000cde8710b6344001d3ac8b1aa408162bba084018132004fc402ea9962000e6f65553624400197ae83a6c690802bb60b75d8e20004f6c14ecaa420008dd8714963040013bb07b8aa89929375108714c9310056ec1c84b182000cdf655cc61880011ff0cba26588002bd604529863000677ba6e7b1220048fd8758640880a9ad8eabaa64900afdcd4951440100057643a87b122000a7d85192604c8014ff0aba2c6908023fa1c5458e100056ec16a7b1a2000c7d751d562040018f8ec32a8488003ab9d764d89100076b292c68802000cee761506244157dcca4b08c299003abdd143d891000756326c4a9220008fd821d9414c001cdea9a96c4880033750b73589100057d406e7b142000add85d0763440017b500296c6880025fe15744cb103078e2a2a918c6005abd87d9764440018fb0e32ec498002bba1275d891000577c12e8b146200e6e82197624c0019bae9b1ec4880033bd8f72546200055ec20a4b0c6004aee82d076244001c7aa82a2c51801b1f9d765d89100063eba8cbb142003c7f7654951c40014bb0a212c608002bb60850d853200536c28e8b1020008ff815c86050c015db042a2c518003b35ca4258c100057bc0ae6b0c4000cef74dcd6204001cdaa8a9ac4080026fa037155142007e2a1ee29944200bd5811536344001d988531ac408003a79534158c100067a2a0e2b1a4000ced72d0b6304001cbac6a9aa4080033b94973d89100056ec18e8b1
  | 26 => 0x33d5cd71d8a100056ac08a0b182000aee85dd3624401367d0bb22a9080023f61d629431000576c16e9b126000cdf7650d32040016bb07396ca980033b21f62505100053fc2ac93026400e3f54950614c001a78a9386c2aa01ebba085458a10007563a2a9b122003d3c755514304001cdaa9a9ec4881a677a1b7154d320066eb1ee4a882000cef855cb63040014fd0b3a6c7100038fd5254d81210071faa4a9b1e2000cef7214963440019bee9b1aa688003b31885218d10526ea290e29926200e6d6558942040019bce8b1aa208002bb60850586200076ba92c68802000cef7258951c4015ad8e4a92a388002bd6067058d21004dfc22ea90a20008ff825c46050c013f70cb846310006bba0b41181210047fc32e89082000aed8115162040015df04a08c09080b2f19070505210055ec20a5b026201aee8759162040011fb0e2a2c588003a75924258c100065fba4e9b0a6400aee8599162040015dd0e3a2c408002b760642d8d100072e412cab182084dba541c14184075d750c3244088002bea02645812100757210c9b122045f385455120840018feeb3aac408002bde0542d85300056ec20a4b182000aec86d5362440019b8e9b1aa6880032f5d074181211667c384e0b102000e9e42d8d42440014fb04320ca88003b39d163588100067742ae43026200cf5819c363484019dae4b1480080027d604705522100677b94a4b046271f4c75549324c4015bb07296c708003975944258c100047f438a8b0c6000add84d4d6304001a7ae92a6ca880023fa1c425823100677216ec99020008fd8758d21900013eb02382a898802bb60b75d8910007e4a96e099460079f8805d220840019dca53b26488003b39d563588100071eb90ca32260059bc845d5324400157d083aac518802af61065981320047ec38a930c6000cef7558921040015bb06296c6080163f61d61942400074e206c6a122000abd82d97644c001ba8ea38a6498857739c932902300057d400e9b142004aee82103624400157b0932ec7100033b9d362545100047ec38a1b1a4200e9e641516304001c7ca9b2ec88800397d535258c10006f5ba0e09924000adf87d5163040015dd01aa2c408003b31d2635881000577c32a910a4203c7c651c151484f37e303300c090803cbd5254189100076631ec4a122000de9841c13248009b58e4a128288003ab10874d8910005a6402a6a926400cef72d8951440253bb07386ca990af5dd49719401000756ba0e8b102007aee821436284117daa64b0a63100023f61f4158e2000577c2ae3b122000ecd5498d62040013df04baa820800375550714c9310071f3aecbb222000d3f749516504001cdccaaa2c40800f1f99470546400047fc32eb1002000dd6751c5324c40197b09386c2aa002b7a184218d100047f400ec992a200ade849516304
  | 27 => 0xfc18ec9922012aee8210163880019dce9b1440880039ba1562544100567d434ed1022000eae429d162040019baecb1aa4080023fe19754c8100066eb9aa63024200cde7655063440017d704a8c40880023f61c54d881000576c1ce8b102000ead43d09620400157d08292c118802bb61664588100056ec18a1b1c4000aee859c162040016eb033a6ca88003b5d0563504100072fa9ea5b1a2000b3e859cb6444001d9cc4292c6080039bd9754d89100071fc12cab246200aed8215163480015db05b1aa408003ba61562440101e7e89926310220049ee82dd64044001d3905b26c688002eba1075588100072fa94a4b18207fef28688210440011fb0c382a6908034f5d0745941000737aa2a6b1020079ee829d954840018fd0f32ac408002b7a0a54d8d100056f42841b1a2000cef7558a2004001c5aa82a6c4880039b21d655881000577432a9b12200a8fc8758951c40015bf04b22c608002b760c54185320047f43ac4a0e2000bf18494110040015db0fa0ac408002f6a005218d1000e76392c52802000bb5819cb64440019baebb1c40880038f95165590100056f41687b1a2000a7f8559360484011fb07bb2a988002bb21a54d891000767316a53182000e5d655516304001daf06b08c299003abd076250910004efc1ae030aa80c8ff87544604851f7d704b00c099003371d563588100072eaa6a6b182000ecc6210b63440011fb0db8aa71000f4f1d5545041000757216c9b122000b3d851c9648c4015db03a96c488012bb20b51d89100074f2a6c72022000cbd741d163484017ab022a0c688002bb60850d8e2000757b26c4a922000ecd624c931900019bae7b1ec310002b7a0a6558c1000772c0880b102000cf442dd91004001cd8caa96c09900acf2116555010005f8c0ee71042000cde545cf6204001dd10ab1220080029f21564981210663fbb2a4a882013cbd87d93624c00179f04b2a6498802afa10655813200577c12e8b162000cef74d89514400f3f100bac4108003b9d07625051051f73296c330a64008fe8715363880019bee8b1aa208003755cd611862000577426cbb122000eaf855916204001cbecba96c688003979964258c100056ec36853182000abd8694964040095dd0432ec48804a7760e70d85320047ec38a8b1c4200cec84dc96344001d5ee9322c4080027761c4258c10006773a2e8b102000a7d8519163484013df0eaa4409000397d5254d8d100aee7392652846000abd849d76388001c7ea92a0c09900a6fa1375880100057ac08a1b142000e6d655d162040c7e98eaa926518003ab19142d813200775a12c5080200cd3c7555142c403f5d904aa6c498803b39d663988100066e3a6c69922000beb82506204400ba7ce8aa4a0880023fe0d7118154025f4412a89022000abf82595648c4015db052a2c40800
  | 28 => 0x45891004001d3e85a0ec688002afa1052181310056f42e43b1a2000abd8499461880015bd05292c608003ab95162504100056e43085b1a2000e3d541516348001d9ac6a126588002b760c5258e1000737c38cbb122000cee74589520400157b0c294c80807ebba0a65589310056ec10a0b182000aec845c762440019dee5a12c318003976116558c100055fc22cbb024200e6f7599562040019bb0e212c608002bbe1171d891000577c12e2302a800ece32d8d524400b37908baa42881e7ba14962440101157741683b1a4200b5e8510a6304001d3ca8202c608002e7a105298c1000577c12a9b162000cef63dc941484015eb033aac3100039719763509103ce7cb8ce1b142000e6d84d9762440015bd08106c688003a7191435853200767aa4c6b102093fca521c1328c001cdecbba6c488003ab21362505100066f3aec69922000e1d5415163040031f90eb2ac408012bb61f64d89100071faa4a9b0a4000add8694a6304001cdccbaa2c4080033be1172181310066f3a2c710020009dd83dc5424c401d9eeb31ac40815aeba1365886200247ec38cbb122001aec8210162040453bf06b8eca99003b355363189100063fbacebb142000e3d54151628c4015bd0f296c688003b3dcd43d8910006f8b8ce1b1420048fd8710161880019d8ebb128288002bba0274588100074eaa6c6a0a2000ead7519362440015db09b9ac408003abdd564588100056e42e42b182000aed869d562040019eeecaa22008002b7e1642d8d100071f390ca32220008fe8714a608c401cbf04b2ac6080127d60670d912105774314ed102206ef1c54552314c4011fb0db9a43200073be1d62544100055f424cb30c4012cec7258d51880011fb07b92c3200127e61e40881100257742ea5b122000ece839d762440132fd0bba441080039be1562548100053f4288430262009f88750620440012fb0e210ca88002bb21c50588100047fc12ed18ca000ade8010b6344001c7b05b2ec898003a7d0563508100047f43ac4a082000eae74101620400197cc8bb28408003b5e19324c71035577410a1b0a6400e5d841976344001cdcea3aec488002bb60850d89100078faa4a8b182000aed829d1628c401d5b0e326c48800337d9373581210056ec1e85b1a2000ead8599162040013f501b8aa888003379d763901100053f42884b046200e6f5258a50040019dee8b9ac4080027721d32505310073642ec52822000e6d7514162040015bb03a92c608002afa1b52d9110026d73928520220008fc805cb6150c011ff04b88c0a98038f551619424003df5416cb1042000add8310b63040015dd09a92c408003ab95040d89100057643ea6b102000ead64d516204059dd041382c4080039bd5162548100066f326e6b024200bd7815d1324c401baea838a64988033d1487158d200066
  | 29 => 0x2c431000397e0a6558c104f7363aac4994a000e9f6415363440455dd05a8ac518803a7d5154d8d100056f416a7b1a2000abe84194614c801c7ecbb2284880023f61c52d813100c7e43ac8b102058aee82d04604c8015dd0eaa6c4880029f61442582310047ec16ecaa46200aef87d07624400157b08296c6080033b6127618910005ed40485b1a2001e6f7558952040019dec438264a0803a79536350d10004eec18e0a126200e3d54153604c801cdca5b2ec4880038fa0a6599231526eb290e29926200aed8214060484013db05b8aa9100023f60c76552200072e286c6a922000f2d5415162040011fd0fb22c3100033bd8f72545210066eba6c71022001fe3711c12148001dd2c4a942008003abd5254588100057d406e63024200a7d85108604c401dcf02b9ac4080039b95154d891000577420a8b102000e6f51d8952440019dee5b128288002b721321d8d10004fc402ea90a2000eae87991620400f3b90ea9a6508006bb2094358810006dca10e0a0c2000aed87d4f62440011fb05b9ac3280334f1d55450f1000d76412a6b102001aee82d5162040011fd0e322c3100023fa1f51d8e200071faa4a9b162000ade84d4d63040015f501b2ec09080397a0a6558c10007373aaa8b102000e9d82d936344001db041b1c40880033760e764ca10006f5c20e09924000cdd8710b6344001dcac4b8c4008002b7a0850d8d10064be42ae890e2000cf564dc5604c8015db073aac40818367d0b735063050756322c910a4200af5811d3614c801a78a9380c2aa002b760c52d85300073632ce9b122000ecc74d8c62440011fb07386c2a9003a719054d8d100071e416cbb222000afa80dc76388001d9ee931cc408002bbe1f435881000737aa6a7b122000adc8459563040035dd0f322c4081c3e31d1424c931006f4ba8e090a4000f8d43509604c8015db04282c5880033b61f6254510004bfc2ae890a2000cdc7558d4104001dcac5b8a6408002af21954901100547fc32e32044000cdc7458e50040019b8e8b1ac408002b760f54d8d100055e43a84b0c8000e6c8799562040013bb0e290c6880033be1f62549100056ec18a8b0462008fd8714b63c40011fb0e2a0c2900029f6166458e200057bc0ae8b0c4000cbe645c76488001d9cebb1ec488003bad88704851000676b9485b1820008fe801d954484011fd0f216c6880025f6167650a1000677ba0e8b102000adf8355163c4001dd0a0b14a008002af61375d8a100057c402e8b1a4200ead54d8a40440019b8e9b1a4288003ab5d764d89100066e2a2e630a4000ecf52d8d52440014fb0b3a6c710003f1549324c5100066ea16e6b0442008fe80dd9548c401d9c84212c608003371d7634c910006763a6c52822000cfa54dd91004001d3e87b1a8488002bbe09511812100736c2ec4a922000ee88
  | 30 => 0x4c100056ec16a6b182000abd841d46048401baaea38a64989f3ba90962840100071faa4a9b026200ece4210b63440015bb0a106c688002b721721d8d100073632ca9b122004eaf74d8942440017b501296c688003a72096458c100056ec1885b0a6000bf181dd220840019dcebb128288056bba0850d8e200055e422cb30a6400cbc845c460550011fd0db8aa9100023fa1c545823100736c14cab1462008fe8715163484019f50c382a288003ab95343d891000766a9264b0c6000eaf745d362440095dd04282c310002fce1151440100047f438a4b046200ade85dd36344143cd8cab2c4290802afe1165185320066ab1ae31002000ed5325853190001d590ab22c408003b9d4762545100547fc3ac52062000e9e641496304001d3ec6a148088003a795054d8d1000756c10c9b122004bea809d762440015eb02202c4080033750973d88100047ec0eec9948000aee84d4f6244001d9ec6a126508002af61275d89100047f43ca5b0a6000b5d8510a63040019aac7b8a64080023f61f51181324ef3ba92c318ca000e6f8499562040011fb0e2a6c5080023fa1c549822100d76412a830a4000aec851036244001cdaea3aac408003ab5d1545881000677b9084b1a2000aee8419762440015db0a326c488002cf61672d9110034be42ae8992203cfc6424c93144001d9ca531ac408003379d85218d100066f3a6c6a9a2000ed773dc563484019bcec210c688003379db5418d1000737416cbb12201fdcc724c9414c401cd90fb2ec48801e7721d434ca1000736426cbb122000e5d65d51630400d8fccab8ca1100073b1c962504100056f42e83b1a2000a7e8599261880014fb0a3a0c099253f290b704ca300056f43ca9b1a2000add83dd763880015db05a1ac4080037990b7158132054be43aa8a9620009f5811c15404001d5ca4b22c408002af60a65990100067643ec4a122000ced72948614c0017ab023826498803ab551625081000576c16a7b122000add831096384001d5cc92a2c4080025f617748821000737b2ae9b122000e6d54d456204001cbca8aa2c60800397d4563548100071eb2ae4b202000eac425d16204001c78ca322a48800337dd3635491000576c2e83b122087dae645ca40880015db042a0c299002b7a1743d8d100056f43ea9b1a2000cf5215c763880019df0eb14a008003b3d8f42d89100047f43881b0a6454b6c855d13248001c7aa82a0c2990025f60470551520055fc22cab026400aed831d762440015d90c2a6c488002b760c5258f100067d430e090a2000e5f54d4d6304001d98c4210c688002ab61275d89100053f428e8b1020009de874c9514c401da2c720220080031fdd675d85320075742ac8b1020008fd871536244001c7acab228408002f960454d89100066fb9aa6b0c4000ecd83d893244115cdccbb
  | 31 => 0x2000eac74d09620400177501290c888003a7d0a42d8d100065e3b0c8a922000e6e65d4962040019daebb144088002b760e4258630526eba90e29926200abc84595614c8015bb0a206c6880033b9d174d8910005cec18a4322200aaee8214162c40095df0e286c488003b390a32d8d10007363aaa7b122000eda808cb63440015790caa28688003ab1d464d89100257742685b122000ade82d976344001d98e8318c4880033b1517218131004fbc0ae89902000ecf54d8c6244001d3880b1a84080033b9d562484100067a2a6e2b1a4000db5545c640040015bd04282c60800337d0b735891000757410c9b1260008fd87153614c801cb90432ec688003379db635091000737a96e4b0ca000aef825d5628c401d3ae8aa2c608003a79534358c100053f43485b2a20008fe871436348401cdca532ac408003e350d4218532006773aaebb122000cdf7658d42040015bb0ba0ac608003a7e1464d8d100055f420cb3024200e9e4258d42040015bb05aa6c688003ba9c070588100056ec26cbb1a2000e5f6594b63440015b90a102c608003b318852d8d100056ec18a5b1c2000cef621c132544015db053a2c5880033b5537258d100074e42ec9b1a2000aec855d36244001c7aa82a2c4880febd60670d8d2100756b26a4b102000ece7518f62440019e88438ac690002bb21153d89100066f3aac6a082000e9f85d9363440014fd0a322c090803ba10162900100071faa4a930c4000cee7458a50040015db05a8ac408002bb60c745881000576c1cebb122000cf5819d9214c001c78c9210ca881a677a1b7150d320047ec3ca530c6000ed75158d5104001d9cc4212c6080033b5d373588100057642e86b1020049f4875452144001d98a8b1ac408003bc58951440100071faa4a8b0c6000fc9531c132480015bf06aa6c7081e73ed88704851000577c1ac4a102000add8215363440015bb07ba6c710003ab10362509100067a320e2b026400abd86d4964040019dae8b1242080027b6087050e2000767a9aa7b122000e9f745536344001c7aa82a6c508002b721741d8d1000737b2ea5b122000aed83d4962040015dd003a2c4082373d5c9618c6200056fc12e8b182000add839d561880015b90a202c6080032fd0a70d8554005f4402ea9924000a7e8519260484019dac5b8a8408002b760c4258f10005aec18e4b282000af581dd762840015bd0c2a6c68802f2f9d942901100063f3b2e5b2a2004aee821436244001d5ce9a1ac4080023fa1c4058d2100736a9ea4b102000a7d85190604c9479eae5b0cc2990038fd525498231006eaa1ee2b026400aef87d4d62040019bcebb1a8688003b355063189100056ec24cab1820008fd82dd9544c4015d90cbaa42900034f55070506500070eaa0a9b1a2000cf754dd91004001d9c84992c31800b4f1d1545
  | 32 => 0x1d3ec6a1a8488003a79904258c1000576c10a0302640bd3c7455151c40015bd0b196c6880033de197194010005f3c0ae8994421faee821516388401d3e84206c6880033b5cd624865002cdf438a43222000ecc7558d62040014fb0b3a6c488002ebe11754ca2100677b9484b0c6000aef815d36244001cdea9a8ac408002b7a0b51d8d100074eaa2c6a082000a7c8559160484019eca5bb220080023f60a70d8554004dec26eb1002000e3d54151608c401cbea92a2c608002b7a0352d8d100056ec1885b1c2000e6f53d4b624400b97ce9b26c488002af61052d853000757c3ec9b122062d9c745d1328c0011fd01b8aca990033ba1772586300047e402e7b0aa804aee82d9762440035dd04280c0908027e20174486100053e43aa8b0ca000ade821d363440019d8e9b1264880023fa1c4258630004fc43aa31042000e3d54150604c4095dd052a6c48802a3f21d6458b100056e412cab182000cf5811d9328403fd9cc499263280038fd9672d913000767b1ec4a922000e6f82595628c401d5d08b14800804b3b9cb62901300067aaa0e2b1a4000aee841d562040095dd05a1ec4880033760c76506300957741682b1c4000ecd831d16204001dcacab0c43100033bdd5624c8100055ec34e4b202000ade829096304001d9b073a6c488002bb60840588100053ec2ce9b126000add8190963040015bd01a16c6880073b9c962940100047ec08e0b2a8600af581d0b614c0019bee8b1aa608003b355163988100065eba0c9b142000eac75d93624403fd9cc499263200023fe1d64181320074e320a5b1a2002cbf7655141c40019b8e8b1aa6080033761c52d8d100055ec24eab1c400fdcf7254d604c801d9ca931cc408003b5219324c510004fac08e0a142000eae54d8a40440013bd01b8a86990038fd5254d8e210071faa4a8b1a4279ee8425891004001e9aa6a926488003ab61162504100076a992c298ca000aed819d762440019f6eca12200800337dd7635491003cde43aa8a142000de9851c13248001d5ac4a1282080073b9c96290010006f9406e2994200a8fe861c151484013f100baa828801ebba0b51d8a100066e292e630a4000aed87d0762440015bb0da94c6080039b14975588100066e43ec6a922000abd8414963840019b8e8b1a64080033ba1172d8c100071faa4a93044200cdd75d8e4044001cdea92a6c4880033bdd1624c810005eac0885b1a2000b5d8310a658c4015f100a98c090803375d5638801001e9f3aaa92002000ead54d8941440015790eaa2c320002af61065181320072e296c6a922000ed74258f10040015df08a9ec488002b7a126558c10004dec38a5b222000ece63d4962040011fb0db8aa910002afa106558121007373aea8b102000cef72549618c001cdeeb3aac4080034f5d475d91100072eb2ca4b18
  | 33 => 0xb7e164258c100072e282c6a902000cee829c361550019bee5b1aa4880039bdd675d89100063fb2ae5b226000e9e8414b63440019dea9b92c68800397d9654d8d1000576c28e9b122000cee745893204001cdca53aac408003b39d263988100073632aa4b026400cbf42dcd61900015bb063aac5188039b55050588100073632ec4a122000e9e6455163040019bf06bb263281f73ddd971880100063e32ceca922000ade85d0563040011fd0dba26488003abd0b41d89100067d404ec9942000ced74d8a2044001d5ee8aa6c48821b3dd8b714ca100053ec10c832a6004aef87193624400137f08baa6588002b760f4258c100047fc12e6302a200e9f5455163040014fb0a3a2c408003b59516344010006763aec49922000cee8758941040015db08282c408003baa15628401000d7641686b102000cdf7658d5204087e68a8aa62108003379d5639001051eebb9ee2b1a4200fe3825c62084001d390b322c6080023fa1c545891000d76412a8b102000ece524c8604c4019dcebb126488002cfa14725901000676b1ee4a0c40008fe86dc5528c0015eb02280c09080397d4f5258c100055fc22cab1a4200abf84597614c801d3f04326c688002b76165458c100072eb2ea4b1820009df87551328c0019b8ebb1a42880029fa18421951000756c16c9b122000aed82dd76284001d3ec8296c688003b3d5063189102ad6e43287b026400aed8795162040019baebb1a64880035e548705461002577404e9b122000cf4651c5604c8014fd0a322c099002b7a0b4358c1000774aa2c48802000aed85dcd62040014fd0bba6c5080033b9d954189100056ec18a8b1462008fd87153624c4013bf0eaa46318002afa1065d85320056ec3e84b182000ecd7558d62040019dac7b92a310002b7a142058c100071f2a6eab0c8000ead8799162040015eb0332cc299002bbe0d74d891002577412a9b122000a7e851d1628c4014fd0a214c3180033a9db6288110004f6c16eb2022000ecc6294b63440035d90eb2ac4080029fe156458d210071ec10ca3222000e3d5415161880011fd0e2a2c518002af6105258f100053f428e83026400ced845c8604c4019dcebb1480880023f21975509100073743ccab102000bda809086344001cdb0832ec488002afa1052986300057742e83b122000eae64589420400157d08296c6880025fe157650b100056ec34853182000e3d54153614c8017d305bac4108003b39ca5258c10005aec1884b282000e9c8519363440015db05a0ac518802f6a025218d1000756216e9b122000adc8755363440014fd0a216c688002b761f5258c100053ec34853282000e3d75d9764440017d100ba264900033b61d62508100074f2a2c72002000ade849c963040019df0fb1480880d77c5c7609812103d77410c9b142000aed851c162040
  | 34 => 0x436a5b1a2000af781596614c8015df04baac5880033b21572d8c100063e3b6caaa22000eaf6415362440011fb0e2a6c788003a7d0d635081049d7dc32c03026400c7c855d932940019b90fb1a84880023fa1f625453002576412a8b044200e6d8719762440015d90caa443100039719742d8d100053ec2885b1a2000af5819926188001f1a86a12658802a3fa1f5158b100066f3a2c6a982000e6c50d895244001cdaa82a2c408012fa20174d8910004fac08e0aa462009f8805d521840019dae4b1463200026f6047055142007572a287b122000ed56354b10040015bf08b92c6081f77c20171882100066eb2ee6b024200aef8250d62040095dd05a9ec488003abe096458a310066e3a2c69082000ecf5258d52040019d904b88c0aa0023fa1c65586200056e412e8b182000f8d4350b614c8011f900b8ec899003bc58941440100072f3aaa8b182000e9d8519363440014fb0bba6c710003a75905458c1000736ba8ebb122000e9f42d0563040015bd0b90ac608003b318f42d8910007663a2c6b102006c7d87d9762440014fb0a3a2c588003abd5154d891000577c2ae7b122000bcd831d16204001d98c5a96c6880026fe117654b1002775386c51022000af7815d563484019dae8b9ac4080039be11655881000766292c6b102000cf752dd910040455dd04286c690803b5e05634c620005eac088431a2000aed83d0b62440019bae8b1c4008012bb20b41d89103556ec18ebb0a6400aef855d16204001d9c64b1aa408002b7e096558c100055f426cbb0c4000dd721dcd60484015dd083aec4880033be1f62941100047ec18ecaa24203c7f8759562040019b8eab1a64080039be1762941100047f43e82b1c4000ade8408163040019baa5b9ac488003c75505498c1014df9406c2b0c4000e2f5495162040019df0fb1282880023fa1f41181320056fc32a8b182000cde755d563040a56d90aba242900033b5d9424c81002577416a2b0c4000ed973d82604c801cdacba12c4080039755363941100069e2a0ecaa22000cea861c132480d1ad8cbb92a2908023f60876551300047f404ec992a200adf845d563040035db023a2c408002b7e185458c100047ec3c84b1e2004aed8710362440015db0ba1ac4080029f21564181210055ec24cab1c4000af987d82604c801d9ee6b9ec488002b760c54d8d100056f40084b182000aed859c162040015db07aa6c4881aabba0b51d853224f793b2631022000ade8295163040015bd0c2a0c688003379d5634c810005a7c0aa6a926400cdf42dcd6088401d3ce92a2c60801e7b2097550610006763a6c490a2000af5819d563484011fb023b2a918002bbe1743d89100057bc0aa9b0a4000eea8458a10040013ef02baa85080033799573186200047f43ca5b1c2000eaf43d8942440015bb0caa2c608002
  | 35 => 0xdd954884015bd0ba1ac60804abba0b64d893000775aa2c48802000e3f5495363040455dd042a6c710803bae156244010004f6c16e2a9a42008ff815cc605082b79d05b2a65180037aa10704c92003cfcc3ecb1042000e5f54d8e5044001cdccbba2c40800f1f21d6559010004eec38853182000a7c8559363484b15dd04280c0990029fa1464185320066fba2c6a902000c7f655cb64440014fb0b324c310002bb60b41d8a10004bfc2ae89922004fe26058621880155dd0532ac5880038fd0b65d911000677ba2c490820089be849d952840015b90f216c688002afe11659813200677b94a4b1a2000add8715163040015df0aba6c4880038fd5254d89300047f438853046200aed821d363880097d100baec4880027de1d6118620426dda10e0a0c20008fd819c3644c8011fd0eb1aa3100023f61e64181210053f42884b1a2000e6d6558952040015bb06280c099003b390a3258c100071eb90ca3222000aed8214163880019b884b98c290002afa105258d10007572a0a9b12201faee8210163484019b8c8b98c310003b31d563988100057ac08a1b1a4200add82d07634400157908b2ac69082eaf21165593100057643ea9b122000af5811d3628400197ee93a2c7100039bd4d625481000757b12852022000cee76d506244001d9cc531a840815677a187050d320057743ea3b122000cf452dc56348001d5f09b12828800337dcd32586500067baa0e2b1a40008fd8715363880011fb0eb1a4328002bb60a70d85540055ec20a5b1c200aaee8215362c40035d90eb22c4081bb67d0b735053100767216c7b122000abe841d763484019dce8b124208003ab19054d89100074f2a2c6a182000eae8759162040015bd05a9ac608002eb61365886200066f216e6b122000abe84196604c8015bf0ab22c608007aba1342588100363f43ecbb122000eaf745916204001d98c5290c6880023fa1f41d8e200047ec38a9b162000add83d516304001c7aa82a6c710002bb60c74d891002e9e3a2a8a922000cbf425cc6050401cbec6a92a288002bb60875d8e200056e42642b182000a7f8655152c40019df04bb243280023f60776551320061e2a6ecaa46200c7f759d563880013bb06382a9180033bdd36254910004f6c10e0a9a4200ced741d162040011fd0e32ac299002bba1743d89100065eba0e8b1620a2ed463dc563484015b908b92c608002bb60850d8d2100736c2ac4a882000ed7814c8604c4014fb0a214c318003979945458c100053e42ac930a6400dd9739c3628c0011fb0dbaa65880023f61e429863000767aa2c73102000ced72d8a504c001d98c7b12a488003ab9d14358810004ee43aa89946000d3d75d5364440013df04baa83880029fa1474181210047ec3cc83026401aec82d4d62040013f501b8a8488003b608163880100056f
  | 36 => 0xac4080023fe197550c102ae6fc3a6430262008fe861c15448401dca84b08c299002b7e0d54d8d2000737b2ce9b1220008fe87d89414c0c573908baa65180033754b735822100d77412a6b102000ecc62d486344001cdaeaaa2c4080033b15172d8c1000767314a4b182000e3f8459564040015db0faa6c4880038f5505458b1000576c0ce8b102000adc85d056304001c7cc932a840820b6d95171902100047ec30e0aa26204ee581d89214401737d09bac41880038f55054d89100066ec3ac6a902000ade851cb63440015db05baec498003b558d42440100063fa90eca8a6000d75525c6508402bb9ee6a12c099002bbe1f43d89100072e3aaa9b1a2000cde725c96304001d3e85b1c8088002bb60a7458810006763a2c51002000e5d54d8d52440015db09b2ec488002bbe0954d89310075d3b0c91022000cde7558d43040019beebb1c8088003a7d9042d8d100066fa12e7b102000ced821d951880015bb08316c68801f5b9c952942100056f428a8b182015aee82d47638800157b0c292c8080038fd0965590100074f2a0a8b182000cdc75d8e20440015bb0a102c6080034fdd75459010006f3c3ac310c4000a7f855d162c40019ececb0c6310002ed60675d911000576c10a9b122007be88254620840015db07b128488002b72097558c100075632284b026400aed82d536244055f64a92022008002e761052d8d10004eec3a652046000ecf7498d62040015dd0c2a6c488002bb61440d891000576c2ee8b102000aed829d56204001d5aa9a12c4080033be1f62509100669e3aaa8a0e20008fe87191604c801d3cc9aa2c608002bb21741d89100066ebb2a69902000cf587d86614c8015bf0e2a2c608002bba1c40d891000767a16c6a122000e6f5414162040151fd0fa0ac5880029f21564585320066eb9a863024200c7d751d5628c401d5f0bb26c4880039b19552185320057ac0ea430a60a2ee582dc563484011fd003b2a8990023fa1c54d8d100047fc32e910020a3cdf73dc56348401d590bb26c48800397d9763509100074fc12c8b182000a7e8510b63c4001f62a8a0a2008002b760f75d8d2100677c3ac52002000aee8550f62440015dd0fa0ec488002bba1d43588100055f424ebb1c4000e9d6350a4004001cdea5a8ac4080031f19470595210072e416cbb1a2000cee7558a2004001cbaa9b1aa6880029fe195454410007363aea3b122000e9c6410b63440015eb022a0c2990073be1d62504100055f420a5b1e2000afa801d060484015d90fa0ec48800337dd5635881000577c3ca8b102000cdf63dc552440017d704aa240880023fa1e5258d100057d400853046200ed64258f100403f9d8e4b1aa2908023f20172d855300766baec7b122000ed5811416304001d3e87a16c688002afa13655862042ef8c08e0a8c20008fe80
  | 37 => 0x100071eaa0a9b102000ade82d4563040019dceca126488003a7a166458c1000677c2ee4b1a200097d85dd220040015f100a90c098802b76167458c100066fbaac6a902000e9f421016304001d9884b1ac4080034f1527655110006f2a96e2b026400cbd741d363880013d90eaa242900234f9d154942100056ec08a9b1a2006d3c755514244001d5a87b1284880038f55054181210957741081b126000cef825c460508259d8e5b12a2980033b58870548100067b328e2b026400a7e859d16188009ad8e4a92a288003375d563900103cf75292c48802000cdf835d932c4105be100b8c8108003a75905258c100069eba8eab202000eac5219362440014fd0a320c0908033de19718801000766b1aa4996207fcfa76dc62044001cb8a4b1aa4080067721d534c8100053fc2ac83026400bd5819c1324c4014f90ab20c099003d354d52181320066ec1ce1b0a8600abe8694864440453bf06b88c099002b7a0b64d8d1000577400ebb122000afa80dd4604c801cb8cbb1aa488003a7d0a4258c100057642e84b102000e6e851d162040015db09a8ac40800337d8d72901100074fb22a9b1a2000ced72d8a40840015eb03b28c310002d760c42195300053ec2884b1a2000add8315363c40015db05a0ac3100033bdcb5258d100047fc0aec9948000aee801d3624402b79d05b226518002b7a1c42d8d10004fcc10e0a0c2000ade80d5363440a3e58a8aa242900133bdd7625491000576c0eebb122000ade86d4863440011fb0fa8ec7100023f61c54588100047f436e2a9260008fe8714163484015db05a0ec2990023fa1f645853200576c2ce8b1020a2de572d86614c8015eb023a0c099002b7a1072d8d100057ac08a4b0c60a7e6c75d893254401cbd0a216c6880172f9d161942400067ac36e29902000e3f54953624c4019beebb1a42880033dc8571181320047f406e2b2a8400e3f54dd161940013eb0238264a8803abd0840d8910004fac08e0a942000ced72148604c401c7ee8aa0c0a88033bd8b714c94101d9e42ac8aa02000add8315363484095dd05a8ec48802f2fdd942504100074f422c6a102000eaf8519362440016df0aba264900039bd5054588100067742ae5b182000add82d5163040072fd0bba44008293f1948714c9310047f43a64b0ca000d79541c15144001cbcebaa2c6080023fa1c545881000676baec520220009f581dd220840019baa8b98c2900023fa1b7150e200056ec2880b182000adf861496304001878a83b2a8880023fa1f41d8930004fac08e0a126200add821516304001d9c8431ec488003ab55341588100074e322a9b1a200c8ff875446050401d5b05322c4080033d9487158d200066f3aec6a122000add8614a63040019bf0fb1aa4880039bdd553d89100075d3b6c91022000b9d8314a648c401cdc84b2
  | 38 => 0x8fd821d95444001a78a83b2a8990038f5ca65992310056fc2ae4b182000afa80149608c401878a83b2a8990027b60b7155132004bec3885b2a2000e5d5458e5004001d5ae8326c488003b395263588100055f420cb30a64008fe871536148001d58c8a10c2990033d59471581320072e3aea9b1a2000ee85458a10040013bb0e994a11815edba1764886200057d404c8b026400e3d6559152040011fb0fa88c0908029fa1464d853200756b24a8b10204af345455131c400197ee93a2c6908039b99654588100056e42ac8b182000e3f5495163840019beebb1c408807e7721d644c9310066eb9ac73024200e5f54d8d5344001d5eea326c488003ab21c64d89100055f434a5b222001aec8295162040019bee6a1ac310003b394b634c9100066e396c72822000e3f7555060504015bf06ba2c690803b35d463d891000576c10a8b1c4200dd6541c5324c4011fd01b8ac89908b3b1c962506310056f416e9b1a20008fd87150604c4255dd04282c710003378c8764c91002767b9ec49922000aee87153624401137908baa65080033dd487158d200047f43ca4b0c6000ade858c963040014fd0a212c608002b56044058c10006f4ba0e09924000eae741d362440059790eb22c40817f37d8b73486300074eb1a86a102000add8295363440013eb02382a690802afa105258c100247ec38c9b122000eac8799162040015f50132ac090802bb61c50588100056f43ea5b1a2015aec82551628c0155dd05a8ac588002b7a1462d8d10004fac08e09928200eaf75d9362440019dee93a6c4880033b5d7624c9100047e432eaa1c2000af581190614c8e1b38e8ba2649882e3fe1d61902200074e410c9b1a2000e3d541516388401cdaa9b14a088002bea0065d8132006eb190e2b026455adc8654f604c8015bd0b322c6080032fd0876505300071fb2ec8a922000ade80d4963040019f685bb220080023f61d628c6500066ab1ae32002000aed8215162840015b90caa46098003b5e0d614c64000756c3ec9b122000abe8419460484011fd0f292c7080033790b73582210074f324a4b182012aee82193624c001a7eeb3aac8080ebce151548811000d7643cc8b102000e3d541536344001c7aa82a2c5080023f61e52181310056f40684b1820008fd87d046048401c7aa82a4c3180033bdc942582310057d400ebb142000e5e651496304009bd4e1b92c3100033b5c8421813100766ba6c63122000adf86d51630400173b08290c688003abd096250410006e6b92652846000eac85193624400157908b2ec090802afa1365d8e20007c6a1a853026400e6f6595362440014ff0ab22c0990038f61f65d91300055fc22eab162005bba809cb64440014fb0a216c788002b760e7558e2000e76392c52002000f4d5354a614c8019e8c9b8ac099002e760c5299
  | 39 => 0x11fd0e2a2c588002b7a1772d8d100fd7741682b1a4200beb825062084001a78a8b80c2aa0123f61f629411000736b2ce8b102000add831516388001d9ec6a926508003379d9534c91000577430ebb122000aee809d56204001a7ee93a6ca880033b58f72505210057ac08a9b0a6403c7e651c15188001d9ca4296c6880027b60870546200074f326a4b1820009bf845d521840019dae4b0c8110002b760c5458c10007673aac73102000e5f85d8d52440012fd0e216ca880039761442d8d10005bd4048432a2000cf442dc563480015df08b2ac408002bea03711813200576c16a2b146200cde74d8f624400197ae83a0c0990039b1d450d891000766ba0c63122000c3c541d9544c001d98ebb18c488002af61365d8620007563a4a9b122000aed82d076388001a78a9388c0aa003ec50a404401004e3f3aecbb242000e6f521416204001cdd0eb2ac408127f1949324c7100071eaa0a9b1a4200b6e851d162040033b90ea1a64080023fa1b715093000737c3acab102000add86d0963040015bf0f2a2c6080039b9d465d89100047ec18ecaa42000e9c64d5363440015f30fb04c09080397d4b6394110007373aea6b102000a7e8519363484013df04bb2a9880023f6187050a3100766394a5b1a2000adc8614b6344001b6a84b8c810800337dc96354810005b6c2ec910c4000ced724c86054401c7b0532cc808002bbe0954185200066f396c6a8a20009df87551324c4015bb0daa2c6080033754973d881000756ba6c9b122000aef835516204001a7aa8b8ca1200027be0971181540067bb88e0b1a4200a7d8610a65040015eb023a8c0990033b5517218131004efc3aa918a6200ee5819c16204001dd6a4b122008002bee1d60181320074f420a4b1820008fe8790a608c401d5d0fb26c488002bb60a74d8d21006763aec490a2000cee8758a5004001d98ebb1ec4880023fe197550f1000576c0ea8b102000adc840836344009fc500b0c4310003371d563484103e5f9c0ac0302420b9f48754541c4001cdeeabaac408002afa185219130007a6a9aa4b0a6407dac7250941841555bb07386c29900337d5173185200075732684b102000e6d75d5162040015bd0e296c688002bd6045458620004bfc2ae890c2000aed831536244001cbea9b1aa488003375d5634c81000756296c9b122000cbc845d932900015bb0c214c608002b7a1352d8d100066e3b6c6a922000de575dc532884035dd05a88c090802bbe1f54588100547f43ccab1620acbd783584614c80153b08296c688003b554d6118532007673aec63122000e9f42d8d4344001c7ea92a6c298002bea0064d8132007573a0e8b102070f8e64509324c4015dd0bb9ac40801b1fa1f65d911000767316a4b182000ece4258d32c40011fd01bb2a890802bd6044058a3100766aa2c6b102
  | 40 => 0x7e0b64d8d100071faa4a9b1c2003c7c7559562040011ff04b88c0aa002b760e521813100774c2ac50802000e5d6354951040013eb0238284080039794b63549100056fc3884b182000e6f755d76244099de4ed18c4088003b56042058c1000736aa2c4a882000ecc7498e6204001baeea38a64988038f9c865191300055f430ebb222000cbd741d1628c401cdea9b14a0880025f61c425941000576c30a93102000abc84597604c94bbaae7b0cc29901e7ba0b759021000676b1ee4a8a4200ed5635c650040019eccbb8ac0990033d5537158d2011577416a3b1a4200e3d7299664040015bf0f292c608003b554f61985320055ec24cb30c4000c7d751d762840011ff02bb26528003ab55040588100066f3b4a831a2000add8694963040019b8e5b1aa688002bb6084058a3100767418e8b1020008ff815c8605502bb98e4992a3180023f61c5258c1000767216c69942000cde425cf62040016df0ab2442908033b1d162548100076ca9ec13026400bb5811486444001baee838a64988023fe05731815205e9e3a2a8a9e2000cef759d762440011f900b9ec2a1002bb21e54d891011677312e518c8000e5e75d49630400157d08328c0990038f5505458d100047ec1eecaa44200aed82d07624400197f08b88c0a1003371cb6350d100053ec2ce8b1c4000abe84d9461880011fd0db8aa890002bba1f545881000676b16e29948079cf5719c362840018f8cbb8aca990223f61f65d92100072e32c85b1a2000adc855d163040015dd002a2c408003ba2156284010357e3b9ee29944200ecd75d8c62440018feeb3aac5188029f6144258c100056f42ec9b1a2006d3c7555143440015db08382c40815677a187054d320074e216c6a122000cdf741d36344001c7ecb216c88800b2f990705065000757ba2e8b10209faf78158c6048401cd8cba16c488002afe1954900100061e2a6ecaa44000fc9421c1328c0015bb0a316c68800277a037154d32007e4a18e0992403be7a86196204400157d083aec2990023f61c5458e200074f2a6c6a0a2000add87949630400159b063aac4080033d1977158132034be42ae890a2000e9f64d5363440015bb0b90ec688003976126558c100063e328e0b2a6400ade82d5363440015bb0d2a2c6080038f596425901000757a1e85b122000cd5635c65004017978e8b22c588002bba1742588100047ec3e83b1c4000cdf731c16348401d5f08b128408002afe195450b105566eb9ec33026400bae849d762440014fb0a324c299002bbe0d62548100647fc3ac32848000e6f6254951440015d908baec488003b614363941100066f3a6c6a922000abe84197634840179b073a6c48801efa209544821052fe3296e29926200aed85dd362440015bb07a8ec2992075ed5070545100056e43e85b1a2000ced7214b630400
  | 41 => 0x1022007400000c0110014000006000006801c00b08a00440b0000006815800802b00000ac01203f031016c00205606b813c064041002833000a0000000000128048001834c0000033d8000404c08d09303e00620141c9814803c00005700b800001001100048fe06903c8020006000049000c01001f000006408a00100c14804d400201600081ca029001001c0480010000030008010007800401e0030cd800005600e01c01d800400000100ec0181c1015001012c00e0008114242012052802c07800e0058d20030499006001c9a408706301540000a801a80540001e9035943002e4273438025f4600800000d003e0001e1801408400212c0000010006000800000400c00c82ac002182000000c00007d076005008000a000000800a4820060010394000001000000001d00283e0010000001802c180006002012c024009001000800004b00f809400600a00180000440370000024000000002805800000e00000f800401a00f008800e0160160024042031024002400401800000a801005b004002402a01e0f1806401c0010278e6400600205d000464e0cf018007c00201e0008ba00c800100200449460760258eaeea1375881100065fba4e9b142000aee8414162040011f900b9ec2a9003b3d516358810004eec18e0aa2620fdcf7250d604c801d9eeab1ac408003ab59162508100072faa2c72802000ece7518c62440015bd0eaa6c68801e3f21975882100057c402643028200add82d0f634400157f08b28c09901e7e61e408821000d76c0eeab102000cdf7558e40040011fd0fb1aa310003a755363509100047ec38a5b182000cec845cb63040019daea3aec488003aba0a64588100063eb2ee4b2020009df874ca408c001baee7b8ac4988023f60f7650620006f8b8ce1b242000cfb7654910040012fb0e214cb188038f55054d8f10005dac08a5b222000baf845962148401cdecbb128488006bba0a645881000cde43aa8a102000e5d54d4763440019eca9bb22008002fc61640440100053e42ac9b024200ced755894204001cdb0a3a2c4080023f60b765501000576c26a4b1020009dc87551324c4019dc85b9ac4080033758f715481000756210c9b12200497c87551524400fb5ce4a1481080038fa08651911000737c3ecbb122000aed8550d62040255b90ca9ac09907ebba0854d893100766a9ac49902000e9d641096304001cdaa8a9ec4880027d604705493100576c08e9b1220008ff835d9219400157f0ea10c0a08abce15154440100047fc1ae43028200aed85d09620400157d08290c298002bb60b4158b1000677baac4a082000e3d54150604c8019bca4b98c290002ab61075588100669f3aaa92062000e3c82595648c4035eb023a0c0908039b949755881031dae42ae89946000cbf425c460550013bb02382a699003a
  | 42 => 0x820400000001f800002600e005816410a013000805800000200600000ac00004206ac0a40040000248000000000009002a02a03a804403022c00080040480fa00000003400060070004004001026009c002001007817c00e0821a580640160060340020006086001812001e003002002c1f031a00a000007400003380743c808a00301b802a07302900f800226c01800ec00000700000040d0003000000000200300080d002e00a00000e462200000186b027e00e000007000a001008000000400400280a83a6000014026001e00c0b404282aa010011000000c0e0000000050e00301f800801802e003000c0ee03f005000001004500300040000180050000002004000001400401b0818074002000001056c0d200c08f093044400f008800c0ec00b000002800000005400000020b5006801404219d00a000400004500607482c4005000803001200805793b814600101200cc048001013839002a007005001024801a018002400000800200ac028002007817c05cd100311c2c5f6000002001000e00100f80000485a302383a800800912c81d8042268000827c004028005800005202f093806c0120050030000006001009800c4f004700082bc000000000804001a076002007c108003002828c01e105000000806a01c013000000003a0248224020003009804404600200492d000015b0148cfc03200f01f025406c008000800001a01e00b06ec04a0480000000194005010802402000000c804802201700582b00000000390224050064003000c00402600000b80080000028004038006031804c0000cd017001804603b0aa805001600700f000800600625800141d20040028000038002060800068600100500080542db0008200000062004035800400000011f01280580000020020429022000013800002d800000208a07d001c7ac00a000001004a006001001c000007016802801e00006c0444ec60790060014022135262802c00006000000000b006704801c00301cf001000800200000000040080e9005001033e00000000680000e3321840c03a02f034803409000300280101c800f00001cc01a003004808000c01d0178cd8006017000003800200002e00501ac032002800009c003015802c00001e01c801c014008037802423209b00000000300080000050008002001000004a01624600700d600a0070010000012514052c0000090028000006012006004c05800200c800000819c0250a1405e02d01581ac00000100380000460000018c6400000001c0e98002000084030001600b0150008000328012802409615c00000a40a600225380280da000000001400803f8f080046d004d003000401e00001b82d07c6034000000402001600f800023614c03280700021e4000001c040008005001401005f0000040004010068805c002
  | 43 => 0x4019006800c04800a001801800a018005000c0400040bd00240100010040000004001002008002601100313c808e00005d000c0840080548e540580d3001006400c017006800007e00f00000000000cd000800004801a08500c004c07e05c8008038001071800800402a0af040400201a00000bc08a00004601c0022035004006070002400d803004a424034800477e006000824828e00e00084840020161f386cc09200501e824400001c0000028028006009002404206302c800800400200100e400402a00282fc6e41bc00004d42ee003006929c00200100b041c07e010001822cff4096014808801801401100080160170010000000012016801c000000000842c00400100088d0000001031085801601500480840480ac029001001600c03c800401c199008800c00007203b017c8e4005000001400000400c02e40007940220138004026002000003c00400001c4a5c01100780400600960eb000003600400100d80144a300e800c06a000004004405a00c0100130012023027009800c055003801000409900400000380060000028008021000000003000100d803401c000015006002601000101f00020030000094000061000003006002d000851445c3c604d004401e00c001001c000000000816c048028004805c00003f0008178008023006003419e000000007c07e00a000003c0d2000000000400000c000000002a01c0bd806403a0100250020002000004801c046012006805c03600b00880a804000a02a004400a000000000002001700e0068210000000000800001c002800cc78008000000c012044040823817a000000003012a00e02a0000010004020803800204002d00080040000058190018001002801402409e00601c408c00103e024400e017000003800000e014807c00000500280c80d803e003801c06001a00700681aa0a70148000dd8006000005c03a00400008dc0063490bc800004a00e0588004000171005000006001e0bd800000217f00181a802600000c81800140a5000825c00800100a0004904000000000000201d00183c4fce00900182a0028019004001835201e001000800c000001800000c01101500010a200000800b800000200396e003a0000634350c2e040005009017604801f810400e00c00b808c00a013034801c1d4001000001c02614d00493e402616d01480180020c005c07e800002300600000060031450000d44001000807404401b003000c002004002003814e006052001804c0c7000002c02c0030d1024843000303f800436a05000e80180c00000028000000000147a1540020020018664000009000017c00400e00f004800c005003801400001a031000000800500281ec118134000008009806c003800801601100a006c0000070008010086006001000400200501680342ae00813b
  | 44 => 0x1e017800401201c00f806400800300001e401244e0018038044003001001400001802e800000000000b003c00601000100fc00000101081d40d200007100540160bc033009400000300400080100080248af000205f000000c00e1be002004c00a001000000800c01600f8ffc01a0070180000064001017801000a005012001403c0030118174000006000004802607c01300000000000ad00f40000000ae8000002013002000000000002f00140380050a602fc008002004004c0000010050154006004024852c00000800600080780c3000000000201400401b087c03100c0014044006005804000210a02d0e3402400002680000aa07800000001de55c00c820001e007006816c13820900700ec00400100481240200b00048018014021040889807a370000001800e211000802804c00800700ac37600b002004805203b0000aac128001001800000000000080b400e00006e000801000d174817c00000500a012c01212a010000000e08a00382ec0740091d3000012805c002000000201400000c000c00d029000800a0010048008590019002801000008200000140d4021003007c000007004800000000100c894c0ca003044002c000000002008800201902289dc000006000806c19e00c000001c000004001801405401104e0000002467010803804c06f002800000e08d0058000028079026000803c00500000cc02e2bd002001400600100100380d201c01d810c01404e000002c198002008002000208c00a015800203f007837801200609680640000c701d00000007dc020007002c06c02d801000002d016004800003102280000600030688000012001000011c0940000018008050032007803431c002000800035601c0000088008001000800c02601500980bc048000000006400000600300081980f5013801c00
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x183d875505458f10004a7e61641496304001a2d5460454d8910005b2a437518c624404568c9650d429853200517a567458e200400125e95a0b74d8d100058b65484589420400146e951d1624c81000533a4854dcd608840103e9815376550100056a650851c132480012cd981d26358810005396447558a400400126d95a1373d891000517a5472d8d4344001e6162549514401000437a5f8510b634400189e87d9042d8d100049be63659d36244001a2d98d5254d89100048fe615415363440018d983a02764ca100058ba544259162040014cf925d56350410005a364c74991620400162c9655054189100068b55182153624c40161e949d75458c1000687619541526304001a4d8560c745881000527652655cc618800162e9510a6458810004ab66075991620400113d98153765522000527a507558d3204001a8e841885218d1000593a544298d62040014d59314b7158d200049ba5684dc7624400168e949d463d8910006876166410963040016d290d496344010004b964485d0b6244001a1e8595343d8d10004a76538614963040179348755151507100068721554d0b63440016a59119142185320060fa1d541536344001a1e859534158c1000517654425cf6204001ae38558941440100068be16855916204001d854350b7158132004c7e61541526304001e515458e50440100058ba5487991620400189e8719052d8d100058764c82595648c4012da9021c52d8d10007835505458d6204001a2e756107558810004a765a84149630400168d93e1c64d8910005a364c425d1620400126e95a12705881000687a165415163040014ce9215173185200058b25b54953624400126f985d752d8910005b4a404258d100400346c97589525441000517a547458d21040015359115171181540048fe6154151608840145d959d363881100050f64454dd9540400149d94dd5638801000687e1b54951630400143d9421576486500049ba54845cd620400183e8755054d8a10005a364e82d936244001a1f875505458c10004b56604258f1004001a2c8455153d89100068be128459562040014d5911c963940100060fdd5849d7624c001ca4645087158132006a3a11839d76244001ae38458951440102ad932595354b604c80162e959d364d89100048fe6154153604c401c4e7654d524c9100062b61372149618c0011ea90e1d544c9200050f658545d95404001a1f84a1365d8d100058b6506554b604c8014e5911d56288010004ab66275193624400125e9521842d8d100058b25954153624400168d9414b63d8910007071d554d8d42440018cf7460e74d89100052d65065dc5604c80123f985947259231006875518315163480012ad94a1773d8910005b2a4074d8c62440012cd9810a6358810006335d5831d56204001c1c745516354410
  | 1 => 0x5b46445058e500400162d9519054d89100048f663659cb6444001a8d7460c745881000693a166210a6304001a1e8519042d8d1000785d525458f1004001a2f86d525458810005872595415363440012ce922144058c100070b1d154589510400145d95d9173186200048fe61541536348001a4e8560c74588100050764c541d9544c001c8d42109731852000587e5b54951630400125e952123258c10005b86445458910040018e652e1d61185320042fe61741d0604c801e0d5415163988100060fa1d5415163880010dc966047054d320051ba5674d8a2044001a4d7560c7558810004a76604258d4204001c1e765505418d100053c64454dd9100400125e95a1372d8d10007139c96354a5004001a1c855534158c100064b1508755121480012d591a025458c100056ae51751c1324800131f985505418d100053aa4275d892144001a1f85a166458c10004376627258e4004001c2c74553625451000595644841976344001a2e8595341d89100058ba5442193624400123f98550545823100687d958314b644400162e9510b64d89100053324975d8d414400162d9510964588100053c241651c5604c801ae29060450588100060f61d5415363c40010bf985d07458b100053364f8758a4004001a2d98d5254588100069555181141630400162f96550545881000794d496394110040018d9831c04058d210062b61172148604c401a4c6560e74d89100068d55181152618c00146e951d362485100043b64a80dc56550c018cd879884298c100070d55054dc5634800185d87a144258c100070b9db54950624400126f9661474588100058b6508259562040016a59121464d89100052b65375d8a204400162d949d465d8910004b32617354d620400164d9310b65d89100068b2115454d620400143e9615171181540040f660541d9544840164e951d2639881000693e1782d8d524400143d941947059521004b364c85d0762440014759510b76440100068b55181151620400168d932096458a310050f650651c1654c8018ae64e0971902200044fa60545c460550012cd981d16358810006995d5811416204001c8c7650d424c9100068b61485591620400145e95d9173186200050f65e82d97644400183e8755054d85200062b61372149634400129e94e185258c100050f654845d921900014f29014b7644010006a9d098110162040010ef9260470595430068b61485193624400129d9421852d8d100049b6604219762440010bf985d074d8a1000587251655516304001a1d842126558c10004ab66075591620400183d8755054d8e210048fa5a859cb644400162d9510864d89100061b997825c6508800129e942144258c10004a7a5285dcb634400149d941d7634c9100053364b7558e4004001e925458e40440100058be51659516204
  | 2 => 0x40014ae941d7624c9100043765f851096304001a1c855534358c10005356467558d3204001c1c745536354d1000cab66254d09620404564c9654d5298532005936544298d620400161d96d525458c10005356447458e20040018cd871884218d10005a564485193634400123f9855054d8e1000617a1f6510b63440011e992a03715511000783d525458d620400183d85dd2745862000437a5a80dc5534c801a8d84a0c7558810004e36448050d424c801a2e8595054588100959325953549604c8012cd93e1f41d89100058be595415262040010dd9810973d88100048f66042d976444001c1c755536350d100060f61d54150604c40123f9855054d8e21005a364e74193624400152d921507655132005b2a4374d8c6244001a8e84a0c75588100043be61741d162040012cd932174158810007a895162505100400162d9419454d89100061b215724c8605440146e952117218131006b1219424c9314400162d9419552581320058b2557455162040014b5941487158d200059564482197634400162d9510b64d8910004b36627518f62440016969414963c40100063360f7214963440014ae94e1f6254510005b4a425458d100400162d9510a6458810006c555181150634400162d95e1c64d8910005172557458d320400126d95a1d43d891000555e55741c5324c4014ae941d5624c8100050fa5c82595648c4012cd9321d54588100068b21554d0f624400183e875505458e100068ba1654d05620400123f985505458d200051ba567458a20040012cd981d163988100058b65464508614c8014ce971496354810024ab66254d0b62440014ad9421572d8c100051e241751d5634840129d94a1772d8d10005b16445418c6244001a1d8421365d8d10006961968014b63440018cd879084258c10006a36106214b634400103e981537655231004ab65a841d56204001a2c8555341d8910005a56505258d100400161e959925458c100058b6506554a614c80129e9421420d8d100072350842dcd608840146e951d162484100044fa6054dd9548c40168f9361f64d8910005aaa438719362440014e8906117218131007a45516390110040014ad94dd562880100060f617749d362440010de981cb635451000627a1f6414b634400162d9414a7558810005272517558d320400162c9459554588100051da5464dc5604c80161d93a0b65d91100053364e859d86244001ac486549324c51000587a5774553634400156995210704c9200064ddd1819d36544001a5b65a0252d8d100068b61084197624400189e8761052d8d100043ba5c85d0762440014e8905d762485100070755054dcd624400123f9855054d8f1000517a5c5258d520402568c9650d425813200627a1c6410b63440d334e96e0553549320063360f72149618c0014ae94a177258d1
  | 3 => 0x320063a5c8804c860504f36e19121562440100043be61751d5620400168e941d66358810005272518758d5204001e535458e504401000593a5474d8c6244001a1d8521464d8d100053aa4274d89214400143e9615171d81540048fe615415261880016e19114162940100060f61d54150604840143d9615076551320048f661651c964040014f19114b76440100052d650651c5604c80183d8755054d8d210042fe61741d1618800183f7561275d891000695d4981141630400126d9521f43588100048fe6154153628400183f7561275d8e20004976606510b63440016c99321162840100044fa6054dd95404001a1d8519042d8d100061b217825c4605500162d959d342d89100071354852dcd60884010dd972144058c1000527650525cf620400125f989944258c100060fa1d541516244001a1d54a005458c100043b65c85d056204001a8d84a0e75d891000687a19541536344001a2f85a166458810005a36507598d620400125d9521020d8d1000517a5474d8d324400168e9414963588100048fe61651c9640400134d91201535493200497e636510b634400162e941d754d8910005176567258e400400149c945d5634841000587654825916304001a1d98d5254d8d1000517a54425cc61480094ad97d89429011000497a5682d93634400125d95a1372d8d100059364c425956204001a1d5460c54185320060fa1d5415363480015aa94214704c9200041fe61751d562040010ef985d475d89100043765c851096304001d4475548714c9310072558d425c64004001a1e85d9042d8d100061761d65149630400185e87d9452d8d100068b21554d0d6204001c8c72d8d42505100050fa58549d9544400125f985944258c100058b654425d1620400145d951d163484100069955181141620400168e941d4631891000627a1f4210b634400125d9521232d8d100058be5b549516204001a1e859504058c10007135d57354d62040012ae94a1771d891000687595831c964040010de9720954d8d100050fa4054dd9548800125f9660c72594100058ba546495362440018cd835c842d8c100078355054d8f624400146c955d3624c910004ab65387d4f62440016d1911016390010005a364c421d36244001c2d541537258d100052b25175d893244001a2c85553415881000517a5672d8e40440018cd835c852181310068755183150614c00161c96d5254d8d10005b16447418c624400143d95a12764c9410060f615741d060484018cf7560c75588100079254d52580604c80107f985d475d891000693616831d162040018f1811c04058d210050b648541d9544c80145d951c963504100060f61d54151620400168d9310b74d8910004aba605259162040014ae94a1d62940100068755181153634400143e9615376552200068b61084995620
  | 4 => 0x400168d9321e64588100059364c4299562040014ae9421572d8c100041fa5c85591604c80125f985505458c100068d55181153614c801a57546045058c100049b662651d1620400126f9899474588100059364c75d49620400123f985505418530006a61928010b634400186e855c842d8c100058ba547495362440010bf985d074d8d210058b656741d36244001a355460454986200048fe6154151618800107d972156498532006a3a12621496304001c1c745536354510005396447458a200400183e87d9452d9110005b4a405458d100400191c5421d544c931005176547258d430400164d9314865d891034da325943508614c801e0d541536318910005a364e74d9362440012d59121c42d8d100050fa4054dd954040014cf925d763505100060fdd5849d5638800183d8755054d8c10006876108419763440014e5919d5624c8100068b5528015362440014cd92dd763901100061b21d85589510400143d94a16764c9510050fa58549c0615500129d942096558c1000627a1d8414963040010be9721165581210068721954153634400161d9519054d8d100058b25175551620400183c875d554586400061761e65149630400123f985505418121004b564484081630400164e959d063d89100049b6548710162040014ea96e14704c9200041fe61751d4604840123f9855054d81320044f660549d9544400126d9521d43588100053aa58841c132480014b69414b7158d200051b25574589320400185d876144258c100049ba5487d0d6204001a2f7561275d89100052d65052dd9100400123f9855054d893100699d498114162040010de9721721d8d10006b118981148634400183f87dd55418141005a364c74d096204001ea15458941440100070b550545c8604c40146d951d3624851000707d5254dcd62440010de9721741d8d1000517a5442dcd608840125d95e184258c10006936166210a630400149e941d7634c9100052ba52859d8624400145e959d3638811000693a16831d162041494d5961d4714c9310068761742109630400164d9314a75588100068755183151638400123d96a1472590100058ba5764553624400145d951d1634c810004b56448714b634400168e941d563988100053564c521c56348001e619558951440100060f61d54152618c00161d959905458c100050f654845d93290001c37549537158d200043ba5c8510162040014ce92dd563900100048fe6154151638840168d941d763189100053364c845cb630400145e951d363485100066a1d0805d1324800145e951937358121005a36507558e6204001c1e76d525418d100058ba5664951620400123f9855054d85320052765375d8e20440012ae94a1670588100060f615741d16348401a2e8655054189100052da5065dc5604c801d854350871581
  | 5 => 0x8100041fe61751d562c4001a1d546085458c10007611d1421c5324c401c55635497194010004b3259839d7624400145c955d3634c9100051d25564dc5604c80161e9519254d8d100052725175d8d324400162e94a0b65d8910004b3a6042d8d424400125e9521232d8d100058765954151630400151d9315076551320040fa60541d9544c0012d89061d5458c1000497654825d163040014ae9421572181310061b6157210b6304001e934258e404401000565e51751c5324c401c2f549537258d100050f64854dd9540400125e952102058c100068b21b54953624400149d941c96354c100059364c8759562040012d59121c54d8d100051765442dcd6088401a3554604545862000627a1e8414b63440014769519071581320058b65275d97624400164d939d752d89100052d25165dc5604c80134e90e05535493200517a547258d410400143d9519371591320053364c855c8604c4012ce9221440d8d1000497657871096304001ae29060440588100043ba5c851036244001a2d54a005458810004aba5387d47624400162e95e1c64d891000517a5c52d8d52440010ed9721741d8910006871958414b6344001c2f54953725863000593e4d87d97624400162d9521d64588100050fa40541d9544c8ab34e9620153549320058b6538719762440012cc9660e74d8910005362418758d520400129f966105298c10006876176410b63440018ac84e0971181540052b25175589210400107f985d475181320068b61d5415162040012ac9461d5358810007855505458d10040012ae94e1d53d89100058b65482591620400183c875d154586500058b654745916204001a1e8755054d8d100058b65442dd3624400168d9414a6358810004a7a5282dd763440012ad9814b64d8910004aba5087141620400186e87e1762545100058765065153634400164d959d063d89102c57225d531c1324800126e98109655881000517654425cc61480014da90e1d634c6202c57264c851c13248001c8f7650d424c8100051b654745892104001c4e72d8d52941100051765787d8d424400162d94a0b65d89100042fa5c84595604c80164e9510863d89100060f615741d1620400146d951d3624c910005b86444058a400400183d8755054d88100068721554d0f63440012cd9814963548100050f658541d9544840125d981496354810005a364e82d93624c0012ae94e1f53d89100059364c82595628c401c35541507158d20024b9259819d3624400162e96d5254d89100068ba1654101620400103d9815376552200053664c42dd9100400162d96d5254588100060f617749d3624c0015e191210704c9200068721554d07634400161d9520864d8d100050fa58549c76055001ad18458e50440100058ba5954153624400189e76a105218d1000587a548259163
  | 6 => 0x2040012ae96a1275d8910004b36607598d62040014ce971096350810004cbe615415362440016659119552185320062b991821c14188001a8e8460c755881000437a5c8510b63440012cd981d0631891000687a1654d0763440014d5911d163940100051765472d8d4144001a4e851884218d100041fe61751d5628c401a1f6560e72d9130006a36126214a63040014d59119573186200050fa58549c36155001a675460450588100049be6154151620400143d9315076551210070b55054dc9618c0012ce9814b635491000535e457558d42040012ad94a1d53d89100060f61d5415061480010bf985d07458a310058ba5482591620400162e94dd554d89100053a24174589320400141d9315076551320068be1685193624400129d989905258c10004b5644805516304001c1d5415173d88100064b1538755220480016a99421562840100070bd52545c8604c401c1c745536354910005aaa508558a100400162d951d26458810005936547498d620400126e9521d435881000555a54741c5324c40b83d8755161942400050f652851d95188001a3b65a0252d91100068b55182151620400107e9721564581210052b25175589320400123f98550545863000cb96448710162040012cd9321440d8910004a72598414863440018ac84dc9325864000539648541c56348001a4e7560c755881000497a548710b634400149e9414b73589100058b65065548614c8012d59810963440100050fa40541d9544400b9348755151505100074a550541c1324800183d855d07418132007235d94350932040014d591dd16388010005172557458d2104001a2d5460854d89100052b65287d895144001a4e6560c7458810004a7a538714963040016aa90e1f64d89100051ea5442dd9100400125e9814b6354910007a150d42584614c8014cd93a177258630004bc64480550604c40126d98dd7525881000647153835c0615500123f9855054d85300062be1d8458a40040d364c9654d5218532007985516254510040018ae84dc85258630005a3a5052d8f62440014f29015376440100061761e8510b63440014d591dd56388010005a364c525916204001535911507655110006cc55080545414400162d9414b75d89100062ba1372149634400162d9510874d8910005b264c84589100400189d875904258c100053564c52dd91004001ea194589414401000627dd1839d1618800125f9660c42994100051b6547458932040018ac8761162504100160f21d54544605040162d95990545881000533a5c52d8d524400113f985d475d91100050f65e82d97644c00113d9815271181540049be6154153624400156a95210704c9200060fa1d54152608c40162e95dd154d89100043b6637558a4004001a667560450588100058b65052197624400126f985d47558
  | 7 => 0x511000437a6272d8e4044001d31545447050510004b3a4885d056304001a8d8460e75d891000687595841496304001a1d85d0842d8d100068be1d54151620400161d94a0b65d8d1000785d525458d1004001a2e84d5351d89100060fa1d541536388001aa6746044058810004b36605298d620400145d951d3634c91000437a5c85103634400162d941d565588100050f654641c1644c80123f985505458d210043be49861c1544c401a1d5460c5458a310058b65954151620400125e952144258c10005276507558d21040012d59121020d8d1000587a5b54953634400125f966144298c100044f660549c7605500126d95a1371d891000517e557458d3204001a8e8418852d8d1000527a537558e200400189d879904258c100049765682d93634400162d949d475d8910005936547458e620400164e951d2635881000536a4272d8d434400161e9655054d8d100053364e85dc963440014ce92dd763901100070dd52541c5634800161f965505498c100051d65464dc5604c801b255460454d89100043765c85d05630400161e951d254d8d100062d5d1811d0604c8016959110163508100062ba1172148604c40149e949d563880100068b615741d16204001a1c86d5254d8d100061761d8510b634400146c955d362485100051765672d8e404400143d9599173d9220004a76508714b6344001a2c5421954885210059364f871976244001c3454dd954440100058ba507559562040012cd93214405881000487e6154151630400168d9314a645881000527a5275d8f62440010ef926047655230007079d15458e500400143e97209655901000725951635c640040012cd981d46318910004b364c87d51620400162d9414b65d89100052725175d8d21440010dd981c96350410004ba2418754d620400129e9421852d8d1000687552801536344001e6352589514401000587a5764553634400145d951d363485100052b25175d89214400164d9510863d89100052725165dcd604840164d9321e65588100062761e84149630400125e95e184258c10004b564680d096304001e0f549516398810004b564485d0f634400186c75e096148650004b364f87553624400183d855d074d8d210053564c541c56348001a8d8460c75588100050f644541d9544c8014b79459471581320068d55181150614c8010dd972172158c100058ba5474591620400162e949d754588100050f648541d9544c00156a951d0704c9200051765464dcd6048401e0f549536318910004e3a438150d424c80107f985d47558e20004ab6538754f6244001a1f865505458c10005a364e74d0b6244001a8f7460e74d8910007239d9435093244001a4d6560c745881000687a1654103634400162f9461f65d891000687a1354d4563040018ac74e096148640004ba2418550d6
  | 8 => 0x62040012d591a004258c100059364e75197624400162e94d9554d891000647151839c76055001ac652219324c5100060fa1d54151634400162e9414865d89100052b65285dc9618c001e629558951440100052ba5375d8a20440015c592150714c9310050f64454dd9548c4010ef985d074d89100052b65075d892144001a4f6560e74d89100042fe61741d3638800146d95a1276189100074ad52541c13248001a4d851884218d100249b66354d4b6244001a2e84d5351588100058b65285d8952440014e5911d1629401000539e457558942040018ad845c852d8c100052b650855c8604c40168d9321d645881000536a42321d9324400183d855d07458a3100437a5c840836344001ac642219324c5100243b65c8510362440ab38e962014350932005a364c755916204001c8e7258d429001000497e615415363440018e9821c04058d2100437a6074d8d32440015a9941d4704c920004b56448510163040012ad94a1771d891000527a527258e500400161e94a0b65d8d10004ab66052991620400126d95a127058810006936158258d52040012e591201545881000437a5c8590b63440016c5911d463189100051be5574d89324400143d9599171d92200052ba5275d8a204400183d85dd274d8a10005a5a505258d100400146d952117218131007835505498d62040012cd9321c54588100049b65787d0f6244001c65521487158d2000d3325d43589320400113e9815170185540051765472d8d43440010bf985d074588100048be6154153624400143e9615271181540052da50521c563480016ca901d46318910005a36527518f6244001c2e745536294110004b36605218f624400161d9310965590100043b65c8510162040012d591a035258c10004b5644858cb634400146c955d162484100048fe6154150604c40149d949c96394010005396477458a200400168e949d763d89100043ba637558a4004001a2e8595040d89100062ba1f84d894144001a1d5460854d8d10004cbe61541506244001a2d5460854d8b100051ba5684dc9618c00149d9414b735891000587a5482193634400162e951d264588100060fa1d54151618c00123f985505418132005876508219763440012d591a024258c10004ab6605219362440094cc9750f624c9100051ba5e85d8952440010de981cb6350510005396477558a200400146e95a1f62505100061be1d8558a500400168d9314b64d8910005a364e741d36244001ea3425894144010004976626510963040012ad9421c50588100068761084595630400164d9314b75d89100051ba56849d8624400183d7561075d8532004376607558d3204001a1c855504058c100060fe17845c460551494d5961d0714c9310051e65442dd9100400145c9561d6350810004a76636414b634400143591150765
  | 9 => 0x588100048fe61541536204001a2c855504058810004b5646801496304001e894350960181323ccb964680dd1620400145e95dd16388010004c7e6154153634400131f985505458c100049b2558750d62040018cd871885218d100062ba11829c361548014ce9710b6350910004ab6508754d620400146f955d362485100042fe61741d1634841723c9859564553100044fa60545d9540400146f955d1624c8100058ba508759562040012d5912142058c10007835505498e620400523c98595645501000587652651516304001e63545895144010004972598510863440014ad941d5624841000533648545cc614800161e942096558c100052da50651c5604c8016e191a1562440100060fdd5849d76284001c375495376440100049be61751d762440012ad94a16705881000527a50525cf62040012d59814963c40100048f663659cb644c0014ae94dd56288010005b2a407418c62440014d591dd563900100065a1d4805d532480012e59121440d89100043b64a86dc5548c0015359115271181540064b15087551324800129e96a1052d8d1000c9b66354d4962040010de981d7634c910005276527558e200400126e95a1d43d89100058764c42d9764440014ad94e1f62545100051ba5787d8941440016699521162840100043be6175d8941440010ed92a0376551310052ba527558a200400125e9521020d8d100051725d5458d520400189d8761052d8d1000437a5c84c876344001a1d5460c54d893000687a1654d0963040016a591101625081000595a544258f1004001a1f85a1464d8d100052765072d8d5344001a1e656105258c100060fe1f745506054401e455354b61985320058b65052595620400164d9314b65d89100058725175551630400122f985505458810004a7a508714b634400149d9414b7358221004b364c87141620400145f955d163484100051d255641c5604c801c2e7455162940100058b650521d7624400149d94d9573186200058b65085589520400145e951cb63505100051b6568758a400400129d942142058c100050fa58545c361550016a994215624401000517a56645cc618800149d94e1f635491000725551635c64004001595941d4714c9310049b6604299562040018cd879885298c1000497a5484c85630400149f9461d6354810005aaa5085589100400123f98d9672d91100049be61651d1620400161d941496354810004b364885d05630400161d93a0b65d91300058b6507599562040010dd972142058c100061b995821c15188001c1f5495173d88100068b617749d36244001b2554604541891000587255645516304001a2c8555040d891000527650525cc6148001a9b64a0242d8d100048fe6154151638400149e941c963544100068be195415162040016ca90dd763189100058ba5075995
  | 10 => 0x9548c40183d85dd27458e20004abe61741d16204001e0f5495263588100058b25564551620400113f985d475590100051de5564dc5604c801a1c54219548c1300052ba5285dc9618c00149e941d56348410005b8646545891004001a2d546085418520004b564680d51630400146f955d162484100048fe6154152618c00125c9660c42195100060f5d5841d5620400146e95dd3628811000527e517558d320400183d75610751812100745550541c5324c40191c54e1d548c630004b3e59831d5620400113e9815170d8554005176577458e20040016c5911d363189100059aa548458a100400149d941d5635881000517a5674d8f62440014ad94a177258d10005a364c82591620400126e95e1d43d89100044f660541d9544c80189e87a105258c100059364e82d97624c00149e941d563588100041fe61751d7638800123f9855054d8e2000527e517558d210400123f985505458a310055a255741c1324800185f7560e75d89100060f61d5415261880014f290dcd71d8a100053364854dcd608840162e95a0b64d891000687a1354d476344001c4c7258d52544100052b65275d8a204400145d95991731862000734a1d63901100400162f9561f64d89100068be128419762440012e591214405881000437a6052dcd62440092e49660675d89100056aa50751c132480014ae9721162508100068ba1654d0b62440012ae989d464d89100448f66365d9154840012cd981d563588100052da5052dd91004001a1e84d535358c100044f660545c760550018ac84e0971181520063a608701416348401a1d865505458c100060f615741d162c40b15c993210704c92000497e606510b634400146e95a1d62900100053aa5b841c132480012ac9661275d8910005a3a5075d8c624400123f985505458a10005a364e75193624400189f7460e74d89100064ddd5819d764440010dd981c963544100058b65474d09620400143d9215076551100051b6578758a40040014ad94a1d62940100048fa60425956404001a1d84d4852d8d10004a7a50858c96304001a2f85a1764d89100053a24174d89214400164d951d0631891000536a4272d8d5344001b155460454d8d10005a364c521936244001a355460454586300052d251651c5604c801ad18558e4044010005276507258d510400162c9461f65d89100050f65065dcd65484015359115170d85540051725564dcd604840126f9819674d89100058b65674d9362440010de96a037150d320051725574d8d214400168d9310a745881000687d95839cb644400146d95e1f6250510004b32617350d6204001a1f6561052d8d1000593a544258d620400146e95e1d62900100049ba5a859d36244001e0f5495363d8910006275d1831d0604840168d9414863d89100068761b549516304001a2d8421165
  | 11 => 0x458b10004b364c8710162040012cd981d563988100070755054dcd608840164d9314965588100068b1538655221880018cd879485258c1000687215541036344001a96546044058c100052be5175d893244001a2d86d5254588100052b652859d8624400164d95109635881000617a1e85109630400185d87d485258c1000527a5c4258d420400129e942172158c1000633a1e4210b634400168d939d764d8910004cbe6154151620400161c965505418d100050f64c54dd9548800162d95a1362509100059364c82595620400129e9810b6350910005b864754589100400183d875505418532007071d55458d41040014ae941d7624851000687a19541506344001c555458d719401000587a536555363440012ae981d5645881000687a1354141630400129d942163258c100058ba538719762440014af945d762485100043e24187151634840129d942172158c100058b6526515162040018ad87e136290110004b3a4885d0763440014e6921507158d200060f615849c3615500146d95dd362881100068b55182153604c8012ce989d363d89100060f61d6514964040014769510b7158d200068b5518215160884012ce989d763d89100078a5505458a100400149d941977358121006a361062148634400164d93a0b65d89100053c241641c5604c8014ad949d56288010005a3a505298d6204001c1e7555163900100060fa1d54152608840183d756107558d210044fa60549c0615500162e9419754d89100068ba1354d4f6244001c1d5415173185200052765075d8d21440018d563604705481000437a6042dcd6244001a2e85953425881000cb964487141620400145e9510b73589100050f65065dc5654c80162e94209655881000617a1e8510b6344001a4e859884258c1000527a5375d8e2044001cd28758e50440100061d5d5811d4604c8012cd9321e5458810006179da85108634400164d9314875d89100060f61d5415162c40010dd9814973d88100050f644541d954484014759519071581320050f65854dd9540400183d855d074d85320061761d651096304001a2d546085458a30004a7e615415163040018cf7560e75d891000527a5275d8e20440012d591a005458c100075154d52dc5604c80145f955d3634c910004b364885101630400146d95a13725863000593a547458e62040012af9461d5358810004a76606414b63440018cd7460c74588100060f5d5841d7634840162d9414a65588100062761f421096304001a8e7460c7458810005a364c7599162040014d59310b7158d20007079d154d8e50440012ae9421d5358810004376627258e50040014b99414b7644010005956544258f10040010bd97a13651862000487e61541536344001a1e84d535258c100063360d7214b63040015a8945d4704c9200043b64a80dd
  | 12 => 0x95620400183d8755054d8b1000587e61541516304001a8e849885298c100054764c541d9544c001c974258d71900100068b55182151638840125e96a1442d8d100048fe6154151624400162d9510a7458810004b6a408710b63440010ef926047655130004a72598414b63440014759510b7158d200062b1d0865d1214800186e85dc8425863000c3b2617558941040014d59119173186200048fe615415260884016c993215628401000593a5442d8f624400185d879944258c100068755183151630400161d9414b63549100052725d5458d42040012ae9421c5458810004b364885d0763440014af945d5624c8100070b1d554d894144001c575258d7194010005876548299163040016ca90dd06318910004aba6275d93624400168d9321162508100044f660541d95448401aa46460454d891000517a5787d8d42440014af945d56248410004ab26174551620400183d875505458e210048fe61541516204001a2e84d5050d89100052ba5075589210400191c54e1d548c531004b3a6075d8c6244001569951d0704c9200070b9d554d8a404400126e95e1f43d89100061ba15829c3615080129d9421420d8d100049765484c85630400145f955d36348510006871968414b634400146d95dd162880100058ba5487591620400185d7560c75181210060f61d54153604c80186c85dc932586500060fa1d541516088401a2d8521764d8910005876544258d42040018ac845c9321814100497a5484c87634400129c9660c5219110006b4e15639011004001634965515150510004a7e62641496304001c8e72d8d42901100048fe6154153614800129d94a0b75d8d1000587a5265d5163040018cd83dc842586300044f660549c3615500143d9115076551300058ba5275197624400161d98d525458c100068ba1354d4d6204001a1c8755054d8d100070b550545cb630400149e949cb6394110004b564485103634400123f9855054d8930004abe6154153624400126e9521c4058810005a3a507598e620400168d941d66398810004aba5087d4d620400143d9315076551100049b66042d97624400164e959d363d89100068b61954151620400153591152765511000693dd5839d762440014ad94e1d62940100251b25d54d89524400123f9855054d8910004b3e59831d16204001e0f5495263988100060fa1d54151628c0014e89061572181310068ba1354d4b62440016699521162440100063360f72109634400145d959d363d89100042fe61741d0604840186d87e1762941100051ba5c855895204001e516354a50440100049ba5787d07624400146e95dd1628801000d1b25d54589520400125d95a0b74d8d10004b36607598e6204001ac46260452d8d10007131d95354932440018d9831c05058d210052765272d8e504400123f985505
  | 13 => 0x54d8910007071d55458d42040014e8905d5624c81000617a1f5214b63440012d4984c9614c6500041fe61751d5634840186e855c8421813100687e6154151630400129e9421632d8d100058b66354951620400107f985d475d8a100042fe61741d163880014d5911c963900100078ad525458a10040014ae97a1362509100068b61954152620400162d94d9654d89100053364e849d8624400164d931d565588100060fa1d54151628400183d8755054d8121004ab65087d4d6204001c1f5495173185200060fa1d54151634800183d8755054181320059364e75d9762440012af985d074d89100048fe6154152608c40149e941c96354c100060fdd5849d56188001c4f75dcd53d89100048fe615415360484094ac9755362509100070b1d554589410400149d949d76388110005a3a507558d62040012cd9810963508100068755183151638800145d951d163588100050fa58545c0615500143d96153765523100517a5774d8e20440014d5931087158d200052765072d8d51440010de989cb63941100068ba1b5495362440014d7915d1634c8100068b55182153634800183e8755054586200058b65764d53624400143d9519070591210058b65087595620400107d97a176418620005362418758d420400129c9660e72d91100042fe61741d362440018e972201321815100587a5682d936344001a2e84d505058810006a3a12839d762440010bd972116598532004aba528754f62440012ce981d363189100044fa60541d954440012cd981d263988100068b55183153624400161e94dd554d8d10006876148599163040012cd93e1f54d89100070b9d55458a4004001ca5421087158d2000617a1d851096304001a1f84a126558c100069361662109630400168d941d563588100243b66375d8a404400143e96150765513000517e5564dcd6048401d1754950714c931006a995181101620400183e8755054d8e1000527a5072d8d51440014cd9321572d8c1000617a1d8510b634400166a9521162440100060fa1d651496404001a95546044058c10004b5644850836344001a2e84d53525881000437a5c85083634400143e901537655231004a7e606414b634400145c9755363549100051765442dcd624400183e8755054d8530007835505418f624400146e95a137258d100058b663549536244001cc993a18704c9200068b5d5841d5620400132f9855054988100048f65a841c96504001a1f84a1065d8d10004b56468094963040018cd835c8421813100687a1654d0b6344001ae18558941440100040f660541d9544c80164e951d06318910006a36118258d4204001a1f85a1764d8d10005956445058d5204001c8d745cd43588100053664c52dd910040012af985505458810004abe6174d0b624400164d959d363d89100059364c529
  | 14 => 0x5d521480018cf7460c7458810005996445058952040018d78754d61185320063c606809d932840b15c89750c704c9200064b150875513288401a2f84a1365d89100049b259859d362440018ae845c852d8c100053364e87d89514400162d94149755881000517a547458d620400186d85dc84258d100061b61772109618c0018e787549611853200565251751c5324c40162d95a0b64d8910004976636510b634400183d875505458c10004a7e6154153634400107f985d475d8930007621d1431c13248001554955d0714c9310068be61541536244001476951087158d2000517a547258d430400129e94a0b65d8d100048fe6154151630400129e942157258c100052e241741d16348401a1d65a105258c100075154d521c5604c80129f966105258c10007835505418c624400161e959d25458c10007a8a51625051004001a1e84d5352d8d1000497654845c963040010dd972164258c1000517e558758d4204001535911517018554004aba607599162040014779559071581320059364c421976244001a1c855534258c1000687a1654d0d630400123f9855054d8c100052765275d8f62440015e191214704c92000587a5082995630400141d931537655231004a7650825d5630400107f985d475586200042fe61741d3614c8034ac9755162508100053364c845c8604c40149f945d7634c9100058b6548799162040018ae8460a70d85540054764c54dd9548c4012cd9221440d8d1000565a50751c5324c4014ae94e1d629401000527a5065dcd604840149e94149731852000693a146210b634400125d96a144258c1000527a5075d8d2144001a2d5460c54588100060f61d54153624c40183e8755054d89100052de5165dc5604c80149f9459773581210050f65464dcd644840143d94215764ca500044fe61741d16504001c4d52149731852000527e5175d8d21440010ec985d762505100068b55182151634800166a90e1f65d891000693a15839d3624400145d95dd3638811000587a50821976344001c1f549537358221005176567458e2004001c2f5495172d8c100064b153825c4605500149d941d5634c8100048fe615415362c4001c4c72d8d52545100049b663659d362440018ce8794852d8d100050f64854dd9548c4016959414963c40100070e15376551100400162e9499754588100052ba5287d89514400126d9819674d8910004a7653871496304001a2c8755054d891000687a1354d4f6344001a1d5460c54d8d2100587a5065d536344001e295415162440100058ba5052d97624400123f9855054185320050f64c54dd9540400125d952096458c10005a36507518c62440010dc966047050d3200497661651096304001e916350a40440100058b6546450b604c80129d94a0b65d8d1000617dd5839d5618800162f98550
  | 15 => 0x5458a310061ba15829c36155001aa57460440588100061b61572108604c40156b955d0704c9200053564c42dd91004001a2c8655054d89100048fe615415163440014b59414b7158d20005a5644821936344001ad220219324c51034ce3a5b8150d424c801c2c7555162508100060fa1d54153624c00183d8755054d85320049b661651d1620400168d9310964588100053364e745d3624400183e8755054582310061ba17721096344001c2c74553625491000687a13541436344001a1f84a116558c103ccb964680dd5620400168d9310864d89100053364e755d762440014d5911d563880100043765c84081630400143e9015076551210060f61d54153604c4010dd972095458c100058ba5052595620400107f985d475d8d210068ba1d54153624400125c9660e72d95100062761d64149630400164d951d2639881000783d525418f62440014e7915d1624c810004b526132585319000149e9710b63509100044fe61741d36544001c646554871581320062761d841496304001a2f985505458810004b56605258d100400129e9421721d8d103cdb864484589100400189d87a1052d8d100049b26175551620400162e949d765d89100063558d811c1420400162d949d752d8910004ab66275d93624400164d932156254810004ab66374d09620400129d942157258c100050f652655cf65880012e89061d4358810004a7e636414b6344001a2e8595343d891000617a1c6510b6344001a2c8555342d89100042fe61741d3624c00129d9421632d8d10005a36505258d6204001c1c7555363505100048fe615415163c4001c2c755536250910005b264c85589100400183d87d9452d911000693a16839d3624400164d939d475d8910004a765085c87634400143e961507655110005a364e84d8942440014d5919d1634c8100060f5d5841d4604c801a1d6560c725923100535647655cc61880014cd93e1d62940100059364c7599562040014ad941d7624c9100068b61485991620400146d959d362881100063c60470141634840183d875505418530005332497558d410400161f955935458c10007079d554d8e404400103e981507655110004a7a50825956304001a1d8521764d8d10006a955181101620400143d9499571d962000527a5052dcd608840129e942097558c1000715d51635c65004001a1e65a105258c1000595a544258d10040016a591e1c64d89100068be128499562040010dd972132158c10007071d15458d5204001a1d5460c54d8132004976548610b6344001a946460454d8d1000535647645cc61880014d7915d5634c81000687a1564109630400161c955d15458c1000693615839d3624400125e952096458c100059365442d8f624400146d95a137258d1002c8f66365d915444001c1c755516350c100061b1d486
  | 16 => 0x258d100400162d959d064d891000539e4575589320400191c5421d544ca300068755183151608c40125f966144258c100059364c525d56204001a1c54219544c530006175d5831d5620400107f985d475d8532006876148559163040010dd981d1634c8100050fa40541d9544c0016c5911d76318910004b36604218f6244001e455354961185320068b55182151628400189d879905258c100068b2155450d620400126d95e1f41d89100068ed96801cb644400183d875505458d210068ba1654d0d6204001475951087158d20006275d1831d1620400149e94d9573186200060f617749d36388001a1d546045458c10005b4a405258d100400125e95e1c4258c100052725d54d8d424400161d95d9354d8d10004976548710b634400185e8719452d8d1000517a547458d320400161d9420a6558c100068755183153634400162c9561f64d8910004b364f879536244001c2e76550541891000587e61541536344001c2c7455162548100068ba195415362440016659121065d89100049ba5684dcf62440012ad94e1f51d8910004abe59841d5620400125e952117258c100048fe6154150614800126d9521173588100051b6567458a20040014d5911d563900100049be558750d62040012ae94215735881000587653659536344001c4f7654d524c8100058b65464509604c801c3b5495376440100078ad52545891004001a1d5460c54d8f100064b151829c3615500143d9115076551100058b65087995620400145e9510973d881000587a5075d53634400162d941d7525881000723dd37350f624400123f9855054d8d2100687a1b549536344001a1d6560c5259010006b118981108634400162e9421e65588100053364e84dc9618c00161f945965458c100068b21554d0962040034cc9754d624c81000687a166410963040014cd93a137258d100049b65a851d16204001a1f85a156458c100050f64454dd9548800125d9521321d8d10005a3a505218f6244001a8d849885258c100058b6546450a614c80164d951d163588102ada32594350b604c8014ea96214704c9200059364e85d89524400149e9499573186200068761d541516304001a4d85a0e74d89100060f5d5841d562c400162e959d064d8910006936146210b634400129e942142058c10007a858942505100400946d97d8952941100052b65075589320400161d9510b6350910005b4a434258d10040012ae94a1773d89100061b217825c46050801a1f65a1052d8d10004b964487153624400161d959505458c1000527a5387d8d52440016ca901d763189100058be61541516204001a2c8555143d8910005a365275d8f624400183d756107558a310068b55182153638840126d95e1d43d89100053364e87d8941440094cc9754f624c9100048fe6154151638800183d8755
  | 17 => 0x4044e300c00c00e00302700002900001b01a0df0000050120060030240000000190400990000340000430154b700400400b0200050500020000020100020040580300a200404a17300208b00300004e0d70500140020190010c800d02501200000000300000e0010890010000000090000000710710c500004900a00900703900000000000300205404000900b14001f00400000f00502104c02504b1a20280000110020001231120031ec00000302b03e00900116b00300400504500616100700205000b00801c01c00c0440011ec20a04400100d02e00847301500800900100001800600e01f0a502703700e01a02b00606b00100e13e00803a02500e0ad00006000f00000c02f02900003901400101d00002502a00901500402400032600200001800101500504c00800300100004200100500100200c00216500606e00816f00b00c0040020010025f40670050b30090050070010030230f301000500002d00304201105901a00100003002c01001d01900000c00500600600102500000b02e00000100f00000000002813900204a00002c00000f00400000701614300001801304d05c01803c0043be617558941040016d290d516344010005a364c4299162040012cd989d063d89100044fa60541d9544c00162d959505458810004972598510b63440011e992a03715521000d2b25d6250941040016e191a11624401000587a5482991630400164d951d363189100058764c825956404001a97426044058c10004b364f871536244001a2d54608541853200527a5072d8d53440012ad9421573588100051b65687d89414400161d95a0b64d8d100059964787197624400143d95a1076506200068b61084d976244001a1f9855054d8d100051ba54845cb6304001a1d5460c54d8e2100535658541c5324c401c8c7258d4250410004a7e598314a6404001a1d84d485258c10005a364c42d93624400162f9559354588100059aa438719762440030ee9721741588100068766354951630400123e96a1272d951000593a547458d620400125e952097458c100053964674589320400161d98d5254d8d1000497654848c963040010ee98dd762901100051ba5474d89324400123f985505458a30004976548408163041495c692150714c931004a7e59831c9640400161f965505458c10007855505458f10040012cd93e1f51d89100052ea5052dd91004001a1d855904258c100051b654845cb6304001e0f5495063189100058ba5052995620400129d985905258c1000555654741c5324c40161d942096558c10007071d15458d530400145e959c963900100051da5442dd9100400168d931d164588100058ba56749516204001c4d7654d524c8100049ba54871516204001a2d859d0745881000636e1d53580604c801a8f84e0b6350910005956544
  | 18 => 0x110580104670000db00400003601400500000700300000909a0042e901002b0c600002403902600600000100a10100f00603b5a901003500102202602464a00403500c01f00b03c00701d00000100100c03300c03301403700a00503810f05100000400700000000200500a00001600000100000101b00201502d00000001501200100805900300100b02c11a00500c00c00300200200011500000d0630010540160052330144330010360000150000150110330aa0000032ae26803b16f32300301100c0310000010530170130280d90040030200240000040490cd00a02609c01001a0050000041a300e00005f00e00000102000101900200100700502001202d00500002300f0760440110020000000330a512802e0230870000040000330160340040030fe00000200f00d00200300101100701b17504d0040b004e3c904203400325a00a03104800000600002500002c0cd01d00b76c0192660860000000002bd04301245600400602e00700903906c00b00602100700000300000d01803c01200206915100100200003103501300a03900000001200002800800001a02202401102001c00c00000627703600231a0000030010521250010000010c500e01400300803600000100400009f00201800130100304800000500200002c0010081df0040000350050010000002b012900200d00203105600900906402208c00b0480020120080190010080150180000000100420010480bb0010003ac00600d00500304d00300001100100f40100a01a02702c01500000201120f01b03e00100701a0020010050070040231a606001c00a00100300a00400300500200000501401c00a008018
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xa4000983ea554151639881000491b52392c6a12820800222fa8656641516204001307d4aa82a4c6b102000a0ba9854e09711815400445d5242aa9a12c40800282da5993825c64088001416d20ebc12c290ca000887aa48555341d8d10004a5752aa0a8382649000222fa961485591620400110fd432a320a9b1a2000a0769c855504058c100054494caa3022a0c48800284da3e1d8558a50040011175490aaa080b102000d0365542109731852000503b4c2a10eaa2649880222ea9e1d54151620400121bd4aa82a6e2b1a4000887aa48755054d8d1000505b4a3a704b0a432000281ea6153835c06155001117d4b0a42cc8b102000a436885421d544ca3000443d5242aa9a16c68800222ca9a1954150624400150a532a8c08a9b1a2000887ea58521764d8d1000425b522a10eaa2649000282ea6150875513248001a12aa3242a0e2b1a4000c856119121065d8d1000486f52aa0a838ac6900032158564485193634400180fcc4ecaa0a831a2000a2368f87611629001000506d502a6ecaa2200800222fa961084d976244001217d13222a0ecaa26400a896848755054d891000521b462a10eaa2649000282da5213724c96190001446d190ec22c4a08200088ba9b9855054d891000443d53c3aa82a2c60800222fa865265151620400110fd4b08424cab18200088b6a454e19548862000443f50cb2a82a2c60800282da4217724c96194001416d390aaa080b102000985ea55415163c401000443f52c2108b2ac60800341596550541c5324c40120fd4aa82a2e7b10200088bea58421065d891000443d52c32a82a4c60800282da5211724c86050401486d10a843aa89926200a13e8d87e17629411000690b26a108438ac69000222ea921554d0f624400141c502eac20eab1a420098aea5541516284010004c1f52aa0a8b1ac40800221fa9614851936344001116d3730aa0a8b102000887aa4855534358c1000682aa8c98a838ac69000242fa2644541d95448401216d15202a6ecaa44000a0b69075219754852000505d4c2a305386c2aa00303985241741d16348401506d190aaa683b122000b4169474508714c9310044994cc8900a9aa49900361154a405458d1004001a06ca2a4292e630a4000a4a69474201744c92000509b4643b0ab12a208002838a061d541516348401416d30a843aa89944200d8155191150631891000443d5242aa8206c68800212da9150875513288401096d48a843aa890a4000a07a985460e71d8154005a0b483aaa438a649880221fa8650651536344001506d110aaa081b1a2000887aa5865505458c1000445953432a82a6c48800221ea9e1954151630400120fd4aa82a2e630a4000a83688855534158c1000491d52396c6a128288002a15a1215541016304001117d4b0a42ec9b122000a07a9c8555040d8d10
  | 1 => 0x56204001307d4aa82a6c6312200098aea554151624401000542b4243aa82a6c688002a0da3215541036244001227548e5b1aa4a8a200090bea5541537258d1000489d53396c6a94a088292c45a61d5521c5324c401226d4ce4b1aa52802000a0eaa054dd9544401000443f50cacc82a2c60800222ea9219541536244001117d4b08422cab102000c0be6276550541891000505b4b32304382831000222ea961954152620400110ed4d0b2a0a8b182000a0769854e1d548c53100485f44c88a9bb2a91000222fa865954151620400128bd4aa82a0e2992620088baa485553435881000505b4842ae4990c0a880242fa9550545c8604c401116d452caa0a9b122000887ea5852156458c1000443d5242aa9a12c608292c85a61d1421c5324c4011175490aaa685b122000a0b69265e09719422000491d53396c6a14808800281ea715086552304c001307d4aa82a0c7b122000a0769c54219544c53000443953432a82a6c68800282da4995821c15188001a06caa84216e6b044200887ea58421065d8d1000541b4642aa9a0ac40800222fa9614851936244001a82aa3242a0e29926200a892995460454d891000443b514b2a82a6c68800221fa961084d97634400140f5390aaa683b1a200090bea554153725863000485b45480a83b2a89080222ea9619541516204001619500a9bb2a8880200084b6a454e1d548812000642aa8c8d002a2c60800281da721554d05630400130bd4aa82a2c68802000a1368e87e1762545100045194cc8900a1a849900221fa9614859916304001446d1d0fc26c4a0a200088baa786550545881000489b52392c6a92a20800224ea6a438154d524c8011175490aaa682b102000a0b69474219744852000688b26a90a438ac69000221fa8652651516304001612d28c8a10e2b02640088baa48555040d891000544b4242aa8202c408002a0da221554d07634400110f5490aaa080b182000d0355192153735822100443d5242aa9a1ec68800288fa361f84d8a4044001a06aa3242a2e630a4000a0ba9c8555341d891000443d4dcc2a82a6c68800221da6e6154151630400110f5490caa0a9b1a2000b0969065548715813200542b4242aa8206c68800222fa865065153624400140f530a843aa89946000907ea5541537358221005253483a900baa649000260fa95505498e6204001a06ca2a4296e6b044200d09655421087158d2000541b4642aa8202c4080036215464454589100400120fd4aa82a6e6b12200088b6a685950545881000541b4442aa8202c60800222ea921d541536244001c23c3aa6a92c230a6400a896848555342d891000485b45480a83b2a89900222da9150865522148401217d4aa82a2e5b182000a0b69c855534158810004c1f52aa0a8318c488002c31a1153765511004001a12ca2a4290e2b1
  | 2 => 0x501c8420000000107c01a40000005000900010008820014c04445464000400000000003dac300c003c10000034046c00480c10684f1c008c02352c1808302c2424101a341448cc0000d00040105c4808000008b0201170e0046400007c0000b00c002810011175490aaa683b122000a0ba9c8555040d891000544b4242aa8206c48800260fa955054d8f624400150a532a8c08a831a2000a07a9854e1d548c63000443d5242aa9a0ac608002a15a121554d0f6344001912c2322420cbb12200088bea19519054d891000644b0ac890a326c48800228ea6a438150d424c801486d18a843aa899442009236a67258d429001000443953432a82a0c68800222fa96108499
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x4b
  | 2 => 0x4d
  | 3 => 0x4e
  | 4 => 0x94b
  | 5 => 0x94d
  | 6 => 0x94e
  | 7 => 0x124b
  | 8 => 0x124d
  | 9 => 0x124e
  | 10 => 0x138b
  | 11 => 0x138d
  | 12 => 0x138e
  | 13 => 0x98d
  | 14 => 0x98e
  | 15 => 0x128c
  | 16 => 0x128d
  | 17 => 0x128e
  | 18 => 0x9cb
  | 19 => 0x9cd
  | 20 => 0x9ce
  | 21 => 0x12cb
  | 22 => 0x12cd
  | 23 => 0x12ce
  | 24 => 0x130c
  | 25 => 0x134c
  | 26 => 0xb0c
  | 27 => 0xb0d
  | 28 => 0xb0e
  | 29 => 0x140d
  | 30 => 0x140e
  | 31 => 0xb4b
  | 32 => 0xb4d
  | 33 => 0xb4e
  | 34 => 0x144b
  | 35 => 0x144d
  | 36 => 0x144e
  | 37 => 0xb8c
  | 38 => 0xbcc
  | 39 => 0xccd
  | 40 => 0xcce
  | 41 => 0x94053
  | 42 => 0x94055
  | 43 => 0x94056
  | 44 => 0x124053
  | 45 => 0x124055
  | 46 => 0x124056
  | 47 => 0x138053
  | 48 => 0x138055
  | 49 => 0x138056
  | 50 => 0x124953
  | 51 => 0x124955
  | 52 => 0x124956
  | 53 => 0x138953
  | 54 => 0x138955
  | 55 => 0x138956
  | 56 => 0x98955
  | 57 => 0x98956
  | 58 => 0x128955
  | 59 => 0x128956
  | 60 => 0xb4953
  | 61 => 0xb4955
  | 62 => 0xb4956
  | 63 => 0x144953
  | 64 => 0x144955
  | 65 => 0x144956
  | 66 => 0x139253
  | 67 => 0x139255
  | 68 => 0x139256
  | 69 => 0x99255
  | 70 => 0x99256
  | 71 => 0x129255
  | 72 => 0x129256
  | 73 => 0xb5393
  | 74 => 0xb5395
  | 75 => 0xb5396
  | 76 => 0x145393
  | 77 => 0x145395
  | 78 => 0x145396
  | 79 => 0x128995
  | 80 => 0x128996
  | 81 => 0xb0995
  | 82 => 0xb0996
  | 83 => 0xcc995
  | 84 => 0xcc996
  | 85 => 0x168b
  | 86 => 0x141295
  | 87 => 0x141296
  | 88 => 0xcb
  | 89 => 0x12c9d3
  | 90 => 0x12c9d5
  | 91 => 0x12c9d6
  | 92 => 0xb49d3
  | 93 => 0xb49d5
  | 94 => 0xb49d6
  | 95 => 0x1452d3
  | 96 => 0x1452d5
  | 97 => 0x1452d6
  | 98 => 0xcd2d5
  | 99 => 0xcd2d6
  | 100 => 0x8c
  | 101 => 0x14d
  | 102 => 0x198d
  | 103 => 0x140b15
  | 104 => 0x140b16
  | 105 => 0x24b
  | 106 => 0x16cb
  | 107 => 0xcd415
  | 108 => 0xcd416
  | 109 => 0x144b53
  | 110 => 0x144b55
  | 111 => 0x144b56
  | 112 => 0xccb55
  | 113 => 0xccb56
  | 114 => 0x154c
  | 115 => 0x2cd
  | 116 => 0x19cd
  | 117 => 0x10e
  | 118 => 0x184e
  | 119 => 0x95395
  | 120 => 0x95396
  | 121 => 0x4953
  | 122 => 0x5395
  | 123 => 0x5396
  | 124 => 0x5253
  | 125 => 0x95253
  | 126 => 0x16c053
  | 127 => 0x125393
  | 128 => 0x4955
  | 129 => 0x4956
  | 130 => 0x95255
  | 131 => 0x95256
  | 132 => 0x5255
  | 133 => 0x5256
  | 134 => 0x16d253
  | 135 => 0x99295
  | 136 => 0x99296
  | 137 => 0x129415
  | 138 => 0x129416
  | 139 => 0x94b53
  | 140 => 0x9cb53
  | 141 => 0x95453
  | 142 => 0x9c0d3
  | 143 => 0x9294
  | 144 => 0xc9d3
  | 145 => 0x9d2d5
  | 146 => 0x9d2d6
  | 147 => 0xd2d3
  | 148 => 0x1692d3
  | 149 => 0x98b15
  | 150 => 0x94b55
  | 151 => 0x9cb55
  | 152 => 0x95455
  | 153 => 0x98cd5
  | 154 => 0x98b16
  | 155 => 0x94b56
  | 156 => 0x9cb56
  | 157 => 0x95456
  | 158 => 0x98cd6
  | 159 => 0x56d3
  | 160 => 0xb1415
  | 161 => 0xb1416
  | 162 => 0x154b14
  | 163 => 0x16d453
  | 164 => 0x24b53
  | 165 => 0x16cb53
  | 166 => 0x140cd5
  | 167 => 0x140cd6
  | 168 => 0xd453
  | 169 => 0x1689d3
  | 170 => 0x16c9d3
  | 171 => 0xb4253
  | 172 => 0x25453
  | 173 => 0xb56d3
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 10 => 1
  | 9 => 26
  | 8 => 738
  | 7 => 4347
  | 6 => 5773
  | 5 => 2058
  | 4 => 218
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 10 => packedAt gbK10 (i*15) 6
  | 9 => packedAt gbK9 (i*26) 17
  | 8 => packedAt gbK8 (i*37) 28
  | 7 => packedAt gbK7 (i*48) 39
  | 6 => packedAt gbK6 (i*59) 50
  | 5 => packedAt gbK5 (i*70) 61
  | 4 => packedAt gbK4 (i*81) 72
  | _ => 0
def gbH (k i : Nat) : Nat :=
  match k with
  | 10 => gbHint (packedAt gbK10 (i*15+6) 9)
  | 9 => gbHint (packedAt gbK9 (i*26+17) 9)
  | 8 => gbHint (packedAt gbK8 (i*37+28) 9)
  | 7 => gbHint (packedAt gbK7 (i*48+39) 9)
  | 6 => gbHint (packedAt gbK6 (i*59+50) 9)
  | 5 => gbHint (packedAt gbK5 (i*70+61) 9)
  | 4 => gbHint (packedAt gbK4 (i*81+72) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 10 => 2*((h/1+packedAt gbK10 (15+(h % 1)*1) 1) % 1)
  | 9 => 2*((h/15+packedAt gbK9 (676+(h % 15)*5) 5) % 26)
  | 8 => 2*((h/253+packedAt gbK8 (27306+(h % 253)*10) 10) % 738)
  | 7 => 2*((h/1449+packedAt gbK7 (208656+(h % 1449)*13) 13) % 4347)
  | 6 => 2*((h/1938+packedAt gbK6 (340607+(h % 1938)*13) 13) % 5773)
  | 5 => 2*((h/693+packedAt gbK5 (144060+(h % 693)*12) 12) % 2058)
  | 4 => 2*((h/100+packedAt gbK4 (17658+(h % 100)*8) 8) % 218)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x3ff03ff03fe07ff83ffff807f49f467d19f3f3
  | 1 => 0xc1ffc0ffc1ff83ffc1c03ffffb68b98ee63c9f
  | 2 => 0xfe1fff0001fffc3ffe003ff80c70c1f307cf1c
  | 3 => 0x1ffffffe00003fffffc0000f80fe03f80fe0
  | 4 => 0x1fffffffffffc0000000000fff0003fff000
  | 5 => 0xffe0000000000000000000000ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x22005200260044802548812a003023408d131
  | 1 => 0x4141405440888290408112a541281888622486
  | 2 => 0xb41aab021135682eb402a5502c50c153054b18
  | 3 => 0x101cf29ab4042037392b00604e80ec03b00ec0
  | 4 => 0x211f3cef39de7302100c01818ffd0003dfb000
  | 5 => 0x3988200c20184204203006060ffef7ec000000
  | _ => 0
def gbRaw : List Sig := (rawDecor 63 gbPos gbNeg).map Prod.fst
def gbPools : List BoundPool := [(0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333, 6, 0, gbRaw),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 8, 0, gbRaw),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 8, 0, gbRaw),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff, 8, 0, gbRaw),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 6, 0, gbRaw),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff, 8, 0, gbRaw),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 6, 0, gbRaw),(0x22222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222, 5, 0, gbRaw),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 5, 0, gbRaw),(0x330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033, 5, 0, gbRaw),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f, 5, 0, gbRaw),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000, 5, 0, gbRaw),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f, 5, 0, gbRaw),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000, 5, 0, gbRaw),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff, 5, 0, gbRaw),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 5, 0, gbRaw),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff, 5, 0, gbRaw),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000, 5, 0, gbRaw),(0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff, 4, 0, gbRaw),(0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff00000000, 5, 0, gbRaw),(0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000, 5, 0, gbRaw),(0x220022002200220022002200220022002200220022002200220022002200220022002200220022002200220022002200220022002200220022002200220022, 4, 0, gbRaw),(0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f00000000, 4, 0, gbRaw),(0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000, 4, 0, gbRaw),(0xff00000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000, 4, 0, gbRaw),(0xff00000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000000000ff0000, 4, 0, gbRaw)]
def gbAtlas : Atlas := ⟨10,rawDecor 63 gbPos gbNeg, 0xeeeaeee8eee8eac8eeeaeee8eee8eac8eeeaeee8eee8eac8eeeaeee8eee8eac8eeeaeee8eee8eac8eeeaeee8eee8eac8eeeaeee8eee8eac8eeeaeee8eee8eac8, gbN, gbR, gbH, gbI, gbPools⟩
end PEqualNP.Outside.L_meta_36783
namespace PEqualNP.Outside.L_meta_36783
open PEqualNP.Outside.L_meta_36783.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_3_0 : Interval s1Atlas 3 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 3 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 14 := bs1_4_0
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
theorem bs2_3_0 : Interval s2Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 21 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_96 : Interval s2Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_192 : Interval s2Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_288 : Interval s2Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_384 : Interval s2Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_480 : Interval s2Atlas 4 480 71 := block_range (n:=71) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 551 := (concat (concat bs2_4_0 (concat bs2_4_96 bs2_4_192)) (concat bs2_4_288 (concat bs2_4_384 bs2_4_480)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_96 : Interval s2Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_192 : Interval s2Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_288 : Interval s2Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_384 : Interval s2Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_480 : Interval s2Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_576 : Interval s2Atlas 5 576 90 := block_range (n:=90) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 666 := (concat (concat bs2_5_0 (concat bs2_5_96 bs2_5_192)) (concat (concat bs2_5_288 bs2_5_384) (concat bs2_5_480 bs2_5_576)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 40 := block_range (n:=40) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 40 := bs2_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_7_0 : Interval s2Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_7 : Interval s2Atlas 7 0 1 := bs2_7_0
theorem alls2 : ∀ k ≤ 7, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
  · exact alls2_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 10 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_96 : Interval s3Atlas 3 96 16 := block_range (n:=16) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 112 := (concat bs3_3_0 bs3_3_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_96 : Interval s3Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_192 : Interval s3Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_288 : Interval s3Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_384 : Interval s3Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_480 : Interval s3Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_576 : Interval s3Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_672 : Interval s3Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_768 : Interval s3Atlas 4 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_864 : Interval s3Atlas 4 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_960 : Interval s3Atlas 4 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1056 : Interval s3Atlas 4 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1152 : Interval s3Atlas 4 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1248 : Interval s3Atlas 4 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1344 : Interval s3Atlas 4 1344 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 1345 := (concat (concat (concat bs3_4_0 (concat bs3_4_96 bs3_4_192)) (concat (concat bs3_4_288 bs3_4_384) (concat bs3_4_480 bs3_4_576))) (concat (concat (concat bs3_4_672 bs3_4_768) (concat bs3_4_864 bs3_4_960)) (concat (concat bs3_4_1056 bs3_4_1152) (concat bs3_4_1248 bs3_4_1344))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_96 : Interval s3Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_192 : Interval s3Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_288 : Interval s3Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_384 : Interval s3Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_480 : Interval s3Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_576 : Interval s3Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_672 : Interval s3Atlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_768 : Interval s3Atlas 5 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_864 : Interval s3Atlas 5 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_960 : Interval s3Atlas 5 960 57 := block_range (n:=57) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 1017 := (concat (concat (concat bs3_5_0 bs3_5_96) (concat bs3_5_192 (concat bs3_5_288 bs3_5_384))) (concat (concat bs3_5_480 (concat bs3_5_576 bs3_5_672)) (concat bs3_5_768 (concat bs3_5_864 bs3_5_960))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 48 := block_range (n:=48) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 48 := bs3_6_0
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
theorem bs4_3_0 : Interval s4Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 25 := bs4_3_0
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
theorem bs4_4_480 : Interval s4Atlas 4 480 59 := block_range (n:=59) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 539 := (concat (concat bs4_4_0 (concat bs4_4_96 bs4_4_192)) (concat bs4_4_288 (concat bs4_4_384 bs4_4_480)))
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
theorem bs4_5_576 : Interval s4Atlas 5 576 88 := block_range (n:=88) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 664 := (concat (concat bs4_5_0 (concat bs4_5_96 bs4_5_192)) (concat (concat bs4_5_288 bs4_5_384) (concat bs4_5_480 bs4_5_576)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 40 := block_range (n:=40) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 40 := bs4_6_0
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
theorem bs5_2_0 : Interval s5Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 4 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 25 := bs5_3_0
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
theorem bs5_4_480 : Interval s5Atlas 4 480 59 := block_range (n:=59) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 539 := (concat (concat bs5_4_0 (concat bs5_4_96 bs5_4_192)) (concat bs5_4_288 (concat bs5_4_384 bs5_4_480)))
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
theorem bs5_5_576 : Interval s5Atlas 5 576 88 := block_range (n:=88) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 664 := (concat (concat bs5_5_0 (concat bs5_5_96 bs5_5_192)) (concat (concat bs5_5_288 bs5_5_384) (concat bs5_5_480 bs5_5_576)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 40 := block_range (n:=40) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 40 := bs5_6_0
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
theorem bq4_2_0 : Interval q4Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq4_2 : Interval q4Atlas 2 0 4 := bq4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_3_0 : Interval q4Atlas 3 0 16 := block_range (n:=16) (by decide +kernel)
theorem allq4_3 : Interval q4Atlas 3 0 16 := bq4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_4_0 : Interval q4Atlas 4 0 13 := block_range (n:=13) (by decide +kernel)
theorem allq4_4 : Interval q4Atlas 4 0 13 := bq4_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_5_0 : Interval q4Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq4_5 : Interval q4Atlas 5 0 1 := bq4_5_0
theorem allq4 : ∀ k ≤ 5, ∀ i < count q4Atlas k, checkRow q4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq4_2 i (by omega) hi
  · exact allq4_3 i (by omega) hi
  · exact allq4_4 i (by omega) hi
  · exact allq4_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq6_2_0 : Interval q6Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq6_2 : Interval q6Atlas 2 0 4 := bq6_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq6_3_0 : Interval q6Atlas 3 0 16 := block_range (n:=16) (by decide +kernel)
theorem allq6_3 : Interval q6Atlas 3 0 16 := bq6_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq6_4_0 : Interval q6Atlas 4 0 13 := block_range (n:=13) (by decide +kernel)
theorem allq6_4 : Interval q6Atlas 4 0 13 := bq6_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq6_5_0 : Interval q6Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq6_5 : Interval q6Atlas 5 0 1 := bq6_5_0
theorem allq6 : ∀ k ≤ 5, ∀ i < count q6Atlas k, checkRow q6Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq6_2 i (by omega) hi
  · exact allq6_3 i (by omega) hi
  · exact allq6_4 i (by omega) hi
  · exact allq6_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq7_2_0 : Interval q7Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq7_2 : Interval q7Atlas 2 0 3 := bq7_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq7_3_0 : Interval q7Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq7_3 : Interval q7Atlas 3 0 6 := bq7_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq7_4_0 : Interval q7Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq7_4 : Interval q7Atlas 4 0 1 := bq7_4_0
theorem allq7 : ∀ k ≤ 4, ∀ i < count q7Atlas k, checkRow q7Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq7_2 i (by omega) hi
  · exact allq7_3 i (by omega) hi
  · exact allq7_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq8_2_0 : Interval q8Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq8_2 : Interval q8Atlas 2 0 3 := bq8_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq8_3_0 : Interval q8Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq8_3 : Interval q8Atlas 3 0 6 := bq8_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq8_4_0 : Interval q8Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq8_4 : Interval q8Atlas 4 0 1 := bq8_4_0
theorem allq8 : ∀ k ≤ 4, ∀ i < count q8Atlas k, checkRow q8Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq8_2 i (by omega) hi
  · exact allq8_3 i (by omega) hi
  · exact allq8_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq9_2_0 : Interval q9Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq9_2 : Interval q9Atlas 2 0 3 := bq9_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq9_3_0 : Interval q9Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq9_3 : Interval q9Atlas 3 0 6 := bq9_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq9_4_0 : Interval q9Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq9_4 : Interval q9Atlas 4 0 1 := bq9_4_0
theorem allq9 : ∀ k ≤ 4, ∀ i < count q9Atlas k, checkRow q9Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq9_2 i (by omega) hi
  · exact allq9_3 i (by omega) hi
  · exact allq9_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq10_2_0 : Interval q10Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq10_2 : Interval q10Atlas 2 0 4 := bq10_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq10_3_0 : Interval q10Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq10_3 : Interval q10Atlas 3 0 6 := bq10_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq10_4_0 : Interval q10Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq10_4 : Interval q10Atlas 4 0 1 := bq10_4_0
theorem allq10 : ∀ k ≤ 4, ∀ i < count q10Atlas k, checkRow q10Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq10_2 i (by omega) hi
  · exact allq10_3 i (by omega) hi
  · exact allq10_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq11_2_0 : Interval q11Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq11_2 : Interval q11Atlas 2 0 4 := bq11_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq11_3_0 : Interval q11Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq11_3 : Interval q11Atlas 3 0 6 := bq11_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq11_4_0 : Interval q11Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq11_4 : Interval q11Atlas 4 0 1 := bq11_4_0
theorem allq11 : ∀ k ≤ 4, ∀ i < count q11Atlas k, checkRow q11Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq11_2 i (by omega) hi
  · exact allq11_3 i (by omega) hi
  · exact allq11_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq12_2_0 : Interval q12Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq12_2 : Interval q12Atlas 2 0 4 := bq12_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq12_3_0 : Interval q12Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq12_3 : Interval q12Atlas 3 0 6 := bq12_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq12_4_0 : Interval q12Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq12_4 : Interval q12Atlas 4 0 1 := bq12_4_0
theorem allq12 : ∀ k ≤ 4, ∀ i < count q12Atlas k, checkRow q12Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq12_2 i (by omega) hi
  · exact allq12_3 i (by omega) hi
  · exact allq12_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq13_2_0 : Interval q13Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq13_2 : Interval q13Atlas 2 0 4 := bq13_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq13_3_0 : Interval q13Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq13_3 : Interval q13Atlas 3 0 6 := bq13_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq13_4_0 : Interval q13Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq13_4 : Interval q13Atlas 4 0 1 := bq13_4_0
theorem allq13 : ∀ k ≤ 4, ∀ i < count q13Atlas k, checkRow q13Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq13_2 i (by omega) hi
  · exact allq13_3 i (by omega) hi
  · exact allq13_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq14_2_0 : Interval q14Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq14_2 : Interval q14Atlas 2 0 4 := bq14_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq14_3_0 : Interval q14Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq14_3 : Interval q14Atlas 3 0 6 := bq14_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq14_4_0 : Interval q14Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq14_4 : Interval q14Atlas 4 0 1 := bq14_4_0
theorem allq14 : ∀ k ≤ 4, ∀ i < count q14Atlas k, checkRow q14Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq14_2 i (by omega) hi
  · exact allq14_3 i (by omega) hi
  · exact allq14_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq15_2_0 : Interval q15Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq15_2 : Interval q15Atlas 2 0 4 := bq15_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq15_3_0 : Interval q15Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq15_3 : Interval q15Atlas 3 0 6 := bq15_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq15_4_0 : Interval q15Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq15_4 : Interval q15Atlas 4 0 1 := bq15_4_0
theorem allq15 : ∀ k ≤ 4, ∀ i < count q15Atlas k, checkRow q15Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq15_2 i (by omega) hi
  · exact allq15_3 i (by omega) hi
  · exact allq15_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq16_2_0 : Interval q16Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq16_2 : Interval q16Atlas 2 0 4 := bq16_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq16_3_0 : Interval q16Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq16_3 : Interval q16Atlas 3 0 6 := bq16_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq16_4_0 : Interval q16Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq16_4 : Interval q16Atlas 4 0 1 := bq16_4_0
theorem allq16 : ∀ k ≤ 4, ∀ i < count q16Atlas k, checkRow q16Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq16_2 i (by omega) hi
  · exact allq16_3 i (by omega) hi
  · exact allq16_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq17_2_0 : Interval q17Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq17_2 : Interval q17Atlas 2 0 4 := bq17_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq17_3_0 : Interval q17Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq17_3 : Interval q17Atlas 3 0 6 := bq17_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq17_4_0 : Interval q17Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq17_4 : Interval q17Atlas 4 0 1 := bq17_4_0
theorem allq17 : ∀ k ≤ 4, ∀ i < count q17Atlas k, checkRow q17Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq17_2 i (by omega) hi
  · exact allq17_3 i (by omega) hi
  · exact allq17_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq18_3_0 : Interval q18Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq18_3 : Interval q18Atlas 3 0 1 := bq18_3_0
theorem allq18 : ∀ k ≤ 3, ∀ i < count q18Atlas k, checkRow q18Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq18_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq19_2_0 : Interval q19Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq19_2 : Interval q19Atlas 2 0 1 := bq19_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq19_3_0 : Interval q19Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allq19_3 : Interval q19Atlas 3 0 5 := bq19_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq19_4_0 : Interval q19Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq19_4 : Interval q19Atlas 4 0 1 := bq19_4_0
theorem allq19 : ∀ k ≤ 4, ∀ i < count q19Atlas k, checkRow q19Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq19_2 i (by omega) hi
  · exact allq19_3 i (by omega) hi
  · exact allq19_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq20_2_0 : Interval q20Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq20_2 : Interval q20Atlas 2 0 1 := bq20_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq20_3_0 : Interval q20Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allq20_3 : Interval q20Atlas 3 0 5 := bq20_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq20_4_0 : Interval q20Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq20_4 : Interval q20Atlas 4 0 1 := bq20_4_0
theorem allq20 : ∀ k ≤ 4, ∀ i < count q20Atlas k, checkRow q20Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq20_2 i (by omega) hi
  · exact allq20_3 i (by omega) hi
  · exact allq20_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq21_3_0 : Interval q21Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq21_3 : Interval q21Atlas 3 0 1 := bq21_3_0
theorem allq21 : ∀ k ≤ 3, ∀ i < count q21Atlas k, checkRow q21Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq21_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq22_3_0 : Interval q22Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq22_3 : Interval q22Atlas 3 0 1 := bq22_3_0
theorem allq22 : ∀ k ≤ 3, ∀ i < count q22Atlas k, checkRow q22Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq22_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq23_3_0 : Interval q23Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq23_3 : Interval q23Atlas 3 0 1 := bq23_3_0
theorem allq23 : ∀ k ≤ 3, ∀ i < count q23Atlas k, checkRow q23Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq23_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq24_3_0 : Interval q24Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq24_3 : Interval q24Atlas 3 0 1 := bq24_3_0
theorem allq24 : ∀ k ≤ 3, ∀ i < count q24Atlas k, checkRow q24Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq24_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq25_3_0 : Interval q25Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq25_3 : Interval q25Atlas 3 0 1 := bq25_3_0
theorem allq25 : ∀ k ≤ 3, ∀ i < count q25Atlas k, checkRow q25Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq25_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_96 : Interval gbAtlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_192 : Interval gbAtlas 4 192 26 := block_range (n:=26) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 218 := (concat bgb_4_0 (concat bgb_4_96 bgb_4_192))
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
theorem bgb_5_960 : Interval gbAtlas 5 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1056 : Interval gbAtlas 5 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1152 : Interval gbAtlas 5 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1248 : Interval gbAtlas 5 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1344 : Interval gbAtlas 5 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1440 : Interval gbAtlas 5 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1536 : Interval gbAtlas 5 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1632 : Interval gbAtlas 5 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1728 : Interval gbAtlas 5 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1824 : Interval gbAtlas 5 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1920 : Interval gbAtlas 5 1920 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2016 : Interval gbAtlas 5 2016 42 := block_range (n:=42) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2058 := (concat (concat (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 (concat bgb_5_288 bgb_5_384))) (concat (concat bgb_5_480 (concat bgb_5_576 bgb_5_672)) (concat bgb_5_768 (concat bgb_5_864 bgb_5_960)))) (concat (concat (concat bgb_5_1056 bgb_5_1152) (concat bgb_5_1248 (concat bgb_5_1344 bgb_5_1440))) (concat (concat bgb_5_1536 (concat bgb_5_1632 bgb_5_1728)) (concat bgb_5_1824 (concat bgb_5_1920 bgb_5_2016)))))
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
theorem bgb_6_2304 : Interval gbAtlas 6 2304 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2400 : Interval gbAtlas 6 2400 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2496 : Interval gbAtlas 6 2496 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2592 : Interval gbAtlas 6 2592 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2688 : Interval gbAtlas 6 2688 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2784 : Interval gbAtlas 6 2784 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2880 : Interval gbAtlas 6 2880 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2976 : Interval gbAtlas 6 2976 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3072 : Interval gbAtlas 6 3072 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3168 : Interval gbAtlas 6 3168 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3264 : Interval gbAtlas 6 3264 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3360 : Interval gbAtlas 6 3360 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3456 : Interval gbAtlas 6 3456 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3552 : Interval gbAtlas 6 3552 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3648 : Interval gbAtlas 6 3648 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3744 : Interval gbAtlas 6 3744 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3840 : Interval gbAtlas 6 3840 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3936 : Interval gbAtlas 6 3936 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4032 : Interval gbAtlas 6 4032 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4128 : Interval gbAtlas 6 4128 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4224 : Interval gbAtlas 6 4224 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4320 : Interval gbAtlas 6 4320 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4416 : Interval gbAtlas 6 4416 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4512 : Interval gbAtlas 6 4512 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4608 : Interval gbAtlas 6 4608 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4704 : Interval gbAtlas 6 4704 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4800 : Interval gbAtlas 6 4800 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4896 : Interval gbAtlas 6 4896 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4992 : Interval gbAtlas 6 4992 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5088 : Interval gbAtlas 6 5088 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5184 : Interval gbAtlas 6 5184 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5280 : Interval gbAtlas 6 5280 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5376 : Interval gbAtlas 6 5376 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5472 : Interval gbAtlas 6 5472 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5568 : Interval gbAtlas 6 5568 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5664 : Interval gbAtlas 6 5664 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5760 : Interval gbAtlas 6 5760 13 := block_range (n:=13) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 5773 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_96 bgb_6_192)) (concat (concat bgb_6_288 bgb_6_384) (concat bgb_6_480 bgb_6_576))) (concat (concat (concat bgb_6_672 bgb_6_768) (concat bgb_6_864 bgb_6_960)) (concat (concat bgb_6_1056 bgb_6_1152) (concat bgb_6_1248 bgb_6_1344)))) (concat (concat (concat bgb_6_1440 (concat bgb_6_1536 bgb_6_1632)) (concat (concat bgb_6_1728 bgb_6_1824) (concat bgb_6_1920 bgb_6_2016))) (concat (concat (concat bgb_6_2112 bgb_6_2208) (concat bgb_6_2304 bgb_6_2400)) (concat (concat bgb_6_2496 bgb_6_2592) (concat bgb_6_2688 bgb_6_2784))))) (concat (concat (concat (concat bgb_6_2880 (concat bgb_6_2976 bgb_6_3072)) (concat (concat bgb_6_3168 bgb_6_3264) (concat bgb_6_3360 bgb_6_3456))) (concat (concat (concat bgb_6_3552 bgb_6_3648) (concat bgb_6_3744 bgb_6_3840)) (concat (concat bgb_6_3936 bgb_6_4032) (concat bgb_6_4128 bgb_6_4224)))) (concat (concat (concat (concat bgb_6_4320 bgb_6_4416) (concat bgb_6_4512 bgb_6_4608)) (concat (concat bgb_6_4704 bgb_6_4800) (concat bgb_6_4896 bgb_6_4992))) (concat (concat (concat bgb_6_5088 bgb_6_5184) (concat bgb_6_5280 bgb_6_5376)) (concat (concat bgb_6_5472 bgb_6_5568) (concat bgb_6_5664 bgb_6_5760))))))
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
theorem bgb_7_1536 : Interval gbAtlas 7 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1632 : Interval gbAtlas 7 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1728 : Interval gbAtlas 7 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1824 : Interval gbAtlas 7 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1920 : Interval gbAtlas 7 1920 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2016 : Interval gbAtlas 7 2016 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2112 : Interval gbAtlas 7 2112 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2208 : Interval gbAtlas 7 2208 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2304 : Interval gbAtlas 7 2304 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2400 : Interval gbAtlas 7 2400 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2496 : Interval gbAtlas 7 2496 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2592 : Interval gbAtlas 7 2592 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2688 : Interval gbAtlas 7 2688 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2784 : Interval gbAtlas 7 2784 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2880 : Interval gbAtlas 7 2880 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2976 : Interval gbAtlas 7 2976 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_3072 : Interval gbAtlas 7 3072 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_3168 : Interval gbAtlas 7 3168 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_3264 : Interval gbAtlas 7 3264 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_3360 : Interval gbAtlas 7 3360 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_3456 : Interval gbAtlas 7 3456 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_3552 : Interval gbAtlas 7 3552 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_3648 : Interval gbAtlas 7 3648 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_3744 : Interval gbAtlas 7 3744 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_3840 : Interval gbAtlas 7 3840 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_3936 : Interval gbAtlas 7 3936 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_4032 : Interval gbAtlas 7 4032 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_4128 : Interval gbAtlas 7 4128 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_4224 : Interval gbAtlas 7 4224 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_4320 : Interval gbAtlas 7 4320 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 4347 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_96) (concat bgb_7_192 (concat bgb_7_288 bgb_7_384))) (concat (concat bgb_7_480 (concat bgb_7_576 bgb_7_672)) (concat bgb_7_768 (concat bgb_7_864 bgb_7_960)))) (concat (concat (concat bgb_7_1056 (concat bgb_7_1152 bgb_7_1248)) (concat bgb_7_1344 (concat bgb_7_1440 bgb_7_1536))) (concat (concat bgb_7_1632 (concat bgb_7_1728 bgb_7_1824)) (concat bgb_7_1920 (concat bgb_7_2016 bgb_7_2112))))) (concat (concat (concat (concat bgb_7_2208 bgb_7_2304) (concat bgb_7_2400 (concat bgb_7_2496 bgb_7_2592))) (concat (concat bgb_7_2688 (concat bgb_7_2784 bgb_7_2880)) (concat bgb_7_2976 (concat bgb_7_3072 bgb_7_3168)))) (concat (concat (concat bgb_7_3264 (concat bgb_7_3360 bgb_7_3456)) (concat bgb_7_3552 (concat bgb_7_3648 bgb_7_3744))) (concat (concat bgb_7_3840 (concat bgb_7_3936 bgb_7_4032)) (concat bgb_7_4128 (concat bgb_7_4224 bgb_7_4320))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_96 : Interval gbAtlas 8 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_192 : Interval gbAtlas 8 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_288 : Interval gbAtlas 8 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_384 : Interval gbAtlas 8 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_480 : Interval gbAtlas 8 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_576 : Interval gbAtlas 8 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_672 : Interval gbAtlas 8 672 66 := block_range (n:=66) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 738 := (concat (concat (concat bgb_8_0 bgb_8_96) (concat bgb_8_192 bgb_8_288)) (concat (concat bgb_8_384 bgb_8_480) (concat bgb_8_576 bgb_8_672)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_9_0 : Interval gbAtlas 9 0 26 := block_range (n:=26) (by decide +kernel)
theorem allgb_9 : Interval gbAtlas 9 0 26 := bgb_9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_10_0 : Interval gbAtlas 10 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_10 : Interval gbAtlas 10 0 1 := bgb_10_0
theorem allgb : ∀ k ≤ 10, ∀ i < count gbAtlas k, checkRow gbAtlas k i = true := by
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
  · exact allgb_10 i (by omega) hi
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
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 17, 21),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 8 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 5, 21)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq4 (cert : Complete q4Atlas) : Lower true (roots q4Atlas) (target q4Atlas) 6 := by
  have ready : Ready q4Atlas (asRow q4Pos) (asRow q4Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq6 (cert : Complete q6Atlas) : Lower true (roots q6Atlas) (target q6Atlas) 6 := by
  have ready : Ready q6Atlas (asRow q6Pos) (asRow q6Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq7 (cert : Complete q7Atlas) : Lower true (roots q7Atlas) (target q7Atlas) 5 := by
  have ready : Ready q7Atlas (asRow q7Pos) (asRow q7Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 2 zero, 16, 20),(inputs.getD 3 zero, 0, 8),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq8 (cert : Complete q8Atlas) : Lower true (roots q8Atlas) (target q8Atlas) 5 := by
  have ready : Ready q8Atlas (asRow q8Pos) (asRow q8Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 0, 2),(inputs.getD 2 zero, 16, 20),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq9 (cert : Complete q9Atlas) : Lower true (roots q9Atlas) (target q9Atlas) 5 := by
  have ready : Ready q9Atlas (asRow q9Pos) (asRow q9Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 20, 21),(inputs.getD 2 zero, 17, 21),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq10 (cert : Complete q10Atlas) : Lower true (roots q10Atlas) (target q10Atlas) 5 := by
  have ready : Ready q10Atlas (asRow q10Pos) (asRow q10Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq11 (cert : Complete q11Atlas) : Lower true (roots q11Atlas) (target q11Atlas) 5 := by
  have ready : Ready q11Atlas (asRow q11Pos) (asRow q11Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq12 (cert : Complete q12Atlas) : Lower true (roots q12Atlas) (target q12Atlas) 5 := by
  have ready : Ready q12Atlas (asRow q12Pos) (asRow q12Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 10, 26)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq13 (cert : Complete q13Atlas) : Lower true (roots q13Atlas) (target q13Atlas) 5 := by
  have ready : Ready q13Atlas (asRow q13Pos) (asRow q13Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq14 (cert : Complete q14Atlas) : Lower true (roots q14Atlas) (target q14Atlas) 5 := by
  have ready : Ready q14Atlas (asRow q14Pos) (asRow q14Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq15 (cert : Complete q15Atlas) : Lower true (roots q15Atlas) (target q15Atlas) 5 := by
  have ready : Ready q15Atlas (asRow q15Pos) (asRow q15Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq16 (cert : Complete q16Atlas) : Lower true (roots q16Atlas) (target q16Atlas) 5 := by
  have ready : Ready q16Atlas (asRow q16Pos) (asRow q16Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 5, 21)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq17 (cert : Complete q17Atlas) : Lower true (roots q17Atlas) (target q17Atlas) 5 := by
  have ready : Ready q17Atlas (asRow q17Pos) (asRow q17Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq18 (cert : Complete q18Atlas) : Lower true (roots q18Atlas) (target q18Atlas) 4 := by
  have ready : Ready q18Atlas (asRow q18Pos) (asRow q18Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq19 (cert : Complete q19Atlas) : Lower true (roots q19Atlas) (target q19Atlas) 5 := by
  have ready : Ready q19Atlas (asRow q19Pos) (asRow q19Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq20 (cert : Complete q20Atlas) : Lower true (roots q20Atlas) (target q20Atlas) 5 := by
  have ready : Ready q20Atlas (asRow q20Pos) (asRow q20Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq21 (cert : Complete q21Atlas) : Lower true (roots q21Atlas) (target q21Atlas) 4 := by
  have ready : Ready q21Atlas (asRow q21Pos) (asRow q21Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 2 zero, 16, 20),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq22 (cert : Complete q22Atlas) : Lower true (roots q22Atlas) (target q22Atlas) 4 := by
  have ready : Ready q22Atlas (asRow q22Pos) (asRow q22Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq23 (cert : Complete q23Atlas) : Lower true (roots q23Atlas) (target q23Atlas) 4 := by
  have ready : Ready q23Atlas (asRow q23Pos) (asRow q23Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq24 (cert : Complete q24Atlas) : Lower true (roots q24Atlas) (target q24Atlas) 4 := by
  have ready : Ready q24Atlas (asRow q24Pos) (asRow q24Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq25 (cert : Complete q25Atlas) : Lower true (roots q25Atlas) (target q25Atlas) 4 := by
  have ready : Ready q25Atlas (asRow q25Pos) (asRow q25Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) (pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p) : Lower true (roots gbAtlas) (target gbAtlas) 11 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact pv
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeee8eee8eac8eeeaeee8eee8eac8eeeaeee8eee8eac8eeeaeee8eee8eac8eeeaeee8eee8eac8eeeaeee8eee8eac8eeeaeee8eee8eac8eeeaeee8eee8eac8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certq4 : Complete q4Atlas) (certq6 : Complete q6Atlas) (certq7 : Complete q7Atlas) (certq8 : Complete q8Atlas) (certq9 : Complete q9Atlas) (certq10 : Complete q10Atlas) (certq11 : Complete q11Atlas) (certq12 : Complete q12Atlas) (certq13 : Complete q13Atlas) (certq14 : Complete q14Atlas) (certq15 : Complete q15Atlas) (certq16 : Complete q16Atlas) (certq17 : Complete q17Atlas) (certq18 : Complete q18Atlas) (certq19 : Complete q19Atlas) (certq20 : Complete q20Atlas) (certq21 : Complete q21Atlas) (certq22 : Complete q22Atlas) (certq23 : Complete q23Atlas) (certq24 : Complete q24Atlas) (certq25 : Complete q25Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 11 := by
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
  have q0 : Slice true (roots gbAtlas) (target gbAtlas) (0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333 : Sig) 6 :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have q1 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f : Sig) 8 :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have q2 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff : Sig) 8 :=
    slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
  have q3 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff : Sig) 8 :=
    slice_correct (ms:=fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds4 certs4)
  have q4 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000 : Sig) 6 :=
    slice_correct (ms:=fixRows 0 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq4 certq4)
  have q5 : Slice true (roots gbAtlas) (target gbAtlas) (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff : Sig) 8 :=
    slice_correct (ms:=fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds5 certs5)
  have q6 : Slice true (roots gbAtlas) (target gbAtlas) (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000 : Sig) 6 :=
    slice_correct (ms:=fixRows 0 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq6 certq6)
  have q7 : Slice true (roots gbAtlas) (target gbAtlas) (0x22222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222 : Sig) 5 :=
    slice_correct (ms:=fixRows 2 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq7 certq7)
  have q8 : Slice true (roots gbAtlas) (target gbAtlas) (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa : Sig) 5 :=
    slice_correct (ms:=fixRows 8 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq8 certq8)
  have q9 : Slice true (roots gbAtlas) (target gbAtlas) (0x330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033 : Sig) 5 :=
    slice_correct (ms:=fixRows 10 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq9 certq9)
  have q10 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f : Sig) 5 :=
    slice_correct (ms:=fixRows 20 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq10 certq10)
  have q11 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000 : Sig) 5 :=
    slice_correct (ms:=fixRows 4 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq11 certq11)
  have q12 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f : Sig) 5 :=
    slice_correct (ms:=fixRows 36 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq12 certq12)
  have q13 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000 : Sig) 5 :=
    slice_correct (ms:=fixRows 4 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq13 certq13)
  have q14 : Slice true (roots gbAtlas) (target gbAtlas) (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff : Sig) 5 :=
    slice_correct (ms:=fixRows 24 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq14 certq14)
  have q15 : Slice true (roots gbAtlas) (target gbAtlas) (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000 : Sig) 5 :=
    slice_correct (ms:=fixRows 8 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq15 certq15)
  have q16 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff : Sig) 5 :=
    slice_correct (ms:=fixRows 40 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq16 certq16)
  have q17 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000 : Sig) 5 :=
    slice_correct (ms:=fixRows 8 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq17 certq17)
  have q18 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff : Sig) 4 :=
    slice_correct (ms:=fixRows 48 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq18 certq18)
  have q19 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff00000000 : Sig) 5 :=
    slice_correct (ms:=fixRows 16 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq19 certq19)
  have q20 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000 : Sig) 5 :=
    slice_correct (ms:=fixRows 32 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq20 certq20)
  have q21 : Slice true (roots gbAtlas) (target gbAtlas) (0x220022002200220022002200220022002200220022002200220022002200220022002200220022002200220022002200220022002200220022002200220022 : Sig) 4 :=
    slice_correct (ms:=fixRows 10 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq21 certq21)
  have q22 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f00000000 : Sig) 4 :=
    slice_correct (ms:=fixRows 20 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq22 certq22)
  have q23 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000 : Sig) 4 :=
    slice_correct (ms:=fixRows 36 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq23 certq23)
  have q24 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000 : Sig) 4 :=
    slice_correct (ms:=fixRows 24 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq24 certq24)
  have q25 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000000000ff0000 : Sig) 4 :=
    slice_correct (ms:=fixRows 40 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq25 certq25)
  have pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p :=
    List.forall_iff_forall_mem.1 (show List.Forall (fun p => ValidPool true (roots gbAtlas) (target gbAtlas) p) gbPools from ⟨build_valid q0 [] rfl, build_valid q1 [] rfl, build_valid q2 [] rfl, build_valid q3 [] rfl, build_valid q4 [] rfl, build_valid q5 [] rfl, build_valid q6 [] rfl, build_valid q7 [] rfl, build_valid q8 [] rfl, build_valid q9 [] rfl, build_valid q10 [] rfl, build_valid q11 [] rfl, build_valid q12 [] rfl, build_valid q13 [] rfl, build_valid q14 [] rfl, build_valid q15 [] rfl, build_valid q16 [] rfl, build_valid q17 [] rfl, build_valid q18 [] rfl, build_valid q19 [] rfl, build_valid q20 [] rfl, build_valid q21 [] rfl, build_valid q22 [] rfl, build_valid q23 [] rfl, build_valid q24 [] rfl, build_valid q25 [] rfl⟩)
  have low := boundgb certgb allCuts pv
  have lift := lift_ok (u:=true) (ms:=fixRows 0 0) (raw:=fullRoots) (T:=fullWord) (xs:=[]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 0 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008373992 * 2 ^ 32 + 4008241864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
theorem binaryLower (low : Lower true fullRoots fullWord 11)
    (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x)=posted x) : 11 ≤ gs.countP (fun g => !isNot g) := by
  have pg : proper fullWord := proper_of _ (by decide +kernel)
  have out := getRep (u:=true) (execute gs fullRoots) o
  rw [eval6 gs o legal h] at out
  unfold PEqualNP.Outside.L_meta_36783.Model.Repr at out
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

def mono : List Gate := [⟨.or,[4,5]⟩,⟨.or,[1,3]⟩,⟨.or,[0,6]⟩,⟨.and,[3,8]⟩,⟨.and,[4,5]⟩,⟨.or,[7,10]⟩,⟨.or,[2,9]⟩,⟨.and,[0,11]⟩,⟨.and,[0,6]⟩,⟨.or,[1,14]⟩,⟨.and,[12,15]⟩,⟨.or,[13,16]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,17⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 11) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373992 * 2 ^ 32 + 4008241864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373992 * 2 ^ 32 + 4008241864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
    refine ⟨⟨mono, 17⟩, monoShape, ?_, fun x => monoEval x⟩
    change mono.length ≤ s
    have hm : mono.length = 12 := rfl
    change gs.length ≤ s at hsize
    omega
end PEqualNP.Outside.L_meta_36783

open PEqualNP.Outside.L_meta_36783 in
theorem PEqualNP.Outside.L_meta_36783 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373992 * 2 ^ 32 + 4008241864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373992 * 2 ^ 32 + 4008241864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allq4 allq6 allq7 allq8 allq9 allq10 allq11 allq12 allq13 allq14 allq15 allq16 allq17 allq18 allq19 allq20 allq21 allq22 allq23 allq24 allq25 allgb)
