import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, children closed at the parent by
-- restriction pools (closeChild of the model), and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36589.Model
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


end PEqualNP.Outside.L_meta_36589.Model

namespace PEqualNP.Outside.L_meta_36589
open PEqualNP.Outside.L_meta_36589.Model
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

def SBf (j : Nat) : Nat := [5, 3, 5, 7, 7, 9].getD j 0

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

end PEqualNP.Outside.L_meta_36589

namespace PEqualNP.Outside.L_meta_36589
open PEqualNP.Outside.L_meta_36589.Model
def s0K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x18000036105c30e82178c37107610
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x20003808010d03004320c020
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (i*4) 4
  | 3 => packedAt s0K3 (i*15) 15
  | 2 => packedAt s0K2 (i*26) 26
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt s0K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/9+packedAt s0K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt s0K2 (78+(h % 8)*2) 2) % 3)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffbf0fffc3fe3f
  | 3 => 0xffffffffffffffffffffffffffdff0fffc3fc7
  | 4 => 0xefff0fffc3f8
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffff012222c444db
  | 2 => 0xffffffffffffffffffffffffff42e44562aa2d
  | 3 => 0x244e89aa3346
  | 4 => 0x1888ee3323b0
  | _ => 0
def s0Atlas : Atlas := ⟨4,rawDecor 30 s0Pos s0Neg, 0xccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000, s0N, s0R, (fun _ _ => 0), s0I, []⟩
end PEqualNP.Outside.L_meta_36589
namespace PEqualNP.Outside.L_meta_36589
open PEqualNP.Outside.L_meta_36589.Model
def s1K2 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 2 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s1K2 (i*4) 4
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 2 => 2*((h/1+packedAt s1K2 (4+(h % 1)*1) 1) % 1)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffd7c3c7f8783e67
  | 3 => 0xffffffffffffffffffffffffe7fc07ff803f87
  | 5 => 0x7bfff8ffffc3f8
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffff804880188984ab
  | 2 => 0xffffffffffffffffffffffffa8b92a6c52aa65
  | 3 => 0x1913b4b5453386
  | 5 => 0x62226c6662350
  | _ => 0
def s1Atlas : Atlas := ⟨2,rawDecor 45 s1Pos s1Neg, 0xaaaaaaaaa000a000aaaaaaaaa000a000aaaaaaaaa000a000aaaaaaaaa000a000aaaaaaaaa000a000aaaaaaaaa000a000aaaaaaaaa000a000aaaaaaaaa000a000, s1N, s1R, (fun _ _ => 0), s1I, []⟩
end PEqualNP.Outside.L_meta_36589
namespace PEqualNP.Outside.L_meta_36589
open PEqualNP.Outside.L_meta_36589.Model
def s2K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xd431
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
  | 0 => 0xffffffffffe03ff81fffffffffffc03f1fffc7
  | 1 => 0x1fc07f00fffffffe0f81f01f80fffffe4ccff
  | 3 => 0x1fff8000fffc0ffff001ffe000fffc0f8f0f8
  | 4 => 0xfe0000000fffffffffffe000000fffffff00ff
  | 5 => 0xfffffffff00000fffffffffffff00000ffff00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xc2450a1402382180318a31a28e2c5150955c3
  | 1 => 0x5489314656449469606a0d49b125596664cc5d
  | 3 => 0xa930a26b6a890ebaad0496dca249ad94b8f0e8
  | 4 => 0x31a2c58d8d1228d4d6b6c091048e3638df00b6
  | 5 => 0xc1c3060e0e1c30e718c718e1c7003820f6aa00
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 59 s2Pos s2Neg, 0xeeaaaaaacc880000eeaaaaaacc880000eeaaaaaacc880000eeaaaaaacc880000eeaaaaaacc880000eeaaaaaacc880000eeaaaaaacc880000eeaaaaaacc880000, s2N, s2R, (fun _ _ => 0), s2I, []⟩
end PEqualNP.Outside.L_meta_36589
namespace PEqualNP.Outside.L_meta_36589
open PEqualNP.Outside.L_meta_36589.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x8e104000405042600382a83017801fd31fd32fd43fc43ff43fe30fc10fc42bc40ff40fc40fd20fc31fe31ee21fe10fe41fe40fc41fd10ff21fd30fe20fc20ff32ec21fe42fe21fc32ff31ff10fd40fe32be40ff20de31fe43dc31fc21ff42fc30fd41ff41fd21fd42ff30
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x4c4c30d02e8a000ce929600ac10c80c4900140f19c01c00172650c06011c19208003dd547429f2a043d431042dca4184f553109f2a0636c524427aa9905754f21ba28a656e51086bea6a0f38c4219eaa661ac21102bca7a15e14141afa9a41b840043aa8218e70c640d6a90816f52506eaa3a1f90c421b6a90619e540c67aa810f994421bb28e85ae21902dea498cf15120e618c433e50902bca6105754f42aea98815e53102baa7a0db94840af29e83e731086eaa2206e10310b7296875e510c73862204fd5110ba28a41e641086dea4885754e10ea18e439d540c67aa818cf15130b729683ad540867ca9885b54840e6188436e51886d8a4a0f10c421eb288639e31102b8a690cfd5130ba28a615c53482dca598f50c421aea98415f53443c843085b54b439f2a6616e528436ca2205b54a10b6a96835e53c87ac8218dd94743afa9a43e4210435ca4206b88440dd280816d52cc73aa6204f95320bba8a61ae54086bca318ddd4532cf18c815e53842d8a4985d944409e2a2215c53507ca8210eb08640bba8a41cd320cadea498750c610bda8283ce318867ea8906d544409f280815c53442d8a498e794c40
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x400000200000010c000000b0100610000c954951103a02110010e40c440042e06050421e155031086d06050431b118d41086c6618c421e15903108746520c6108b59421103465308610e199031086c4614c832c554d51102c46250431e195031086a5640c42199185520c315540c42187594311038431086409518553083843108440
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0xca0aea1884220605650c42110282bacc818843215da540c421
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 117
  | 3 => 24
  | 2 => 4
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
  | 5 => 2*((h/22+packedAt s3K5 (736+(h % 22)*6) 6) % 46)
  | 4 => 2*((h/39+packedAt s3K4 (3159+(h % 39)*7) 7) % 117)
  | 3 => 2*((h/29+packedAt s3K3 (912+(h % 29)*5) 5) % 24)
  | 2 => 2*((h/8+packedAt s3K2 (196+(h % 8)*2) 2) % 4)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xfffffffff01fffe07ffffffffffc07fe3ffe3f
  | 1 => 0x7f01fc07ffffffff83e07c0f80ffffffc933ff
  | 2 => 0x7ffe0007ffe07ffffc007ff000fff83ff1c3c7
  | 4 => 0x80000007ffff81ffffff800000ffffc1fe03f8
  | 5 => 0xfffffff8000001ffffffffffff000001fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x914284011c104200c628c508e2c425212561b
  | 1 => 0x224c518b224a28c581a8350d12558ca4c930ed
  | 2 => 0x4c289ad54487516ab4125b64249ad23971c346
  | 4 => 0x68b1636689141db35adb024848e36711be03b0
  | 5 => 0x70c183870e1861dc631c638e70038421eda800
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeaeaaaaac8c88080eaeaaaaac8c88080eaeaaaaac8c88080eaeaaaaac8c88080eaeaaaaac8c88080eaeaaaaac8c88080eaeaaaaac8c88080eaeaaaaac8c88080, s3N, s3R, (fun _ _ => 0), s3I, []⟩
end PEqualNP.Outside.L_meta_36589
namespace PEqualNP.Outside.L_meta_36589
open PEqualNP.Outside.L_meta_36589.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x3c02c000402648a0070030581561822c3ff30fc32be40fd40ff20fe42fe31fe43fe30fc21fd21fc42ff31fd31fe32fc31ff32dc32ff42fc40fd32bc40f421fc10ff40ff41fd30fc43fd20fc30fe10fe41fc20fd10fd43fd41fd42ff21f721fe20ff43fe40fc41ff10fe21de32
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xc815060010400600010c05280025461c0600007200098e040858b0a4c5802f8c106004960200a8a57d4d10daaa043b42110278a8884f55320b6a9683d632c876aa2205754e20f2a1043e4210836e43205794c10b7a9221e4320876843204f55310aea9e85745150aeca2206b94840ba28a61b8400836e42205d14532af29c437751482dca5a0d714d219f2a6615d531037081905d14520bba8a857551ccbce6410cf15130ceaa06577514caf0a0a15d944309eaa065e652086bca5195754f41bb28e655c5350ad8a4886794c40baa8e873d54086daa5a1d754c10e219043d5310c6bea6a15ed4142af29e83cc32882daa4206e94040e721065cc328873865205794832cea988176518827ca0204fd5120bb28e857551103a86410f3508329faa2215d53886eca310e795032b7a92637651d0e78a8904f95032ea19643cc320873864205b94b43bb290433f544c27ca1204f953109f2a04375510c39864107908620afa9a43b6540875aa4205794f42b6292635e53882dca4205d54620baa8e85b6511033c64205794c40cf19481ce520cabea6905714d10eb190433e54c827aa9985bd4930b6292615c53483cc8410ddd4530
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x10800000000288010000300003085400000ac954951102c6628c8219318953042e0605082199189510c2c46350821e199032087883210020e195032086a5640c821b2181420cac46150832875943210385640c821d194c21883843208640c354d52102356508440e10c821103443294620b1189310c785540c821e8084400830d540c821
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x404a0aea1904220505759903208702b286410881215da540c821
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
  | 6 => 2*((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/22+packedAt s4K5 (736+(h % 22)*6) 6) % 46)
  | 4 => 2*((h/46+packedAt s4K4 (3159+(h % 46)*7) 7) % 117)
  | 3 => 2*((h/29+packedAt s4K3 (912+(h % 29)*5) 5) % 24)
  | 2 => 2*((h/8+packedAt s4K2 (196+(h % 8)*2) 2) % 4)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfffffffff01fffe07ffffffffffc07fe3ffe3f
  | 1 => 0x7f01fc07ffe07fff83e07c1f80fff83fd933c7
  | 2 => 0x7ffe0007fffffffffc007fe000ffffffe1c3ff
  | 3 => 0x80000007ffff81ffffff800000ffffc1fe03f8
  | 5 => 0xfffffff8000001ffffffffffff000001fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x914284011c104200c628c228e2c42520a561b
  | 1 => 0x2a4c51cb224728e581aa351b1255ca34d932c5
  | 2 => 0x44289a95448a514ab4105b48249a94a961c16e
  | 3 => 0x68b1636689141db35adb021248e36711be03b0
  | 5 => 0x70c183870e1861dc631c639c70038421f5a800
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeaaaeaaae080e080eaaaeaaae080e080eaaaeaaae080e080eaaaeaaae080e080eaaaeaaae080e080eaaaeaaae080e080eaaaeaaae080e080eaaaeaaae080e080, s4N, s4R, (fun _ _ => 0), s4I, []⟩
end PEqualNP.Outside.L_meta_36589
namespace PEqualNP.Outside.L_meta_36589
open PEqualNP.Outside.L_meta_36589.Model
def s5K8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K7 : Nat → Nat
  | 0 => 0x30440000031c00021c00c00001c43d5045057002fc21ff31fd10fd32fc31fd30fd41ff40fe30fc40ff42fc32ff32fc20ff30fd20be41fe21ff20fe42fc43fe32fe40ff43fd21fc10fd42fc41fe10ff10fe43fc30fd43bc41ff21fe41ff41fe31fc42fd40fe20fd31
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x483ff40c43fe6210ff90940fe21043ff410c7e8a2a16fd0a42ee19063fc41c437e85a07f90a20de20841fd42043fca2987e4c210ffaa0637c53507fa63086f54041bea8643dc53443788390ffd0c32fe21c657d54c43fea7907f48110fd98621ff510c2fea6087f54031be2a465bc41cc7fa8410ff0ca30de2a243fe53c87fca2997f10c31fba0c83fd32443f86210ffcc930ff18c43ff52cc3ea20087f54231ff188637c53482fca0197ec8220ff90041ff42cc2fea818df95230ff90e41ff42c83fe43987f54a30bf2a0837c53c83fa83186f10841bea9c61fd52843f881085f54e10fe2a065fd219037aa8197fd4241fe29487fe414c7fca1215f54243fe99241fe104437c8310ff10e21ffa8e81fe328c7fea0a16f50841fe294637d53487f8a020ffd5110ff21a63fe210437c84a15f94720ff28663bd42d02fea9985f54343bf29e41ff31cc3fe8298770c930ff294617e51102f8a2997f10b20fc88021fb20483fc82207f10b30fea9a83ef32087fc82887fd4b31fe90421ff53843fe63905f55321ef99065fe528437c8218ff55230be2a461ff32d07fea118ff88421fda8243fd42c83f862087f90030df19483fe4350ef8a2987f4ca10fe98e813f544c7fa85987fd4041be2a241fe32043f8a2987f4cb40ffa86637d52d02fca421ff14a41fe28465fa30083f8a118fe84010fea1c81fe43102f8a910ffd4432ff29281fe414827ea8887754e20bfaa0415f53443fca5887f8c821be29621ff40483fc86887f90931ffa9421ff53087b86518ffd0110ffa9a43fe510cbfa6520df94431ff18a61fc414c7fca3197f90920ffa1a43ff53d03fc83087f90d32fea9083ff328c7faa3107fd0941df19083fd218c3f081907f14642ffa0081bc410c7788310df54642bea8063bf43d0afaa4185f54430fe28e813e51107fc84207f90d20ff21221fc32083fea6087f8cb30fe28265dc310c2f8a918ff10440fe2a441fc434c2fea6105f94243ff29a83ff420cb7c82987fd4a43ffa0c63fc41443fc80a07f0cb21bf29c87fe40c43f887997f88730fea0841fe300c3fe86187fd5121bf28421bf32907fc43905f54c42fe98021fe40882fca310ff08530ff990217e5390bfc87087fd4143ff21265fe53c42dea498efd0641fea0e43fc31c83fe86a1fb0ca21fe18e61fd438c3fca020ff10520db28883bc53907fa84197f8cb20fea8263f85050bfaa3187fd0210ba28a85fd32107fe6410df94f42fea8a877d5010ff884197f54742ee21865fc50507f86598ff10f41fe21283ee320cbbe8721df95321fea9087f441087f86510ffd0410ffa88416c524c6f8a0a1ff90e41bf29c41fe42843eea2a17f90441bea9e81bf32107fea110df94b41bf28c65fd41cc7f883087f94241ff188437c54486faa1a17fd0421ffa9c83ff43c43f8a7a05f95121
  | 1 => 0xe540427ca8107f54321dfa1c837e53902f8a8187f90d41fe18221fe51883f86420dfd5130bea9663f950ccafea2a15f94321bf288657950ccafca2215fd4943ee21c657d544cbf88418ff90832df20e43ff43043fca2a07f8cb31ff28887fc428cbfe8621dfd5331ffa9c81f5310c77883205f94821ff29261fd52902f8a2a1ff50d10fe10c61fd21843fa63887f4c540fea0e81fd420c7f8a421cf55331fe182417e50883fa85197f90430ff28243fe30043f8a5187fd0a31ffa1261ff53482faa1217fd5310fe18c43fd320c2fca8217fd0c21ff20641ff52507f885997f50d20ffa9483ff42ccbfc81987f90521fea9881ff214c3fea0217fccb21fe20441fd54043fea1997bcca21dfa1c87fc54442fca418df14141f79084378504c6faa321ff0c210fea1a65fc54c42fca6907fd4141be2a041fd42ccbfa80207f10310fea1c21fe32887fa80887f8c721ff29843f441c87d842107fc4110ff29061ff42d07fe82107fd4c42ffaa461fc504c7faa8907f54740bf28841ff314c3fea4a07e0c010beaa443ff41c87fa80907f15232bf29485fe5190bf884985f54c20ff28263fe20443be86a1ff95330fea16837e53083fc8690efd0c41ff99663fc51903f8a4885f54e20beaa2617d5490bfaa8887bcca32fe90621f710043f680107f55321ff28087fd544c3fe4210ff48740ff29483fc51d0bfa84987f14021ff10421fc53487fa8720ff8c420bf2a663fe54c83fc40907f4c940ef19661fd32c43f8a4087fd0f20fe28087fe54443f8a0197fd0f30beaa463ff41cc7fea8907f8c831ff21243fe54043fe61184f15110ff18641fd32883fc86185f54910fea04217e52d03f88290ff14f10ff88421fe51ccbf8a3197f10620fe21885fc544c3fa64207f10f42fea9621fe43502faa8105f94643fe10021fc54887f8a2207f54a43bea8c81fe50ccbfe84085f95131ffa9481ff51d0bfe80185f95120ff29283ff54083f886107fd4620ff21061ef20083f8a6a05f95030fe20861be41083f842107f54743ff20e21fe5150ffea6107fc8410ff20a81fc43c87faa4205f94f40ffa8a65fc32902fca3997f94b43bf28e87ff318c6fca210ff10a31fe20241fd428c7fe8410df94042ff10a61ff30082bca7107f90620fc98221fd4390afca318ff50f40ff99443fd31103fe86a0ff54032fe98a21fd324c7f641887f50640fea1883bc42907f880886f50c43ff29e857e50ccafaa7217f0c530ff28c817d508c6fea610ff55231ff99063fe43c43f0a090df94832ffa9e837e544cafca6197f95321df20e63ff41887fc64987f90e20bea9087fc43cc6fea8187fd5032ff99465fc41503fea3207fcc410bfa9c41ff408837e8420ff54c42fe21021fd31482f8a9907f14830ff21621ff40502f8a8987f10d42ff19683ff544c6fea7887f94931dea1
  | 2 => 0x43fa8690ff8ca30fe2a421ff5210f7ea720df15220fea8c85fe548c37ca620df94040bea8483df314c3fe84107f90c21bea8c417f54c83fe42104f95032ff2a4217c53083fe41087f94743be2a063ff51d0efea0a0ff94321bf29621fc5250f7c8520df54b43fe21e81fc4390bfe61086f90740ff21021fc51883f041885754e20df28883fd21503fea4185fd5321ffa9883fc41043fe65207f14f21ffa1c43fc514837ca8105f54f42fe28485fd430c278a890df95231fe20843fa20083faa598fecc010ff10c61fc21d03faa890fe8c110ff210436f52443f640087f48710ffa9a85ff42c87f8a0217dd0541ffa0661fc324c7faa818ff50b31ffa1c65fe41cc3fc87987fd0c31bf29221fe500c77c8620df14f21fe18c61fe404c3f8a9985f14d10fe90c417f51483fea5a1fbc8621fea0a637d53087dc42107fd0b31fe21c81fe51482faa0197f50820de20e81fc30c43f8a7107fcc420deaa663fd53d02faa5a0df15321bf29e21fc32103fe84215f94e10ff28841ff508cbfaa6a17f94843fe19221ff528c3fa82887f10820ff98e43fc54083fc87907f14940df21083ff41903f461087f54f20fea9841fe53082fca42077cc631fe21643fd43503fa82205f55210ff28885fc30882faa7207fd4342bf29487bd43d0bfa87887f54b419e2a263be53907fe84a17f54432ff18261ff43ccafea8197f50520bf2a661fc32482fca9907f54810fda0481fd43883faa4a05f14d42fe21663fc52d0ff8a3185f54a31bf28887fd53043fc85987f10720ffa9a21ff40c83fca918ff90b20bf2a087fd320cbf883987f14241ef19261fc5110ef6a090ff54a41fb98a63df328cafca9107fd0d30bf29843fc32843fc63205f94030feaa0417f544cbfca420ffcca30fea9261bd4350afca3a07f95331ff292877f52442faa818df14142fe99283bd509067aa8195f54420fea1085fd32486faa898ef54e41fea06217d540437e84a07f88310ffaa421df430cafaa2205f15032ffaa641fd50d0ffa6290ff50220ffa8a817f53486faa020ff50610fc20041ee20483fc42105f14540bf29663ff43d07f86520dfd4132bf298817f54487faa2a07f95310ffa0c61ff428cbfe8510ff0c420bf28063be41903f8a1a1ff54c21ff90c43fd21103fa8220ff14a40ffa10637e530c7faa8187f15230ff20021fd310c3fc86196fd0240fe19681f9300c3fea39077d4d21bea9a41fe32c877aa9087f50d31de20c61f521087f240105f94232fe90a21fe32083f86390f78ca31fe10c81fd54887fea7a17f14a10de298837e50d0ffc84a0ff50a21fea9463fc51d0ffe8718dfd4d42fe98c417e5010ffa42907fcc820ff29063fc400c3be63987f10a21ffaa261bd42503fa60107fcc621ff18c617c52042fea7907b14910df20c61fd43103fca0217fcc431bfa82877
  | 3 => 0xa810df94221beaa661ff41103fa60905fd4e10bfa9e437f54087fe64995f94a10fe29a41fc510cb7882a07fcc920fe29841fc50487faa3907f90e32ffaa643ff514c3faa418ff94c10ffa9a83fd40c83fe61107f94e40fe99261ff54ccbfc8618ff14243fe984215c5350bfc6298ff10621ffa1e85fd430cbfea998ffcca10bf2802179500c6f8a7887754c10ff90c81fc50cc77883107fd0520ff21443fd53843faa3987bd4931bfa9421ff42902fea8887fc8310ee99065fc54043fa81985f94c41beaa061fd32d07bea6885f54b10ff98621fe53d03f8a2997f15120fd18061fe31103f863a07fd4b40ff29c41fe414c3fc62887f10d31ff21063ff528c7fc80106f90531dfa8483ff548cbf88218df94630ffa0c21fc32487fc85197f14342be2a043fd53d0bbc60987f4c410ff288617e51d0bfc6420efd5110ff994837e5310ff8a5a07f54c41bf29481fc43107faa7215f15332bfa8263ff53503f886207fd0641ef19063fd41487da84217dc8521fe99661fd31086bea690ff8c520df208817c504cbf886997f10010ffaa043fc21103fc87997fd0c20fe296837d520c67aa990ff14730df20a21fc4344378a420fb14931fe99463fc320c3fa20087f10a40ffa8a85fe434c37882207f08520fea1461ff218c3fe63207f14e41ec980617e54102faa7a0ff8c610bf290217f548c7fe85187f54f10bf29061fd20043fe6420df54f20de28083fc54ccbf842885f94842fea0861be41482fea4a0ff10d20afa9a857b5050bf8a2a17fd4b10fea14817c53487fea2216f10510ffa8487ff404c2fca9997f10e10bfaa465fe41c82fca320ff90930fea1a83bc414c7fc87a0ffccb40ff18041dc53487fe8790ff10530fe99021fe42ccbfc20087f14643be28a85fe54ccbf261907f90631bea8e657e50d0bfc8208778c630fd98261fb504c7fca598ef90610fea8c81fd53d07f865887f54420dfa0081fc540c77aa420ff14b31ff2a043fd32087f881987e90040fe19281fd31cc3f8871877cc431dfa8083fd31c83fc85a0ef90140ffa1e63fc418c7fc8718ff14e40ffa0e81fd32c83faa9107f10e41be29c21fc40c83fe8220ef10520dfaa243fc21843f865107fd0c42ff20843fd514c3fea021ef4c841ff28e61ff524c7f885a0ff14d42ff98c61fd41503fa83887f10a30ffa8881ff548c7fc43207f54941ff90221fd54cc3fca6887f14142fe28861ff30443fea420ff54b40ffa1a85fe52043faa021ef94241bc28243fd400c3fa83105f94e41fe908617d52043fea2a1ff54141bea9a21fc51082f8a8997f14c42ffa8243be50107f8a810ff0c6409f2a643fe428c6faa720ff14931ff18e81b441087fe60907fd0010df21c837d53043fc65207f15131ff21887df308c3fca121ffc8120ffaa441fd50d0b7883087f90c10fea16433e548
  | 4 => 0xdf54630ff294817d5490ffaa9887fd0920ff2a465fc52103fe62207fd0a10ff90a417d53103fe84997dcc631fd18641fd32083f661185f94c42fe210817e508c7fea221ffd4f21fe21241ef4290bf621087f14332fe28885ff31443f88420ffd0430fe21221ff53c43fa80987f94d20be29a81fc20843dc84217f54331beaa241fd42103786420efd0c43fe21265fe31486f8a8887f54443bea8665fd30883fe64a07fc8610beaa481fd42443fa87a0ff14c21dea0081bd41107fa83987f95032fea0e41fd438c7fe62905f54730ae29a43fd42907faa9905f94021bea9e43f820043faa3195f94410fe21421fe5350bfa6598ff0cb30dfa9483fc53043fe8520ff90721bfa8a81fd30c43f865907fccb10df20a43fe41083faa110ff94742fe90821bc54443fa84905f94020fea9221fc31442f8a4a1ff8c430fe21a43ff52043fa6310ffd4341bf2a6217e548cafaa710ffcca20ffa8c87ff31842faa8885fd5120bf29c437a50ccbfa84996d10721fd28665fd51ccbba63987f54520ef21887fe53503f88390df14910be28263f6310c6fca6087f48421ffa0e21fd428427aa8105f54042be29c43fc430c2fca8887f90c20fe18021fe508c7fc42207f90f42fe29e85be410c37a8720fb08620ff21e43fe21443fe83107f14732ff20e637f514cbb8a6a17f90541deaa643fe4310bde41107f90f31fe10861fc41083faa5a1fed0140ff21041fd5190f7ca520ff54e40fe188817d518cbec20887f95221fba08437e5090bfa86087f8c540bea9083fd4310ffc64204f95331fea18435d53043fe85215f94620ff19221ff40083fc42907f14b10ff2a243ff42d03faa4187f8c710ffa1c81fe50887fc8590ffc8740ffa10837d538c7788290fbcc932fea84857d52103faa020ffcc740ff20461fc52507fa6510df15010de29483fe54483fc63106fd5131bfa9c43fc31483fa43987f94d21fe10a817e50903fc43086f90d43fb108437f514c3fc64905f54221ffa8c65fd320c7fa43906f95321ff10021fe4350bfa80085fd5310ffa8063fe50d0bfca8995f15310ff21085be41503fa62987f55032fe21e21be41c43fc64997f10d40ff21663ff10043fe6498ef90620de20861ff32103fea190ff10b40bea9441fc41cc7f863087f94132bf2a261fe32843fa85a07f94440ff28043fc43883fca0a1ff90621dea1883fb5050bf880985f94730bea9421fc30c83fca321ff54532ff21285fc32507f843887f50841ff28687df5350bf2a018df54610fe982217c54cc3fe60185f54331ae29a21ff414c7f8a0a1ff90e21ee18c61fe21d02fea4a07fcc910fe10c41fc54487fca8987fd0510efa1c657e54887fc8218ff54931bf28083fe32d03fca5a07f15321fea1e61ff20882fea898ffd4c40ff194837d538cafaa2197fd0e30de20e21fd43c82fc
  | 5 => 0x32ffa8a41fd43083fca4887fcc430ee98863fd4310b78a898ff50f42ff90a81fe53907fea4a1df15131fda0641ff42503faa0a1ff50f31fe29883fd42487fca6205fd5010fb90c43fe40482faa7887fc8620bea94837f52c437ca9087f94840fe98c61fe41903f8a3905f94430ffa1a63fd438cbfe86207f54442fe99481fe53d06f8a4a0ff8c720fe21061bc43107faa121ff55232ff28465be540cabca6087f54121fe204617d53106fca420ff50830eea1887bc41043faa720ff10f30fe29063fd50907fa8710dfd4930ffa9261ff42883fc81087fd0b10fe106217d54882eea2a17f14d41fea0041dd314c3fea4885e94031ff182417d540cbfe86887f95031ff280657d54c83788210ffc8710df20e61be41c82fca5197f14930f699065fc43c83fe40087f88020fe19261ff54887fa86a17f14031ff98021fe30443dc43107fd4343ff990657f53443fca7087f55131ffa1a65fc50887fe63887f50530fea8465fd51103fc4290ff54f21ff192637d54906faa5187f08730de20e417e528c7fe87087b48020bfa9a83fc21c82fea9087fd0d20ffa8c61fc42503fe64a0ff0c521bea8e85fc32d07faa0a1778c932ff19243ff315037e84217f10b10f619043ff500cb7e8520df94241feaa043fd5010afea9106f4ca41bf28c81f541107fe8720ff90e40fe99461ff544cbfe63105f14c21bf29461ff41507faa6a07f55210fe21441fd42503fc42187f95030fea16217d548cbfc61087fd4242ffa8c85fd5150af8a998ef10730dea9883fe42903fe81205f54740df29083df300c3fea8085f14a10bf2a063fc310c27aa9087f54e20fea1441fd52cc3fca898ef14241bea8887fd310c77aa8107f8c830bfa8a877e5190afaa9187f94b30fe20c81bd52907ee8390fd90441df20a837d508cbfca3a07fd4e21fe19463fd53886fea910ff94630fea1863fc53d06faa998ff54d20fc98041fe5290ffc83187f14c40fea82657d528877a84217f54332be29261fd31082faa890fe50040bfaa665ed21087fe61907f54021fe98e43de53043fe84887f50631ffa0a81ff424c7fea8187f88710be298217f52043786520ff10c329faa243de314c7fa8498fec4110bf2a041fe21502fea090ff48530df2a663fc32042faa3907f94e21ff29463ff32487fea3987f0c540ffa8265ff4390ff0a098ff8c940beaa6657e51107fe84207f90a30fe20041fc20443fc87187f88620feaa265fc42907fe8290ff54430ff90a21ff21103faa9997794e20bea8885f710843f8a710ff10d41bf28461fc31c43fe6298ff0c821fea0821ff4390bfa87995f54a43fea08437c53883f883187f10931ff196217e52906d8a4885fd4d20fe98061fd32c86f8a4a07f0c620ff28283fd434c3fe64187fd4e20ffa1e81fe32883fe8620ffd4831fe90041ff408c3faa690
  | 6 => 0x804004000090010400243b0010280e00201201a07c308130080000302304c000008000120000502500c004008080000340c0140160040003d14400c2a80301e00800838050da02300111407c24001006018008090100240543000000c030000320046800500a040038051282042683b0060ed2200000004c0000118e040028110000940c0000a40582581102c0000c80200402c1080600c0080a810108004000030000241381c0061700305b00a000060010620500481506e0300202d0000000300142c0780281c04802c3a802a2a0100001b05400803006a80088030020960280101d028030000000a4424020230040007b80002e00c05006000004290020060cc018010040240782d03a0704700004e064078090000181b804000d6403801000004000040120842f80100200004823010080000030001ac010300040280084500014800807056038528000380b4058060bc0c40000b0320040e8b7000020000040440100100e0dc0340981f000018000440c20f00400d00a05000000002004118040540143f09402c010080000020000500609a0381e8100001340502001405c070870ba1c800002004010000d08260140102a000026ee0d30743ec2700d07a0300100d034000220108fc1281780200c0b8008bd000000000a105e0bc0400f0460040101c00e0b42604c0020f4018080482740000401e0343982a222028108140201b0000010160980a849008074098020040040f00102c004218240523d40d84e08c0003e8080060001701f0140500400402800803001000050060140020040680db5c04c0100200400c1f81406e0100001420ffc438c7f8a9907f54d10fe286437d52cc3fca3907f94c41bfaa4613e51907ba60185f54a40bfa82857c54843fe86a07f50230ffa8263fe41d03fca7215f94d21de20a61fd42506f6a098ff8c310df20c63fe42906faa1a0ff15030bf29e43fc5390afca198ffd0e20fe2a463ef4250afca9087f14841fe19063fe54883fc62087f8c220ee19661fc54cc7fe8490ff15132ff996617e52cc2f0a0a17f8c730bf29861fd21083fc8620ff94142ffa80437e52083fe60985f94341ff90a43ff32c83fca8107f4c320ffa9683bf53107fa63207fd4732dfa0883ff54cc3788720df55021fea1e43fe52d07f860107f90e42ff21e81fe320cbfaa4a1ff14540fea8683bf4350bf8a5985f94d10bea8043fd54cc7f061887fd4840df20821fc43042fca7a0df54743ffa10617f524c7dc4290ffd0730ff29e41fc53842fea6a06fd4841ffa0e41ef52443fca2a17fcc521fe28683fc53c837c8210ff90040ef188617c51483f88490ff94341fd28063ff210c3fa8310ff10c21fea0863fe42d02fca5a1ff90110fe28a877c524c7f842085f14121ffa9c85bc418c7fc64a0ff90841fe29a21fc41d03fca6215f95
  | 7 => 0x60300381102001c14827000008090080004280100050e190090001880001180005a02c0002d01c0081781a0e815c0001e0780040000d0021a4008051100244d8012b01ec008010020b4010090161bc4280007408000007004050008130000080003d1982b80ba64424080083f60240740400018c0141704201652402806000050080040dc0140100201a000320240a6014120712d8098001b500e004068080460200080b0f40540000000c0080000200008800009008080002d61c40280a02e0000184500200200002008000000120310041d0060050000245181304036c470130300245b0230000180f8a90020240280d0200200b8020520040316904204806000000010008000240035b010008034001951120ac0000c000270090110020a00a00200602c19830086004008160400000000500200c0200100a00c0b8060122e4118030040740000100800802
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x524437b31d4121cf150524c7af3290421b7d8d21cc37852c41109fd96420c3a73210421de983540433d5490832dd987538867d6590930be582218c2f76154940bbd89544433e5310431dd1445050be452841109f584524c36d5210840ded81534836d53cc8219f195410827e6510130ed99041c873f54cc931d758f548cadc63545429f590538839c54d4d21cf94f43d0af6610c8219f992520867b6548020cf950410435e548cb309f98b538433f5190530f518d100427f6055232db14842442be60d0a41b718d42c827c63540419f582539075e530c410d794f51882bf64544309f58650cca7e6510531af980429073c4194040c714c414435d5308010de980540c27f6154243d710e520cb786194332bb189430876c52501108f59053842f960d4b31db14b424c73e544c721f318931cc33e5490441f6901300c27e65cc6409f582544cbba4108310cf55020843b44390441bb587320867e65d0620de50f504875e5310c42cf594414c2f9638c0309f59253483db5314121cf947401033f54885109f195215033e54143219fd8d54443db3154031af59243106fa6090940af58442107b960904109798c54087af52105319f582548873c6494740e758c501073d6155210ed0ca511067f6550520bd587529035c5348110bed95100427d658ca40de191500c6bd608ca41d7d4e43443d9314c0309b99452442de6310832cf55152842fa60cc821cf951420c76c54d4931ee18142d029e63d4a41dbd53524c67d6510b31ded4a500c75f53d41429f58454082de6315010af988509075e5350410dd987548833c54509209f98c540827e6194a409f58e540876f528c1109f58c548437b62d4121ae181421075f53d0921cf14e41506de6395110af596411035c6214d10bdd855250f3f5410630af59321c823e64d4532cf951410827e6510a10af993310c27f6254643de4c7504873f5414931cfd4841c4378534c320de94e300827e6114132be987400835f6294c10bed8152d0f7a534c210de18550ccbf030c40109f98a530433e5490630b7d8d410c35d510c4309f98654483ba418c030af986414c75c530c610ee98052106be650c8419f19151c835d53d0220decc7504c6f561cc3109f19443c86be6414f21cf552500cabf6550c439f990540c6be64c8410cf90650c87796095120be18142482de62cc631cf98e540cbad548c832de5405050e7960d5332d75835350b9e534c8419f992530427e65c8530b7588438cb3e5490832ed98441c439e538ca419fd8954442bc604ca41e7d4d539067d65d0c10be980418c2ed62cc420db14c524433f6455210be982544873e540c4209fd8d524427f6550821d7982538827f6590a30db94a218c33e62950209798c54882f96090c20cf55352cc7ba41c8310cf10e511073d5415210cf94e414835d53c8010
  | 1 => 0x427d60d45429f590534879e54cc8329fd95420835e63d5032cf58854486be64cc431db94f524437942d4121ee980539067c65d05309f997328435f53cc110cf18254cc6ed628c6219f59542c439e6310730cfd4a52106bd6490841afd85431073d5415221afd91210c27e6394d20ed10421c43765184010ded0450487b84350040be9835310a7d6494d10ddd4651882bc648ca419f58252442f960ccb309f995438873f6590520de580534433e6414a10fa885300827d61d52329ed81528c73c5410630cf99253887e752cc531eb10d4210b9c418c1308f99253486be64d4c20afd8d50906be6190d43db993524c67b6054d21db189510c2d960cca32bb98b43c82bd654ca419f58e520433c5494d21ee9824104375518c420cf19641c827d6414520af99021d027f65906309f19521d027d65d08329f993524c73e6590620f3988430cb7b4254332e754c329073d6115110be18142d035e5310c409f98e510827a6014c219f586540c33e5450731cf59441cc37663145429f992544823d6494d219f99053886fb604c410f6cc5300c33d5415020be982418c33d64d4a10cf55342042f76154d42ebd50524427c6590d109f98253d0b4c528c531db149324427e61d4d209bd89544c2fa600c710bd992210867d6494321d794f30c827c6454a10e7d4e53107b654904419f58054ccb7a6014c10d794e324833e54940329f195218c35d53d0e21af983439067c6550b319fd9532d06dd6388210af58e421067d650ca41db14b424c35e530c840f9d085150be852c4110f60c630443da53cc310cf153324c75c63551219ed8152d0e7e658c420af59021d027661d5220eb8c8329073c54109309f59642cc73f6455221dbd4820c427d6590b30bed81420875f53d0910de90d50ccadc6350820cf58554cc67e63d4542af588439073c6454720de0c5500c67f6550f10b798f40cc2f661d5220ed90841c867e64d4c10af59321082de6390530ad19121086be600ca419f590524c67d64d4530d7550430cb5e6315021de54c30042bd648c841bed81428c75e530c0209f58354c87d9434c0309f19432043775194542af98b43106fb6050e309f988540ca7c65ccb10be98342c42de6394121cf990548836c63d4910cfd94418827d6194b43be580210433c5450130af596418433751105309fd96430c76c524c110bb98a430cbe66108420de50b504c7eb6050842cf95120842db654c030be98331cc33e5254841bb58b5010fb4418c710dbd4a414435c538c941b798f5010a7d65d0f109f99442cc39e324c841cb14a41442f96090630cf951510833e52d0a41dd94d310c6bf65cc8419fd8d540435f6254c109f988548c6f561cc8319fd96420ca7d654c420d798c54cc33d5390621d794e428836c6254d109f997430427d6114c20f6983328ca7d6510c21cfd5
  | 2 => 0x6354321cf951300827e6115230de948504c73d5350842e7904310c3b841c8010be99220082ed65d0a429f194214c2ee6210f21cf904505067c6354440cf18b544c67e61953209f98e540833f42946429f184544427d65cc420ed90a411073c64944409f993534433e5414e10cfd50434437a6514142dbd4821442f86050a10d7190534427b6055121de550400827e6508440fa884504873d5290630fc98730c437051d4142af5834350b755114730dbd80524c778654c110be18132c42bd6190c419f99053c82bd6594041e7553320cadc63509209f58f525073f540c910cf99441487ba6010740cf14841842f864480209fd94420c67d64d4d10afd9131886ee628c621dbd4821502df6550c43e7993310c7ae640c8219f99743c437b4194031ded95308427e658c7209fd89544cafb63c4210cf950420839d534c841be583324cb5d5454c109f98353c86fb6048640bdd85328c73e5450020bbd89534433e54d0210cfd4d425035c53d0110de553504875e5390e419f98a548425e6395110ed191310c73c54d4121d798c540435f62d4d21f64c030043b44188421d714e31c867e6215010de109500c73a4154031cfd9441483775194643cfd4b509073c6255321ee905304427e6315310cfd88544877a6514121cfd9153443755108420cf440544427e65d09209f983548ca7c6254031af98c529075e534cb40af59052cc3bb5094041de94c5050abd64c8520be580315035f5394c42cf550414873c4114121dbd4a524433f64547309f18d50086be6010540de59740903783294031d754c431073e54d0840eb50842d075d5348010cf95332c867d6494430cfd5310442de6394910bd18542486ee6210e20ed10c41086be63d0a41be58321c827d6550a319f98b54c42ef6254d41cfd9641cc33c54106209f185521031d5310410cf14e41c437950141219fd9531903b43210421cf15150486fb60484109f997219033e5290430bb5884310aec6255110db14b325067e6590531cf90a51107795494031db90c52442dd6314041b7987320ca7e6294010db94842d067e65ccb409fd9732d067f6550720af98641043795014142cfd4a418427f6254d10de95320882de6410c32dd547410c3d553440109f994434c67e6394021e758c414c27d63d4121b7991320cb3f43944439f58e529076f528c510b718d418c27c6354341bed8132482f96014442f3d0e320cb5f6114d109f99441c82dc6348430d354832cc35d6114d10edd91310c7ae548c832d7583534427e6550530cfd94418c27d6215130ed18c41c867c6354841cfd92510827e650c440cf551208427c60151109fd9431c82f561941429f992500837843940319f58a544ca7e6414a10c7d53534427d63940419fd8d52843b561d0c41f6509300c37854c8120f698331cc27f65505309f189544
  | 3 => 0x109f99421d02ee6214c41dd5805150bb56210721be181319033d5490531dd947418837b6054720d7d4d435037754d0421cf54441c827c6354620cf952430833c2055020eb54b42d033c5210531af59321d03793114131dd145314c2f46150d41fa901200833c54d0e21af59742907ea60cc9329f595418827d65cc020cf58e54083bb42d00209f98a51042ef6250e20cfd52548c73e6494010b798e41cc27f654c420ddd465150edc6250c43afd8d52907d8538c110cf153214436d5214831de1845050bea6008420be982544c75c548c831af191504cb3d5414e10cf58d548433f5495021de14b504c77b32d4131cf551530833c5110530db54f52442de63d4321cbd50524427d6294c10d798c54c827f6355130cfd5031487793254031cf996410c67f65d0831d754c53086be64d44309f99443886dd63144209fd9643886fb604cb409f98b540c35f520c930eb152214867c6354b41ed14e511076c52cc110be99630442f661d0a21de948400827d6550d20e7d4d4350af56190f319f586520c27e658c540cfd0d521073c54d0d109f986521033c548c910da14b104433e54d0310d794d30042ee62d46309f588548432c5414931de98f504875d53d0010bb58b438cbcd434c832cfd53414433e5414f219f983540873d54d0210bb58a408835853141219f983514ca7d61d41429b98b53843b56190e41be98332486786055132af58e509076d5188620cf953438cb3e544c8209f18151d0b5c530c5219f98e54086be60d4e419f59532c433f6455021d70ca510c6ea60cc8219f59351483da324c110c794e41043ba5490040db94a20843bb42d0320db54852843b84108010b798c540867e61d5030eb588418867d6510420cfd95421067e62d5210cf18954843eb42d4142db14b42442bf6454420d714d41486ed638c832cf95343c827e650c5209f59641c82f9608cb10cf152204435e5310810cf50c5150a7960150319f194430433e5390521d68c9500c73f63d51319fd895010f775194640e7d4e414867d6508730cfd9251902bc644c621bed81528c75f63552329fd97311033c5290410d794d400435c534c210cfd51414871c5414d21d7545300c2fa6090020f594f100433b54141219f99632106bd61d0e41dbd48414c73d54c80209bd8954443b66410421cfd5343887775194443d7953534427f6454910cfd9441cc27e65105409f19743c836f53cca21de545300836c6254c21db54b421035e53d0f42b7987300c35c5384110d714e32c427f6550410e78c841cc3d9530c010db58a544c6bd6494221db94a428c27d6510a30ed153214879c6350b40de181520427f6550421af191524c27c6508540ded875050a776154d20a718d421067e64948309f994428c2f960c8420cbd50524c73d5314c419f994434caee6290e429f181548867f
  | 4 => 0xf19151cc2ec624c420cf94841cc6fa60cc720cfd53434cba43210421dd586544c7364214542bbd914210a6f6254d10f3988328c7b96010520cf18a54082f86054b43dd944310c27d6094643d714d5050a7f6548420af9874210abd62d4c419fd8d544cb3d5490030cfd9542d027d6094d209f18951902bd618c841dd584548433d52148419f58b534427f6508440b7980328c76e5414910fa18930c827f6590a10cf948410c67d6394b41cf54c41102f461541439f19531486be61d0940be98b30042bf640c8418f992544423e6494221cf54a511067d61950209b18954443796094f209fd95430c33f6355020f6980310c3db324c030bd584520c27e6494432fc101100427e62d5230f3509320ca7c65d0d21ee18041c82bc614ca41cf18c54486b4614c841cf59250042be64d4331ee907108427d6494432db54852103b642104219f197424c2dd6310b319f996304827d65c84109798e524427f6550841cf594429067c6510c20cf152304435d6154e20d754c53c427f60550319f597438436d6295132b718d504873d5354841b6580318c27f6550431af993315027c6550d32be181434c35e5390c10decc4504c67d6414a10afd9131c42bc6150c439f990520436e62d52329f995438437b32d4121cf95042cc73d6590c41afd89509077864543329f586544427e65d05209f9845050a7e6590931ddd46515033e5450a208f993538433e4154021bb596210827f654c832f6185300c2be630c841dbd4a504c67e6588530cfd53420867e60d53319fd8951d0ef960d4732b758f51d0a7d60d4f219f59641cc3b76210721b7d8d424c7d6538c4319f98854c427d65487309fd9643c82df6350a40cf55153c86fb6050921db949429076d62d5220ded42500c73c6494432cf552418c2be64d4630af582421067e6314810be582544c7db634c110b7984438cb5e534c810f68c6300c36e52d0b41cf59052842f76150910afd91514cbdb644c030b7d8d21c82ec624c7209f997428427c6354242bb58843d0b3c65104109f590504877a4294031be98343c427f65084109f58c54c42f86050d409f59732c427f658c010e7d4d53107794314131b718d42d03b743d4542cfd53404827c6590e10af990520c6be64c8621bbd89438ca786054432f5544310c35f5394f429fd8d544835f6554c109f586521027d60953319f994325027d658c010cf596418c7ba544c020cfd91544839c41cc230f9d04210833f5310410d754e318875c538c3109fd81540875d63d5221bd5865350b9f320ca41cf59642106ed62884219f9845388378534c110b758c424c6ee62d0d20cfd50414c2f96090e109fd89548c3ad640c821be980530867d650c540af98241502f76150110dbd53524437561d4f21db94b218427d6095130cf953424c2bf6254c41af99052043ea6208
  | 5 => 0x4250af960cc820d618153043af328c841cf98954c87ae6210621d7553534423e6414930db148325067d6494e20bb597328cadd6010e329e99630443775194142eb99321887b751905419fd96434427e60d5020af59053c82de63d0a31d754d318427d65501309f58b54cc2f9650c010cf94641902de6390832fa480200427e6550d109f594210c35e528c430e7950430cb5d51cc030d7d83534877860548419f18953903b76190841cf950430c6be640c9109f98454cc27e6590f10cf55120082f96010620ded425010fae4188521cf152414427e6294e409f58653d027e6590e219f99253443f261c8310de996304427c65d09109e18152d0e7e658c940ee180410835c53cc2109fd855010e7e65909309f98b544c2df63541429f58a50cc67960152329f99252cc33c5410d31e7905300c37652d0641ddd47215027e6394010dbd4921442bd6214241bb98b50cc73f4214540ee583529067f6590430be18c200433f54d0531bd59741c873c54d0b10cf95243ccb5c53d4142d7d4c32c42f7614c921af5933144358538c110dbd4a520435c6354b109fd8953903f04144010ed10450087b76294441cfd4852106f5618c9319f98a51d0f6c5288310cf992528c75e534c610d6d95300c27d6295121d794f420437743d4542cf548410c79f5310510ddd9541106fa620c310cf551424c27d6314141f60c430c43b552944419e580530873e54cc020be58031cc27d6550830ddd85534876d6295110cf150324c67d6510f209f98454082f46150840bb18930c83bb544c110d78c8514cb5f53c8110ed18c410873e41d4121bed81521076d530c821bdd85428827d6548430de508504c67e650c931bdd85428ca7d6548640b6181314c2dc6350a109f9835150b5e530ca40fa50920083b66114a41be98331082bc6448510cf99054ccbd8624c030d7d4e43507755110740cf59741906f661c8310e7993314c2be64cc530af992329067e61149309f185538833d53d4841bed9530c837965cc0109b988540437b6055131d754c518833f4254241db58854ccb5f5350d42be583410c27c61551329f996410c2f860485109f1855090f6d52cca10eb0ca410867e61d5031cf54a414437854141219f19743087f13084110de59630c82f661cc310de58650ccabd6010e41b7d8d525073e6095210cfd50324c79d6310730cf148414c33e60151219f98f52442dc6355120d614d30083f3604c431cf952400c33f5490910bed81410c37b6414142cf55041c82f96184010ee10730c43b46150841de152500c73e5490720cf58054487595344010be58052d0e7e6508630af59321842bc65cc841af19131c42f46150310ded09500c7da630c010b7d8d21082df6350b31d754e100427c658c940cf552410c67e6394442cf953420835e63d53329f98a50cc73f5410d319
  | 6 => 0x67f65107209f590534837962d41319f181548c73f6095321bb58b50cc73e544cb31cf99054c43775190540ee983329073e6510631bed81534867e62d4543be181218835d5454e20af592534873e5494321bdd855050f775148520db548529073e548c8329f19432503ae41c80209f994319033e54d0c32b798e204437b53440109f58b5050f3f63952109f596438875c534c9219f9944350abd640c910cfd51324873d54d0f31e7550430cb3d54907309f597319033d54d0020bd58754cca7d6194a439f992528c27d6590420cf548411027d6510e21db180524c6bd64cc721e7d8d521067d6550910cfd4e41c827f6454b30cf152524427d6294f10d798c53882ec6255130de149500c73f6550842d718d544835e6394910cf59053087b44154021d758a53882fa60d4a43bb588511033c52105109f58a548c73e54d0b329f990524437965c4210be18530442be640ca20bd58642c86f9600c830be583434832c52105319f58e510836f6254b10de887504871f5310521cf55142cca7f6155320bd98742d075d53cc610bb58b418831c5390521b758e50c873d5410a32d7d4c31c86776155121d7d4d5150a7d65ccb40de991500c67e6194f40dec8450486fa60cc840cf94942d033d548cb319f19152443da214c030cf95142887f06048421af59441842bd64cc6209e980540c6bd648c940cf95043c873e54140329fd9530042bc6454532ee58241c43b46448421bbd89310c33c54c8521edd4a511067e60d50329f99642843766114810cf18154cc7796014f209f580544cb3e6415020cf551420c3b95448020cf95243cc6fa6090b20b7d8d42042bf6448530cf95032c86ec6254d40cf15231442df6348520cf548429067f6590910af58042106ec624c520b718d214c27e6510030ded0c504873f5390520af181521073e5110421cf951420c2de63c8430ee58041d036d524ca30ed98841c875f5394c21cf152324863e6414f21db548524c2bd6290540ded8650ccb9e6410c32de8c8504873f54d0b20cf152534427d61152329f588504c6f565c4210af98c509076d5214b30dd594410873d5290410cfd52544ca7f6550830d6d4c30c436e6295110da14b504c67f6590620bd98442c87cd520c831d794f318427f64543219f597430cb7b64141319f18053443b76150a41d714f32482de6314810bd9865350b5f53081109f5805350afa6010f309f59441087796254332f5546318c27e6414931d714c424876e6214f20afd8143d0b5e53cc010e7553438cbcc320c6219f98e54482bc6448620cfd50424863f64544329f990530827d6590840ed105310c67f658c6209f58e50042ee62cc420cf99641886be64c87109fd9432082f46155120b759632cc27e6394321b758f42cca7f6354a40b79945350abf64485409f58c544873d6590530ebd4a
  | 7 => 0x4d4e10d7d50438cb3e54102309f58a540c75e540ca319f58e50082bd6408210d79845350af96014c21b718d215033f5290531b618131cc2bd6210c41af58041103b65294441d794f438827e64150309f99432907b954d0020bb189304833d54d0c32bd986408427d6494232b758f528433d548c8329f992518cb7843d4131bb588400833e5354c41e799331cc27d6494f10ddd4c5150aef6250c219f58054086ec624c7409fd95420c75f5394f41cf151534433c5490931dbd83524c7b76210421d754e408827c6590e21bbd89311033d64d45309f99421cc37b6314131f5d8d10042ed6215031f6d82310c36c52081109f58c5050a7d6395020be982214c2bd640ca20cf146414827c6114d10be582314c33e5050040c7d4c41442be6314841af58853907af64508429f58252cc67d6590820cf94a511067e6494421af593318c3b4410c410dd185544836d5414910dd984540867f6590b31cb548521073451105209f98854cc37852141319f980548cb7a534c030ae58332106ed62140419e59420042df604c8329f988540835e63940209758e50c86dd638c431cf18154c867e61943439f58653d0a7d6595030de14a308427d650cb41b798c54c83ba60907108f592530c75d5394810be181524c7d931cc1309f58554043ce534c8329f99353c42bd6414b319f58f540435c6094e20cf18154843ac41886209f597428427e6590630d754c43d0abd63d4a419f982518cade63d48408f992544875f5348110cf550500cb3f5490d21be181218c35e63d5010cfd95540cb7661d50309f997435073d54906219f58c54082f7634c431ee10610042be60d08419f98a51102dd6314640be583324835c5390d21cfd40509067c6354342be59730c433c4194031d7193534427e63141429fd9742442fb6050840af191218c2ee61084209f58854cc2fa60cc841af99331cc27f65cc810af59132107756115331db9524210abf6254041de988504c73c5410d20bed8131887f330c4010af99032c87ba41cc230bb588531073d54503109f994214c2f661d5030af189539075e6314f10cf596418c27f654c520bdd8542906be6494d21cfd91544c33d51904409f997215033f5490931dbd4c328873e5390620be580418c27d65504209f594324437561d5210cf150214426f654c8329f58b54843b56210421cf95341c86ec624c730bb58b41c873f65104209f586548c3cf430c821afd91329073e54d0b31be59720042ed62d0c21eb148414436f5314910d718d510827d60d4943ddd85544ca7d658c520bdd85428c2f96008710ed10721442f4614ca10be982420827e6114c21db14b204436c6255130de98054ccb9e3210530dbd48214c27d65d0830dd544510c33d650ca41eed81421067c6454232d6d4f504875f53d0d20cf14c418875d530cb20af9824310
  | 8 => 0x21d794e308827e6315110eb90520082bd640ca30cf950418c2ee6290621de59440c836e52087109f996314875f53d0110af590510827e62d4c20cf953200835f3154031b718d21cc2bf64487309f98e540427d6550720bd98754ccaed610c821be982314c35d53d0f40dbd48404437a6414131d7594318c2f960ccb40ee98332106f9600c720cf990540c76f53cc821cf15352443d8434c030f698e200827d6094a43cf550410c67e650c110cf90650083b8418c030de5875050b3d54153219fd97418c3b641c8521b798c509067e6394841cf98254cc7d8324c030f30ca214c27e6510d40cf552510835e53d0c419f582530873c5390420bb9884088379518c320cf10650c873e5490b21be98d100427c6154f209f995215039f4350a32af99032907b96014e41cf94a41cc3d85314121ed98441443775108540fcc8450486bc604c841de10f504867c6548510db18c524435d528cb30cf98b544c67e6414530bd587304435f6354c219f18151ccb3d5410630ee98041042be6390c41d754f520427e65c84409f191500c77832d4121ed94e51107cf624c431cfd9641087b841c8310f5105310c73e53105209fd9721d033f65904109f196324433e5410730b7d8d21d027e62d4530ed8c841c875c53d0921cf153414c6f960c86109f594215037b41d4131f30ca310867d65cc421b758f50d06fa618c030ed987421067f65506209f98b540cb9c5414d21d754f31882be628c841d754d318827c6510030af58b50107d9300c310be980411035d5350e20eed50504867c6154f42d759053443d8514c030db988540ca7e6094d21cf583544c7db600c930be58341cc25e63d50109f58053886bd64d4620dd98453c427e65d0420be98053d0bda608c9309f597438827d6194e42de980538427c654c110ee58342d037832d4131f614d308436c52909419f597300437953c8220ed98752906ee6215031fa08440082bd6094a41cfd5342487b94314142cf994544439e41cc030d794e328827c65c8540b7d85310c6fb60508419f592510c7b66310721cf94e511075e540c831af993500cadd658c430af59032c867f65508429fd95418c36d524c841de54f300436e5414931cf55241cc6ed650ca219f594311027e65d0530e710c329075f5494e20af98b41106f965c83108f990540cbdb31cc130bd59241106be61d0e439f997311027d6588540decc8504c67f6548010edd0c41c86be640ca30af584439073d5390740d794f21882be6110510be982329033f5454910de904504873e51104109f59643843eb3248020cf152414873c5390620dbd49414c76f6254d109f597214c3d83254031cf14c41042ef624c431be58343d039d4310c40dbd8c524c67e658c8409f98253d07da53c8220ed59321886f56190a41be583421033d5410230eb10721886bd6
  | 9 => 0x885200827f6510a10d7d0e520cbba4188020ed98441c876d650ca21db54b421073c54485109f98a54cc2bd64cc421cf15143ccb7b54100209fd8d511033c63952109f98454042f8604c6219f988535033c6454d208f593528433d52904309b98854cc36e63149109758c54086dc614c030af590524c27e6510910de582544c27d6315110ed58c41c873c5350d42af19121086be6394241e9588410875f538c520d7151538835f5394f409fd94218c27f6510a30bd58642086de6310a32d794e418835d53cc640bb59721887b661d4c41bb1895350777514c530ded8152d0fb441c8620b798c521075e53d0c429f99532842dd6388010cf94a410867e60d5332e7593318c6be640ca31ed10631442bd640ca41ed988410873c54502209f5825210ef661d0f419ed81544c75b53141429fd95430876f5210510db94942042be6415020edd82511067e6394d10bb98a30883ea6208310bd58440842df6350b32cfd53504c6f7614c841b758f54042fa6010f20be98243442f66114032ded5150ccb3d5290730cf19641042bf6150441cf951530827d6395010be58053906f9600c420b758e410c67d658c540eed4150107af3210421de582544433e5450c21f6d85300c35e53c8010b6982324c27e65d0d219fd9732c423e6195020be181429027e658c740be983318427e65d0730f6d05300c2f46150830d714e40442df63c8530d714d31443b64148421cf552530827d6414f219f98653c833f6455131be983411033d54151319f99643482f5610c8319f996434c37761551319f98b544427d60d5032ed984418827d63953109f994318837b41d4121be582211033f54906209758f548865e6394020cb148414435e6014d429f982540c73d51906409f992500c79f6350e41d7d92538833f5110530cd94841087d75314542af980421073d65d0e43b758f5010a7960d5031cfd9554083f0604c431ee90720883e761508429fd8d548435f5394e20bd986430c67d6510b10eb15352443e46244010ee10420c435d5350a20af592425027e65d0d309f98e54c86be61d0f42db94a32d027e61d5020d758f548c2fa6244010ded9550ccabc6054e419fd95428c73d5310621af5924210a7d6588740ed107218c35d3154031cf54a41d036d520ca10bed81415035e5310e21cfd0e511067e6510921cf8ca51106f76155120af593318c6bd608c8419f980540c2f86050931db149204427d65d0820eb588501075d534c640bb98843486fa60086409f98a544c27d6590931de8c4504863d65950329f99441442f96010910bed81544873c548c5219f19632843ad54084209f994424c2be6310a41bb98b410833d54d0a20be58e200835e60d4d21af18d411067f6154d219f99421442f66190d41cf55350cc6df6348610ded8153486ed6210c20bb18931842f761508
  | 10 => 0x835c5350910e798e418c73d5390e419f996434c6be6515110ddd85544835e538c620e754e329073e5210430cf14c41c42be62d0f42ddd4441482dd65cc230b798c52d03b554d0721e714d4350bad4210b21f698c30c437a42d4121de945100427d6315220be58031482b96014841b798c428c2f960cc430af98732907d9608c6309f18d52c42bd6294c41bb58a544c6fa600c620cf55143086bc6454430cf95331842be6210841bd185425073d5394441cf989540833f5495232cf14a41503ba5014041bd58643c432f52905319f982531076e524c841af98a509077760d4542f3d89314c35e53d0c40de540500873e41d41319f580535067c6550c21be9825150abf654c841cf54e41c435d63d5220de5085050b5e538c840af590328c7ba418c320be980430833e5490520fcc83100433e4114131fad48504c75d65cca32ded4250486be640c821be1815150e7d6054c10fa58332886fa62cc310d798c540c73e5390621cf153430c76f5210931b6181310c67d62d4f10f5d8d310c76c52d0110cfd4841842df6350a21de94d30c827c6590c209f59253086dd6310030afd91524c27f6054442bb983328875d63d48109fd9532907775114142bbd89315023f6550c43d758c540877a4354031be18143c833e53107219f99631442fa60d0a209f19152c433d6095032b758e314c2f960cca10cf14c41c867d6015221cf98a54cc73e5450e109f980525075d5314f41d754d439033d54d4f21de58353c83765044010dd94441103b44108510cf589548433e54d0810cf153504c6bc648c8419fd97329027d60d52319fd94219026f6550842be582439035d54d0c32ed18841c863d64942218f992538875e6314e21f34c8328867d65cc9108f98454443b66310421eb508428827c6215120cf153434867f658ca109fd9153882f86055131cf94e411033e41940309f99432d067e61149409fd96430867d6055010f6d4e30442fa6110320dd597218867d6214d10da148504c67c6255230cf9514310a7f65904209f997324867d65d0c21cfd91540835e5308010bdd8110042be644ca419fd9631d027e63953209fd94321033e65905309f59742cc67f6510d20ddd935150b5c53cc510b758b430cb3e5490210db94b211035e6314d20ed182511067f654c620cf951318427e61141439f99252c427f6154910be98031442be600c841b758f548836e5248610ed8ca511067d65100309fd91508875f5384110bd98442086be60d0c41bd58442d07755148620edd0e411073e5350c43de90b504c75c5310d20f654f300427e61d5220de50c5050a7d658c831d714d43442fa608c8109f191538867f65504309f18153d0b5e63d50319b58854cc36e5210841be181210877964d4131be597409027e6114f20db94a328c3ae320c841ded5040c82dd63d4a41fa
  | 11 => 0x6f6255121fa14a304436d5250a419f594430cb3e5190431af191518c3d65344010de94f50486ee620c0209f98054cca7e6014532cfd4a414c3ad6214c419f18554c827d6094432cf55331842fa60d0a30cdd0c5150add63949109f19543487db53d4121d614c5050b1e5310410d75974390f3d5450f21be18131c427c6054f41bd58720c437351d4142be98332506f4614c310de54050d067d6510d21cf54f42907795494332cf94e414435f6454c10ed14a511073c5210410e7d4c41486dc6350a40af587431073d5494f21de592500c6dc6350931f50ca310c76c5284110d754f31042f7615092197d95310c67d63d5210fad8910042f56190210b7997314c35e5454c10ed107210876d528ca319f18550ccb3d61d51219fd815210fb55394441cfd52204425d63d5220fa48020c435d538c740cf151400427f6354642d714d43503d9314c320eed42405033e5450a10de54f200433f54d4d21d798f54cc73c6215131f64c5300833d5210630d794d200427f6510c32cf194410c67d6095110b7987328cb3f60d5110f6cc530c827d6595021cfd8d54c86be64cc420cb153524433c5450b209f98853c42be65d09409f59731d027f6154d20de14a30443b4418c721ded51500c6f86308310cf55143842bd640c821b798c418c67f6590f109e18154487b74310421d794c218827d6590d21db949420c67d6510c30d758c54c82be60d4841be983214427d6510520b718d100436f5294a30be98031c86be64cc720dbd4a5250ebd64c8640af990500cafb6050830ed984418c33d544c7219f594329035e53d0e21dbd49324c73f5410930db54842d035d5350c10ee58052107f020c4010dd98454887ea21d00209f593504867f6550931ee90630082bd6394441d798c54cc6f86050b31af59441cc73d5190630de5445050bb441d4321e7104310c27f6548410cf54841cc67d6015231f30ca21cc36f6254a109f982520c79c5390521d754d310433f54501309fd9543c833d5450e319f98a540c67d6094f21d7994534867d6115332b7189310c776518c630be18143082786054841fa948200427c6254343bdd85428c6bc6454d2097d95300c37a3294031be980210427d6594c10f6d4f5050b5d5390010bb58b51d02bd64148308f593514cbb44108620ded0e500c73c6255032db54842106de630c5309fd9543103da524c030ce105500c7796094d21cf54f4290b7561d5321ee10530443af5254841be18142042776548421cf153404c27d6254c20bd98642c87da424c030bd185420c6dd618ca319f98c52c437a524c020bbd89314c2b661cc841cf55240842b960d4a41cf551318433e6590421afd91504cb3e65104309f59251ccb775194740af98f421073e6414c21cd98651106fa60cc830cf951200833d6510720de1475050b6f5294b40be9844
  | 12 => 0x10e41bed81420c76f3294632cf105500875f4314943edd5041c873c6155020d714c31c867e6094841d754c531076f520c110d754f43106dd60cc8329f992500cbaf43d0942cfd53524c77451d05309f596219035d5350c21d7d8d51082bc6050441cf94f43107b56110841ded04504c67d6550e209f18d54c42b66114c41af980531076f52d0931e7d4e32106bf6454632db94821d033d6414f21e7907318c6be6110421ed984418c67e6494010cf550414c67e62944309f593524c2bf6448720cf484544867e6510931d754d420427e6115232d758c548837651c8420f694c300427c6355221cf95052843ce5308620be98353d075f5310d42bed81425075e3294431ad98641086bd64cc521bd986429067d63d5310be98032443792114121d754e4390b3e51904309f99352043b661140419f98b530876d52887109fd94410c7365110430bd9845090ef46150110be58341082be6294e41dbd4c320867d65c8440d78c4504c73d5410b20d7d4a324c37b5094342e7cc8321077953141219f596530873d63550209f983534867d65cc820ed104218c27f62553309f58a51902df63508329fd89540833d5450a10ba181210867e6314c21cf151534875e54d4d219f583534873e6415130b7d95320cb6c64d4910cf94c41487e742d4542ed1854210a7f65108209f19541c82dd6390530dbd49425073e54d0020bb58a300823e64d45209f597418c27d61153309e98053042bd650c841bd984320c73d5450320ed993214867e65d0a319e983540c7b461509409f586530835d5310c42cf990540cab66114e41af98253906df6350b10b718d42cc67f654c9109f19541483ae62d0f42be58031d033e6415331cfd0950106bd61cca41de10c504c7795308010af98041d033e5290640b7586320c75d6014d219f19542cc2dc6348720b798b310c7db314c020cf587544433e5290510dd58653443f161c8310be580531069f63548419f588548c35c538c420af189439067c6254241ed144414c33f54c8510fa98a300827c65cc520bb98b51d027e654c941db94b42107ba5448020de59630842dd6315021b758c420ca7d658c740d7552530433f6455231db54932d02b561cc841cfd4e418833f4354a43eb98853107ac5250940be18132882be6114c419f993538837554104219f19543042be64840108f191518c27e6510520fa0c9200835d5314c409f986539036e63d4910be983320c67e65cc940de0c8504c77954d4131b798f51d0afb6050730cf55331c86fa6010910b7583430cb3c5450a319f596214c35f530c940cfd5343442f561d0d31d714d4350a7d6494c20cfd52324427d6494e21f6982318c27d6494b10bd59441c879d4310c30be58341c827c62550109f99054086df63c8730ed8c8410875d63951319f98c544c35d53cca20be58e30083
  | 13 => 0x9f98e501073f5414131bd185424c2f46155132fc1445050b3e5390640af98241d035c5354542bb58021082bd6010c41d7cc5508c73f5490510ded425090af961cc1309f983538879d6390631eb90421882f661c8110af992321067e6494630cf55050c86bf644c620ab1894350a7e658ca40cfd80544867f6508740ded81524427e6194a43cf19151082f86054542cf98a54c86fb6450040de98353882ee62144409f992510437960d4f219fd89539076d5108420b718d420435d5388620d7d8b53442f661cc110cf54841442ed6214343be181328c35f54d4d21ded4f5050b9f53909429fd96420435e530ca10db94a429067d6510821d78c6500c35e53cc430f998732886ed6210720d714f324427d6494010bb58b53842f9600cb30bd1854210b7b62141429f58754ccabc644c510ad98752907af52948419e98054cca7d6214540dbd89544c33e650ca419f19443842ed62d0521af990208437663d4542ee953400833d61553219f995315036d52d0b40cf9085150b6e5208630cfd095090b3e65106219f982540cabf650c841db14e21486f46150940cf550528433d62d5110be580318436d5214b409f98c54486f5618c210be983410c27c654ca41cf584544c67d6494a30cf95041c839f328ca41be98343883d953c8010cfd81540cb3e5450b32ded845050adf6350b41de15150ccb3f62d5131e998841086f4614c931af18532106fb654c210ed188410873c54d4931afd91518833d5390510d7d8d524433d5415032bdd95210867e65c8510de98354082ef624c730cf550430c2bd64c84108fd91518ca7f64547309f996328433e6414810cfd8954cc67c6550931ed984410867c658c5209f99643c86fa6014732be18142ccb5d5390e41be98053906bc64541319f98f514827c6155330af596521073e5390710be58353d06dd65cc631b758f50c867e60952329f58b514c3cf624c730cf191518c27e6590c20d718253043f2610c0109f997304433c6454620de980530827f65c8730af990324863e6515110ee107108435d4214d429f98e548427f6054c10be580548cb3c54d0932db94e210835e548c9329f185540cb3c41d4131be58351d0bb56310421af185540833c60550329f592530cb5e534c430cfd5230442bd6484010af593510c36d63149109f58f520433d5410c329f58b505073d5450b21af98232906dd608c531be98043d02de6310230cf950430c33c5410110ee50b405027e60d4810d794f40042fa60d474297d954310ebe64cc5209f592520435c1054c10d794d430867c6510f10afd91314433d5410f32de95150ccb3f5450920eb508420cb7a60d4f21b718d21083cf530ca219f59542cc27f650ca419f98e50d06bf6448420ad987539067f6510c30dd98754c437a4194031bd98443cc6fb604c8109f59431d033d65
  | 14 => 0x95434867c658c941d7d8d530427e6194f429f58f5150a7c6550830bd984308427f6550e219fd9631087cd5388620ded95100437a5408310bb588548c27d63d4a109f59443443af5290510fa54b20c42de6390a32afd9131c873f64553319fd8554442f76150f21af993214433e6590520bd189411067e64d4c20cfd4c414833c548c931cfd5231443ad528c841d798e50c863f6550040be582524c77560d4542eb95021082ef6254143af9874310f5d5314f42cfd91510c37554107219f58c5150bf0614c1109f99721cc36f5210930d794e329035853d41219f58e54887f321d4121cf58254c867e65cca41b718d410c33b54d4121cfd5253442ba60cca41d7546318c3af6250a41af98742d031c5310521cf55054c827e63d4b109f597310427c6454221fc986308436d52ccb31cf153434c77a60d53329f997438867e6095331cf953438c7ac3210421ce18154082fa60cc940cf55143082f66190821de908504c76e52cc8319f18152d06dc6348520af58f52106be6390a41be98043843b76150841af59032486fa6094931ee98041c437a53c4110b3189310c75c6154c10cf150504c67d61d4d209f1815110a7e62d4f10dbd4831442dc6355110bb189514c36f5250510b758c418c7bb6050842cf548410427c650c421ed107214867f6254430cf95251082f46150932fa90920082bf644c8409f19531102bd61d0a41cf95050cc67f650c910ad587421075f63551329f98353043ae41c84219f597428c67d6094443cf98154cc67e6590420e9107210873f52905109fd8553102bf6448520dd945319036e62d4f21af983425034e5308620cf953328427f6454a10ed951411073d4294442d794e10042be60d4a41af18142907b4418c421d7d8753487bb6050940cfd4a41502bc644c620bdd9510042be64cc7409fd95404427e650c740d794e31887ea21d4121cf5524008368528c110e7906314c77a5450040cfd52324c77463d4542d794d21883db60d4d109f99621cc2bd6494131ded81544c27f65cca109f58354cc75d538c710be18141442be65cc841cf5974290b786054432f654c20043ce424c832de95320c427c6355120e7105300c35d63152329f994544836e62d4e10f68c630c833f5390710db94a210423d6494a31edd85439067f654c820cf182548427f65487409758e524427e6394242eb106214875d530ca10b7189314c33f54d0d31cf549401027d64948219f98c515027c6510c219f98e519027f654c540d7d8b5350b5f6114d42be582328c33d6510710eb948529073e65d09409fd9643c875f6354f20cf906500873f61953319f588505067c6510020de18152d0f3f6454910ebd894350add65d0c32dd544418833f65104219f58c52043775194430cf107504873f5490721cf150414437a3194031dbd4b32507a4410862
  | 15 => 0xccadc6350b32cf58154c867e6510730d754c328827d6590c30dd944210839d54d0c32bed8131443774214542d7d4e30c437a6014e21ded4b504c67c6454332bed81424c2bd64cc440bdd85421073e6494821be98232c42bf64487408f992544c76e6295131ee58041042de628c831cf551420827c65105309f98e54c43d9314c210de18152102dc63c8530eb988501067e6550910db54852cc67c6550530de941300427e62953319f595410c3795014321bb588414837b6314121ee107308c2fa6284010de98a500c6bd6494a31de94a300c2bc644c6309fd89531033d5110440f6989300c33e5310620af993318427e65c8520f9cca21087d832cc1309f18d51903af52509409f596428c33f5408510e7990438cb7751946429f984540875f5350d21cf596410427e62d4143b718d51082bd65d06419f18152907365110740de15250ccb5e63148109f997210c2f96010440db548200433d54ccb21bed814210bda318c020af98441486fa6014831cbd53524c6dc6354142d714e214433d53907209f98252d0e7d6494b31cfd42501067f658c4209f986548cadd6388310b758c54c82fb6050720ddd44314833f5490e31bed81425027e65905109f994534867f6054e429fd8552903b664cc6319fd855210fb551104409f994420c6bd6494d10d7d4d31486bd65d0a429fd954310a7e6094e42b798f414c6dd6395110cf54e41486bd6090e41af99252c42f960d0740b7994324c27d6590c31bb18931903ac41c80209f58e521035e6315032bd18532043745190540f6183314c2ec6250721db4c4524c7f25184010b7d8d219033d5410730af99321882bd6494e21dbd49324c2f6618cb21db94921103ba418c210af98753907765148620cfd4c41c827d6414e21cf55332842bf658c8419fd91528c63e6515131db90f524c75d53cc8109fd8554486bf644c841eed4150906ed628c421fad8930c82fa60d0e30f9587328867d6115230afd91318c27d650c640cf989540cade62cc5309f596310827f65d0d20b7d9531cc33d6395210be980538877a51cc230be98354887784294332cfd5254ccb745314542a758c501073d54cc420b758e41cc27e6394720cf952530833f5494910d71515304376518c420af996329076f63d4931cf994418c37a52c4110af19032906ec6250620dd94721c827d6494632be181428867c654c720bb988501075c6354841cf9495290778534c210be98031087b564cc5319fd81544435f538cb10b7586324c27e6194830b758f520433f53904209f99632042bd64941219f181531076e528ca31af58a509079e54d0c32dd185540867f65d0a10dd953214875f5390942cf95150cc779514c030af19131c873e64d4e109fd9531d03764314542be983324c23f64546208fd95411066d6215230af593510cb3d544c4209f5
  | 16 => 0xc62550319fd9152cc73f5450c319f59654083b960906309f58a500427d64d4e10d7d4d42487755148430f64c0304427e6550d209fd95328427c658c5409f58a538427c6550f21af98853106cc624c530afd9152442be654ca419f98a5090f9e63904319f994219023e6494821d794e31c437a43d41429f99453443e8214c020f3d4a324cb5f6354f10cfd5254882ee62cc320db98854c87cc528c9309fd97420427e6094a31f6d49300c27e61d5120cfd8854442ed6508620cf952410c67d6014d21b7d8d544435f5350d10be98021c433c54105219f195304835d53d0620be58341842f86055121cf55041cc7ad5214841d714c30c427f6155332e7107300c37854d4121cfd8c544876f5294831e710c32106be64c86309f58254486fb604c620cf54c41d027f6590010b718931cc2de608ca319f58252107b46154841af986414435e64d4d21de104504867c6454b308f994414c73e5054241af58a41d033e6355020d754f43d0ade6290c43cf552400427e6095121af584431073f54d0a31ee907504c7756195110bbd89505067f60548109fd95400833c5310620bed8152507d45314542af98c53106ee62107209718d54442f96508310ed95041c86f960cca40be583424c35f534c510eed4250906bd63d0a41cf54841cc33e5490631bed81544cb3f5210531af58c52106f76150e41cfd8e54c875d530c621bd18542cc37661d4b10afd92329075f53901109fd8d519035f6014d21db98b530827561d5030f6cc530842bf64545309fd96321027f6454420bed81424cabe640c840cb153524c6ed6290621af59232d03b44194021cfd5153443795384010fa182210836f5294b41db14f524427d6414132af590200427d6394841d758e54487cc5314910eed81521075c5314910cf58c544c67c6154c42ee191100427e6494f10af19532106df6354910be983324cb7b5094141bd986400427e6194a30d7d905350a7e6510d309fd85540c35d538cb209fd9532d035e5350f208f19151c833f5410310cf144414836f5294a419f195325027e6195230d7d4f314867d650cb409f997414867c6590d20b798e408c2fb6050420be98053106f860484409fd97210c2bc62540419f59741083795314142f60c6300c2bd6214c41af191211033e5488610cf59641d02f661108419fd96430c33e5350e419f59053043b66110521cfd91510ca7f62552109f98e52083795414131cf95140cc27c61540329fd9541cc2fa60885209fd96329075d5310e209f997321037b6055110d758e52442bf604ca41d758953042bb6050a41bd584530827f654c9419f993504c67e6510d209f19643c43b56190a41b758c52042f761508409f191534436c52cc531cfd52414c73e548cb21d718d52d027d65d0530cfd5254083af324ca41dd544510cb3d5410621de90e50
  | 17 => 0xc030cfd5041883f36048421de590504875f53509109fd8554882f960d4a43ded81528c79f6350c41cf948410877a6514131be58331cc2de600c831b798c50d0a7e63d5221bd58440042f46154142dbd4932443b44148421de54f20482dc6348740de50950ccbb950140419f99432043af54d4910cf55351082be64d4532af988439073e6414e109f99442cc63d6494d10ee107208827e60d4931de8cb504865c6354b408f594329077b43d4121bd185438435c5310d10fa18121086f960086309f596321027f6054632b718d428876e5288020bb98a310875d53cc420af59353083b441c84409f180524435d63951329f99632486f561d52209758e54442f6618ca31afd9131087eb52c4110d7d4e5150b3e5354e41eb951320cbb641cc531d714c324435c53c4110cfd5241cc75e6414d10f64c030882ec624c410bb58b40c835e5310220d7553534873d65907319f197430427e62946409f588535073d5414f219f58a5090fd8524c030ae18142d02ef624c420cf94942906be6310841ee992100427e650cb40edd44414c35f53141219f582548cb3c64549109f98653882fa60ccb30be980314877863d4142cf104504c67f6254c10cf18a54c867f65d0e209f58653c835e6194c10f3988320c7ac4148020be58343043ae528c841d7952320c67c6454732bed81218833e5490040d754c329033c4194020ed10550c86bd640c840afd9151c827c6154a43be982429027e6394840ddd4651cc37843141429f58c514827d654c120ee590200427e63d45409f596420c2f56110f31af58253906be640c841cf552430c67e650c8409fd91500cabd6494b10e7d0c32906f96090530ed906310c76f524c1109fd8151d0b9c548c531b7d8d210439c438ca41af582531077753d4542be181420cb7a534c020cfd53524433c5310420be18142c43d5610c8319f18d51d02ec6148020db98852c42f7614c3108f593514c3ba414c030f9d4a104427d60d5221cf54841d037451cc520bed8131c867d6114132be58054ccb5f60d4d429bd89510c2be64d4720cf150304433f6454d209f986534833e5490f30cf99441c433e65904309ed95100435e5494e20dd14421502de6314442bbd8931c82fb60485109fd81548c67d6594c20ee540509073d54886109f595404433e6510620d7d4f314427c6454432de14f5050b9f548c531ded0a50ccb2f5290510ddd95210876f5210910be98221d035d5388410de54050d0ef96015031b798f41cc67f6510010af99050c867f6354041de8cb504c65e6315010cf55340c43ba4154031b6580310c2bf64486109f986540c2dc6348610bb58b30c835e5394810d754d31082f96010d10be58332cc76f52501109f99443c433c62d5110be980414c2ee618c832d79875350af96090540af988521073f548c531cf152414c67
  | 18 => 0xcf553108427e6510e20d754f100437a41d4131bd586100427d6590430fad8221082be6414e10cf996414c65f63551109f58f51502fb60486309fd9542cc79e5390e41cf151504c6bc6454732d754c530433d5254241af58e52907d86394031bb98b438867e6494e209fd8153107d9524c030cf99054886ad6214c419f993514c33e54d0f21cf994414c27e6590920cfd095010a7d6314b10de952500c6dc6354b10ee106200833e54d4321af991321075d5314d42db14b314433c41940309f590504c67e61d4810af98b509079d640ca31cf150314427f6510810cf95231c876e520c831d794c418823e6414f20de540508caf76150e319f58652d03766514542ddd47414c27f6054841db54832cc6bd62d0e41be98630c835c60d4d42f614f5050b5e5350e41eb551320cabe61104409f195418833e54d0b309f58152043795410320ee982418c37b6054f10db54b218427d6550f20db94a420433d54d08319fd8d50886f963480209dd85544cbb641c4210d314c52442bd640c8419f980535067e6014f2197d8d52442fa6090530cfd80544c67e63153209f99732d075f538c420cf94c41102f6618c8219f197434433e54d0a30cf54c53907ba4214142cf15141442f66448421cfd5143ccb765108720d754f51882ef6255130db544218836d52508319f98f540c76b52d41319f194315033d54cc820ddd95310c76d4314931eb588410873d5210430d714f414433e6415330afd9153483766114c20f658331cc2df63440109f596325067f65d0830cf988544c67f6550e20bed8142cc33f54485109f98353086f96088530cf952418833e540ca10de99350486dc63c8730ded0b5050b3f6590630cf951510caf56110b21db90f524435e6254c10be58332042ee6210520de59430c435d520ca31f6580318c27d6215110cfd5254887b96484010af191310867d650ca10cf150438c76d5288210dd58754883776154b41d754e428833d54d0a309f59643083ac6448421f654e10042f76150c21e7990328c7d96014d109f18951d0f5e520c4309fd8950d06fa6090540db149314427e61d4c109fd94430c67b6054d109718d54486fb6050d309f194324437451c8540f6c85300c27f63550209f18d54c833c5490520dd9835150bb64250441af185540cb3e6510410de949500c6fb604c630ddd4651c836c5290110cf551420435e53d48109f584540cb7563145429fd9443c867e61d4930dd545319027f6548530eb508424876e60d4931d7952328c6bd650ca41be580320827d65cc440dbd4b424c36f520c941be58032c827d6294f41cf95241c87da3254031e798e414c23e6414a10af99043106ee63c8621f6d95300c27c6454f10b798b31cc37b21d4121cf55250cc6fb6050d40b758632cc3da324c030cf990544833e54c42109f59632503db434
  | 19 => 0x1528c75f54d0e32b718d420caec6250d32bd18542c82bd6290e41ee90440083755114440b758f414c7d853d4121be986200836f52cc110dd545318c33e64d4532ed10731842bc6448430bb58b53d06de63d0831d78cb504caf9600c640db94120082766114c20de4c5500c6f96288020e714c414873e6315110bdd85524c33c6510520de8c7504c73d5454432b7d914310ef86050b41d654c30043794354332cf952420867e63d51209f994310833d5214a41f6905300c36e6214810e714c321073d5410f21f68c7504c67c6254f40b758c521073d51106309fd95414c67e63d5110dd597318c7ea6210020f90ca210875f6354f21bb58b404823d65104209f58c504873d63151219f5865310a7c654c8109f99732442dc64cc832be58042102fa608c010cf55032c877a42141429f98f54883b66110440db149424433c6510421cf153408827d6414f209f196424c35c6454c109fd9521086dc6350b10db149424c7da53cc010ab98853106cc624c730de90750486de63d4a40db14b324c6ec62503209f5805250f5f53cc921be583324c75c530c9409f59251883765110620bdd855050b3e5410520af59050c86be61909428f996414c67d6395121ed59651106ed620c020cfd51504c6f96014831de947208827e6314910d70c9500c73d5410e109f189548437b5094321ee50b40c83b8418c320af596531073d5490821b758f428c67f6548440bd185328873f43946439fd97428c6be6494d10cf90550c863d64d4520dd98453086f662904419f58653442ee620c621d754c430435d6214d42afd8943906be64d4a10af98732107f23194031be98630082dd6388530be18f20042dd62d0e32cf151434c2bd64c8621d714f43482fa60d4b31bd586434427d65d09319f583535076f52d0910d754c320427c6154b409d185544c27e650c530b798e5150afb60544329f994410c6dd638c832eb948521073d5310710cf59253442bd64c8710cf550328433f5414d21f58ca310c67d6595010ded0f504c6fa6384010cbd48414c73d5110640cf95043842be64c8421db50c524433d5290640de949200833c5210540cfd88544c6dd6314b409d587548833e53106219f99543c82d9638c030cf152314c7d8324c320ee90440c827d61951328fd9152443ad64c8621bed81514cb5d6114d429f59443883d6610c630cf953418427c654c4209f19432507e662d0721f6d8d300c2ef6254d40f68c6308433f53106209f996210c27d6214c109f995214c27d6294c40cf94841cc2dd6314221cf94a41842ef624c520d754e31c835f5394f10bed8132c43ae52d0b40bdd85420c2ec6254141fa94a200827f6354740b798a324c27d65106309fd94438827c6354840bb98b304833e54508409ed81524423c61151109f98b54087ba5014241f9ccb41086ed62cc120
  | 20 => 0xc2bf6454931d7988534427e6510b10d794d430433e5410b20db54a429073e5210640d7d4f324427d658c841cf948414427d6510a109f19532506f561d0f419fd96430cb3d6315110b718d42d067d60d49319f9825110bcd62d0e32cf953310837864d4131cf14a41c43ea2108010be181544cabe6114e419f582534436d6588420cf54842106bd6214041f5984320c6bc6250c41d714e435067d6394740cf952428437661d5031fad4820c43da314c030ded87504c67f658c9109f586538833c5490310db988548c2fa600c440b7d8d424436e52ccb31d794d31042bd6310a419f98c53042bd61cc841e7d4f4350b3e4194331af588415035c540ca31bb9884310b7864940319f987540867d65cc840af990320c33d5415010f3d8d320ca5c63548419f19521cc36d6508620e794f321073e54d4032bed8131086f56190f219f58e520873c5414d10b758f41cc77a31d41219f997218c35e5390010cfd52544879d63d4a41eb905210877a52d0020af583439073f6510530ed986429073e5454b31dbd84524436e52908318f59052843796094c32bdd85420c6ef624c740dbd4a425073e5110431cfd0c5150a7d6194343be98341cc3ba4114131decc5500c77a6014810cf951424c23e64148109f59630082fa6015031bed8141842bf644c5219f996434cb3e54d4a10de19250ccb3e5290710cfd48414c35d534c721cfd5254c873e5310510cfd925190f7b51d4142cf9524210b596014d10bdd85425067c654c510cf55054c43f3614c110bd587204427c6550f10be18152106bd610ca41cf55341c867e6195220cf58f544876d62152209f595438433f5454931cf990530832e5250a41f34c8328827c6054643cfd4e41503ad42108409f994310875e5414d21f614d30442f761541329f994314873d54884209f58b548c6f4614c1109f1895090e7f650c010be181314427d6550120fa8c32008377510c5409f5805150feb50881209f58f52502bc6454910e7d914310f6e2114121cf55250c87d753d4542dd5445110af860484309f58e544c67e658c5209f98e528427d61d4d42ded48504c7ce620c930af582419033c54d0a329f99053883794354031db587524433d54d0610eb4c8329067d6590620d714e424433c5390520db14a21842be6014a419fd81540435f6014d10dd586544875d53d0410ee50b400835e6414d21bd98732cc77751946309f99432482ec6244010b7980324c27e63d53109f99441083b8418c020de98b504c77961141429fd9742cc2f56190010dd98454c435d6510c329f58a54c42ed6294131d7587534867e65d0830cf95240083775150540bd987438c76e54d4931db98b54c873e544c4209f19150cc6bd64cc430d794f32d032f54d49109f19542c43d8324c020d754d328873d6590720eed53504873f5410d209e18
  | 21 => 0x604c7219f59052042ec6250120f6d8f504c67d61151329f993504cb6f3294421bbd895150ebe640c941db597218873c6494443dd54721c827c6588540bd58630042fa6094d42cf94c41c42df6350a32bb18943082be64cc531be580310436d6294d218f990530835f5414d21cf951420827c6510b10be58351d0f5e6315332be59740c835c6014d21ded4250d076e6214f219f99543c435d6494e20e7cca321076f64149319f1815390aef62545309fd9721102dd65cca32cf994544c6f9600ca10f658032cc3cd320ca30af59053082bd640c8309d58754ccabe608c841bd98443d06f965cc010b7d8d51083794254031f394832cc2de63d0932bd58442086f960d4843dbd8953482f9658c020ddd46514cb3d42542419fd96434827f6550130be19130c827d64d4f10de94b108427d61d5032bbd8930c83d8214c030cf15130443e962d0320de106500c6ef624c610dd147214c33d6195321af192215027e6494321d754e42042f86050e40af593310c7da538c030cf55242843ba4144010be181528c7b04144010de8c8504c77b530c0109f58f54442ee6294d10bd58732cc6bf6510420d754f4310bad5214a41cf150314875e530c2209fd8d544c67e63152109fd81544cbb45484110be98030443cd520cb30b758c428cb3c54d0010af583329073e5110430b7d8d428827d62d5331dbd4a5210f3e6255331bd98742487385414121d798b53442fa62cc230eb993210873e5494432af596421067e6590521bbd89544c73c5450521af98640502fb6048421cf553528433c5410910d7d4e214877b4314131d794c320c27f6055120b7d8d414c6ed62d0c42d70c9508c7da514c030bb189318875f6354b10be98342103794114121dd94e310c6f960cc720be990400833c54549319f194434433f5314c41cf55141cc6bd64d4720cf98f54486bb6054841cf15140443796584010cf950428cb5e53cc410af59052042de63d09309f99643043d7518c531ded8153442ef6254540cf95140c833d54d4032af99232502796094d219f99251c827c654c540be185300c33f54d0130be98351d0f9c41cc631cfd4e41843ae6210421e714e4250b7b6254031d754f31c867d6510c209fd8d521067d65c8430db583524c67e6495130d795253042bf6350a419f996404c33d5190740be98332c82f8604c620e7106314c7bb54d4131bd586425067e6550a109fd95320c35e524c030dbd84524c7eb6248020db953524433c63d51109f992518835d5314e41af191314879e54d0e32de553400835f538c940cfd51420867e6294d10af988321067c654ca40ed10421103cc320c421dd544410c3ba60d0b40afd9221503e4624c431b798e5050b3f5410a21cf146405023c6454730cf59641cc3b96014c41eb949429077565c42109f58e54c833e5450c20f6d89300
  | 22 => 0x420bd18542083f34044010be583540c76d52cc831af990320c67d6588730b7d8d41cc75f5314910de98354886be6414021cf55340c836b5214131d794d31082fa60d4732cf14e41c827e62940419f98c530827e61d4c209f98a53102bc6454931cfd5142c836e62152329f992528c6fa644c020cfd96418833f5210540d794d41882be6414930ddd5041086ee6210f42bb58a534427d658c620af590325077b61d4121af99441442be6110430cf10650087b954d03209798c520433f5310710cfd8654082ef6250d329fd9532042df6354b409f19153482be63908419f18953107ac4108620edd53314c6bf6050d4297d8d544827b654c030cfd52544c33f54953309f197430833d53906109f19743c86f5618cb21cf50e51d0be432d04219f990540823d65904209f9865310b3c5490d109f980548c77a6014c21b798032cc35c540cb309fd89508c73d64d4f21d614d304437b63d4131bed81420827d65d04319e59430042de6314c10d754c520436d65cc8219f58c524436f64d4910d794c320875e6454c10cf552414c2f965cc2309f18550d0e7c6154e429f592518c3786055131b758c428c23c64549109e982544c76c5288530cfd5041c86be6090a41af58a431067e6015010d71875350a7d6294410d754c320873c5410a21cfd50414427f6154343d7d4e214427d60d5332cf550320827e6414121cf94c41903745188520cf95351082bc6454420cfd4e539067f6590b10ded93504867e6590120db54b32102f4614cb41de9445050b5f530c520be181318c2ee61884209bd95210877860544209f992500867c6154c209f98e50d0af960cca21e70ca418c6be64c8521af987529067d6414c21b758e21cc27d60145329fd81520c77a60d5230db14b324427c6550810be19130083b46150b40be5835310a7e60151319f582540873d4214540bb189414873c5450b109f98252d073e53906109f58a534435c53909429f59441883ae6210a41de0c450486f56190e41cf941501079e6390730b7583438cb3565104219f9865390b7a60d48109f59742087b441c84309f994410867e6094432edd854210bd9614c0309f98a53c4378538c020be584200435e5350810b7583328cabe6014841cf151324427e61148109fd97438873e5450f31cfd96410c35d65d0e32d7d4e5390afa644c320e7593310c6be61904219f18554882ed62d0d32af191510ca3e6494d10cfd5040442bd6408310cf597429073d62d5121ee153504c73c6095020edd85425027d63d5021d7d4e5050a7d6095120af58b419073d5310510ed185321077651cc430d714e314827d654c910bd18542482df6350b21be58f10443b854c4110dd59441c86be64080109f98253c86f960cc420bb98a400833d6295210be18132103b96010710cf594410c27c6254443cf55242c86f8
  | 23 => 0xcd85100435c5350d21cf99054c83d8324c210b7584328c67f65487309fd81528c73d65104319f594438427d65c8630ed153314c67c60553219f58f54c823e650ca41bed81535073f5450d21be580420c2be64cc410d794c43d075e53cc420d7d4e315027e6510020cf153424427d65d0720bb588318867f650cb419f597329037854c83109f98453482ee62951319f99250cca7e6194b409f596431027e6015032be58253486de63d5221de98550ccb755114630b7d8d50487cc3208530f694c20042f46150b40d7d8d53887795208310ee98041883766115031cfd4f52106be610ca41be980421027f6454d219fd9641c82df654c030de597208827e62141439fd81544c35f5310d21db588538867e6315120d794b300c27e650c921db58b54886bd6494931db10c524c75f530c921dbd4f52442bf644c4409fd9532086df6350a419f997204427e63d5210cb548421067d60d49418fd954210b9f6350a41db94b32d07af62508419f98e53486f86050c109f995430827e6414532bb58b43d0a6e6294d10bb58843cca7e6588440be59440c827e60d5131db59432087cd320ca31cfd4c41082fa60d0c40ab588501067d6590010cf99253442ec62545409f99621443af5210510d794c32d067d6195220b718d21903f351141429f597321076d5214940e754f321073d6510640d714d314876f62548109fd9520082de6310830ed984410c27d60d4d42bdd85424c33c5450d329f58754cc37b6314142be58241c82be654c841cf95142cc67c6550910d7d95538827f65104109f59441042bf64486409f58e54c873f544c521be986308435d538ca10bed8131487796014530db190524436f52c8110de54b504c6f960d0f10ee59020c427d65d0520b7d8d21c427e6214543f3d4c52443b4410c721cf59641083776014542bb58b53102f6610c010ae983321067c6590c219fd94410c2de63d4a109f583544ca7c6354a40cf985540cb3f5314e41d7597430cb3d54d0420af181421075e6395110af19032106ec624c710ee18254083da614c030de14550ccb7a41141319f98253887b441d4021ed50441c86ef62503209f596431075c5414d10bdd854210a7d62d5130ee95310842f8634401097d95320ca7f6454231b7d8d428c27d6510d20d714d524433d5410c20ee990200433d5450330af191329027e65d01109f59721cc27e60d4d42bdd85425027c6154e409f98b548c67e6590f209f994424cbce620cb30d794c31882bd640c831be98332482ec63c8621cf552510cabd61d0841ded42508cbda53c8010cfd4d52106bf6550040d7d4c328873d54d0e31de54b20c425f63551329f98a531067d64948319e582544c73c6355020d794e328433f52105109f59542cc6ef624c1209f580544c67d6590c21cfd87544c73f5490430de58253c87e44108
  | 24 => 0x504873e5454321bd185428427f6588640d7d4e31843b66110431e794c431073f5014041d754c31d02dc604c431cfd51424873d544cb31cf151324877551d04409f189510c27e6014c21d758e50083756194910db549218427d6590421b798f42cc27e658c920be983410837451d4142cf50d529067f6454430f68c4504c7793214121d794f3204375510c7309f98251d0efa600c430cf552420837843543329f58650d0a9e6314241af58a501075f5310d10bed81430833e54108329f5865090abd654c8419f98e52d027e60d5010af58c509073f6550c419f98a538435c530c420ee107504c67d65884109f98a518c27d63d5121ee500400c37453d4542bbd95210875d63d4a10cf18e54083b764504419f98753087796094d209f58e500873c5450932db94832cc77b5094221d7d4c324427f650c620be181214c35c5494c10afd81321067f6510d109f59531882df6350a31ed594410865e6394321be583424827e65d0941be98354cca7d658c410cf993514c33f61950329fd8152d0f765314542db14a21442dc6354520ebcc93210778524c210be98241c835d64d4d21dbd95320cb5f53c41109f19442043785408310be982430c35d538c210af19732906fa60ccb40af994329077a60d5030af984410c75f5394c10bed95200827d6194243af58f42106bd64cc530eed91100427e65d0b30d794531cc27d6215331d798e544867f6155131af59053c87745154142cf551438caf96010530d794c32c827f6154b40d7d4f41486ed65c8220cf953320827f6254440be98341c827d6215131cf952418876d5250a30edd905150b3c54904309f5865010b6f52081109f992530cb9e53906209fd9743842bc6448530afd91504867f6154f209f99053486de6310030db14b414c67f6054f419f988520437a6094e10d794e308433e5290740ee907304c33d5490220cf952410c27f6054d21ded88504c73d5490430bb1895050ebe60d0b409fd91518c37953d4121be58332c43bb6050b40bd185434c73c54cc110de989500c6bd6090c41cf54c41c83784214121bd18520c435c6114d42af191311039e414c4319f993524c394414c4319f98e52c43775194440e798c50906fb6050f20cf94441d037b3254031ddd8f5150b3d5410b31afd95411075d5314e209f98851502dd63881109f992520427c6454c21cf996418c2f960147329f19742042f76150932ce90450486f96090420cf54c414873e5290440af986414873e51504419f58c540433c5410921d714f31487b954c4210af593315033d5490f30be181215033f54cc5219f18153886de6394321af98c501067f6590820af593329076d54d4910ee10630842be63d4841cf54b401037b54d4131bd58643086bc6448540eb90621082ee6290421de98054842fb60509209f9845350abd6510e41f
  | 25 => 0x3b44210721eb10721086bd640c930b758c540427e6214c21bdd8530442bd6394041ed106310c67d6494021d7d4e424863d6414f21b718d544876c52909319f181544cb5d53d0e20c794e418827c6054a43cfd52504c73e6510531d7440534433d5390640ed10721502b96014e41af99050cc73d5450a209f994425027c6454d21af98043907e76244010ded95200839f430c8419f1895010f3d5414420d7550534867d658cb419f1964204379514c320f354c32087b564d4542a798c521072f5210510dd544514c33f540c110dd544310c27f6255121add85321077a528c110d7d4e50486bf6550f42d794d408833d54d0a21cf59641842be61d0d42f394c320875e3254031cf550420ca746154d209f986500cabf614ca419f98e5190a7f6454b10be98332842f56110f41dd1805150be960cc821ded4b200427f65cca41eb50842507cd320c821e7907310c73c6395032d714c504867c658c810bb983320867d6015031d3d4c524433e544c832d7d4d32483795014131cf54d52906bd640c940de944300433e52d0841dd54451d03765288421ddd905150b5f53d0510af987401035d538ca20be181424437b6055120d754c324827c6454831cf98d548433e54900109f597434435f5454e20eed50504c73f63d51109f992528433e6494221ee980531073f5450010d754f218833d5415330b7d8d420867e65d0630d754d520427f6355121bed8f104436f5248110eb98a418877b6494031b798c51103bb4314142d758c52042f96090940ddd0b5150b7864d4121de59740c833d5490f31b718d21043d953c82209f58354086f960ccb41afd91210437a4314121cf990544437451d0520bd586328c7d9214c030cf94a418c33e5410431be18f20c427e60d5321de94e304437861d4142cf152434863e65105109f99743c86ef6250120cfd51408836d520c8319f992530c73c64544309f98f544867f62547409fd81544873d51904209f994200435d63d5010be18131086fa6090420de982544875d530c8209fd9442cc27d6294031db94a200437b5494332af98a439067e63d5020de582544867e6014d42be18152507795254031af593500ca7e6550930ee105500c6be64c8440f3d8d4210bba6010630b798c500877a3114131dd597410877551087209f582548c774518c530b7983318c75e51cc730de94f108433f6455031cf55342cc2be640c9309f98853842bf648c841be980414835f534c120cf54e41883b65110430b7988320c79d64cc530b798c410c73c5410531db98a534435f5394e41cf950418c7e960cca329f195211027e6094443d714e5150a7f65108219b58a534433f54d09329f1815310b7950143319fd9543483e82148020d7d92530427d61d50309f99532442ed60886209f595428c33e4154031f68cb304c35c5350921be994
  | 26 => 0x3c8220ddd8554c86f96014643b758f404c33d5490c32cfd8254cc75c53d0d10de983548833e54d08329f58a50d067e6588640b7d8d5150a7d65904319f986508caef6250620be18121cc27e62d4d41d654f300433f5190520db54832102de6310530be982328c27e6510c20ed90710043cc3208730d7d8d538835f6154e209f58e52902bd6490d42be18142c867d6315320d7d4e53c876e5210840cfd5342c427e6414c219f59250082f96090d10be980420c3d86094c10ded49500c7375110520be582310435d530c7109fd95218c27d654c440cf150414839d63904319f997424867f658c821cf1925110add6310431b7d95310c7b4410c4219f19743882dd6314241ed4c841c875e5388410af181439067c65885309dd85544c2fa630c010fccc7504c67d6295030cf14f4350b5c5388110d794c329067e63d5321de58053887766114b10bed81419027f6354b10af98b531067d6414d10be982210439e5314e419fd95325035e534ca20cd944411035d538ca409fd95329037b4214121db94b320c27c6054432ded91500c7d8318c3209f18954cc73e5494b31bed81428427661d5332f64c730042be6484110d798f52042fb604c440d7d4e534875c6254c109f98650ccabe6210c41dbd89544439f438ca41cf551320cadd63144429758e500836d6294d109f994428c67d6294d21cf59641c435f4394a43cf593514cb9e6314841cf9524310fb54110421db10c524427f658cb109fd9742c427f6454732ed107314c67d6510931cf99353c87d931940319f59353c867e6214c10c7553430cb7661d4f109f59632843b85414121fa087400833c6494420cf18a54cc75e5310f40cf55054882de610c430db14832443575314542cf54f42d037b5208010be983540c67c6454321cf152504c7ea60cca21ed107214c27d61948439f18153c873f5394c41cf153424873c5390510cf95041c867f6254443d754e30882f86050a209f18953102de6314041de580530873f60553219f994435067c6155020cfd5041cc63f65904209f18d51083766114e21cfd9154c83b8414c030bd98732887745108530be983210c2ee60c86219f195210c2f96014e21f514f5150b5d5314f21ed59321486786054d21bd98742107b44108430cf952210837643d4542bd986425063e6494b10cf15343ccaf46150c10de506500c75c31940309f5845050f3f5414121be582214837a53d4142cf950408833e54d03309758f54042f9600c621be58342d03d96388020cf992530c6f5618c8219f9825290e7d60149419f994544867c6054443be58331843b854141319fd9432c429d63d4a419f58b54c42f76150b30d794d30883db508c1309bd95200836c3294421d794c428835e63150309f59543082bc6354041fc4c5500c73e5490c32bb987208839c438c841db14b1044
  | 27 => 0x419f98e520867c65505219e59440082fa608c4109f185544c2fa6014031af590510cabe64cc621e7d935350b3c6355210afd91310c27f6355321ed984414c33f64551219e983548879e63140419f995430867d6014c21e7907314c27e6414e109f58b53502f86050a30ded53400827c6510a10bb58b50d079e5314c41cf95321842bd64c8510cf54e410436f6548421d794d31c867f62547309fd8152d06dd63152209fd96400c37a64943329fd96210437563d4542ad59441c867d6154c10dd54451ccb6e524cb40bdd8921086be62140419fd8152cc6f9600c710cf953438435c53cc921cf4ca51107b84110320b798f51c82bc6454121be98054ccaed62cc6209f987544ca7f63550219fd97410c3ba414c320cfd84544433c54c8110cfd53324867e6015110bd584208427e650c1209fd8950d0e7c6550f20db94832d077a60150219f5875050e7e650c841cf95232843b44290441e7d8d43d0b7b5154332db54821c436d5414931bed81211027e62947309fd96428c76f5294b319b189510c2f661d0c41af993319039d5310c41e759331cc2d96388020be58221d036d5290831af984415027f654c421af992524c76d52508109f596210c2be640cb30cf548419027f6550010f6101300c27c6590530bb98843083cf53d0942d754a328c67d6494f20d754d10042bd6484110be980320c33e52106109f99443c82fa6008630d7d8d54487ba41c4110de58f50486ef6250721be181428ca7c6154b43cf553430873d6510731de90950ccbdb31cc010d7596320c75d534cb40cfd85540837841d4131cf590538427e650ca40ded0c5050af96010c40cf552418c73c6195020bb980328876f6255120b7580318c27f6510e10d794e43882bd60106409f994325067d6194232cf54a418c7db534c110cfd5031443d8318c020dd94b410875e534c841f3d48328c73e65107209f1895190ebc6354841af984414c3765188430cf95220842be61904409f9825310bb86050a419f592510427d658c830ed90c41c873c63550329f58e5010a7c654c9109f98e548836f52d0110cf58354486bd62d0c419fd85544cb7960d53329fd9542cc33e6315121cf95052cc73e6095020ddd47214c27d650c810db14b414436d62d53329fd8154ccb5c53c85109f99641cc33e5450810be98041d02f561cca219fd96311033c5310520ed906104435f5314142fa88420c435d53906209f98e544873e54d0c21db54b42d067e60153319f98c51482bf654ca419f98a548c3b441c42109e980540873d54d0b31cfd51414436f52949319f595428435f53909109fd89548c73c4154321db98b54c827e6194043bbd954210a7f6550c419f992510836e5210b40ded95500c67d6394640d714e324437b50940329f592520cb3c42944419f99421482bd64cc7309f185548cb595
  | 28 => 0x58b5150efa60d0930cf981548436d52886309f980540c75e5490c43ded42504c73f5310540d794d518827e65cc5309f98f54c827c63540429f58e508875c538c940af189509077b5208310d7d88534427e65d0d329798e534433e5414432ded05500c6f7614ca109f596420caf561d50309f58453483b64390441d794c320423e6494010bb58a400835c6454e20bd984408436d530ca21b7193328cb3f6550441d754f210435d5308620dd14431503776544010fa103200835f6114d21db14a42443785414131d714e41443b441c8730be983418433e64150219fd94418827d65904409fd95320c75e53cc220af18d429067e6414b10ad98452907e55108420f614d30083d960cc8329f59643c427e6394a40cf952308435d530cb21d7588534877654904419ed95401027e65084309f9865210f3c54d4d10de953200435e528c630f9984218833d548ca109f587548836e524ca30cfd9154cc2ec6348421e70c8418c76f52cc531d7181530437b53cc0109fd85548cb6f5284110d754f430439d6414d42cf594410835e63d5030de149304433d4254041eb4c832106bd64c8620d754e320427d65d0f21b798e400c2f56110841cf54d429073e5490421f6105300c3b55110620d7d4c30c436e52082109f99630442fa60d4a419fd91530435e53cc721cf194410c3b84110020d798c530427e64d4d219fd8954c435e53c4010de58052c435e524c832bd98732d067d6114f209f98453082fa6090d40f68c930c827c60550219f98a540427f65cc841be18142906bd65d0e43ee90530082dd63d4b419f58f54c867e6295030af996321075f654c030cf950320835d5310f419f59252cc27f6550521db98b54082ee62d4341cf150204433e5410c20cf592538867f6154c10af191310c36c52d4131ed10731043b53294441ae580531075b53d4142bb58b51d0ebd6414e10cf55054087eb528c110db50f524c6dc6350910ded4b20c42f961083109fd9732d037851cc130edd8c41c867d6494730cf90e51107da53840109f18d5190abe6408310de992500c6f8604c521cf550544427e6415010de10d500c75d53880109f986530839f5390d43cf552410873d5488210edd0841c875f53cc120b758e408c27e6114943d754c32d06fb604ca209f18152d0f783254031ded5340c82ed62d0f20eed935050b3d5390c41d714e30443795014031e7905314c36d5210b41afd8943107755114443ddd85534827d6195332cf185540cb5e53d0a208f592538867d6295330af583419076e5308420dbd4a218427d6510530be59630c823d6494b10e714f4350b5d538c6209e980538873d54d0832af58e4250b3f5495310ded8a500c67c6590520cf982540cb6c62551109f987548c2ee6514931b7181314c35d6315010afd9151ccabc64cca41d7d89538827e6394a
  | 29 => 0x1483b75484110af593218c3e86050842d7d4d50487f35084110be5825150abc644c431ddd46314c2b461508429f98252cc6ef6254430ded42504cabd63d42419f596310c27d6508010de4ca500c67c6550d10cfd5042442f561ccb41eb90d4210a7c65d0b10cf550510ca7c6550110edd4e51107b46444010cf151414c67d6590520db94e21486f66190f319f197414831f54d4d21edd0a411075f654c7309f594321067c650cb10ded4250107776155110d7950324c2f960c8510d714e314427e65d0d319f99532c425d6594c109f98f528439c644c431d754d439073d6494221db190524c63d6494010afd95421067e6590720cf15120442be64142329f98c52506dd6310530cf906508875e6314d10cf54441d03d9538c210e754e41043b44108530af99331c433e6590631d759153042ed62d0d20be59610042f76150d41cf552308433f6315110be98f20042ec6254543ed98750906b46150940af191534433d53d0841cf14841c435e53d0410d754e300427d63550309f185531027e6550c10af993210c26d6295131bb58854cc35d5314f20cf952418435d534c310ded935050b5e65cc530cfd4a52907da538c210bdd8542c833e64150109f582520c73f5488521bed81328c27f65106309f19152cc6dd63d0330af593514cb6f5250931db54942cc3cf5388521d714e5050b7a6015232db94942cc3db634c320be18143c43ad54c8020d714f4350abe62d4041cf15241cc33d6295331d714e214875c540c930cf594418c65c6354b10db94b20c427d6550f10be181428c75d6510e328fd9151cc33c54d4d21d794c31c436d65d0a42be980540867e65d0430cfd4c41843e952080109f58654c827e658c440cf94a418c7b442104219758c548837a5408010b798c41cc27f6354720afd91310c6ec6255131e78ca418c73c4194331af99641443ba4114121d7181538833d5390421cf588544427f6510030cf15342087eb60484219f98e51d02fa600c5309fd91538437b53141219f99443043b441085409f594325027e65d0e209f98b540c77561d5331f994a210879f644c431d754c53d02bd60d0c41db94821043da324c020cfd0a51106be63d40419f59441cc36e62153209f19531902f66114e409f996218c33e5390421cf993514833c5490720de540508c73f54505319f590514cb5a534c3209ed81510cb6d6215330cf592520873f5414d10d7d4f504873d548cb219fd855290fb84114131be98031503784294031d754d4390abe62d0d42dd587540c33c5490930e758e414c3ba6408310cf94841c43766114c10db94b421037853c4110eb54942907e8524c110b798f51d033e54d04209f59541cc35e504c030d7d51530439c538c8419fd89500c76e6215330ae98053906bd610c8419f98f520435e5310c10b718d42882ef6250c209f
  | 30 => 0xbd640cb30b798f520427d64d4c10b75974390ef864880209f1815210fba41d0140f5d4f21487d9600c4309f98f504875953080109fd9442442ed6210621be58042cc2f8604c440d714d300833e54d0c42cf59441086fa60880109f19532c433f5490520cf94c418427d62d5131cf99053c833e54d07319fd815190b3d6414810bd1855250ef9608c940db58052443b86054841afd9221d02fb604c430f554731cc27d62951319f58a53907ae5450842cf55343843b64310421dd987548c67f65cc840f354f328873d54907219f596210827e63d4940cf95340c82ae6214041be98341d035e538c821b718d42c867f65d0420af59020442be6414a30cd55041c873c5290541ed98441503b461908419f99352842f5610cb319f59721902df6350921ed986439073c54904209f98652d0f6f5294940af58b41107796015320d754c5310baf6250940d78c9508c67f6454232cf550544cabd64cc7209fd9441cc3775194732cfd51324427e62d5331af990325033e5490820cf95141c87b55410421cf98b54442ed62cc721e790531cc35e538c8309f997424c75c5308510cf55343c873f5495120be9805190f6e520c830de58053c436e6215020fccc4504c6f8604c930d7597308c27f6354b40dbcc8514cb775108530db14820c427d60953329f997414c67d65ccb41eb94a429073e5490710de90e500c67d6550521d7d4e531073a4194031cf95231842f66410421cf18d54c86bf6254e41ed98441cc25d6510c32de909500c73d54c86109fd96430827c6154043cfd4d529075d5390410b718d428cb9e41cc730cf95043ccadd6314620be192300827d64d4c20bb98b438cb9e418c630af196321073f5450110cf552418433d6355321eed5310442dc604c730be18121c827d6414930d715232cc2bc6448720cf95032cc67f65d0d21b718d428c27c6454620ed50c5150afa6208010ed4c8410867f6550c109fd95321027e6095021ee906401027e61d53309fd97318835f64d4d42db583524437651d0430e7990320c6bd6090942d754d321077a6094d21d654f200436d524ca31de15320882dc6354141eb988421073d5450f20af19532907b84144010d715353442f860508218f592520867d65d0930f6d8d300827e64d4f21d7d88534875c63550329f58a548c2f76150820af18142503ba4350040dbd4a20c433f544c110de59150cca7f6454d20d714e52442bd60cc8419fd9420042f860504309fd895090f5f530c941d714f30083b554107219fd95428c33d5190620be19230c83cd5308620db94b42d02bf650ca41cd544418837a60d4c109f18d50c879c6350a419f996434427d654ca409fd94311035c548ca31f5946318c35f5354910af58f501067f6510020bbd8931042de620c930dd94431cc27c60546329f58954082dc6354841dd5445
  | 31 => 0x54032cfd50424c67f6254c208f191534433f6095032af59032c83775194530d7d8d534827e61d53329f990504cadd63d0831ed54c41087ad5448020cfd50434875c530c921afd91315027d61d49439f596324427d63d5120cfd51434c36c5414910b7982320c77454c8621dbd8f524433f54104309fd9442cc7b76150b40ded8b504c7ea6088620f354a328c73d54d0c20f9d04218836d5214910f6d51300c2df6348510de104504c6bf6150a41f5984310c37451105309f98753882b76150841d715353486ed62d04209f18151d0ef96090b20bb189314437754d0721bd18542cc75c538c540d7147314c2fa60d4f219f194400437a5490040cf55231c865d63d4810ae98053106dc6354941cf182540ca7d6014f21bdd85424827f65d0a30cf18254c87795014042be18530c827d6414530b7582318c2be640c8209f59631c833d6414930de153504c76e6514931cf550414c27d6550e21edd8c410873f540c9219e181544c7ac6250d42ee50040cc2de6388530d754d21883b742104218f996414435e538c0309f994300427d6548630be983518caec6254131db98b53c827d6294630cf950510827c61543429f59632906dd618c130e758e41cc33f5390621db94920c433f5190540ed94c410873e53904309f994544c3745150540ded50504c67d60d5121af19221d027f61540429f996325067f63540429f99253c82ed62904219f99742042be63948419fd89531067d6294f40d754c31c83345190540d758b5350b3d5310610d754e31042df63508409f583540c73d54880209fd8152907746155130b758f518827c65cc540cf550530837a60d4c209f58253d06be65cca41af986410c27e65d0120f60c6308427d650c821be98243cc3785454031cf552318437543145429f586524433e51d0240cfd925190abe6090841da149304436f5294b43af191210837a61943329f196428435c6194c109f583530867e62940439fd9541083795214131ded0a500c67f6550030b718d21c427d650c410afd9121c433e5408610af99032c82f562107219fd85521027f6454720de181534877051141429f195438833c54d01109f994215035e5390810ee95340c835f530c420cf906508c75d5314d109f984540c2f96010c30ddd85534433c5310720e7590320c73e54905109f99353c833f5490d10af99232d03ac41484219fd8953d063e64d4c20e7d8d42106bd64cc420cf95041882f9608c9309f992534833d5014041bb98831086ee62d4e109f988504c6f76154d20b718d429073f65107209f580548cabc6250f42d798153882776544010d7145314c3796508010de982530836d53cca219f584538833e540c721d794c31886f46150a40cfd96410827e6494910cf996410835f5394f20cf951500cb5e530c820ee580418833f6550040ed95041086
  | 32 => 0x2bed81429027c6510f208f593538423d65950209f195324873e53907209758f52843d9414c030cf95242cc67d65909109f194424427f64548319f990504c73e5410621cf948411035e53d0f41cf94841d036f4314931d7d4e324873f5214a41af593518c27f6054a43b799453443b66114841cf552300835d538c4219f98b53442be61d0a42ee107304c33f5490730d798653882bc644c530de50e50ccaf46148110de949300c33f54cc110bd58742d079c644c530e7105310c6f960cc910e794c418837950140439718d544827f6454c21cfd51324c76e524ca31af592411067a60d4f21ce153504875d53cc4409f58e548433841141219f996420c2fa60ccb31ded4c200436c52141319fd8151ccaf960d0e20eb54842106de6388020af590320833e5410430b7d8d505073c6590730be583518ca7e650c930f314c32887cc53d4910f6cc6500c73e5390740be58231c43ba414c210be58c40c833d54d0330ee15230442bd6190a41bd984520c2bd64cc841cf5095010a7d6550630be189401027d654c810f318d4210b5d51cc230de94730043b95488020be181214827e6414f10cf550400c27d650c8209758c52043ac41884209f59252082df6348620cfd5341487795014221be58353c873c5410931ee580418c23f64544209f98252906bd64cc520ded8550cca3c6454432af191315033f6454720be582420827f6510c20cf996414427d6294743be98221c427d65cc5409f997324c79c3290431d714f41486f561882109f59632d033d6590621be9835210ebc6448520cf152104436d6414910f64c730c427c6510e21cf907505067c60553329f195428427e6294643af990510cb3c63151109f185548c36c5250940be58041482be610c8419f588548c77b6454332be983314437a528c210db54b32cc35c53d4910cf18d54cc67c6354810dd947219027d658cb109f997314875e53c8220d754c210427c6054831d7d4e32886fa600c730be983434c3cf528c930af181529074c53885219fd8d54c42fb60484309f994420caf561d0e31bd98740c439f644c530ed10721c82bf644c530bed81310c7eb4214142cf550218427c6550d309fd8d510837661d50109fd81544c75e53148109f597215036e52ccb30b758c41cc2be63d0641ad984521077854c8010cfd5342443b441087309e58054ccb5d53cc3109f997314832f5294a419f58c52506de6388730ee50f5050a7d63d4b10d7d5053442f46154d42cf55350c87ac5290531b7982324c2be64d4e109f58a53903796254031be98332903756194d219fd9643042fa60cc931d714c434877b53c8010b718d428c73d54153319fd9731c827f6454c209f992520c67f6254630d7544318c36d5288410cf981540827d6394a10cf55321082bd62107409f583514cb7941d41319f191520c33d54
  | 33 => 0x82414c35e6494e20ee552300836e52887309f191520435f538c910cf54441082be61104209f196424c7b66110720ee952308439e53d0c41cfd0a51d02bc6448740bb189318c27d64948309f181544867e650c510ebd4a529077a6094f21f5944310c2f86384010be583328cbb651106209fd85544c27e65d0940be58430042de63d0630db597328877b4354332d7d4d300833d52d4041bb98840082f4614ca31d798c53c873d5490510be98321cc2ee62d0c219f98254886ec6250d429f195404833f6455230cf948418c39c6395032cf152434c6f96010740dd94f5150aec624c721cfd52548c2be64c8530cfd9154c873d5450e30be583328835e5390e40ee980411033f52542419f997428c2bd60148419f984524427461551209f9865090ebc6150f42f60c5300c2bd6490c439f593524427f62550309f99431c827d60950319fd89540427e61d5130af98a431075f6355131cf952408c27c6054841d7d4e204435d6315230de50a50ccaec624c6209fd95434867960d4f21afd91504c6ee62cc620cf54a41842be640c920f9d46214873d5490420e7951320cb3c4154031ed107210835e6154c109f58c515039d4310e40dd946419033e6395321db94e320ca7c6550d209fd855390bb45310421d794d30c433c6255020cf95042c875e538cb20ded9530082f8614c020bd98432cc7d9644c030b7d8d421067c6354910af583529075e538cb41e7107310c7b4414c7109f59742cc33d5410631cf94a41083ad524c841dbd89544c7e741c8421db54a428c359514c0308f19151cca7f6054e41cf552408c2fb60549439fd97218c27d6294043af580329073e53d0e419f58a511033d6195331dd94741d027d658c821d614d308437565d0641d714d214435d5314e42ed58742106f96310020cf552320833f5490610cf98d54cc7d8544c0309f9875250ef86050540d794f43d02ee62d03209fd94319027d63d45209f98a53d077943d4142de150200433c544c931db94e218827c6254740cfd4e414433e650c841cf152418437941d41219f59253c87755114542f6551300c27e6315220dd54451c827c6154232cf18e54cc7b45110520f3148328c67e6510e10d7d4f434867e65d0930eb58a418867d650c720cf191518cb785294031f394f208837b50940429fd9431d03775154142cfd51428c7da324c2109f98a5110f3d6494a319f58c52502ee63c8421bd58e310c73d54104309f18152cc73d4354843e7990324c2be6195020bdd8542d027f650c821cf54c418827d63d4141f6cc730c42be61904319f58e52d033e60d5121cf150410c36c528c931bb185320cb7a60d4e10f5d8d21087da544c030b718d42086f961cc010bd185420427e6015132cf95352cc77831d41219f98652cc27e65cc740bed81424c6f86050921d70ca51cc379501433
  | 34 => 0x427c64544309fd96320439f54d4d21d7550438cb595384010cf191534434c53d4910d754d21042fb6050810cf55121842f561142439f19732507ad52d0841af58a40503db634c210cf551428c27d650c840cf54c419033e6415231db886500833e5190630cf15241cc7ba6090540f654d30c833c5310510de10b504c73a41d41319f98f52506fb6144010cfd8c544c7d832cc010bed815350b6d52887409fd8d520427d62d4131e79524310e7e6014c10db14e21083b9548c210bb98a300827d65d0020db50f524435d5310220be98243c835f5394e10bed81315027d6414c209f996428c2dd63d09309fd89501067d6550932dbd4a40443b55190640b718d515027e65cc720cfd91518827d62951109f593538837960d5031d794f30c435f5390521db14a414c77a6015020bd58841086de608cb30d7d4f21442f96210320cf14e415033f5495320cfd53428cbb66110420e7d9131cc33e6510540d714c5050ade64cc832cfd91540427f63548409f986540cabd64900409fd91500c75e6314d21be583548867f6510420cf552310827e62947409f594420c33f5494d21db44052443d83294031af990520c2be63d4a41cfd805444376518c6409fd97319033f52d4041d754e320836f60d4910dd58453c875e5394620bbd8941487b441c8520d7951538833d5390520bd584500cb6c53886209f996318827d6590020be9945050b3d5490a329f18954c42f860487409f992530876f524c510d7d8d544c27d65d0e21d714c314831e53106209f19643042f96090640be580215035d534c440bb98854cc27e65508109f587544c3ae41c8220bdd85324c6df6354b10cf95132c87ce528ca319f594211027e60d5030d754c53082f76150a10f34c8320c35d534c3208f993514c27f6550c32af98043106ed62cc521ded425090efa600cb309fd9732442fa6290040db949429027c6454f20bb588540435f63548419f9865090b5c6494e209f99743086f960d0e30cfd53424c73e6510510eb593210873d54143319f99532502bd640c9209f597430c2f96010b209f990530427c65509209f58251cca7f6254f10cf951218435c6494c10d714e504873c5450120af593514c27d6550c219f185534827d6510c109f592524433f5495110dd545310827e6094642f310c328873f54d0c31db54b320c33d5415232cfd52434c67e6294910e7590324c2ee62cc721d794e31086bc64487309fd8d548836d62d4e219fd8950cc7754214542af993215035c6294c10cf54e410833e5490c31be58332c86fa608c710b798e204827e6590831be983320436d5288730b7191320ca6d650c821cf951438c3796094910cfd5242486df6348630db14a324c27d65cca419f195314827e65cc540d7d4f434427f6550c31bbd89318875c5390921be98042cc35e5390e42ee5
  | 35 => 0xf5250910cf94641883755114642fa084200436d52c84409f58652cc2ed6214443be5974008378538c320ded4250cc6fa6090c209f18853482fb6048530d7d9353487b66110520f34c8320c67e6414d10db14b214427d61d4930cf59351483ba41c8120af58353107b86050841dd54721902ee6295110d7d4e414427d6215310be98f20c42be6190530ed10721d037960d4b10f6109300c39a414c030dbd4942503b46194841ed10421c82ef624c7109f98753c839e640cb309fd85528c27d6294740bd18553502dc63509219f19151082be640ca10f6501300c36d5214b10be58332906fb6054931ed98e511077a538c210ddd4651482bd64cc610de54050d0af96210020db14a324433e54d0b21d614f5050a7e6215110d754c41883b44184110e7105314c36c528c531dbd0c52442fa60906408f59053c833f54d0f32d754e43c833a41d4121bb58a4350af56190c31de5475050b7842d4121af98a421067d65908219f99742cc6b66294441cfd83544c73e6394441be583420433c6494743de4cb504c6df6354540d7980534867f6354620d754e300827d61151209f197428427c6550430d794f408833d65904309fd8d54886fb60485409f992510c37565c4010be5825350a7c61553329f997420c79f43d08329f98a54442df6350830af59032d027c650c0109f586500cb3f5390521cf152434833f54d0010eb508420833e64d4c20af98641503b64144010ed946419027d6508740ed10710042ef624c6409f19521902bc644c730de94550ccabc6050c41bed81439027e6215331cf950400c3e76248421e70ca414c3365110620e719131cc2f56190d41af593214867c6550932bb588408833f5110520af59050cc73d5408420f398e20482f661d4a40cfd8b544433c6454732ee582415037b5094143db14a20442be6110520dd944219033d5450831e718d540cabe6510540cf14b42503d6534c4319f59642c43d6618ca31d798c54882fa600c720d7d8d538427d61d52309fd9743442f464884219f588538429d6314841bd18542cca7e60d50319f583548cb3f54d0220ed593318c7ba6090530b758f424ca7c6354241eb953200836c5208610cf953420c6dd6310830d514c5150afb654c0309fd96410c75f53145429f98c540873e6415230cf95142cc3cc53d0942cf95243c873e5450a3097994534427f6510c21bb58a544433e51104409fd85520c36f52cc510db593524c75d6315231bed81314c27e6215230d7592530427d64d4931be18121843796214131b7987430caf960cca309e582534825e6514d21af191218436c52cc940ed94441102dd63140219f5845350b79650c010afd9131cc2f96008530cf550548c2de6314221be58042083db534c020d7d4e30443e83048020bb18121086be640cb40f6d81314c27e65ccb10d794d52
  | 36 => 0xcb20ebd50524c75c5354121ed107218433d5190430e7150534427e6508110cfd87544427e6315321cf552414827d6394642af58b539077964d4121dd544518837a60946309f595328435f538c510cf18154083795154332de90f504867e62d4540b7983310c73d5210631cf550410873c5450a32dbd89538873f54081109fd8553442bd60d0441bd9865050b6c5288540cfd8b544867d65d0b109b98a52443d9538c020af98f50906be6310c41d794c308433d6590620be98052d0eee62d0620b7d8d4250779530c310de504504c79e63106319f9835150f6c528c1109dd85544835f530c610b798f548827f6155010cf180544c67d6114d40ded4e100433c5310540be99230c827e64d4d209f984544c2de63882109f98e54442fa6015232cfd91544427e6590b319f994315037a5108010de90f504c77960d4930be583328c6f860507309fd9741c827d64d4d21e759032cc27f650cb40d7d4e534433e64d4a109f587504ca7f6510f10be98321c836f520c931ed18e511067d6015331f64c9300c35c5350d41ed98752106ee62144439f58e51086f8604c431de55340c827e6115320dd584528435c5310110b7d8d210867c6355220db94832cc33e5490531bb588438836d5290810af990204436c43d49319f98a548c67c654ca10ee905200833c54d09209f58a54cc67c63550209798f548867e6494c30de4cb50487d8604c431f314a314c6ef6244010af99352cc6f96090410e7107314c27d6094743bb98853d02b86054841e798c43906ec624c421db980524c67d6510c31cf54c41043b44108420be98c20042f7614c810ddd4731483786054a31d758753443b8414c3209fd89540c67f6508730d7d4f30082f8614c210be19530442dd610c831dd5445150f6d6215010cf153434c2bd638c841ee904300427e6194c40af99321cc2dc63505319f987525027e62d50109f992538873e6494b10d7d4c315033c6590431de982530ca7e64940309f98650d0b6d5214a40db58a53482bd64d4b319f99432c427c6454c10bed8d300c36f5294b30d754e324827e654c810ed54c41c875753d45429fd855090b9d6314841b75924310f3f6455030bb98b404827d6590a109f596540c77a6414121d7586538827d6588010b798f52d067e6590910de59440082f46155130cf90c5150f3f54c81109f58b538435d63d5231be980410433d54904109f18d529067f6454d109f992508c67d63d4910ed98a511073f54d4d109f9875050fb841c4110f614c30c427d64940309f99721d027d650c020cfd52540c33d5190730d794c32c86be6414b31bed8142cc6f56108010be98031083ea2188020eb949321075f538c521f3588430cb5f6414d10e794d439067c6315130bdd85544cabe6094c41dd544519027f654c120f594731cc37a51c8010eb948421076
  | 37 => 0xdbd4a214c33e4194010dbd4b414c77b42d41219f99743c82bf658ca41bd191210873e5488020cf550540c2f9608c820e78c8418c6df6350831e754c53107b84114121fa983328cb3c65107309fd94328433e5210631cf98a54843f051d41429e980548ca7e6314121de58054cc35e538c740db94a210877b6055320cf553530827d6414e10cf94c410871f5414d219f58e5090b775194432d714d32482be6410841cf953210833c54905309f996418827f6548640be98032c82f86054943d754c32906f66188210d794e200433f54d41219f987504ca6d62951109f595329077761551309fd9153c83f1610c010ed10421482f561d03109f99053c873c54107209fd94329039d5314e41bb988548c27c6354442b758f52103d453c8521edd5321486fa600c5209f98850506fa6090410af58f419067e6510120d7d4c214437461551329fd9150cc77965cc3109fd8d509073c5450c31e754f43106f960cc821d794e32906be6114a419e982534875d53d0f41cf9494210b6c5208530cf990540c3384194031eb54a429067e6014943f9cc8410873e548c820ed98441d027d64d4e21ddd475050b6d520cb309f59743c82ee62d0721cf59441482fa60c8420f314e21487b66114e41f6d8131cc3ac5414931db548520427e6395221eb94b421067d6590030f5d85314c2bd64d4a10be98052106f5610cb10ddd8b5150bba41d0320cf90550cc76c52905109f597400c37b4354031cf94e41042ef634c832bb98a504c6be64d45209fd8154cc75e63d52208f99641486fa648c020fa88630082f6618c2109f586540cb7950141329f5825190a7c6154242dd54641902de63d4a41cf95252842dd63d0b30ddd44414c35d53cc320fa4c3200835c5310510fa98b40c827e6014c20d714d304827e65cc120bd984400427c6590b10ebd5221486f4614c921cf54e41c87ae4188120d794d10043ae5448020cf15053487da434c0309f18950cc73d4394443be58352d06f565d0421fc584200433e5410210cf95041086fa6010b209f19432843b960cca41dd984548c73f65553219fd95210c27e60150209f58252d0e7d650c941ded0b504c67d6195130af9974350b3e5490440bed81430433e5414c20d794e31c82be60cca41d714f5048677654c431dd544514caee6214343be98352d067e64d4532dbd4a528c75f53949109fd89544c73d5310e419f582528c6dd63908329798c54c827d65d0410bd98643c433e6510520ee105300827d60d51319f9974350afa6010d10bb58843c86bc6350841cfd4e410876c5254131ed95310842ee630c821be98342483755114742be18142106f46150a21be580318835d530c210be582210427c64540329f584540c3796015310cf14e41842fb6550040b758f51c83b56510721ce553400833e54d0a20af59032842f9608
  | 38 => 0x6318c33e5450e329e98354ccb3d5410610dbd4b324437b6214121be58042843366510421be1815350a7d6510010af98b539073f5454121db148325033c6590421db98852443355110430e710731cc23e6494a31d714f31c43b84190040bbd89504c7b66110610d754c30882f46150b109b58b538427e62d4c10be98031d03785194332cf952414c27c6510930d798553882de63906319fd94420caf961cc3109f9805150e7e6394910de580540877965d0020cf9464108379518c020cf15131443756114e10bd597318c73c5490110af19131c827f6590730b718d421033f5094241cf98e54cc6de618c430cf95143c82bd6314a41cf996414873f5450e21cf953430827d6590c32b7594438cb6d5214a438f990540836f5290931bed8121cc27e64d4910cfd90515033e5310430d7d5353442ed62d4630afd8532106796014e21dbd4a520c27e65104309f5845050b3d51106209f99251cc27f6354742f694d300c3ba5450040ded4c5050a7f6550a10e74c832906f8604c920db588548873f54481109e195304433f53d09409f58654cc33e548c020ebcca418873c4154231be58e304435c548c9309fd8550d0b5f5494c10db54a42cc27f654c020dbd4b32503b76444010cfd96414c27e63d5021de9845050b9f6350842be98342d025e63d52208f590530867e63948109e597300427d650c420af593211033e61950209f597428c39c6350841d64c5500c6fa600c820f64c530442fb6054542af992504c73d43548419f59441c836c528c5109f99253486bc650c841af1854210a7d6414f10e710531cc2fa62cc130eb58b43d0b3d5448420dd546319037a54141219fd9431042f96010f30b758e504877862940319f988530837a3254031d794f210433d5494a10cfd9554cc73c4194221bb189438875d6395110e754c410427d6315321af99331443ba5488020ddd465110b3f6155331db94c524433d6494b109f988544833e5410610ed907318c6bc6150940dbd4a5290f7551145409b988548c2ed6290f32d759632cc27f6054443cf55150c86f960d5332afd9131c82ed61cca21d794e320435c534c7109f18153086be6094841e7551320cb5e53d0c10cfd4e41507f251440109f593504c67e60d5121d7d8d53443b66010721edd8654c86796015021ee906304437b50940219f181548caec63c8421bb588310873f6494432af99052cc33d50142419f58c528427d658c6409758e544875d5310010f6583328cb3d5410210de980540427f654c8419b98a544437b5494031ba58840083db424c030dd54c5150b5c6154e20d758e544c33c6015121ee18154082bf6050a41cf15041cc27f6588010cd59441c87b554c4210ee907400835d538cb21bed81321039c3290730e794f43d0a3d64148109f99542c42fa6010820de983540c67c6255330
  | 39 => 0x427f6588430ee58241c83793214131de54050506be64d4732de58354c82fb654c020f658c504c6fb6050a21d718d544433b54d41319f18951cc2fa60ccb10de1445050a7f64548109fd9632d035d538c821cf14e410867d6294643afd91214427f650c4219f59431483da310c010de18c504873e6515121af99321c836d5314910fa14b504c69f6350a41b6185300c35e6314c20ded50504867e6590d2197d8d52106bc650ca41cf54c41087ae5490842f3d4f52442bd64d47329f189544c3b543d4542f390d320cadf6350940ed10421d03b65194041db548524c67d62d5010ee952300827e6015321af59321086dc6350841cfd0e51d0abe6494e21db58a544873c5310421d7d4d308437853c4210be58430c42f9600c6309f987535033f54d01109f98251d0a7e6114d40b7d8d4210a7f65440109f98b544c6bf6454630be181314c2bd64d4730de18b504c67e6115031db988540c73c4194231be181315037b654c030cf586548439d6310631cf55041c86be64cc721ee10740502ed6214f409f996319027d62d4540be58042d02bc644c4209fd97430427e6014d21b7983314c23f6454d21cf94e410837551d0740cf950414436e6214c20db548528c6f960d05109f59253486b46150b40dd54421902f561d4a43cf58251106bd64cc7409f99732903b751905409fd9621d02fa6090e10bb988308837a60d5210db54852d067e60d5231f5145314c27c6254440ed18a51106de6514d21f618d100427e62d4d40bb597320867e65cc920edd4c410873c54cc5109f996324433f61151219f58e509067c6154843cfd5041483744314542db5485250ef860507209fd95421027d654c7409f988534431c5414d109f58a548435c6414d21b7580310c27d6195131fcd0510043d8604c530cf95232cc65e6314c10bd584308433e54d0f31cf95241082bc6250441be58a30c835c3214530dd984540427c6454a30cf953538433e63d5110e794e410433f5490930cf15041083784214131b7d8d525035f53d49109f194200427f6354a41de14d30082dd610c930d7952324c33a4114131af98e501077a4154031db14821442dd63d0630eb58841c827d63947209f587544835e538c010af583429067d6550810ee983529073d5290710b7d8d404c33e5194041de54d100439f6350940de5405090add63c8630ded81544863c6454d20af19151c83db314c110dbd87524c67c6510431f5d8531cc35b3154031d7d8d534867c6154830db94a42cc27d6394342d7d4e325076d6215031edd8041c87e94048020cf98154c873c5450d10d7d8353442bf644c420e9104210835d5310410cf594321067f63543429f594218c27f6054f219fd8d52d07ae41084209f980548867c6550e219f597430827d650c620af99331883786394031cf95041c436d520c830e710
  | 40 => 0x65509219f594310867d61d4940af590500cb5c538c921cf94a410435c53d0d21af191100427d6588440d794e310437751cc540dbd4b504c75f5390d42bbd894350abc644c520db99452442be6114841bdd85429027c654c840dd50f5150b3f54d0d21cf59740903b96010440ded93504c73f53105219f59251c823f6454430cfd49501067c6254231bed8142c433f5484110d754c431033d6015110af593518cb3f6590720ba98332886f56188010de19050487ce53cca21bd98740443b641c8621be58021c833e5494e10cf553424c33f6550f42cf594418437a5184010de90c504c75e650c9309fd95314867d6294c418fd91518c36f5294b10ed109411067e65d0d20bb189314867f650c841cf54b50907796314121ee582410835d518c430dcd445050a7f6550930cfd5241c827e65cc420fa583324ca7f6155020db54942902be63d04419f98a508c73c54d0d329fd8153443b651d4041f60cb30c436d64d4910d794c51882be6494a31eb148414c75c530c110dd987540876f64149109f189540c2bf6050441ebd8942d027d654cb40afd9131482bf6448620b718d21882be64c8420d7d8d53083f230841108f992530c73854d4131bdd85424c67c6590f20af19151cc33d5490b209f597320435d650ca31b718d41cc76f5288510eb98a41086f86050420ed9085150b5c538c610d7d4e435033f6155032bdd8532886f96094f21cfd51434caf86050830d7d95320caf96015021d754c539035f5410c32d754c31882df63509329f984544ca7d65d08109f994328433f64145439f9875350b7b5094332cfd84544c7784394332af59050086be64cc630afd85421076d528ca30ed10421842f86050e30dbd4a215033d53d4a419f18d54042f6610cb109f59732087ae640ca21bb98b314875e6054c10d7d4d214436f5414910af58343d0afa60cc8329f195204433e548c420cfd5241082bf6050e41ded4c30c435d530c840cf18954cc6bf6550842db150524c775518c630b758e400c33c5450910dd145214839c6354841d794e320836d6014931be583324877a63540319f59643c827c6550831ed582511076d54d4931cf990544875d53506209f196438833d54d4e10cf14e414877a3154031ded81544cb3d52540419f99731882be60d0641cf905508876f54149319f58a510c27d6548740de14e30442ec62504209fd89509073f5110540de18153042bf644ca40cfd4c418867f6054643be18132d02be61950329bd89544c75e534ca21be58031c867c6590f21bb189510c37953d4142d718653882df6350930bd587431075e63d4a10cf14641502bc6050b40cf99641c42fa60d0d20d794e410435c53cc120bb58a30882f9628c020cfd50438c67f65cc7409f99442506df624c832b718d214435c5414d21b7d8d418c27d6550531be596308
  | 41 => 0x20cfd5240c43765248421d78ca51cc27d6594810afd91218c27f6354442cf550430c6fa6010710d7d4f4250b3e6415131d714d414434f53d4910e758c50907ba6090420cfd5041842f86050831f618131cc2bd6094841cfd91548837965c83109f185540c2dd610cb30af580321073f5310510cf55143cc6fa60886209f18953c433e6415132af993214827d6510910de50c50486bf644c740cfd4a41042be6414f20cf948410827d6115320bd18543c867e64d4c21bed8131082f76154d40fa08420c433d5490f32b7993328cb795014243bd98443106f96010f20db945210875f6414d21b7d8d40cc27e65cc841de583548873d5494e10b618d100439e32904319f994414875e53084109f181540c73c544c5219f19732503da318c110be98343d033d6115121dd987520433f5410730cf18f544873d5450b30cf94d431073e5410f30f958b41c873c6494742d7d4f214867f6154c42e7d4e53906bd64cc5319f99643882be64d44209f58e50c867d658c810db590524c7764214542ddd46214837454c85218f19153486bc6448640be18142507376414542d718353486f86048640ed980410876c5290940cfd9154c427c65cc8109f987540439d5390620cf596410876c6255131be582430c2bd6510a41ad98752107ce538c832afd81531067d6394442be58021082796094f21eb98841c827f65104219f99621d02ed6008620cf552430c27c6550130be58342c427c64542319f597325027d61d4f209fd81524437b4214131de4c450487b854d41219f18d540867e6495110cfd52544c67d65908109f58a5110fb660944419f992520cb3d54d0e32f914b314c6bd6394841cf94641c837b53d4121bb98a320873e5490c30db98852842fa60c8610cf550400835e538c0209f9835250ef4614c8419f992508873c6395321cf95030843d4434c4319f59741cc2ee62d4743cf94c41c83ad640ca21cf597439073e5490521de10f5050af661d4a43bb988540427f6590b30af586421073f6454630bb983210867f6510c10bdd8542cc7db53141429f59520443b76448421ed994410873e6255210cf194414c27f6054c21ee98241c833e6510730de993504c67f654c410cfd0d529075e6514d42de10750486f66108210bed81420cabe64d47309fd8153886bf6150e41cf951538433e5490731cf950210827d65085309f982548c73f54c8521cf94c41d036f5294841d714f214867e64d4e10cf58f544433f5494121f518d21086f46150b41bed8131c835d520c831eb588414835e520c6309f58253487b46150e41de14c50486fa60ccb41be58031087bb548c110af590530879c3210431cfd52324867e6494820f654d100433d5415332be98042d027f6510e219fd9432043b8414c2109fd96410867d6394440ee90750486bd64d4f219f98a544c67c
  | 42 => 0x7906310c2f561d0a21cf153324436e5290a409f99642c42bf644c610b7d8d42cc3794214121af993310873c6510630be983328867d650cb109f592530c36c43d4910f398c328867f6590d21bbd8120082f96090a40cf95031842f96088710b718d420c27e654c5209f59352c42ee6210621cf15143486ec6250e42af597439075a3114131f6d83314c2bd64c8430de949304437b53c8120cf183544867c6550c20db58f52442f86054d21e7904318c37a6314142d7580534427c6054a31d75805350a7f6454432be18153507d9300c0209fd96321067e65151329f592510835c5390521dd987530873e60550329b189544c33d5310520afd9732907b75310721ba58a30082be640cb319fd96320833f54905219f594219027d65d0d21b7596320c69d6314241e7993318c76f520c910cf54f4210a7e6094c21cf98a511065d6315010af990324c75d53cca21be982534877a4294332cf54c410827e6510630ee980414c27e6414930eb0ca418873e54506109f58e51d0a7d65886309f185529033e52d0b409fd8154c867d63d4142af99032902f960d0c40fa58a300833e54d0a21af996414867f6354341af98641082f761508109f18d51d0a7e61d4142bd185524c39c5390510d714c32887e5610c8219f19443883b760104219b98a544c67c6454021be98032842bc644ca41db5485210ef96010c20b798f42cca3f6454732cf196410833e5450c32f698032cc3da538c020bb18931103b95410020be983520c77a6154031b798331cc33e5150040cf553420c33f5290541de54b20042bc644c740bb98032086df6348440cf583544435f6355110cf55041442bd64cc6409f582518ca7e63d4142cfd52540c77963141429f994534829e6314041d714c5150bba42d4142de94d30443b661d0c41d7552538835d5314d40cf953420c27c65507308f185540836f52c4110afd8d50107b65110740be58241c427c6155120cf55342cca7f6590e10b758e300c3d9300c320be98c20c427e63d5010cf551428873c54907219fd8153d0b5c530c510fa58221883ba410c310cf55030842ed6290c32b718d218c35d530c010cf592530c7ea60cc821cf550410827d65905309f5835150f765450441d7d4f308433e5250841cf548418437965cc230b798c51902f76155130db58b53882be64cc6319f592530427d63152219798e53487af5254a41decc450486fb6050b419f99632d06ee6210f32cf153314876d52484408f99454487b4414c510cf95350cc76c52485109f194424c7d86054c10f5d05310c67d61149439f590524433e5190730cfd51424cb5f61d4d42bd9945150b3d5454e10edd8554c86f8604c730af59641d033c6195032db98b530867e65d09109f195428c27e62943419f58a51cc33c54106108f59353c86fa6010a10f6182310c3eb3048
  | 43 => 0x304c36c52105319f996424ca7d658c8209f58c540867c65505319fd89534867d6294d20bb98d210877b6054730e7153534427d654c640d514f5150a7d62d5031cf95153c873d54907109f18d54842be6190520cf94a410c73f6510431cf95121083db604c431b7588430cbe7624c431be580314867e658cb10d754c31043795454031f68ca500c6be64d4432f618d500c77a6454332dbd89510c27e6590a31be980510cb3d5410010d754d328827e63d4141ad98753106fa608c930de58a500c6bc644c6109f596438833f548c521d714e31486bd640cb319f19532107cf430ca21cf550318437953cc3109f594210435e53cc6209f990534837954141219f98254c86fa6014442afd8152106be6394441ed50c41c867d654c840b7d8d514827f654c720d759353443b65310721fc586308423e650c8419f997438433d54151219fd8554cc27d65d0c31be18a10043b56294441cf15050487786054a30bdd8520c42f7614cb41af99321d02bd65907219f1944348776514c630cf99641cc2bd6014a419f993538875d5350410be181514ca7f65cc420d794d438827d6590831eb988414833e54508329fd9743c837a42d4142bed8d20083b441c8640cf596410c73c54107319f19153c877463145429f58f54886fa608c940af59331042fa6090710cf593538435f5310110dd584530833d54506109f59741086f76150e10cfd52540427e60d4941ce107504c6f66114c20cf552418836f52d0510cf944418c27f6510f20bd987324867f654c440be594200437b63d4121af19121042f46150e41cf99053c873f5450b10be583321027d6494421d794d31883786414131ee906500c76f520c940ed10531c873f63d5121d7193534873d5450c32ee90730042f9608c6309f98854086bd6510721cf95353083b454107219f18953906dd6395121d754d308833f5390721b7987308c27d65906309f18953d073e5350f42bb98b41487b86050842be580410437a538c030db54a321067d6590c42db98854042fb604c520ded4650ccaed6210d219f59353c83b86050940d798f548876d52082109f19541442bd648ca419f58e50d067f6550c209f98e500835d5314e21cf151424867f65d0620d794e40882bd640c931be982218c35c548c932cf98a540ca776550441dbd48218427c6254c10db94b328435d5310a20db54a200437b6054841d7d4e538877761551219f5885050f7b5094343de548200433d52907319fd91538863e6414c21cf191510ca7d6510b30af58b50906bd640ca40bb98b51cc31d5390620d7d9153883e65108420bed8143c42be64d4620f5586328c6fb6050510e7d50534873d62944419f99443c873d5350b40cf55142cc6bd6510420cdd8554c873c5450e21eb10720882f46154132bed8121083d9624c030d754d408827d6214543e
  | 44 => 0x27d65d0d20bb58a200827d6395220f514e104427d6094c41af993518cbb8410c010ed984414c7da600c630ed984419037460d4542f5d45314c27c6354a10cf990524c27d65d0620be587200436f64d49319fd9621102f861480209fd9631903db534c210cf550540c76f5290940db94a32107b54210721cfd8e54082dc6348421db14620482f76150b32b758e5150a7e6014910cf54b409027e6494f219f181539073f6454d21cf18a54842f965c4210cf50e51106f561cc9219f597400435d5310e21ddd885150b3c5488510e7d0f428ca5c63544209f194300827e6015121d714c325067d6295120af99252442ed62d0e219f990540cb5d6214d109f596434439e3290530d754e43882f86050930d7d4e535035c5350110af99250886f9600c9109f995424c798414c030be583321073c6590520dd544411027e64947328f994414877a5294031cf54441cc2ed6290e42af99021502f960c8430ebd4a414c6dc6350941be980214c27e6510620afd81401035e5350a20cf94e41c86f860508429fd9641042f963d03209f98454882bd6110a41af98e529073e5410821bd584431075f53d4542cfd8354487745110520cf994410c73d5410410ae983529073d5450832de181544cafa608c630ddd4741482bc6454620cf980544c75e5348410cf982511073f6295331db14a504c73d6255331cf95043cc6bf6448421cf55152cc67d61d5020af59351482b86050a41af993218433d6055032cf95332cc79d320c841cfd4a41c433f5490630b718d420c67d6094a41bb58b51cc2f46150e31f3d8d21087b7614c8419f59250cc73d5454331bbd89314433d5415231f6983320cb775194743f90c8410873e41542318f993528427d6094f42be181425033e4194040ed10731c87b841c8120d7d4c414437661d5221af19632906fb6055131af984414c73d6510630d7993534427e6590c21cfd9151ccbd9300c120cf153424c6dc6354b409f58254c867e6215031b7582310c2de61d0e32de953504c73841d41219f98b54cc37651d0440cf550420867f650c020fa148504c6fa60085409f592530c6bd6408540ced50504c6bf64545209fd9150ccb9f6350d42d754c534827e6495121cf944418833d5415120db548521079c3210530cf55031c86df604c030b758f51d02be6294441cf196414c2de63d5010af593510827d6395130ed906210876d6114931de14720483746154841be18141842de6390c329f58650042be6414420d795032cc35e530c920d7553438ca7e6215030cf55141c876d52086309f58054486be640c810d714c315033c54d0120f68cb30043b441440109f98c540c67d6215031bd185424c67e6394042cfd50414c67d60153219fd8550ccad960cc83297d8d54486be6410d42bed815150e3e6414e10cf18854442fb6048520b798a
  | 45 => 0x3141429f586531035f654c4319f987540ca7d63d5020cf151420867c6590d219fd94210c39c6350842eb508429027f6054c42be98243902df6350b209f195324833c54906309f98454ccb3d6510621d754f30882be64cc5219f59250ccb7b3214121be58b400833c5310610cf54c41c867e6394241f6545300c27f6354242cf95130842fb604c610a718d521067d6494031ee10740c833d4294441dbd954210b1c6355032ee583321079c6350940af191518cbdb514c030fc8c5500c7ba64100209f59643482ef624c721d714d324427f654c4319f99252cc65e6395121ed10450c86be64cca41f998432086de6310b31cf55332cc6f565d0641b758f52903da310c310cf149425027e6195130d7992530437a4314142af583539063d6414930d7d87534433d5350841af988539079e418c130af99052842be618ca41d7d86538835e6294c10cf15332487db404c0309f99741c83755114420f310e320ca7e64d41219f98c52842f6618c010be58243503ac5414910bd584324427e6510010bd986434427d65cca10cfd4c41087b66484110ed98441cc67f65d0730b798f50d067f6154b439fd8953d03cd320c820d7591538839e530ca41d7d4d43506bd6390a41dbd4a525075c5310910d7d4c414867d65cc941af590508cb3e54502109f98c50507ea5248020be58b40c82f56288421cf95042842be6414c20dbd48504c6f8604c7209f582544c76f528c931afd8d421076f43d4931bed8121d02ef6250e21aed8142106bd6310841e7d5053442f960144439f995414827f6590020cf550300827f6154810ed58041c875c5494e209f99741443385414131ed107210433e54104409fd8554483b661d4041db597328cb5e5450c43af193321067e65108109758c54c83795014041fad49304433d65904409f189544c7795014032be58f40082bd63d0441af98b439067c6510d209f586528c37a5288020be181424cb5d53d0a209f59543443d853c4110bbd89318827d65d0910ee99040c82f46150c21cf94e410c73e60d5131cfd8d54843b543904419fd95300c2be6414c21afd894210a5f6354b10db148404435d530c421d714d304433e6510420b798e200427e6214d20cf150524437b6550040cf59641c86be64d4f21be58043d03b84148020cf580544c67f6355030db993524427e65cc930af99042503765148430b798c424c67c60553319f59731c839f438c8419f58e544827f65908319f994404439e324ca41d794c310867e6294343f398c320867c62540419f59430042f66110c31af59032042fb604c7409f98c540cb3f53d4a41eb10620482bc6054c419f982544c6bd60d4841e798c431077551886209f98e51d0b3e5410531dbd4a424431c5390510de951500c73f6550c43cf95241042bf6454d219f19532d06756114c20dbd875244
  | 46 => 0x10dd94541902dc63509409f582538867d64d4a10d798c53c835e53cc440b718d404c35d538ca41cf992534867e6510830cf950414c2796095121ed98441042f9600c440b7d8d210c27c6454e10d718d52443eb40c8020af593215027d65108209fd97219036e64149319fd9532c427f650c420ed105310867a6095121d7d4e31c86fb60486109f98c525027f6154e40eb552210833d5410b21f64c030842de63d46209f58b544433c6510720ed58e511073f5450120cf59441c87d8644c0309f58e51043b44108640ee907200433c5290610de50e500c67d62943439f18d54c86bc6454d219f59631086de63c8630ee106304433d6494d21cf19151cc33d5450420cf988544427f6550120f60c930442ef624c630db949428c37a528c0209fd85538837965c80109f98e510877b4214142d60c9500c67d6315120afd8d521067f6588630d754d300426f6254d21cf904504867f658c020cf551308426d6215031bb98a4350abf6050841b7d8d420833e544ca10af983321075d62d4d109fd96438835e5310f429fd8d54c833c54c4110cf58e54c87b441cc631be583320cafb604c930cf55241487b56484110fa580210836e5288710cf152438c73c6590630cf10650043b841d0020be181510cb7a51d4142bb584328875e52cc230ed50a411067e65d0b10ed98443106ec624c430be980319033d6590520e70c841cc27d6494a109f98e52d07e56210421d714c32c435f53cc920be580438427c6550630cf588544c73c5490620fa588400827e6094643fa88440083db6344010d754c42042dd6390a32af984410431d5390410b798c510823d64d4c20cf550428433e5154041cf150414c27965840109f98a509077551cc430db54b32d077931940319f587530833d5450210b3588430cb3e5450310d754d400427d6115220db588538837b6054432cf99641c827d6550c10d7597318c6f8604c420cf55252cc73d6055331f554f10042bd6590420bd587404436f5294840bb988430ca7e65105309f594420427d65c8010af590528c27e65905309f980534427f6254e10db54a32d033d6394441db548528c2ee62d4f41c7153534427f658cb41dd54731cc2ee62d4c40be986304433f54d0d30d754e32d077b6114121d754d518827e6195020de94e30c82bd658c8418fd9153482f661880108f99353c867d63d5220d794d31103cc328c621cf10550cc67d62d4d41d794e32c867f65d0f10e754e439067d6115130e7d4c321063c6454620d7d4e53083e55188620afd93321073d5290a419f996420437b63d4142afd9332906be64d43219f98c540c35c5390d10bb588410867c6550a31dd55341086de6314620cf544410c33f61d5121db148414427f65d0f21cf94c410433d54105208f594321077863d4121dd94841086fb62480209f59731883785
  | 47 => 0x582429077862141319fd85540caf76450441ed993314c67d6510831be991200827f6254d20f6d4c30c435c5390d40de54c20c42f960144329f195318836d6295120f6991300c27f65108309f5825110b7963d41429f9865010b2c5414910be583529076f6255132cfd5331442f9650c3109f19632c439e5310410d7945310c75853c4110c7153534867f654c110cf146414c27f6550d10d6d4c504877b6054b10cf54841c436c5250531de9875050b3e6355032dd547418827d6590f21af596329063c61550329f99443487784154031cf15040c42bc6150040e798f529073f61953219f98a54c42df63551209f580540cbb74314542cf153414433e54d0a10b7984430cafb6388020dd54f5150a7d6595032bd584300433e6510421c7d50534433d6510620af593318867e6550d21af58a4350f7960d4f109fd85548c35e5310010be189100433f6454420cf552438435d5390c10de18154486f661cc8419f19441482fa60cc430d714f30443ac4108420d7d4c304435e53cca20cfd5143443b73210721dbd4a414c67e6294f40f398b438ca5e63d4810ded90504873c54d0a31cf55343c827e650c910af1915148376514c420ed54441d027d61d4e20be181314827d61149409f189534437661d4c109fd954310e5e65cc530be583320c2fa600c020cf55132c869c6350a419f18552cc27e6590110b7594318c33c5488521ddd4651d0b7a2114121ee904200427661d5030af58a539075f5394d41bd185424427e6215210d7d4e53103b46010721eed91401033e54d44329f982544cb5f6550c43cf15342c835f6354b40f614c5050bb661d4e41cd50c5150a7e6510d10cf944410827e6195332f6180324c33e54cc832dbd80524433c6454d21ed10731086cc6348421fcd475050a7d60149319fd95424cabe6515121d7d9353442dc6350930be18142cc35d2114d21bdd85428877953c83109fd8552cc2bd60d0841ed99321887786254031cfd52540ca7f6154f40cf55132842f960148418fd9151c833d54cc832af58241102ed6210c32cf55052cc67e65cc510d754e439039e32907309fd8151d0f3f5490110cfd51314437a6354332bb58830882dd63941429f58853502f46150832d754d320437b53cc310cfd51534876e520ca10de953204827d6195120d754c534875c540c831cfd91544ca7c6550e10bd587424876e6215021cf585540837b53c8220afd8d411067c6510421af1894350a3c64546328f992524433d540c4209f195434c7e65248421b718d4210a7c65cc910cf15043443b543104219e583548876f5294930cf952438436d5214830db548210427d6494221cf95040082f5610cb21e754d439075c53d09109f195214c37b3194031af593214c2de63d04309fd9631c827e6115110ed94550106f66190f21af586439073c540c9
  | 48 => 0x9027d6094b419f99642cc27c65d0d20d7d805350bb651140419fd95215033c5310521b7d8d521067e6550f21cfd5041083b66114c41bd98432443795454332ed98732107796454031d7d4d414427e62d4141cfd52428876d65c8220ed580410877853d4121af99331102bf6050c41cf990548ca7c6154f40b7185320cb3c54949319f593534833d5390440fa94b20c42bf6454730be9805110ef960cc510de18c5050a7c6454e20af191514c3b661108419fd85530837a54943329f18953842f76150832d7950534437451941429f586529027e6094732bb98b434ca7e60149319f582540cabe60d0441cfd5142442ec624c431cfd52524c67e60953329f59642106bd65cc8419f191518c2f46150b21cf105508867d64d4c21ddd0c5150bb44108410d794c410433d529084197596310c27c6054d21ed14c41c867c65c8530cfd91548cb7a60951319f997320435e530c7209f98e518837b64943329f191518cb3f6510410cf59441042bd6590c41de950504c67e6494c209f983535073d54d0a109b988540c67e6114c10a7d8d42106f96090f30cfcca51106ed64908429f98a539075e530c7409f197438435e3214530bd58b41c879e41cc2309f992544ca7d64d4132cfd91540cb5e538c431afd9542d02bf6454432d754c535076d61d49319f594428c73d5410f30be98332442f66190e419f99250cc77a63d4142eb58a41087796015031dd55341c867e6014542ded42508c7ad43d0942cf553510cb3f6510430bdd8542c427d6550f21bb98841086bd65d0240dd58754ccb7a6014e209fd9442c42bc6150b40ebcc8418867e62d50209fd8553d0a7d6394620bed8930c825e63d4a10f6582324c36e52cc840b7d8d42482bd6510640e7d8d42d02fa600c410cf996410427d65108329fd95204437452d0541dd5445190f3e54104209f99253843b54210421d714e4350a7d6215010db15352442be6294c41db94c218836f528c531cf953308427c6254341fa189100427d6414b10af980501075d530c020cfd5243482dd63143429f988514c35d53ccb40db54b20c436c60d4931cf99054c867d6394910cb14942503384114131cfd4e410433e6395210ee95040082bd6414a109f586534867c6454a31be58232902f46150a20d7d4d414873c52905319f58653903cf528c531cf59053c827e62d4131ed146415035f530c521d794f32106be6294041bdd8540c42be640ca21de980548833e53104209fd9543842ee62d0c42b758c214c35f6214d429f587544cb7942940319b189544c73451105309f593514ca7c65d0f10b718d424cabf6054a41dbd8952442bd6494910de590504c67e6550e20cfd52414c33d5454420be983420427e6114d10cf54641c83cc624c431bb189534433d5490f21af189531067c6054642b798c214c33e6395020af
  | 49 => 0xef6250e429d185544cbda32cc310ee5905050b5f5394e409f596430427e6414520cf95041486bc644c640dd54451d0ebe618c841bb189438cb6c2194020de95350487e85208310af99032c42dc6350b30ed905310c67d6550831cf95041cc73f54953319f98e50886bf6454d10cf4c4544c76c5308420cf551300833d5410f319f59530442dd6010c32dbd49504c6ef6548020afd96410835e534c640cf94441cc37860544309f996204436d5208740b718d524433c5410d21cf194410827d65d08319f98a500c7bb6010420bb58221083784314121be98332c86f46150a30cf14e41c86be6510521b758e418c73d540cb31d798253043f161cc3109d594410875c518c130cd946419027d62d5230d754e430867c65d0931db58b53842f96490040cf15032487783214121bb98a43ccaf66108010cfd51434c77451cc540db99052443b8544c110db98b540caf961cc230be18132043af54d4931dbd4a528439f5390510dd59741c867d658c440cf54a410c6be64cc841be983328833d6195020cf550420835d53d0c40d7d53430cb6d5290a409f987548cabd64c8730bb98a40882fa60cca32de14b108435d538c8409fd9542042bf644c640af992504873d5415130cf55140083765110430edcca51106ec6250e209fd8d50086dc6350330cf55330842df6350b40dbd4a324c36e6214c21e798c410c73e5210410cf985540827e65d0d40f310c320873f6195210cfd5041c827e6195330cf55241c837a524c210b7d8d544875d61d4d42d794e43086bc6448710ee10750486f56110c31bd986410867d65104309f98054087b55110430cf19441883746154d20af59331c42bd6314041dd58752842fb6050910b758f54887bb43d41429f98e510427e64d4520d7d8d544833c5490a21ed10721886f86048710bbd95320cb5d6294c10b718d52502be6515131d754f208833c5490910db14830442fa6010c409f988544c75c53d0942de58054cca7d64d4810d794e320cb7b5114142dd58753843b46150a419f583538867e6115032d754f42043b66114241af59350c873e5490a329f58853c42fb624c020afd91100427d62d4c10de582544c75d53cc010cf14a414c33e6494910ee90730c427e60d4c20ded84504c75f530c510be583325073d6414c209f184524427d6094742eed0b405027c654c740de18e50cca7d6094e42be58041c436c5308620ddd8c5150a7e6094e41f9988410875e5388620af586329073f54d09209f181540cb776154910dd14431483775194632af98252906f960cc831eed8041c833e5290731af59032886bf640ca41cfd95548433e6195032bbd89310876d520873097d8d52d033d54d0b21be18131d02f561cc841db54852d0f6e5208730c714f4350af46150a329f984544837443d45429ed81521073e5490b20af9874
  | 50 => 0x94332de59420c427d6494231b7d8d214c3b66110621cfd96410c6ec624c5309f997415033e5494331ddd5041c86f46154940b798e20c42bd640cb10bd185534827c6354221ee951308427c65cca10dd545419037b5094142d798c53842ee6514910cf553438c27f6055032be58341102be64c8640cf552430833d5290440db14831442bf6350c439f98754c827e6314542c7d4e414867c65d0e219f983548867d654cb419f592528c7cc624c53097d8d510836e5450842d7590534875e53cc640ee10430c423d6414c20cf14a414437654c8621f3948320c77b53c8310af58053107b46010421dd58454c86be6510531be18142c82df6350a109f997434427f65d0c219f194420cadd6308730d7d4f31c427e6215130db588548c27d6195121fc984200437852d0140db148424c6f961c8310cf98d54c867f6510a31bed8142c873f43548439f996438427c6154a30f5d0d310c6df6348540cfd9154cca3f6510420bd58453903b56110c41de980548c2dd6310230bb18931502f96014f42db149414437b3294031f910421883da53440109f18d54442bd6010a418f986540cb3d54d0731cf50a51d035f5310d209fd95424433454c85219fd81548873c60d5131ded0f5050b3f5210410cf153314c67d65cc520bd98643086fa6008720be181419037661d5332d758b534875f5394d20bed81428caef6148421dd544518ca7e6514910f354f208835e5350e429f19431483ba6010520b718d211027d6394b10cfd0a5110b3e5410c32afd912110379518c030cf1534148778538c2109f99443087796015232cf946410867d6510020db54920c436e5288740ba189100427f65d0b31af58053907b561cc8419f997430836e52080109fd94434867e63d5032cf551320827f62551209f19532d036d520cb41d7d4d5050afa608c820bd185429077b4394332bd986324c79e3210431ee580414c26c6254d10cf15041c876a2114121af990540cbac54d49319fd95310c3ce53886209f980538873c5450d31af191321037861940319f594424c27e6195132bb98b43d0bb654d0721af1854350b5e6454e20be18131842f66110b41d7589538827f658c4108f592524433f6414542b798c548835f5394d42dd946218839d5310620bed8142ccb3f6295210cf951438c75e5350e409f196424437a6014a109fd8951903796494332dbd4a529027d6295010af98752106f6610cb219f18d51c83af328ca41ed90b5150b3e54d4f21af58251106fb6050a20af982511067e6014810eb50842cca7f6454632be58232042bf6054e41db193524c67e65151109f997325076e62d5021d7d4d31c42dd6388020d7596310c33e51107209f997424ca7d65d0430ddd46510827c6550930ded8152d033f54cc531bdd85434c67f6590821d718b534435d63943219f98f540c2
  | 51 => 0x9f58e544cbb4410c6109fd85500cb6f528c910e758c410c6f76148110be597208833d61d5131bbd89314877a6015031db90c524c67c62546309fd85508ca7e65d0130db148424c36c5250941d798c53086f562d0421af191310433f5310721bdd85430433e6415210fc4c6500c67d6494032be58021903e461508429f5805150a7e6510920ee551308437a60d4a10cfd5254842fa60884409ed81544ca7d6395110cf15250487b44194321be980430c36c52085409f98c54886bd6294441c7d4e414435f5310910d794c300433e5490220af18d509075d5350f209f18d52d027e6394440dd546210c35c5308110e7106310c39e5450c43ae583329077551c8420dbd8c524439c410c630cf95320843784254332d7d4c424873d61950329f5865010f5f5350110e754f43d0a7f65508329fd95411075d53946209ed81544836f5288110c754c418827f64546209f596410427f658ca40de58550ccaf960cc940de98c50487795294031b758f210c27f65887309f99632907b84194031f654f30c427d6590a31ee906100435c528c5319f58e52083e65188620cfd8554c875f534c921d794d30c827d65c8740edd8e511067d6154810ed0c841c867f6454f219f988535073e4194031cf95331c877960d53309f189548c63c6454420eb90621882f960c8730bed81428c2fa60d0510be983329073f5450a32cf593530827f6255130d71805350b5f6294e20d794c328837b54d41219f5825310a7c60551319f595314877a508c0109fd9542c42be6014e41cfd5332442dd6388120d794c43882f96510020bd58742106de6390431cf151424c67d65104319f99642486bf6250441af591329067c61540429fd9543c876d5188420b798f404c35a524c030af19132106f960d0a20d794f32886f565c8621ded4c20c42bf644c410d714c41486f46150a31be98232c833f5410521af59641cc77960d5310bb98720082de6395121d754c5384379658c020d754a320c75e6514d10cf0c9540ca79658c0209f99641483b441c87109f98c540427d6295130de94b504c73f6055331eb0c8418873c6590430be98041882de6308730be98021082f7654c431eb14a414433d63d51319fd9540103e441c84219f99352c433d54102209fd91528c27e658cb40cf95253c873e540c020be98343043e82188020cf196418833e6095321af993514c37a5194332ee582419039c5310510eed8142906dd63d0430be583434c37642d45429f58b540c33e54d0e30be580310c2be640cb41d714f204433c5390621cfd51424c6fa6094f21d754f321072c5290531ee551300833d6095331dd94731cc3786055020edcc8410867d61952329b58854042dd63144409f994300833f6155210bd584320867d6294241dbd95200827d62150308f191510c2bd65cca41af982439077b62
  | 52 => 0x46200180b100b4002011c005129c008080801300e0002000000021d005701600bb0000006006c2b40000007199c00a00ac6b200000050a64137000002c0050001016805f00000000028021007c30b002001e00000024a0c264001027a007009d004008f001800b0224008002002b02e400600600190000000000000302400be006948f00200000028004000000200100060068003000400005f4000004c01b000c0000040001001400827c8012008401400700660000045000000100580000134002005000a001c002007401901e003900017bd001c014003000000000fd00000020000002003c00015f400300002c700680010254048001800001f4000001801a0004048000800000c0012002400100740000028031000000300040010000036004c015001001a0004001003c0af002c001002c0020004015009c000003400f00040000004035003c000007c05100033d5310c41cf95241cc27e60d5132ded42509077a52d0240cf55320842f960d4831db149324c36d5214941de94c504873e54100109f58754c837951943329f588514c33d61550329f992510c75f534c9109fd9743083cd6388120d794e43c827e6495131cf0ca51106dd650ca319fd91520c3796094d109f58a508c77943d4131f694d30c82ee62d4043d714e328875d6114d219f9825210f3d62d5131cf55041c43e8218c020d798f54cc3eb52d4131be98740c833e5450b21ded9530c833d54cc0209f992508cbd93154031e7d53534427d61d4d40d79835350bae5488420bed8131903ba6090640cf95020842bd64d4331af590520c7af6448421be98031886fa60cca31db94832103cc6348421cf592524427d6510f21f6d4f10442be60d4c41dbd4b21443b44310721d754c43d03d8310c010f5d4e10443795014241cf95143c87794154031bd987434c77b62d4142cfd89548437a42141219fd9150086f661cc831cf151524433c62950329fd81510cafa620c0109f59443c42fb6050a419fd9153c43765110740d758353487766014542afd95431067d654c8419f59253842f960d0a30dbd0f524435e5310c419f58a50106f76550441be994504c67f6550440ae980521074e5388620cf946410427f62553319f58653482f96088620cf55342082f56510421be58f108436f6254d218fd9153443b841cc010bbd89410827e6588540cf55242cc73e5454a109fd8153482be6590531cf14e41042be61d4c41be58254486bc6354a41e7d0d420ca7a6094f21e750c438c35f534c110db149324c65c6354910af59032d075e53d0620af98b419067d6548440eb907218873d5410620d754832cc35c53d45429f59531c82f96090f20cf9974350b9e6310530d7550534435f5390d21cf15242487b75110520cfd91518ca7c6355121db94d320cb6d61149109f994544c67c6454c2
  | 53 => 0x28010000007300081300000000085000e00000210034002001400f00140030028008001c00100bc0440000011001c012054800f0168001002c02a004000000146db000000100b806e009000f003801802e4003004c0460004024001815a018400f1a1802e0000016000403e002802b000c0a601b800d005c00000000670080007000006500800000024000000000c001c03a000c005004801300181e702c801200b804a0000001000420f000c001000c00322340010000046001800000000020024077033c00000a0040009c00505d800000b8000034c014000c00c00b000c00501f902640010048000000001600bc05900740000014003000c001001003f003401600000270118028000c000000800e008811e003800b0124004005c00206d4010004c0060000d93000800400500020e840000154000005800000003492c6c0d3001c00b004c7390034018001006101180050008021000401900380280034015000c009000c1d0006c00801ec002007c0490004000003002600690df101c002000400400080710018051003c1d300ec0000028034000809b00000010020057001c00003b00000000022002c00102341ad012c00401500010000001002404a1a5001500000102cb400001fc026000001b085c016001800000009c3000807001580000024001006c0000010000001861500a403a0038018000c0e800fc13c0004000000000100a80b700082d2008001a10840680028009000001400000000000004011802b000c00700601b41188000001400200007d52fb844c013000005380210000007018801a000011000000050000006000c00f00000020028004009c0060000004000c00203bc004000802b027c33f0000000011800800000300028003010c002000800000980b400343b20050005008c05e0000000002c02b01840f1042c000000800001400180188003003000100240100b8c002070c0a7000000b000000d008000300280b70028067000c00a02f800d006c00c026c00f1d680000214001003c0000000001003000d002000800700012170019005800103d40000244025001013201900170048000001000414a4001028c001009404f01180000338017001c0470004006008401600200120040000001002600040010008005001800300540470068000016000c01a400300000080004000001c00a0020018000000f012400100000b8000c029000004e000001b001c0070000b56003c004002005a000403801700410174012005800003ac00b000c00d0000006001800a000003a000003300dc001014807d01c00030044009009c1670000026000015b000c0490778000000c000004001f0098000009001a0010004008c00505e801718041273df000102780a9002c05c000000003ac0140d00004027400d0014000005c0030135
  | 54 => 0x407c0ff406901500000094032001000b00080000000001001c0260074001007000100000030000006002400501b802000e0026000c00400b40005238001000800004e800d000c0010048007000003a003c00a00003a3007000900a4fb8000009400042810020001024c0ff0000000000801500080050280000002418200a400b0010008029c0cd000c0110000117000002300100000620005003400300cc00804d4002002c5a0001800200005aa004001201440120238004002801a04300030004067000800400000fa0034000007c536000015100300ce0218007010800f0018005004c02e018c00300000000020050003800000140000018002000003301cc0070ccc00a000800200001ca00000310004045009010e0a54001006402d00400901430001005c049001401400000060010000000401b00000120000009001800c001400000d000300cc06300287fd0014000007c05c001c0050000039002000000dc0070000000003c00000401a100080070184000000000201780000160000000001800007c700180000020022000001600542660018028000000001064ed036000e003400500400010000013000c01f0008000000400300380030014d8e0040129000c038009001600b403000280010000483018800b00340160000021004830500b80180004000002001801680000000000004c013005405708cc024004800000340020000000000c00501f001706ac4e00008001006400000140000078004007400000080320a9002c077000000c42aa00001353858003004802200682f7025854105500021c100020004023004800a08780080080008000000b000c001000c000001401d000003200dc017000c034016c00201300000008064000057b02f8011010940f00b80e000000000098061009400002740540070000000416920cc0000008000005400700000a600bc0000000000000006d00c801b004016b0ca800101c403a001c0120000001001c0230080004002c09a00a001100041f700e0002015c005272c00b003c0f80004000013c03b0018024000c498001003900000070014001000000000a401c004400d00000150028048006800000000c9007400400d802a000000c000006505b400301a40060000994009000000840040ba8000005000d00180030154010003000400180040010006014436f00000160000002010075e000c002000408d000002409bc143003c01808d00060008000016800c01880060004283004c00000a800a18c000d013c0100e28151002013a0214000007401207ac0050218001009c0e8016c000047c00301d40210050029002404f006820e004400e010c00a0000000000000e010400000b402200f03bc009c00500200210068099022400d0008004007000500080410004190001c00200540000008000
  | 55 => 0xe400f00e400100140000004311024404005c800800000130c28002007403701a80000000000000000400ec03900101fd4f9c01e0084002006001700b400200880000004008011400a0050007000c040002803d001c006033400000f00d80010006005c00300000b5006800d000001600a8000006c31500a404e0160183003800022ac00002a4007000001800280150014026002c000000800a0000025001800000000090000004012000300540010000000002005e028000e001c006000c00000180030004000003000400140010058010291406806bc9ef00bc14d005806300000030004000004800000a0001043848800700181d8400e0110000000437e008c017001c00000880630014016013000700680000040008003c00b002c113018c00000140020238347007c00600080072e38003002000600dc051221c003021001b007814700d000e001c0000090007004400600000000000001007002100c40530074063002c006000000000000422ab40bb00a002d00bc01e41ec00900880000240000000003b0060069004004a001800900011120000002001000f0974004009c0840064007000000e00780370004001001c0080000000001401502e906b00dc00c00000000008001001c65702a00000134099002809800900090000012145801100080180004038000000701e80000078018007800b00540b400b000401a400001000010064000021001a02ac094003c0a2001c41f00400410004013000c0170000069006801700200010028001004c0010e74003000401903080670084000002800a00500050000040001800100e00020054b4b037000b0074005002401500f0002007400300200072bc001b0668030000000400941df007800100004bb014c0350060007000000007ec00100040120024007006c00102e8062001800000840120254003000c0080014012000000002100500190008000c012000c00a011c003004c04500000020b4c005000400600c800000103510190007004002f001400c023406f005406b0078013003c000000800a0018152001808c008800001580380a5c000002839f06a005e00300fa00180050000002021000700140011d80000007400600000020014008005002b004800000c800101040000000000000000000c00dc006c019002c0420068268000002f069c00102d000c000c05f006c00200240000020007001002e000000700000060020105002c0020004041000c007001000000380000218043007802e00a8079054cb30000809701442f3012801200f400000a80f30044004000802e003003d00080000044000002083f0020002010000100a8000004c03100ec000042800401e8093000800300b414c009000800740010000028006410f00a8032003001500200010678001003421d000c01b01a
  | 56 => 0x14032002c000159c01b000001c000001f00084280008008004800e001c002016811600cc00a033c00f0058006008405000000130cb000100100000010002002000d001404d001400901900070154002005400101840190114041001801d000400b00046a6016c00201c0008027000001300010050000080009a0000004001400000107fa000c009000004c0440003021c15e000000000000900000000001813f000000c05bc0880070008021001b00000000068000025802a00440010000007001411d015c0010000001001c00201040090038001000c0380004012001c0cb00080c9003c001000402d003406805d8000002401e02b000000000020000000000400100000150080028012801600b800400202ec00281040000002004c00000200760008047020807d00fc00402200010014015000001c005003d00dc0410024002001800000e000900380a8003c000000800e0004000000000b005400c161404000ac00500bc128035406a0000008000861600c8037002000e00180000000001005003b000804300b4000000001d008c0000038071000400a00c80000018003004006f020000200040970000163009800208880000010000000c01900000040008000000400c0018046000004f6c0c0e700780010010005006002a00180ad01180000054035002400307ac003000003900300000000004000005800b06d0003800b003002500501140080002000000c0080007001400d000c0f10058031014c002012401c00000031cdc005000000e0018006000007916b4024003400105b418f0044000001400a0000000002000300b40000030005005c001000402ba2dc16800c800c015409900540080084015000006b01d000025c8039004c13a060c00000000090c5c00800080010024005001c004000800400000001fa401f002c061005000400300417af00080008026000c0030040002000c0770008000000000000080050050040001c054006400300ac012003802d000000103a002200040070014000000400606c4002007000b0e0002b006400000340080084000000002900e4005002c00000040080030000000000100000df00380020040004003c0000034004004411c01380030264001189000c000800e00040aa00c40000004083000c03c061086d001c000000000b2be001301240130000142009c004000000e011c030004801601ec003000581a000800b00302b800e000f21bc03800780000008019193006c0038021001000a00f8000001c0060000035005403c0090037014c0170018ad70000001006400100344d6013453f00cc000001400300080701184003006c0070000055003001a000232000000f2000c0093d8402500f4006000033900f402b0134003008800100e408e00480240000001007c058019c001000000c011c00
  | 57 => 0x2b01f000201a80023bec00000f800e00a800600000090134001006c001000000000000130000c0e0034003000009d03f8007001800b00103c401740001b1c06c000001f0030000008c13100040000000014004400e0128096000402a02b0005000012d0138013000001c00d801a001c08d00f801800bc00501ec06700000000030002003c00000a4004000057500040000040002013c000000800c001c01d001c0a6009401b00d41720010001004000a001400004d0015000400c0020004045c021000004500480040008001004c17700c40210004012005000700305a2009000b001000600140160010000036400200040010010000016402700c4005005c01300080400024007009402b00040050000001000400608741f400340001434001004403501e0001000805f02bc00130b40000138363009000000080510048004000403108ec006000400a00f406300000010040000011410f000002806a8035000000001540080000002000000700980020000003000000e00600000001326012002100cc010014800601e000316800010004018422c037000800100080b50000000000400c0060007002c000000c5e0002803700640000128042000400000200380050045012c0083ab4003008444e00000020048004007805d00d000000041f10010093001001e004401e00543d9004800300880040858003001c00c000005000000080144002003c010015400c0000019000002f0004005007807d00000000034000008402e000000a0080032001c0a700782530000000003800b0000038001c00a04bc011001000500d40000040015003000a002c00403f400003b00020010001000001700f02f3024800400ec000002000702b801d0010007000000e025c1090080000004401f004c00100e400006b803e003c0050064010359816500011e6000000e001000c004c00e0008000005400a010803a0004011000c00b02f0046000403f1294025001401201b00070040051007c04d0e600010000005002801300b800f00c400f01c0000001c0f5001800200180000004002001c01c027c00c000000300040040008000006c000059c000015400904c001700040020088002007c000000000000240012d74006000801c00b0015028003b000000a0088000000c00a02f401b007c01200780010108000000003100200010000000000003f0018ab3003c014005000d00040200004006002c002000400d0340007009800701740050108156000001c00000080024002001001b001800101e806c000403d000000000d4000006c000000c0370000000000000300b80040000002000800800000020044005001c022001400500ac61c00280000000010005c02f0034000012800000480030240018002c01602900000000000001c00310f80890150002033401800
  | 58 => 0x100540014014000000120e8000000400000000854cf405400f000c0000af5002642f009400e001800401b80ca001c024005c02d0020001007800006c861b00000210010059000000600000001fc40110000001011400600100010004000009c006001c00000049a40064000000400700480010070053000c003003000a00e805c154400102040040008039035c00d00000080004005017c006000407e00c0010001403307e05550010004001401a01a000c00ac013001402c007c0070008d4902140010960000007c00402fc0ad00400000420002009c00900140050695d68002c00000f8011001c049000802a00080f502ec0db01400580350498007800001c000500380040020001006c04c001400e019c00a001c000001c0230044013001c01f0008005002800200c400300240130000315009822c00a40f0001c0ec00000140080039008406d000000e0078065001000100840330040002099c0020028005002802e000c0180018005000401a0008002004800000480300000034000000f019000400340010074045031400a000000c00500030000016001000b000400e0004001005c0660310005007c02e008804b000c778000000200e8005000001600302a3003c005000007f002c0110000032005c00004f800200d0006006c02e005001802800000008000002400101d8c32012002a000001800f401a000000028e000b0038005000003c01080080034004001415c000000000f800100080d3000cb67000000104a800b002c06b01200030004000001c00c0340000000002d09840000038062003000000540050184051106827d00f80000f4401c02f400909a003400000010000065000c051013400300f8022007c0050068000000000e00f4002000003f002801f012c33103d000e000000002300d801dc0010008005000800b004401a0044004009c000000000217e401100140190010035000002800e80bc00ca272015807a01ac03100080770024000000000105d00d7004c008011c002003800c00700ec001400700140002864002005c003027c00f00a00100000022247403e0098001003001201980000000004000400001080000014027020c03309600ad00100000000022000c000001000500cc000001802600180440048057007c00f0064051001423d0000001005001900200010ae400d00001e900d80d402d48d901682900020004062c014000002300b8011001c001000800300000000000016039c00f01cc012014031e000000f00080220098328005c0102980374004c003002405b000c001004002d002c023000000000003650005ab3002006000082cf004c016000000300c4d0b001000e000002a119000108000000004009014400000200070000014029c00000a40830000000009802a0000000005004600c800a06900
  | 59 => 0x740380ea000b003c00125fc0580088076004801202a008100000130000004002803100840950010047000000300580330004037002c01c02e000008600390000006000400600e012d000415300000000178001000405a0004062009c000002c000002c00300e409401ac000000000200b40020004024176c000000800700f004700080040578008001c010003c001000000f0000000000000800240c8001817f000402d005800303ec03f025c013000c00100841e4003c41300f800b0008015001480a00680840000009005000700508ad022001b022409a005802d000c000007800d008c01a000000300c001900050210114000000c00f002400000180340124000000c03d003c01500c4014000002d00040080014004017c002000002c001c01f0088000006402e0010000000000200c0004006806900300000
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x98c5e73d95424421ebb4a819643535cc60d4931c3ea931ca890d5a75905300c29a38aa720a414b5d263d4910cd6a530062886c863189100431db82c8292618e19360544328bae7b28848847976947300432cb1ea1282438e5536048420cb2c7300a91974b53149304430eaa4c7a94218e9506050b31b48e6b108210d1e7395041486b8b8864a80639ad946048421c70a8b066498f9063105100429dba2c3a82859594c615081087aed2a4802051d74d84534861e3a2c3290614b9ca65904108daea3128610e5763185534832cb1cc02a4619598551cc0308f2e03288610e71619835488358320c090843879975390521e56a8290a098e58650c9304426dbaac0188619c944604c640c6cca208429862f6414a215030fb9ac8292618b59262d4f21b90e4a8a60184d97018d420c23c3aac1992431e1c16494831cd2cb3066510e2c6454a321063cba8c918041569d4414c0308bae732c831065773d95100432cb98c0a8865475cc6590620cb2c7306a40845d73d95424422fbb2a62984317dcd621454087ee8b2a631069463185521061eba6c2a9a43535c8548cb30ab2e3292601865461545300c29dba2a2a86656c5c05394441c5acb3264310ceb76884400823bbb2a228e654d9c46510431c9ec4192a118c3d74d9721cc32ca9cc4880218b1516210720ba2e2196618871853906304423c3aac1a1a41565d4214c030a3ce6304a90846f76548521032ba9cc328285c314a418c5318baec2a06518d5a7614d30442d9b82a528883c69d0534c210caaa630a840875153984200428eb9ea520c21475cc6295321a3ae6310a898ecb6218131cc2a6392c229a21591c95114530cb2cb29e600864f63189544c2b4b94a9a8263875536350832c3eca31a85a045f7694e20042ad39ea1286831edd95314121ab6eab0a601862e6414b314421e3a2c1288651e9c06590e21c6aa9308a01970c53d48414421ebb6a8192210f1d1654c6208f0e032a84886c832580310872629ac5a0a43171cd6548640a6ce3aa4a818658535825150aad380c229a858e551608c820b28e6b108210d5a73989500c77030842980410fdd95314c41cb4c6b06a910c3d75191310823d3b665a82634e1c14254241ab2e72a0a090d397498d500c6d238a84216431b9cb65501108f4e1b288690d1d73d8654c878ba988390a210f5d0650c42187eecaa0851947b7654c20c429d3a4a5a826317dcd65487408d8e4b00a2a1d1d731944188359b08c0a1083471cd5190420a72ea20a60106396454050086acb88a6980410f9d36154f20c68c9b0aa690ce87058b43086573a8c4a1a85559c46094e208beeca9863884ba70d97321070fa9cc220a43871915354620e90c5192a018f9061105300c30eaa6c6908411edd5628c0208f6e0b2a6420e4c5358b31486ad39ec3a8243561c16454c10
  | 1 => 0x43486cbb9ac4208434e5d06254031b62e12988390ce87058841087a5b92a79002187d516394910e2ea7a18a2a164e6394a20843b0296c298221479d26314d1087ee8b0ca51855b73540504872d31ac02a043659c7530c8418f0e0b2a8418cba70d97329068e39ac2aa065a994a6114841ce2c3300a61053a75907504868f39ecb20a410f5db5210610c5aa6b10a620f305110720483942a6a4282630f5da5390521e66e828ea0a161d5458e20082e43926298221475cc6510520e60e0a8882184b575185321061eba4cb10861179ce6094841aaae229e6010475711964388327b18a4a1221875966410c32c6aa630a85a047b765445050a2f3b6a6a1221c50c85110530b8ce22986510d1e74981538838ab20a7a8a85721c9644c030b66e0b108390d2d72996410422fbaac421865961d95344010c5cec29284a061c54d8d424863ab8ccb19481531cd528c841c76a8302849955a70d885348717326a590a211e1c16114943cd6a430242886c96394a2008317326a4192210f9c66414930ad2e5b18a0a151e73981548429d380c72a6434e9c26415131b48e2aa0421066b6518910042b539086282439654f604c8109b2e6324401053b7054a414432da9ac018a4356dc15414d21ce4c2a8c601871a74cc5500c71aaa0c2a10650fdd95415020e34e829a601051f73550414869d3a663a82632e5c365cc84187aec2a06490f1b65105300c35930cc029c839a94a60ccb418f2e132c6520e3854983324c72729ac421c418b950624c610a5aea2084210596731804108799b2882880214e1c1615502087eeab2642107277250c5150b46320c498e61669d0524c030c5ac4312a9086ab64189100421fbb2a820a630fdd8540c931a5aea1908210c3f76550540ca9cba4a428263531c95314d40cd4a430284085397098d54c870f324a7a8c418e551600c420ae0e2a80a0a167161983540c38a29a8628a853a9c263c8421e3483188a098d947350841c870fb26c6aa2434e9c06295321c6ca830a851066b52181314432d31ac1aa6651d9c76590d20a58eaa108490f1451107314c2a6b94a61948195d4f615092187ae9b2c40084d870584324c34bb18c2a9083365ce60c8430c70a8302a498d3b7454650ccb92a908210e618d5536150820ae4e329ea0a163664147214c30f322a7988814b5d641884208eee2b2a86104b5761042150316aa6c4a0e435c9c75454332cb2a7316600843d76153314425d3b082880218d99441c8530d54c5300a620e1f6494d518821fba2c3a98411e5d6644c0208f4e032e861065865cc53044398a8882980610f9d2650ca1093aec1908318da270cc8410863db82c929063cc94660906408eeeca88a29865a65d4c504863bb8aca212614d9c4649443296cec1908390e3854d81424c72ca9ac2100219358d6295110c9ec629282
  | 2 => 0xc6a14419a14b605051087ced2a28398e9563984521072db1ec0a9a439654e6010620ab0e0aa6a690e1d6414e104428e3a22029a219a14a60cc931a58e8b08a48855b7350b504c74d208c0988639614d600c420ab0eaa126018535719504148326b1aa429681c6151300c1108bae632a831062d6458b53843c820a62982210f1c56414f208bced29a200863564147215031d2a0c098c21175cf6550521a6ce3a10a2a06d161cc7304c34a3088298061a994a6114a41b48e4b188210d7071589500c72cb80c6a88414d5c663553218d8e4b28868863954181510cae539662980414e5d331141318daeda986510c3c7459632442b9b8a85a82431e1c16215231c9aca19043985377158a54cc69b388ca208218b991621523087eecaa0a918c5e76d4d5050a1ebb4a720a219654d6010410e4cea208421062c6554a321068fb9aa920a419558e61d5220878e8b2a43186a46210531086ac382c5a9a850f1d9544c420c72ca20c200852d74d87524c61fbaac998c215adc95308310cb4a4b00621863b54982524c61fbb2a0284830f5da54c8420cb6ec98aa018e396498353082d4382c420c43699cc321042187ced2a2621051d7315342086b53808629221c6551300c210ea08298aa018e355418542cc32d32a601824196d4d600c52093aec1908218e696314b1044364b1864900411e5d8540801087ee8b2842986595358720042d8b80c620e438e9506048610cd2c5300a808558754c030442973a4c7a92218d9845190140acee2b20a48856a70950524c70eb1c83280419a14b6050931ad0e0a90a498f0e63548521061fba2c329841369d8534c210c3ac9a98648865453185424869cba663280638e1936054d2087ee8b0aa40845e7694d4204334294c01822117dcd6295010a5ae52a08298d4e72d4e31842ccb98c0208412d5d841d4321ab0eca8a601849f7654c531071c2a0c0a16214e5d3615433287ce9306a4086a8705885010732296c2a02210f5da5290631972e1b2c6520e4c63949218428eb98ca20e411e9c26394810a6aeb308820854c73548524430f32aa61948356dcd4214142b64e03188210d58705865388334382c42a4614e1c15490521ad6e4b22a018e1e6414e50487463148298863179ce6590720ce4c2b00a610c3e74189500c69b3a6a210a610f5d85290530d2cc8b086418e986418131cc21fbb4a819421175db530ca21a76e0aa0a890d54715895388364b10c4980614e9d660105208dae5b2a868845e73d95404439238aa429083ca50842141218b8eca9a420843d769944108392a908210e214d5c4541062087aedaa08390c5f7654c539031bba0c2a9a41e4944414c030caca630a851065953d851004316b20a598a634edd542d0020c72cb2a4610843f76153314871c32c8298221365ce60c8720cb2cb29e411064c53588
  | 3 => 0xc85450c31d36c7b02a420c7b70595420c61eba0c4a98214d1c5521064087eeab20410851d74d86538832ca9ec090c41175cf6590910ccca430a8520e1c64d4d214428e39ac4aa4218d9486150b40caac7308a4085367119441882a7b9aa8292219514e6194142a58e4a8c821845f7654c530421f3a4c728e419cdc3654c431a6eed28883105c8724c7304c34c3188288021471cd541512187ced2a2430853671d0e5190e9c382c6aa041871526394910b4eed9908210e5763d455050b98b80a220a61e85c04108620c5cc8b10a80865a5358243c8317a9ac429883991486150910ca8a730e6490f2b70548521069abb0a220a41365db214c0308f4e032a6420d3970d8b544c717aa0c4a82638b593520c940cb0c728a200852c7258d54082e43828499065561cd5014141cb2ea30a601863954580510ca3d380ca210215c1c54214142c70e0b24a110d6b70584524c62eb98ca208438e95160ccb21d50c520a2008479759833204296b96a720c219654d600c6208eeeca88a2186a4719885010675384c690843471d161d4d10976e0b168620d357418c5150ae439262a8063ac9866014841a76e0a9c8290e585358031c86ccb8664190839914b6150941d90c4302639863a65d52304432ca9ac1996810fdd5640c8208d8e4b2a80885397014c4188792bae64208438e9536050832e48e4a18a2a147b764c4504875930ac029c83d114c5284110b54e19908310c7b7654820042aa38ac8a98210f9d85210530d60823024210c5c7358b505063a38aca21a416a1c16210720c74a8b06641965553984200431d2a6c0a16438b9916215031ce4a23024218659535834288359b08c0a1681a6105600c63087aed2a0a70867361181544861eba0ca19221569d7424c03087cec294829853874589500c63d386cb21e435a5cb53080108e8e2b24a41843d76d4e410828eba0c129821479ce615503287aed2988290e5b7654f2004316aa4c5a9c21a618f605484187aedaa04088558750c9308425b3a4c8908433a9d8304802087ee8b0ea69061e54d8d428c30fb2ca899065569cf5094042cb4a6b006210cb47458432c862f398ca10a811b5da5288421974e131ca420c7b7654050ccb1a2a0c2902215cdc54254031a6ae3aa0831071975905300c2adbae4298061a998841cc7218dee4b08a0a1cd876505300c358208c098843d2149314c110a9ce5a9ca70873051980414c2973a0c0292634e5d363141428f0e0b288498c3d75d91218434bb18c2a12814e9c0639521087ee8b2a609043e76951418431a2a0c2a12431edd95014132cb2ec29e208843e71d954210aac382c229a43479d36114d21d4cc5308a620e3464545210c28eba0c129c419554f614c810cd0c4302a898d8d7210c329062eb9ecb10e81695da6210421ce4a2302431065a5358332d022eba8
  | 4 => 0xb6e6a8ea0a165b6314f108421f3a4c5a9843471cd5210710cb6c731ea090d3a7418e500c68fba2a629a211e9c3658ca41cc8c5b0aa89862e64d4b314424f3b48298e6117dd85388110ab2e7a90400863a54d81510ca8f39ccb20c414bdd16114931f208398a610846f7654852cc31ab2cc2208638ddd95110620e4aa4208431852f72550414422ebb4a628c418759253c8410ce6c2302a89958d7214e321078a2a6a790a438b5496014841a5ce5a9ea520f1453d0c5150a1f3a6ca1962166dd1614c030b62e1a988390f90414c5500c71db26c0aa243569c8534c1109d0e4b00629043e76d51534861f3a6c2a84655c5c46214131cc8a5b0a608862f5458a54442b2b8c8629221471cd5210510c98c6292848866b52982524c62eb9ccb20e410f9da544c610e48e2a908420c6d7694a20082c239ac42084327dcd644c841c3aa9b1a430851d73194410431ab28c4208430f1d1619403287aed2a6430843d7614c41086b2392a310861a558e6114041e48a220c40905387054b501061fbb2a8288410f9d36154830972e03266420e3565993218870e2a0c6a12434e9d6414c110ae0e2a9ea0a151e73981540830fb288298061e49c4414c030ab4e7296208865963983548831baa0c2a162193dd56210c32c76ca20a200867365181210870e39ac829261695cb6310421cb6a6302848865b65d81310c65ab8cc8990839a58a6094d2187eecaa66390e7061d81544ca6db82c5a1c654d5c463d5110a76e8988a098d39751063008236b90ca21e21a918a4250441c5ac429082a065853582434421eba6ca902211e5c065d0c21d52c5b00839079041cc7300421eba6cb19043ca1505214131c68a930e6490c7870595430863d380cb992838759153c8410c5ecb2a264196b0419803108696392a920a618e99160150218f4e1b12a720e2e65150524c63d386ca21e4387d506354121a72e0324a3a151f73589548432d31ac1aa661171d95350a208f2e032a8610c7a76cc9500c697ba2c3a9263d254e2108010a9ae52a0a6885a47150842cca2eb9ccba0c414d9c75310620c5ac4a80a020e3a5498352cc62fb9aca90221c3591520cb308dee4b0ca00843f7458453482ad3b2a2980614edd1319403187ce9b0aa518596731825110768b0a60184214e9c06395032c76c9b02a898d1d7394a414439429083882210fdd16214530ab4e1a9ca7a0e2e65d4a414c6b4b90a8a8063a954a6114a41c3aa831a859862f64189544c29b388a620841539cb530c610e34c8a98400852f744c4524c6a7394a9a9a214e5d33114121a5ae42a0831845d73d8950906b5396c3a82639554f6150a20ab0ed292601863a54983320ca9d386c32a0414b1c94354841ba2e3aa2601853a74188504c68e39aa420e81595c46014931a9ee6880a48855571d90534431d2a4c1996434b5
  | 5 => 0x847b705954348237b92ca98e81acd876050841ad6e0aa6a498d2d7218e54842ac39acb88421871936354d21cb4ed29a619056970d93524c61ebb4a8280658b9975414931acee2b20a498c7970d95424c69ab9ec828a859918b6155110cd0a4b066498e3a6590630442d2b90a7288839654d60d0c108baed29c64197196454c200421ebb4a520a218d15161d09218b8e6b2a809055973d09500c61ebb4a829e430f9d365c8430ae0e2a16a098d5b73504504c72cba8c098863cc94560906408bae6302a3a14d87358420c422f39ecb10e81d194c4108620c98c6a92430856870548525062fbb2a629a818e19360547308ece232c861063754185424878ca9883904412edd950142418f2eb318400855975885300c38a2988390a214e9c05310621e2aa6208620843f7655052cc716aa6c4a08414ddc56355210a76e8988a090d1c74586538831cb22c02984353dc95314d108f6eca12a018e3b65905300c2ad39c82a80639394e62cc620c72ca20e600866852983314423bbb2a228c87569ce5114142a3ce7aa68710e2f54189438865a38ac7290838d9516114032c38a831aa090e3754185404425cb86c4a9c838d153614c921a5ce9310a48863b65982418c334b14c12a263595c764d49109b2e6302841853970d8b544429d3a4c6a8063565d65344010ae2e2318a090cda70d8f21cc23d3b0a6980414edc16215121c9aa6312632055973d875048717aa6c4a9a219514e6190d108b8eca9a20087185414e3044296392a8a10614d5d441084208f2eb31220086c863d89100429b388cb208418b9935294131c9cc6a94410846f7258653d022f3b0a6a82434e9d36114131b52e4300839053870550414c69db82c4aa6634b9d762509408bae7b2e84885a472580410861e3a2c329461179d85454e20c38a9b1a428865a63580538863cbaec0a16658d5db51105208bce7b2c839043f76550414429cb84c6aa6631ddd95114730a74eba18a0a143d741942004297394a620a21659d2534c4318d8e4b08a0a1d58735445050a1f3a0ca19221475d06114d42c6cc8b0ca690d397418c5050a2e3b6a6a12210f1da51500408bce732e84085697018c524431cb2cc908021cc9466010620a3ce7aa4831055973d88504c65a3a2c3190435c5c4534c020c72ea3028420e3654185428c32ca9cc118821c4544414c03087ae9b2e639045e73994418829db82a820a43561cd42141428f6eca98a0a15697018f5244297390ca208639514c6150110ab2e7b10a090c6f76548525021e3a2c329221479d36154e2095aec1948310e1f54d8d42486d23a2a210841175cf6510020a6ae32988290636549844084316326c4a9a211e9c265d0e21a3ce6328829046e72194430423db82ca192830fdd95415321b96e4b0a601871453984414431a3288298a218755163d4a10a
  | 6 => 0x8316b24c5a9841cadc15210841cb4c7300a810e2d6218954cc696b94a920a21879915308010b4ae43188390eb261583321072a318c2aa2414e5d25314121ce0c2302a420c3e7419531082963928628a85659c7328c841d4ea430a84a064e6358854cc2ccb8665190838e95160ccb31c74a9b028598d5b754c9300c395aa0a4982213a5c8648c320ad6e4988a090c5f7654c534431c2a4c1292631e9c065cc910a72e12988390d3a70d8654cc68fb9ac52a421475cf5410620c9ca6312621847870594434861f3b6a7208418d951610c210cb6a6b08618862f5458a544c798a888318061ac104604c710c68a9b0a84884b9701953210738b0ea128285c654e4108010e48a420c628843e76d51504c63cbacc0218414bdd161d4910c6aebb0a6420c6f7654c524432cb2aa7900219358e6295110cd0c5b02a88871753984414868eb98c52a0418d1936154d20cb4c6a98600847975983430428fb9aa820a21a598c41d4321e4aca208431061f64d4d2144334292c190a211ddd562104218f6e0b2a8610d377158854442ad3b064a80634b9c86095032e96a6294608854f7358452442cb39ec528883531c9518c430c3ec831aa890d3a70952414874a208c0988638e551600c610c70a9b02428862d52984521070eb26a6192818759053c8521a5ae431ca998d1d73d9641482d339cc4208434e9c263553318dceda92a098d6b724c4504c636bb4a7190654b5c86510530ca8a730864884787058e5110b8c382a7208216c1c542d0020a38e6aa08290f157414c5150b1caa2c1218412e9c0650ca418f2eb3066418d1d73d96410878a2988308221e81042108310e60a990ea090d5b75509300c297390a820e6187d94414c43187aed2a6621068c62905314c24ebb06420a61b418f4144010cacc7a8ca0a151f73588544c68f398a820e414d1c5545093087eecaa0a198c7b70588548c71caa6c090c219318f6254910c6ea930c868864f63d49424431aaa4c321e435c9c263d4542a74ea20a608863765d854210a5c382c2190834e5d742d0020a9ae72a0a48847776544511021f3b4a8a1c63479cc6510421c9ec729285184787058a5110e1eba6cb99221969db654c0308f2ea3026408753531445050b1aa98c2a10850f5d36154c10c76ca20a4010534711502144316b24c4290210fdd95310521d28c630a84a064c5398b314862fb9ac5288815adc93194031a3ce632c821047b70595420421ebb0a8192639a594218c020ab6e6b28418845f735805150a1eba0ca10a614d5d76210421e90c5292601852c74584524c71ab2ca820e431e5c165cc810e2aa7288831061d6494f218823c382caa1463569c254d4d218bee6b14a32066b65d8910043523108298e21361c1610ca31ab0e6a16a098d3b70548418c68f39cc0aa643569d6318c110f208390a601
  | 7 => 0x7080214e9c26355032cd2a530665a0d38744c6500c6cc3a2c498061179cc6550810c5aa8b16a70845c7358a5110326a9ac429e814e1d15014121d1ae431aa420cb970d9732907a429662982210f9d0658c810c3cc8b18a810e3854580414c297b92a720a21a3191424c832a6ee2a90821845d73994200430eb20a61922156dc165cc631c3aa9b1a8598d3a75904504c71ab2884208438d596611041087cec2988210d597014e328878ba988390a439618f6054b40da0c318a601866a6298353c863a3aac2192219ad886055121c3ca8b18a2104eb76886300821e3a2c3a9e41d2148324c110a5ae9b08a48843e74d85534832a29ec2902210f9d8544c521a76e0aa0a898d377154c41442b9386c5a8a85531c954d4d10c3ec929a20086675218542442cd3846420a61479d26314d21a9ce5302a60843d76d4e41c8734a94c110c611b9ca6550e10a74e8314a018f325158041d021eba6c2a966165dcd4290441ab4e030ca71043e7498a510430eaa4c7286431e9c26550810cd2c4312a018c9d7610c321065bbaac3990839a54a60ccb31a3ae6304a90868d53588531072ab1ea328a851edc1650c910c3ac829864a06395418142c86b5b82c829221cad4a41d4131a3ce7b16a890e1f64d8d534861f3a4c128c65ac9d84144010c5acaa10841043d74996328426cb84c790c61999486150a30c38a931ca090ea662944501061fba2c2a9821565cc54c8010a5ae42a68618c3d75191218434b29cc2298834b1d13114931c58a8312a098e2d64548200425abb6652888393d8c625511087aeb3206598d3b74540504869cb86cb20a410f1d16194d2087cec29c83905687250c5050b5930ac0298838d99441c8520a3ce6328831055971d95300c28eba6c3a9a8596596630c010c3ac6a90a420f28705485210714a92c029083695d73210421c6aca20c6210e3765104210c26cbb68298061879925308010c3ea831a8490f2652104210421f3b4a8908418e95260ccb31878eab26628853575cc8410872db18c0aa2639c1876055120cb2a6302632053771588544c63abb4a51084387d9153440108eaed28c200843d74d85534830f2a6c6a1421175da540c930c68a830a859061d6494c32c838cb9882a80630f5da521051096ae9b0a6420d8c73588418868eb98cb208210f5d84194010c38a8b1c408861d5418d420ca1e3a2ca10a611ddc56550d20e90a6292608863954980510cb942a442282431b5ca654c540c5cca2948298e9a41181314c316b20a590a218b59542108328e8e2b20a4986a46210510042973a6c3a92211e1c16590931e346420aa018e1d5458e20843932908210e81175ce6510620ad4e1218a48863454185428cb172a6c498e438b993520c931a3cea298828863965953108431c328a8982218d99251cc43087ce9b0aa690eaa545884
  | 8 => 0xd528cb40cd4a430285205707054f5150a97390ca20e6156dc1528ca31e36a6208618845d73194215031caa0c0a1c614d9db43145429b2e0326651955a75885300c25abb0a620e434e5d441880208ece232c871045e73194420430f2a0c690841475cc6295210a6aec288829843e7199053c821fbb2a629c83aa5516210020e4ca420e422061f5498e204422fb9aca2122117dd95314d21a3ae6324a3a155970953534869ab8ca820a431ddc56550910e2aa7308831054f73590524430eb22a610021d254e62080108beeca98a7a143e74d96324422e39acaa0841c35483210730e30a7208a090d1d74981530426c3b284980614edc1651052087cea32262884eb75588400829b3a6a328c419398e2194020cd4c4b00a99062e64d4a524c735312c129a211d9c46590c10e34a620a61906715158031cc29c382c2aa6638d9506150a1087ce3b2a802052d72194418c334b14c1a9c41c69053154031e64e220aa018e73515825150b0f2a4c7100411b5cb654c110ac8e2a90a4984e87258430c429a3a2a210e41aa19062440108daed298a48853875580414c2f0382c4208430f1db544c521ea0a6288a0a15377154c414872db2a60180218b9905294131a6aea3008390dc97094e320cb16aa4c5a86635a9cb4114121d60c620a200861e5498c510832732ea6292210f1d16114c20a70e8988a090d1e75106314c72c312c029a211edd95014041e54a43028520c7b7650b50486a8b88a6980410f5d3658c910e1ae7a94a520c5c7654d218829aba0c028a854d1c55415130b34e9b0a60184bb7058432906373b6a498a21969d8534c210a5ae532c831845d75982328c6b4b808629221175cf6590720a6ce232c8218e3a64550400828fb9ac2aa041b2989300c020b32e819260186a562944501061ebb2a9988414e5c05310421ab2eb322601862e751894350a9abaec620e430f1d95448420a70e8988a098c3e74d9430042a6392a218861279cf6254241a3ee6b10a8885547354631082cbb9a84208434bdc954905318bee6b2a840869964180324c21ebb4a620a218e553604c721a9ee6aa6a4886976318542106a6392a629a834e9c352542418deeca90a418d9573180410861e3a2ca98e412ddc562d0c41a72e9b08a0a173271107504862f39eca2122195d4c614c110a6cea3188210d3671d96410832d380c6a8841b818460508428deeca90a421d6572d835150a3cbb665a82435a5c864943328f4e132c8418d1e7399441886b9388c728665969975314142a68eca18a2a14b77158a43106a7396a698421a618f6050841ad4e52a6a098cb57614c410872c382c728643c3dcd5210841a58e4aa28598e3b65951308421fbb2a82a2438b1486150940e90a7108a090c3c74584524c316b20a41928117dd95314c20e4aea208421065b63d81544cb2c3b2a
  | 9 => 0x4a53066508568724c4504861eba4cb98841aa58a6014c41a5ee8880a48843f7655053c861e3b0a898a435cdc15314542c5ca8b10801065b539825150b8aa988390c411b1c96194f40c3cca20e629861e53984410432ca9ac1190214d9c45310620ea4e3a9861886b06110520082d3b92c020843a5d8c61508428f4e032c860846e72197430429c382a420c634b9ca54105318daed2a4842143e7499532c42ad39cc8a86655c5c253d4542f0cc79908210e956398752906ac39aa3a8285ca14a41d4131a6ee2a908318659658cb3004237b92caa1a41665d0624c030c3aa8b18a21043e711915348395aa442282439614e618c110c68c828a429043d7498b53086a7390a8a9821661d1214c03087ce932a650853a759063044317320a410221e1d8c321042187aed20ca0086c8631814210a8fb9aa2208411e5c261d4d42ab2e7300a50843c745952044326b1cc42a46587593539491087eeca9c8290557735805150a3d3b6a2a86650f5d3654c521878e8b2e648856872540504c72ca9ac2180215a5c84394332ad0e4988a098da972982410838daa2c029a214e5c25490521970e0b226520f0f63149425021eba6c2a90615c9c64354031ab6e6a12a19952e72d865408354b148220041d2149300c110ce4ca288a0a161c5498f414c63db82caa146387d536350931a98e6880a48846f72585530430f326a708221659cc6210421ae0e2a12a19952c7454c524432d32c63182218718c6155032c3aa730882085a57218041c870e320a690a21551c56254c10cd2c5300a99967051580315031aaa0c2a1c214e1d16194332a9ce52a0a68863864d815348739b2ec0988638e5526094f21d34c8306629853471553210838c2a6a6282434e1c15415132c6ec830aa89063a5498353c864f3b082988638e99260d4e10c3acab266318e5963983548c32c29cc021221cc10721d4121b4ce43188210e355418542cc78c29882982215a1c931940318f0ec98ca018cb97098e521069dba2c32866553dc96154e20cb6a6b006210654631455050a8eb9ca820a219518c5148520c5ca8b16a198cb97690420c430eb2c83188611e1c1650c941c3ac9298400864c63d49424430eaa0c6a0661475cc5490720c3ea831a428845e7654d420423b38ccaa1e41665c3328ca41c6ee2b20a498639649805308795386a529483e810421d0020c74e8302a5a1c6e72197430830e2a2c729221ca14a414c110a5ae4324a3a068f531894350ab5b82a829263565d731cc0109b2e031a421862e6250a51d022fbb6a7102211edd950143418f2eb31e418853471551510829dba2a7a82439a98960d4f208f2e132c8418e377159351482adb9a85286651b1c965d0d10c38c929aa3105a67218041c870eb24c7a9421471d1530c920d48a430a84a053471548411039928ac020881531c
  | 10 => 0xe5a53d8121042f038a8490041879516394321a9ae42a4a60862e62d4b5090792290c2a128156dc15314d42a3ee6a94838863754185424c6b8b88a718041ac105600c610c74c9306a790d4c724c5500c6973a4c1a9263aa9896014c41d18c720a4210c3f7458652443a429ea4982219654d600c410ae2e1b16a2a161d64d4c324865b388ca194834d9c76455030c3aa831a8598f1874545300c31bb288298863ac98560d4a41c68c830aa69046f76548529071d2a6c0988410f9d4644c521a74e8190a098f0e53904218823db82c528c87175db5410e32a3ce6294820863774185544cb9420c42282431e5c06510e21ab6eca98600854d73953524430eaa0c6908418e994548c110a3ce7a90830865953583420431c326c0a9a213a1c162d0e21c74a83026390e5663587540c2b9386c7a8a859554f6150810cb0a7b0262885397418e50ccb1d2a4c018e4317dd95410c32972e032e6520e3b52580521075238cc429883565c26314d21ad4e1a94a598e5753d855050b4731cc428083369cf6050930a74e131aa990e1d5498e200823dbb2a028463535c85454c108bee6b2a42205367598441482b938864a80630f5da419422187ce9b28640843f76550544ca96b94c82a2631ddd95114620c5acab264310c5c7614d424861eba0cb90a614d9c45310540c6ac928e432063954d81510cb2ca9ec090821b1d8c624c43199ce73064310e1d64d4f3144236bb6a4106218ed506050910c5acb3206410e9963540501078ba988210a21539cf5294b419d4e531a200843d76d4e4184236b96cba1a219add56210020a3ce6304a81054e73988524421fbb2a8104212d9c4658ca41cb6a7b02848846f7654852c42ac3aa62982214b1c95350b40cb2a2b00631845e7614d5244296ba4a629221179d85350921d54a4b00a420e4c6394942cc32da9ac1992218e9516014432b4ce5aa08390c3e74d85500ca37b92c128887475cc52904108beeca98a7a0e377159252c43d1b82c4208439318e5148421cb2a7300820861e5418d428421fbb2a420a214d9c6605502087ae9b0aa71065963d425050b1cb2ca820041871936354d20d32a6b00a720f517114d3084317aa4c52a2211d5c76590f208ece332c652062e64d4a52442ad38064a8063729c2534c832ae0e2a14a19961f5498e50487c2a9864208431d5c6655093087ee8b0ea71063b64181544c78aa9aa220c41c99484108710c6ca830a842043f75590328425cb86c9994838b99352cc531ab0e6b08a0a165863d4d100432c298c298421999486150b308bceca9a20086366458453842a7390a9298210fdd16394420e4ac428882904cc73588410861fba2ca902211b5cb6510d208beeca98a6a0cd973983210832c298c0a12211e9d460509218b8e6b00a2a162e5418931c86a6b90c829a438b5516215230cd
  | 11 => 0x871d324c129a430f9d85450f32c98e6b10a99853a75106304438cb80a720a214d9c46590720a3ce732882087843210421cc275384c790c43d4dc53154031d2ac620ea190d1e73d86540cb8da988228243565c23114131e6484288a0a151c74589538830fb26a698a21b218f6048421c6ec9b0aa69062e6498b53c862ebb6a7102211e1d94294031b66e0b108210e356458453082ac38262a8063475cf6195210a74e8294a018d5a739505048739a8ac018a4195d976344010ce0e0b08a6105b17014c410869b38eca2086117dd563c84308e8e2b2a86106b061d815210793a908210a8193d8c5248510c38a73088290c3d76d50410821f3a6cb98c418d55361508328f6eca8c619045e739964204327bb2a419661171cd6550110a3ae7302a908559709875350a3abacc321843179cc6510010cb6e732c608872552984521072db9eca88021d4d4c51d4142ea2a620a200851e73d8654c870eb24a619483179ce65d0620c72a8b04870868d63508420cb0f328a720a431edd95014131cb0c2a8a601852e72d51428c63ab8ccaa1c418b59352c851087ae9306a40861e651505348752b14c2298834d9c74294642a6eed288821854c73584524422e39ac528c811b9ca65cc4408bceda9a428859973182540822e3b6a6a12434e5d032d41218beeab08659871b54d4c504869d3a642282438b5905208110a6ee2a98829052f74584524434731ac4280838e15160d0d30c3ccba9c82885347250c5150b69b18c0988639318f625512087aeda94830853970d4c41c871baa0c2a1241e89c04108620a72ea20a401061d6494c32086adb82ca194632d9c665cc841d2ec630a85a065a53580310421fba2c329a4393d97635084287ce932862107147154c41042673b486990650f1d16548430e6082a80a010e3b64d8153486ab398c028a858ed53604c510c6ca830a841845f7654c5348296b90a8a00218e1516094d2196cec1908210d3672944410c32d31ac02a6654d9c76510730a68e2b20a4984b57610450c87922a0a5082210f1d16394420878ecaa263086b263105100425b38ccb19483561cd4254332cb2a6b04620843c74585530421f3b6a8a82434edc16155331a5ee4a88821846e72d944384297394cb20c612e5c26394a41a70e8a9ea090e4c52582314c74ba18c2a1065661c16390530a3ae632c821052d7218c544870f31c8328041471cd6295331c68a430a84a045c7359521102acb84a719643651cd4210421cb4ca18c608849d760ca418c759322c21002117dd95414d10a72e132c8210e1d5498c510832d328a628285471cd62553318f2e032a8418c3d76148414c32b29ec2a1021875d46350841a6ce232c831065b5398332442d3b9286208439c98660d5221d9064b006310e946318542107c299064208431edc1611494387aed2988218
  | 12 => 0x2908387d5063509208baeca9c400843d74994310824eb9cc1290832e5c0648ca418f6eab08400861d6458f52842cab9ec528883569cf4114131ab0e0aa0a690e4e531894188365298c4880214d1d151c84208bae732a42a04e8705884188765b80c498a619698d6015320c72c9a84a098d2d72194410c2cdba2c49806153dc96114d4287ee8b0ca68861e6390650c861f3b0a8a04419694d600c620cb0a6b006290f1853105300830f2a0c6a1061789c332104219b4ed98a619065a53583321072da9ec098a43e494c4144010a58e4aa48298d5970152320c64ebb065208632e9c065cca41ab0e6a14a19943d74d97218c25b38ccb994831d5da5490441c6ea630a84a043d7419432c4393b92a2208611b5ca6550f10c9ca7310811043f7458453c8236392ca982215a5ca5414131ca8a7b0a8490e396590440083162a6c4a9a212e9c364cc8418f4e132e8418e3954d81310831cba0c0a96878755263907309b6eca0a6018636645875284236392c2a9821d4545314c020c3ea931ca88852d729905444274b94c01884187d506350931d88c7b124210d3a74948504c6973a6c22922156dcd5414121cd0a4b00648845e7694d30c432d29ec090c41179cf6254341e34a420a601855671d51538832b29ec2a1441721cd42480208f2e1b2e65a0f2b5414a30443c8a988288021e81042110020cb2a7304641047875582434421fba2c2282659614e6094542cceca30a842166a62d42504c764a98c4880214b5ca6590730b34e320a601870c631494250326b18a421263479ce5310510caac6a88a32045c735885150393b88a420a211e9c06510c10cb4ca298a090c6f7654c32086a739ea529081a418c41440108beeca98a7a04da76cc5300c21f3a6cb18021569c36214d4287aed2a0a2104ea76cc9200823cb84caa1263479cc6095331c76c8302a21954d7298153043a329cc210c4187d906354910ea2e2192a018f255210421d028f398a920c414edd16114142d32c6b00a420e3554185428c32729cc418441569da3254031a5ce52a482884cd76d4c32886a739ec3a9221a9948614c841c58c9292422056870553524c70e2a2c7282439398d62153328dce5b2e82186595358332886ad39ca3a8285c6dd1514c030c58a53088288539740c9500c746aa2c4218650f1d16114e20b62e03188210d2e7218254cc72da98c0a1243175d6600c8318dee4b2a860861d6454c3288339b08c0a9a4387d905348510e32a6208600866652185420c75820ac018e434e9d44114121f0aa6208431068c531894350b1caa4c11904187190635491087ae932c429863654d85328428fb9aa420e811e5d6608c810e90a6294608852d75106210832db1ec0a96211bdd9521481087ce932c431859573984410c71cb2aa820041175da5490c4387ae832864086377659441
  | 13 => 0x53840108f4e1b2e6420d3671d964188317b20c4aa2214b9da5250a41b62e1308820865463185521074d31ac1a9483179d463509108dee4b0ca1a1c3e74d9731c825d384c7294838b5506250c21c74a8b00870869963106200821f3a6c2a9021c6d5053c4110d30c220a601864f6518d4210a8eba4a7a1c435cdc54214142a70e0aa0a898e1c64d4d5244327a9ec498a210f5db53106108bce732a850861d65590328c667baac421865655cc6094441ad2e4308a0a143e74188534829db82c42a2638d5506150a21c76c8302a218787430c841087c339864208431edd95410020c9ac6294408856870590524c6a6b94a8194639554c6150c10a5ae43288218e1e65d4c414422eb98cba1021531c95414d10e48a420842a053a74cc6500c65d380c9194831e5d46284010a98e4a8a601851c74587534870e322a690c411d1c56550b30cd4a53066598d1e73d484104317320a598a639a14b6050940a72e9b0ea098e5870d95310c69cba4c6a866593d97624c431a70e0aa0a890c3d75191318430fb2ec8988639a194524c11087ae9b0aa19965853983214421fbb2a829c219514e61cc110a68e2b02a81961d6498c530869d380a6208438b5516290c32e36a720ea090e5453d855050b2ba9cc329a85a558c6394441a72e12a08298f14414c5500c65a3a2c2190434d5d46310421ab4e7a84a190e3954982410831c320c0a88654e9d03294031968e2b20a49866952983328421f3a4c7288439654d6014c41c72a8b066590c3d76d5321442ac3b2a6880214d1d15114530a76e0a9c828861d64d4e504878d3ac82980614d9c46510430a98e6a90a4a043f7458653c82e5396a698421531c9534c810c38a9b1a8498c797518e1004332296c2a1221531cd6414910cd4c5304a898f48528c7504c6b9b8aa628285479ce52105108bced29a431071832905500c71bba0c2aa241279d8414c530b52e4300821063865580414c2acb9884282638d153615092196ae3b128620d3a740c8504861fbb2a82a66595d4c614c921a3ae6300a898d717098f5150b2631ca4908818b595640ca218ece332a871051d741885344236392caa18218799564cc530c72c8b06a790d2d721805448726298c4a0a431edc16550d1087cec2a28290e71615405090e37b92cba1a219398c52d0531cd0a5b02428866965084200431aaa4c3216434e9c06395331c3ca931ea50865963583548863cb80c2a98854b9cb53106108dce532c63a06b1615833210752a94c22908366dd1214c030c74ca2a0a090d1d73996418823cbb6a7080211e9d8534c210a68e2a14a221635651042104316b24c429e4193d4d6294d10a6ee2b1aa8104b471590204437130c43100410f5d263d491087eecaa0a50847970d97321078ca98839002199d486150931970e0b2a6420f18539085050ad338ea5
  | 14 => 0xc829c208871853106304430f3a0c6a9083a6905600c430cb0c7b02a88852d7494f524431b2a4c221e635cdc56254332a9ae5b00a6a164e63d4a5244364316c098863c594e51106209b6e6b16819059873580414c23dbaac2180219c58560d5332a74e9a8ca19943c7458453483922908398a630f1d16194232cd4c5300a818d6b7250c5050a1f3a4ca98a41569cf6214142c38c929a20086a66290a411061f3a4c7a9221a518c6150842caaa6b0c80085737150b504c71cb26a1282434e9c253907218f6eca80a02165a6398354ccb4db18c0a14839c58660d533299ee4b06861967151980310c30fb28c898863ac58660cc841c72a9b028590e355418542ccb17bb2a429083479ce6055331e50a520c60884d9768c430c429b38ec8aa441871cd6494a31a3ce732c839052d74983524c717aa4c52a2638b5496010841c68a830a8498e2f64d89534428f3a8a620a4393d8c5250931ae4e3aa4a19954e73d93524434d2a2c199065c690731540318d8e4b0ca1a1c7b7650a50cca9cba6c3286658bd965448020ae6e2a12a19972a52d81429061fba2c3284658d59564c8621e94a6a90400862e65d50524425c382c5a1c834b1d161d4910d1ac7290a420e6852181425061e3b4a8908415a5cb3114121a5ae9b08a498e3a54181420438ca9c8308021969cd65cc010e32e829a610851f7458553882373b0a4a82634b1c96055032a72e12988290d1e73952414428e39aa2208410f5da5210710a3ae7a90830866752185204430e322a688021d414c51d4142c3ec9a9aa48863b54582534870eb24a7080214e9d35154332c3ea9b1aa48851d73182540828f3a0c129c412b9d84148421e886428842985717018c5150a2ebaec690c418ddc564d4532a74e9988a090e5463d85544431cba0c0a9083179cf6550521ea2a290a60186946318542d030f32ea829a430fdd8540c910ab6e0a98a690f0f54d4c52442aab9ec1a8a854ddc553104208bae6328858854d73d93524432ca98c0a1441879516310832a38e8b0aa71053974149500c69a38aa420e6187d5163941218f6e0b10a2a1f1764d4c5150b16b20a410a814e9d331141319b0e0b0865985397418f5050b0eb20a7292214b1d153d4910c70a8b006290c5c7654d420432631ec4aa2211b1c96314540878ecaa26390e2e64d4820442acbacc4980612e9c065cc841cb2a6b00a610e68525833250327328a6292212e5c2658ca419b0e0b1e84985a47250c4108637394cb20e614e5d06294031ab4e730ea0a145c7358854443653106598261e4106310c310ad4e129c4290c7b7059743482d8b86c5288838e55260ccb21e50a8292608871964d4c5050ba5a9260182210fdd954108218eee2b28869063864181510c21fbb2a819643a594e61cc841f22a220a60187157114c414431ab2ac998c6387591
  | 15 => 0x77765445150eb5390a9280639554f6150c108beeca98a620e1d5418d2184257394c3a1a854b1c95490510a6ee2a9082205d171180324c2adb82c5a9a85179d85454c10ea6a7a88a0a143f76d5331442ad39cc8a806353dc96194e208dee4b2a821853a70d86540ca3d3aec0a12630f1d16194c20cb0a7b028488559701845350a9aba0c7a8a850f9d0650c8108f6e0b2a8598c3d7614c41c822fb9acb21221879536350b21a68e2aa2a2195367294441d029cb80c72a0658b1c964149308eeeca98a2a162e5498b538432cb00c029a85179d8535454296ee2b226420e3a65d50504861f3b6a620841cc9466010440cb6a6302a2a143d75d9032106adb9a8428243c3148418c531a3ae732c8210c6d72d9643442ac39aa028243cc1073114131a6ee2aa08298637641855348354a12c0210411e5db530c310a5ce9298a48863765d91310c63dbb2a0286874d9c4659041087aec2988390e595398a100430eaa4c7104210f9d3658c821e34a8980610852e72d5142c432731ac52a2438759053cc510968e2b206498cd976109300c32cb1cc12a2634e5d76010420b32e998a601871a73905500c62eb98ca20a415c9c25314542ab4e030aa7105357194c41c831a30ca2a008187193534c510e2ea6a18a2a165b5398253486acb98a81002156dcd42141319d0e2b10801043e76151414421fbb2a990c219598e61d5220a3ae63288210748731493044312290c2a1281691c94314542c98c72928418d3575d0841086ad3a84298061cc5905114142c5ca8b168390e5b63d8152d02b4382a829263d2d8c52d413187aebb226390c3e74d8552cc296ba0a5a1261475ce5490521aace7b06a2a143d7694a41c432d31cc1aa443565cc641413187ce83286210d5b735405050a3db82c229a858e1536054d21c68a9b0a40885967114c321072cb00c029a434b9c86510410c3ac8a9ea31061e6458c54c829ab86c828a853a1c162d0f20e36c8a9a200869a53580531062fb9acaa0a4359dc9631454287eecaa0a01963654984500ca3dbb263a82430f5d7644c610c98c7a928498c7b70596424c727b2ec690843d4d85514c030a6ae9300a2a17325198041d023aba8c2a1843569d7634c110a58e4b0aa810554735805150aacb9ca3a8285a998a6114041b64e02988210d3675188410869c382a528883479ce6055032caec628aa0a162e6454832d06adb9a8528063a519363484218bee6b0ca1a17a06210510042ad384c8a9c413a5c8648c020a6ce3b2c83184db73597108432cbaeca98061875926394910a3ce8310a6885347154c414829bb8aa420c81361c163885308f2ec2a640084da70d8d424c2923928628a85725cc6088420ad2e5a08a090e1d63d48521072bb18c2a9083c514f43d4542cb2a7b0263104d873582414c332a90c2a1661569c35394c42c3c
  | 16 => 0x8727b18c4a9a21c659053141428f4ec2a2a1996576518d1004317b2aa89004187597530c841ba2e2192608861e5458c42cc727a98c498a218b553624c721da0c3a0a601853771550414870eb2a64190830f1db544c510c76a930664884797694f1084334b2c43180411d9c665d0830e30a8b00a68855a75180324c22e3b0a6a12211d9c76590f208f4e131ca420d1e74d87534422f3b0a6992418e19060544208f6eca16a098c3e769514108236b96cba1a435c1c54214131ea2a220a6018671515805190eadbae62986418bd506250521c9ca7b1283105357198d540ca1f3b0a7208438b9516210c32c3ac620ca01045e731855010a3ab8ccaa1e415c1c5429403187ce932c43985c97098c320861f3a0cb98a41561cd6154332c5ac8294208858d7210c3210697b92ca20a619614e60cc910c5ea530882886347159252c42aab9ec5a8a85c55d053d4542a6eea9908210d2d75107200829d3a883a82632d9c6658c841a70e0aa08290d2d7590d4210a1f3a0ca196214b5d06014931a3ee6a94828854d73980524c61eba6c2a9221c9dc45210531d60c9b024210e396595230082b4b908628243179db535454287ae932a429855b754c6500c71daa2c1992214e9c06395020c70ca20a608863764185544ca4eb9ec4a84830f5da52904218dce5b2a868863b54582524c62fb9acaa16219658f5094321c74c9306a50870f5314a414438b29cc2208210f5db540c931d2cec20a6218c787650b504c69b388ca20843d24c83294031c76c8302a890c7a76945100431d2a6c0a10415a1c16114931c76a9b02848863671d96410830e2a0c690a21a9d9662104218eee2b10a89853a7094e414865b38cc7290834b5cb6195331c3ec8a9a431064f65189310c716b2c6419083565ce4154031ce0c2a8a601856a7294d304431aba6c2a9a419618f6054841a3ae9b0ea690d2e7218e54c8732290c2a12631d1c56550a308bcebb1a428879041085300c23d384caa1c43871506350931c68c9a8a629855973953504872631aa4a166193d8f5248510c5aa931460105a671d4a5290716b26a4192838ed51600c521a5ae4328820852c72551424c29a38a8628a858d9d36154d2087ae9b0aa68851f745845350b1d2a2c1990419a58b5094131e28a829e4290e1f5418d414c6a6b9ec3a92211ddd95114743c5ecb20a4210d4d721845350a8eba6c029a850f5d06054b31a74e8312a018c3e74196328429db82a420a219a1c162150108f2e131ea2a1718539071044352b14c228083175ce60d45428d8e4b2a622061c5498e204438aa9cc2208214e5c06215110a74e9b0ca19943d76148410428f398c12a6438b5935208110cb0a6b066288714531042144333b10c2aa2619614d60cc910a9ae7310a48843d76d5040c421ebb6a8214431d5c46510c208dee4b2886884
  | 17 => 0x98214ddd95110620ea2e229a601062f5498a504c72da9ac199243a554c614c8419b2e730643086377498754882d2382c4208435c5c363d4542c5ecb3148210e3a5458253c871caa6c098c211d5c46590c20ab4eca9a20085707154f204821eba4c528e618e5536050820c5ac8a90a51843f76550548cb0fb2e86a10651d9c4650c81087eeca90a420d2c72551428423c382c829263a998a5294441a9ae5b0ea6a163954583320821fbb2a0280831b1d562d0d20c6acb3108390f1653984418829d386c5aa263c994c4108420cc8c5b0aa68847a70d8953d076830ca29806196d8f60551218f4e030aa62149e7694d321062ebb4a829a214d1c543944438beeca98a72161d64d4f314871c2a0c0a12216c5c05294441ad6e4b0ca19969841181310c696392a22086199d97624c431c76a9b02a690f1653107210421fbb6a819263569c361d4d428f2e1b288598e5b53181314422f3aec6a12439914a61c8110c98c62928498ce972982430832db1ec0a9221369ce6344010aaae2310a68869863181429078bb2882988630f5db540c92187cec2a2a690c6f7654852d0e9d3a6c3a8263a3188414c4318d8e4b2a868863b651814210b1bb2ec8880211bdc96550d108eaea30a840855970d875350b16b2a641908396d4d6094d42cb6c731ea0a1559731845050b1d2a0c0a8865c5144418c130a3ee6aa0829079361105300c2acb86c429a851e9d76050921e32a720a200864d5358853106acb84a619241c554c41c84108eee2b2864a043f74584524c32db1ec0a908396949600c630cb2a6b0063885587355050487c8208631842187d90534c510c6ca830a8590e8d63988501069cba0c42826396d4e600c510a68e2a98832063654185420ca2eba8c6a10211edd9501432187ae931ca210d3672944411034cb1cc0290839a994528c110ab4e12a0a690f1553104310863c3aac19922117dd95314f10f2083b026218c7b7058e5110b35b2ec0908430f9d260d4931cb4c7306a91045e7614d21442a639aa410e8166dd1314c030c3ca9b1a841965865d8d304431a2a6c2992632e9c3658ca418bae732c43a0639541814284274382c420e410f9d365c8630a5ce9b08a498e7070d95310c7a429ea5182219314f6250521878e8b08a09962f65905200830f2a6c690c2196d94604c43193aec194829843e74d8553042963a220292211b5cb6510e10a3ae732c839057071508504875331083188430f9d85390420caec630aa899564725445150f35290c090c211bdd95414931878ec2a2628863854980424428fba2c4a9c414b9ca64151108ecebb0a84886b061181429068eb98a920c413a5d82110020aa8e2a98a69051e7318a54c865a38ac1290838b9516210f21c3cca29c82884787058653d0a9d384cb208438795163d4a1087cebb226290c3f76550540
  | 18 => 0x350a41e2ca6a88831066462945310829bb8ac4aa6631edc162151318deeca90a4a1d2c72550414c316b22a4296614b1c95415130ab2eb192a018e5a7614d300829cba0c7280630fddb54c85108f6e0b2a848853776144414831caa4c0108413a5d8218c020c5ea8b14a68863775587421062f39cc1a8a85699c86010421aaee6a88a2a163654d8542842e938ea8980616c5c062107218f4ec29a608847970d8953d072d31ea7906212d5db5310721ba2e2292601843e7498b5344387aa6a7a9221c914a6110510ea0a7a88a0a145e731944148296b90c12a4219c58651cc2308b8e6b0ca5a065853580424428fba2a629a43561cd4214121c3ca831a841943f769503208326b2aa790441d214a318c110cacc6b08a61066b5218142506b4b8486292218e5516090420a38e6b28829049f764c8329071d2a6c090c21d2dc9514c030c3ca831a8590d387054e414868fba2c4a98211bdc96550110a74e12a48298e5b53983324871c2a6c0a12418e1936054720cb2a7306851063854d81314426d39cc4880218e95160d04208f6e0b16a6885397098d540cad538665208439654d6088620a5ae52a0850856a70d93524c69db82a920a414b9ca6415131a5ae52a08598c6f7259531902b838ac4a86654e5c25390520b2ce39906420f90418c6304423cb80cb992839614d60d05108f4eb300648869963940501066d3b0a498061535ca6314d10ab0e6b0ca19963965552300825abb06420e43179ce65108108b8e6b2a40884bb7059132906cb38ea729c8317dcd62550208bae6328800846c725825110f4bb188290843565ce5114142a5aeb3108420d3775508410862ebb4a7180611e5c065d0f218b8e6b14a20863a545804208335a92c129263a5d8f61508418f2e1b28869065a5358031887543108288021cc90851d41428d8e4b2862a065b63181534868e39aa920a41995486150a30c3cc9a9e428843d74d9432086b2b88a710841a358d6214041b88e6b108210cd873583424c326a9cc5184419358f5288110c68e2b24a518d3671d48414c35220cc1908434d5d363d4542cb2c6a80a1a147976946100429cb80c52a6634b9c86095210b4ce51908210da671d495290696b90c928e8796d4d6094f21cb0a6302828866462d45314c237bb2a4294870f9d85450b20c3cc9a98648843f76550540431b2a2c2298419a197524c110cb6a7304658866862945100428e39aa82a2410f5d85210610a5ce9b0ea498d1e74d84534421eba4cb18e41365db530c310a76e0a988290d9a74d45300c29a38aa420e81c514e6110521968e2b04a620d3574d835150a6d38eca98061561cd4294031cb0eca8a601854c7354821c43a5b14a49806117dcd6295210a74e1320a890e6962980548c2d2b90c62084396d4f6050921cb6a6302428852d72d4c418428f3a0c4a
  | 19 => 0x83126390d3471592528c769a08c098863c914841c8510e64e220ea098ea463107210866c3b4a6880218b95262d433187eeca988290657531855050a36bacc421841a598e6114841a70e0a14a3a05387454550ccad238ac8190438e54960148418f4ec28aa19943f7559032c863dbb2a7080218e5d46050a41c3ac8a98640854d721835350b87aa0a518a634e5d33154031c3ec829aa4885547154c5350a9a38aa810841951cf6544010ccec430aa8997a362105100434d208c098e618bd53624c51087ce832e429843e74996214c21f3a0c6a9421179cc6510421a6ce32a2a21045c735954204387aa0a6292211e5da528802087eecaa0a8885a572180410873932ea22828547dcd6510520d36cb20a601863765905210869a3a2a228a410f9d85450a3287ae9b0aa01945d7518d21883583088298641879915314810a3ce7aa083104d873584200423d386cba1463171cd6494810caae231aa21063765905100421ebb083284432d9c4658c841b32e02986420e963218532106b9b82a7a8a855cdc53214121d6083b024210cb870591321070e320a6a92219c944604c420c6aa8b08a61043c7615121443623168298863e810660084208f4e1b2c8690e2f765484210696b90a9a00210f5d3650ca10a70e0b10a898c797018d51d0a97390c72a6633a1c1610c821c68ea30a84a065a7614f104431bba8c2a1681d8d08511414287ae9328601063774984530832a31ea2a8285479ce6415110b96e4b22601871653107218831ab8ec8a8c418b953624c4209b2e1318841861f64d4d3148735294c1990818ed516095131c72cb20c601061e6514c414432629cc521a85551c5538c920caac730ea918c7b76550504c6d83828520883871cd650c841a74e130aa810573714c8504c636392c229a814d9c75254241a38e8b12a6086b041580210429cba663a82435a5c26314910a68e8a88a29951e73d9641c829cba6c2282634b1d1521493087ee8b0ca6905cb724c5300c316b22c529a214e1d152d4131c98a7b12628853671d4c41c831caa4c1a9e438795163882108f4ec2a2a018ec862d81314c296bb6a52948356dd5624c030a6ce3b2882985347150851502b9b8aa7a8285c91c95110430c5aa8312871943e74d96200438ca9c8398021275d83210730e28a620e4290c7776544514cb463148298e614d5d763104218dce5b2a60885a7751042108297bb2a4290831e5d46050c10878e8b0ca19953671196418c2a6b90a9190630fdd16194332ce6c3b02a89963a5458031842adb82c229a85175ce65c8640a5ee8a98a4884ba70193329072da9ac1992411e9c065cc810ad2e42a6400853974d87504868eb9ca420a21cad4a41141318bce732e42204af764c8329061fbb2a998c21335db520ca31e32c8a9c200865b7654c300422fb9ac929021875d46
  | 20 => 0xc74580514cb0e322a690821175cf6590020e2aa620a2008731431445050a6cb9cc190a21879926314810878e8b0ca68872b52107504c78c382a6208214edd131d4121cb6a7b02a2a153970990544868eba0c5298219614e600c910ab4e198aa118c3d76d5041842a7396a7984219a14a60cc941e4ae3a908298e3a611815408296392a82a22196196324c110cb2c7306a80851d739944188733b28c4988634ddc560553218bce7b2e848863664547310c31caa0c098e433a5c8644c020a6ce3b2c821855a7318550ccb463108298a610fdd161d4f20b2cec20a6218d6a72cc4504866d3b662980419654e60cca20b48e4a1ea2a1478705845350a5ab88c999083c65d4414c030cb2c6318a0a171563144414c31daa4c12a243561cd42141318bee6b0ca00865553584530822e39acaa16211e9da524c110d36c7b028520e1d6454f3188334a90c090c21569c3315403187ceb326628843d74194300830eb2cc998c6317dcd6194b40cb6c7b02a8904cc735884188726b1ea529221b818b4144010e36a9188a098c5e73982529063d384ca1968396d8c6054420c58a8b16869943d75990320821ebb4a819663471cd6155020c74ca20c608843e74d943208726318a4a0a631b9c86510c2187cedaa2a4886365418542cc636b90ca20a61a598c4194321a3ae7b16a890e2e5458b538431caa4c018e43171cd65d09108bee6b2a808862e54588418870f322c6290218ed936054d10c68a8b0e6490f0e6454832cc335b16c0a9a21cc1456010520d32c8322601852c72585548422e39ac52a2414e1d1519433287ae832a621056970953524c738b0aa0280650f9c66414c20a3ce6314a998f1551106310c3d0208421002187995640c93087aec29c8210d5973105500c63a388caa1221879925314810cd4a5306641861d5458e50c870eb22a629e415cdc54294332b60e2b20418843e7614c41c828eb9ea520821c914c4108420bc4e19944210e5965980318c2d238a84210650f5da521063187eedaa06490c5f735825110a9bb8ac0aa6634d5c4539042087ee8b2a63904797518f200422ebb4a7188638ed94414c030cb2a7b0285105667190c524430f2a6c6a1663369c36348530e2aa6208431063554986408429b388cb208439598e61d533296eeab0e8420d2e7494f524423b38ccaa1261179d8534c7108b8e6b2a8290c3c7458453c822f3b6a6a12431ddd951146308eeeca88a221cb97610420c428fba2c3a9a2195d4d6194142cb2c7294401045d73d94428428eb9ecb20e410f5d854081108bce7b288410748520c630442b2392a3a08618d99351c8530c72a8b06a598c797518c200435820ac0188438e1516094931cc8a430a808861d6494c320429cbacc120841ca150528c110c58cab10829065765d8d210871daa0c0a0a210f9d9544c420c5aa
  | 21 => 0x69cb84c82a2639ad886054430e18a629482886345418542c430f2a0c6a166396d8260d4d42e18a720c4290d3a7494c50486b5b92a9a82630fdd564cc4208e8e2b28849853970994418863c382c528c879a997528c110a3ae7328820867365181310c69b38ea420a810f9d2658c420c3ec8a9a631063464d4521483a938864a8063179cf6590421a9ae5298640865a6354f20043523108298863e8dc04108420a38e6b14a9086c462145314c30e326a6a82431e9c36510b318eeeca88a2106365498732cc6d2bb08390843a594e6114e41c3acb2a6861943c7159353083a9a9ea3a828547dd16194e20a6ce232c82904b571d9332106cb38ea719083535c8540cb30a9ce5a9ca7a0c3e71d954310f0e2a6c6a92210fdd165484308bae7328840843d7499532c4317328a8292210fdd1650c520ce4c3306a99965953583328823db82caa1a430f5d260d4931a72e1b16a890e5a625805344317312a5288839698d60153308deeca90a50853974d84504861eba0c4a9c219a98960d4f21a5ce42a4831855970d90534425b394c3a98839658e6095121ab4e7b14a018e5a6398352842d8382a5288835a9ca538c1108dae532a87084787650950ccb2ca98c0a102127dcd62d404187ae832c640843e7498a510c2ab38ea929c41a3d90624c431a3ae8306a6a155a70d4d300829b388ca20841c315353149108bae7b2e821061e73994329065d386c4a9c83a518f6150841c3ac9a9ca690c7a709875350a9a392a220861695cb6010421c9ca6312200845d76d4c31c870e324a6908211e1d95344010c72cb2a6801070f5354a321069cb86c32a065d214f4214142a6ce5a88829871632144414c33830ec0aa26187590530c921a76e898aa018d597194d30c821f3a4c128865171cd6255020c3cc9a9e628845d7615232cc31d322c02984387597320c841ae6ea98ca018c6f7258c515021f3b0a8a82432d9c76254c41a70e0b12a998f185414c504871cb22c129a438b553624c420ad2e1b0ea498e2d64d4a1044392296c2a12811b9c865d0e10c5ac9a94a098e1d65d0c32106ac39a82282630f9db544c510e62e9a88a0a159671d4d531069a38a84a80859cd466094542a6ae3aa0821872952580521072ab1ac3aa441c614e414c210c68a830a608868e53588531065b38cc129083471d15314d218beeca9864905357498c5150a2f398cba1021aa5896014c41c6cca208429069462105310c69b388cb20a61179da5348410cb4e6302a2197865310421882adbaa6398021999486150810a74e12a08290d2d7294e4144339b2ec090843c654c41080109b4eda0a601864d53189100430eb24a6194414e5d32114121e48a420c208865853580314830e320a698a21c5d905314542ab4ed29a619053671196410c297396c32a0659654e608c810e1ea7a94828843
  | 22 => 0xa215a9cb5094043c58a9314a098c5d73d95404423bbb2a228a855adc931d4121e32a320a6018733641475050b1caa0c0a106553dc954d4d10c74a9300621061d6458e524432c31ec0aa2438759743d0832e308298aa018d5a708c8514c2b4b94c6a80638bd50624c510f40e0208421046e7299543c431daa6c0a92631b9da5248310a72e031ca998c3f765504148727b1ec4aa2214d5d35110530b60e0b108390c5d7694e20042adb82c5a9a211b9d7624c510ae0e2a80a0a1c3d74d94300421f3b4a8a14430f9d2658c720ab2e7a08a098db27014a511068fb9ac2aa6430fdd95415031ab0ec98aa018e3854181424ca37390ca21e211e9db3214131ccec5b0aa89852c72585540cb2da9cc4186211d5c765d0d208f2ed298a0a145f7654c5310ab4b80c8292211edd953c8010cc8a5308648865a75982324c399288839044156dd6310c0108bce732a840864e6314a204430e324a690c418b19562107208eaea30a86084d97398321cc333b2ec2a10859694f604c4109d0e4b08600853671d0e5110f32392c2298418ddd16114c20c5ca831262105c671d4c328863b3b6a2a82850f5da54cc610e2ea62086390c5c735942150354a92c029083535ca530c920c74a8b06a790c6c725964344326b18a5a0a630f1d95310520d62c220861884eb7558a300832db2ec688021d214e21d41218f6e0b288498d5a7214d308432aa9ac31802156dcd6114142c58c8292a098e586354d100428f398c52a421c61915344010c74a830285106d061c85300c32a298c2a82859314c624c510e30a6a18a0a15c872585300c2ad39ca498041531c95314d1087ceb326428857071540504cb16320c4a9a211b5c865d0c10a5ae52a0828852e72194414c23bbb2a228c818ed966090420a74e0314a998d5973d0950ccb4c208c098a615cdc1511454287aed2a66390e3576948410872a31ea290a412bdd95214841e6083a84a190ea471588501061f3b0a6208414bdc9531051087aec2a0648853a7418e50ccb2a29ac3282850f5d2650ca10d36c83026218e55639875404386a9aa4990834bdc9549053087ce9b2a408866462d85544c72ca9ec0988214d9c76494420d60c420a200847875580434422e39ac128885d2d4c52c4110b2ae6294a220c3c75593214429d380cb208611e1c16295031d54a8b146010564715485250e3c3aac019221475cc5450b20e96e6292608853471553424c316b20a41922187d935354121938e6b16a020c7b70588544431bb28c2a1083175ce6094a41b60e2a1680a071551104310c2b4b96c3286652e9c0650c841a9cea2186510e4c73588540c70fb20c6aa2211edc16590d21b64e12988390ea962540501078c2a0a7882219694c60508108f6eca80a121ee261983328869cb80c7aa2214bdc95390521aaee6a10a2a16b061d814290
  | 23 => 0x94e21d34c8300649851d7594c410431daa0c090a214d5d443107219b0e6b2841885b27018841c87c22186420843711c5424c832c6ce3b28821054e73d4821843a5a9462282630fddb54cc521a5ee8a9ea48861f6494d319029cb84a820a43661d1314c030cd2cb108400843f7654a414431a3a4c2298412d1c56408310c6ea830a849966a6298353842a6b94a619483551cd511454287eec2a06490e5a53d81318822ebb6a618c219694c614c320e4ce3a94a520ea95458a300838a2988298a211b5d662d0c21ce4c3306a91043f76550544c29b3b28628a850f9d265cc420d30c6302a420f1953580418838d39882a80630f5d36154810a3ae62a083906b041d8131c871daa0c098a218e55260cca108d8e4b2a8218658531812144316320a490a21471cd52944418baec18ca01855a70d87534863db82c329687171db53485108f4eda9a200847976d4c20042b4b86c9a9221ca148414c110e18a82946298e1f6454d210431cb2cc8100211bdd95414910c74a8302621059a740c9300c334294c02122187594418c430a6ee8b18a2a15c8724c530c8316aa0c4a06418ed516095121c9ca6312621071b5414c504870eaa2c7210650f9d3650ca10e48a6208431059a74c85300c32d31aa6100218e1536050910c3cc8a9865a0d3671194418c2b3b92c028a859614c6050921c70a8b06648869863d81429071db26c0a922156dcd62d4131a6ae32988290d3471548418c317324c5a9c21ac98660d4a41ad2e12a0a498c3c74586538829cba883a00419a58a6015031c6cc8b08a6104757694c5150a9cba065a82634d1c56355020a72e929ea090e1e65d4f4350b1bb8ac929463d25c05314910a76e8a96a098f275298441442b5b9262a80630f5d7644c420e1ca720c43105717194c5050b8c29882282439654d6014e21c38c9a9a6290c3e7419432842cab98c420e431d5db5410721c9ea7314a68864c635492110326b10c5298218d55061508308b8e6b2a848863954580210825cbb482100214b1d161d493195eeca90a520e5953982218831daa4c018a21569cf4254031e32e8192a018c5e7694d318438739ea5294830f5d065cc5208f2e131ca420e3b6555130083533b0642084393d943288730a3ae9b08a6a16b041181310c6d2b8e64208439614c604c510cb4a6302851072852904504c65cb86c9990833a1c1628c421c72a8b06650851e7498b534429c3a2a0282631ddd95114442ccec430aa89045e73d97410832d31ea1282858e5536050a10cb2a6b006210e5763d85544821fbb2a819041a654d60cc841ac8e4a88a2a055a7394d304431d2a4c028865471d12114d21974e032c6420e1f6598e41cc32ca9cc1208218ed976050842cb0c7a98418865853980314431c326c0a92219394d6210220c98c62924288539701514208717aa0c4a9
  | 24 => 0xb026290dc8724c5300c21f3a4c7288418b58d5214841b4ce42188390e5b53980314874830882980614b9d44188521ad4e5a84a198c6c76d49314423cb80cb21843551cd4214542d2cc7308a120e3454185324871a2a6c2a12634d9c7549522087ae9b2e631058d7214c321069b38ea8a04419ad8b6054d21e2aa62988210d3a70996410c74db18c0a90834d1c56494b108bce730ea0a163671994329070eb22a619483b418e5144010a72e02a2851966b52983325068eb98a420821721c931cc310c72a930062106a55218532106b8b8ca7a82854e1c162552108b8ed29a420861e65993314c23dbb285280630f5db53107218beeca98a720d387058a54cc735312c02a0635c5c75454332a6ceba18a2a146f76548520c23abb4a718863569cf6214121a5ce5aa28410d1c7355241442ad3a8c198a614e1d131d412187ce9b2a6290dca72d4d300838c20c6228263d414f51d41429d4ed202401063765191100435238ac4298839598551cc230d4cc620e4210c7870588544c71c320c0a9a4393d4c624c521e4ae3a9082885b07050841c861e3a2c3a9a41d8148614c110e1e86a946420e6762185534821fbb2a82a44195584518c130c5cc8b14a68863564984530829a3a2a2108418bd516294131cb0a730682884797099432d072c298c2982211e1c16295331caaa730c800863775587321065bba2c3990834ddd151104308baeda98621061d6414e504870f2a4c7a86434b9cb6195331a5ae42a4839875151885300c38c2a462282638b550624c420aaae229c621047a75d813148799a18a228285aa58a418c020c5ac8294a098d1e7314c41043982a662282639398e6215010a70eab0482984db7358b400829aba6a220a41479ce65904108daed2a0a498ea732185321062eb98c2a80854b9c75294a4187ae9b2840085357198154c8787aa0a7a92210f5d265887308bce7b2c400866b53189100421fba2c329661475d36154e2087ae9b28658863854181424871baa0c2a1a639a1486050910c76c9b02a39053a7498b504c765b10c098863b418c4144010cb0a7b02a2a143c7655121843a4a9065280639694c604c420b30e0b1882987a041580210831c2a4c199221ccd4c4144010c70e0b20a4986387059252c431ab2aa9884214e5d262d4131e96c6292608853a70d4e41c872c29ec098a435a5c85494031c74c9300a610e5753185424432731ac52a221569ce524c110cb2c6a80a020e4e6358854882ad384c3a9a850f5d3650c820c3ac929ea31054f72591538832cb1ac12a243ca14841d4131c3cc829e42886946418d100431d2a6c0a16619558c5194142cb2a6302651061f6494d2104354b10822004147dcd529444187ae8312a018c3d7614e410825b388cb994839a14a618c110c3cc8298648853671d9641cc3922a0a598a63871cd64
  | 25 => 0x41181310c67838ac6900411b5db52086108f2e132a8710e355498643cc636b96cba1e2147dd161d4d42cb2c7306a910cac725834350a9ab8ca820a61699c0321042187ce9314a39851e7319441c83d020842980419658d5014241a48e4a88821854c72547300c359b288288021c6550534c210caaa630a8610d3a7014e410431b2a0c2a1261e410531cc310cb2a6b04420847976d4820c4386b1aa42908317dcd641491087ce932e650856b7258550ccb2ca9cc4180211edd95014342c9aa6312621069963583529062fbb2a629a859654e60d0810e56a9a96a098f1b5458c504c69c3aac020a4117dcd6295120e4aea20843106a86450920082d938665288838798c4194020e62c9a88a0a167061d8152107b02966228263565d6530c01096ce2302a620c5f73584525028eb9ec5aa2638799353c8521c3ec929a431043d759932184358308c0a1281a3d90624c5308f6eca80a010e4f531894350aac39ac8a80634ddc56255210c68a930e8490d557114c3108316326c4a88618e9506050a3087eeab266390d1f74484534872cb2a63980211edd94214131ab0e0b0aa71064d53d89100421fbb2a8194218b1516210520ea68298aa018d5a70d8a530429b38ec9288651d1c56550830ad0e4aa6a098d3774544418826c382cb98c639618c60544208f4e0328640862f64d89510c31cb2ac8100219658e60d4a10c6ac828e62a05a671d49521074231082988634e1d13154031ccea430a84a069a63983529074631882908438ed906054420b66e0a148220d35769444188347b20c690843475d06014d42ab4ea18c608845e73994400430eb1c8328643691d1610c8218eee2b2a648851e731484104256bb064208431edc16194f42cb6a63026290d3a75907104421f3b4a8a062187191534c620ae2e3aa4a19946f76548524c69b38eca20c41d21c9514c0308eee2b2a851865b7654d100422ebaec6a14418d59664cc631c9cc6b10a80843d769943210696ba865208438d5506150810ab2e730ea0a168c64189310c68eba0c4a9821175da531481087ae9b0aa11951f7354841c429b38eca20c611e5c3658c910a6cebb188210c7571997420c31732ea420a63369d4604c5308f0e0b2c8690cb57198232107872988210c4117dcd62d4141c72a83026210479769505048735312c02a0439598e61d5221ad2e5b0ea0a15a670cc8410866db82c5a18658e59260d4e10a6ce2328839068c6418d210870e2a4c6212634b5cb6195210c6cc328e8120558735453008296392a720a21b2d8c6048421ac8e2a90a4a046c7258e511032db2ec098e618e99160d4f21c6ee930ea99971854d4f504861f3b4a8a12619a14b604c510c68ca208429854f754c8320c316b22a42902159dc94314542c5ac4314a998d3771548414438c29c83a8243ac184414c030c70a9
  | 26 => 0x9d3ac8228243a358d52148418f2e1b2a8690cb671994321066c3b263280639318f525094087ae9316a68861e6494e10042d8b8665288831ddd95114632ce4a2302631845e7399542442f138ea4106215cdc54294031a6eea20e421063754185428c68f398a820c416c9c33210721c76a83028490e6852983214432c32a60180419694d600c740a38e8b08a68861e6414f31443933a88210c41669d3314c0308f6eab10801051d73990544872ca9ac3980214e9c26355210c9eca31a4210c7870595321072ca9cc410021ac10660c851087ee8b0ca01971a75105300c30eb24a629021471d15314d2087eec2a6428862d64d48324421fba2c3280210f5d85290410e1ec72928520e696254050d0e2eb9cc1290838b553624c610976e0b2a6420f2452104214c297394a420a210f5d365cc420c5aa8b14601059b74545300c275b92c7a00410f9d06254331d4eecb108210c3d7695032082d9386c5288834e9d3615433287ce932c650847975991200828fba2c229a214b9ca5410510d40c420a200853575984410c38aa8882980619394f6244010968e2b206518d3571d4c41c832ca9ac018e414e9d36114121ad0e498aa018c6d72194430430f322a708021475cc60d5131c58a8b14a098f48528c4504c62f3a8c790a61c314f5290510c3cc9a9ca48863954d8143082acb8c64a80630fdd1650c910c3ca8b1e8398d38705885448717b20a490a210f9d8544c510cd2c4b04a898c3d7614e41c8297390c12a6431e5d66090c20d28c831a4210d1d7398154c8697b92c2aa663175ce6550910a5ce532c839865b75580310c21fbb2a998841561c93154031c38c9b1aa21071853d0c5050a96392ca20a619914b6150931cb2a6302621061d6454c520434db20c098a611e9c26550931c6aa830a8418c3e74180524438cb80a620a219654c604c610a6ae2298831045c75586324c22e39ac228285d214c214c02087ee8b0ea0995b37050841c86d3b92c6208439354c624c610cb2c6b00a810d5b73484504871db2ec0a16814d5c460d5131b62e19908390e726158354c431732a8421283171cd6194010ab2e0a9860086396590430043a8a8e62980614edc15490531b8ce22906518d2d72d96414c22f398caa0c41aa9046048421a6ae3b16a898c3c74595304431cb2c82100219c58660d521096ce232a6520da672d8c410865a38ac819021ca54a601484187eecaa0a89046f7654852cc64f3b08298e6196d856014d1096ce23286420d1e7394c414862c3b2a68802187993530c921cb4ea302629847771590524c29cba882200418b1516294d108f4e1b2e8690d4e7395052443862a6a7a9221879d46350a41e60a3300829063b64181534866d3b6a2980619618d5308010d30c83026218e4e6398a544421e3a2c3a9c413c5c46308310b32e9b0a6018690
  | 27 => 0x218d5964210421ae6e2a10a090d4c73544210838b29882108212d1c56294c418f4e03288710e5953582410432da9ac018e4387991530ca20aace7b16a2a15687250450487a4b80a7a92211e5db5410320e308398aa018e695258052d0e1ebacc8104211edd95014242d36c831a2008636549845308316326c4a9a431e1c165d0d21ab2ea18860084b771580321072aa9ac229c81569c26454c10ea2a6b08400862d6494832cc358b0882100215adc961141428f6e0b16a6a0e5a53d81420432d290c2980614e5c361953318f2e13288418e595318131882ad39ca9a82439654d60cc810b32e031ca81971b744c5500c78c19082a8063ac184414c020a3ee6aa48290d3a740c9500c61f3a6c2a9841e1188414c431cc8a430a608845c73595428429d3a883882218e951600c721ab4e1a9c6390f485314b104438daa6a7a82438b95162d0420ba4e229260184787058b535078629a8421243569cc4214131a9ce7a94a50843f7655054c8326b2ca7904411e5c365d0d10ad0e498ea090f197414c5050b8db2c8298061471cd6155321e628628ea0a164c5398843486363aac421a438759253cc410970e0b168620cd973d89200821ebb6a998a21569d8534c020c98c7a92428870e5350842882ac382c4a98211e9c2658ca41c5ec9b12a898c7a70994420c69dba2c2a86652edc162d0e41c6ca93088590f1553104210429bb828628a850f9d26548530c6ca9b0a84194b970192321061ebb6a821261475cc5450821878e2b20a49845d75991320ca9db82c2aa065179ce65080108dced29243086356595341c863d3b6a8a8063b2188604c431f08c61908210dc97098c328865b38cca994830f5d36154a30a5ae8318a48861e6310650c861eba4c128865b8d886048421d64c420a200863465107214c26c39ac010a61275db530c8419b2e031a821864e53988438831cb2882200414b1c95410531ae6e2a10a098f3174d475050a36392ca98e819398c5210931cb2a7300631053a74c8750486b4b90c828243661d1514c030b94e5b06629862f65191210869d3a065a8243965856014d10c76cab04821047a75983434832731ea5102214d5c762d5110c6aa830a8590d58705845350a78382c2196218759153cc410c5ea9b12a098e2c54d893144364b1843100411edd95414121c70a9b02a498d5a7214d300831b320a398a411b9d8524c5108f2ed290a098e1d6458c5204237396cb180214d9c46510530e96c5192a018c5e73d9520442ac382a629a83565c36214d10cd4a430242206365418542886b4b90a8100211e1d9514c020ba2e229a60105597094d31c861eba6ca98221479d6418c531b90e498ca018e1d64d4c3250697bb2a421083591c9431454287eeca9c8290e1e6498f52843862a0a6292219354c624c620a9aea2186410c3f7695331082
  | 28 => 0x4010ab6e6aa6a090e96631045008637b92ca18a819c98750941428deeca90a49865a63580540c795aa0a5a82638bd935254131a38e6b0aa90862f65551320ca36b94cb18e81c91484108610caecb29a200845f73597424431cb2c83080211ddd95114642cd6a4302848867051d81314c31ab288390e811e9db52540318eaea30a64086595358031d03472a2c4218650f5db5310420974e132a6520cda76cc5308426d3b0a8980610f5d36154c20c3ec8a9a620849e73982521071c2a4c129a434e9c25310721cd2c5306a70861d5418d42c869ab88a8208618e1c16510420a9aea1946210e6962980548821eba0c4a86634e5d6414c020c9ca6312632053a75107504871ab2cc4208438e55360508328e8e2b10a89853671d53408831ab288218843569c35394f21d2ac6208a010e1f54d8d42443a329e8210c41a618c60509408beeca98610869765105310c72c3b262a8063361cd60105308bae7b2c40084da7614d3008335290c0a14613a5db520831087aec2a66290e395458253c8726b1cc42a043171d85348510ba2e3a9a610854f7654832cc31caa2c199065695d44108420a76e0a9882885547354451483a42946498221179d8535414295ced20a4210c5d7399542042acbb6a6186210f9db5454931cb4ec29a608845c7694d100432bb2aa688021879506348610a98e6a94438843f7655050c86acb80a619443e4104604c431ea2a318c601063b65d9110042adb9aa5906214b5d26214910e608298aa018cb970194321072da9cc129a85531cd528874087ae931ca39065953980210430f2a6c6a104153dc95414d10c74e1b2c821043e74996210c335312c02a661c6d4c41d4121c3cc8a9e43106cb62181314c21e3a2c3a92618b9945210531a6ce3b22a99961f65d9131cc22fb9ac2a902187d95544c832c3ac9a9e428855a76949300c394382a421083d2948324c210a6ce3a94a520e2d76d4a529068e39ac0aa0658b1526210d21c72a8302861066452185425030f2a4c71042196d946344010acae3b26a498ea66254a511069c3a2c4a86650f5d065cca10e4ca430a8520c3d74180524430eb24c6290218b19352485108f0eca8a619043e749943008334310c0a886153dcd521491087ae9b2c60086a565988410872ca9ec0a10211e9c06550c21a5ae52a48298c3e74d9721cc395aa0a5882210f1d16314520ea4e229a601043c76d51214423cb86cb99221179da5350a2087eecaa06598da67098841086b5b82a429263e41053194031c5cc8b10a99843e75990324429b38e8628a85535cf64d49318bee6b2a850862e6458b538421f3a0cb99421479d361d4d21ad0e4a8a601843f7459521cc25d380c9190834edc16155321cb2a730664086585318530082cd3a0c4980612d9c465cc841a70e8a9e409065a53583320421fbb2a8200
  | 29 => 0x6628852d74d87524432c29cc1992436a5d03248020a6ce3210a2a159873582414c21ebb0a720c218e95160d4b31f40e0b108210ea464189310c61f3b0a890a211e5da51c8010c38c7a9aa420f185458c504c69a38aa82a2418b59052cc510b28e6a94a220e1c539874350b4c20ac0188618d5c76454732e96e498aa018c3e74d9632c4317b2ec890843565d7424c030d18c8312629862d6498a534421ebb4a8104218795163d4321c3ccb2986520eb261106200821ebb4a8298414e5c05390621c6ca830a841049d760ca41cc297390c72a041665c3320ca41c9ca63126390e3a54181428438ba9c8428a85569ce528c110aaae229a601055a70d4c31c861eba6cb908612e1c162d4c41e18c72928520e9a41580318c316aa0c498c210f1d1650c910c76cb2a2401047771592520c31a324a290c41365c064cc832a6ce3b2c839055872545300c38ca9ac0208219698d5384010c6aa9308a6106545318542442d9380c7288834e5d252d4131c9ca6312630855b70548328c752b108318843b21c0624c530b54e19948310d4e72d4e531021ebb4a720c434e5d06114142cb2cb1886008535739085150a3cb86cba1c43ca15352d4131a6ce3aa2879943e74d85524423bb8acaa1a43a518c4148421c3ea831aa48852e7418c5244317b26c4a9a431e5d46050b32f2082188600847771595434432d298c098c814e9d26354332c3ea8b1ca890d39751804108335a96c098a21aa58a5014041c5ec9b12a88865853d81414423cbb0a8106210f5da52104218dcea312628853575984410861fbb2a8204410f9d85454931c5cc8294208862e54588430823bbb2a8208438799353cc521cb0a7b028490e566358754cc71caa4c19906596d8c6055121c5ac9290400856572d8f5150a9d3a0a4a80639518e5148430a6aeb30883104777654451c832c29ac1992434d9d351947328f2e132a8790e4f63189544c717aa4c529a21179d46350921d36c63028420c3e74d94200432a29ec2a0221d294d2008010a5ce5b0ca90847b765405050e3c382c628a85ca148418c110ab4e630ca19945e73d96424431bb8ac9a8a61179db535412196aec1908210ed061545300c30fb24a6988210f1d1650c520b62e03108210d1c735505444326b18a410a618358d5214841cb2c7300a4084787058652d0f4d31ac029083b118c61508428bae6328840851c7454e3248237390ca200210f5da5310621c3ac929e631043f74596324438b2988210c414e9d441141318beeca98a790e1d6414f3148637394ca98a819654c60486209b2ed188600849e76905310c7a4a98c4880219318c5250940ab2e7b10a0a165a53d81428829ab8cc0aa0416a1c16210421a9ce5318a68865853980434432c29cc0182219658c53c4110a3ce72a082885a67190421082c639aa519083c654c418
  | 30 => 0x695052cc7982a64228243c594c414c721cd0c5b02a8985a672994410870f32ea829a211bdc963944408bee6b2a809051c7354a41c43922908210a21471cd5290510ab6e0aa6a690e35651043104316322a4990838ed526094d21a3ae732c82085657218c5150a3cbb4a9200818d54e61d4a41b60e0a108210e5b60983534872aa9ac2100218e152600c510ab0e6a8c601062c54d89504c6cbb9aa5288832e5c064cca41ab6e0b08a690e3854181314430fb20a698a439694c604c721a5ee4aa0a898e3654d8542cc758320c0988638ed964144010cd0a5306648845f7654c538829d380ca208410fdd5640cb31a90e498aa018e396599040082ca39ac420e432e9c0654c8418dee4b28829854e73953524430e2a6c6a82438e5506048610cc8c4a8a632047970d96329078c29883882210f1d95390520c3ec9b1aa88861e64d4c204432ca9cc1a1c411b5d66348421ab0e6a80a0a16b0611814210762318c4880214e9c25310521a74e998ea090da471508420822f39ec4a848395d946348421e32e829a601063954580540872ca9cc1108214b1c95354841c6eea30a84a065965cc73004296392a820a2187d92534c620d30c8302629845e7614d300832cb2ec1188614d9c45390420a6ce3b2c829043f765505308296392c2aa663729cf6248020c70a8302a690c3e74d97310822eb98cba1421c9dd5621042187aec294830846f76548529023db82cba1263871936354d10cb0e7b2a200854d750c8310871b2a0c2994214d5d76190841c72a8302630843d76550328431d2a6c098c219659432cc0108f6e0b288690c7975181420429b38ea92a665719c7520ca31c58a8312628843c74587504ca9aba4a4208438e5506050b31cb4a6302630872852907104429abaec020e430fdd85408110ab6e0b16a690c5f7654c53886ac382a629a430f5da54904418f2e0b2862085597095053486b5386a5296838b1506254d109b4edaa260184e87158a3008399a18a3a8285665d0524c030a5ae42a4831851e73952414863d386cb994830f1d5640c91087ee8b0ea49861e65d4c414870eaa6c6a1041d414f21141218b8e6b20a48863554584500ca36b90ca20021179ce6550b10ba0e2a12601843e7695141c861fbb2a82a4439694d60cca20c70a9b028490c3e75993314871daa6c098a433a1c1610ca21ae0e2a18a098cbb7058b5310716326c4a9a410f9d85454131cd0a5b02848863754185424422f3b0a6a12219a14960cc910878e8b0ca690e9863905100431a324a2908619354c624c721a3ae63288210c7771595420429bb8aa420e814d9c46590730e32a7300831051d73950414868f3a0c1298210f9d262946308f0e0b2a8598c7471595434828f398c52a0410fdd95390510c72caaa4610855a7098c534861f3b6a8a9a2195d8f6155121cd0a4b
  | 31 => 0xdbb284282439a1496008530aaae7306a2a143c7650e5110eacb84a798e43a598e5114041a3ee8b08a690d4872545300c2b8b8ec82826317dcd6508540a3ce732883104ea72989100435930883a06412d1c5600c841ab2e0310a6885657118c52442a739ec4a94219658e6015021b2ee6b108390dc8724c530082a6b96c329c410f5d66110420ad6e4a08a090c797598d10042cb388a7190838b1906254430d90c5b02639865863d8152c42d938c8288021565c2530cb21e30a7a1ea0a17a041086300833930ac1aa063699c86210421caea630a8490db270d4c41c869bb8ac52a4218bd906254430b62e031ca220d3671951510ca36b96cb18021ac1876050940ab2ebb04621853874548504c70eb22a619481369db314c1108f4e032e8790d9671d4d539072d308c0a98218e59641cc010caac6a88a210659639805404386aa264190418bd944148020d90c430262986355418542083862a0a7a9221171cd65487408bee6b10a88845d75d8d420431db2aa8900410f1d16194b3087ee8b08a6105a576cc8410869abacc2208634e9c05390621ae0e0a88a29961f5418d424429b38eca20a411e1d94254031d2aa7308a620c3e76151420868f39ec32a421c69915384010b4aec1908210e2f64149314421f3a0c0a96634e1c15490531a38e6b10a888718744c5500c6d9380a7288838dd944108440c70a8b066490d5975905300c297394a720a21c65d33154031c3cc8a9e631051d73150418831caa6c0a0841699c85410721a5ae43288398659531813204316aa4c5208434d9ca6510421a3ae7b0ca81047b70597434866cb8cc1192612e5c0658c841aa8e6a88a2a053a74cc5500c62ebb0a9190630f9d76448510ab4e7b0ea0a16d061085300c30e320c6a88411e5c365d0d21c3ac9a9ca68861c63d0d521062fbaac7100219394f624c410a5aeb20842106695298332102363b0a498a21565cf61d414287ee8b00a29963776544410c2973a8a420a21879506350820cceca312200862f6510521086963a2a429263965c26394910a6ce2328829055a758c9308431bb28c8908438b9945290510ca8a6b0c868846d721974384326a9ec4988218d1936154d10c3cc9a9ca090d4e72d87534421eba6c2a9e4196594310c0109b4ec28a601853974cc7504c71c2a0c090a2147dcd5210510d2e8630a851964d63988540428eba4c5a9a2147dcd4294441e2aa620e200861f65905300c23bbb2a228a41965d463440108baed2a0a690e705158021503a4b18a42826387d536354121a5ee4aa48288555711805348738a88c098c81c994c4108620c6aca20e620865763185544c22eb9cc029221555c75454e20c5ec9a92428861d6454c3208637bb2a429683c65ce4154031c9ea6312638861e6458f528421f3a6c2a9c41c3d4c5210510cb2a63026390c3d7
  | 32 => 0x18b5935294910ab4e1312a60847b76540500cb0e324a698821e85c33210421c3ec8a9aa31065a63982544862f3b4a6988415adc95414131cd4c4b04a88846d76950524428fb9aa920a21879926394910ad4e531aa018cb87058841d03a439262a8063c5dcd431454296cec2128220d707058c5150a2e39ac3286859a14960d0510aaae2304a71063b5418153486acb9ec8282634d9c464944208f2e132e8710e73515803150327b1ec4a9221279da414c530a6ce3218a2a1e1c6494d31103993888228243561d5214c030c98a7b126290d737150c504c71d326a1282439654d60084108b8e6b28848843c7459521cc32729ec498c418ed536050921a76e8a80a098e1c6354d429070eb28a6190839cd876055121c76e0b24a58863a65d50504c78a29c8428a854d9c75210410cb0eca9e400861e6354f52907a539064a80634e1c161550328daea312861059974d45300c29b3a6a390a61a958862107218f2e132e8418c3f74584538828f398a920e41499c75294a41d60c2302842145c73594414831db2c82900412d9da4148421a38e6aa48290d3b7054a418c61ebb4a8286634d1c55415132b52e420e819043d7694e410c70e322a6988210fdd95414432c72a8b06a790cb870584329069c382c52a4212e5d260887408beeca98a4085d071591300c34db18c0a1681175cf65481108f2ea302861061d64d4c204421ebb6a820e63cc9c44114131a3ae9b0ea6886685218141442ad398c228285ac5806094441a5ee8a90a498e9863181421061eba6cb1962187d96414c431c68a830a8490556739835150a9db82a920a438b592520c83196ce5308a620e587654c200428f39ccb208432d9c4654c84187cecaa2421051d73981540830fb9ac929463ac9844110320a70e8a80a09943e74d9530443a4392a790021c654e41c8220a3ae9b08a68855873589500c61eba4ca98a416a1c94314142a3ce8314a60853671d5343ccb94290c0a12811d9c46510c20c5ac5a80a020c3c7458653c8297390a920e614b9c8651043087eecaa0a99863464d8552443a429ea5882210f9d0650c020aa8e2a98a6a055b7350b504869c3a2a628243561d4324c110e48a53088298e2f64189534431c2a4c1a0a2195d8f6155132a6ce3298839062d64d48324c72c29cc198a218d59441c8440ab2eb318600873271106500c70fb28c898e61959975314542c5ec8312a898d3a70d8654c871cb22a028465a9d906150842a58e4aa6849865863d81524423dbaac690041565c06414d1087eeca9882885967318041c869a38aa998841b8188604c431a6aeda88829055b75591300c38ca988288021179db5354910c76a83028498e2f64149504c63db82ca992210fdd16094432c3cc829ca48851c7354a41d032bb18c2aa2419358d6215010ab2ea196600856872591500c63
  | 33 => 0x4108eaeb3224210c797694e300c34d31cc029083179da534c721a9ee6b20a498c3d7614c410833830ec0a9a41ac1846050b408f0e0b10a2a1e1c6414d504879828cc120a81cc1072114121caaa630a85106596554f20882d8382c4208430f5da54143218beeca98a7906a46210531c86b4b96c3a826356dd53154031ae0e0a88a2a165a5318131103a529064a8063875926314f20b32e990a601863a741815210637b92cb21a21595c86014542d60833006390e5463d85544871db20c0aa2659c1846055132c5ac8a90659847a75181424c71a322a290c418b9935284110cd6c6296208851d749815388338b08a3982610f9d6640c9419d0e0b146310f2b52104504c696392a6a1083d254f6244010a58e8a90a48851d7318254c868f3a4c0a9821175cc6550810d60823026390e3764185544c21f3b0a42082117dcd6510520d18c420a63987197414f5050a2f39eca21421565c26314f21e32a620e600863965106300831a324a490843569ce524c2109b0ed28a60186d2618c6300c2cab98c420843a518c41440108f2e1b2c8790cb575d85321065a3b26528883561cd54d4121f44e19908210cba70193321069d384a820a63365c263c8430a6eeab108210e2c54d89314870eb20a790a21179db5454c10a76e8a98a090e6b651814210b17328a420a2193d94624c730c72cab24200843d769524210a37396cba1a218ed5260cc9219b4eda9260184af764c832106d2b9686208434e9c06295210a9ee4b22a60863664984530822f39ecb200414e5c25310520c6ce33286420d397018e54c869dba2c4a8665179ce6588740e50a8296a098c3f76d5020442acb80a8190634d5d7431072193eec9906420cd973181410c30fb20a6a8243e158f3210421e36a829a608851c735504148358308c0a9083c68ca41540318f4e131ea2a153671d944108352324a4908435c1c542d4121cb0a730486886956310650c869b390a220a61875915314c21c68a930e808856a72151500c636b96ca21a216c9c06310721c3ea8b1ca88865963980548830fa9cc220a218e5506050a30e28a620c628843e7498b53c4334b12c02a063a658e5014241a70e0a988290e4d5318930c8316b24c4298431edd9518c020c3cc8a9ea31065b7654c200429db82a820a411edd95014031a3ae9318a690d73715405050b2ca9cc119481561d5314c020c5aa9b12861045c7358a548432c29ac190a210f9d3654c910c3aa831a841045e7399521502d53866420843879536354420e18a829c4290d3571d48414c29cb84a720e435adc95014131976e0b226420c9e73982529068eb9ea920c419ad8b6055131a3ce7b0ca81061d7418d521078639aa4290834d9c45310410cd0a4b00848847b765405088726b1cc52a2638d5966110421c38a8b1882985a77558841086a6b90c929c4
  | 34 => 0x8a2a147475586434421fbb2a821e650fdd95415310c70a93066490e98631814210b8820a62a80638d5506150930a72e029c8210c3f7655042c830fb26c6a884169dd83210421ba4e2298618865a65183314c22e39ac52a0210f9d7644c510c3cc8aa086196356558041086acbaca6100219694d60cca21c68e830aa69065853580434438d29c82986418b15162d012087aeb326421053974d875050a8eb9ea42082187594430c841a6ae2298821052e76149425021f3b6a898a431e5d660d08108deeca90a4a0e1d54d8d41cc70e2a0c6a1241561cd42d4121caac7a8ca0a1786530c8410861eba4c128c659654d6014f42a9ee4b08a68866a62580548cb832988210c41c9d484108510ce2a2b00a21943e71d91534833532ea42826372dc9514c030cb2caa98600862d65552210828f3a6c329c411e5da5114142a76e0a94a220d3970996410c637b92c028a879314e62d052187aeb3266390e3954982418c32c32ea698221c5d4c410c6108f0eca10a098d1c7458453486d93a6c2880211e9c06590c21c5ac9a9662885577154c5350b932908210c614e9c26510621d2ca630a6420e596354050086f1388a410621335d8320853093ae7304a520e685298032442b5b82c829263179ce6590620c3aa931ea190f5153d05100421ebacc8196431e9d831d41218f2ea3028418e595318a100428e39ac42a2431e5c36510d21a98e4b22a60869763185429063dbaac118821331c56210c328bce632c840845d7399542c42ccb98c020e411edd95014141976e0b086420e5b63181544cba4a984210021ac107604c421a3ce7b2c8210d4e73d4a218423a38aca19281961c1658c430c38c929a631064e53189310429cbac83180419a9896095131caea7b0a848854c73548525070eaa2c62a0439394c624c440c72a9306a598e5953980310431bb2ec890843a6104604c730c9ecbb1263984b67199532106acb98a9904419598d61d522087aeb326621063765105210876830882980618d59462107218f4e03288610cb976104200426dbb284980610f9d365cc910c5aa8b10a99865863181544869d386c5aa2438d1c564149308deeca90a420c747159532102cd3846520a610fdd954151319b4e1b1e429864e5398b41882d9380c4208438dd944144010ad0e4a8c6018559758c5300c31daa4c121a219698d6094910cb6a7b02428843c7650a5110a6cb98c0908619398d6215031cb2eda98618852f745485244335a90c0a1263e10c8418c4218bcebb1a848843c76951310831baa0c2a1641369cf6048530c6ca830a84086e061885200831d2a0c0a10615c1c542540318f2ed28860084d876545300c2acba88298061475ce6510620c9ac7310a91847b76540509069b38cc6aa0650f1d16194010d36ca20a601847970d895390787b9aa4290839354c624c
  | 35 => 0xd0a5110a37b92caa1a434d5d441c8420c6cc328e802061c5418d52442cc3a2c2980610f5d0658ca10c98a63126290c3471590524c23db82c628a854bdc961552109b0ec90a601843d769503284296392a82a263c99484108730cb4c6b00a610d39740c8504c61eba4cb99421965965308010a3ee8b0ea690d717190d500c63dbaac1990635c1c1531454287aec298830853b74589500c6ad386c6a9e430fdd161948308bee6b10a98847a75d814244333b2ec4880219a94b6050b30f08642086210cb67198232106a639aa8292219a94960ccb3087ee8b2a608863654986208421fbaac990c219318c5250941c72a8b04841074b53884504871732ea520a214d5da5210421a74e9b0ea090f0e531062188387aa0a710a438759353c85218bceca9a420845d739875050b87a9ea420a218ed946444010970e8b1a401061e6494c320425a3a2c319643ac184414c21087aeb320650865a5358031c43162a4c5a0a434d1c55310420a5ae5298828863a5458332842f138665a08434d5da5110430e30a720a608862d54189430831b2a4c2184212edd95014041a6ee2aa0829054d72150324c32ca9ac018c43c614c414c210cb0a6302a2a143c74588514c38ca9cc1208214d1c665105108b8e6b2c848865a63582544863cbb664282430f1d161d4c20d48c220a401045d73994400430f324a79082187d976350842ab2e6310a098c6f76548528c71daa2c19924356dd5214c030c72cab20418851d73952414430eaa6c6a1421875536350b21e2ea72988390e3571d91510c31cb2ec02084117dd95414d21c5aa8b10a80847a70d95434874c318c0a16819ad4a60cc9108bce6302a3a17285414b1044352b108420e434b9cb65905308dce5b2e878865663d465150aa6b98c0292638b5886295210878e8b2a6290f294210a50ccab539087286659914a618c931c58c829262884ad760c841886b4392a02828787190534c521c6aca2084218659654c0300431cb2aa9884211d5c76590d21c5acab206410c6e72d96434431abb6a220a612b5d83290421ad4e1a94a421c6d72d95404421ebb4a8294211ddd95114742ab0e6a12a018d3970d8654c870eaa6c6a884187991530c810ab4ec29a610861d6454c32c833930ac1aa665531c5520cb30cb2a7b02651063764945319034ab1cc2284834d9c76590530d2aa7308a720c3e76d51214431b3288318a21331d9424c832a3ce632c831071b5390430c432cb2ca618021a61906344010c3cc8a9e42084b676cca511063d384caa1e431e9d4604c5218f4eb3066490e596554c200422eb9ecb2084374dc5624c03087ce9b28648862d54588540c6e938ea6186218b9926294d108f4e1b2e65a0cda7098b314c32d31ac12a2218e9516010c20e1aa419483986356558c4108733a90c2992639614d60cc920cacca29
  | 36 => 0x38cc9a9841631cd6210421a6ae1210a2a153571d4c4188334b14c12a243475d26314d10ab0e0b16a690d377158d54c863d3b06228243565c43254031cb4a2302639863954580548ca8f39ec5aa2218b591520c831b1ae52986520e58611815304236b94cb988811b5ca6590630a5ce52a48298e5965983328ca6cb9cc0210618d5506150a10a72e0314a990c5c73584525030f324a790c414bdc95410530c6eca20843a063454185324c72ca9ac1990838dd946150842e66e8288a0a147b7058a5110f1b3288390a210f9d854500108f4e032a8418cdb76485300c316312a4a80830f9d0654ca10ab4e598aa018d1e73d4a41843a429c42980418d59654c4210cd2a631220085357518c41c868eb9ec5aa22196195314c110a74e13288218e3965180410831caa6c0a0c21c99cb6414542c6eca3226218e585318131486a6b90a619621cc54c4144010b62e19908210e5a53181218823d380cba18434ddc55210410c3cc9a9ca68862c54189314871ab2ec6208430f5da5490c43d48c420a62885b370508410863b38ecba1a410f5d4644c72187ce8312a70861e64d4e534861eba4c528c611edd931540318f4ec292a018d5b73509500c72ca9ac020c411e1c16550d21d62c2208600857071591500c764318c090843c615053d4121b28e2b206518c3e7695131c863cb86cb994831e9c365d0e21c5ec9a92628852f7254c414861eba4c7288418d9506150831a3ee8880a68862c5498a534421eba0ca19421c6d51300c110c74ca2a0a098d4d72d87534430e2a6c6a1265175ce65d0810a38e6a14a220c5d73997211031db2aa8984214d9c65310520ad2ebb04421063964980520438d2a260180410f5d83294441a5ee4aa0a8886395458332cc61fbb2a4294831e5d76050831c74c8b04a690d1f73588544879828ac020a6117dd95314e10cb4a6302631065453185204431d2a4c1994210fdd1654c521e18a620c4290e585398031487a4a9ca410021ca90621141218eee2b2a859864c62145314c392a888210c419659560cca32c72a9b028598e5863d815448334a92c0290835a1c95014141a70e0a948318f9363105100438639aa421083171cd62153109b2e131e82185727194c5050b2cb1ca788421a9d844148421d96c6312200851c7454c534430e2a6c6a12215c1c15114543c5ea9b126290c3d74996218c297390a820c618799641cc530a74eb20ea098e1e6414c204432ca98c4880214e5d032141218f6eca80a0a164c6294531cc25abb6a820e430f9d46448510ab6e6a90418846e72194414c21f3b0a8a18638d5506150a208f2e1b288790e3a54d81428432ca9ec0a182147dcd5190420a68e2a9082187a041086200829cba06528063479cc6510420b48e4a88821864e53189318831c2a0c0a12631bdc9654c110d4aec20e4210d3671
  | 37 => 0x2ddd93294441e4cc428882905a67214e511072ca9cc1a18214d9cb4314542c5cc8296428843f7459532042743b28490041ca14b6050940a3ce632c820843f745953244339b08c0aa263a598e61d4a41f08e6b108210d9671d4e531063bb8acaa1061569c86054c10a74e029c8210d6472544410c23d3b4a6986418b990520c9108f6eca80a198e6a65148504c674b94c1208419a1486048510cb2a630286084ba70d9221d023d386caa12631e5db3294031c3ac9a9c208871451105314c29c382c2aa643ca1484114131d34a6b00a720da672d80410872cb2aa708021591c54314931c9ac7310a99072452105314423cb80cb21c438d9506150b30a6ce232883984b970197321071baa0c2a146596d4d6094542a5ee4aa08298ec963886200821eba4ca994214ddc55210730ab4eb19260886b041580310423cb86cba12214e5c35390721d52c4b0082905697295020c423dbb2a028465c9d4a6110531c72a8b006390d3776144414c38a2a0a708221565cf52c8010ab2eb30a601869b63d81421071bba8c2a10856a1c943d41428f6eca90a098e3964982534866c3b2a688021965c265cc5308bcedaa2a71064d53189438831d326a1282639354c624c440cd2cb306651966862d81544c62eb9eca21041275d8530c841e52e1a94a520d6a72949304434ab1ca2280834e5d05294031c68a830a849947b7058a540c72cb1aa0284435a9c361d4931c6ee2b24a410e2c64d49504c63cb86cb21a418dd9441c8430b40e0b108210c7771595321023cbb4a82826347dcd6155210cd0a4302628843d7498a510432c318c0a90830f9d06254c108f6e0b14a998cb67199432906b5394a828263569cc4154031a5ee4a8c821874963d48504c637b92c229a81c598c5110530d6082302628863854181314861fba2c628a41565c2538c920e608318aa018c3d74d94324438d2a0a6980418d15061509108beeca8e6018656631465050b1632aa4990835a9ca53c4110d64c3300a620d3b74548504c74a318c2a1483b1188414c43187aed2a0a21965a63583540c66d3b08498061369d6608c93087ae832a650847b76540504878ca9cc0208214d9c76510720ab2e1b0ea690ea8641812108734290c0a126327dd95314e41e18a6290828853775104210838ca8882980612e5c0650ca41aaae6300a2a153576d44414c2d938664208438d59543104218deeca90a5a061d5458c54c8297394cb2086395d4d6194d42a6eeca88821853571d48415030f320a6192430f9d85290410d60c3b028420c3d761532144334294c018a218dd96414c4318eeeca88a3a052d7215041cc31c2a4c018a43655c43210431c3cc829e4290e1e6494c328828eb98a9a16410f9d36154332c72a93066598f8762105310c71c2a4c021a21561cd2114121a5ce4328831852d75105200821f
  | 38 => 0x30c74c8b00a9195967314a511071d2a6c098e43c554441cc030b2ae63008390e5a63d4250487173b4a4a148365dcd4210721a3ce6328820862d64548520c69a38a8728e85361d9315403196aeb30e6420e1e6514c414878d3a064a80638d153614c11087ae8310a690539701534208717b26c4a92215c5c46394332cc8c430aa89869964183314c2b838a64282630f1d564cc521c58cab108210e4e630865008335b10c0aa2639a14a60d051087eedaa0648861e6494f31042e439263980212e9c364cca41c5aa8b16a198e1c5418d424421e3a2ca99021d194e51886209b0e0b286518d1c73550414422eb9ecba16219a148614c1108eeeca88a2a06b06110530442ac382a629a8596d4d600c5408dce5b2886887305158241502b5396a1286831e9d8524c21087ae831aa50845f735845050b0f322a7988210fdd95410c31c5ac9316a70861c5398441442cd3888298061725c0530ca21a5ae4304a998dd071589300c30fb26c6a92214e5c06295032c3ca931ca190f3251580418834b31cc2280836c9d84144010c3ea9b1a428861e54d8d210830eb20a610221c654e410c010c74a8b06830853a70d4c41c86b9baa62a80638b5935294931a68e2aa0621045d73194200422eb9ccb2102127dcd654c841ab4e1192a018cb47159032c877031082880219654d6014e41d64c33066420e5a65d4e304423dbb2a618021a3d90624c730c76a93066498f19544c0300826d390c098a61c994b6150a41e4ea4208429863a54181420cacb38c829886396d8c6054841c3aa831a850863b64d8151cc32631ec4aa2438b58d5210841a3ce7320a890d3874484504878caa0a698041935886254c1087aeb326630866862d815344395aa6a428263531cd51884208bee6b2a821063774987540c31daa6c0a1263179cf65d0b1087aedaa66290c7b70590524c69bb8aa720a418e9506050b21d48c8312200861f6518d4210a5cb84ca99483a69516388020d60c3b02842143e74194214c3a830aa2980618799163949108f2e032a6420fa041085200832ca98c0988814e9c263550208f2e1b2c8690c3c74595324423cbb4a51822147dcd529074087ee8b2a621062e65d48414430e326c6a92218d95161ccb31cb2cb29c200863a54580428432d29ac019641c6950534c210c3ca831aa21043f76550548430f328a829a2187d906355120c76a8b066498c5e7614d3084316326c4a92218b991520c840a3ce6304a81956872550504c74cb1aa0284834e9d253d4121c38a831a8518e9553987321078da9c82282439ad886055132c76a8302a498e1e5418d420c717322a590881361c163105308bced29a6510c3f74597324429ab868628a854d5d060d4542e96e1a98a48861f5498e524423cbb4a6282438759153c8620cd2a4302422053b7058a54cc71daa4c12a263
  | 39 => 0x431865563987548870fb20c6a88414e5d35154332cb6e1b2a6218d967318841c865bb8ac421883e10c84108530aaae3aa4a71043f76550548c30eb1883286438e9526094f2187ae9b2864084797098e5290716326a498a218e95360484208beeca98a62055a73d0950ccae9b8a84980618755163d4321e4ce53288210c3f76553210831631284a80839318f5250941ab6e6a88a0a165853d812144355b20c090843ac98441d0020ea2a7b0a200869954583320ca1f3a4c5a82639614d600c540e2ea730882886b061d8142d030f2a0c6a16618ddd06155130cb6a6b00630846f76548524429cba643a824359dc54314931caca6b08600843e74d94320822e39ac2a9021665c0538c8418deeca90a51845e7518d21442d238a64190839ad97605084287ee8b0ca71045f73595219021eba4c5a9e2117dd95388010a6ee2b02a81964c5318931c429cb80c62a2214e5c254905318bce6328858875151d05300c38ca9c83900214b1c95310510c3ac8a9e632043e74d85534429a38a8528e810f5d262d4131a9ce5b1aa7086c462d45314c21f3b0a8a9a21721c9314c210a3ce7294828866952181428c2a6b90a8190634edc16215110ae0e2a98a0a165b6554d100421ebb6a821c63535ca54d4d108f2e1b2e8518c6f72595311022eb9ccaa1421879d06354b40ae4e0318a2a15737058c5150b4cb1cc1a9483361c16390530a74e0328821846f7558432086ad386c4a98211b9ca6590630c98c6312a8887877358841087a529064980619694d600c720968e2b20650871564d4f5150a3d384c7294834e9c06295032c6ca8b0c410845e73980524432ca9ac1a1c41c614c41d4121d4cc42086210c7875580424425d3b4828802117dcd6550910a5ce5a9c830855a73d89500c6abb8ac4a9c410f1d1654c120d32a8b1c401045f7654c300831b326a398a41175cf6254341c5ca9b1263085b07150b40c821e3a2ca988414b9d64188521c5ea83126290e5463d85544822eb98cb210219a589501404187ae932c621045d7598e200428fb9aa82a243a654d6014c41ab4e5b2a601863464145314c32c29ac019221ac9856014841ba6e2b22601861e6454c321023b38ccaa10219cd876055120c72c9306a50871a52905300c26739cc690843c6d50538c110a68e8a8e439069b6418131cc368208c098863179ce65c8640c6ca830a859943e74194200438c29c8298041175d85388110ce4c2b06a910d1f73550544421e38ac829841699c86310721b28e29906420c5e73197428426cb9cc1a08618b5516290020ae0e2990a090c7a76d5150cca1ebb0a720e43b818a5144010e36a829ea090cd870584320c69cb84ca208634d9d35194430e488210ca01053a740cb504c66d3b64298061aa588418c0208bce6328400845f7358a5104335baac5180418719563105
  | 40 => 0x800002200501d00e4010f6b009003800200100880100060590000020196040000001800600c002012000403e0080010010038000010800c00c002000006c00400580580040de01202d8018001410006000400500203f401f6c6000003403e00200a800c064007000002803602f03c8c9800131e0060064000004001800418c140002803000402900100d0000126079000c0020150000014040000015816000000100a004400e08b009812c15200400b8e0816824b000808801000012137e4004004004002c002000009001800200b00686a00000000218ba00003da00300600040a3001821c010001001800800200400052e7218e54842adbaa62986414e5c054d0a32c3ea8b1c40887145310531c431cb2882100210f9d854549108dae532c839864d63548521072729ac5a0c41875d06354b408d8e4b0ca00865463d85524422ebb6a6186219c1476048520a72e129c8290ea5760c84108732310a298a6196dd95384010c6acba188210e386118154083a229e8428a859254c6244010c70cbaa2608843d7655032082acb86c429a431b1c9654c640cb2c6318a090d59750c63008236b96cba0861179cf6510020a5ae532c8218d3974d4650ccb1a3a2c229841691c54210a20a3ce7a9482086585318131c426739cc190843b418c6048421c6aa830a8790d947350a411078c2a0a698221c454c4144010c38a8b1e809861e6414f314870f2a2c7100419394d62cc6208ecec28aa0a15697218f5050b1cb24c1a9e430f1d16154810ae2e1298a2a147870597424c71a2a4c3a1a638755063544208f6eca80a021d1d739905444316b26a598a63361c16308530e32a6b04820863b64d81510cb1ab288390861531cd54d4910ad0e0a90a4a1eb261104400831cb2882180214edd12114121a6ee8b00a2a166965583328cad339686208439514f6150910e60a220e609843d74d95324438aa9883988210f5d26294430c98a6b16609061f64d8d5344327b1ec4a9a211d5c76590d20c76a93006290d6b7259150cca2e3b4a6a1021d29c8534c020d32c720c401053675984414c31d2a2c0188411e9c06354742c76a83026290ea762105310866c39ac110a611ddd95114432cd2c4314a018c3f761533144354208c0908438799253cc620c9cc6a94439863b54d812144236392ca20a61879506350b32cc8c528a632072652107218429db82a820a638dd946150b40ad4e12a6a498f1774d4c5150b35b10c0a9a439a59560cca21d30c320a60185727094f5150b2c328a6982210f9d85450531d4aca208431054d73190524c61fbb2a82a6639ad4b6050931974e132c6520cf17118c20042aa38aa61924196d965344010a70e8b0aa19965b53582534861fbb2a82a0619598d61d5332c6ca9b0a841053a7014c410434d29ac19908317dd9531462087ee8b2a
  | 41 => 0x80aa170000804402800800609c2160002029000000006e008000c014195023009c0a400300000e009875a00380000a4004000040800c05a044801404609a00280000b0000000801802a06d0008090004001010007800200e00d0000284000000000005000000a01480380120000004000015000003403c00505e817c01c000002837804000100003580e000f04c004c000057000001c06c026002800002a00101d82d81c40070000a2445804c01c802c11402a00086e418e02300000040000bd03a810409a04e05980000ec0250318840000034007800000c04203500080ea007013004c0240c600780cc08c01100980940140a40778154000079007009806400000a813c02600701f800400000700901900c800903b017c02001e000804805a00702a800422601301a018000208e00103e804428b013000000600900a010c02c004034820000001301901c80120120038004026000019021400400101c00180b4039001000400c00f012802810a04a007807c00002202d80000060ce02b800400600d000008400a032003000000200a00c8038000034000000008603800481200104a102100300060050050114000000000800000a008028000c098009003817c06a00401c022c000003001003c07e00924e9bb822a0011c9020802200400d802000c00305c00003600010020048010012001800003ea2001f00280d20b8081027807811400400400000010760040e3601900d831000600000600541c0034034809c00402101e800002600000000d8360017004805400801e00080040ae01100f002800600000280c001000100000b40ee34e0290004000001025000c0b201800b847800c05b00002700200340030070076000000009001001a063800001c04001080c400002c008800406e0000d501540000fa002801000e0f8001801402400100180e01c0000009001c02e00300fbf8400000100000280000158190064000006000001878c01500500dde8200000e82a491002d01e800000601401180c40060c1002000c00000e0228264290000031001c04d15b005000401a0021738000024001005008805e08e033801401200c003000800204402eacbc04602a57e800004202000089145fc00000b800000a00103580340a400000c0068000065010800421e00000b000801823900b809800602a000005c006000013000c032006004813cf9a000001800804800200d333804f4af006005c00c038028804000000100185e00280bd0308004000011001800436c00001e000400000b00200123a01b900100b800208a03000ec33e02200200ec098004000003800c01a031000802000002d0098002007000000002204500c099866000308c809000000000a8234000291016802c01a00001300bc00c00000580540000002b5004001000c092001400004e
  | 42 => 0x13802c02201104b805c00a00800200040000001d8000c01c002001803808a02100b002c000004074002402402c015008c29600000b800000401c06a801000000200d0ccc450045020801c00208600103e400a054000800400000000b000107847a07580800000020050007276002005818413e00e02a818c00200003b80080420040000100000018001803c00a376000801421c7a20058000082005003805001a003021800000401202d81280462ad00000100220020000020040088004002400c002004811c014000000800005000c008000801403901480040040e100580601c201f00203f817616b000024131800708a8004016013005000409208b000805000400f004805800000003c80000002c0000001400203b024009401a00100115e003e00e6508000036001008803400402a00b805800002800105c0020006002000c00e04400100180b464604d800013005400000040ca000008831c0000090058024000017036800001a081003804c0240b2001029c01800c05d012437e01e000870c0000071ba80b8004004000800004e0340128008000001001000000200d0b200500aa187007806401405402f00141a81b300000780821af00000a0000970000002c00001100d82d4008007227800404e02c00a005800000100697a91b405901701a04100c00010000164002004805c01a00004a019000a01d00e00cc05800400100000da0000010018000002005819410c015000804000001400300b00dc0100d2001004c00400481b400e000001809000e00700180041de2cb0de000017e00100081b00200000070748052000000858401006d006800000c00101000880600180c102e401e00100002c8080005000800c212003030016000c13e002013000a01c00000bc0ee69c005805a20c00016a009000005800a8018000000002807403445a001001000801f064800000402102d000000400f01180d800a085003000001600304800400f000f02f00b012a01100c0208048000006015014e00d0a9013c02601a000802c2980058fc000800004f000809800002503500d800202502c8000000000005807c00003e000003c04800c001001800001c001004002c02e0cf01b400212600680080780033448008068fbb006007400800906f806000e00200000040480000001988000002003811c02c010012804c00c0580060410000024010822401c0b500f000804a17d001808c074402015bca401825a023809800602400800fc02600802081140300230000014000076000000c00016300f00080480040000018044015027006005a000003003401206a003006800400100e80f000400000d40980060050b781cc20401b001021400600300d003c056367001850003c02201c0078008000016038400400107c00440bc007000000003402f001001
  | 43 => 0xc07400101100540000dd00001f4094020035000008a007001800c00200001a827c1f000c0478240016006003800835c026006808403c0000999758012000001c76402a00801680100000100020004024008053801008a006003003c036e16009000000003d000800800a054000000000403602c803808200c010000027401f008000c01203b127016400002300b80600f82b802400f400000c0320b10000011008000400200302981f002000d00d011c05c00f00b80c800c010004000004e00c00700ac000008001000003e0030e20bf045610b000035002c035004023c00900912180080b201f8ad801c0622020143e1c00a000001001401e03d00000e800001f01d80a97ce03001380200000000068014014001023801805e00b040801000203c00080c80001a600000541640f100002109ae2540018000000000006000404200001701ec00000e02f01b00762950090020452000000012000a0450028000180018001002000000500b002019203200080d000401003a031c0100320188010028c8a01f000002404400101a4010c29008491800421c00600e40020010090005328d0800180080026e2001803c0ba03c0020008002026015020c1a000705600900020ab00e80b663e00b02484bc878002001816001801702b00c0008037021800000a000000003000005700080100080007c481a402211a645828400000400380042f400600080240142d6047802002a03602b001400265219c800003c069007001037401500180000434c10000b2800002e02c001c61c043007002004c1fd018801000600c003006c05a005436811800000400d8064000009000000800200e01d000001600806e00f40100190018718000005001800c0eb46800f000000000200000b41ca095012009c000072001800048a01500c801001000000003dc0020680063ef001800200000d401a124002000c00601610280000b200000003580160c8008003034e0fd001800005200001480a000e02500100d801c05a00e001802004e039811d55e001007005803600000380d04c20090f18008012006002b34000001304c80380ae02801b002400408d00086dc012019000001800200b0210384160003000001c11e0020048084002059000007800006200000b402600f00f801c034000009801804007b00f80c002a01b00101880180b514b800800001301a80242c0004002000000200509204b401006d005000801e002007810c0d800003c800000200e00b02a8026010003807c00603501c0000006026000005800c08e009003c0000a7014000c000f1706a00080120080080064120000001003c02415901200000020060001100000001014800000405204a0000000000000811806c047000824000c02a001000803800f0d281004e60000000214022000009800000001
  | 44 => 0x2e91260050060064002717021808800a001041827809212001c011c000000000007001608c00300a000800003a00083ea03e003842c00001c0018194016007016803800003200287243aa0900270094052002000001405e007000000001c0c70000000002000009007802600c002db5c0005ee00001a00000000578000000017003800002c000008804000002401180080000e3040801c09a00b07a022408400e00006b800600b003040801001e0bd882800c00007e8000432008028800402a01400c800000000000080f40560070060110000000005005c05a00d000011001600503b004d69000401000c416401202d00400080000bb00540040140035d3401a011000804002c01400b802c040009026800c0402b8000000800a00704a001c02c01d0060028008009004800407a03e002000001c0000d182c8140004007001c01c00e00880b80000010020068040001006804002600d01780b00024b4025005c00201500380d401c0240600008042016008001c000027000005400403b000039405600000300a401e04a04380
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x86150a41c85735886210721a30815506054432d13535c25310721a0c8758d5214841d1075105314c110a8884588624c030b818018c3210421aa082584410c010ac081588624c030b04835484108740a0e8758d5214841e11631075094321e8062107604c431944815c8540c930c5175184414c030a44815886254c10b20815084294332aa28298c4144010c4a7614b314c110a1481591530c810b0482544414c03094887149314c110a498594c6244010c15651c5320c8419858718c3210421d12745c4534c020d21751c04108420c867310660c8421b118194c414c320c4876dc93154031e086454c6244010d11535c05310421e07639486150a41a9081590644c030e096354a6014841c157654c5310421b04835484108710e1053104604c710e0a635496014841b41811cc524c110c1876d915344010d127654c4144010c25651c54210820a0d831956210421b0882544414c030ca1625c06210721a488654c6244010d07531c94314542a90835844108010d12745c4534c210e126454d6108010e0553548614c841c6072185514c030c197558c4188020c2b875496014841d1375107214c030a51811896014d10b058518c3210421b8082544414c0309198714c414c020c51635c46314121a24825506150830e1063d4c4144010f0053104214c020b1284d85514c030c197654c4108010b4082546214c030c18761d1315403194a829d9514c030b06839d44108620ca0641c54248020e23531884144010e10761053154031c25651c94310421e1053184414c210d1274547314c030a488654f6244010e1175184414c030d04721053154031c48651c9314c110a928398c4144010c25651c5320c841b81831c04108420e06631042194020a5386546318c020e09531884144010f0382544414c030d11745c4534c020c19655c0530c841c28755896010520a308654c4144010d20711c15214841b118094c414c721b05850c8410c421b12808c85110530e8032105600c421c857618c3210421ca0711c16214041c9074185514c030aa2829884144010e116510731cc010924825c34314542b11810c84154031a2682dd96510421c27761c55214841c1876dd1514c030e1353584410c310e08835496014841d12745c43254031e09635496014841b4082544414c030e0462144414c530c17731c56494a31c29625c06295331e41531884144010b1082544414c030a8882590644c030e1275184414c030a908654c4144010d22715c35294a41c84641c5424c832c29755884110020e11535844108010d22719c35294a41a51811d95308010c15655cc6210421e1253184414c320f03721053154031c91645c4600c930e1353105600c721aa082584410c310a508654f4144010985870c8410c421e11531884144010926829db43145428d0815d8424c030
  | 1 => 0x1a188654c4144010d12871053154031930815d03214131c49651c931cc010e118518c4144010b21851042188020919870ca4154031990805c43210431c90761053194031e23651884144010aa0815884110020b118114c414c020b2082544418c030e108654c4144010c25751844148020aa0815096010820a248254c6150b40e80631884144010a0c845886254c109a0805cb4310421a888458c3248020c197654e4108010e1065105314c110e1175104604c431e81531884144010a908694c4144010e2052104604c510c4876dc9514c030e11631055014021e138654c4144010f0052105314c110c29655c860104209198714e414c020c30711c16414930a3281d956090420c15651c5640ca31a508654c4144010e1253104604c721e1053184414c020a2980195528c841b4082547414c030e8063d884144010d0a739c35294a41c25651c96010421c917310660c851085b855da310c010d06531c54210a20c0d655c8430c841e415318b4144010d20721053154031a24825506150b31b118114e414c020d80721053154031a518118f5308310b1086544414c030b11839c44154031d05739c75294a41d08531c94314142d10845c4534c020f01531042108010e20521876050940c9276107214c030c85769cc3210421c9274187214c030d127454f6144010c91735806094441f0052106318c110d08741c93154031f01531884144010c15659c7320c841a15831506150b20e04631486150940ac08158c3248020d4072d85514c030e1265106318c110b21851c04108420951819d7424c030e1061546414c030c4b761c9315403185b8754e6244010d4072d053154031b108058c5110530e0765188414c4318598714e60c8510e0453188414c710a4a82dd95344010e8362104604c431e1153584410c010a2682d506150a31d08731c15214841e82531884144010e2165104218c020e1086544414c030e21621456010520d04531c94314542d80731c16210421a30815516008420f0153d884144010d117510731cc010b208250c51d41429a2809ce6210421c49531c9610c010834815d06254c10a9086944414c030b128710531540318d3865c432cc310e09631c15214841a0d831956210720a108654c4144010d807210531cc3108e0815c8644c020d1275106318c110b04825c45310510e0b835496014841e07631486150940d80721053194031a24825506150930c48761c9514c030e83631884144010c1876dd13154031a4a82d4d600c610e22521876050a41aa1861042108010aa28098c41c8421b1284dc53154031c0d655c8530c841e05531884144010d08731c15210841d0b741c93154031d08741c9514c030e81631042188020984835cb6010421c2975588418c020b0682d4c410c610a188654e4144010c31751844148020e046394
  | 2 => 0x4214c030f0082544414c030d10731456010530e2052184414c110b048254441cc030c90761053154031c50865c4534c020e1053184414c110d107210531540319198714e414c210a92839884144010d1076105315403191a871053154031d11535c26110410c25651c96310421d8072105314c110c85631c54210832b0082544414c030c31655c06210421a4a8654c6244010a29821956010530c3071dc16414930b04815483210730a14815905308110c0d765483210730e01531884144010e095318a4144010e1185184414c030e4053184214c020a24815905208110c26621c54294740c88641c1424c832b0882546414c030b0482544418c430c1a7654c41440109a280ddb3210421b208250c5114142c5076545214c030c88641cd4248020d04731c55214841c19655c3320c841a2486148414c510d10711c15310410a24825506150a108588754d6108010b1286544414c030e1252184414c030e105310660c8510c19655cc6010420c1a7654e4144010a2980191528c841e11539884144010c91635c06394441c497314a60c8510a2980195524c841e205210660c8510e05631c55214841d00721053154031986839c26210421c24741c96114c20e1353105600c610c48761c93154031d1074545214c030d12545c4534c020e1254585300c210b128654c4144010c25651c5640c821e13761053154031aa080588418c421e08631486050940c18761d1514c030a28845886254031ac1811c0624c530c24721c56414930e22521846050a41e0b6454c6244010b81809cc3210421d08729053154031e0453188414c510c31651c56408310d11715c05310510d11545c4534c020d13845c4534c020e11531056008410c4472185514c030991819c232105309a0805cb6310421e0653188414c72185a869d95344010950855c4324c110c18761915344010d4072185514c030d1387544414c030b1387544414c030a0d821956310530e2081549601484185a86dd7214c030e08639486050a41a148654c4144010990815d0624c030a48825856014d10c9276107314c210d20721c15110430d04731c55210841a31801506150a32a1681995530ca41b418114e214c020cc072185514c030d0b741c9514c030d83731c16210421b0482544410c430c14731c56414930c9176106310c310e127654c4144010d40825c4534c020a3081551600c420a2682d506150b10e0963dc15214841a9086544414c030b2185dc04108420c0d735886295210c4872185514c030d8073dc16210421a0d831516210720c3071dc16494b10930815d06254031c17731c56414930b1280d4e5310721d06739c75294a4198587d8c3210421b2082544414c030a84815c86354841a60815886254031e21531884144010d12731075094321c31759844188020a498094c624c72
  | 3 => 0x135f4191a00002550001c0e02060003211011b8001a68004027208800182a0280042000f031880f29800460d0a0248a0f970140a7c0005002001604400080004cc86b1407c0804028ac4410258000e0303038060a0f0240413040d00409478500208078dc3200460584a04028002a4f068100200092d03201040b40a0e001600000000103c0029070ee04048000e09078181c000a0200021018082c00002408603068144000000087a03000040200000082819e1053104604c510d20711c15210841c51715806014d21d08721053154031b118594c4144010c4b531c9610c310b11859c4414c03091a879053154031e1153105600c410b1280d4c410c721c28875496014841e1165104310c010d40721053154031a14815506354420e20521846050940f00721053154031aa081588418c020c5276547414c030a0d831956210520919870c841540319198714c414c210c92645c4600c930914815d06254c10d1175104310c010e8062104604c431e1153105600c4219258714c4108420b108654c4144010d11751
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x238000000628008019010020002a002080102082500082100ee085d481588418c020b014b2a631082880216019094c6210531c8642730a9cc420a2008484261535844108010e003b6e420a62a806330292a1951105300c2c012ca98c420a20086109d882547414c030c02bb102a906420e6180576614630c841087802c6388e0a90a420d0225d631c15214841e00b98a420cc190a21a03532096110430c430210c422e229a601050465c5310660c8510a08cb8a630882980413019814c4108530083102ecc04e61908210d4025c52105314c110c40bb3003186420843a008620951105300c28252dba88390a6018680615631042188020d00410c2a8c8298061820872055258052106c032b298c420a20087001d8721053154031e01bb0e420a62a8063a018654c41084200428232e298c220a6108640a1072d85514c030b01496a620ac018c21900842097114d300828092eb18e2a90a420e10218825c4534c020b004b2a7b108288021a0086e0951105300c30110e41aa4b00a420ca066032105600c421c80bab063808210841a00832055258052107402a6412c22086008580a4b8654c4144010e00328e420a629822121296a195310510042a0124b8ae029882886085d4815884110020
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 42
  | 6 => 1947
  | 5 => 11355
  | 4 => 6815
  | 3 => 438
  | 2 => 49
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 8 => packedAt s5K8 (i*5) 5
  | 7 => packedAt s5K7 (i*16) 16
  | 6 => packedAt s5K6 (i*27) 27
  | 5 => packedAt s5K5 (i*38) 38
  | 4 => packedAt s5K4 (i*49) 49
  | 3 => packedAt s5K3 (i*60) 60
  | 2 => packedAt s5K2 (i*71) 71
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 8 => 2*((h/1+packedAt s5K8 (5+(h % 1)*1) 1) % 1)
  | 7 => 2*((h/28+packedAt s5K7 (672+(h % 28)*6) 6) % 42)
  | 6 => 2*((h/677+packedAt s5K6 (52569+(h % 677)*11) 11) % 1947)
  | 5 => 2*((h/3883+packedAt s5K5 (431490+(h % 3883)*14) 14) % 11355)
  | 4 => 2*((h/2285+packedAt s5K4 (333935+(h % 2285)*13) 13) % 6815)
  | 3 => 2*((h/160+packedAt s5K3 (26280+(h % 160)*9) 9) % 438)
  | 2 => 2*((h/37+packedAt s5K2 (3479+(h % 37)*6) 6) % 49)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xc07f01fff80ffffc0fff03f07ff83ffdf11e3f
  | 1 => 0xfffffffffff01ffff03fffffffffc07e3fffc7
  | 2 => 0x7ffe03ffffffffffc003ff81ffffffc1e3ff
  | 3 => 0xff800003ffffe03ffffffc0001ffff83fe03f8
  | 4 => 0xfffffffc0000003ffffffffffe000003fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x55294c2988e2449c02cb50b46a5a1ce4f10e1b
  | 1 => 0x830a14501121c904b01515508caa44281676c5
  | 2 => 0x2a44289aa24492295540826d2134a95341a16e
  | 3 => 0xc68b163448903b669a6d80849c73623ba03b0
  | 4 => 0x3070c183870e1c3b8e38e38e70043843edd800
  | _ => 0
def s5Atlas : Atlas := ⟨8,rawDecor 31 s5Pos s5Neg, 0xecc8e080ecc8e080ecc8e080ecc8e080ecc8e080ecc8e080ecc8e080ecc8e080ecc8e080ecc8e080ecc8e080ecc8e080ecc8e080ecc8e080ecc8e080ecc8e080, s5N, s5R, (fun _ _ => 0), s5I, []⟩
end PEqualNP.Outside.L_meta_36589
namespace PEqualNP.Outside.L_meta_36589
open PEqualNP.Outside.L_meta_36589.Model
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
  | 0 => 0xffffc07ffc01f807ffc03fff463e3ffdf11e3f
  | 1 => 0xf803ff80ffffffffffffc03fb9c9d9323fffc7
  | 2 => 0x3ffff0001fff80fffffffc1f1e1c3c1e3ff
  | 3 => 0x3fffffffe00000fffffc0fe01fe03fe03f8
  | 4 => 0x3fffffffffffff0000000fffe0003fffc00
  | 5 => 0xfffc00000000000000000000fffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x2879c00b2c28584352c20e5902120a54f10e1b
  | 1 => 0xb0884580558aab0c655a422a18c8d9301676c5
  | 2 => 0x8112aad5004135d109acb4b4c17161c341a16e
  | 3 => 0x222373669aec00824e373b08ee01be03ba03b0
  | 4 => 0x443bc78e371c6e780041c10f7be0003edd800
  | 5 => 0xc78020400380070400382020fdedf5a8000000
  | _ => 0
def gbRaw : List Sig := (rawDecor 63 gbPos gbNeg).map Prod.fst
def gbPools : List BoundPool := [(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 7, 0, gbRaw),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff, 7, 0, gbRaw),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff, 9, 0, gbRaw)]
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeaaaecc8e080eeeaeaaaecc8e080eeeaeaaaecc8e080eeeaeaaaecc8e080eeeaeaaaecc8e080eeeaeaaaecc8e080eeeaeaaaecc8e080eeeaeaaaecc8e080, gbN, gbR, gbH, gbI, gbPools⟩
end PEqualNP.Outside.L_meta_36589
namespace PEqualNP.Outside.L_meta_36589
open PEqualNP.Outside.L_meta_36589.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 3 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 6 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 1 := bs0_4_0
theorem alls0 : ∀ k ≤ 4, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_2_0 : Interval s1Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 1 := bs1_2_0
theorem alls1 : ∀ k ≤ 2, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
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
theorem bs3_2_0 : Interval s3Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 4 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 24 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_96 : Interval s3Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 117 := (concat bs3_4_0 bs3_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 46 := block_range (n:=46) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 46 := bs3_5_0
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
theorem bs4_2_0 : Interval s4Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 4 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 24 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_96 : Interval s4Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 117 := (concat bs4_4_0 bs4_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 46 := block_range (n:=46) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 46 := bs4_5_0
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
theorem bs5_2_0 : Interval s5Atlas 2 0 49 := block_range (n:=49) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 49 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_96 : Interval s5Atlas 3 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_192 : Interval s5Atlas 3 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_288 : Interval s5Atlas 3 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_384 : Interval s5Atlas 3 384 54 := block_range (n:=54) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 438 := (concat (concat bs5_3_0 bs5_3_96) (concat bs5_3_192 (concat bs5_3_288 bs5_3_384)))
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
theorem bs5_4_1248 : Interval s5Atlas 4 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1344 : Interval s5Atlas 4 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1440 : Interval s5Atlas 4 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1536 : Interval s5Atlas 4 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1632 : Interval s5Atlas 4 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1728 : Interval s5Atlas 4 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1824 : Interval s5Atlas 4 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1920 : Interval s5Atlas 4 1920 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_2016 : Interval s5Atlas 4 2016 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_2112 : Interval s5Atlas 4 2112 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_2208 : Interval s5Atlas 4 2208 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_2304 : Interval s5Atlas 4 2304 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_2400 : Interval s5Atlas 4 2400 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_2496 : Interval s5Atlas 4 2496 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_2592 : Interval s5Atlas 4 2592 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_2688 : Interval s5Atlas 4 2688 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_2784 : Interval s5Atlas 4 2784 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_2880 : Interval s5Atlas 4 2880 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_2976 : Interval s5Atlas 4 2976 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_3072 : Interval s5Atlas 4 3072 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_3168 : Interval s5Atlas 4 3168 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_3264 : Interval s5Atlas 4 3264 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_3360 : Interval s5Atlas 4 3360 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_3456 : Interval s5Atlas 4 3456 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_3552 : Interval s5Atlas 4 3552 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_3648 : Interval s5Atlas 4 3648 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_3744 : Interval s5Atlas 4 3744 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_3840 : Interval s5Atlas 4 3840 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_3936 : Interval s5Atlas 4 3936 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_4032 : Interval s5Atlas 4 4032 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_4128 : Interval s5Atlas 4 4128 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_4224 : Interval s5Atlas 4 4224 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_4320 : Interval s5Atlas 4 4320 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_4416 : Interval s5Atlas 4 4416 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_4512 : Interval s5Atlas 4 4512 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_4608 : Interval s5Atlas 4 4608 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_4704 : Interval s5Atlas 4 4704 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_4800 : Interval s5Atlas 4 4800 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_4896 : Interval s5Atlas 4 4896 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_4992 : Interval s5Atlas 4 4992 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_5088 : Interval s5Atlas 4 5088 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_5184 : Interval s5Atlas 4 5184 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_5280 : Interval s5Atlas 4 5280 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_5376 : Interval s5Atlas 4 5376 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_5472 : Interval s5Atlas 4 5472 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_5568 : Interval s5Atlas 4 5568 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_5664 : Interval s5Atlas 4 5664 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_5760 : Interval s5Atlas 4 5760 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_5856 : Interval s5Atlas 4 5856 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_5952 : Interval s5Atlas 4 5952 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_6048 : Interval s5Atlas 4 6048 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_6144 : Interval s5Atlas 4 6144 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_6240 : Interval s5Atlas 4 6240 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_6336 : Interval s5Atlas 4 6336 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_6432 : Interval s5Atlas 4 6432 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_6528 : Interval s5Atlas 4 6528 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_6624 : Interval s5Atlas 4 6624 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_6720 : Interval s5Atlas 4 6720 95 := block_range (n:=95) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 6815 := (concat (concat (concat (concat (concat (concat bs5_4_0 bs5_4_96) (concat bs5_4_192 bs5_4_288)) (concat (concat bs5_4_384 bs5_4_480) (concat bs5_4_576 bs5_4_672))) (concat (concat (concat bs5_4_768 bs5_4_864) (concat bs5_4_960 bs5_4_1056)) (concat (concat bs5_4_1152 bs5_4_1248) (concat bs5_4_1344 (concat bs5_4_1440 bs5_4_1536))))) (concat (concat (concat (concat bs5_4_1632 bs5_4_1728) (concat bs5_4_1824 bs5_4_1920)) (concat (concat bs5_4_2016 bs5_4_2112) (concat bs5_4_2208 (concat bs5_4_2304 bs5_4_2400)))) (concat (concat (concat bs5_4_2496 bs5_4_2592) (concat bs5_4_2688 bs5_4_2784)) (concat (concat bs5_4_2880 bs5_4_2976) (concat bs5_4_3072 (concat bs5_4_3168 bs5_4_3264)))))) (concat (concat (concat (concat (concat bs5_4_3360 bs5_4_3456) (concat bs5_4_3552 bs5_4_3648)) (concat (concat bs5_4_3744 bs5_4_3840) (concat bs5_4_3936 (concat bs5_4_4032 bs5_4_4128)))) (concat (concat (concat bs5_4_4224 bs5_4_4320) (concat bs5_4_4416 bs5_4_4512)) (concat (concat bs5_4_4608 bs5_4_4704) (concat bs5_4_4800 (concat bs5_4_4896 bs5_4_4992))))) (concat (concat (concat (concat bs5_4_5088 bs5_4_5184) (concat bs5_4_5280 bs5_4_5376)) (concat (concat bs5_4_5472 bs5_4_5568) (concat bs5_4_5664 (concat bs5_4_5760 bs5_4_5856)))) (concat (concat (concat bs5_4_5952 bs5_4_6048) (concat bs5_4_6144 bs5_4_6240)) (concat (concat bs5_4_6336 bs5_4_6432) (concat bs5_4_6528 (concat bs5_4_6624 bs5_4_6720)))))))
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
theorem bs5_5_864 : Interval s5Atlas 5 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_960 : Interval s5Atlas 5 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_1056 : Interval s5Atlas 5 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_1152 : Interval s5Atlas 5 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_1248 : Interval s5Atlas 5 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_1344 : Interval s5Atlas 5 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_1440 : Interval s5Atlas 5 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_1536 : Interval s5Atlas 5 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_1632 : Interval s5Atlas 5 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_1728 : Interval s5Atlas 5 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_1824 : Interval s5Atlas 5 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_1920 : Interval s5Atlas 5 1920 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_2016 : Interval s5Atlas 5 2016 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_2112 : Interval s5Atlas 5 2112 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_2208 : Interval s5Atlas 5 2208 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_2304 : Interval s5Atlas 5 2304 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_2400 : Interval s5Atlas 5 2400 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_2496 : Interval s5Atlas 5 2496 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_2592 : Interval s5Atlas 5 2592 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_2688 : Interval s5Atlas 5 2688 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_2784 : Interval s5Atlas 5 2784 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_2880 : Interval s5Atlas 5 2880 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_2976 : Interval s5Atlas 5 2976 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_3072 : Interval s5Atlas 5 3072 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_3168 : Interval s5Atlas 5 3168 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_3264 : Interval s5Atlas 5 3264 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_3360 : Interval s5Atlas 5 3360 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_3456 : Interval s5Atlas 5 3456 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_3552 : Interval s5Atlas 5 3552 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_3648 : Interval s5Atlas 5 3648 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_3744 : Interval s5Atlas 5 3744 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_3840 : Interval s5Atlas 5 3840 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_3936 : Interval s5Atlas 5 3936 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_4032 : Interval s5Atlas 5 4032 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_4128 : Interval s5Atlas 5 4128 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_4224 : Interval s5Atlas 5 4224 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_4320 : Interval s5Atlas 5 4320 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_4416 : Interval s5Atlas 5 4416 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_4512 : Interval s5Atlas 5 4512 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_4608 : Interval s5Atlas 5 4608 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_4704 : Interval s5Atlas 5 4704 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_4800 : Interval s5Atlas 5 4800 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_4896 : Interval s5Atlas 5 4896 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_4992 : Interval s5Atlas 5 4992 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_5088 : Interval s5Atlas 5 5088 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_5184 : Interval s5Atlas 5 5184 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_5280 : Interval s5Atlas 5 5280 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_5376 : Interval s5Atlas 5 5376 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_5472 : Interval s5Atlas 5 5472 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_5568 : Interval s5Atlas 5 5568 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_5664 : Interval s5Atlas 5 5664 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_5760 : Interval s5Atlas 5 5760 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_5856 : Interval s5Atlas 5 5856 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_5952 : Interval s5Atlas 5 5952 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_6048 : Interval s5Atlas 5 6048 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_6144 : Interval s5Atlas 5 6144 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_6240 : Interval s5Atlas 5 6240 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_6336 : Interval s5Atlas 5 6336 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_6432 : Interval s5Atlas 5 6432 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_6528 : Interval s5Atlas 5 6528 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_6624 : Interval s5Atlas 5 6624 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_6720 : Interval s5Atlas 5 6720 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_6816 : Interval s5Atlas 5 6816 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_6912 : Interval s5Atlas 5 6912 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_7008 : Interval s5Atlas 5 7008 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_7104 : Interval s5Atlas 5 7104 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_7200 : Interval s5Atlas 5 7200 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_7296 : Interval s5Atlas 5 7296 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_7392 : Interval s5Atlas 5 7392 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_7488 : Interval s5Atlas 5 7488 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_7584 : Interval s5Atlas 5 7584 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_7680 : Interval s5Atlas 5 7680 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_7776 : Interval s5Atlas 5 7776 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_7872 : Interval s5Atlas 5 7872 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_7968 : Interval s5Atlas 5 7968 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_8064 : Interval s5Atlas 5 8064 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_8160 : Interval s5Atlas 5 8160 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_8256 : Interval s5Atlas 5 8256 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_8352 : Interval s5Atlas 5 8352 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_8448 : Interval s5Atlas 5 8448 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_8544 : Interval s5Atlas 5 8544 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_8640 : Interval s5Atlas 5 8640 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_8736 : Interval s5Atlas 5 8736 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_8832 : Interval s5Atlas 5 8832 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_8928 : Interval s5Atlas 5 8928 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_9024 : Interval s5Atlas 5 9024 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_9120 : Interval s5Atlas 5 9120 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_9216 : Interval s5Atlas 5 9216 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_9312 : Interval s5Atlas 5 9312 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_9408 : Interval s5Atlas 5 9408 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_9504 : Interval s5Atlas 5 9504 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_9600 : Interval s5Atlas 5 9600 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_9696 : Interval s5Atlas 5 9696 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_9792 : Interval s5Atlas 5 9792 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_9888 : Interval s5Atlas 5 9888 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_9984 : Interval s5Atlas 5 9984 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_10080 : Interval s5Atlas 5 10080 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_10176 : Interval s5Atlas 5 10176 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_10272 : Interval s5Atlas 5 10272 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_10368 : Interval s5Atlas 5 10368 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_10464 : Interval s5Atlas 5 10464 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_10560 : Interval s5Atlas 5 10560 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_10656 : Interval s5Atlas 5 10656 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_10752 : Interval s5Atlas 5 10752 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_10848 : Interval s5Atlas 5 10848 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_10944 : Interval s5Atlas 5 10944 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_11040 : Interval s5Atlas 5 11040 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_11136 : Interval s5Atlas 5 11136 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_11232 : Interval s5Atlas 5 11232 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_11328 : Interval s5Atlas 5 11328 27 := block_range (n:=27) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 11355 := (concat (concat (concat (concat (concat (concat bs5_5_0 (concat bs5_5_96 bs5_5_192)) (concat (concat bs5_5_288 bs5_5_384) (concat bs5_5_480 bs5_5_576))) (concat (concat bs5_5_672 (concat bs5_5_768 bs5_5_864)) (concat (concat bs5_5_960 bs5_5_1056) (concat bs5_5_1152 bs5_5_1248)))) (concat (concat (concat bs5_5_1344 (concat bs5_5_1440 bs5_5_1536)) (concat (concat bs5_5_1632 bs5_5_1728) (concat bs5_5_1824 bs5_5_1920))) (concat (concat (concat bs5_5_2016 bs5_5_2112) (concat bs5_5_2208 bs5_5_2304)) (concat (concat bs5_5_2400 bs5_5_2496) (concat bs5_5_2592 bs5_5_2688))))) (concat (concat (concat (concat bs5_5_2784 (concat bs5_5_2880 bs5_5_2976)) (concat (concat bs5_5_3072 bs5_5_3168) (concat bs5_5_3264 bs5_5_3360))) (concat (concat (concat bs5_5_3456 bs5_5_3552) (concat bs5_5_3648 bs5_5_3744)) (concat (concat bs5_5_3840 bs5_5_3936) (concat bs5_5_4032 bs5_5_4128)))) (concat (concat (concat bs5_5_4224 (concat bs5_5_4320 bs5_5_4416)) (concat (concat bs5_5_4512 bs5_5_4608) (concat bs5_5_4704 bs5_5_4800))) (concat (concat (concat bs5_5_4896 bs5_5_4992) (concat bs5_5_5088 bs5_5_5184)) (concat (concat bs5_5_5280 bs5_5_5376) (concat bs5_5_5472 bs5_5_5568)))))) (concat (concat (concat (concat (concat bs5_5_5664 (concat bs5_5_5760 bs5_5_5856)) (concat (concat bs5_5_5952 bs5_5_6048) (concat bs5_5_6144 bs5_5_6240))) (concat (concat (concat bs5_5_6336 bs5_5_6432) (concat bs5_5_6528 bs5_5_6624)) (concat (concat bs5_5_6720 bs5_5_6816) (concat bs5_5_6912 bs5_5_7008)))) (concat (concat (concat bs5_5_7104 (concat bs5_5_7200 bs5_5_7296)) (concat (concat bs5_5_7392 bs5_5_7488) (concat bs5_5_7584 bs5_5_7680))) (concat (concat (concat bs5_5_7776 bs5_5_7872) (concat bs5_5_7968 bs5_5_8064)) (concat (concat bs5_5_8160 bs5_5_8256) (concat bs5_5_8352 bs5_5_8448))))) (concat (concat (concat (concat bs5_5_8544 (concat bs5_5_8640 bs5_5_8736)) (concat (concat bs5_5_8832 bs5_5_8928) (concat bs5_5_9024 bs5_5_9120))) (concat (concat (concat bs5_5_9216 bs5_5_9312) (concat bs5_5_9408 bs5_5_9504)) (concat (concat bs5_5_9600 bs5_5_9696) (concat bs5_5_9792 bs5_5_9888)))) (concat (concat (concat bs5_5_9984 (concat bs5_5_10080 bs5_5_10176)) (concat (concat bs5_5_10272 bs5_5_10368) (concat bs5_5_10464 bs5_5_10560))) (concat (concat (concat bs5_5_10656 bs5_5_10752) (concat bs5_5_10848 bs5_5_10944)) (concat (concat bs5_5_11040 bs5_5_11136) (concat bs5_5_11232 bs5_5_11328)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_96 : Interval s5Atlas 6 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_192 : Interval s5Atlas 6 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_288 : Interval s5Atlas 6 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_384 : Interval s5Atlas 6 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_480 : Interval s5Atlas 6 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_576 : Interval s5Atlas 6 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_672 : Interval s5Atlas 6 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_768 : Interval s5Atlas 6 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_864 : Interval s5Atlas 6 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_960 : Interval s5Atlas 6 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_1056 : Interval s5Atlas 6 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_1152 : Interval s5Atlas 6 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_1248 : Interval s5Atlas 6 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_1344 : Interval s5Atlas 6 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_1440 : Interval s5Atlas 6 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_1536 : Interval s5Atlas 6 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_1632 : Interval s5Atlas 6 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_1728 : Interval s5Atlas 6 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_1824 : Interval s5Atlas 6 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_1920 : Interval s5Atlas 6 1920 27 := block_range (n:=27) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 1947 := (concat (concat (concat (concat bs5_6_0 bs5_6_96) (concat bs5_6_192 (concat bs5_6_288 bs5_6_384))) (concat (concat bs5_6_480 bs5_6_576) (concat bs5_6_672 (concat bs5_6_768 bs5_6_864)))) (concat (concat (concat bs5_6_960 bs5_6_1056) (concat bs5_6_1152 (concat bs5_6_1248 bs5_6_1344))) (concat (concat bs5_6_1440 (concat bs5_6_1536 bs5_6_1632)) (concat bs5_6_1728 (concat bs5_6_1824 bs5_6_1920)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_7_0 : Interval s5Atlas 7 0 42 := block_range (n:=42) (by decide +kernel)
theorem alls5_7 : Interval s5Atlas 7 0 42 := bs5_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_8_0 : Interval s5Atlas 8 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_8 : Interval s5Atlas 8 0 1 := bs5_8_0
theorem alls5 : ∀ k ≤ 8, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
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
  · exact alls5_8 i (by omega) hi
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 5 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 3 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 18, 19),(inputs.getD 1 zero, 17, 19),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 5, 13),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 9 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) (pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact pv
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeaaaecc8e080eeeaeaaaecc8e080eeeaeaaaecc8e080eeeaeaaaecc8e080eeeaeaaaecc8e080eeeaeaaaecc8e080eeeaeaaaecc8e080eeeaeaaaecc8e080
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 18 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
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
  have q0 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff : Sig) 7 :=
    slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
  have q1 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff : Sig) 7 :=
    slice_correct (ms:=fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds4 certs4)
  have q2 : Slice true (roots gbAtlas) (target gbAtlas) (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff : Sig) 9 :=
    slice_correct (ms:=fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds5 certs5)
  have pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p :=
    List.forall_iff_forall_mem.1 (show List.Forall (fun p => ValidPool true (roots gbAtlas) (target gbAtlas) p) gbPools from ⟨build_valid q0 [] rfl, build_valid q1 [] rfl, build_valid q2 [] rfl⟩)
  have low := boundgb certgb allCuts pv
  have lift := lift_ok (u:=true) (ms:=fixRows 0 0) (raw:=fullRoots) (T:=fullWord) (xs:=[]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 0 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372906 * 2 ^ 32 + 3972587648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36589.Model.Repr at out
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

def mono : List Gate := [⟨.and,[1,2]⟩,⟨.or,[0,6]⟩,⟨.or,[5,6]⟩,⟨.and,[0,8]⟩,⟨.or,[3,7]⟩,⟨.and,[3,7]⟩,⟨.and,[2,11]⟩,⟨.and,[1,4]⟩,⟨.and,[10,13]⟩,⟨.or,[12,14]⟩,⟨.or,[9,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372906 * 2 ^ 32 + 3972587648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372906 * 2 ^ 32 + 3972587648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36589

open PEqualNP.Outside.L_meta_36589 in
theorem PEqualNP.Outside.L_meta_36589 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372906 * 2 ^ 32 + 3972587648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372906 * 2 ^ 32 + 3972587648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
