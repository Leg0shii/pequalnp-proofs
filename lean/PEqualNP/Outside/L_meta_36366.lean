import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, children closed at the parent by
-- restriction pools (closeChild of the model), and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36366.Model
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


end PEqualNP.Outside.L_meta_36366.Model

namespace PEqualNP.Outside.L_meta_36366
open PEqualNP.Outside.L_meta_36366.Model
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

def SBf (j : Nat) : Nat := [5, 8, 7, 8, 7, 7].getD j 0

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

end PEqualNP.Outside.L_meta_36366

namespace PEqualNP.Outside.L_meta_36366
open PEqualNP.Outside.L_meta_36366.Model
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
  | 4 => 2*((h/1+packedAt s0K4 (5+(h % 1)*1) 1) % 1)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x1ffc1fffff83f83fe0ff83fc3ffff03ec733f3
  | 2 => 0xe0ffe07c1ffc1fc3ff07fc1fc3c0ffc179cd9c
  | 3 => 0xffffff801ffffffc0007fffffc00ffff81fe1f
  | 4 => 0xffffffe0001ffffff8001fffff0001fe0fe0
  | 5 => 0xff00000000001fffffffffe000000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x4244451104250808a849a124065290944310b1
  | 2 => 0xca48c321292129416942a50c4286a584594594
  | 3 => 0x491080a5242129410844a52a8084a2980aa0a
  | 4 => 0x94a2124a034a54e65290421b312c0309ac0f40
  | 5 => 0x18c39c739c739f3b9ce7738222308c31f7f000
  | _ => 0
def s0Atlas : Atlas := ⟨4,rawDecor 62 s0Pos s0Neg, 0xfcfcfc00fcccfc00fcfcfc00fcccfc00fcfcfc00fcccfc00fcfcfc00fcccfc00fcfcfc00fcccfc00fcfcfc00fcccfc00fcfcfc00fcccfc00fcfcfc00fcccfc00, s0N, s0R, (fun _ _ => 0), s0I, []⟩
end PEqualNP.Outside.L_meta_36366
namespace PEqualNP.Outside.L_meta_36366
open PEqualNP.Outside.L_meta_36366.Model
def s1K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K6 : Nat → Nat
  | 0 => 0x1e0c02c04421150050011c0105148fc32fd42fd20ff31fe20fd32ff42ff21fd10fd43fc20fc10fe42fe21ff43fc30ff20fe31fd40fd30ff40fc21fd21ff10fc43fe10fd41fc31fe40ff30fc42ff32fc40fd31fe41fe43ff41fc41fe32fe30
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0xe43dc434c6fea498df94031bf296637f540437ca9905f94430bb28861fb304c3d884905f54f10de21c85bf54442fca8885f54840df218817d53083bc87995f54740ee29a217c540c2fca121f7cc030f7a14857c504c6fca9995f95331eea9e417e530c6fea6906f50b41f729481bd4310efea9906fd0441f699043dd31cc2fca2205fd4131af298853c544427ca8195f54b30bf290217f544837886215f15010bfa92837e5210afaa7a15f54332bf29e817e5090afaa7905f94832f7a14437d52887dc84995b54810fd88221de53906f8a090ef10640bfa98417e5290afea8885fd5030bea8861ed428ca7aa9105f14530be2a065f7318c6fca521fbd0920be2a263bd42902fca218f7d0e43f7908437c54086fca9106fd0d40bfa9621bf54486fca910df94331bd28043bc43d06fea090fb08620bfa90217d510cafca9197d90441ef996633e540c2fca0186f55021f790c437950086faa2207bc8720bfaa2617f54cc7daa5207754c10ef994657c54ccabca610df15320be298417d5090bbaa720df14e10be28a857f53442faa6207754c42f6a1085f5310c6faa121df14e20bfa9e437d5210efca6104f95331bf298837e544cafaa7a0df54a43bfa8a87ef52506f8a818fbc8220de21c817d5110afca0215754c21f7290217d5010af8a69077cca30be28a65fa100437e84a0df94a31bea98857d500cbbe8798df94621fd180617e51086fca7a0df94630bf280817e548c2fca918df14d41bfa92877c524c6fca710dfd4143f621443df4350efaa190cfd5110be29221be4390bbca6216f95021bea90637d544c6fca118ef90d43dfa10817e51cc2fca8215f15120dfa1c83dd32cc7ea20086f15130ef188617f54886fca5a1df94820f7a1285ed5210fea62885f94640fa908437e50d0bda65905f94b41bf2a063bf43d027ca918df54e21afa9a815e53c82fca6886f90c42bfa8a61fb20483dc43105f54640efa1c61be43d07be6218df940439faa261fb40902faa1197ec8220bfa9e41bd41503ea8220f7cc530be29e21bf4310ef8a9195b54843bfa9a85de4310ff621087b14910df2a6637f514cafaa1a1efd0d42be29a437d51ccbba86995f942419f2a4417d531077e8620df55240be2a6637f51483bc64995754c10bf2a6437c54882fca110df54021bf29221bd54c83de42907b54830beaa4637d508c6fca5a05fd4e21fd28043ef52442fea9087b14941bea9e43de314c6faa5105fd5021b729021de53043dc40905f55241bea8685ef324cafca6195f94c42ae29a217e5410f7a83a05b94b31bea8e616f52506fea8106f90e40f699443dd4310fb863185f54a40bea84437c52506faa7a07e54021bf29a437f524c3baa610df54e42bf29483de304c2faa4187794c21be2a261bf4210bf680a05f15121ee21e63dd328c2fea9995794e41
  | 1 => 0xd544caf8a0a14f55231bf2a081ee428cbeaa2185f54742beaa261f621087b887185f94843be282655c53502fca7085fd5232de2a2657e51082fca5195f15330f6990657f53843ee82a0fdc4010bf29061bf4290afca1a0df94720bf296217e518c6fea9986f509419e2a2437e51d0efaa718fecc230b6292215d53906faa690df54e30bf29e437d538cafaa610ef50d40ef99061bd54043dc84215f94d20bf28c857d52d02faa9216f10440fb288617d52d0fee6298cf15130beaa241f6104427ca9907d8c431be2a4637c54c86fca320efd0040bf288857d54cc6faa7105f55330fc980617e528c2faa3185f94643bfaa2637f540cbda84995f95121bea8c217c524c2fea9107b88420beaa465de53c82fca010df95210deaa0653e540437c84a06f55220bf29e217c525037a86a16fd0e43dfa16837e544c77886a0fb48421bf29e413d54086f8a9087dd0641b729481df324c6faa018d754f20be298217c52843be86185fd4d40beaa0637e5390ff240885f94240bfa9e21bf544cbf440885f94032f7190437e50d0ef8a4087b48020bf294217e51d0b7a84207b94843be28287df308c2d8a4a0ef55231bfa9c417d51c82faa6905f55010beaa061ec42086faa4085f54632de21281f631442fea5085f94e20be29a817d52107bea6a05f54c10fca00817f53042faa810f70c430dfa1481dc430c37ca918ef95032bf2a261be540c378862077d0d31bf29c8575510c2fea890df94840f719641ed21c8378a890df54043b6a90617d51d0fba6418774c030f6216417c53442fca418efd0540dea1e81bf40902faa4885f54643bea94617e530c2fca020fbd0b20aea9885f710843bc63185f15132bea88877d54083ba6498df54620beaa6417e54cc378a8886f90a41beaa6217e53d0a7aa998d7d4d10bf284417d54443ee4310ef50e41ef98c637d540cbf22008774c832beaa2437c5250fb8a6a05b54a40be29a85f9200837c80a06f90b40bfaa2653f544867aa818774c431be2a2217f51502faa1a0fe88020bf288217e52903788420df55321ee98a61bc42906dea4885b94830bfa9a43ed52042f8a2907b8ca21bf28c657e53907dc4290df94841bf28465be43506faa3217bd0821beaa4417d52843de65196f50c41dfa0c837e54082fca3a05f145439eaa021bc42d02faa7085f54041bf288877d52c42faa921fb8c8329eaa065be4250afca1995f94321be29621bf41d037ca9105f14c21be28a816e5210efca621ef50842bfa8a85be42106fea9885fd4d41bf280217c53886faa7206f90640bf2a6217e540cafea0a17750f32f690a417d51082f8a9887e48210deaa6637c50506fea818df14f20bea9c833d54c83ec63887b8c920ef21a65bf43d0b7ea8985f95030bf2a0837e5304278a8995fd4940fd104217d54ccafea918df54b31be29
  | 2 => 0x1a068000c0e118404038160140491c1921012001d612c00008091386c0000a0840d01c000300a3d8020945c00c07800031fc7300c5419c2e0341a098400b40a160020e4000000301800024d42f01f7b811030a604c010c43f0080300405150090001504c201b0000280f234010102b001677540208803014070d000078030241564400004030000201c410200700404030635a0280000a02cb10948902819170020289e000002fc46014211e40d0945f0980c0a016001f10560a0000f0880800c1521c4206c0001ddb0041a064120c87e1980177400090070000b22400130be068900080f00400004010700010c06014031080a00c080740100000004130041f07c02030060301a0c0473180498813000170085dbf298817e54042fca2195f54241deaa061be540437c82206f50040fa98e217f50507bea6886f90541bf29661ec21082faa9084f95021beaa4617e52086faa910df54331af29821fa40102fca3995b54b31bf2a0437e508c3da64905f94c21bfa82657d53442fca0105f94e40ef98e617d52906fea610fdc8521bf28c417f54c86f8a910fb94830bf288837c548c37a87a15fd5230dea08837e54c82fca8905f94210bea96833f544cbbe64195f54a31f7296637f52442f8a8107b54b31f7900417
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0xa524423d64d4e218f992528c25d63153218f990538823d65950308f993530872f54d49108f993530423e6415010c794c429071c6355030ab19121482ac62505409bd895110355514c0309ed95300c29d6310a41cb551520423e64947309758e528426d62d50109798c525071d5494f209dd9510043665294430b3588430c2cd63108219e195204436842540219b588540425e65cc53097596310c26c6254630cb189540866d62d52309ed81544c63d6414e108f99053c831e5390a419b988530436952440109b988504c63c6454031c758c544ca5d63948209b58854cc26e65d0920d398e52902ac64487208f990530426e65c8520ab58843902776155120c7951530876b21540218f59252842ae6290140c7d50534425f654c431c7d5353443553254430ab191328872c52509419758f540432e5454b31d5544310c25d63d52219798f540863d6494e219d984538825c6354041ab19132086776550441c7551530863f6550441c7952530423e64944319b98b540829e648c4308f596421072e54c8220ab992204823d64d4e209798e51d026d6215031d3d4c524423e6414b10ba181324832d54948308f992530c66d62d4c109d195314423e6510940c714e425023e65d0d429b594420863e64150218f99250c871c5310940c7553320c23e64d48108fd9153c872e5250a40cb55132c823c6454d10d9949510c23f6454632d314c524427960d4c219e980540866e62148108f59251cc27960d5021d358e529026d6294d10ab58843d066d658c8218fd9152c423f6550c418f191534834e534c821d954a510c23e6494d21cb951520432d548c832cd951510c23c6454b108f990540cb1d5454c109798c514823d6414c209798c54c863e64942329b988540426d62141318f59253c423d6414f208f596540871e53d0e418f992544865d6394a408f9925008279601502197596530872d54d0b20cb94b409023c6454e10cb952520c26d6214c109798f540c74d6314941ab18941d023e64d4f208f990530869c644ca309d587540c23f64543329b98b540c25c63542219758c540872d54548309dd95310c72d43548439758c520434e5394810d5cc9510c23d6494d21cb588544cb5443544308fd91534867b65480208f99053c867661d503097997434c75a53940218f191518c27960d5232c755343cc63e65d05409e58053087556114d109e980530866f62551108f590538823e64d4a109798e529038e43909329d984540823f6454630ba580218831e5454f209718d50d0a5d6394740ab189411065e63d5010c714f43502776154d209798c520431c548c1309b189544c72c5414910cb55252cc66e62943418fd91534427965840109798e544425e63150218fd91520c63f64542219798c52c423d64149319bd8954c426d62d50309758c540425e6394742
  | 1 => 0x876921540219b189534434f53d49108f592530c71c544c530d398a530872c4394a409798c540ca3d65950329d984540c32d5494810d354e4210b6a3254021d394d520432c62553208f990520435a53540218f191510838d43509329758c540826f6254630d314f524434d53948108f592508cb2c54909329b58a53c423c64549108fd954210a9d63109409758c52c426e62153318f593520426d62d52108f592510c71d53508429b58a50d0e3c6454b30cb950218827a60d52328fd91500c66e62d50109ed81534865f6550c438fd91510831d54cc8329d584540c34d4354843d654e500865d63947429d185534829e648c6308f992520823d65904409b195324823e6494a10ce552500863e65151309b18951d0e3d64d4a10d398a53c831d54d0c30ab5884390a3e65d09418f99251cca5c6550d328f593530436960149109b98a544432e54548309bd954210ad4614c93197d8d544423e64951328f992544431e5494c219e980540c71c53505409b98a534425f6355210c714d435032f43548439b98a539063d6414131d554d100423e6510d418f191520c69e63905418f592500831e54cc6319798c540823d6494a30c754c4310b1d5494c21a758c42d03685288110cd551510c32c54885219b98a53c434e6294e418f990538431d54ccb319d9845304355518c430ab5884310a6d62150309e580540c65e6315010c795253c823e65d0d40d354d4210b4e534cb20cb153524423f65500409e980520429c644c8308f19150cca5d6594c10a798e411023d65950108f992544c26f654c832cb952218823d6414c21d398c525065e63d48109e181544c65d63153209718d544426f6548020cb952520426d62d53319e181534863d6590c409b189511033a54540218f993538823e6494e21a7191300c34e43548439718d544823d64947329718d548431d5390c429d98754ccb5553c40108f99353c427a60d4c219b189544423e6414c209bd89544865f6354041c7152434ca3d64948209b988540ca5c63549109bd95210871c54d4d109b58854cc75743544308f590530427765484219b988538429d6310841d5547300c32e52d0a4097d8d544832d548c8218f191530832e43149419798c530874d6294e41c7150534431d544c8309d58754cca3e64d4e21c7552530426e62d5230d394932cc66f62551318f994544ca9e648c5319758f54087395454021a718d401025d63949108f59250c863d6414810cb551320ca3d6494d109b18954c426e62d53318f994544423e6494d109758f520427561150209b195424ca3e64141318f19153c863c64542218f99253c425d63d53208f593530872e5494b318f59353c825f654c0308f590514825d6314520c754f4210b365494430da54a10042cd6310a21d654d500863d6414f218fd91534834d53548109b98
  | 2 => 0x9008170143c124020680d0000b338021903d058070881e1704710419004000002a00c1b02000004460000103c0a05c0803c000cc00000130040d00418028000003301410030340015c000010bc1f0840411c3e0185500011188240514703002005430f0210000037c000f8020300d0740a02c616880207400148120186c03409008dd1500c01000004000580f0182602c1600801000b61245a0040700c010240009c0f000020000733000090000ec00024020041301800060b70015e090030448e090060f80609c0a0040f018000b8010040201c13058180b000000000c0020e81143c10000012354314400008610182a0380a080000080000e756114e20cb90e529031c63553318f990540c25e63d53108f191518ca5d6510c308f590534825d63d5310da4c9500866d6294d219b994524425e63d52219b58a539066d6214e109b596520434e6214d40cb14b425071e5454c1097d95320ca5f6354910cb94841902ad6210d419b98853502756114c209798f54c823e64949109ed95100426e62150309d984530823f6550840c755153c827b65500408f990524c76552544309b988540c65f63551309bd89534425f63542218fd91530834e524c8309b58a50d072d548cb208f592524423e6414d209b98a50d0f2c52905418f990514834d6214d408fd91524425e6314c10dad09500869e6390640a719132cc6cd6210e309b98b54842ad6210c40cb55342086e960084209d185544826f62547438f191534865e63153209798e528427a60d50218f994544866d6588420cd552510c25e63949109758c525072c4314941b358843cc6ac64484219b988530825e6394820ce952500869c644c9318fd91538426d6214d409b98854cc31e53d06419758e544431d544cb3197994534423f6550c438fd9152cc23d6590c42cb94a419023d64d4f109b58a5444354538c510b358c424832f54149109b98b530431c54cc530b358c42c831c5390140b3588434c71c53d0540cb55152cc71e5350e419798e534425f6354342ab19132c82ac644c920c7551320ca3d6414b10cb551320
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x2a090000000004808004d4008002000004803435ce5250a40a1ae431aa81841c7655132cc70731ca520c81451d13254430a1ae429a86a060c53189415020e3b2a899061435c86355331c18a731480a0549731095008686b98c4aa641515c84354430858ecaa2659061664546310c306b1ac42a265435cc6255021a1ae629284a0c2c7655132086943a264a80438398c5290541a1ae529a8720d287448550087152a2c010c4185191514c030
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x500080d8714c625054080d8714e629014080d8798c529054180d8798e5290640
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 664
  | 4 => 539
  | 3 => 25
  | 2 => 4
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s1K7 (i*5) 5
  | 6 => packedAt s1K6 (i*16) 16
  | 5 => packedAt s1K5 (i*27) 27
  | 4 => packedAt s1K4 (i*38) 38
  | 3 => packedAt s1K3 (i*49) 49
  | 2 => packedAt s1K2 (i*60) 60
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 7 => 2*((h/1+packedAt s1K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/20+packedAt s1K6 (640+(h % 20)*6) 6) % 40)
  | 5 => 2*((h/221+packedAt s1K5 (17928+(h % 221)*10) 10) % 664)
  | 4 => 2*((h/200+packedAt s1K4 (20482+(h % 200)*10) 10) % 539)
  | 3 => 2*((h/29+packedAt s1K3 (1225+(h % 29)*5) 5) % 25)
  | 2 => 2*((h/8+packedAt s1K2 (240+(h % 8)*2) 2) % 4)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x81fff83ffffe1e0ff87f87fe1fffe07d19f3f3
  | 2 => 0xfe1fffc1f87ffff07f87f87fe1c0fffee63c9f
  | 3 => 0xffe0fffe007fe3ff8007ff8ffe00ff8307cf1c
  | 4 => 0xffffff8003fffff8000fffff0003f80fe0
  | 5 => 0xffff0000000003fffffffff000000003fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xa402088850102002900980920252212808d131
  | 2 => 0x884110480a400502882082420844a50622486
  | 3 => 0x144aa290354906a58444d50b540a950b054b18
  | 4 => 0x5954c425240d4b394d50440d992c0613b00ec0
  | 5 => 0x61988739c67193ce7667664110301863dfb000
  | _ => 0
def s1Atlas : Atlas := ⟨7,rawDecor 61 s1Pos s1Neg, 0xfafafaa0faaaf0a0fafafaa0faaaf0a0fafafaa0faaaf0a0fafafaa0faaaf0a0fafafaa0faaaf0a0fafafaa0faaaf0a0fafafaa0faaaf0a0fafafaa0faaaf0a0, s1N, s1R, (fun _ _ => 0), s1I, []⟩
end PEqualNP.Outside.L_meta_36366
namespace PEqualNP.Outside.L_meta_36366
open PEqualNP.Outside.L_meta_36366.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0xc00400000000c024b000006592000081002200015002300000146ed32ff42fe42fc21ff32ff20be40fe32fe10fe40ee32fc41ff40fd10fc10fc20ff30fe21fc42fd30fc40bd43fd21bc40fc43fd31fd41fd32fe20fd43fd20fc32fc31fe31ff43fe30bf43ff31fe43ff10fc30ff41fe41ff21fd40fd42
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xd461800318301810b282801240000000000a3215980281440306051802444485021008a0a183800b6e520c2d8a4886b50e329f286873c5050e7ea890d754c21ae29a213e54cc2bca610dbd49419f2a6215e53c82f4a010cf54e40bca80433f544827aa9885b54843dc20061785050e7ca818db54e329faa2613d54c835a65205ed4143b7296619f5350f9a86996350d32e699263ce434ca78a9185b54b309f2a0873d5490e78a8904f950309f284813d540c2eaa2185e94031b6a9663cd328c2bca6216e94040d7194813d54cc2dea4885b94a439c282873e54cc6daa521db94843e6990613c544867aa8195b948329f2a641b840cc27ea8884fd5230dc282877a509075a86995b548319eaa0633d5310376a0a1cf95032b7290639d434cb5a64205e54241d7a1a656d520c2f2a018cf953329e2a2213d54086baa7906e102109f2a0433c544c37080885754c42b729663cd32cc67ca0206750f32bb288615f534435c642073d4d329eaa663af438cad8a4a0cf55332
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x600000010062004002340000002000000134532544308e594400c3185310110a6181434ca386055331c354d321024d6314941c3d51328c3893210030a618143ccac86050d32e2181434ca8c6050d32cc544400c30d544cb31e2d81434ca886050d32aa181438cb0d544c830aa181434ca8d6490d32
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x70132544400c304b2a6420061421c1544cb31
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 99
  | 3 => 21
  | 2 => 3
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (i*5) 5
  | 5 => packedAt s2K5 (i*16) 16
  | 4 => packedAt s2K4 (i*27) 27
  | 3 => packedAt s2K3 (i*38) 38
  | 2 => packedAt s2K2 (i*49) 49
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/36+packedAt s2K5 (736+(h % 36)*6) 6) % 46)
  | 4 => 2*((h/47+packedAt s2K4 (2673+(h % 47)*7) 7) % 99)
  | 3 => 2*((h/28+packedAt s2K3 (798+(h % 28)*5) 5) % 21)
  | 2 => 2*((h/8+packedAt s2K2 (147+(h % 8)*2) 2) % 3)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x3fff03ff87fc21ff0ff87fe1fc1ff0133f73c
  | 1 => 0xfc1fffc1ff87ffe0ff0ff87fe1fe07fecc79cf
  | 3 => 0xffe1fffe0007ffff000fff8ffe0007ff0f8e0f
  | 4 => 0x1fffffff803fffff0000ffffff803f00ff0
  | 5 => 0xfffe0000000003fffffffff000000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x5844118c50810405301380960244b11811b31c
  | 1 => 0x9402284800a00405104882220941248445145
  | 3 => 0x308d45103554a2ab0889550d540864b30a8e0a
  | 4 => 0xa29188212440ab328aa0440999294023a00ca0
  | 5 => 0xc3190e39c66733dcecce6641103180c3ff6000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeeeee88eeeecc00eeeeee88eeeecc00eeeeee88eeeecc00eeeeee88eeeecc00eeeeee88eeeecc00eeeeee88eeeecc00eeeeee88eeeecc00eeeeee88eeeecc00, s2N, s2R, (fun _ _ => 0), s2I, []⟩
end PEqualNP.Outside.L_meta_36366
namespace PEqualNP.Outside.L_meta_36366
open PEqualNP.Outside.L_meta_36366.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x14000801491c01c0240080000055000780444141fe41fe10fc21fd41fc20fe30ff10fc30ff21fc31fe20fe40fc32fd43fe43ff43fc43ff31fe42fd31fd40ff32ff41fc41fe32ff42fd30fd21fe31fc10ff30fd20fd32ff40ff20fd10fc42fd42fe21fc40
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x41f631442fca6087dd0541be2a0217e52043dc40905f14532be290217c54c437c87206f90a41fa20e637f53087f220085f94830bf2a4217e518c2fca3105f54f20bfaa0436d520c2faa2195f54643dfa1a817c525067ca8185f15230bf294816d52c42fca990fbd0a20bf288837f530837e8621fd50621be2a2617e5310afca520df54730beaa4833e540877a8621df54810be292217c548cafea9885f14542bea96817f53482f8a818774c030bfaa0637e53482faa7186f90d42f7a12857f504867aa9087b48620beaa2217e53102fea0a15f94a42beaa2417e53442fca190df95121bf2a2637e5110efaa0216fd0f41bea86657c54482fca8985f15231bfa8a877f52442fea0995f94841bfaa0417d50106f8a8197d44010be29e21ee32c82faa7085d54640bea80657f5250efaa990ef50f41f6a1243f431042fca020df54242fba08636e520c2fea5886f55021bfaa643ee42c86f8a710cfd5120bf298437d50d0af8a690df54f40bea8c61be42106faa7196fd5120be2a663f431486fea0a0df54a40f6212657e544cafea6a15f95110beaa6637e5210fec8220fdc8521df218817e52d02fca6105f54620bf28c837f544c2fca7905f14d10bf29041bd54ccbe86310df54f21df21c83be54ccbec63885f94f21f6996417f52042fea7887d48510bf29a437e54103da4210df94730be2a6417f54842fea8197b88521ef996617c544437e85a0dfd5331ef994657d53042faa898fe8c210be28287bf42503f2a018fb10820bf286637e52102fca2205f95310faa0883de53082f8a2985d54442de21e857d528c6fca9995fd4520bf2a0217d548ca7ea898df14f21fd280637e50086fea2987bcca329e2a2437d5290efaa8085f55230bfa9a813d54ccbf240104fd5121be2a263bf435067aa8105f54f42f6a90837c5250f7a86a0ef95232dfa1885be40502fca5887d14530bb28c81bd54082f8a090fb54a43faa8c81df308c2faa9995f54440af298417c52503de40107b94831fb880217e51083ea6218db94841fa98a21f5518cb7a862177cc832deaa4217d508ca7ca9087dd0510bea9081f7514c2fca6196f90c41fb28c65ee32c86fca7215f54742beaa061f610442fea9185f14b10de2a243f6510c278a8986f55232f729621bf4210af8a49877cc631be282657e5210be863087bcc932bfa9a21fb304c37a87a07e4c110dfa1e817f54c82fca7a0df54e41f790441bf419077887207dc8621bf28443be54086faa198df55130dea12817f544cafca0187d48710f7990417e548837ea890fd88510bea9a437d54cc2fca9906fd0640f6214416c5250278a8905fd4f20de21a85ef4290bee6318fe88020de2a2417e540c6fca410db94b10bb288617c54842fea790fec4210beaa2437d508c6eaa2105f94e10bf294637d51842fca418cf95232
  | 1 => 0xe5410efaa7217d88710bf286877e548c2faa021fdc4210bf29e857e51d0afaa5185e54031ee990657d5110bde42107dcc4109faa261bc42907e88218ef95310beaa4637e52d077ca9085f55032dfa08813d548ca7ca9997e4c030beaa6217d50886dea4987b90921fa20a217d50c86faa5087dd4543f6292817d52d06fca021df54341bf29663bd540c2f8a9985fd4931bfaa021745150efca3995f94431bf296877f548c6fca720fbcca20bf29465bc41502fca3205d94632dea0c813c544c77a84a0df54743bfa82877d54902f8a5087b8c832beaa2657e53d037885207dcc521bf2a0413e54c42fca2085f15132bf284617d52883ee8398fd54430f7294877d50d0fde43106f50842bea8487f55110afca620df54443bea98857d54886fca1a15f14c21de218837c53043be6218df14d40bfa9c217d53d06f8a818df14931df21a877f54ccbde85195f14131be2a4413d540c2f8a6a0df54e40bf288617e540c2fca521fb4c832dea0881f731842fca4886fd0441bea98417f504c7f480205d54430bea9c41bf409037e85215f55031be29e41bf4390f78a8985f14e10bf2a6617e50842faa2107e8c110bfaa0617c51502fca1105f95042bf296617f54442faa9216f50b40f6a90637f52843da8590df54b43bf28085dd310c6fea2a07e50040bf2a043f7314c7be64987b4c920f719243be41506faa598ef10840bea9083fb20482baa6105f54642eea98417d54843dca420df54f10fa20e21775150efaa421fb54830bfa9a837e500cafaa710dfd5330df2a061ef424cbbc60987d90521ef21887f521086faa510df953319f2a0637f52502faa6885b94a43bfa9c417e50907f661185fd4941deaa0637e51886faa2187b0c820fd180617e530c6faa4885f14520df20e81bf4010378a898df94743bf294617d518cafea8904f55021bea84837d53103de4310fdcc621bf29c41ec524c2faa018df54b30f6992437e5390fd885197b48020beaa6417e50082fca2217d88421f7908437d52906faa9105fd4d21deaa621be429037c84a17d50521bea90637c54082f8a2a1fe4c210bf28e81ef42082daa420df94e40bf28487f741907bc6298ef10841dea08833d540c6fca0207b94830b6a90637c5350bec6218df54830f721085bd43502fea9195f14141bea80436f525037c87a15f95221df210817f54886f8a910df94232be29a417d52c42faa718dfd4532bf2a0653d54c42fca8905f15121fd90441bf544c2fca018df95041fd8822174514c3da42105fd51319f2a0417f54883f680a05fd5121bf28c6577514c3dea4985f94010be29c41f65110afca1215f95232f6a96217e51c83d865105f54c41fda0481ef52502fea2a15f54c21bf29c437d54082fca120774c930bea8e657e5190eeca2107d94420de20e817e51086faa3907d90621df2a
  | 2 => 0x1040011092024041e002020071580021c020185b2dc83004000282e1241e0a4020243e00c33040000100205c0304853038111a806028030800e0002304024040030002609009098090001e26809010040140600000000010005d008000740015c3b2c80039c0a0086c0d408128000040524c3b0000007401030190007b0403a00c2d0b0010042d00015040028e00f01048000130d0340003b04005000043800e00c050400138c09000010002308047034040c4da00c02264012940215c0800404020010043d00000014380042105c0900000004004f80004c250004e14c05010000dc0902c920040600c160a00501018000080080a02c0106c0001c231dc28008000100f010030080102402020002541903839710000000000c360042a004242400f1440005015000280109b00000000000ac0c05429014151f80b068030340bbea8c81bf42d02fca118df94631f6a10856d5290efca5087d54420dea16837c54ccbbe8721fb4cb21bf286837f524c2faa921fd14543b6292616e520c6fea710df54d20be2a043bf42507eca3205f94832dea00817a500c77e87215f95231bfa9821dd4310efca2195f94c43be2a643df300c2fca1995f54740efa1a877d54086fca3215f94c30f7192417c530837ca818dd54632df20a81f531c437a8721774cb30dfaa263bc43103bc64996f10e41bb288857e53c43ee83885f14142fd080217
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x541102796014c218f590530866d65cc8208f993538423d6414e109b98b540c6e56210710d95865290e3c6454e21d354d200823c64547208f992500426e62d53109bd8954442756115232cb952520c32d5494b108f992518832e54548318f99253c867a6014c10cb95252c425d63148108fd91510ca3d65908409b988540423e64d4a10cb54b41106766115320cb152424872d54d08209b588548c66f65508428f19151cc25d63150209d987548ca6f65480208f596431066d6214d10b958841cc63f6454e218f990538823f6550c429b58b540c66d6295130c7551530833454cc521d314d324863c6454d109d98652cc25e63148108f993530827661d50108f596421072e54548308f59353c826e6294f41cb552520c32e5494831ad584421066e6214c209b588538427561141329d5865290e77654c4319d19541487666194b109d584540823e6515131b9584424cb2c52509409b5885150f2d5454830cb15232483704154031ab58841d023f6550040ad19131c435553544209b58853c423f6550c43d994921c42b46150f40d314b324c27661943429bd8950d066c654c9209758f54c8771315403197d8d544426c6255130ab98a4350b2c548c9219d98753c82746154e20cd953108427761551329bd89548c33654544208f59253c831d5494c209d58753c833651d0640d958a519023d65950209b189544423e6414d109d18553d0a3d64d4e108f99052442776550441cb55121086b464485108f191534836952940318f59052c437160145309b189534436652544309e181544ca3f64547209b58a518c23f64540329b98a518c2b56110a419d984540827b6054d219798c540832c52105408f994544876661149408fd91520425f654c030d9945210835653544209b588530427a6014c219b997424ca6e6214e108f99053082ae64cc8209d58453882746548510cd55121c43a54250521ab98a431072f54149308f99353c8734540c521ce952500c67561d50208f191520427665d05109b98a519036752d4530d99885150e776154d10cd90e519025e6315010b9988314863e6494f20bc580318423d6494d219d185544c26f6255120d9549510c26e62150319d584540cb355494430cd55221c433454cc5318f191500cb3654944308f59052842756114c20ad1854310f6a5294031d354f420826c62543419dd85534832c6255232d354f320826d62d50308f99743506e562105109798f54c866d65108208fd9150cc73654cc6108fd954210b346155310dc8c5500c63f6454d218f992534872d54d0a32ad18543502e56210431e990a414873554946329d987540c3356115121cd153514c27b65440109d59431042766114c10cd55121087374254442cb14a415023f6454e209b98b54cc23d64946309e181534872c43548418f99352c426e6214543
  | 1 => 0x823e6494b319d987530826d62944108f593530825e6314c20cd50d5110a6e6215310ad18543506ae6290f429d586544c27b65500408f596540c2756115320cb151324827965840109ed81544ca3e65d0d408f593530867960150328f990530872d54c8420cdd53514c34d53c80208f191510cae56110a328f994544833654546328f59353c87346155031cb151324863e64d4f10d95095110a6f6254043d9148514c2756194342cb549411066d62d4f108fd91534432d5494831bc580310432d54548319d98650d0e3d64d4f109dd9510042766194a439bd89534826d62d5330cd951510c2b661901409d584540c371514c0309d986544c23e64141329718d544426d6294f418f990528423e64951308f990520423d6414c20ce552500c66d62d5310b9986324873754145309e983548866d62946409b98853c423d6590c408f59053c426e6214d108f992544827561d50309e980540c6746154d20da549500c676658c510d9986520c65d6314a109d587548c2746155330d958452502756510431d3549300c32c54d4930ab189401025e63d5020cd551510c27661d50209d195314427661150329dd85544c72d43149408f992544866e62944108f992508c63e65d09408f59250886766115021d354d210833642946409d58652cc26e62150309b58854042ae6290c40d998a519026c654c921ab98a4350e6d62d5331bc185308434c6254c208f59252cc73a54540319e583548873554544208f59253c86ae64cca208f191524426e658c920ab592324866d6215310ad59031886b56110a408fd91528c67a6014e219b988540876a5254031cd55341c433442946409758f540823f6454a309b988548c63d64148109ed95200823c64543218f590504cb555394420cb14a405023d6494b309b195424874d530c8208f191534866f6548421ab993328cb2f54d4930ab59232c863e6415031d994a510c27561149408f593528427661d52208f992518c2b5640c5219d984538834d53108208f59251042776154f428f592518826d650c8209d587530823d6414e20cd952510823e6414f1097d8d524423f6454d20cb55152c426e62d50309dd8553102e561108208f992510432e5454b108f990540867461551329d587548826e6214c21ad19121c423e64d4c219b588540c2766114132cb18954082f1600c521d954a510c23c6454c108f590538873651506409718d52442ac6448620cb90d521066c62552309b98a544c3364314543d354f210825f654c8329d984520426e6214c108f994544c27a60d50318fd9150c863d6414c10d594e510823e6494b30ad18543d06776548421cb152204823f64547309b98b54cc63e64951319d984540c23d65950218f590534432c5414930ab98a43903354254442bc580318863d6494010bc181214432d62151218fd9
  | 2 => 0x720080000004014000d4090102d0000300c03038010004320418008041a039020060081f02802164001b0050940200000020000540b00406018000000305801000010e80b0341701c02008040143f014020080202402000200000100c0301400008540341901419008010001d038000040a0041a0000825c0009004010000101c0100001c1f0003a04402000030400c0d40c000010040200c0d00c3b01c240101d1200a00810390010102a0080001c01020380015e0000b000070280d0000301c02010000340e0000c0200a000001b41909c00008181883a000150280e0044f03d830000903014000010000e05c000003b01c570000e0280063c260000001016000010142000c000001a000000040005003000030280000005000060000200401004012a00210000010000000e002ae64cc9329b98b540cab46150e428f992534823e65d0941ce551500c66e6294f408f992530ca766115232cd150514c25d63150109dd8554cc2ac64480208f59253482746154c40c7951530833554884218f99250886796015031cdd0d5110b675214530ad191310c63e64d4f20ab98a439063f6550441cb553210867661d4c21cd553410c6796014e218f990530426f654c832ab19121083666194a43cb551210823c6454a30d9549411066c6254331ab588415023e65105409b1895010e3d64d4b10cd551518cab4644c5109bd8950cc6776154e208f990514cae56110a2097596530826e62d4f108f191528c67661149409d984530826f6254d109d987548c23d6595031ad992104437341540319d597310427561d52328f19150cc66d6215031cbd0c52502b46150c42cd952518ca3f6454c108f9905384336540c610cb54a421063d6494c32cd947409031e5494c2097d95310c73443946408f9944350a3d64942319ed95300c32c52d0940d354b300c23e64150209b58a53d03345490521d99095110b355494420d954a411067761551308f592520ca3d64145329e195304423e64150308f590524436452d4530d95885150f2d52108418f99052c425f6550c439e980540ca7960d50318f990538872f4394a439798c528427665cc521ad584421023e6494832dc546300c26f62551309d58650d0e3f64549108f191538
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x1720000018000000040000002462004800003831915348420c48a530c80a056172105500c6163b2a890841495c86155310a4ae2312a91943576150314869238a8629281295c86150d41a4ce5218a2a1e3054580314861a3b2a890e21295c66290d42a60e898aa018e0c6454d2008216bb0a919243499ca4394640c4ac4b08a890d25711895408292b88a4a1281495ca5150640c64a8b006308645535844208292b90c2aa0638399153cc820
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0xc20825869ca4314543825861c54314940825869ca43946408258714a6190140
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 664
  | 4 => 539
  | 3 => 25
  | 2 => 4
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
  | 6 => 2*((h/27+packedAt s3K6 (640+(h % 27)*6) 6) % 40)
  | 5 => 2*((h/256+packedAt s3K5 (17928+(h % 256)*10) 10) % 664)
  | 4 => 2*((h/242+packedAt s3K4 (20482+(h % 242)*10) 10) % 539)
  | 3 => 2*((h/29+packedAt s3K3 (1225+(h % 29)*5) 5) % 25)
  | 2 => 2*((h/8+packedAt s3K2 (240+(h % 8)*2) 2) % 4)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xfffff83ffc3ffe0f0f0ffffe1f81fffc0ff33f
  | 1 => 0x3c0fffc0ffc7c3f00ff1f0ffe3fe0f02327dcc
  | 2 => 0x3ff0ffff0007fffff001ff0ffc000fffc38e0f
  | 4 => 0xc000fffffff803fffffe000ffffff003fc0ff0
  | 5 => 0xffff0000000003fffffffff000000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x8420088a20410002030251120484a14804b115
  | 1 => 0x896291864a0a26508590b8a7212c2a1a12554c
  | 2 => 0x10c6a2141a94a2b590812a8d48184cb2c30e0a
  | 4 => 0x2884420900089292824000892514021680aa0
  | 5 => 0x230c8738e32733cecec9ccc1006188c3bfe000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xfefea8a8eeeea0a0fefea8a8eeeea0a0fefea8a8eeeea0a0fefea8a8eeeea0a0fefea8a8eeeea0a0fefea8a8eeeea0a0fefea8a8eeeea0a0fefea8a8eeeea0a0, s3N, s3R, (fun _ _ => 0), s3I, []⟩
end PEqualNP.Outside.L_meta_36366
namespace PEqualNP.Outside.L_meta_36366
open PEqualNP.Outside.L_meta_36366.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x3c03c0004002541006003062156508183ff30bf42be40fc21ff20fe42fe31fe43fe30fd31fd21f621ff31fc43fe32fc31fc42ff32ff42fc40fd32bc40ff41fc10ff40fd41f521fe40fd20fc30fe10fe41fc20fd10fd43fd30fd42ff21fe21fe20ff43fc32fc41ff10bd42fd40
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x18180200000680000c0000c180cb06b150800000802604200003c0170206a800000100140000206081000c000000001d39000c2001200033008c0800400100017a500cad8a4986b50b21bb288433d540867ca0204f95042daa1443e632486e8a2a1cf943429c2828576510ca7aa9195bd4930db10c81e642486eaa2195b94b109faa241765190a7aa8194f152209f2a063785050a7ca990cf55321bba8a877651083ca8490cf95320bb28885a542486eaa3905d54642dc206417a500c6eaa3195d54420bca8487e521082f4a121dd544429f2a041b5211027aa9985dd4530bb28c653d54082f2a0195754c20d6a12436e521067aa818cfd51109ea9481b8408c278a8905b548319eaa6213e540cb6e8490ebd4942b7290633e54c42eaa510f94c9219faa2616d52c427ca810ded41429ea90813e509027ea898eed4142db10881b542486daa420edd0a21dc202613c544c27aa9904f15131da90c8179500c7ca43104fd5220f3a92433d5490a78a8886e94040ba28a61b84008278a0a15794c209f2a465b85050a7ca9985d94720
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x68000000e7080c0000000380a000000000100007003a36050921e848440083455348420c654c40082396510020c954921103255448420e818142487275448620aa181424866562145438e181548caa86050b21a959242486b06050921b818142486a06050921ac18142886a46050921ca148404c2a5648c921
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x4000000701534844008310b2a4220041281c1648c921
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
  | 6 => 2*((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/22+packedAt s4K5 (736+(h % 22)*6) 6) % 46)
  | 4 => 2*((h/75+packedAt s4K4 (2673+(h % 75)*7) 7) % 99)
  | 3 => 2*((h/35+packedAt s4K3 (798+(h % 35)*5) 5) % 21)
  | 2 => 2*((h/15+packedAt s4K2 (147+(h % 15)*2) 2) % 3)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfffff03f0f87fe1e1f0ffffe1c1c0ffc1ff4cf
  | 1 => 0xf03fffc00fffc3e01ff1f0ffe01fff026278fc
  | 2 => 0xffc1fffff007ffffe001ff0fffe00fff838f0f
  | 3 => 0x1fffffff803fffffe000ffffff003fc0ff0
  | 5 => 0xfffe0000000003fffffffff000000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x1288118a120980060702511a0484a1680cb4c5
  | 1 => 0x25852286a54226610990b8a720496a1a22585c
  | 2 => 0x41154414815422a920812a8549404c9283090a
  | 3 => 0xa2889200800891252240008929280215406a0
  | 5 => 0x8c310e38ce6733dd9cc9ccc1030308c3fbe000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xfea8fea8fca0fca0fea8fea8fca0fca0fea8fea8fca0fca0fea8fea8fca0fca0fea8fea8fca0fca0fea8fea8fca0fca0fea8fea8fca0fca0fea8fea8fca0fca0, s4N, s4R, (fun _ _ => 0), s4I, []⟩
end PEqualNP.Outside.L_meta_36366
namespace PEqualNP.Outside.L_meta_36366
open PEqualNP.Outside.L_meta_36366.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x3031000400404c000b1ce09e0040801c0543200fc42fe10fc41fc20fd31fd32ff30ff21ff10fc40fc32ff31fe20fc43fc31fc21fe30ff42fd30fe31fc30fd43fe43ff43fe42ff32fd40fe21fd42ff40ff20ff41fd21fe40fe32fe41fc10fd10fd41fd20
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x4001314124108400d2c00017487400031c204044040e146001ba28a877551102bca6205e54243af298837651082dca5885e94032b6a968775510caf4a018dd546429f2a6613d540c6baa7a14f953219eaa0416e52d0ebca6105754c40b6a90637a50886daa420de54031af29c216e52106daa4205e54032af29e855d53842f2a020dd946309e2a2216f524c2eea2a1dd946429f2a0635f53486baa620db54b10bda828575510827aa990de542219eaa661785050ad8a4984f95020ae29a433e540cadca418d754c20baa8c6176510ca7ea8885d944409eaa0657a50106f4a121db94840
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 40
  | 4 => 60
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (i*5) 5
  | 5 => packedAt s5K5 (i*16) 16
  | 4 => packedAt s5K4 (i*27) 27
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt s5K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/27+packedAt s5K5 (640+(h % 27)*6) 6) % 40)
  | 4 => 2*((h/34+packedAt s5K4 (1620+(h % 34)*6) 6) % 60)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x3f8ffc7f07c71f8e38fc7e0ff1c1c1fe3334cf
  | 1 => 0xc7f07f8ff807fc703f1f8ff07e01ffc04dc8fc
  | 2 => 0x7ff800ffff81fffc01ff0007ffe01ff8e0f0f
  | 3 => 0xf800000fffffe07fffe000007ffffe01f00ff0
  | 4 => 0xfffffff00000007fffffffff80000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x90a510813088280218241223504854541114c5
  | 1 => 0x9123081211920090090c846132048c8c05485c
  | 2 => 0x2202292443025034401920c4249409288e090a
  | 3 => 0x4c5248a404094ab240010a492930117006a0
  | 4 => 0x24486000c624926d2492498c00302021eaa000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfeeefca0feeefca0feeefca0feeefca0feeefca0feeefca0feeefca0feeefca0feeefca0feeefca0feeefca0feeefca0feeefca0feeefca0feeefca0feeefca0, s5N, s5R, (fun _ _ => 0), s5I, []⟩
end PEqualNP.Outside.L_meta_36366
namespace PEqualNP.Outside.L_meta_36366
open PEqualNP.Outside.L_meta_36366.Model
def q6K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def q6K4 : Nat → Nat
  | 0 => 0x350de439d43bf43dd43ef21f621f521e521ed21bd43
  | _ => 0
def q6K3 : Nat → Nat
  | 0 => 0x2200a600000000001a7434872a8710f190d21e2a1a438d43c86caa510e150d218eaa48795434874a8690e350d21
  | _ => 0
def q6K2 : Nat → Nat
  | 0 => 0x2856490d21
  | _ => 0
def q6N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 10
  | 3 => 11
  | 2 => 1
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
  | 4 => 2*((h/3+packedAt q6K4 (160+(h % 3)*4) 4) % 10)
  | 3 => 2*((h/17+packedAt q6K3 (297+(h % 17)*4) 4) % 11)
  | 2 => 2*((h/1+packedAt q6K2 (38+(h % 1)*1) 1) % 1)
  | _ => 0
def q6Pos : Nat → Bits
  | 0 => 0xff0f3cf9c71fce38ffc88f1c71c71c7fc8307f
  | 1 => 0xb7f03f7e07e3f03f11f0f1e07e781f9cd4c993
  | 2 => 0x3bffc07ff803ffc01e3f01ff807fe01f270e1c
  | 3 => 0xc3ffff800003ffffe03ffe00007fffe0380fe0
  | 4 => 0x3fffffffffc0000003fffffff8000003ff000
  | _ => 0
def q6Neg : Nat → Bits
  | 0 => 0x10408082040410000020410010404001025
  | 1 => 0x41108a1092048490221011212448490a844892
  | 2 => 0xc1228220824904124051014904524112850a18
  | 3 => 0x1e4410052492282004aaa40209249240380540
  | 4 => 0x2e88204504002924892cc892490082403aa000
  | _ => 0
def q6Atlas : Atlas := ⟨5,rawDecor 31 q6Pos q6Neg, 0xfefefea8fefefea8fefefea8fefefea8fefefea8fefefea8fefefea8fefefea8fefefea8fefefea8fefefea8fefefea8fefefea8fefefea8fefefea8fefefea8, q6N, q6R, (fun _ _ => 0), q6I, []⟩
end PEqualNP.Outside.L_meta_36366
namespace PEqualNP.Outside.L_meta_36366
open PEqualNP.Outside.L_meta_36366.Model
def q7K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q7K3 : Nat → Nat
  | 0 => 0x50000a3d105d32be65d887a90f920
  | _ => 0
def q7K2 : Nat → Nat
  | 0 => 0x324c920c532487848520
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
  | 3 => 2*((h/9+packedAt q7K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q7K2 (78+(h % 8)*2) 2) % 3)
  | _ => 0
def q7Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffbe967377446b
  | 3 => 0xffffffffffffffffffffffffffdf1b9c7b8593
  | 4 => 0xffe3ef83fa1c
  | 5 => 0xeffc0ffc03e0
  | _ => 0
def q7Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffff422881110829
  | 3 => 0x244424221092
  | 4 => 0x0
  | 5 => 0x18015a402340
  | _ => 0
def q7Atlas : Atlas := ⟨4,rawDecor 58 q7Pos q7Neg, 0xffffffccffffcc00ffffffccffffcc00ffffffccffffcc00ffffffccffffcc00ffffffccffffcc00ffffffccffffcc00ffffffccffffcc00ffffffccffffcc00, q7N, q7R, (fun _ _ => 0), q7I, []⟩
end PEqualNP.Outside.L_meta_36366
namespace PEqualNP.Outside.L_meta_36366
open PEqualNP.Outside.L_meta_36366.Model
def q8K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q8K3 : Nat → Nat
  | 0 => 0x6023d085f31da43e442e98ef21
  | _ => 0
def q8K2 : Nat → Nat
  | 0 => 0x344c510c531487848510
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
  | 3 => 2*((h/9+packedAt q8K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/1+packedAt q8K2 (78+(h % 1)*2) 2) % 3)
  | _ => 0
def q8Pos : Nat → Bits
  | 1 => 0xbea673b7606e
  | 2 => 0xffffffffffffffffffffffffffff3bbc3bbc93
  | 3 => 0xdfc3cfc3c31c
  | 5 => 0xeffc0ffc03e0
  | _ => 0
def q8Neg : Nat → Bits
  | 1 => 0x424880910426
  | 2 => 0x0
  | 3 => 0x241415020918
  | 5 => 0x18016a2012c0
  | _ => 0
def q8Atlas : Atlas := ⟨4,rawDecor 46 q8Pos q8Neg, 0xfffcfffcfcf0fcf0fffcfffcfcf0fcf0fffcfffcfcf0fcf0fffcfffcfcf0fcf0fffcfffcfcf0fcf0fffcfffcfcf0fcf0fffcfffcfcf0fcf0fffcfffcfcf0fcf0, q8N, q8R, (fun _ _ => 0), q8I, []⟩
end PEqualNP.Outside.L_meta_36366
namespace PEqualNP.Outside.L_meta_36366
open PEqualNP.Outside.L_meta_36366.Model
def q9K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q9N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q9R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q9K3 (i*4) 4
  | _ => 0
def q9I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q9K3 (4+(h % 1)*1) 1) % 1)
  | _ => 0
def q9Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffbfcffcf8fff873f3
  | 2 => 0xdbf19f3f1c3f8d9c
  | 3 => 0xffffffffffffffffffffffeffe1fffe03ffe1f
  | 4 => 0xf3ffe03fffc00fe0
  | _ => 0
def q9Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffff40640108248920b1
  | 2 => 0x24ac285909932594
  | 3 => 0x1101502242244a0a
  | 4 => 0xe091ab493064f40
  | _ => 0
def q9Atlas : Atlas := ⟨3,rawDecor 30 q9Pos q9Neg, 0xfcccfc00fcccfc00fcccfc00fcccfc00fcccfc00fcccfc00fcccfc00fcccfc00fcccfc00fcccfc00fcccfc00fcccfc00fcccfc00fcccfc00fcccfc00fcccfc00, q9N, q9R, (fun _ _ => 0), q9I, []⟩
end PEqualNP.Outside.L_meta_36366
namespace PEqualNP.Outside.L_meta_36366
open PEqualNP.Outside.L_meta_36366.Model
def q10K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q10K3 : Nat → Nat
  | 0 => 0x8400002f18de32b8637cc2e985c32
  | _ => 0
def q10K2 : Nat → Nat
  | 0 => 0x20294414c2390a318c424c2590632
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
  | 2 => 0xffffffffffffffffffffffedfc7f3fe3f0fe73
  | 4 => 0x76ff8fcffc7f0f9c
  | 5 => 0x78fff00fff800fe0
  | _ => 0
def q10Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa0180202049440a5
  | 2 => 0x122324452122a652
  | 4 => 0x9416819484a2b18
  | 5 => 0x78a4eae920ccde0
  | _ => 0
def q10Atlas : Atlas := ⟨4,rawDecor 53 q10Pos q10Neg, 0xfafaa0a0aaaaa0a0fafaa0a0aaaaa0a0fafaa0a0aaaaa0a0fafaa0a0aaaaa0a0fafaa0a0aaaaa0a0fafaa0a0aaaaa0a0fafaa0a0aaaaa0a0fafaa0a0aaaaa0a0, q10N, q10R, (fun _ _ => 0), q10I, []⟩
end PEqualNP.Outside.L_meta_36366
namespace PEqualNP.Outside.L_meta_36366
open PEqualNP.Outside.L_meta_36366.Model
def q11K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q11K3 : Nat → Nat
  | 0 => 0x4202022e98de30b8617cc6e195e32
  | _ => 0
def q11K2 : Nat → Nat
  | 0 => 0x100498404c6390a309a408ca310931
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
  | 0 => 0xffffffffffffffffffffffddf1ff3f1ff0f3f3
  | 2 => 0xffffffffffffffffffffffeffe7fffe3fffc7f
  | 3 => 0x76ff8fcffc7f0f9c
  | 5 => 0x78fff00fff800fe0
  | _ => 0
def q11Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa21c2243049261b1
  | 2 => 0x1021040421248446
  | 3 => 0x9446819484a2a98
  | 5 => 0x7894eae920ccf60
  | _ => 0
def q11Atlas : Atlas := ⟨4,rawDecor 45 q11Pos q11Neg, 0xfaa0faa0f0a0f0a0faa0faa0f0a0f0a0faa0faa0f0a0f0a0faa0faa0f0a0f0a0faa0faa0f0a0f0a0faa0faa0f0a0f0a0faa0faa0f0a0f0a0faa0faa0f0a0f0a0, q11N, q11R, (fun _ _ => 0), q11I, []⟩
end PEqualNP.Outside.L_meta_36366
namespace PEqualNP.Outside.L_meta_36366
open PEqualNP.Outside.L_meta_36366.Model
def q12K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q12N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q12R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q12K3 (i*4) 4
  | _ => 0
def q12I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q12K3 (4+(h % 1)*1) 1) % 1)
  | _ => 0
def q12Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffbfcffcf8fff873f3
  | 2 => 0xffffffffffffffffffffffdff39fff1c3ffc9f
  | 3 => 0xebfc1f3fe03f8f1c
  | 4 => 0xf3ffe03fffc00fe0
  | _ => 0
def q12Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff4061010824892131
  | 2 => 0x2088281109124486
  | 3 => 0x1523506a42a52b18
  | 4 => 0xe0a1ab493064ec0
  | _ => 0
def q12Atlas : Atlas := ⟨3,rawDecor 29 q12Pos q12Neg, 0xfaaaf0a0faaaf0a0faaaf0a0faaaf0a0faaaf0a0faaaf0a0faaaf0a0faaaf0a0faaaf0a0faaaf0a0faaaf0a0faaaf0a0faaaf0a0faaaf0a0faaaf0a0faaaf0a0, q12N, q12R, (fun _ _ => 0), q12I, []⟩
end PEqualNP.Outside.L_meta_36366
namespace PEqualNP.Outside.L_meta_36366
open PEqualNP.Outside.L_meta_36366.Model
def q13K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q13K3 : Nat → Nat
  | 0 => 0x23005f329a65b4cb7195d32
  | _ => 0
def q13K2 : Nat → Nat
  | 0 => 0x2350e32
  | _ => 0
def q13N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
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
  | 3 => 2*((h/8+packedAt q13K3 (75+(h % 8)*3) 3) % 5)
  | 2 => 2*((h/1+packedAt q13K2 (26+(h % 1)*1) 1) % 1)
  | _ => 0
def q13Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffbfdcf3e3f3e74cf
  | 2 => 0xfffffffffffffffffffffffdfef3cfc7cf9b33
  | 3 => 0xebf03f3f80fec3c
  | 4 => 0xf3ffc03fff00fc0
  | _ => 0
def q13Neg : Nat → Bits
  | 0 => 0xfffffffffffffffffffffff404104009020045
  | 2 => 0x208041042040112
  | 3 => 0x150aa0690a94c28
  | 4 => 0xe082ab24a14e80
  | _ => 0
def q13Atlas : Atlas := ⟨4,rawDecor 29 q13Pos q13Neg, 0xfafafaa0fafafaa0fafafaa0fafafaa0fafafaa0fafafaa0fafafaa0fafafaa0fafafaa0fafafaa0fafafaa0fafafaa0fafafaa0fafafaa0fafafaa0fafafaa0, q13N, q13R, (fun _ _ => 0), q13I, []⟩
end PEqualNP.Outside.L_meta_36366
namespace PEqualNP.Outside.L_meta_36366
open PEqualNP.Outside.L_meta_36366.Model
def q14K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q14K3 : Nat → Nat
  | 0 => 0x110000ee995c30bc6170c6f995e31
  | _ => 0
def q14K2 : Nat → Nat
  | 0 => 0x12009a408c651053298404ca590630
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
  | 3 => 2*((h/9+packedAt q14K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q14K2 (104+(h % 8)*2) 2) % 4)
  | _ => 0
def q14Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffddf1ff3f1ff0f3f3
  | 1 => 0x6efe3fcfe3ff0cfc
  | 4 => 0xfffffffffffffffffffffff7ffcffffc7fff1f
  | 5 => 0x78fff00fff800fe0
  | _ => 0
def q14Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa21c824304926171
  | 1 => 0x11258415212624b4
  | 4 => 0x840280848488a0a
  | 5 => 0x7892eae920ccfc0
  | _ => 0
def q14Atlas : Atlas := ⟨4,rawDecor 51 q14Pos q14Neg, 0xeeee8888eeee0000eeee8888eeee0000eeee8888eeee0000eeee8888eeee0000eeee8888eeee0000eeee8888eeee0000eeee8888eeee0000eeee8888eeee0000, q14N, q14R, (fun _ _ => 0), q14I, []⟩
end PEqualNP.Outside.L_meta_36366
namespace PEqualNP.Outside.L_meta_36366
open PEqualNP.Outside.L_meta_36366.Model
def q15K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q15K3 : Nat → Nat
  | 0 => 0x400001000007830b06178c2e187b30
  | _ => 0
def q15K2 : Nat → Nat
  | 0 => 0x2690230
  | _ => 0
def q15N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
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
  | 3 => 2*((h/15+packedAt q15K3 (75+(h % 15)*3) 3) % 5)
  | 2 => 2*((h/1+packedAt q15K2 (26+(h % 1)*1) 1) % 1)
  | _ => 0
def q15Pos : Nat → Bits
  | 0 => 0xbbc3ff3e3fe03fc
  | 1 => 0xfffffffffffffffffffffffdffc7fffc7ffc7f
  | 3 => 0xfffffffffffffffffffffffefff8ffff8fff8f
  | 5 => 0xf3fff03fff00ff0
  | _ => 0
def q15Neg : Nat → Bits
  | 0 => 0x4479224e09261bc
  | 1 => 0xfffffffffffffffffffffff208b0412424a455
  | 3 => 0x111068249094a8a
  | 5 => 0xe224eb92418f60
  | _ => 0
def q15Atlas : Atlas := ⟨4,rawDecor 43 q15Pos q15Neg, 0xee88ee88cc00cc00ee88ee88cc00cc00ee88ee88cc00cc00ee88ee88cc00cc00ee88ee88cc00cc00ee88ee88cc00cc00ee88ee88cc00cc00ee88ee88cc00cc00, q15N, q15R, (fun _ _ => 0), q15I, []⟩
end PEqualNP.Outside.L_meta_36366
namespace PEqualNP.Outside.L_meta_36366
open PEqualNP.Outside.L_meta_36366.Model
def q16K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q16N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q16R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q16K3 (i*4) 4
  | _ => 0
def q16I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q16K3 (4+(h % 1)*1) 1) % 1)
  | _ => 0
def q16Pos : Nat → Bits
  | 0 => 0xb7c7cf38fc7f073c
  | 1 => 0xffffffffffffffffffffffdff9f3ff1f87f9cf
  | 3 => 0xffffffffffffffffffffffe7fe03ffe007fe0f
  | 4 => 0xfbfffc3ffff80ff0
  | _ => 0
def q16Neg : Nat → Bits
  | 0 => 0x487490582531631c
  | 1 => 0xffffffffffffffffffffff2094040909122145
  | 3 => 0x1921aa324264ce0a
  | 4 => 0x60102a492408ca0
  | _ => 0
def q16Atlas : Atlas := ⟨3,rawDecor 27 q16Pos q16Neg, 0xeeeecc00eeeecc00eeeecc00eeeecc00eeeecc00eeeecc00eeeecc00eeeecc00eeeecc00eeeecc00eeeecc00eeeecc00eeeecc00eeeecc00eeeecc00eeeecc00, q16N, q16R, (fun _ _ => 0), q16I, []⟩
end PEqualNP.Outside.L_meta_36366
namespace PEqualNP.Outside.L_meta_36366
open PEqualNP.Outside.L_meta_36366.Model
def q17K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q17K3 : Nat → Nat
  | 0 => 0x118006d32dc6574caf994d32
  | _ => 0
def q17K2 : Nat → Nat
  | 0 => 0x2350e32
  | _ => 0
def q17N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
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
  | 3 => 2*((h/8+packedAt q17K3 (75+(h % 8)*3) 3) % 5)
  | 2 => 2*((h/1+packedAt q17K2 (26+(h % 1)*1) 1) % 1)
  | _ => 0
def q17Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffbfdcf3e3f3e74cf
  | 1 => 0xfffffffffffffffffffffffdfef3cfc7cf9b33
  | 3 => 0xebf03f3f80fec3c
  | 4 => 0xf3ffc03fff00fc0
  | _ => 0
def q17Neg : Nat → Bits
  | 0 => 0xfffffffffffffffffffffff404104009020045
  | 1 => 0x208041042040112
  | 3 => 0x150aa0690a94c28
  | 4 => 0xe082ab24a14e80
  | _ => 0
def q17Atlas : Atlas := ⟨4,rawDecor 27 q17Pos q17Neg, 0xeeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88, q17N, q17R, (fun _ _ => 0), q17I, []⟩
end PEqualNP.Outside.L_meta_36366
namespace PEqualNP.Outside.L_meta_36366
open PEqualNP.Outside.L_meta_36366.Model
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
  | 0 => 0xffffffffffffffffffffffbfcfcff8fc3ff33f
  | 1 => 0xd7f1f33f1fc70dcc
  | 2 => 0xffffffffffffffffffffffe7fe03ffe007fe0f
  | 4 => 0xfbfffc3ffff80ff0
  | _ => 0
def q18Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff4064100824912115
  | 1 => 0x28ac84590992654c
  | 2 => 0x1909aa324324ce0a
  | 4 => 0x60102a492208aa0
  | _ => 0
def q18Atlas : Atlas := ⟨3,rawDecor 23 q18Pos q18Neg, 0xeeeea0a0eeeea0a0eeeea0a0eeeea0a0eeeea0a0eeeea0a0eeeea0a0eeeea0a0eeeea0a0eeeea0a0eeeea0a0eeeea0a0eeeea0a0eeeea0a0eeeea0a0eeeea0a0, q18N, q18R, (fun _ _ => 0), q18I, []⟩
end PEqualNP.Outside.L_meta_36366
namespace PEqualNP.Outside.L_meta_36366
open PEqualNP.Outside.L_meta_36366.Model
def q19K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q19K3 : Nat → Nat
  | 0 => 0x1200206d21ec439487a90ef21
  | _ => 0
def q19K2 : Nat → Nat
  | 0 => 0x2950a21
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
  | 0 => 0xfffffffffffffffffffffffbfd99fe39cff07f
  | 1 => 0xfffffffffffffffffffffffd7e1e4fc1f73993
  | 2 => 0xe7fe073fe07ce1c
  | 4 => 0xfbfff83fff80fe0
  | _ => 0
def q19Neg : Nat → Bits
  | 0 => 0xfffffffffffffffffffffff404220008410025
  | 1 => 0x289509244a2a892
  | 2 => 0x19115069424aa18
  | 4 => 0x60002921000540
  | _ => 0
def q19Atlas : Atlas := ⟨4,rawDecor 23 q19Pos q19Neg, 0xfefea8a8fefea8a8fefea8a8fefea8a8fefea8a8fefea8a8fefea8a8fefea8a8fefea8a8fefea8a8fefea8a8fefea8a8fefea8a8fefea8a8fefea8a8fefea8a8, q19N, q19R, (fun _ _ => 0), q19I, []⟩
end PEqualNP.Outside.L_meta_36366
namespace PEqualNP.Outside.L_meta_36366
open PEqualNP.Outside.L_meta_36366.Model
def q20K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q20N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q20R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q20K3 (i*4) 4
  | _ => 0
def q20I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q20K3 (4+(h % 1)*1) 1) % 1)
  | _ => 0
def q20Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffafc733f8e387f4cf
  | 1 => 0xcff83f3f03ff08fc
  | 2 => 0xfffffffffffffffffffffff7ffc3fffc07ff0f
  | 3 => 0xfbfffc3ffff80ff0
  | _ => 0
def q20Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff5072462830d1a4c5
  | 1 => 0x3096a0590932685c
  | 2 => 0x90428124824490a
  | 3 => 0x62002a4924086a0
  | _ => 0
def q20Atlas : Atlas := ⟨3,rawDecor 15 q20Pos q20Neg, 0xfca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0, q20N, q20R, (fun _ _ => 0), q20I, []⟩
end PEqualNP.Outside.L_meta_36366
namespace PEqualNP.Outside.L_meta_36366
open PEqualNP.Outside.L_meta_36366.Model
def q21K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q21K3 : Nat → Nat
  | 0 => 0x8006521ea43bc87690f621
  | _ => 0
def q21K2 : Nat → Nat
  | 0 => 0x2950a21
  | _ => 0
def q21N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
  | _ => 0
def q21R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q21K4 (i*4) 4
  | 3 => packedAt q21K3 (i*15) 15
  | 2 => packedAt q21K2 (i*26) 26
  | _ => 0
def q21I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q21K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/8+packedAt q21K3 (75+(h % 8)*3) 3) % 5)
  | 2 => 2*((h/1+packedAt q21K2 (26+(h % 1)*1) 1) % 1)
  | _ => 0
def q21Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffbfd99fe39cff07f
  | 1 => 0xfffffffffffffffffffffffd7e1e4fc1f73993
  | 2 => 0xe7fe073fe07ce1c
  | 3 => 0xfbfff83fff80fe0
  | _ => 0
def q21Neg : Nat → Bits
  | 0 => 0xfffffffffffffffffffffff404220008410025
  | 1 => 0x289509244a2a892
  | 2 => 0x19115069424aa18
  | 3 => 0x60002921000540
  | _ => 0
def q21Atlas : Atlas := ⟨4,rawDecor 15 q21Pos q21Neg, 0xfea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8, q21N, q21R, (fun _ _ => 0), q21I, []⟩
end PEqualNP.Outside.L_meta_36366
namespace PEqualNP.Outside.L_meta_36366
open PEqualNP.Outside.L_meta_36366.Model
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
  | 1 => 0xffffffffffffffffffffffffffffffffffbecf
  | 3 => 0xffffffffffffffffffffffffffffffffffdf73
  | 5 => 0xefbc
  | _ => 0
def q22Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffff4205
  | 3 => 0x2412
  | 5 => 0x1828
  | _ => 0
def q22Atlas : Atlas := ⟨3,rawDecor 42 q22Pos q22Neg, 0xffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00, q22N, q22R, (fun _ _ => 0), q22I, []⟩
end PEqualNP.Outside.L_meta_36366
namespace PEqualNP.Outside.L_meta_36366
open PEqualNP.Outside.L_meta_36366.Model
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
  | 2 => 0xffffffffffffffffffffffffffffffffffdf73
  | 4 => 0xefbc
  | _ => 0
def q23Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffff4205
  | 2 => 0x2412
  | 4 => 0x1828
  | _ => 0
def q23Atlas : Atlas := ⟨3,rawDecor 21 q23Pos q23Neg, 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0, q23N, q23R, (fun _ _ => 0), q23I, []⟩
end PEqualNP.Outside.L_meta_36366
namespace PEqualNP.Outside.L_meta_36366
open PEqualNP.Outside.L_meta_36366.Model
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
  | 2 => 0xffffffffffffffffffffffffffffffffffdf73
  | 3 => 0xefbc
  | _ => 0
def q24Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffff4205
  | 2 => 0x2412
  | 3 => 0x1828
  | _ => 0
def q24Atlas : Atlas := ⟨3,rawDecor 13 q24Pos q24Neg, 0xfaa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0, q24N, q24R, (fun _ _ => 0), q24I, []⟩
end PEqualNP.Outside.L_meta_36366
namespace PEqualNP.Outside.L_meta_36366
open PEqualNP.Outside.L_meta_36366.Model
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
  | 4 => 0xefbc
  | _ => 0
def q25Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffff4205
  | 1 => 0x2412
  | 4 => 0x1828
  | _ => 0
def q25Atlas : Atlas := ⟨3,rawDecor 19 q25Pos q25Neg, 0xeeee8888eeee8888eeee8888eeee8888eeee8888eeee8888eeee8888eeee8888eeee8888eeee8888eeee8888eeee8888eeee8888eeee8888eeee8888eeee8888, q25N, q25R, (fun _ _ => 0), q25I, []⟩
end PEqualNP.Outside.L_meta_36366
namespace PEqualNP.Outside.L_meta_36366
open PEqualNP.Outside.L_meta_36366.Model
def q26K3 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def q26N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q26R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q26K3 (i*3) 3
  | _ => 0
def q26I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q26K3 (3+(h % 1)*1) 1) % 1)
  | _ => 0
def q26Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffbecf
  | 1 => 0xffffffffffffffffffffffffffffffffffdf73
  | 3 => 0xefbc
  | _ => 0
def q26Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffff4205
  | 1 => 0x2412
  | 3 => 0x1828
  | _ => 0
def q26Atlas : Atlas := ⟨3,rawDecor 11 q26Pos q26Neg, 0xee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88, q26N, q26R, (fun _ _ => 0), q26I, []⟩
end PEqualNP.Outside.L_meta_36366
namespace PEqualNP.Outside.L_meta_36366
open PEqualNP.Outside.L_meta_36366.Model
def gbK10 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK9 : Nat → Nat
  | 0 => 0x1002820400810001400000000022cb0400002400800000000060180180541401fe30007fd4401ff20007f88001fd41007f95001fd10007f08001fd31007f48401ff54007fd4801fd20007f55001ff40007fd4001fc52007f15001fc42007fd0c01fe32007f4c001fe10007fc8401fd43007f90001fd42007f50001fd51007f94801ff41007f10001fe50007fd0801fc50007f90801fd53007f54001ff53007f4c801fd52
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x8a8000ffd5143005fec6a800bff32840017eb088000ffd9530005fec4a1803ff6584001fe988a000fbc8620007ba6498003fe54840017fb1a8200ffd4420007fca918007fc53440013f32e8400fdd0521057fe21180037d5014007ff188401eff90452017fcc7080037d52d443ffe086a400efd0d42007fecb10003ff5348419fe30a800fff14e40007fa65a8803fd41d4001ef1826000bf98353005fac7a8002ed62100017e302a600bf5923002ff8a690003fc4284001fe9888000bf58252007fea7a0802fd61d4c01ffa8c6000ffd8121007fa631006ffc5350801ff2128206ff0c620007fe8690803bf4350401fe2146000bf58632007fa8628002ee6210001fea9a8000af59020017f86108003be40500017eb0c4015ff18d21087fe65a006bfc51508017e3024200ff4ca40007fa8710003bd5450c31ff20a6400ff58630007fac708003fd43c84017eb2c6400ffd4921007fa63a8002fd6414801ff1942000ff18a10007fec320002f56108001fe2828013ff0c7500fffc83a9003fd3244001ff3246000ff90931007fe8498803fd43d4015ff28c6012ffcc45003ff8c710003fe30440017eb0e8410ff0c340007fea898802fd63c8401be2a4a000ff54e20007f8caa0002fd64d442bff9824200ff55210007fc8108003fd3248001fca022000ff54921007fac0a1803fe408c001beaa6a000ff50e42007fccaa1803ee52484017fb246000df95050007fe4228002fc6050801bea92a200bfd9121005fac690803fd2084001ff1824000ff58d41007fea4a0803fc50100017eb108000ff50e50007fec690003fc50880017fb222003ff04020005facb180027e65080017eb288000fb48420007fc61900037f5454001ffa8a6000fb50b20005fec908003fd644c4017fb1aa400ffc8210007fca118057fc4348401ffaa28000ff94210007faa9180037d53d4401f6a124000bfd8d20005fac5a882bfe218c0017eb2a6000dfd9540007f46108002fe60d04017eb1a4000bf591320c7f82099003fd518c007fe2884018ff88532057f82118002fd65d0401ffb1a4200bfd9542007fc842800bfc6384025fe190a000ffd0850005fac52a002fd6108043fe180a800ff14a100c7f8a299003ff6390001ff32c6000fd50510006fea6a9003fc528c0017fb12601bffcc942005fac3a180ffe4108001beaa2a600ffd5220005fac9a9803fd6150c2dff992820aff1463004ffca298007fe434402bfe29a420dff94d40005facaa1802ff6050401ffa1c2017ff14f41005fac3a9003ff538401fff21c8000ffd9543005fec299002fd63880017e302a81bff0c14202ffc8690003fd42d44017eb06a400bf59532007fcc908003fe604c435ff18a840aff90630007fac098802fd6588001dea1e8200ff19543057fcc31805bfc3050401ff2826007ff94e20
  | 1 => 0x3fd6550c09ff28a4000ff4cb50005fac42a03bfe51900013eb2e8408ff8c7200b7fc86a0803fc5084001fe2804000ff4c740005fac5aa003fd514803bfe29e8400ff4ca20005fac828013fe21480017fb2a6200bf59121097f88628003fd3214001bea96a000fb8c921007faa708013fc51480017f3008000bf58910007fca088003fd5444013fe30a6000bfd8142007faa320003fc6548401ff284801eff8c452007fa42a8003fe2084001feaa48019ff042320affcc690803fe5048001f6a164200ff90a30005facb90003ff218c001fe2046000bf58f41007fcc0a1803fc4084001ff1844000efd0940057f8c318002fc60504017f306a800bf58e500057cc81003bfc1090033fe28c640eff88640007faa890003fd41500017f300a000fd48510005facb2a01ffe4388001fe2a26200efd0240047f8a3900037f5254401ffa846000df54c50007f46088003ff544c8017eb1e4004ff04120007f8ca9003fff31900017eb2a4200ff19530007fa84a0803fe5448401ffaa42000bfd8151007fe8518003fc50d0001ffa842000bfd91300bffe65a0857ff32484017fb1aa800ff90a10007fea688003ff5390005fe194200dff90d40007daa590802fd6590001fd1824000ffd0a10077f8a320003fa40840017eb1e8400bf98052007fea918003ff6148001fe312861aff98542005f8c0a1802ff6050c017eb00a400bf58e40005fecaa0823fc10c8001ffa9a4000ffd513002ffe6290002ff6350801beaa4a400ff509310cffc8319002fd64d48017fb0a4000bfd8121005faca10003ff65484017eb246400fd54521007fec0a8802ff6454801bf294a000ff14130097fc8628057fc304843fff886a400ff50d41007fa86a1002ff62440017fb12a600ff581210bff861a083bfe41900017eb0e8000ff50d520fffc63a9047fc4114023fe188a000ff98931007faa4a0002ff6254001fe3242000ffd8d40005eac220002fd6115001be32a8002ff94e10005fac1a9802fd65908017eb18801eff04052007fac890853fe43d401dfe30c80009f59440007fec318003ff5244001ffb142004ff90520007fcc099003fd21900017eb1ea400bfd8530006fca8a9003f930440017eb168600ef95143007fea520003ff628c001bea92a008ff907200b7fcc6a0803fd50840017eb2e8400bf181520fffc43a9003fd2148041fe30a8600ffd8e10007faa89088bfe43d5003fe31a2000fb480200077a8720003fd42140017eb1ca400ffd8152005fec498803f61044001ffa924000ff58a30005bac610003fd4350001fc9824000ff50620007faa11805bfc3250401fe90ca020ff98543006fea8a9803fc658c01bfe31a8000ff50450007faa510003fd6284043ff990a800bfd8d21007faca90803fd31500017eb288400bf58232005fec0a9802fd6444019fe1
  | 2 => 0x20005fec4aa003fd32d000dfe0844000bf58e54007fe810806bfc31508013f32c8400ff99521007fec688002fd63080017f304a800bf58343005fac910002fc6054401ffa046000bd58642007faa310003fd4348401fe2a42000df55351007fecb2001bfe21880017fb2c8000ffd4e200b7f8a6a0802ff6250445ff98ea800dfd4650005bac62a0027f65500017eb226000bf59252005fac39002fff3110001ffa988001ff94d10007fe86280037e5214001f72124200fe8c220037f8a310003fd6050439fe0848400ff9961002ff8c69001fff318801fff29c8000bf59542067fc82a000bfe4384001dea1a8200ff19640007fa87a9003fd30840017fb2a6000bf58254005fac62a002fe60d0c27ff10ea000ef50d42007f8c0a8802fc604c8017fb0a840aff10630005fac32a01bfc61880017fb1aa200ff4854002ffca690003ed32c8401be32a4000df15152007fec4a1853ff31d40017eb226211ff904500e7f8a321047fc2114001ffa928000bfd8a10005fec2a9003bd4250001bfaa4a400ffd9520007f8a899002fd60d04019faa4a800ff15230007fea7a1077ff31d0801fe302a412ffcc050005fcc11904ffe41d4031ff30a6400ff19620005feca90002ff638800dff20c4000ff8cb51005fcc1a1003fd21140017fb2a8600dfd4950007fa4220002fd63d5001ffa944000df55353005fec688002fd6594001fea126400ff48620005fcc129003fd4108001ffa08a000ff58943004f8ca90003fd4284001fea946000bf59321005fac7a8803f93088001fea146000ff54a10007fcc4a086ffe6350839ff20c8400ff4c941005fac508002fd628c0017eb064200df95352005fec708002fd6310801ffa126401ffcc910005fac1a8802ff604c8017fb22a000bfd9610007fa8318002ff6150001beaa2a200bf58750005fec09883fff329001bfe29a8000bfd9540007fac9080037f5394001bea8ca000ff48750007fac6a1003fd31080017eb1a2022ffcc354005fac628002fd62d4c01ff3028200ff50e52007f8c918017ff3248001ffa8c8000ff18153005fec2a1857fe5348401fe28460009f594200dffc86a1003ff5448401fe32c2000bfd8940007fea290007fc3044001be294a000bf58650007fecb1803bfe31900017f300a800bf58a20005fac3aa003fd4308001beaa0a400ff4c84003ff8a710002ff6055009ff18a4000ff50e1007ff86120003fd6584017fe2988000ffd4720007fa8118002fe60c8401ff3226200df54d52007ba8719003bd431000bfe1824000dfd4d51007faa498002fd618c001fea042000ff98a10004facb21003bd43d08017eb1c2000bfd9521007fac498803ff6055001fe9928000ff19510005fac5a0802fd65d00017fb2a6400ff5053007ff8c720002fe6090801f69924200ff981210077a802000
  | 3 => 0xfb02a600ffd9210007faa488002ff6488001fe3024200ff8c941007fea7a0003ff618801bff9928010ffcc7400077e8720083ff1050c016eb1e8400ff54530007fa6490827fc514c001ffb0a8600ff54a4004ff82098003dd434c001ffa0c6000df54d51007fa65a0802fd63d0013ff10a6000ffd8e20005fec898803fc424c40fff9944000ffd8540005fac121003ef20880013e32a8000bf58642005fac921003ff528c001fea924000bf58a40007fac690802fe60d4801ffa942000bf59652005faca88003fd4190001fea1ea200fb88120007f26108003fe644c819ff18a8000df54450007f8a890803ff5350843ff988a800ff181540dffe62a1003fd4148025ff990a020ff9454303ff86110003ff51500017f3008400bfd9630005fac5a0003fd6150801fe98c8000fb50921007f8c8908037f5094001ff2942000bf59020007f8410806bfe2150801f6a924200bf59210007dc8490003fd21d0013ff20a6000bfd9620005fec8a8803fc5250401feb246000bfd8553007fac4a082fff321001bfe1828000ff50720077f8632006bfc1050801ffb2a8000bf58054007fa8790003fd5450001fea1c8000ef50b40007fa86a8802fd6448001fea1a2000bf5925008ffc6228003ff614c009fe18a4000ff94a30017f8a708002fd65c84016eb188000bf58452005facb0801bfe3188001fe210a00bff0c0400affc8690802ff63500017eb0c8000bf58450006fea8a8802fd6110801ffa926000ff50d20067f820a0033fe5150021fe29e8000bf58850005fac920003fd31c8025fe180a011ffc4050005fec890053ff32d4001ff190a000bf59541004feca90003dd434c401ffa9a8200dfd9520007ea6290803fc628c001fea9a201dffccb42006faa7a9047fc1014045ff996a800ff98a30007faa8a1813fc6148001fea9c8000bfd8550005facaa0003fe5050001fe9942020ff04143067f8a2a001bfe5188035ff20a8400ff90b51005fcc1a8803fc50440017eb18a400ff14240107fc42a1847fe2114001fea124200bfd895106ffe62a0003fd614c801feb2c6000ff14120005fac329002fd6548029fe186a000bf58b5009ffc63a8003fc524c401ff3224200bf59743005fec0a9073fe319083bfe1868400bfd9153007fc61080037e50540017eb14a000bf98020017f8870808bfc30d5001fea9a4200ffd8143006faa8a8063fc414c801fe3028600bd58452007faa2a0033fe21500017fb2a2016ffcc141107f8a2a1803ff4248401ffb246000ff50c52007f8a190002fc604c4017fb0aa800fe50210005fac021002fd60d5001fd2022000ff59132004fcca20003ff5444041fe10a8600ffd9510007fca110003dd5350c01feaa44000bfd9132007fac099003ff524c401ffa9a8000fb48620005fac1a10037e5494001ffaa48000ffd51
  | 4 => 0x3a000a20615003084000642706409054010080d80a25818060961a09e068080580a000066681c1c83a068000e004008320121c00800560180280e0c900000021783ea289609000020e004800038041803e020000981e050040d014008020180213026008041c87c1302ae48160384e00aca008380880a20024008100080681812248bc410123d0307f84804822000101901a0e0200c000010100000b7082c0080e068341a00ccd01600004010080183603800010025e0940381c0214c00800220081d000570060484400032010000480c94aa8360140580a2c82000904a30380682c0384e0700200000100a206026030041380c0395c02898e7adc001dc00014000ea08854028060100800800bd006040002003e00008018500a84e0683a06070440201a8020195a158000883c0108e0a6180d0220381025800038be2299e060022d0003d8600d8000784807aa4000020081a0780601000038001382600000000728c0200283009bbc028240106a330ae05000091580086e00002fd63908017eb264000ff48530007fa86a8003ff5188031ff8826400ff98943007faa690003fd3148001ff180400aff086300077aa9a180bff3084001feaa26013ff04350005faca988037d5394041ff20a8600bf59350007fa4318003ff6448401f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0xc6550230006fe31d9120006fc5158a40005fc70591320067c6319520006fd63d4210007fa6018121004fe7648540026fe3158910004fd764cb500a4ff76542300f6f410584521079f3150d41006dd63d4420005fd7199543057f66148630096de6314040006fd7358452004fd7218154005ff7648630066ff3159110006fe43d852001fe63148420166fc654c210006ed624c4400dfbe3150d4215dfe7550d20007e8704862006efe4359230007f6744c521004fd7615210005fc7050d410077c7559131006fe7558632004fd764c440006fe6358542005ef7250e42006dc1058c200cfef638c921006fd6450d210b6fe3058743005fd73d8620004fe70d9543004fc76552200073c6555143006bd4358b410efee32d8943006fd6350420005bd7418a1001fef5148420005fd76d0a30024ff7158910006ff6559230006dd7258c40006fe72d8e101777f7119540027ee2148520036ff31d8a10005ff7050f510ef9f3150f4202efe3158232156fe7650f51006fc61d8943005fc7650d21006ff64981210defe31d8d4223fbc51509400eefd31d8943005fd74d8630006fe6359121006ff64d4d21106f4615854306cfd7699230056f6618c020005fc705093107ff7314c6400063d649525026ff463d0521005ff74589311b77e65d4d210ff7d51d4a10007e9728c2200057d75d0850006ff6450d2101fec1048420056fe305863016ff873502100057c7054f511777c5319540006fd6190230007ee70484200aede43d8d21064ff715911004edd3158e10016dc6358e10006fe63981210067f319974204efe1058e10006ff63505400e7bf41d91210d6ff3159121007bd435042005efd531814301efd3118121046fe31d812103efe31d89300063d6550f42005ff7150e2021fde5150d30004fc7655230006fc7650d521b6fe76484500077c6554620006ff7459121056f63158630175fe75d8540007fb5350110025fc71d51200057c7550210277ec6350921086ff53d8143004fd7418121066ff3159210006fd43d8a10004ff7458452165fe7548530007fa6550210006fc75d852001dfc7150c20006bd6450c20004fd72d9131006fd74181510cefd71d8d21006bd435864017ffb3290210006fe21d8e20006fe7650d52007dd7050d31066fc7059210007ef544c9210a5fd73d4230007fa428c2101277f54d4d10057fb218c21015efc6548210006fd7259050005fd73981210d6fd3158b41006fd72d8e20087ef324cb40006fd618c3200077d7119520007ed7448420004fc7650d10004fd764863000ff9328c110006fd62d8630007fa758c120004fc7059442006fe43d8540107bf4150d21006dd43d8530004fd76140400eefe30d8943006fd715905000ff53158630006ff54d8d10006fc75d9121155fe75d814305efe43181430057e75d0a10
  | 1 => 0x8c20026ff5158321056fd61d0630005ff7254e10006fd7059131006bd6350b40047be4150720006fe63192100057e75d0a30005fc705893106efd3159130004fd76d0a10004fc7058c540e7ed31909210067f5318151056df31d8d10004fc7059351006fd7358450006fd6150230004fe7695121004ff7358054005fd7314120005fc7054d20004fc7058753006df7258c54006fc5458d21005f57190850026ff6150520006fc7648630067f4314c540056ff21d8e10004ff7159352007bd5390140005ff7350720006ff644c921006fc7558632007d7634c521046fa10d8121005bd7414240006fd715913216ffb325021004cff7158d10006fe6158d42004dd7318142006fd7158f42005fe76d0d21006ee6214040007bd7150d420077d4354450186fe6550931006fd63d8a10007dd434c620005f970d0a100067d6454c50066fe1059210004fd71d8143007f850c8210006fc5358341005bc7055343006fd6450630005bd7408210005ff7448630076ff3198040065fd76d021015f7c511952008ff66148450004fc70595310066d6548420016f531d8530007f731d8540004fe7650520006fe6198143006fd53d8520006ad4358840004fb7059542026ef2158a1002efa30582321bf7c54d4931004fd72d8d41004ff7158a40066f431d8540004fc76551300067d5458452006fe41d8d40006fe7650e20006fd74d8520007ed218c020005fd741812108dfa70d96100076e5248450005fd76d0d210c5ff714c910007dd7550d30007f53148520006fd7559230004fd71d813205fbc4318143006ff7059131005f57190931005fd7650a30007ed5248620005f57114a3007dfe7348640006fc5358620004ff7158054007eb218c220005fd7314a100d5fd7150a10004fd7118142006fe7118143017da638c2100defd3158b43007ed544862006fdf3150d40006fe2158850057dd31d8d1001ef45158420006ff64d4d10006ff3159350006ed6290a10006bd4318142006fd6458e10006ed6214040006fe51d8d40007be7050c4016ff83050210035fc7155220006ff6390a10006dd638c0200073f5495121137f85390110006fd764ca10005fd7398a100077f7558d21004fc7654620115ff73d5130004fd764cb41005f97090a30007fb548c110007fb6350210107dd3150d21005ff72591310d7f631509210057e7518a30006fe6058131006fc7558630006fd7650e50095fa70d96300077e71195400047f7559220005fd7294210006ee624c440035fe714ca20004fe7694a30005fc704c72006efd53592300067f6514120005dd7394230005ff74586300057d7508210157dd6350c50006fd7158f40007f75348510105f4715814300efd3258630006fe6558943005fd744c9410067f65d85201d7ef315092025fbc5150e40006fc53d8910176f
  | 2 => 0x6fbe43581430067f6550d40004ff7158e40006ed6218943006fd644863002efd3158232006fc53d91210073d5450f50005fc704c7400077d52d4520004fc7059353005fa7090a30026fe41d85200057d71d4250007bf53d09401ffee7348620006fe7559210027de314c520004fe76952301b7ed624845007fbf31d0e40016fd634ca10007ef744862006ebf4359230006fe7058c40006ed6218a30006fe4159230065ff714c540004ff74587500c6ff614c910006fe7058642006fe76505201877f53508500067c654c9400077e7319540004fd7650850035fe711422004eff6150530005ff7250d41006fe5318121006fd64149310047d7518142006fd7458f50006fe73d8520006fe705912112ff8535011003efe31d8e20005fd7695210006fd63d4520004ff7358254004ff7158232006fd4218131006fd64d8a100067f3119520006df7258c400067c6550d20007be7550f420afe5324c521026fe51d8520005dd73d0921006fd649812125fbc6150e40005fc7654d40006fc6558a1002fed3258a30007ed52d8121007df7358931004fd74d8d21006fe70d8d21006ff7458d21004fd76504500e6bd41d9121006ff659814306fde53581430077f65d4d40006fd6318121006fc65d8d40006fc70d85431befc654c620007dd634ca10005fd741493102efe3158a30006fd64d4e10006fe5159230007ed4348620037ed31c862007efd31d9130004fd76d0630007ef7250d42005fd74d4620096df3258c500057e75d0932005bd7494240095de73d0850005fd731921003efa608c0200aff53148530066ff6148540006ff5458630006fe4358a1006dfe7348540006fd7648630005ff724c640004fc7059131007d87050d30004ff7458c50005fd7090931105ff7150d10006fd6390210016fd638c210005fa7094a300fdfd71d4a10006fe6558d21007ee42484500077d53d4620005fd7499630005fc7055121147f45350510004fd7218151006bf64d0921037ed5148620024fd7698a10007ef7259132007fb748c120045fe7150f20007b9401023007fde434c640005fd744c921016de63d8e10006ad6448420005ed72942200057c7550230105bd73d0d41004fc7654a301befe654c540055f67190a30096fd30181531577f5250f510077d73195200077e71d9520096dc3058c50006fe5118143006ed6250a300077c6555143005fd7650931006ff6348540095fd73141300c7ef214ca10006fc75586420077c7550d52006fd7358750006fd74d8d10006fc7359121055f67110230007dd53981430067c1019540116fe30d9153005ff744c520025fe71d95200fefd10d8951005ff7154d20007bf7150d42004fd768c850006fe4118143105fd7150d10004fd7614a3006ff7314c540004fc7059742004ff735825208f762154450006fe415
  | 3 => 0xc6554d40005fd7099131006ff72d8543006fe61d814305fbf3150c40086fc53d8143005f8705513007fef324ca40006fd6350210007ee654c921035fe71d8e200057d7590850037ed2188210006fc7058d21007ed6390921006bd64d0a10107dd3150d10006fd644c921006fd71d9230006ff63d8520005fc7054530006fc7558a10007ef424c921005dd7315131006ff715913205ef93018143006fe315922024fbc53d0940005ff724c540006fe6198a301befc654c540005fd7194220006fd63d0921006fe74d8d210d6ff31d8542005fd71d523004eff4158e10006ff74d8d21004ff7158c54006fd644ca10004ff7259230007df7358131006f73258440004ff7458a1020fde518c130007bf6450e1002edf32d8d2002eff634c520007bd7050d4107efe43d9230007f4654c521006f43058440005ff7258131006dd7458c20006dc7058c5406fde434c540004ff7648450005fd71195300057f7558543006bd648c02025fbe2150e400067f65995431dfec519092007fbc3050e40006fc61581430057c7548210006fc53d9110006fd7650f50007ed42d4520005fe70d8543004fe70d9532006ed6250850005fd7119520006fc6558143006fd72d8d10005fd71d0a30006ff3159050007ed525812107cff73d91301877f5150850005ff76506300377e51d46200c6fd4158d21007f8758c120007be7550d41037ef3148620007ec6590921006fe7359050007ed3148020005fd718c020006fd764c7200047f76540500c5ed738c92101ff65118121006ff32d921010fdf3019543036fd31980200067f7655350006fc51d894013ff45348510005fc7054520007f9418c22006ff830502300067e654c44008dfd71c8450005fd7219630006fe764c620006fd64d4d21005fe70995210067d625445003efe3158e20006fd7650c200e7f631d912103ffa314c220007ed3218121006dd6350f50005fe70d4520006fc75d8d20005fd7448630006fd7650f20026fd4158a10006bd6450c52007fb6450210004fd7418153006bd64d4420006fe7648540076bd41d9110054ff7358d10007ef5350920004fd71d8152006f67058452006bc1059020005ff7354a40006fc3118142005f77150e10006fd648c2101c6fe655063007ebd43d913021fdc5150d30006bd64d0450005fd72d8e10007dd4314931006fd4358420006fc65d85400057d7518a10107f63150d21005ef7254e2008f7d5114210107b47150d41006fd65592300055d7315152006fd64d4d10106fd2158f41007f531484500377c5154620005fd74996100079d5350e400067e75d8e10006fd6450c50026ff6148520007bd3150040005f970d0e10086fd634c740005fc7058d410afde43d8d21005ff7458a30017f9434c210006fd5358a100077d54d45200067d658c020156fc7650f51
  | 4 => 0x8121007bc7050d42007f4644c521007fb60981430ddff735093106efa305834305eff3158c40004ff745863209ff63148750007bd4310210007ef6350921007f850d0230004fc7654d21005fd74d8d21005ff7358a100047f7558321025fe75d4520155fc7558143005fd7695230006fd5358620006fc5359210005ff735494007efc31d9130007f77150d41005f77150f51005fd7499521006fd43181520077e6554a30006f731d8540007bd424c7400077c51d95200067f7654b5003efd31d8930005fd70d09310077c53d9540006fc5458630006fe619813201dfd71082101bf7c544c450006fe75d8d100057c7558d41175fc754c940004fe70d954107efd53d92300077c7558532006fb614c12006efc31591300dfbd7250d4215dfc754c5200079d434c440046fd31d81210977f5350c50004fd7118154006fd6398a10005fd76c8630006ff6558a10006fd7258750004fd7498353005ef7258143006fd5418121006de7058f42026fd2158a10006ff6450630005fd7114120106f410d8543006fc6399210026fe4158a1000ef53158630006fc515913205ffa3018143004f87059542006fd64909310bfdc32d854302ff9438c1200c7ed414c921007fa728c210105fd7150f211f7fa418c2200077d5314120006fe3158850007cf7250e32004fd73d9210006fd6458131066bd4159210005fd73d46201b5fc7550d21004ff7654a1004ff9634c210005fd7414210025fc7114120005fe7098931186fc6550a10006fe7258450007ed6250a10007dd53d8143004fe76d06300f5fe7599521006fc51d8d40055fb734c110006fe6358a10006fd53d89100077e6555230004ff7458e10175fe754c940007bf64d092106efe5359130056fd41d8d10004fd768c941007f77150d21005ff7059131005ec7258143006fd71d89431b6fe6548630006fd6518143005fd7218143005fd72151310067d5318152005fe70d9543006fd7218151005ff7150c52006fd624c740006fe4159132004fc70595430a6fa30d81530b7dc3258543005ff7348440006fe3258450006fd745863007efe3158e40006fd6314340005fc764c52007fbf3250e40006ff6314120025fe718c120004fd72181310047f7558341006fd64981310057f75502100067c7059742005fe7090931006f5614c720006f9628c110047fa10d8121026fe5158a10006df7158f42197ee31881200067e654c420007f9718c120006ff624ca10006ff3158054107f641d8543005fd73152100057f754c85004eff6148530005fc7050d21005fe7695121005ff7250d210cff710d8d21006fe73592100aff5724c521004fd7318141006fd7458d21005fd71d09320c4fd764c921006ff5458e10004fd76d0850007bd43d0921007ec544c921007bc6550e4009efd61487500076c65549210077
  | 5 => 0x77f5454530155fc7558543036fe51d8910006fd765093101efc1058420007bb7050e40047de314c7200077e31195200047f7655052017fa328c2100d6ff3158b4106fdf3158143005dd73991210067f6550d20006fe705842004edf3158e10006fe7058c54006ff6448630156fe6550d21007ed218c220037e63148620005fd73d854010f7f5319543006ed6248750006f67058440007ee754842006dfc731414001fec7048420005fd7198143004fd72d8d40006dd7158c40006ff42586300077c6554e40006fe41d9230006fe7558d21006fe6318121005fd7310210005fd7119540007bd43d8640006fd72d8530004ff7358850007fb5250210006fe51d9230005fd7319520006de31d8d200077c754865007fbc6350e40006fd75d8520007fb624c2100067c658c120007ea728c220006fd4318121007bd4350850004fe7650d50037f63198121117df3199543006fd6558a10027f81048210055f671d963015dfe75d8d20005ff744c72015dfe75505201d7ec5350920006fe62d8630004ff7158343037ef5148620004fd72d8540007f5424c5211aff8718c120094fe76941301c6fc6550630006fd72d9210004dd73d96100077e5119540004fd76d0a30006fc5159120006fd7158f50005fd768ca10006dd634c440277ef3250921057f9418c110004fd764ca1014efc654c94107fbf53d0e40005fd768c9410047e76d4950006ff7258e10006dd6350e10006fc53591100c6f6614c840006fd7418153006fd764c540004fd7615230026fc51d8520005fd739814101efd5118121007f87050e4006fef324c940006fd6308210037ec1048620006fe764ca40006ff644c5200d7f63159121005ff7258e101b5fd7648450005f97390210004fc7059132005fd7694a10006fc5359121006fc5159230035fc7154e2003eed32d8930007f9644c210026fd315891007fbc4398143006fe7058d21006fb6098121004ff76552300057c75581320077d7319540006ff76484500dfbd4350931004fd74d8e10006fe6159230005ff7150e42005bf7350040105ff7150f2106dff7354d40076ff3158640005fd7114130037ee70486200077d51142300c5fd714c921006fc70d8943007f763d0521004fe7650d10007fb6098121007bd4350620007ef5348620006fd5218121007e53148420007ed7448620006fc6319121007bd5418143005f57119230006fc74d8d21004ff7159120007f9218c220006f57358420006fd745875022fbe51901400e7bd41d9121005fd72d86300067c1019520277ec3050921005ff7159230035fc7150e20005ff764ca10007eb7048620007bd74981430077d5114240004fc7648640004ff74588500d6fd31593210977d5314130107bd4150d21004ff73583420057e75991321577f5150c50006f5615045001efc311
  | 6 => 0xd7299630006fd6454530006ff735921002efd3158a30016ff638ca1010dbe76951430ecff7259132006fc65581211777f52d4540115ff7655143006ff7559230006fd644c850007b942502100067c7059420007bc7550d420cff441d8d21005ff714c840077f9319021014fdd634c85005fbd4310230004fc7654640057f9218c110005ec7054921006fe65d814303efe3198232107dd3150f21006ed6448420006bd6419230006fc30587400b6fd3258743005f5719421006ede43d8d400057c7558931007ed3248620004fc7058752007f9748c210005fe70d4720004fd7318121007f87050d40006ef7259132175fc76d4540004ff7358341007bf7250d42005ff7154920006fc7358a10006f54358642006fe72d8543006fe764c520004fd76109311b6fc6548630006fc5458e10006fe71d8e20005fd7694a30007f5314874005fbf5350c40006fd72d9230006fc70d8d21006fd7158a30007f97048630006fd73181211777f53d4940006fc7650d2006efc30d8d40006fc7558c40006fd63d81210057f7558143004ff7648630006bd64102301f7fa718c220004ff7655210006dc7058c40006ef3158840006f5614845015f7f53d4520075fa7019210006fc7650d50005fd7318a10055f67118a30166fe654c2100077d5114140006fd7318152005ff72585430067f6599521005fd7110230004fd7650a30006fd618c020005f77154d10006fd6498132006fd3258440007f67548510006ff75d8520007fa7050e10026fe7058a10006fc63d8540006fc51d8943006fe6498131005fd7414230057f63148630007dd439093106efd3158343056fd6150630125fe758c1100057d75d0a10025fc71d4920017fb734c210004fe768ca100057d73d4250006dd6350c52147f67350510054fd71d8d10006df6350d52006fd6598143006fd6398141006bd6450f21006fe43d9121007dd4358131077f63148640006fc7058f42027f6214c520006f9624c210005fd74d8a10004ff73584520057f7550450006ff3118142006fc65d8121106f66150c52004fe70d89430a67f7654c50006bd7359020036fe5158620006fc7559132005f87054a20005fd73486200057f755023001ef63158420015de7308210006ff6450931086fd53d8143006bf6450d201bdfe7550931006fe3158a4001efd61d4420056fd21d8d100eeee32d8943156fc6550e10006fd63508500057e7598943006f4755842015efe6548210006dd6314040165fe7550530006fd63507500077c7558543004ff745863020fde718c130004fd71d8153004fc7654d400adde73991210067c654c920007fa3048210006ff64181211b77c65d4921005ff7359210046fd615072010dfd731523007efe53d9130007dd439813107fbe3150e40006fe65d9121005fe764c520004fc7059741
  | 7 => 0x8d420eedf3258f4206efc3059230006fd735872006dfe75d4d40007bd4394240006fd7650e521e7ee31c8220175fe754c540006fe7059131006fe61d9230027f81058a10107df3150d21005ee721021005dfd73102300edfd73d0931007dd73d8943006fd7650e1006eff3159130006fd72d8543004ff764874005fbd434c840007bc6450e10106ff71591310067d5318151005ec7050921006fc73d9121006bd64d0850006fc31d9120156fc6550e20004fc7059352026fc7058a10005fd7098931004f771591300077f6599521067f63148540005fd72d4e40004fc7058f41007f7644c5210aedf32d8d21026fc3158910056fd6148630006bd6450450005fd73989410067d6519610005fd7198943006fd7650d210aedc30d8d21006ff32d8540004ff7458a300057e7518a10006fe5358910006ff65d8d40096fd6350c50006fe6558a30006fd63d0a10006dd6350420005fd7115132006ed7158840016ff634c210004fc7059743006ff62d0931004ff7358052017de6350e101ffec5348620006fc6558e10007ef5448620047f651d8121096fd4318153007ed32d8121007fb518c120005757114a50006fe2159230006ff6454530004fd7318152006ff53586400c5fd714c9101aff8108c1200aff5434c521045fe718c320005ed7210210006fc764864003ff9314c22005eff3218143006fa70d9230004fe7648550007dd739813103fdf3150e2007dfe73942400057f7548210006fd74d8a10006fd6348750005f57114941067fb7150210005fd73d4a10005fd71d8d2007fbc53d0e400adff73485300d5ed7299121006fd64d8a300067e3199642006fc7559210006fd7318154006f571d9121006fd6214230107f451d8543007f7715913101eff3118121006ff3258740006fc7458e100067e4319540107bd4150d10006fd644c620005fd7690a10004fd764844004cfd73d8e10007b94390210006fd7258f42006fc4258630005fc7654d21217dc514c930006fc65d8520006ff7650c52006ad6250040006fc30d85400e4fe7619121006fd6458a30005fd729954303eff634c620125fc7550d10086fe63d0210035fc7154a20006ff6348210046fe4158720007bf7150e40006fe73d8540005fd7115230015de73102101bff5614c4500adde7315121006fe53d8121005f77159543004ff7258f40007bd7150e40007ea3088120005797095250006df7158c540077f539414006efc63d8d4006eff32d8d4001fed4148420005fd7494230007fb7350210287bc7150d42004ff7648440017de4358e101befc654c520017f9324c210005bd73d0240004ff7650c5005efd63d4c40026fc5158a10005ff7348520005f87048620057df31d8d10004fe70d91210047f7559120007f553485101befc654c640006ff73d8520005fd71d4e40005f
  | 8 => 0x16ff73d8530004fe7615230047f810c821006dfe7394140007ec658c92102eff6350d2014f7f514c8500057c7055151007f9629021004efd4158e10006fc7558f42006fd6310a10016de43d8530006fd764c620005dd73192101177f53d5130006fd4258450227bf3150040006dd634c450006dd638c210186fc6550931004fe7650d52006fe6558a100067c7558d21006f7745842015f7f54d45201c5fc754c941005fa7015210005fd71d8943005f97094a30006ff7358420006fd53d8a10006ef5358840036fc51d8910006ff72d8d10004fc7058642004fe70d9531007bd6450a30006fd64d4931015de73d0a100067d6550e42086ff3158f400c6dd3158f21006fd65d81430077c6554630006fe7558642006fc63d9121005f77154921006de7058c40004fe7650a10005fd74d4e40005fd7298143005fd71d4d4007dfe7319640027fb1058a10006fe21d8943004ff7359220006fc6258543005fd7119630006fe43d8a101dfee31909200e7ed2190a101a7f8514c120007be7050d42004fc7650d520f6f64158452107bf7150f41007df7150e320073e5450c500defe3159232006fd641812105fbc5350c40005fd7219543006fe7558a100077e73d954004ff71058e100c7ed214c910034ff71d891015f7f54d4d200aefd63d0d21006fe6298131026fc61d85201bf7f544c750006be6414020006fe4359121006fd624c450007f85050210007ef6298943006ff32d8520006fc6559210005fd7319510005fd76d0931007bd431494107efd634c640007f9628c210005fe764c54009efa10d8151064fd76d0210005f87054910006fe51d81430057d75d0a3002efc7058a30004ff7358242006de4158c201777c5119540005fc704c540006fe31d8940004fd71d8142007f77548510005fd718c2200e7ef649092106eff3259230005fd73d085016ff86350210007ed3258121006fe2159132007ed318812007eff31d9130005ff7348450007dd7150e32007ee324845023fbe3150940006fe7558720107bd7150f41006ff7650f21006fe4359210007f6644c521006fd3218141006fe21d8d401b5fc7558d210d4fd76509211bdfd764c75005efd634c840026fe21d8520005f57190a10006dd63d4e100b6ff634c941004fd764c8500067c65505400c6fe1058f21105fd73d0d21007bd43d4a4001fee41484201577c65d5143006fe75d9121006fe6198943006fe6559121005fd718c8500b5ff7350630005fd7314340006ff7648630085fc7348740005fd7119620005fd7114320007fb544c210006be644c42003efd634c620067f93150210106f661d8543006fd64d8630064fd7699210156fc7650c50006fc30d852002eed3258a30005ff7058931006fe7559230006fd74d8530005fd7650630006ff71d8943006fd7458450005ff715
  | 9 => 0xe704c921007e53148620006fd6258131115fd73d5130006fc63991211777f5114140006ff7648440007ee429812106eff5359130006ff6458a3007f7e53d4e4002efd768c320004fd76c8630006f47058642007bd7250e40005fd72d4520076fd31d9210007bd4390941005fd7498132086bf7650c400077f7550c50006fe7648550107bd4150f21006fd7359121007f571d9121006ed42d85200067f64d4d52006fd7648440006ff7058d21007f53148750004ff71592300067d52587500afdc30d8d21007fa748c21007dfe73d8640036fd41d8a1015f7f7319520005ee7210230007bc7050e40006ff7258f40005f57190b51005ff7458532005ff7158943005fd73d0210007fa30c82100e6f41058642006fd6298131006fc3159220006fd7318151004fd7695230006bd64d0d21007bd31d0240046fc515872006dfe7319540046fd51d81210077e31d952005efc5358c400067d5458750005ff735524005efe3118143004fe7650e20006bd7159020006fe765062004efd2158e10004fd7198352007b9649021001ef91018121006fc3058a100defe3159132055f67114a30057f2718c210107df3150d10007fb548c120005fd7690a30007ef6248630006bd6450420006dd634c7400067c6548540006fd3218121004fc7655210025ff734c520006ff6358a10004fe7650530005fd73d8520005fe7019543007d9434c210006dd634ca101bf7c524c4500047f7558232004fd7695210004fd76487400057d7598943005fa70d0a10125fc758c110005fd72d4d40006fd6358121007df7150d30007ed4390921006fc7158a300067f658c120007ac6450921006fd43181511777f53141400067e41195401677f54d4530006f6735844000778658c120005fd7650e100067f54d8d51006fe6118a30005fd7610a10007dd7150d301c5fe754c941027dc314c5201f7fa218c220006fc7650e20006ff74d85400eedc3058f42006fe6358941006fd7458e10006f9601812104efc7058e10006fc73d85400afed638c921006dd7158f42046fc31d8121006fc65d8d21037ee2198121006fe7558f42004fe76485300067f5458e521b77c75484500067e6550c20027f65158121026fe2158a100057e75d09210efed32d89430077d53d4a10006f57458642004fc705953213ff47348510107f621d8543004fd73181510077c6554e20005fd7314210006fd764c420107f47150d21156fc6550d400eeff7258f420067f3199440004fd73d8540005fd71d9230005fd731494106efe31d8d40004fc7654d20005fd7318121036fc5158620005ff7155220007f9728c220007f77158131006fc65d8530005ff7150f5208ef64158450005fd71d8e400067d53584500077e6554d21006fd61981320aefd7358632006ed624c850004fd71d8154006fc62d8543
  | 10 => 0x4f400067d6514040155fc7558943006fe7159230005ff7355140007dd43d4931125fc76d4d10106ff7158f41006fe63d8a10056f46158630006fc7458d21176fc6550210004ef725913008ef62158450006fe3158052006f5614c420036fd21d8a10007f9728c110035fe71d9620036ed219802007efc3158e400b5fd7350530007f9601814306efe70592301877f5350b5107efe5358e40007bd4314240026fe31d852001fbe4150420005ee7094921006fc6558a30007ec70486200056d7590921006ff64d4530006b543584400aff53148630037ef51c8620006ff6394140087fa30d814322fbe3190140006fc6359121056f661d8630006fe6358121007f53148640006fd7458850005ef7250d42197ec31881200057e7508210006ff6118143006be4159020036fe41d8a10005fd7090b51036fe51d8a100c5fd738c941007ef7250c200afef634c9210067e431952019fee5388120106fd7158f4101fec5148420004fc7648530005ff7259210006fd4358450006f5614c440076fd3198341007bd5498143004fd73d81410d5fd7150921006fe64d8630007ee4248630006fe765053006fbd4359230007ee754862005f9f3150c40016dc5358e10006fd73d852007eff53d9130006ff3158342006fe21d9230004fc7058632006ff63c8210006fd6258543005fd71d8d40006ff7648740056ff71d8d10007dc7250d31006f56114040006fe31980520b5f57199131055fd718c1100e5fe7619121267bf3150b40107b71050d41006fe6358141066fd215921007fbd434c640026fd515891003dfa7018a30175fe7548540006fc71d8d20006fd64d45300d7f62150931007f23084110007ed64909210077c654c520006fd74d8d21005ff73482100e7e63190921006fd6118143005fb7350210005ff7654a30006fd624c6400befe32d8543186fe6550a1006efe3159230006fd7258c50006fd7650c520afdf32d8d21005fd74d8a30007bd424c540006f573584400aeff7358d21005ed7210230007f9428c210006fe6359210005f57190a30005ff724c620005ff73504200076d5248750007f53198121004fd73d81510047f7558d21107dd7150d3100fdf3058630006fe764c940006ff6598121004ff7158352006fd624c440056ff6350530006fd638821001dfe7150c200057d7590a1007dfe73506400057e7510210006fd735921003fde434c620006bd4358840005fd74d4d400c7ed414cb210b6fe325913114efc654ca10004ff7259351007f57548510006fc64d8d21006ff3158b400afef434c92110edf3158c54006fc5258630007f96250210107df7150d310067c7059440006ff3258a10006fe63d81210057e7598131005ed728c020006fc72d8543004fd72d8e1015f7c7319520007f87048620006ff7650f50006ed624c840007e
  | 11 => 0x5ff7150d200057c7055353006fc75d8943004ff7158254006ff7358720007ed5248520017f9438c210004fd7610850006ff7650f20007ad4248740006ff625863006dfe73d954010f7d5319543007f94390210005fd711954306dfe7350540006fd7648740026fc51583210057e7590931005ff7150c500077f5354a40005fd7118943005ee72192300047f7559131006fd6258630004ff7358910004ff7458b530b79f3050d41007ea428c120007df7358532005f9748c210006fc10d8d20006ff6458a1001fef7218121037ed4148620004fc7654530007ed31c8220006fd7458a10007bf7250e40025fc71551200079d4350931006ff65d81430047e7619540025fe714c920006fd7258c54057fb718c110004ff7358a10006fc51d81430b7bf4350630006ed6248740006fe2118143004fd7650f50085fd73d0230006fe6159132006fd6314a1007dfc73486400067c6550520006fc6398121006fe7648530057f9718c210007f8654c210006ff52d8540006ff73586421bdfd764c450005ed7215121007bd439814101ff91018121006f57458452006ff65d85200057d75192100077d54d4e400c7e7104c921006ff7458632006fe71d8943004fd7650c20175fe7550d40006fe4359050107f631d8543005fd744c450005fa70d0e10005ff7358542005ed7214020056ff6348530006fe764c640006fc30d894100eff4358630017de634ca100aedc6358d210fff63199521006f56114020006ff7259210006ff32d8941006ff635092107eff32d9230006fe71d8d40006fd74587200057d75d8e10005f5718c2100eefe31d8943006fd764c941006bd4358a4001efc7058420007fb408c210015de73192100057d7518a300077c7558d21007f96018121005ff744c640007f5644c52106f7e53d4d40004fd7648650006ed6250a10006fe7648640187bd6450850007bd54d814307efe6390210004ff7158f40006f67558420004fc765491005edf3158c40004fe7610a3003efd3198232006fe6458e10005ed7219230007ed7350921005fd721961004efb614c1100befd30d8543006ff6350a10006bf6450e10005fd744c5200057f754c750046ff31d8121007bd7250f41004fe76d0e10005fd7419630005f77150d410047e7615152006ff63d494004ff631d8530006ec5358840004fd711813201ff63118121007ed53486200063d6550c401c77f53d4941004fd7650e50006ff31d9120005ee7090921026ff3158910007bc7050f41006fc7650e10006fe3159120175fe75d8d40004ff73584200977d5350c50007fb728c110004fe7614a10006fd62d8543005fc70585320077e5319521005ee7219210095fd7314230005dd7315210005fd708cb51006dc5158c201ffee43486201b5fe7518121006fd7458632005fd7314240086fd63d
  | 12 => 0xb734c120056fd61c8630007bd43585420afcf304c921006bd64d0c5007fbc3150e40125fe754c9100c7f71058d21006ff53d8121046ff51d812108ef910181510047d7695050004fd71d8d420077d5114220004fd74d8d10125fc754c910005f87055230007ec65486200a6de4358f500d7ed3150921006bd4398341007db734c210005f87055240005ff744c540006dc7058f420077c3119520007ef7548620056f41058630004fd76506300067c6548520006ff63d85400ff7f51d4921056fd71d8e10006ff624c540007be7550c40006ff52d85200afed438c9210067e4119520006fc6558543006ff535834205dfa70d92300077e5319520006fe7458e10006fe31d922004efd1058e10006fc3158a40006fd764c7400067e654c840005f87050e40056fc705863006efe6350210007bf7150f42006fe75d8543006fc61d8d40006de7058c54007e532d0521037ee5148620006fc5158d200067e658c0200057d7590a300057f7558d21006fe764ca100077c6554921006ff62d854302edc31d8d20006fd74d8e10005fe701513108f7d51484500077f5354640006fb624c210004fd7694a10007ad4350921005df7355143006fd74584200067f6599610005fd7314140005fe70d4f40006f47058452006fc5358640005dd7315230004fd76d0c50006fc7558a3003eff6350e20006fc7058632005fe70d093125fbc7150e40004ff73583540aefd4358632004fd7218143005ed729512123fbc31509400077c6555121006ff62585430077d53d4520006fd64d4a3002efd4358a3001efd6150420005f77150d21005fe7099543007f76158543006fd63d0450006fd7118143005fd76d0e10007f7544c5210ff7d51d4910156fc6550e400077d5314210077fb3190210005fc7054d40006ff421813106efc5359130007ed4248450006ff63d0210006ff7650e5204ff9414c210007dd434c520005fe70d9121004fd7694a30106f641d8543004fd76c8450007dd7250d31006bf6350940005fd7319540007dc7050d31004fd7650f20005ff7348740007f57198131005dd7310210007bd43d0450006fe65d8943007bd7150f42007f531485400057c70553510057d7315250006fd6598121005bf7448440006fe41d8943086fd634cb40004ff7258e10006ff61941200067d5358850155fd7650c5006eff3158343007bd64d0d21006ff63d4520006fc7059121005fd769093108cfe7694110156fe6550e100067f64d4d51006ff7458720006ef6248530005ec7054b21005fd72d9230006ff7650d21007bb74502100057e7510230004fe764c540006fd64942301b5fc76d4d21007bc7550e40055f6711923008dfd7114210006fd64989310067c1099420007bd4350a1003ffa318c2200079d5450d300057c7558121004fe70d8543026fe3158a10
  | 13 => 0x4540005fd71142400f7f7101952105efd3118143007bc7250d41007f9418c120016de4358e10006fe725863011ff65384110006ed4258720026fd624c6201c77f5350450006fd7650630007bd7498141007b543d05210977d5314230004fd71d923001cfe70d8a10007d5434c521006ff32d91210debd4359232006fd6294210067fb3150210006ff6314140006fe64d8d21005fd744c720005fd71d8a30006fd76486500057d7599121007f77348510287bc1050d420aeff6350d21005fd72991310077f5354940036fe31d8910026ff51589100cdfd718ca1002ffa314c120006fd4358850006fd7650f210063f6495152006bd6450a30005fa7014a30006fd73d9210005ef7350921007ee744c921025fd76c82100067c65d8d20006ff64d45200067f65485400f77d51195210067c6319540006fd6448450004fd7614941006fb618c12008ef63158450007dd4398931006fc7258630007bd4350b51006fe6158143005fd728c21004ff9214c210006fc6158a30006ff7158f4001efe4158420006dd63d4c40005fd7110a30006fe6558e10004fe7694120006fd7158c541577e6519543006fc715923007fbe5350e400277c5154520007b764d0521006fc30d912106eff735923007fbe7050e40006ff52d8530007d9324c210004ff7258f41006fc421813106eff634c540006fd635464007dfa7019230004fc7654930006ff535891000efd735863027fdc7150e3215dfe75d8520007ed5188120007ec6550921004ff7158052006ff7650e10006ff64d4d20005fe76d4d40155fe7598143006f57358452017f9638c210016fd63d0e10004ff7358b54007f9639021007efe31d9230005dd7318a10006fd6218143086fc5358f400077e3119540007dd434c45015dfc76d4d20007f94350210006ff64d8d210077e5119543004fc7654520004fd768ca100077b658c12006dfc73485400067d6354b50087bd43992300057d75d8630006ad6448020006bf7459210006ff62d4530006ed6218a10006bf745923007efc53d91300067d5458f500b7bf434c941004ff7359210006ff7258630156fc6550d20004fc7654e40007ed7250d21004ff7158042006fb6098143004fd7690850006bc5159020006dc7558c40006fe7058632107bf7150d41007af6450921004fd7218141005ff744ca10007ee424c520006fd73d9121035fe711962002eff638c120006fc65d8543005fd7610a30005fd74d4520007ef7348420016ff6350e1007dfc735524008f7d51195100077d54d4d40006fd4358452004fd7614020005fd7348440006ff315922014efc654c940006fd7458a30006f561d4630157bd6450c50006fc7648530007ef648c9210defd3159232006fe4258630025fe7114120005dd7315132006de7058c20004fd74d8a10037ee414862002df
  | 14 => 0x7f96350210004fc7650d2004efd7158e100047f7559130005fd73d4520005dd73d0850004ff7650c520057d76d4250006fd7258f410077f5454630006fe31d8142005fe7014931005ff7650e10004fd7218153007be7050f41037ec6148620006fd6390a1004eff2158e10006fd7358642066f641d8540006fc7650d510057d7194850026ff614c5200067f3219540017f531d8530017df3258e10005ed728c220007dd435893101fde314c420004fc7654a40006ef6348620106f451d8543005fd7498931006dd7158c20005bc7458121006f47558642007e6424c521004fd7615132004ff7158242005bc70551431177f53d51430277e51d45200047d7694850007ef62c8630005be7408210004fe7690a30046fe31587200047f7558042007787550210006dd634c840004ff7259131007ed635092115dfe758c120004ff7359050005fb7055230007ed6290a3005fde5318143005fd73d04500077d6519543005dd73d0931005fd73c8210004fd74d852007efd3198343007bd4354a400067554584520067f3299742036fe3158620096df3158c50004ff7158342006ed6448620007dc7550d31016ff7358e10005f87055140005fd7198132005fb748c210006fd6450931005ec704c92107eff3158e40015de73d9610006fc10d9132006ff65581430067c3019540006fd7218154004fd7298351006fe6559210006ff54d8d20006fd325845002cfd768c320004fd764c750004ff7458d21007bd5450e40005fd744c8500afdc6358d21005fd7194120005ff744c420217de714c930006ff6114140006ff72d8540004fe764c940004f57118142005ff7654630004fc70595420c7e4414c921005ff7254d100f5fd7114a1006eff5358343006ff7158c40007bd6450a10006fd5318121005f97014a30007f56150630004fd72d8d10006fe75d8520007df7250d31004fd7690a100067c7559131006fe7650d51007f9648c210006fe7558c400fdfd71d4910006fd6198143004fd7690a3021fdc7150d30005ff7358121007dc7550d300067e76195400a77d5399630005fd731512106dfc7355140005ff7158143007f96490210004fd74d8e20004fe7690a10006fe73d8a10005ff7150f20006dd7258f42005dd73102300cedd31d8d210077f7558543037f63148620006fd62d4a100067e2119540005f87050d40007bd43484400047e76195200077f654c520006fc7259131005fd7114230006ff7458a301cfec5150920006fe7650d20005ff7454530004fd71d8d40006fc6118943006ff7650c200077f5354540007ed7298132007f563d05211ffec73486200b6de6350420005fd7118a30006bd64102100cfed218ca100ddfd735093119fef3188120007bd43d4941066ff614c54005dfe7314040005fa7010a10007ed3248440005fc765
  | 15 => 0xc75d8d2114efe654ca100bff531d8543006fc65d8d10007bd5450d4001efe5118121006fd6458532007bd4354640006fe7559121006fd6110230004fc7648540005fd7348520007bd7250d41006ef7258a10165fc7548530006f73158440005dd731093106efd5359130097de6350c5006efc31d8d40006de3158c20006f761485200efbd43d0931066fa10583410077e7550d51006ff3259210007f93290210006fc1058f20007fb514c2200077e51996301177d53d5130094fe70d9630007dd434c720006fc3058742004ff7650f210c7f44158d21006fc6158943006fc3059210247bf3150940005fd7498121004ff7158c400057d75d092101fee3148420006fc53d9120007f56148630005ff7258d41006fc65589430077d531424002efe3058a30006ff6398121006dc7558f42006fc6118143006fd64d4620004f77159543006ff6518121006fc5358910067f96450210086fe31d8143006fd6458931005ff7159132105f67198943057f64158630006df7258f42007f55198121257bf31d0240006fe7650d21175fc754c540006fe7558a30005fd7114140076ff31d9210025fc7150d20007f531181210cef6315863215dfc7550d200ff7f51d4910005be7418a10006fc71d8d40005ff7158a30006ff7359121006fe75d8943037ec514862014efe654c941005fd7390a1015dfc7548520007ef7250e200077c65545200b7bd438c941007f6654c521005df7354530006fc7059131005fc70549210f7ed7219521006fe71d9230004fc7058d21036fe21d8a1006ebd4359230007ee4218121004fc70596420077c7558d41006fd64d8d21107df31d85430d6bd4159321006ff31588401277f53d49101777c7319540006fd64d8e10005ff7150d42047f631d8121086df3158f40006bd4398342005fd7014931007ed648c921005fd7399521077f6214c640007ee65909210afcc634c921006fd764c440006fd64d4e2008f7d51141100077d5314140006fe4318121006fd62d4630006fc5358342006ff6114120007ed75486201b77f534845001efd4118121006ff7259132006fe764c910006fe6458931006f9628c210006fc31d8940004ff7654a30005ff7350620007bd7250f42006f67058642007f9218c120007bd3190140005fd7214210005f573d0521007e9214c220006fd64142300057f7255351004ff7258c50006ff6450e10004fc7650d500dfbd4350a30006fd6348440006fc53d8121006fc7258e100a6fd6399630007bf7458542007e55148620004fe7610a10037fb10d8a1005fbe4318143107df3158543006f76148540007bc7050f42007fa7048530006fc1058a30005ff734875006efd3159230006ed6348620005fd73d0a101affa418c120035fe7150e2001fee2118121006ff63d4910006fd644c520005fd7399610
  | 16 => 0xc620004fd76487500277c51d4520005fd72d9210007ed3248520004fd764c7201befe654c620005f571d9630005fd764c941005f571102100079d434c640006fc1058e42006bd6419210016ff634ca100aefe3058632027ed2158a10176fe6550210004fc7654d1003ff9318c220026fe3158321004fd72d9230004fe764ca10006f561487500077c6554530006de7558f420057e75d8e100f77f51195210067e3119540006fd62142100adff7348630004fd7418131067f6214c540007bd4350450005fd7190850006f761505400addc7358121006ff61d814308eff6148450007ee3298121035fe71942200afee3248630007f9408c210006fd72181530adfd7348530006ed624844006dfc73d4540005fd7650a10005f87054920105ff7158543004fd71d8943006ef6298943005ff764c941006fe7258e10057fb418c210006be648c020004df735952106ffb30592300cfdd31d8d210057c7558141005fd72d8543005fd73195210e5fd719093105edc5358c40005ed721422007efd53d9130026ff7158a10004fd73d8142006ff6458e10006fc1058850076ff3198341005fd74d9630007f9748c2200edfd73d0a30006fc6358a10004ff73587540aede634844005dfe73484400067f6548520005ff7654e10007dd53581430c6fd4158f21006fe6558143156fc7650f52045fe7114320006fd61d8143006ff6114130006fc631812106efc5358343005ff7258630006ff32d8a10006fd75d8d40007e55248510007bc7050d41006ff74d8d40005ff7458d2107efd63d4e40036fe3198321026fd3158a1001dfe718c020006bf6499230006fe764c941006fe6559230005fd7114a30005ef744c921007dd435093107dfe73d9640106fd4359131004fd7650420005f97010a1005efc31181430047e76d5150007fb625021001efd2118121006fe71d8d2008f7f5119510117df3099543005ff734864001efc5158420005fa7010a301577c511954305efe5318143006fd7650420037be4150620005ff7250c5007dfc7354640007bd43d085008f7f51484500fdff7654921006df6350d20006ff74d8520007fb528c110006ff3258742004fd7650d2115f7c7119520007f7424c521006fd7358850006df7358d21006ff3259121004fd7610a10004fd7650e52007f5735051007fbf3150e40004fc7058b5314efc654ca40006ff3158a40004ff7258f51006fc64586301277c65d4d10017f9328c210006ed6248450006fd63d46200b7bd4350530025fc7154d20005ed7390921007fb5350210005fc7059131004fd7650e10006fc75d8d40027f6315812102ffb638c12005ff7314c440006f54358420005fd7310a100077e7319520006ff73d9121006fc30591210f6f63158452006f56148650007bd4350520005f571909410071d5454d43006f
  | 17 => 0x22fbc3190140006fe65d812102fdf3150d20006dd6350c501b5fe7550d21007ef7348620006fd54181430057c7055153056ff41d8e10004fc7058f54005ef7148020004ff7159132004ff7648750006fc7559230006fe6258630006ff74592300057f7154f52005ff7354640006fe51d9130005ff714cb40006fd6310210006fc7558e10006ff63502100077c654c54015dfc758c12006dfe73d8540007ad4350b21004fd71181530fefe10d8951005fc7058d21006fe7558f40004ff7258450006ff6314110105fd7150e10005fc7054540004fc7059721006fd6298141025fc7154920037ee2148620004fe76c8630005ff7348540007fa654c2100cefd72d8d21006f57258440004ff7158c500057f73540500ceff41d8d21005fd731962006dfc7354540237be5390140007dd4354530006fd63d4640006ff31980540057d7519230007be5418143007bf7250d41007fa628c21007efd31d9230006fe6458532006fc5359220004fe70d9132004fc7059121006ff6354940006fd725921008cfe70d9610004fc7655110006fc7650d21004fd7615121004ef7259530006bf6450e20004fd7614a100e6f64158642007bb4250210004fd7648450006bf639014026ff663d0521005f87048520007ef6450921006fe76509311aff8518c120004fc7650e20005dd73142300edef7259132006fc3159120006fd54d8d401b5ff7648450006ff7259230006fc65d8943004fd76507500afed3248530004fd73d8154005f57108210006ff7459210004fc7654540004fc7058f52185fd7650850006fd65181210067e2119520005fe7099131107b62150f411b5fc76d5121006fd7418152006fe5159130004ff7259210005fd7199630007ef6348620006fd72d8e100067f65d8d20005bd7414040006ff5258630006ff621814306dfc73d4940006f9618c220006fe75d8540007ad42485400077f3119520006fe53d85201777f53d4540004fc705875406efc3159230107f46158543037ec2198121026fc31d85200057c7558532007bf7448440005fa70952100afdc6350d2102cff7358d20047f81098a10007f93250210106f621d8543004bf76500400077e7598131007ed43509210057f7550c50006ff5458a300c5ff714ca100057d7510210035fa7018a10004ff7358620006fb628c11001efe4118121005fd72142301c5fd7650450007cf634c9210d7ed3150b21007bd43902100067e6550e4206efe5359230005fe7010931006ff61981431c6fc6550620287be7150d42006be41d9120007de7050d31006fd7650c50005fd73484501affa718c120006fe7650e1006efe53d8d40007f8658c110006fd7558a10004fd7615131006fd6298143005fd73196400075d5350c50006fd6350450006fd764c520007ed744c921005fd7114020006ff644
  | 18 => 0xd43d4640186fe6550a30066fd3158341006f5614c450047ee21d8121006fc6458d210067c30997420fdff71d4910006fe7159132004fd71d8e20006fc63d8520005ef7250c20006fc6198a30006fc7558d21006fe7559131006ff6398a10005fd718c120006fc7059132115fd73d5230006fe5358a10004ff7259050026fc3158a10156fc6550d10006dd435863207efc5358e40006fd64552301b77c65d5121107bf4150e10086fa30d8143006ff6354540007be7050f42004fc7655120006ff75d8d40006fd635894114f7f544cb5101ef410584200ddbd73d0d420067f6599630004fd7610a30006bd6490230005f57110230004fd7398354006fe65581210fdef7259521006fd72d8d400077b755021006eff6350d40007f9748c11015f7c65d4520006ef62485501ffef3248620006fd62d46400055d73152500dfdf3158943005ff7150f50006fc3059050004fe7615210005fd73d8a100d7ed2150a1015f7c65d4d20005ee708c921006ff3258440006fc71d8943005fd7118143017fb634c210006f67058420007f53148620006ff54d8d21004fd73d8542007f8754c21007fbe4398143187ed6250850077f93190110156fe7650c500057e7590a1025fbc1050e4007fbf5350e40007bc7550f42006ff31d89401cfee3150920006fd53d81210057e75d8630036fd614c620007df6358d2116ff85350210004fc7058b510067e6550420004fe76d0a301079f4150d31006ed72d8e200df9f3150d420b79c3250d41007f573841100cff631d8d21006f7634851000efe32586300057c755913107fde5398143007ed7250f211b5fe75d9121004df73589100067c6119520006ff63505201b6fc654862008f7f5114110007f1418c110007bd42d4540006fc3058440004fd74d8532006fd6558143007fa7050d10005f97010a30005fd744c750007bf7250f41005bf7454640007f97050e10095ff7314130006bd43d8941005fc7054d21105ff7150e1005fdf3118143006dd7258c54007df7050d310067c3019520005f57110931006ff5358a400075c6554d43036fe31d8a10006ff3198342036fd31d8910006fc76485400047d75d8e10007ed72981210067f3219520026fa1058321006be3159020007f4544c521004ff7650f50006dd634c8500d7ef31509210efbf7250f42004fe7694a10006fe7058452004ff7158f42004fd74181521ffec3048620007ed3248450004fc7059521006f75358440005fc7050d52007bf64d0e1006dfd76d02300d5fd7490931004fd72d8530005fe70d4d40006ff7650e50007bf5350940017da434c21002efe3158d20045ff76482100adde73d0921007bc7550d41006ff70d8d21277ee6350921005fd7650d210067c7059642277ee735092102ff9314c1201b5fe75d81211277f5314110004fe7615121
  | 19 => 0x89411ffec6348620006fd764c64005efc3058c40026ff6154520007f531d8121006fd611423006dfc73d8540006fd63989410077e5399610006fd6358141006ff65d8121106f62158f41004fe70d91311677c65d45301b5fe75d8d21007ef53509210cefe10d8d21096f93018153006fe7458630005fd744c6400d7ed71509210adf571989310efdf31d8943007bd4350941006fd64d4a10006bd6419121105f471595430b5fd7350630006fd7058d21006fd6454630006f561d4420006fd73d8a100077d54d46201b5ff76d4d21006bf64509210067e41994201affa218c120005dd7315121106f631d8543027ee2158121037de314c62006efc70592300073f549521006dfc73d5140005fd72d96100e6f45158642006fe6158132006fd7258f50006fe7058f41006fd6458630006fd7118153007ec644c921006ff7458a101b77c531952105fbf3250c40006ef63c86201b6fc6548540006fd76487500dfbf43509310cfe6318c921097df3150c50005ff7155120107dd3150e10007fb728c12007fbd434ca40005df7359521007f1218c110006ff63485201c7f561504500aede63d8d211777f54d4d40006fc7650d10007ba6490210006fd6114320004fe764c910007be7050d4107ffb30d923008dff7114110006ed6290a30005fd7010931004ff7258f50006fc75591210c7ed714c921006fd63d0850006fe31593200977f5319530057f2418c110006df6350d21005fd7498131006f53258440006df634c920006fd6348450006fd43d8540006fe41d8d20006fd764c840006ed62082101777c7119540007dd714c930046fd614c720157be6450c50007fa758c11005fef324c840007f8658c120005fc7055143005fd73d4910006f5618c020005ff7354540005ff7154e20006fe7158a300047f7558343086fc63d0210006fc31d922002ff9728c12006f7c53d4d40006fe76486300defd4359132006fc6198143007ee52981210067e6548440004ff764865007f9e5350e40004fc7650e10004ff7654630005fb7054a10007bd64d0a30005fd7314220006f56150630007b9439011005efd4318143006fd6348740005ff744c620006fd54d85201bf7f5414931006fd5358910006fc6559230007de31d8d20005fc7058941007bd4350720006fe7558f41004bf7458910007ec654c92106eff31d8d4005fbc3050c40006fd72d85401577e7550f5107fbd4390230005fe70195210057d7510230025fc7119520005fa70c8630007cd438c9210057d7315152005fc7050d51006f96018143004ff7458753006ff3259050006fd7258630004fd76d0e10045fc7150f20006ff6298143006fe7158850006fd52d8520005ff724c440004fe7695210006fd63d4a10006fd70d8543007f8508c110006ff644ca10004fc7654a100047f7558d20007b
  | 20 => 0x37ec51c8620006df7358e10076fd31d9110046fe51d8121087de53d8143007ed21140201befe654c640005fc7054d1003cff768c020005ff724c520237bf3190140007dd43d4530125fe75d8d10006fd7118154036fc315862007dfc7354a40006fe62d854301efe2118121106fe1058f41087be43d8143066ff31d8540006fd74d8e20005ff7448450006fe53586200067e3119520007dd718c130007bd5458143007ee658c9211777f7319540006ff53d89400067c65d8540005ff7454a3007fbc5350e40287be6150d4202fde434c520006fe75d8d21026fe5158910006ff31591200067e7619520116fd30d9153006dd6314020005fd744ca10065ff71502100057f7154c50006dd634c420005df7358121006fc5358a40005fd7198a30007fb644c210025fc71d8d20006fc6458e10007bf5450e40006fd6348210006fe53d8910007fb428c210006fc7558420105dd7399131036fc31d8910007ed5298121006fd6254a10006fc5158242006fc54d8d211aff8618c12010fbd7419543005fd7308210007f55118121006dd6350e420befd32d8543006fc6558d21006fe7559132026ff31d85200afdc7348630006fd7259230005fc7059521036fd3198321004ff7650e52007ed42486300c5ff714cb41005ff714c9400077c3119540037ee314862008ef661140200057e7590a300cedf31d8d21004fd7650720006de7558c4006eff3159230005f57198943004fe76d0a10006fd5458a10005f571149311bdfc75509310077d52d46200e6fd31d912102cfd72d8d20006fe73d9121026f621d852005eff3258c40006f45358440247bc5350940066f621d8540004fd7650c5217ffa4390210006fe4218131056f64158630024fd76c8210006fc735921008efd2118151025fc718c120095fd73d0c500067d6454450016fd638ca10004ff7650d21085ff7650230005ed748c921004fd74d8530006ff764875007eff3198343086fd31d814310fdf3119543057f621586300076552545210067d62d4650005f970c8630006fc5159130007bd5190140107d62150d31004fc70584520b6fd32591310d7e63150921007bc7550f41004fe764c5200befe30d85430eedf3158f4207efc31d9230007d9638c210056fb618c1100077e5319540006fd7648450005ff73502100057f7548450004ff7650f20007dd434c750006fe6399210006fd43d8520125fe7550d10076fb6190110007b54350510006ff3218141006dd7158c5405eff3118143005ff714ca400afe6324c52107efe53d9230107bd7150d41007fb718c1200067c65d8d4001fed3148420005fc7059121004ff7158a3006efd435923002fee3258a30006fd7358420006fd6350921005ff7150e40007f87048520067f931501100067c1099642005fd7119230005fd7615121004fd73d
  | 21 => 0xd71d91210afde63d8d21007dd434c640006f56148630007bf6550e400077d5314220004fd7650f21186fc6550a30006fc51d8d20006fc1058c20004ff73584500077c6554d100079d438c941005fd71d51300cfed418c9210aefd6350d21156fc6550d21006fd4358a10007e9428c120004ff7650e10016df3258e101b77e6519521005fd7114220007f8428c210006fc65d9121006ff6454a30006fe7458c50005fc704c9410067f52d8550006fd6314210006bf6499121005bd7418a30006fc31d8142006ff63d45400aff7434c5211c6fc6550520006ec3058840006fd7650720006ff6455230006fd63585420077e6554a1003ff9438c220115bf74595430cdfd718c941085fe7314340006ff63d0a100077f654c540006fc65d8143005fd71d8e20005ed72d0d21006fd4358642007bb4390210066fb6150110006fe7358a10006fe70d8943006ff63d0921006ff3218121006ff6350620004fd71d8d200073f5495230006bf6450d10007ec7548420066ff7159210007fb748c110287be4150d42007ec624863008df67190850006ff631812110dfe7599543155ff7650c50006fc73d8520006fe7458d21025ff7148210007bf6450921005ff70509310077e6555210005ff7150d40007bd4398941006fd62506300edfe7618943006ef62d4930026fd5158a100e6fd72d91210067c654c5401b5fc7558121005bf745812109ef62158750006fb628c210005fd748c210007bd43509210bfbd43d0630006fc6358121007bf424c540006dd6348440005fd76109310067d6514230006fd7358a10006fc7058f4106eff63d4d40067bf4159210006fd6454a30005fc7058543007e53248510005ff7158132006fc51d91300057f7254f51006ff62d4540057fb638c110004ff7359121026fd3158321007f9718c220005ed744c921005fd72d523001efe3158420006fc5158232007ee42d452000efd3058630006f7735842008ef66114040004fd7695121005dd73d0a10004fc7059632035fe718c220006ef6248540054ff71d8d100ccff7358d21057f9418c21008efd6148450005f7715512109cff7654210006fc63d8121004fd7418132007be5498143005be7095143006f77159131006ff6558121006f77458452004ff7458720005fd744c540006fd764cb40007dd518c130016fd43d85300077d5348450006fc6159230006fd7458452005fd7348740004fd761493104efd634c210005fd7419521016dc3058e10006ed634842015f7c53195200077d53d4910007ed424c921006fd4358750006bd6450a10005fd71d81430067c611954004fdd3158e10005fd7314110006ed62908500bfbd434cb41005fd7399210004fd73d9121004ff7358720007ee32181210057e75d0931006df7158c4006ff83059230005ff744c9411b7f56148450
  | 22 => 0x8d10006fd64d4d20004fd73181420077c7550e50007ed424c520006ff6310a10005fd76d0a10056f45158630007dd434c5400aff7634c521006fc1059230004ff71591300077c755893114dfd764c850004ff7655121007bf7150c40046fc51d8121006bf649921009f7d5199610006fe3159020005fd744c420005df73486300afed434c921005fd76486300ddfd7350a30006ff6454630066fd315911006cfd76d0230006ff53d8520004fe70d853204eff7158e10007ef5248620005ff7358141006bf63d0940006fe70d854315dfc7550520007ed2194220006ef6188120057f9218c21001efd721812108efd1018151006fc75d8d1006eff5359230006fe6458d2100eff6350d10007f57348510007ef6390921005ff7650d210057c7558d21005ff7150230006fe4158a30007d77150d3107f9f3150e4001fec2118121007f77150e10007bf7050d410077d71d9520006bf6450d50004fd764c420036fd31d8a10006fd6414210006bd644c420006ff31d9220007bd6419121056fd41d8e10005fd744cb51005ff735894104dff714c210006ff6458630005ff7250e100079d4350530004f571d9630096de4358c50077f92190210155fe75d8943004ff7159050025ff7154520006dd63d4f42005fc7654d10007f8758c110006bd6450e5202ffa318c12009dfd71d4210007bd43d0a100067d65195430057d7114a500077f65d4520006fd65d812125fbe7150e400afd6434c521006fd6350720086fc31d8143007ed62189430057c75581430067d6514020006ff6458d21006fd7258450005fd71d9520006fe7558e10006fc6359210007f475485100067f7559131005fd7299610007de7250d31006fd65581211c6fc655053006dfc7319540006ff53d85400d6fd3159121004fe7650d20006fe64586301c7bd6450450005fd718c32017ffa6390210004ff7650c200079d43d0931007f77158d410cfdf31d8d2106dff7350230096fd63d0c50056fd71d8d10004fd71d91320cefd41d8d21005fd739424006dfc7354940006de7158c20005fb7350110277ec5350921066fd3159210155fe75d8543007ed6290a10006fe41d9132005ff7650931007f53158121005fc7654d20007ed324874014efc654c9100addc7359521006fc1059132006df63d4d21007ed5388120007df6350d21006fe65d8d21006fe6319121026ff3158a10027ef2158a10004fd76d0931006fd7258c40006ff74d8d10004fd73d8152006ef3258840004ff7654d21006ed62c84500dfdf3150d42006fc10d8d40006f6755864202efd634c520007f86550210207ee3150b200077e7119520004ff72586300067d651421016ffa4350210006fc7159132006fc75d8543006fc61d814307fdf3198143007ed7348420006fe3158b50004ff7359110006ff76486500e6f
  | 23 => 0x6ef6298a3008dfd7114110005fd7390941036ff31d89100067f65d8d40015de7318a10096ff6350c5006efd32592300067d64d4e501079d4150d3102ede43d8d20006fe6118943056dd31d8d10006fc75d85400077d531411000ff9438c11015f7f52d4520005ff7458131004fc7059541006ff72d8d200077d5114130005dd73d09320eefd74d8943004fe7650d21007be6450d21006fc65d8d200057c7054951005fd73487501b6fc6548530007bd435075016ffa6350210006ff7258c4006efc53d8d40005fd7199132007cd32485300057e75192300dded7299132004ff7158f50004fd73d8520005fc7059543045fc718c3201177d53d5230005ef7250e20007e9218c220006fd6250450004fd74d8d20005ff7359121087f83099230005ff72552100067c31195400cdff7358d21026ed2158a10004ff7158252005fd7448450056fd21d8e10006fc51d912014fed624c850006ff618c12002efd72d8d2001efe31181211bf7f524c750004fd7318154005fe7615121006fd7359050165fc75505300077f3119540036fd6154620026fc5158910005f9748c110287bc5150d42026fc10d85200077f5194120006fc53d8940006ed7358840006fe43d9210004fc7655121005f571d09211b6fc6548640006fc6558630057f9718c110006fd73d854015f7f7119520007fb524c210006fe4118132004fd7650a10006fc7558f41046ef76484200077d73d95401bfdd634c450006bd4358742007f6704c521004fe7650d51006fd64d4520074ff71d91100077d5114120006fd3258740006ff71d8d20006fe4158f20005fd769512106efe3059230005fd73d9121004fc76546300befd634cb4107eff31d9230006fe655863027fde7150e3207efd43d9230006bd6450d21006fd32d8540006fd62486301b5ff76d5121006df634c921004fe70d8d21036fd51d8910004ff7358750007ef644c921004ff7654e10086fe53d814305ff93018143006fd644c750076fd31980400c5fd714ca10004fe70d8d410057d7395050005fe76d4520006fc51d8930007ef6548620037f6214c620006fd6358a10005fd71d0230006ff6348620005fd7119640007f5704c521006fe70591321577c7550f52026fe1058a100047f7558910004fd764c840004fc7058f510057c7558543026ff61d4520165fc76d453006eff634c9400bdfd73d06301b6fc6548520005ff745463013ff65348510006fd64d46300077c6554540006fe41d8e200077f6599543107bd4150e10005fd74d4a100077f7548450004fc7650d5105efd3218143006ff72d8520004fc7654e20005ff7150c20004ff71588500067d65195210e5fd7190a10006bd6414020005dd73d0a30006fe75d8d20004fd74d8931005f9701521009e7f7654450057f63158630006fd4258630056f621d
  | 24 => 0xf70d8543004ff7159220007bd7150c40004ff7359120077f4314c6400067d6354450006fd3258750006ff72d8530004ff73580420067f3299440006ff74d8530104ff7159131007df7550d3002eee3258a30037ed3148620026ff5158a10006bf64d0e10006fc70d9121006fd71d8d2015dfe754c520006fe61d8a30005fd71d962000efd4358630004fc7058b54006fd6350a100dfde435093106efc6350210005fc70589430067c3099440044ff7648210005f57114210005ed72192100067c65d8520007dd32d4530007bd64d0a1007fbf434c6400077c6554640007ee644c921004fc7654940066fd644c640004ff7158f5210edc3058c540a6fd6350f50007f77150f510e6f63158642004fd764c450007ee5218121004fc7654e10066ff31583410afd4634c52107fbe4350e40027f63148520005ff7458a10006fc7559131005fd7298141085fe7348740006fe7650d10007e5424c521005fd73d0921004fd764cb40007ad43509200057e7519210006fd6398121007bd43581410067c654c520006bd6450f20007ed6250a300efbd43d0a30104fd7699131006fc70586420057f7154050006fe4158e420bdf77159131004fe70d9521007df63d4d21016fe30d8530006fd624845007efd6354e40006fe6258543005fd7199230026fc1058a100067f65d8540007be7550d42005ff7250f51006fd4358720006fd764cb41007bf7458941006fe6398141006ff7258a10004fe7694140005fc764c540006fc75d8530004ff7158e20005fd71d4230007ef7258d420fff71099521005fd7298131006f773586420077c6554d20086ff3258f40006bd64d0a3007f7c5354e40007bf6499121007f07048510006be7159020006ff5358a10006fc53d85400067d651963007fbd5350e40007f1718c210006bd6450850007ee7250d211677f52d4530006fe21d8d20006fc6559121005bf7448640004fd72d85430c7ed214ca10006ff7159230077fb3190110007dd7318143006fd6458d21006fe3118142006ef6448620006ed628821004ef631d8530036ff3158620006fe415885007ebd4398040006ff7558a10004fd72d9210006ff6490931087f7314c740057f2218c110006ff7458420006bf7459121004ef764802005efd741814321fde7150d30007bf7550e40006fd63c8210007fa648c210086fc3058f40006f47058420006fd6158132005f87054a10006fd61d0230006bd6450f50005fd7319610007bd4358941006fc625863005fbf7418143005ff7154a20056fe10d8d10107f410d8543006fd644c720005fd7394140004fd73d81211079f3150f41006fe5158e40006fd7458642197ee5188120087df31d8143007fa7048630006fe73d9210005ff7654d21006fd6458a10006fd32d8520006fc10d8943007ac7250d42067f92150210
  | 25 => 0x9131005ff7259230006f77358452006f56148440006fd63d0210087f830d0230007b77150d41006f57458420006dd6350c200c7e6314c921005fd73d421005fbd434c44001efd614c4200a7df3150f500b7df3058543006fd7218143005fe70d8943007f551581210d5ff7150931006fe7359121004fc7650d21007be7250d4106f7c5354d40037ee31c8620006ef32d8940004ff7258750007f8504c210076fd21d92100077e5119520045fd71c82100057d754c45007dfe73142401eff8514c220287be2150d4208ff631484501777c65d4d40004fd7690931025fe7150d20086ff31d8143006fc6198943067fb3150110007ef7448420006fe63d9210007df634c921006ff74d8d20006fe63d91210047d75d813107efe31d9130005ff7350520007bd7250c40006ff73d8540006bd4358440016fd32d8530025fe7119520106f66150c20005fc7654530006fd624ca10005fc704c520007ed3298121006fd70d8d210975e4354c50006fe6558543006fe3158242007af7250d420d5ed74909210067f6514140004ff7158d20015de731521006fbf4359230037f65198121277ee43509210b7bd434c941006fd71588500077c6554e10006df6350d400047f7559110006fd7118152006ff63d8121005fe70d8d21036ed21d8910006ff71d8d40007df73486300057e7598941017db324c2100eedc5358f42006fe61181430077d651952109efd61996100057f7558121006fd644c450006ff54d85200067d75d8e10006fc5359120007f55384110006dd6350e50176fe6550230037e65148620007755148450007ed644c921007ed4348420006f571d8e10067bd41592100057c7054b511b7ee6248450057fb618c110005fd73d9210005fd73d964001dfe71140200047f7558a40107df3150e10006ff7158f42006ff7259131007ed42181210057e7599121006ff7458e10005fd76d0630007ed704c921005ff7654a10004fd73d8a10006fd71d8e20006fe64d8e10005ff7458e100adfd7348630005ff7348620005fd7348640006f56150420006ff7458630007ee6550921006fe74d8e1005fbc7050c40004ff7458f5006efe3159130004bf74595100b6ff638c941004ff7258c401b6fc7648450006fc5158a30006fc53d8520006fe7650d50025fc71d4d20036fc31d8a10006ff6250931006ff31d814210edf3258c5406efc5359230084ff765023004ff631485301b77f54d4d21006fe7318121007be7550e40007ed3248750007dd434c420056f62158630006fd64d52300067f5318152004fd7650c50006fe53d8a10005ff7050d51004fe7650e100057c7054d51006fd628c2100c5ff714c9410b7bd4350630007f87550210005fd7190a30006ef6298a10006fc61d8d2001dfa70d8a10004ff7358a40007bd4350640004fd7418151006f
  | 26 => 0x6cff7359130006fd624c75008efd61c8450005fd7319121006fe425845024fbf31d094002ff9318c1200f7f63119521006fd74d8d20007af4350921157dd731954307efd32d9230016fd6350e10006bf64d51101577c7550c5005edf3258c40004fd76d0450006ff7258f41006ff5458d21006ff6254a100977d5319530006fd6318a10006ff624c941005f57118a30007ed7348620006fe70d9121106ff6150d1004fdf3158e101cfec3150920006ff54d8d40007bd7550e40036fd61d4620006ee7358840005be7418a30006fc5158e40006fc5358a10006fd61d423001fed210821005efe63102100977f531413005efd634c440036ff51d8910006fd71d8d40007bf7448640175fc754854015f7f511412018fee3148020006ff5458a10076ff31d9110006fc7648550007f9728c210036fe3198020006fd7418121007dd5318143004fd7118143006ff7158a30006fd7158c5004ffb714c210005fd7399121006ff7650c50005f97095210005fd7348540025fe71d8d20005f9744c2100057e7590941006fc7558720005fb748c110007fa60181430c6ff4158d21005fd73140401b7f571195210077d7119540005ed744cb21006f5435845200eff634c910004fc7058f42006f57358642007fb5390110005fd73d9540037dc314c620006fe6158a30006fe7558630007be7550f41006ed628c850006fe7650630007ec7548620055ff718c110006ff5358620106f66150e42006bd43d8542007f57118121004fd7118152106df3158f41007bd4350540005dd73d9610007ed424c72005edc3058c40006fd7258e1002fdc31d8d20006ff61581430067d6548440007bd434864001ef641584201bf7f504c450004fd76d0d21005fd764ca10005fe7650d21007f5744c521007dd6350e100067f7558d21007fb514c120007bd4314040006fe764c54015f7f5314120175fc7550d40017fb438c210156fe7650f52006fe6158943006bd6490210004ff7650e50004fd764c740006fe75584200afed3248630165fe75d8530007746554521055fd718c210007f531484400bfdf30d8543006fa70d8a10006ff651814308ef41058450004fc7648550005ff7250630006ff53d891025fbe4150e400f5ee7694921007ed3248640005fd74d8e10007bf6459121006fe639912113ff67348510006fc5159220006bd6450c50005fc7655121006ff54d8530004ff74584200e6bf41d912105efc7058c40067f431d854006fbe4350d40006fc7558f40005fd7015131047ed2198a10007ed5218121004fe7614a30006ff6358121006fd61581430aedc53d8d2125fbe5150e40006fe65d85431befe654c520056ff638c110007ed21142200057d7195050006fe7058f42006fc7458630004ff7458450006fc5158e200b5ff7350530006fd6114020006fe725
  | 27 => 0xc00206202800600200040060cb801001400b003c00000000f803400e00900a04b8002007098800c040003005005802000500c808403a11d145800800001b001000c00e012000002c00200400000c806a00005f019c00003f000800407000201000c800a00b010002007600000200480000010000000014036050000c000013009808403e000058800000800901c800400203e02080b00580fd00000300140040000014002001000800400000300e00280e804503f81280ee00b0098088026000000800801c021004001c0a803d00e80c000000000007d801c00100900a800000d00000149aa00400083540020040bd007c03e0cd035801003a001006800400a004004002c0bc005002800015200800e012c11a000000800400a0040b9800008600205a806800c03a00180a400c015004800015a030036fd51d8a10066bf41592101b5fc7559121096de6314020006ff7358a10007ed32485400077f31d9540006fe75d8530107f661d85430057d7195352005ff724c740005fd7419610007ef62589430067e41996420c7ef414c921005fd744c620006fe75d8d40006cd6348420155fe7518143007b87050e400afce438c921007bc7550c40007ef7250e42107f47150e10004ff7358321004ff73586420dcfd7650932106fd74d8543006fe61d8943006fd6450e10046fd61d4720004fe70d8941175fc76d4d40007fb618c120006ee42d8520004fe70d8931005ff76552300067e3199420007de7550d310067d6550c20006ff72d8d40046f63158720006fe2158a3005cfe70d92300067c6550d40005fc7654520016ff63d0e10007f75350510006fd72591311b5fe75981211777c65d4540005ff7655121005f57115121007f551d8121037ec3148620007f8508c12001ffa101812107fdf3150e400aeff63d0d2115dfe75485200cefd10d8d21105ff7150d21107d47150d310c7f63158d2106eff6354d400057d7394850005ed71c8220057f66150630005ff765521006dfe73141401ffee534862011ff67384110007bf7250c400aede4358632007f9624c210006fd7258f40076fd614c640006fd644c420025fe7194120004ff7258c54007ad4350b20046fc1058720005fe70d9521004ff73586400e6ff31d9121006fd631404006efe43d8d400057f735445005dfc7348440005f57114a10006bd4318141007de7550d30005fd73d8640007bd6450d210afdc53d8d21006fd7159230006fe3198242004fc7648630007f9748c1200e6fe10d9121005fd73d81211677f5114130006ff5358341006fd7458c50006fd54d8a10005fd72d4620005fb744c2100067f54d8d50006fd7158c40105fd7150d2115dfc76d4520027be4150520005f771581430067c3119520005dd7308210004fe76d0d2102efe31d8d200067f3119540007ed4298121
  | 28 => 0x101100e40120070130414000000127003000200000a81dc036008005805006e002013000000c00000000a019e002000076002600000e802810c0060020010000004006006000005f00001b803403a06b002802400904302a0000001000017c02200000108a001a003005803800000300b803c03c00602500a001600600e8000002018002800427c04101d830002e0000050020032000030801000601b000800401001a00080280000310429ce001404f020809c000005002802004600c1868708090007003801c002000056009400000000c006806608501a81b0020000019049001601d0098348000023019000c03802a092003c0161e8000800400a000008020000c0040040064000004002000006600100100b402e050000811c24c002013025000201600000b40240b5005831418a00000000040120040078048052000024802c1600010020010016002013804c37c00c001803c03c00200e002c05e0350000000000052007803400800300201180da08000107a402e003000003c01c2c0006804804000801280400060000078080052005000803000807f0010064024000000006401600200203d812800d003000c06203f000001400001d00200040cc0060018100010000016803400c00700b802802c00201f803003400001480380d4005045000037e000001000405e00000e002c02c002078027c02e009030078002200003302e0050003000000004c00a0000024428000035800c00a000000008401a02000300000a2000005004000000e05f8000030024014011c0e40000000004058006000805800e008001001001202e0e5819969a00602f000000005d00200000a60d002400080020c300d000007a07e053800800a003029802c00201e01c800c0060130138054008035005800c0a80000098054036018000008c0020320078000012000005053c01603100080000000af013004408205600f00bc01201906c8028064008002800000001b000800002206c000803801c001000015c08200b00001c007884c006809000c0000490004010000010001000200d001003800000700102e800004200080480000b10208d400020e0025800400000400001c000001a00c83c802a0980060024000002003006802e00002f8024102000000810800a0030028230000020007002c0240020290030000017005801c0060500eb802403802500c80000000070008028006004026026803417a00200184340030240000036001001800000c002000001400004e00500d402e0030028190bd4010006800404a015024800c004089062025802c0110008024000049005001c002046012802c01a00004a017c00c003000000003000800700740c202d000802401803600c00f403a019004035c000000001003c04c0000038274016013000003800200302a0
  | 29 => 0x803800e002002813409800f00e801001000c0000068064008015010c00600f00d000098400f001000401600200880bc01400000a0004020003052000401e028000835c0a600000a80880c60040018000052ec40000000124000035800c008001000800c064019000001c15c00a00080f001200000a008c02404f01703e80220000070000024007000000000015600201a4054005006013002221800004240a81750028024010007006828c0c2000015000810409800200100901a500c000000000301c80080044f7000006400e00500500cc00200200c000000403100a01f401e0240080104012001005017c000000000802402a01400300d0010000000806400204b006000454e208000800000000308d005000202300000441361b0006806005a0090218024014008001001017a032022031011600900180040d6009034801c00001c00000840100070038058012000001000c00a02c006800404008f01880140120080000000054085097002400000100100cc018002000000000000901d001824e00c01280440cc000013002001600001a00b800205600a8c0003a00c004800406800c00101500080110008728042006000000c00000100006f800001f00280000221c2002001c02a05b00480d00e00020000080006008009000811a007056801c01000d000004c01400000500d80000620160064006000003000c0000270058000008000001014c2ec00202b000005e001000800c018094040806c00400100000000da00000601980440120010520004004000000401803b001000c03800b029800803a001002000890600400280080e80210018df80000052af00fc010000008000006e000026006000000000701140060000000010068130000002410a02e001001806e005001807801412802e00b801007201e017401401a00d0018000002004807c0780130000000000006000000000e01c0038000044009002002000400200c014800000e025800400034801780e400800a004001400200100101c000804a039800405400000000540083d600680040f200013680000da14e000000000e005033800000600000380001360320060070000000000801007400903c810c00000c011930406401e008800000003e000801400003200b00000b2041000009075201d005001819200b00000900524e800d085000001e01a80c40ba00201680b404a0500030000640006017802c194010000001000200004e800000002600e80000000680010848002000004801803c006001805801c0510108020004025000996c0a2043003002c000002000801c00416406800000320960020000000007000004405a05c000804000600a000005800009e7ea80180c0164064020c0480020018028000003011811000400101d80dc02201b00100200040020000000060
  | 30 => 0x3480ec02802f06800000f800f00600bc0000000b980b802c04100000001b400200280300300000a7804000600902380000bc00105c804008c04900d00ac0520001c400800020bb00182ac004000017807802206201900d41200080b4005800403e0028060012003009802c00a00b00100cc00e00800580200e8000003069007e00000e00000780020008058b0800106d8004000000005800802e01e015800002000204d80ac09400200701b00c809d028859002800a00980c819c9c8002000000601900a800000205b20e805011400100d801c03833b04800843ee043001
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xcdf835d931c80015f50129ac488003b550d614c4500047ec30e0aa24200cbd7419363484a5dca64b0a4318003375cf32181410066e98ae7b142000aed820c764880011fd0db8a86a00029f60c10994200047ec36e2a184000af880585604c8018fccbb9a82100033d5d1614863024d5ec24e1b1286009f8805d932504cdd6a86b0a83180031f5d572d8e10006d721ee4b028672be78350931484011fb0f316c2a18023f61270d8931035f3408ca90c4000e9f3159143d4001af0ebb9a810800337cc47650d100067ab88e2b226400bad821c14350801d3ac6a1a8210003379c563140200057ac3a86b0c84008fe8714564480011fb073b0a908002ab6103058840004f6c0ee4a1c8400dd781dcd6048401ced0232ec2a00032f5d943d045000576c14c23146000c7d761d543940011fd0fb1a42a0003374c77650e101b63ec38ca90a8000cde865cf42484014fb02184ca200da9fe1d65195210043fc3aca32a420dafa809c5648c0015ef06ba2c2290023f61f32592100865fc3a863028200be98748630880015db0520ac72100337cc573d85200057641ae2b108000cdd738c460508013df04b9ea3100029f61663d8a10005f9c0a8720420008fd8794c60484013bf0ea8c6098002b76047058f420067690ae5b242000cdf74dcd63484015eb0239ec2a0002bea0051591300073a30e6232a80008ff8750c60548eb97ae2b2287908033b1c96158143006eb29ee2b028600ead4350961c8001e3aa8a9ec0a18039718e31195202f66eb8ac6a1c2000cf9109c36150c0197ae8b24c090802bbe09764c54031f7318ec490a6000af581d91418c0019bb0fb1a8690802bd21d43586420067ab88c3b1a4000c7c65dcd21500019be63b9ac3100027760f765093100757c0a86b108000abd8414d64440019bac7b8a86280037348573082100066eb9ac7904203fee5634c5218809b9eac7b8a8690802ed60f64d05210057ac3a64b088055cf9615c3218c0014ff0ab0ac0a18031f9977150c200047fc12e7b24200dcde73d8e50500019dce6b9ac4200033d5c66118a303de76b1ee4a1a84008fd849d943840c79dae7b1242980a797a0c654c9400073a32aa3b024200e9d4358931100017cf02a1c84908f3798c571c82200053e42ac6b0242008fd81dcd62900019ea62b96c2980035d184755854300657b9ac4a008055afa801cf61480015eb03392c898802afe19439021023fd490a84a0420009df835c7544c0015f501996c2900039790c654c54000677bb6c490c6000bd8805d5434c001bcae2908a0100035d9d77150f5113ff0992431822000ed673cc7615000175f04b8a86a1002ed6047050d4137edd086e890c8000cb574584501000197ced3228690802afe0d64192100065fc3ac9a142000e1d5458d43d40018f8eab92c898802b760e7558e10
  | 1 => 0xe65b92c9180023fa1f62586300056ec1820b184000ee96290a30840019eee8b0a43180029fa1831195400047ec0ced21460008ff8758d21100015df06b8ac420003765d1638c2100066e98ee6b224200cf653dc5644c05d8fcebb2ec6a0002ede057050d413367bb9ac2a0c60008fd874cb61500015bf02b1a87a80df9d21573584520065fc3ac9a1a42009fa87d8940840018faea3aac9180023f60f71592200047ec0ee6b244000cdc7158d430801b5790caa2c0a1802faa0365486200056ec18ebb1a4200af98690a30840015ef02a1ac210057f1207634c9210047ec38a6b1420008fe87145648c0011fb073b085080023f6077458c500059e42ae2a188000e9f6450d31880011fb05b9ac908002bb6083158a400053fc0aa6b10a000add819c163d08558fceab2cc0a1803c75515398143006ddc22e91822000bd584d8d31484013eb0238286a8802bd60442586300053f428c3b028630e6f535894214001f32c6a1c81080033b5c94218131004bf438caa8c6000ed7715c563100015eb0339ac890802bde0d74584200065fa8ee8b122000c7d751d761480019ba62bb287908023f6077258f500065f28ee8b1220008fd84dc963840015db0428ec498002bbe09764cb400065f3a2c63142000cf7645c6424c4019df04bb243180032f5d943484400047ec0ee4b1880089ee861c152484019bac7b8a8610003c71955350e400055ec20e4b1c2000e5d83d9763500019bf06bb48498803b58c573584200067ab8ec23028600cbd7450c6054801f330638287200023f61d43d8a10006da388e0a1a8200eb54358541080015f50121ec290002af610631912125fcd98a872042000ead828c564080019eae2308c0a18032b59371480200056f406e2b1e8403cf671584500800159b0538ac6100023f60b7458450006b7190eab1a42008fe878c564480019de43b92c318002ee2015450d4000766b1a64908a000cef8758862840011fb0f20ec690002af61332590501571ec20caa1a8000d76311d560484015f10ca1a81080023f61c53591210074ec1ac89884000e6c654c9215000197aeca1a83a8002b760c10d894313eea39ae690a2000e5e4319531480018f8cab8ec6a00033bdcd6248450005aec1ca232a8600fe1511c121880011ff0eb188508002af61943504500057cc0084b0c6000cde87d8f53484015e902b2ec0a193b798c5748c92113dea41aea90a2000e5c6550d31480111ff0cb94610800337dcc31591200067ab886230284008ff845cf614806fcbd0632a62a00023fe1d43d85200057b4326290a40008ff845d943840011ff06bb2422018f794c6708c9210047ec3ac898ea000abd849d943484019bf06bb243180432fe1d43181420056ec0ee4b18a800cbd64dc94314001a78eaa1ac0a0802b7e0d644c92100576c10a2b244000
  | 2 => 0xb7159050034f6c16e690c4000a7e851cd64484014fb09188ca900035dc407558d21026f2b92633024200cbd43dc5629006d1fb0eb1242280029fa1671592300047fc3a86302422aa7e859d943840013eb0e2a26290802bea0051d91300067bc36e2b028600dd7315c46050c0197a83bb287908033ddc4615814300576432a7102402cc7d639d7618c001d5c62b2242100037550d7114931005ebc0ae4a1a6200cbc7458d60484014f90ab8ac8990037c5d470485103cfca196e2a1a82008ff865cd21d00018fcedb2a62a00033b1da7250d210055f420c4b0c606acbd73593428c0019dee5312c3180029fa167558d211b73ac08ca90a4000cee32dc5628c0011fb073b26290002bb60b64509310066eb9ac62042000e7621195315005dab8a6b98caa00033be1d6218a301b7b2b0ca4908a0008fd87043644c86d1fb0fb2ec090803b3dc97258c400047ec3ac89942000cdd731cd6448453cbea2b1a64280027d6077250d210047ec38a7b224236d76811d560484019eb033b262900033de1971908500056ec18e9b1a4200aed821476250c1b5bd0630ec6a00036b5d142181210047fc22e3b1a4000cdf7398d605040197a83ba2c6908127b60a70d95210074eaa6c6a1a8000cbf7454d62440019dce7b1242a00027be097650d213c74fa0ec6a1a4200cf586dc543840011fb03bb286290033b58e721021000576c10a3b128074fc441d8d324846dadd0e32aa4908033d21d61506300074ea1ac498c80008ff835cb61500f7b5ae9b14c4a1803ab50d71588400067690aed1942000a7a8088465480015e902b2cc0a180ebd20543584200047f43c82b146000e5c75d8d43548019bae7b1ca0a0002af61943504200047ec1ced21420008fd83dc964840011fb0eb1265080023fe1d6450d21006663b26490a6000add8704163080011ff0eb1c85080023f61d644c4200457643265b024200cdf7350d61c80015db04082c6100123f61c30d85201578ec18caaa286108ff865cf4084001bcae290ca110003375cc63181210047fc3ac5b0c6000add828c763480015bb063aac9180033b60a76485300047f438a3b128600eda861c1434c00157b0ca1a85080032f5db64d0e100056ec1ce8b1a4200be9819ca30880019bee6b1a8210002eb61062486300057ac0eebb0a402af1d639514314001dcc63b1242a00031fd96709954304773bb2629084000eb48050d61100019e906b88c0a10038f19543505400075dc3287204206dbb9849806050c015790ca1a84908de9f215764c7400076bb8ae2b1e84008fd82dcd61d40018fceab24849880375d8f7150d210066ec32e7a10a000be68090931484019b902b98c0a108ae7e117550d300047ec38a3b028600ced7458921140099ece2b10a1080023f61e64d8e100076698ac69084000cbf74dcd64840019d
  | 3 => 0x8a126200a7e8599363484018f8eab22c299003375ce639912100677b94c2b028600aed829d93250001e38eaaa28698002be61f609812117edca1ee89842000adf845c56308001dcc62b2242101573ed8570c863038ef4b96c13024200cf7711c1644c40156b0939ac2200031f1d76258543004fd43ec6a042000a7e859d363484015eb03382c8988033bdd16248450004f6c20e09924200cf571907644c8011fd0f98ac910003ab61d435884000766b1ce09084000a7e850c56448087f3282a1a6108003795cb7150d211569e3aaa8b028600bad8499542484014f500188caa00039d99531484400066eba2c6990a04bebb6150e404409776902baa8720002b76047058c400047fc0aec9908000cf573cc761500019bac7b928708002afe197250c40005bd404e232a8000c7f655c763480013f70cba26108002bb60a7559132006dcbaee0a1c8000af781591514c0019eee398ac828002cfa167250d410047ec3e623028400c7f751c163484019bae6b1a4220003b3dcd634842000772a12c2908a000dd4719c9434c4011ff0cb868498803735cd3298121006ba32ee2aa24200c7e7558c20840015ef02a1ac5080023f61372584500047ec0ee4b20a000e9d6350f4214001d6ea6a1ac220003b31d563484200055fc0ac8a18a037c7c855d8544c4015eb06382c2100031f197724c5200075bb26e2a1c20008ff845d931140019f220382c8988029f2157458d2100577c0ac52146000a7d82d9665840019bcc6b96c7080023f61376484500057d400c33128600bcf825c1434c47ffc26290c6110002fce0543502100056ec18a3b028600ead43cc562100018fb0e32ec6900033ddc661589430047ec0ae5b1a2000af581dcf614800157b09b1684988031f9d762d09310067b98ae23028637e5f525c5631500197ce2b8ac810003d954951181210047ec08e0b1ea400f9543d09314846f4fd0db2a62900c39bd456250850006ceb9a63a0480008fd831c164484553790eaa2c0a18027b6087050d211b63ec30eab1a4200be9831c12188001cf6cbb0c6090002bd60453586400075aa1ac290880009fb8748630480137ab073826290802afe197250f410055ec16e8b246000fa76450931484015df02b1284280035d8c47558d21005ba42ac7a0a4200abf845d9410800157b08182c8909937a8c37250e20005eac0ceaa1a624af9b31dc1439000dbcce290c61100029f60c10195400047dc3ac03024200af78750d61908d997eedb928620003795897190a10006dcba6851842000a7c85585604c8019bee629ac488002b7e057258f420257a40a86b1420009f7815d1328406dcd8caa9242900028f61031195400067ab8cc33146000d3f411d56150c015eb06382c32100375dcd31581210047fc12ec988a000afb8758a30440019ec63b8ac7100023f60
  | 4 => 0x384055cbb0632a8690002bd60c705845200676b12e3190a000adf835c1644c4011fb07ba2c390002af61a7050f410067bb92c29888000abd8414d629000157b0829ac9080033d59771581431be3e282ec2926200e957350d61100015db043a2c3180033e84176c863000577c0ac4990a000aee875912108001b3ae6a1cc4a080337cc573d85420075bc0a87b1282008fd87d8f4284001fc3023824310002bde0d745864206f4fba6c6a1a8000cbc31dd162440019bae6b0881180031fdd675d8d400076b98ae2b18802dafa80185648c0015ef08b9ac2100032b591728c02000676c14ec90a8000b7a80cc465480018f8eab1a8108072b960875586420055ec1c82b204000f99541c1434c00157f0ca1e82280023f61e5358a100057d400a6b122000d9f7350d62504017e3033ac6088002f5e0d754851000577c12e6b142000cbd7650d41080011f90cba262900032f5077650e100053f42cc5b0a8600d9d7350f619005b9f6c2ba460880031fdd675d85201b63e3aacab024200dcf631c132484018f8cbb8a86a00027b608705512100576c14c2b246067afa801d1618c001da90ca1a6290803b35d1634842006eceba2a730286008fd84dc5628c0019bae6b1841080033d9cf61505400047ec16ecaa420008ef87588628c0017b3063ac6088002bea0365d81430047ec36e69088042fc9214c930840ad9eac6b8c6108003f1dcd3248510004fc402e690a4000f966450d31484bb9eec7b8a87080023fa1e53d852000676c3ec790c4000a7e8598d64840019bae6b1a4228002bb60a43591210047fc32e898ea000dd483dc56050c01d9f0ca1c64908023fa1f42586300047fc22ec9942000add839c5644c8019f6c6b808508002cf2157150e400055ec20a3b1a8000cdf7318d6048401b3ee6a1a4220002bd60753d8540006f9c3a431822036c7e7559660484011fb033b0a918003375c631d8d200057c402e4b226200ced31dc9644c00195ac8b90a0100ab1f9d765181430066eb26e690c60008ff835db4284001ab8ebb1ac6908032759173102300066fc32e62042000fa97450a30480013eb02382a690803ab5916250a300047f438c6b0242008fe87ccb61500011ff06bb485080023f6067650d1000676b90c5b0a8600cbd7458c5010001bc8e2b9286908023f6077650f201be3f438ca98a80008ff8758931900018f8cbb9a4290003ae20143983420057d404cab02422aa7c855d94348401dd2e5b146088002bb619324844000576c26c690c4000abf845c163484a7d68e3b2287080033ddcd614845000577c0ae6b1080008fd82dd943484877a902baa869800367dcd4348640005b7c2ae690c4031afa80dc962840019f2e0386c6908031f9d763d092100576c0ee4b22640d8fd87d9763500018feebb92c8988dabd60672584501853e42ac
  | 5 => 0x10db9b60865485400047f430e0aa2422ad5e871955350c011fb0f20ec7100023fa1c10d8d2015e3e3b6cba8a4000cfa30dc5608c855e3ac8a9a86280039b59670484200057c402a5b0a40008fd8758d21d40572f90ab9a4290002bb60853589100047ec1ee4b20a000cf7719c5628c0019bd07bb286908033be19728c0200063e3aac2b028600cbf74591624c401daac698a43a00031f1977150d201b63fa9aec908a000b6e85d0932484015db0521ec890802cf61251195430047fc0ae7b028400af48750d61080014db04188caa00023fe0572d92300047fc1ae5b242000eb48550d6110001b76e9b9a8108002bb60a7159230004dfc3a8628480008fd82dd9538400197ee9322c7080023fe1d43181510047fc3ac9b1a42008ff825d931d40015df04b24c4988031f19573485400067a308e0b0a8600cf57458521140111ff0eb0c61900032b59172102100063ebaae9b1c2000add83d9132840015ef02ba2c708143e34c54350b210067bb8ce2b2264008fd871476350001d5b09992c4200ae5fa1c31195200057ac3e64b08802ad3d841d56050c0197a82bb287908033ddc661581320066fc0ee6b122000cf77358521100019ea623b286908032f9c5648c0200055fc22eca0c6000af781589218c0017ab0239286988031f5ce75d8e100063f32ae31804000eaf5159121080011fb0f20ac4280033b997725814305e6f39ac690880009f7815d9424c401ec8caa8a43100023fe19701093100576c14e2b146000ced87d8d21880011fb0fa12c31800397dd56350c50005f8402e690a2000e6c654c921480017cf02b9a84908023fa1c3158a402967ab9ac290c6000d5d431d5644c4019cac4b8c85080033b5c872586300047f438a8b1c2000cbc7498d60484016dd0b32264908023fa1c65581210057bc12e6b0880008fe8714d64480011fb0c38286908027ee0176509310047ec24e1b0a6400a7e851cf64484015b906b2ec0908db9b60865485200067b18ae3b1c4000afa80985604c8011fb03386c8990033d5c761d81430065eba6c83024200adf835893284001dca64b0a422800fb5dcd614c420004fbc3aa70822000bdb8348630480017d501290c090803ab5937250c200071e32a86a0a4000a7c855c363484019ed0bb8ac8980023fe0576508500066fb9ac490c6000ecf825d1630809df4e86a126290803a718e6450d210055ec20a7b122000afa86dd2304400157f06b2285080023f61c51d8d201beafa92e62a26200cbf31dd94010001d6a86b0a822816fab4856450a1000677196eca1a4200cf7735854108001ae8823aac69080373609739912107f4f3028698880589f987d023084001d5f04a18c0a11efe3cc77250d421b576c14e2b10a000bcf835913248401c78e0b2a86200033d58d710821000677b94c4b0a8600bad821914
  | 6 => 0x6af980eab0a8600cf583dc5644c0019bae7b18a0a00023fe057610a300065ec3ac8988404efa54350931484019bee731ac908002f9e09704c5210066f98aeca18a000b74855cd214401753b083aac6200025f608705535100576c14e6b142000adf8650d31140011fb04382c7a8817b360b634c9200066eb98623028429a7e859d932840011fd0db9a82900031f19573d85400066fc1aeca1c2000ced73589211400176f02b9286a0802bea025358a100067b18eeca1a4200abd84145644c00137b0f2a4c0a18033b4ca76d0d2100576c1482b184000cbd43dc9648c0015ef02b9ac8908f6bea007258e101b5b6c34a4908a0009ef8748630880011fb0f21ec2a00032fd0f71592300047f438a3b226000af5811d562840d19dae6b1285180033b5cd621404025fcb10a8698c8000abd849cd644840157d0ca1a84908029fe1d53181520047ec1ee4b0ea000ab584cc961100011fb0db9a42280032f5d1644c4200067ab88c3b028600cef215cb638400157b0d38287a1003371ce76486300063f3aec92126200cf5865c4528c0019be63b9ac320002af61273d8a100066eb1ae31804000af78750d611485d1fb0d386a7a0002faa0232181210057bc0aca3028600a7c855876050c015eb0229ac488003379d76350d210047fc1aec908a04bdb4715c543900011fb0eb2264908023f61f63d021001df340c84302420becf7258d3210001d5ac498a8020002bb60a31592200057ac0ceab0c60008fe871916384055a7d0e32aa8a18035e44275d86300067dbb4e0a1c2000a7d83040654800157b0829ec090803b9909614863001d76432643024200bea80908604846decac4a8a42280032f50e76505302de5eb8ac8a1420008fd839d941480015eb03b1a43100023f606764c9400047f438c6b142000cf571d865048017f36e83828698002bd6137358420004dec1ee890880008fe87109618c0019ba62b9ec908002af6136350a1000772b12629088000cf7745852114001d8d02b1a4210003375cf63d8121007e9c1a4318220008fe87591218c05d8f90aba4c1a9957bc887618c12029d5ec24c73028200e76311952150001a7eeb3aa87200023f61f325905000577c32872124200ced215d932840018feeab82c6908025f61c31195200067731ae43242000cfa105cf604840197f08bb28318002af61053586201547ec3ac8a18a000abf8458f4248471ceb0232a82900033b5d1624c8500074eb1a862042000cdd7358c50d005b9f2c6b868708003b3dd163484200057d400cbb0286008fd87d8e42840017590ca1a84908023fe1d644863029773192c290c6037c7f525d931d40019e907b8ac8980db9b1d5624845000775b0c611024000adf825c563d0839b6f08b8c84a08027b21d43486200047fc3ac62042000c7f755d163484015ef08b9ac32
  | 7 => 0xff865d132840011ff03b9ac4880227ba18704c92100756318c8a124200af78154d61880019df04bb265a08033b4857650a100247ec38c7b0a4000ee63158921140019bae639ec290186fa60a60181210063e42ae9b1262008fe8714f64440c99dec7b928710002af61031592200072f988caa1a402bd74515c465480014fb0b38ec6a00976e50d748c1100066fbb6c6a1a4200cf8805d943484011ff04ba0c0988033b1cd62484401572e3b2a6a18a000aed821866050c019bae639ec890803735cd439092105f4f318e0a1e8400b5c855c5438c801dcec898a4310003b58c621d8d200067ab12e31842000eac7059121080018f8cbb9a8290037371cf634854000577c12e1b0a86009fb815c0428c001d3908b1a8708002bb60a4118132035f340eca90c4004de5725466048401dcb05382c3210023f61c311814200576c10c3b028600cf6315c763500014fd0a322c7080023fa1d634821000766c1ee4b226400aed821d76250c015bb06082c9180023f60773580540067b10ae7b0a40008ff845c4604c8011fb0e182c890836b7a0c10d8d400062f31cebb1c2000e5c7558d4394001b3ae8a1cc098803b9a0763486200047fc22eca1a4200cbc7659143484017b307a1461080032fa1b744864000772b126290ea000af7815956050c017cb053a262908033d4c776486300065eba2a83024200ed54358531c807fdcec698a4310002bb6194248450006b7bacea90c40008fd81dc9631500137f06ba0a120002b760c1058a30005dac0ceaa1a8200fc9329c1214c06f4fd0b3b263100023f6077258f40005d7c12e0a1a825ee9f4158d438402bd9b05b1a64908031f1d561502300056e432e29926000cdf315cf62840019bceca1a6290002be20165581430047ec0ceca1a4000af5818c9611406b9f2ed18641080033b5ca42181310067cb1ce02142000a7e851c5644c8011ff0ea1ac428002bde0532d85400066e43ac6a1c2000aed8204162140019bec9b9a43180039954961487500063eb8cebb1c2000cdf31dd943840011ff04bb265080033e5c070d8543007e3b9a6290c4000cef625c6628c0015eb033b26290003ab1d942485400057ac2663b0a8004cf671d863048001be301b8a87080023f61076546300076bb9ac290c6000ead4159121080011fd0e28ec890003eca0143505100047ec3861b128210cdc7358d21d00015db03996c4a00023f60b74586300076dc32869842000cef764c92110001775012a0c0a18033d8c571d8d420067729ee4b2260008fd87d8d41880019bc873b262900028f6103119520006ba3aee2b1a823cfe231dc121880015bb0710ec4a18039d884654c520006daa1ae2292820d9bc875514350001b9ca7b92c0a1802f9e05744c9210067ab8ac31804000a7e859cd6484001d3ac8a1a62280032fdd26458d210
  | 8 => 0xc8a1aa2280031f1d563482100057d436e31824036e747558521140011f90eb1a43a00033799773486301572f418caa1a8006be681d8d2188021d3f0ca1a62200023f60c70586420073a32e63b0a802997d86dd53214001d3a8798ac4200029f60b31195400047ec36e2a1ea000b7a808c465500015bf06b2ec090857b3487634c92106c7ec3ac92846000cf5635c4508400197a87b8ac9180023fa1e31d894000736a8ac4908a000cdc85dcd624400dbcee498ac0908023fa1c5158e200072f32ec7a9a4200afa800c5648806f2f90ab8084988023f61f644ca100063e3aee0b1a42008fd83dd16284001d3ac6a1c8108002bde05764c6400065eba6c9a8a40009bf8750c5010001d5d0eb2242100033799773581210047fc22e630242009f8805d131c80016df04a9ea3100031f5db7550c500047fc3a86b0ea000fa46450931484015bb0628ac7100023f61b7250c5026eea31ae7a0a4200af880591604c4f1d3a83b1a86908031f5d9534845000756b22422804000abf8650f42840015ef02b9ac8280029f6166358a100067b98ee2b2460008fd86dc1424c4019ef02bb263a00031f21572181310053f42ec6b142000cbf74d91514c0011ff0eb0881180029da0765996300053ec18c232a4000cbd74992604c41fb3ee2a1a6320002bb60b64909310047ec14ec98a8000abd8498c64840011fb09b9ac3900029f60e21195400057ac34e898a4230c7f535d94214007fc70438242880037c5c5408c21000757c22c4a146000cdd7390f62840018fb0fb2ec6a00ab1f2157650c500057d404cab028600cf571907648c001dcb03b1a43100023f6077458a300063e3aee8b1a4200add8315363484018fb02bb4a4280023fe1971908500066eb9a87b142000af5810c361480011fb07ba2c2290023f60e7650a100074f98ec8a1c4000cbc75d9143440015ef02a1ac2290027be09744c6200066fb9ce7b0a8000aed82145648c0019dae4b08a0100023fa1f64486300047ec3ac8990a000cdf31dcd64484014fd0a30ac4a18033d5937150e1000766082c69084000d75535c450840015b902ba2c6100031f60d7695050004f6402e899242008fd87887648c001ceb03b2ec290003375cd639812100677c12ec9968000eb78150d61d08015eb02186c4a0803375cd61142300047ec36e2a18a029c7e871953250001d6a86b08a0200023f61e51d8d4007dcf41ecaa1c8000cde635d3638400dbcce290ca1100023fe057218143004bf438caa9c2037d77545c4524c4019f261bb287080023f60f71580420063e3aae0b226200cbf415cf64484019dce4b0881180029ea003119520004f6c16eca1a4200cf58758630080015f50130ac0a1802bd60e70584400055fc22eca0e4000a7e850c764480015df04bb265a08033bdcb61581430073b408cbb0a40008
  | 9 => 0x7050e400057cc1ec1302421fbe7825d521440018f8cab9a429013f751c57150e321553ec3ecb32a864ad9f315cf40900019e902bb28708002bd60763506200057bc0aec98a4000cbf845d943484019f420b98c090803375ce63981210067743ac49888000ee661189218c0015db0428ec0a18029fa1474586300067ab8cc3312860087d870c465500011fd0f18ac520003b94c96148440006daa1ae32128200ead6450921140019de43b92c8988023fa1f32592101e7f128ee090c4000c7e7558a604c4017cb053826290802b760c74586300066fb9c86b224200d7752dc543d4401ce8c23aac2a18031f9d563d0921005b642ae09924200aef82591514c001d5900a1ac42002fe6e107050d300063fb88eab226200a7e8599163484011fb03b9ac1a1003b654d6018143004f6c3a422844000a7c855cd61c80015bf06b228690803b358d43484200056fc1ae2b226400ed7735cd61080011fd0e3b287080037a21d214c22007ece39a86a948000afa80885648c0011fb0f28ac918157bc9c5628c2100055ec2063b12802ba7e85d8d2084001d8b02b1a42100031f6077654050004f7c3a432844000cbf7414d62440014e902b28caa18031fdd67558a100047ec26ec90c6000adf835d163484011fb0f318c090803ab9cd43588400055ec24e3b1a8000bcc825c1434c40179b062a264908031fdd77458d2100757ba2c49088000b5c855c5434c0019bae8b1c61080032f50d76d0a30006ceb9a873028200db7744c56048401cb8caa9ac0a19d7a74c56450f210047ec38a8b0c6000dce21dcd6048401d9b0eb1a42100039bd4b62d45300056e41aca3024200ecc634c860484015db05188c0a1003abe094358b410047fc32e890c6029e6f5158932140019f460b88c0a18da5f61b75484500047ec1cec9942000be987c8630880011fb0eb1a42200033d5db7150e100047fc1aec2928200dd77354560484011ff04ba6c708002f56067250d311b63fa8eec908a000cbd7450c60484011ff0eb2263100023f61f635052000577c12e8b142000b7a85d8d40840f19bee3b1a8690802bea00425863000677c32e89924252ed473d8d2144001ec8eaa8a4310002bea0063591210075ac2662b088000cde865cc5448401d3a8798ac5200033d5c621d92300073a3aee2b2262008fd8798b618c09db98c6ba264908031fd9573d85200066e3aee6b1a4200aed82145628c001f3100a1a6320012bda0430d85200047f43860b242000cdd7650d31080014fb0a30ec0a1803abe194350b2101ef338a431804000c7e7558f4284081dcc62a12c390003b658d628c210155afc32a6a18a000abd84ccb64840018fb02bb4a82813bf118d424c5210066e98ae9b1a4200b778154f524406f8fea4bb0a8988029f21563589410055a43286a0a2000e5f658c76348001c7a
  | 10 => 0xb0a8000ee632585211400137f0eaa6c0a18033ddc4105913200757ba6c890c4000c7d835da52140018f8cab8c60900023fa1c525863000676c3ac49888000cbe87d9143840015bb05b8ac6200033d58d7114a100066eb1ae22804000aef825d1628c0015eb02182c3a00032f5d164484501b63f438ca90a8000cdf739cf614800157b08188c0a10023fe0d74181520066eb9ec7b0a4000ed78158d31d004fdcec699242880023f61e51d8143006b6328e0a924200af88059560484015db0428ac8900027b21d434842014e3ec38ca9924000a7e85d09618c06f2fd0a38284988032f6107650d21005d6c0ee4a1a8400afb80508604c4019eaec98a42280ae3f61a70d4720005d6c14eaa1a8400af7815d1618c00137b07ba243200033d1cf61485400053ec2ce7b142000cf5711846250c011fb09b8ac7a8002eba1943509210057d40063b1280008ff835d94348401cbe6232a86a0002bea022158a300047ec3c62b10a037c7c855d8524c4011fb0e28ac899003579d543909310047ec3c83b1a8000be0805492144001dd704b126108002bea0221588501763e3b6cba9a8000cbf7450d6284001f4f02a1a84908032fdd86450e100067c3b2e090c6000afa8014d6284001f2a86a1262908023fe1176506300057d400c7b224200aed828c564080775db05386c8908033ddc731592200047f438a6b068400cf5635c440840011ff08b98c0a88032f5d3421813100576c1463b1280008fe86dcd2150001cec6232a4290002bb60a61d923000676b90e4b226200abd84d89424c4019bae7b18c09083f371cd63546400065fc3ac83246000a7d851866050c1b1fb0e086c6a00029fa1464586301863fa8aeca10a000ced829d932500015f50128ac720002af61332d89410075643286a124000af78150d6190801a7a863aac6a0802bea0251d8d4000677b92c4b0c6000e3d659c143d08015eb02186c2a0003ad50f32584400066f432e7a14200087f875946550c011fb06382c229002bd60472d85430047ec1ceda1420008ff835d941140e7bcae69968290803b658e30482101bcbe42aec2126229d5d635ce5214001d5a86a16c290002bd60475d85400053fc1ac8a88a0009df8754c6050c01d6c82ba2c2100033d886764c5400063eba6a6302a200cdd31dcd62440019d8e530ac0a1802bb61943484200057c402a9b1a8000db97450a30840013f100ba262a000373cc772581430067bc0ae9b1262008fe870c762500019da643b242980032b5d162140400075aa1860b088000a6d820c465480019de64b90c0a18023f21f63485400066f42ee6b122000cdc315c763480015db02182c420003ad61d43584400055ec20c7b024200ed78158d311000197ceca1a82900038fd5364d4d1000676bb2649088000cdd635ca30840017d702b9461100036edd7
  | 11 => 0x8c8019eae6b0a4220002bbe19744c921006dac3ec9a0a4200bd78359131484015f50032ec0908033b59772581430067ab88e2b24604fd9d7150e32504015ef02b2242280b77698d748c2100047ec18e0b0ea800d5f311d56150c8997ae6b208118003375cc63d8121006d63a264b024200ced87d8a6250c019eae6b0a42280029fa1b311952000676b94c5302626ef9a531c143900011fd0e29ac3100df9da04654c52000576c1482b10a000cbf7418d6048401f36c8a1a610802f379cd63140400047fc3ac63024200e74511976150c019bae7298c090802b760e764c5400056ec1ce8b1c2036b778654521140019de63b92c898002fca0275485100053e42ae2b1e8000add83dd363484019eee330ac5180023f61b7150c520057c402eca1262008fe87585408c0015ed07382c2200036edd1644c2100055fc3286a08a000adf8790563080015eb02182c3a10033ddc671d8d4000676b90e4b1c2000add82dc563d08014fb02318caa0003f85c5218c22035e5fbb4e0a188000ed4634c5604841b1fb0e30ec6a00023fa1c6558143004dfc22e3a9c8000aed8214d62840119ece2b08a1900bfe698d43902101ffe441a431844000ead8290564080013ef02b9ea4880027be1d21142200065fba2c89884000cbd64dc543140015ef02ba2c6908033be097650a300047ec1ee2b068400cf910dd9218c0bf9deed3824210002bd60a73584400066ebb28698ea000af5870c16110087ba8e2b8a86980035d5d47548510106dac26e2a1a8200c7e65dc931100014f90ab1ec090802af6133159050006e6b9a643024200fc68250d31484019eb033b262a000337dce3158a400247ec3ecbb0a4000b3d8414f65500015bb0628ac720002af61943d08500047ec26e4b0c6000abc845c363484011fb0ea10c0988033958971908500056ec18e3b1a807abae871c9435086d2fd0fbaac6908027be1d63909211563ec30eab0a8600cdc835d921140179b8c638286908ab97d456350c500055ec2442b226400cf57158450080018fceab18c5080b73ed8d70d0e100055ec24eca1a2055cfb7358930840015ef02b1a43a00032f9d94350a100066fb9cc6b224200cf77198563508015790ca8c80a00bb1f99574942300074eb1a86a10a0008fd8790961140015db0418ac910002bba086458e100047ec1ee8b0840008fd86dd13108001d6ee8ba2c21000397a0c65d8d400056fc1ae4b08a000bb48650f41484011fb0eb22422800373dcd52581210067bb88a2b226000cf765dc56050c6f8fea8bb263a803f679cd43d8640006f8402e32142010ade831476050c01cdeeab1242280039ddd5614845000677992ec99080008ff865cd21d40011fb0f20ec4a18023fa1f635021000773212c2908a000b6d829c765480c5fc4623824310143e920543509210055ec24e7
  | 12 => 0x2b7e0d65181212eef9186e2a1c2000afa8018d60484011ff0cb9a4228002af61331983420057bc0a8630242009ef8748630080017730238287200032fe1d6450d210047fc0aeca1840008ff815cb63440011fb0f29ec29000337dce53589100047ec36e4a0c6000a7d828c465500016790ab8a87a10033d1877258543004fac08e0a1262008ff8750d61c8001d68a6a1ac2200033d60d711814200666b1ee4a18403ffe1314853088001de2a2b00c0908023f6107058b5305e6f31ae62042000afa8094f62440019eae6b8ec890803c7551535814324e5eba6c53028653cbd71d9143440017e30232a81080033721d634ca10005eac0ce0a1a6208af48150d61c8001d6ae6a1ac2200023fa1c6458630154ee43aa6b02861bb9d849c9434c45d2f90ab9a42a00df1f61c654c5201bd3e42ac498c8000cdd74d8d32484211fd0c382a8a18023fa1f61581430057ac08a4b0c6000cdf7358d62840017ab05b8a86988db5d9d551d81210053f42ce5b0a8600cbf76d9143840011fb0c38284988de9f215764c5200055ec20c4b0c60008fd87ccb64840011ff08b90c0988023f60772592300047ec24ec9942000afa80945644c0017730ca1c81080029f60e21195200067bb8cc2b028600ed78358531080017cf04ba262908033e4407058d210055ec24c73242075eb47159143484011ff08b98c0a90033ea1b748c1100047ec3820b1c8400c7c75dc1644c405baee2a1ac098802af61275592300057ac26e6b08a400abd84cc46050801aed0bb8a87a8803e5e05434c4400053e42ae0b2262008fd86dd1218c09d9dac6b968690803ad211615063000762b1a629084040cef765d1210806d2f90abb286908023f61e3158b500056ec1ec49928200cf571584408c001dcf04b0a43180123f61d62942100066eb9a6430282008fd81dd943484015eb09b9ac3210037960470549210047f43862b244030e3f5359142140018feeab92c898803a550d614c4401b4f643aa4b024200abd8650d42140015db0418ec4a00033d58971142100067bb96e2b226200e9f6350f4248461c7ea2b2284280023fa1c53d89100065eba0e8b1a420fb9f845c1434c4534f90abb264a08033761b7348630006eaa1ae32126200abf8359141140019deecb9287908ab971d56350c500066eb98c7b2242009ed8748630880093db05386c690802bde0543587200066e32ee6b024200c7c7559163484015bb07a10c0988023f61b714cb401bcbfc32ea988a000aed829d562840099ece3b0ca0900029f61463d81210066e32ee690c60009ed821c15348417daee2b1a62200031f997734844000677b90c2b02864ecef635cb43484014fb03990caa00033d6067650d210047fc0aeca18a000cdf65dcd60484016d90ab1c84908033d5c461d8d40006f3188e0a124200e9d7450d61
  | 13 => 0x63f3b6ca98a4000cf5315c7648c00157f0ca1e84280033bdd862486300047ec3ac6908a02ac7e75d976050c015dd0c99242a0002e760c6550e400057b40ecab246000cf5315d9218c01b5f100baac918002e760f6550e40004fa43aa690a2000ddb7358d40840019ed0db8a86908023fa1c51591320053f428c2b028600cfa305c76050c019ecedb8a86908af1f9d765d85200066fb9a86b142062beb8258060484011fd0e28ac7200032fe1d64102300047ec16e2b1ea000afa8094d61880013f70e90c6110002bd2056518143007e2a1a6290c4000ade83d9562840558fea2bb286280023fa1c6258630107ca426e2a1a62009f78754d214400155b0998ac420002af6133258742317f1288e090c4000abd8414d60d04d1d5a86b128518167b3485634ca10005f54048490c6000cdd73d8c50480015bb063aec6a0003c755153181430077399264b08803afa94350a30480cbbb221b9a43180df5d14171149310065ea0ae7b224200a5c8359465484015eb07b0a42a00035b5c951142200055fc22c6a1242008fd870436250c016eb03298ca908023fa1d634844030677bb6e89084000aad8204164080015bb0628ac898003ad61273584400067ab1ae32142000af4815956050c015dd0eb1a42100023f60f74588500075318ac89084000e5f75dcd6348401d3e62b2286280fff190d31486200057ac08e6b142004afa809cf6148001b9ee6992c0908023f606764c9100067ab22e31842000ecc5158d21080013df04ba262100034fdd353546400ae6eb8ec69924200cef215d932840019eae330cc0a18033ea1870485200047f438a6b068200cbd849d943480011ff02bb265a012fa74c543983410075caa2c030286008fd84dcd61d40019bb0cb98a8908ab1f1d57650c5000676432e89924200abd840c16110071c7b0832a82a0003abcc562500400057cc1ce1b142000bb5819c94350401f8ee698a42100033be097650d210057c402ec9928200af5864c521140011fb0eb0c6190002f9e05704c9210074f326c6a1a4237e5c505c56315001d6f04a1ac2200023fe0d76487402d676b8ac4a142000dea80dc943880011ff02bb26428003375cd63d0850004fdc1ae1a14200097d821c153d44011fb043b28708003ab50d62484400057dc02e8b1a4200ced72d886050c0157b05b2287080023fa1c5358a10005b6c2c853024200cdf31dd94314001d5a86b128428002f5219434c5210066f18ee6b064200cf67358521100015db0538ac8990023f6107648630005f4c14eb1824000add831516384001de50c382428800337cc573d9210005eac1e8498a4200cf9309c363484011fb0f98ac8280022fe1d64192300056fc32869884000cf7815d9218c00173100aa286980037960973d05210065ec26eca1c2000ecd63dc943908011ff08b9ec508
  | 14 => 0x57450d61148019f261386c6a0803e360f7250d420066eb9ac7a08a000cbd745913214001da8c63226290802b760c54586300075c432872042000cdd731cf615000197ccbba2c090802bb60851d912000677b92c49888000cdf7398d61508014fd0d3aa86a88031f9d564d8e100056ec18a8b1a42008ff865d132484015dd04322c3180023f61f32d854000756b22431804000aef815cb63880011fb0e292c3180023f60e76151210047ec1ee2b00a8008ff835d941d40011ff06bb26508002ad61053584400047f438a2b2440008fe87145644c0018b8c63aac690803ade1d435844000577c32e69084000a7d839d8655000155b0428ac8100033dcc6764c5400065fba0e0b22420d8fd87d8e505000195ac8b90c9080039b99532484400063f3aae5b1c2000cec721856050c01a7ceaa1c84a082eaf6107558c4000757b228690c40008fd871476250c011ff02bb286290033ea037650e100056fc1aec908a000ecf8258d32100014fb0d298ca908033d5c621d89430067bb8e62b2240008fd83dc56414043e3b0832aa6a18027be1d52d81210067ac3ac228040369f4875456048401d6a87382c2200032fd0d74d8e100067ab88c33128653e9d31d914384001bb6e6a1a81081d6af6126358941004f7c3ac91924200db471dc943504011ff06bb085080033b5db62c86300067ab92e3b1c20008fd829c3644c401b3a863828498802bba1a42486301b63e42aec908a000eaf5350d62100019ba63b9ac888003378c6764c5200057643286a12422ae5e8319543480779dae5b24c09097ba75056350e10005d6412e0a1a8200cdd7390f64840cb9bac3b9a43180036edcf42502100067b18ee2b22603fdcc735cd21880019bb0cb9e84908033da067650d210063ec38cbb0a4000cfa861c143500015bb07b2287080023fe1d6350a100057bc0ae8b18a000a7c85591624c401b6a86b888118002bda1d4358420004fc402eca1262008ff835d362840018fd0c382a4a88023f21d43d85200066fb9c86b142006de77254560484eb97ee2b2287908031f1d56158132006afaa6e6a8a60008fd819d8528c00197e86bb283180023fe09764c44000576c10623028406ee6604c521080019bd0db9a43180033721d6348440004dfc3a87284805ecdf7158d43840011ff0cba262280033b1cb61581430056ec18ebb1a2000ead835912108055abceaa9cc0a18032f61f64d09210053fc2ac73024200de4815d132484552fd0fbaac2a1802bb60b6350a101569f3aaa83028600afa8098d60504ab5f50031ac50800337e1773589100257b408a6b122000cbe87591310807f7d5003124318002bea0063191210057d40664b142036c7e75d9760484019ea633b24298002bbe1162484500072ec18cbb1a4000a7e868c765480015db0518ac428002af610535922000
  | 15 => 0xcba4610813be318d43509211b4bec32e3290a000cbe7458c208405b9f6c3b9a8088002dd20565195431bcbe42ae13226200cde315d931080019bae6b188508003ae5d36098143004f6c3a422804000ee482585218c001daf02a1ec298002afe194350a1005fcbb8a8698880008fe8714d64880015f50131ac0908aaaf2195450d400063eba8eab142000f956450d31484013ef02bb684988023f60b7458e10377cd988e0a1c8000ef2701c16190801b5c43ba2c0908023f61e32584500053f42863b028400bb986d0e40840019ef02bb286280023f21d4358a10005db43287a0a4200d9f7350d615081b37b09386c4a198fb98c563486200065eba0e9b1a4200abd840436250c014fd0d188caa00833d58f7150d410065eba2c93026400cbf74991614c801c3ac8a9a8628002afe096450c500073ac08cbb0a4000cf6315cb614c00177100b8a8720003bc5c7618c12000656ba2c431420008fd87d91218c0011fb09bb2a3180033b8c7764802005ecf39a862808000abd8414f6250001d5f04b22851802e6f21d54181431b576432a490a4000cf7815d943840019be62ba6c6908363f61c1059230004fdc1ae021420008fe87945644c0015f50dba460900023f60e7694140034f743eca90c4000eac8550d62100015b90cbaa86980031f9d563989410067bb88a2b226400cef7358921100015eb03212c318002f6e0d218c22000766c1462b184000cf97358060484015db053aac5180031f9977150e42005ddc1ac9204200097f8759465484011f90cb9a42a012fe64c54390110006f3396e2a1a4200aed829d932840011fb043b2a68812eeea006450e10007f1b9243182200fe9e639c1431000197a86bb464a0802bea024358a100047f43e63b22402a8fd87d976050c019eea7b8ac8980e29fa1676506300047ec1ceca1c2000cdd73d8c50440019bac7b8a64200025fa1e6554d2100656ba2c410420008ff8750d61148013eb0238286908033bc8572d85430066e432e7a142000ed58158d21100019ec623b242980027d604704c9411b63f3aeca30242008f8805d943484014fd0b382c690803ab90564484200057d404a3b226000add82dc563150015f501b2ec090802b760c10591320056ec0ec6a1a8000cbf43dd163840019eae3288c0a1803769c47050d300055ec20c63024200af5810c16448401d5ac898a4010002bea0071d8943006cfba286b126200f978150d31900019ec433b26290002f560e654c52100676992e5b246055ee92158a30840019baa3b9ac488002f960763486200074fc22c6a1c202ddda43dcd40840011fd0f10ac918002af60e41d91200047fc1ae43028200cdf7358d21d00157af06b8262908029f6167159230006ebc1ae32126200de7815d132484019bc86b8ec6a00a71f215764c8500065fba4e9b1a4200eb
  | 16 => 0x3181210063fbaceab2460008fd8715363484011fb0f326c318002bbe0964509311c4be42aec9928200cf7764c521140015bd003aac7a10423fe1d648c2100047ec3c63b028400cbd435db418c0019dac4b8c842800337cc7735891000576c10a2b1c4000c7e765cc6550021978edb8286a08033de1d61140200073a3aac290ca000cdd7390c604840157b0829ec2a00023fe057650f500066eb9ec7a8a4000cbf74991618c00176b0338286a0802af2117058d2101d7a40a863024200df087486304400157f02b9ac8100fef320d754862000576c0ce6b108000fa5424c52150001ae8cbb8aa688002af6127650e100053ec182132c8400eb564dc54348401f8ec6a12629098f798c6708c9210066fb9ac6a8c8000cef65dc96050c552fb0cb9ca828003a7d8d43505401bd3e42ac898a4000af4865cd41440011fb05bb28708002bb608515913200757bb28490e8000c7d75593618c0011fd0e29ac488002bd60765592300067a42ee2b226000cbd31dd162440014fb02318ca900032759173d0850006e6ba6c69924200aad849cd62100015eb0ea1ac2290e31fd4d76504500047ec16e2b18a0008fd839c3625040197b093b282900bf3e58e70d0e10006eab9ec7a0a4200cdf73d8d2150001bac62b98c090802af6127650e200047f438a8b0c6000e3f7559143140015eb02186c8908023fa1c5358a400056ec3c82b18402ad5d831d56050c011fd0f29ac310002bea0053d89100047fc3ac63142004aec8654960484019f6ecb8287080023fe0d76507200067db84e0b226200af78750d61080011ff06bb282100bb1f19676d4d401753f42ec6a042000cbd435d9418c087da902a1ec29813b798c7735092100767402c69084063ecc73d8d21880018f90abb263a00029f60732195200053f43663b2a8000ee762585218c0015f303386c9180033bdd94248630006f238ce4a1a42008fe86dcd21480019bce3b1a64900033e84076485300057ac1662b088000cbe71591430800167f0ab8a8720023b5dcd614c7200047ec3e64b088000eaf8650d42484018f90ab90c0a88029fe156358121007c6a1a8498a4000a7e859c76348001d3ac8a1a62100034f5d1511424005f4f31a8620420008fd87947648c06f8fd0e32a62900033d8c772586300067bc3ac31804000ef3611c121480011fb03b9ac888003ba50b618c1200056ec18a3b2260009f88748630480011fb02382c9a90029f60732997421beae282e62a26200eb48650d41440011ff04bb283180033bdc851591300066eb9a863024200cbf74991624c4011fd0e2a6c6908b6bea0071d8d40276f318ae89924200ee952580604841b5bd07b2ec6a00023f61b744c720005f4402a53024200ced321d94348401f32a7b82872012fe5205434c6400047e43ac890c60008fd84dd9528c01b9f2e
  | 17 => 0x126200ced32dd9218c00157b0931ec5080023f61b7150f200059e42ae0a1a8200c7e655cd21100019bae6a18c0a8802f9e0543486200057d400c3b028600add8304363500019e8cbb8ac0a1802af6127650d200047f43ca6b142000cb77458521100011fb093b28690802b76077258f4200757c12c6a168000cf7865c6428c0011fb0f990c0a0802ab60a715902000576c10a7b024200aed82041644c8018f8eab12c2a1802af61331d91200047ec3c86b14202ad3e755526050c013db0438286a9003e320943509310067ab22e22842000c7e7619531500017ad0ca1a62908026f21d43484400065eba2843026200c7c65dc532500015eb03992c2200db9d60465485400056ec0ee4b18801bd9d7450e424c401d98ec99242980033d5c641d8e20006ea38ee0a1a6200abd840c56448001dcf05b1a42880022fe1d64192100066eb9c87b224200c7d87d9761480015db0429ac520003a7591434c7200047ec0ee6b20a0008fd8759131c800117f0eb20c890802af60f64d0921005d7c22c6a124200add83d914348401b3ee6a1ac0a08032f50574d8a1002773b96c290a4000af880589604c4011ff06ba6c290002bde0d614845000677c12ec9942065cdf61dcd218c0019bae8b1a65080027d61f424c5211559ec34a8a18a000cbf74591618c0011fb05386c6a08023f61f32d8520006d7ba2a4b024200abd848c564080013df0e908a0100037ae1d218c2200047f438a7b0a4000e9d83d9143840015f50029ac310002af61332591210067bb8ca2b22604bfb08150e40840013f100b9a43a00033718c7058d21006f8398e090a2000ced215da42840011fb0f326c690803575cd5114230006dbb22e3a124238c7d861d563504019ed06b88c0a1002be2017359121006f2b8a6390440009f98710a308400197ae8b24c4988033d5c47158a300066eb9cc63242006de67148450880012ff0eb28caa18032fd9173992100067ab8ac31864000cdf730c56290001b3b06382a8a1803ab5cd43588400055fc22eca1c2000e6f7654921d40019bae6b1cc508002d72157050d310053f42ce7b0a4000aed82043644c86f8f8a0bb263a8002cf61031195200057bc0ac9a8a6000aed82145634800157f0ca1a82100029f608311954015cbe42ae898a4000c7e7558c4084001d9c62b1a42100029f2156358141005af400caa9a8600abd8650c40840015ef0f992c2200029f6167358a10006eaa9ee2b028600d76755c6604c401d38c6b228690803b5dcf63485100047ec08eca9a4000e9d6350f428406b5f30d39461081332fdd97250c400047ec3820b184000de6319c242484019ea62b96c2a18026f61d439424027fc6a0a871924200de682dc54348401baf07b8ac0a18023fe0d7650850007d9c0a872042000cf675dc5644c407bcee4b88c0908029f6146
  | 18 => 0x8001ba903b9ac09083fa798d4390210004fdc0ae12146000cf9305c46050c0197f0eb20c8908023f21d43584200047fc22ec98840008fd87905628c0019e862b88c0a1802bd20173586420047ec3c8630242008ff865cf42140019eee310ac5180db1f9db75484500047f43c86b142000eae755912108001b72a838286a0002fc20175485100066fb9a86b10a000cf785dc5644c0019bf0db9ac09080ebb60875584200047ec36e690e8000cf7635c642840011fb023b2a710002bb60861581430076ab9a86b08a400be8805cd2188001b9ee9b1a64908033e8417418121006d7388e4a1a8400ced21dcd628400157b08182c8280023f60e7650d210053e42ac2b028600f988050d414c0c7dca63b1242980033b5d862486300065eba0e8b1c2000cee325cb63840015eb0229ec09080337d8c7050d21006daa1ae22042077fa631d9142484014ff0ab0ec0a18033358d72140200057bc0ac890c6000cdf738c961140019f460bb46508003e9d9132d0521156ae3aaa6b0286008fd81dcd60148013f30fa146108036e76127050d31004fdc3ac03024200cbf74d8d60484019e862b9ec2a0112bea0374592300067aba2e3b1c2000cf487585218c0011fb043b2a7080031f1d761581430047ec16eca18a00f9be87d95439000179f06baa43100033d5c621d8e200063f3aac72142000dda805cf42840015ef06b0a43a80a65f61973948500065e32ee8b02420f9be8719543900095ed0232ec29000367dcd4354a400055e402c8a1a4200cbf415d9438400157b0831cc89080337e1d63484400066f98ae7b0a802ddbb435d230840015eb0229ec4880033de05764c44000676c36e4a18400fb9e8319543900011fd0e29ec89095fb6585638c210005f4402a4b0242008ff865d132140013bb0638284988fbf88c5218c22000766432871924206be48150d21880011fb0ea18c0a90023f61f31d81420065fb2ee8b024200ead435885010001dace318ec6900023f61f6310a1000677b90e0b226400cbf411d943484015bf06b26a6908032fdd16458a10006ebb9ac290c6000bb8805526050c01dcac898a4310037379cd6414230375ddc22c03028659cdd7158d32840013db0e90c60101bbaed907050d400065f322e318040009ed81dc943880011fb023b2a8900029fa143158a400063b3aae3b1c2000b7a800c465480016dd0b3a26490803b958931487400047ec1ee2b148024c7d619d7638401fb3ce6a18a1200023fa1c51d8d200072f41ecbb1a8000a7e859c1644c4017b30238286980036ddd1515812107fcbb8a8698c8067afa80191618c00177303b8287200032f50d7218141006ba3aa62b024200cf553dc5644c00157b07b24c890802bde057058d210067bc1ee2b22600fcbc769c143504014fd0c188ca900029f60e41994200063e3aac8b
  | 19 => 0x3ab60543588400057ac0ce8b0c6000aed82905644c8019dc63b92c89812fa7cc543983411663e32ae72828000af581dcf61500011ff0cb8c6428002bb6137258a10005b6c106232a4000adf8458d31140011fd0f20ec690003b94cb61485400067b432e32146000aed8214563900014db0d29242281bf2fd8774486400057d40482b246000cf9621c1528400197ae8a18c0a8803b318d32981210072f42ec7a9a4200af987d826050c015d904b86c2a18023f61c5458d210065fba4e8b0c6000d7b75dcd40840014fd0a31ac8908036d61171989430047ec18eca8c8000af78158f411400197ce2b20a0100023fe057690a30005d6c18c8a124200eb543d85415000197ee8b22c0988023f60c7654a401be3e282ec2a26200cf586dc543484019f0ed38242980023f6107654a300047f43ca3b1a8000b778154c50440014ff0ab0cc0a1803a7611635042000732b12a2908a000cbf7494d62440015f50018ac8900027b61d219422000576c10c23028600afa80145648c0011fb03bb28610143a74c54358b41004de43a8690c80008ff825cf615000197a86b88c0a10033d9cd611404000576c16c72142000cdd7650d31140011ff08bb242280029f606761952000676bb284908a03897d865c6541406d3df0ea94c090802cf61031195400057b400eab0c8400cf571cc460508011ff04b88c0a18029f21572591310047dc3ac03028600cdf739cd62840018fceaba6c7080e35d58571950500067cb80e0b226200cdf7458d32840011fb0fa10c0988032fe1d43588401bf3ac08ca98a4000fcb8348630880018f90abb08498802b760c10d91320075aa1a64b088000cdd815cc60508019ec63b8ac8990033358d728c0201563f3b6eaa18a000cdd865cc54840019bae7996c4a0803761c47050d3018e76b8ac41042000eaf8650d42c80019eae330cc0990029fa167458d21005f2c0eca90c4000cee321d943484015eb0229ac31018bbad8870485200063eba8ebb1a8000a7d839046550001b5a42ba041080031f1d8654c5200067a32ee2a1c2000af980992604c401dcaa5b0a42900035d1d7715913100677c12ec9908057cdd7158e30840011ff02ba6c7100029fa1671d8d4000756c2662b108000fc5434c52108001d9904b1a6508002bb6086118943004f6c3cc89924200cef8758a428c01b9bcc6ba46108002b760e4158c200055ec2662b26a000add811c163150019bf06bb24228002bb61a744c9210057d436e51822000ee7624c521500019cae4b08a0100033b5cb62d85430074eb1a8498e8000a7d828c46548001ecaa4a8cc090812bea027358a100066e98ae9b1a2000abd8414f61480015eb07382c229003375cc63d85200057dc32872042000cdf7358d60484015bf06b92c3180032fdd16458d210074aa1e62b088000abd84145648
  | 20 => 0x6fb9ec690c4000b768019551484018e8c23aac2a18033761d635042000676bb264908a04be9d6150d31900cd9eae6b0a8318002af60b74592100063f3aac22046000cdd7458d31080019f2603b287081627e61e648c2100072e318eab1a42008fe86dc93150001aea623aac6908032f59373504200047ec10ecaa42000ee53258521d40011fb09b9ac2290032f5917319121006f838ce0a1c20008fd83dc5644c0019eb0cb8881180033be19744cb210055ec24e7b0a404df946350f41484019bce2b1c60100032f6127650d100047ec26e6b084000cdf7358d40840014fd0b39ec2a0002b76067058c4000677994ec9928000cbc7159143080011fb09b9ac4280ab8fd4d6450c501b6b73aaa430242008ff815d363480018feeab82c8988032fe1d64d0a300067ab9ae4b088000aee8650d21880019dd0fb1a4310002f62017150d30006f9b8ce0a1c20009df835da424c46dced0232a42a00037620173d0a300057b404eab0c842ddb9435d230840015eb0321ac89080f3d9c5618c0200053e42ae0b1a4204af681d9761480095f100baac5080127b21d52485200063fbace0b1a4200adf825c5631500197b0fb24c890803abe1d43588400074e322c6a1c2000abf865c543d08019eec9b8a87080031f5957419630006bba8ee2a18a000c7c655c763480011fb023b286880033bdca72591310063a3aee2b226236d75615c652140019bae639ac5080029fa1642586300057bc0a86b0ea036e6f5358921140011ff0eb226290002b7e057258c400067639ec490a8000d9d439c3424c4019dae8b96c710003370c6764c520007b2a92a2b024200cf6635c440840015ef02a1ec2a0003374c57650e1000676b1ae420420008fd82dcd6414001b9f05b9ac0908023fa1e31592201563fa9eeca18a000e9f6350d42484111ff0eb08a1900023fa1f63482100067a38aeca1a4200cf571587408c0011fd0e082c5180033e5c07058d210066e988eca1a4200ed57350d61908016bf06a88a0980023fa1c51d8d400067b41ee2b226000cde71d8d43480015eb022a2c3180032f5937150c200059e42ae2a1a8400eb54358531100011fd0e28ec4a00033d5897194210105eac1ce898a42008ff815c86054c019bee731ac090802bb60b53d894000766b1ee4a184000abd8650e40840019bae6b1e81080031f995744c420005b642ae690c404ede5315d2324840155b0518ac8100026f21d43546401c4bec36eaa08a02ad5e7554f6050c0157f06b8ac8100023f60e70d912100576432872124200ced76dc943080011fb0f98ac9a80039e197618c12000576c10a3b1a80008fe87cc560d0801d5a87992c4200023f60f74584500066eba2c6988a000cbd7650d4214001d9ea2b1a4210003b6219434c210006d7ba264b024200aed81d8a6250c0157f06b2081080
  | 21 => 0x51dcd62440019bb0cb9cc8908031f1d57058d210047f43820b226400d9d645cf428c001cb8a632ec690802bde0564506300047f43820b246000c7c755d163484019bae7b1ec2a00032f61276505300065fa1ee8b1a4200e777654521140015df04b82c690803abe096450a100067a40aeca18a02a9bf875526050c011ff0eb18410803f679cd43942400063e42ae8302a600a7d84cc465500019daeca124318002bd60643d91210067ab8ac22864000abd840c764480015bf06b0c6190003ba90b618c120005f4402e890c402ae3c6555143500a1f1a62a1a8490803ada01435844014f2ec18ca9928000cbf74d9131480019b906bb243180032b5917210230005eac1cc898a4200cdd7398e64840019f260382c89894fa74c76450d100067db84e1b1a422ac7d871954348001d3ec8b1a8708003b959131484200053ec086032a8019fc482d8d31484016e90ab9a82880029fa1471d89430047ec16e2b18a800eb68550d61100011fb033b287100033dcc5764c44000576c1483b2264008fd86dd12114001dca65b0a42900031f5db754845000766a0ac69084000af7815d93188001d98c6b2264908033b5c93218141176ae39ae632a80009be8750d21100018feeb382c8988023fe197448450005ec402e29926000e7775dc5644c4015e90cbaa4288003571d773585321563e3aacab028653e9f31d91438401b37b09386caa18032f54774589100047ec08ecaa44000e9d43cc460508011ff0cb9e85080023f61c30d91210073a32aa2b024200e9f7450f614c0018f8caba262a0147ba487628c1100066f18ee6b142004cf671d8450480019f460b90c0a1803375cf62d0931037e3c1a6290c4000cf5745853108001baca3b9ac09080faddd1615042003576432653024200d5c321d56150c011fb0db9287080033bdda7250d2100676b9ac49088000a7d859cf61480014fb0a30ac0a1802be60760981430055ec1820b204000c7c855d060544015f50110ec6a0002d7e157150d30004f7406e89924204cf67158a30840015f501b0ec0a1803374c67650d1000677196ec90c6000cbf41dcd6484001b68e898ac09083f67dd1535814300756b228490c6000de582dc543484015eb0ea1ac210003575d47550d3014f36c10ca9924000a7e851c9618c0011ff0eb28c0909e7e5cc37150d410047fc0ae83026400cf631dc563900019ec623b286908023f61c31d814200576c1060b224206be68190a6048401d3c82b1a821000357cc47558143006daa1ae3a124200a7e8518f64484019be63b9ac8880023fe1f644c52000576c1062b224000ead3159121080019deeca124228002be20171591320053ec16633288000cf581dd943484019f460bb6870803eb7a0c5158e402cf6790ac69942000ced32dc9644c401d3f06b228690802bea024359210006
  | 22 => 0x38286980032b59172192300057ac0ce4b0c602aabd849cd64140019eae230ec4a193fe5205438c9413af4e98ac8a1a4200dcd825cc54484215790caa6c0a18032fd067650d2100576c14e3b1a4000c7c855d94348401daae798ec2a00029fa146258630006f4a90e090a404efc6435093148401f4b03b22849080337dce63589410055ec24eca0a4000ced821d94348401baee7b8ac0988033761973102100057bc22e6b08a43af8f3150d42480011fd0e312c2a1802bbe096398a10035f240aa890c4000ced219d9324400179b0732a6490803f150d424c521024f6c14e1b224200c7e861c15454c015f50030ec4a18023fe1973484400055f420e4b1c2000aef82593514c0019ec62b8ec6900036d55371581430066fb9ec690a4000af581dcb6150c011fb07bb243a8003ba5cb60981210066fb9cc6b142000bb78458f414840157f06b248108002bbe0964909310047f43c84b0c60008fd8758f41140014fd0b322c299002d7215714c9300063eba6a6302a4008fe871516348401b9aa7b92c0a18023fe1d4358a10005bd4006232a8000fc76390931484011fd0f21ec29010ff4205434c2100047ec38a7b0a8036d747554560484f9b72e9b04c0a18032f1d063581210257a40a87b0a4000ead64dcd21080015bb0918ec6900033de057650630286cfb8a86a1262008fe871456290001baac7b8a8708003e5e05438c94100576c14e8b1a4200b6d820c465500015db0c99243a0002bee1943502100047f43ac6908a000df1745c63084055c7ea2b2286280023f6077258c500065fa0ae9b1c20008fe8704363500abdd642b1461080032fdd16458a30004fcc18e090a4000af78150f6148001d6b03ba2c890802bd6043058a100047ec08e0b22644dfa5434cb4148401fa702a1a61080023fa1d64484500071eb28e0a1e8400c5c75dcd6348401dac8798ec2a0002bee1d6018121006dca1ce1a142000e9e83d9143840019dae4b088118002af61275591210066eb9ac62808050db4715c543508011fd0f98ac890002f9e0554486200066fc32e7a1242009f7815d132d44015db0d2124228002bda0373586421b737a8ac4908a000a7d851846050c019dea7b92c8980036edcd425021000746a1ac49888037e5d83195315006daeceaa8cc0908032fe117650720004f7c0ae518440009df835c4504c0011fb03b9ac0210023f61d63d02100058e402a8a9a8600e5f7654d4314001d9b04b1a4220037379cd64942300057c402e8b1a4200a7f8458d5114097f3662a1c80880027ea03744c5400047ec1eec908a000ee63158921d40019dc65b92c898803b31c163484200075bc22c2a084003fe3721c121440578f8cb3b6a2900033bdda42486300076631ec89924200af8805d94348401be6ea382428800337a0573181420076ab1a629088000cdc
  | 23 => 0x59130174be42ae898a8072ecc6358d4248401d6f08b0a8318003ab60a7159020004fbc0ae89928200d9d7350e509000157f08bb286908db5b6087558121005f3c0a869084037e77545cd611486d8fb0e32a42900023f61c53592100065fba4e8b1c20009ed8794a60484015db05382c6908032f5d16318a100066fc1aec9884038c7e8719541480095ed03b1ec2900032fe11768c9410057bc0a64b088000ed543cc761500019dcebb1242980033be097650a100053f42cc4b0a8600cbd735c5640800157b0829ac890003795c5218c2200075bc0a86b088000cbd7650c52504019eae238ec6900033bdd93248450007f0a90e090a201abe58490931484019bae7996c508003761ce70486300067ab8c823026400db643dc56050c0139b0638284908031f9d5649813100577c12e6b224236e77535852114001b58e239286a1143e5885435093125d5fc0ec8a1a2024c7c655c65048001d5b0eb2242100033759773581210067632ee4b0286729ed879d1324840197cebb228688003e3d8d43509210053ec1c8232a4000a7d84d96658c0019daa7b92c898143e98c543509210047ec3c823026400ced329d9214c0013df0ea1a4310003378c573181210075aba286b084000cf665dc543840019bf06b96c898803ab14d43588400077318ec890c4000a7d85985648c0015bf02b92c62a002d92015254521005f8c18e090a2000bcd839d1324840197ee93a2c690802f960465486200065eba2c61042000eac7559121080015df0cba242100023fe0d76151210072f418cbb1a4000bd98399530840015db0518cc1210038f54d6450c50007d2a126290e80008fe878c56090801cdaa6b1242280023fe0971d8d200076bc328698a4200ced325d9218c0019e863b8ac918002bb60830d91210076bc1ac298e4000abd8414d61900019dee528ac8980039d0c465d854016eed31ee6a042000cdd839d9314809d5db0530ac8990029f215625813101ef338a422804000aef8358921140179b8e6b1a4220002bb60a70591321bd3e42aec98e4000dd7815cf424c4019f6e1386c2a1802bea0031d91200065f98ee8b12200dade83145644c001b5ae9b2464908033e84076485400047ec3884b0c6000cbf74591614c8014fd0b302c098803b558d31484500063ea9eeca18a000cdc865cf42484019bac7b9286280023fa1c53586402eef8986e2a1c20008fd87ccb64484019ec63bb24318012bda043058a100074b39a86b088077ead82d914248401d5f04a1ac42018fb98c76348620006da38ce0a1a8200cf7719c76348055c78eab2286280037560d71989430047f43ec8b1c2000eb954d826050c017730932a81080023f61076545300065fa0ae9b0a6400af5819d93188001d9ac6908a010003ab59270484200052f41ecb32c2000cee735892110001bb2ea
  | 24 => 0xc8000aed829866250c011fb073b242a00023fe1d62d85430066e31aeca1a4200add839c9644c4019f4603b286880023f6077458f50006db18ee8b024200dd5815cf42484011fb0eb1a43a0002faa0275486200066e98ceca1a4200cfa10dd9218c0019f501bb24318002b760c10d8d2000576c14ec99220008fd841c163484015bf06b92c8988023fa1c53591100047ec08eca1c4000ead430c16210001d5ee8b2242100023fa1f3158a4000676b12e23128600c7f655c7635000197a82bb287080029f60732994400063f32ee89884000adc8359660484019eae3208c0a1802bde0570591310047f43861b0a4043f948150d414c0558fb0e32a86a0002afe197150c400066e38ec6a1a4000aed820c76448017b3ee8b98c0a1802bbe0963989410065fc3a86b0880008fe870c364484017cb033226490802bda19314854000757ba284b0e4000abd83d914248401d5ec9b928710003e3e09438c9410047fc1ae3b0284008fd878c564c8001d3ac6a1a85080023fa187054d2130e7db08e090a4000ced82dd9218c057ae8e2b88ca90156bea007358a100047f436e898a4000cdf730c164484016ed0b3826290802bd60475d853000556c20a6b1080008ff815cc60508011df0eb10c4a1803371d76350d21006ae3aee6b126200eb7845c96110001b5ec838284908032f61b74484400057d400c2b128636c7c75d9560484011fb0eb1c85080033ddc4315922000576c1662b108000aed829d921500018feebb82c898802ab2194350921004f6c3c853024200add831d7634805b5f50038ac9180032fe117650a300056ec1c42b226436c7c755d921140011ff0cb8c85180029fa167358a100057ac0c84b08a000aed82191618c09bf88c699682908023f61d61d023000576c10a2b226036d75811d563484019bac8b9ca118002dde15734851000767b9ec690c4000abd849d763500077c902a1a42100033e44076486300057bc32e898a4200f978150f424c4011ff04b8ec9180023f61371588500055ec34eaa188000e9e3159131080018f8eab1ac0a08023fe11764c720006d6a1ae42046000ed4634c7604840197ac8b9e8428003a7d8d4350520004df43a8690c8036a7e859d9218c0018fac9b9aa2280023fa1e515923000676bb464908a000abd8414f6444001d5a86b128508003e5e054350530004dfc22ed1928200eae6319142484019eccbb8a86908027b6077250c20004fbc0ae89924200cf771985648c001cd8e0b2a421000337dcd63487501bd3e42aec98a80008ff865c630080019eae238ec4a18033b1d97250d210047ec3c42b246000eaf825cd64080015e906b92c2200039d19531485400257643264b024200add83d9562840011fd0ea12c318003bcd85218c1200066eb9ec7a1242008fd82dd16314001d9ec699242900033d61771
  | 25 => 0x80197ac8b9e82280033d8c576484500055ec24c6b142000eb5435c961100019deed1924228143a7cc54358b410067618ee4b2260008fe87145609085d2fd0e188caa00039714c75d8d210074ec26c6a1a4000cdf739cf644840d5ed0229ec4880023f61e42181310047ec36e690ea000a7d810c0654806f2f90ab84c49880337dce31588500066fba2c698840008fe8750d62840019be62ba6c6880031fdd77058d21007caa1a6290880008fd8715163840115d90ca96c0908031f54f71588500065fc22eca084006ee6619c121080015bd03382c61003eb7a0c51d91303874f98ac6a168000aec825c1644c4019ece6b9ac2200023f61d63d0a10006ceb9a8628080008ef8758862840011ff0eb18a50800337207735891000576c14ec99282008fd8714f60484011fb0f188c0a113b6b50d748c9210047ec3c87b142000ecd8290563080011ff02ba6c6880af1f21572983510067b10ae7b0a80008fd87145628c0015ef02bb26220003275d16314040004fd43ec498420008ff825d931d00019eae2b0ea1180031f1d772591310047fc12e2302a800af5819d931500018f8cab9ec2900023f61c42181310047fc3ac829262008fe879456390001b6f09b8ac0a1802af61053591210047fc32e89884000bcf825c5438c86daeb023aac0908023f6047058c540067d086e6b068200aef825c1644c401d3ec8a1a62900023fe1f63485400067ac32e3210a03797d86dd531d40019bae631cc8908033bdca72586300063e42ae5b226236d6e7554a604840167b0939ecaa00033ddc561502300066fb9e64b2242008fd831d921900018f8caba262900032f591718c02000676c36e4a1c8400a7d810c265d08015f50121ac8280029fa1672591310067b18ee2b1a4000aed8214562900015db0428ec898002f9608544c52100656ba2c43146000aed829c164484019eae3108c0a18027de0573141100065ea0ceca1a2000cbd849d9434840197c82bb28210002f9201424c5210066fb9ec6a0a40009f787544604840157b0738ac810002bea0063d81210055ec2662b108000cdf731c163484019bae7988c0a10032fdd163581210057bc1ae4b088000e9d64d8d43484013eb03bb284988033d5d1614c45000766c36e4a1c640087f865d531140017d100a9242900029fa1463581210057d406c7b024200aed821866250c019ba63ba2c708002bee01649813100772b1262908a000ecf8258d32840018fecab9ec2a00023de057650c500047ec1eec90e8000ade809d563d08017cf02baa43100023fa1c6458d2100576c3264908a000e9d6350d41d407dfc4e290c61100023f61d644c4502a77490ac49842000be5819d132484019daed21242280023f60f71591200055fc1ac8a10a000cbf74591638400157f0ca1a84280033d14f7159130005dbc0aeaa1
  | 26 => 0x2bb60a73d85200057ac0860b0880008fd8790563c8001d6a8798ac22000337cc47650d210074eb1a87a08a038e775358541140019deed21242280023fe0572d8d40007d4b1284a042076bae8619142484017cb022a26490802bb61f31588400056e41acab024206af68114d61880019bae6b1e85080033ddc961506300065ec3ec9a1c2000ee54258531c80011fb0f10ec6a0003b360a7158c200247ec3ec32824000ed763dc543484019bee739ac890803761cd704863007cdec26e2a1c8000afa801cf64484554ff0eb28caa18033b4c971d894300676b9ae2b108000cf5865c66250c019dee5396c2a18023f612764c5200067d082eda0c6000bd583191314846dad8eaa92c090803755cd31981210055ec20a7b2242009f7815cf40840614f90abb284989a72f5cd6450a300055ec20a6b06840bd9c7350d21100011ff06ba0c0a88023fa1c61581430055ec20a6b122000a7d85987648c007f8f0698a4210002af61331d922000677192ec90c6000ced721cb6150c016db0428eca9000337e1973d08500056ec16e6b1c2000abc815cd6408055abd063aac0a18023fe1171d8e200073b40ecbb0a4000a7d8190c65500019eb0cb8c85180033be1d62189430047ec3ec690a800097d870c465500011fb02382c7a10033dcc77158343006d6aa6e4b028620f9483dc543504011ff08b96c708002bd60754d85301f7753024318040008fd87145648c0015ed0c3aa42880ab4f61075585431be3e42aec98ea000aed8214763480017cb0338264908031f595721961000677c3ac52142000d9d7450e624c4018fcecb88ca900027721d435453000577c12e2b226400cf77458531080a797ee3b2286880023f6077650c500047ec0ceda146044eda535806050c019eae3b08a0980023fe09765045006d6f418cbb1a80008ff8758d21d00019ece7b0a42a00023fa1c51582320066ec3ac6908801abe5829913148401cb8cb18ec6900029ea0243195400053f42ce2b14600087f87594658c001be501b8a87080023f61e41181430047ec3ac82926200e5f54d8f53484011ff06bb28508002bea0253d85200047fc3ac89942000eb57450d619080197ce3b228690022bda0453d8121007f098ee090c40008fd87d8f20840014fb09988ca90002eee1943902100047ec36e2a1c8400bb8805d543900011fb07b8ac121003f84c8704851014e3ec30eab0a6430a7c8558d4248463de4a2b00c0908027ee1d60181430057ac08ebb0a4000e755358521140016d90ab9a42100aab760e7458c5032eed086e690c6000cbf7498d60484099ece2b14a108002af61051592300065fc22eca1c2000c7c65dd1315000156b08182c2200033bc877358a100066e31ee8b1a4237c7d8719531500011fb0f98ac4200032f5d26118a300063fb2ce132a427bdad84dc94350
  | 27 => 0xf43821b1286008ff87589418c001d3d09b1a8690802bd60430592100055ec20a3b028600acd8204163080015790ca1e8490802bde0543d8a100055ec20a7b224000cdd7318c644840157b083aec89080337e1d631404026e7bb1ee2a1a42008fd84dc96314001d3b09b1a869080337dcc53591210047ec1cec2942000aed829d9214c0011fb0e182c3a100337cc67650d1000677b96c498a8000abd840c3625040197f0eb2081080023fa1e21d8d40006ceb9a862928200abd849c5644c8011fb023b286900036b50c70509210055ec2662b148000cf465dc543484011fb033b08518003375cd63d09210071fbb2a8a1ea000aed829cd64484011fb03386c4a1802bbe0964486300aeeab8a873126200aef825d9218c001ae8ebb0ac2a1802bb60a41d8e20034f7438ca90c40009ef815ca3008001b6ca3ba2c0908023fe0576d0a300053f428c3b1286009fa87d9130840015db0538ec6a01377518f7150d210047fc0aeca1a42009ed81dc943508c79dee7b1242980033bdc96158143004f643aa690c404be9f3150d61900113dd0c38284908029fa1661592300067cb8ac03028600af582cc761500019baeca18a4988039dd9731d85400066fb9ac69042000cbd41dcd64840019bae731cc0a08023f60f71580520067dbb4e090c6000cdc31dcd6284001bb6ea38286980034f9d543989410056fc1aec98e40008fe8794f624400195ee8b124220003b55cd43584200053e42ae1b0a86069ee87d8d2188001d3ac8a1a63a80033b5da4248630004df43a86a8c8000be78150d42484015bb0638ec690003675d143149310047ec3ac62942000cdf73d4d62440015eb033aac8988023fa1e31d91200675ac26c2a0a8000cbd7650f42140019bae6a98c090802b760e7558d21006ceb9a8721282008ff815c86055001bcae2908a110003375d17158c200267cbb2c51842000ecf325c9631000197a823b286909e3b51c76350d210066f38ae2b1840008fe8758d21d40019d8ebb124298002bbe09764ca100056fc1aec98840009ef875886250c558f8ebb2ac0a18023f60b7158c400053f42862b244000bf18190a30840011fb08382c3a98027be0572142200047ec26e2b18a0009ef8754d21880019eac8b88a4988033d98572d86300047fc12e2302a600bba809d54390001d5820b2242100033d5c7618c1200065fc22eca142000e9d43cc660d08015df04ba2c690802bde0565d81430057bc0ae4b226200cdf315d943840011fb0ea18c0908023fe097615131004dec3a862808000eae815912108001d6b04a1ac220002bbe1f315884000676c16eca1a4200aed82145608c8019f221386c2990031f21574181310047ec3cc23028600adf835d931880015bb073b262900038f5967050c40004fac08e0aa24200dd980dcd218c0018f8ebb1ac09080
  | 28 => 0x1d8630480219bce6b18a1a0003795c5218c0200072f32a869884000b5c835946548401af2613aec708002bb6081058e420075c432872022000edb631c143500011ff0eb08c0a18031f21572181530065f20ae83024200a7f8558f6048401b3ee8a1ac098803b9605624c4400057ac1ec290a4020db543dc543504e7da8c6b1e829080337e0d7650d21007f0988e090c40008fe87d896150c019eee218ac8900026f613764c9410056fc0ac6a18a000cdf865cf42840f19bae3b1a869081abba18754862029f4f98ec8a1a2000dd5735c6604c401d1a8798ac420003971d77358d21007cca98e0a1c8000e758119761500011ff06bb243a80023fe1d43d8a100053f428e4b1c2000a7e850c762500011fb053b2650800337e0d764ca10007b2a8a4228440008fd83dc562140011fb033b4a090037a76136350d400056f430eaa1a60008fd8790f61480015bb06082c721002fae1d218c220007cbb1a87a0a4200cdd645cc508c00175b07b2284908023fe097650c50006d6a1ae42042000ead6450d21080011fb07ba2c3a8002bee017259131004dfc22e69088000c7f751c1644c401d9d02b1a42100a71fd45764c85000576c1462b16a000a7e85985628c0019bae6b1ea1080036d1c57250d4114e3ec38ca9928000cdf738c564480013f501b9262900031f54f72584500066fa8ee6b12202ae3d8419543480adbe2e6b8c61080023f60b7158f400065e28ee8b122000aed81cc96210001dcb05b0a42a0003374c47650d100047ec3c62b204000cf6315d9218c0ef97ae3b2284908033794773589100055ec3287a08a0008fd831d951500015ef02b2cc0a18023f61d63c82100047fc22ec990a0008fe870c361500011fd0c3828690803c71d55350e400067ab8c623028400d9d7350c50900015db0428ac12100337617735891000756b22e69084036f658119552484019eaec98a42200023f608705935100756c24e6b1080008fd81dcd60908011fb0c382a6908026f610704c9410067bb9ae3b224250f8f3150d4248401f2a8698a43200023fa1e53589100074e41ac8a1a4238c7d87195414800193ac8b9e85180039d195314852025fcc98a8720420008fd831c162d50011ff02bb265a80de9fa16764c6401b6b6c10eab1a4200d6c754c9604840157b0931cc8908023f61d32181410067b18eec908a03dfe231485308800157b0ca1e8508002dda17424c5210053ec2ec6b14205cced7158a42840011ff0cba26390002b7e0d65981210065ebb286a08a0008ff875946050c011fd0e29ac9080023f61d64486300053ec34a232a86008fd8758f4214001d8c62b1a4210002bbe056218a300055ec24eab24200dafa809c763500011fb09b9ac228002bea0221d8d20006b6a9ae42844000b768599131484019ef02bb684988423fe1d63143400047
  | 29 => 0x9e81080023fe0971d8d400067a98ceda1a4200de88748630880db9f6c638286a00031f215764c72000eeab8a8730262008fe87947644c0019eeec98a42200033d591719093113fe239a6490a2000cbc8759143484019e8633b262a0002bbe0953d89100056fc1ae2b10a000d3c651c15450c015dd043a2c3180027e6047050e400047f438a7b224000cbe419d94148001f1a86a126390002bd6047258e10035f3c1a6290c4000ee5724c961100019e8e33b28708002db21563509210065eb22e228040008fe869d94348401dce62b126220003756057315121006af3aae73026200cdd73ccb64840019eac9b8a8690803bc589718c210006ae318eab1a4200abd84041644c801bb6e738243180033d5c761141400057ac1ce0b0c8437e74505cd611480197a86bb285180027d607744c9410067dbb2e090c60008ff815d8544c81fd3cc738287a10027be1d43484200063ec38cbb1a802ad5d635ce54140015eb023aec2a1803b3905634842006e6e39ac890c600dcde73d8c50500015f50018ec0a1002bd6067458d21007f0a8ee090c4000eb88050e60d04011fb07bb24220003b9189614863001d72c10eab084000bd9831d630480019eee338ec4a18033be1d6208210006d4b928020460008fd875914384001dd2c4a1461080023fa1c535912100756c0ac89084000aef835912188001f1ac8a1c6490802bb6086458e101853f42ec6a142000ecd6348630080019bee6a9ac488003370c573181210067739ac42808000ed7735cd61908019bee739ac9080de5f2157650931006ed406e690c6000aed864c921d40019dd0db9287100023f607735912005e5e3b0e0a1a8200cf6319d9214c01fb38e6a1a43200027b61c544c921006ae3aa86b126200c7d8719761500018faa3bb24228002bd60e70584200053f42ceab226200ecd8458d21080013bf06ba243180029ea0243195200067c3b2e0a1c2010ed77158d31d007b9f4e0b18c5080023fe1970909310047ec3ca7b024200e74511d76150c6dced0232a4290003b58c763485200065ab22e22042000cbd741d1618c0011ff08bb263a80023f6137358a100055ec2664b088000cbd419d943484019bee7992c508002b36085158c200067db84e0b1a4250e9f3150f615080197a82ba6c7080033b8c972d8d410357a40a87b142000adc805c563d08015ef02bb263a0003ad61332584400067b18ae5b0a8600cdd81dcd624401b978ecb8286a081abd205535862026ef2996e2a1a4200dba80dd121900011fb09386c690822bb60875587200067d43ec49842000cf686dc543840011fb05b8ac918002b760f42586300055ec20c73024200abd849cd628402137d0c382a8a18023f61c10591320065e3b4c8a1a4200fc543909314840157b0818ec0a10029f60c61195400047f43a86b084055ef27
  | 30 => 0xa100047ec0ee6b1220008fd8704163c80015db0429ec290002b7e097158c400047ec3ca23028600eac8650d42484015f50028ec6a00023f61f3158b400056ec0ec6a1a4000cdd7318f61500019bceca1a62a0002bea0063991210065aa1ae23028400a7d8190c6548001978e3b2286900032f5d943507200078ea9a862848000a7a8088465500011fb0f29ec5080023fa1b714c9400075742a86b108051cf9619c3218c0011fb053b287080033e4c07058d210053ec206232a4000af5819c163484019baedb9a43180029f6123199420005bd404e632a4000eae31591200800157f0f18ac810002be20163581210047f43862b22404ede5315cb4348455cbb0632a86a0002afe1943102100047f436e2a1a4000f9b8050d31900019f4603b2869013fb520543586320066eb9ec7a922000abd848876250c011ff0ea1ac2280023fe0973181411bd3e42ac898c4000cde7158d4308001dccc3b12431807bd960865545210067ab9ac22808000a7c85591604c4eb75b07a1a8490802bde057650c50005dcc1cc92042000cdd63dc931100019dc65b92c708002bd60742586300069eba2a628480009f8805d94348401cb8caa9ec0a18032f9077458a100047ec3c82b184035afb8158a30440015bb07382c8988033ddc621592300047ec30e09928200bd7815d5434c0019d8a7b92c8980023f6077650f500056ec32869884000add83dd763500e9f8e21b1a6490802eb60a7050d420051ec34a8a18a0008fe8758d21d001b9bcc7b9a8108003b550d614c4200057bc12c2988a000ead4358932100018fceab26c318002bb60a31d92201b53ec3ecb32a4200cf7835c460508718f90abb282280032f5d86450e1001cf643aa43024200cbc74d8d60484011fb0db9a83900df972157158c54004dec3a862848000abf845d931480019dcc6b908108002bd60764486300067b18ae3b246000c7c65dd131480019bb07bb286908ab1fa1c6550d200066eb9ac428460008fd878846050c011fb07b92c2280023f60870591310063f32ee2990800087d870c465480011fb063b2a4a00029f61671d92300067a432e32146000dd4715c1434c4019bd0eb1a422000397195434c5400076bc0a86b0c64008fe87cc762500015bf06b2ac09080337e0573181420047ec3ac62142000adf835d1638400157b07ba2c8908023fe0d71181420047f438a2b1a4000cbf41dd163484019cac4b884108003e960943d0521005dc402e4a1c8000cf764dc5434840175d0da1a8490812bda0463d85200057d400c23128600cbd65dd16048401d5a86b126220002be201615814306d6f41820b246000cdd7350c6054801ba8e23928698802bd60f74584200066f43ec6a1a4200e9e6319143840018fee63aac6908023f61b735042031d76c14c33026459cdf7158d32840219bcc6b
  | 31 => 0x8200aed868c921140014f90ab9ac890803375cf63d0a1000576c14e3b246000a7e86cc465500011ff08bb24318002bb61a75484200065eba2c93026210abd841d563d00019eee320ac9180023f61f63d09210047fc12eca1a4200abf845c363484018fd0c382a8a8802af61073d9121006f9b8ae0a1c2000ed5718c763480017d100baa4310003b69c07058f4227fe240a8719242008ff81dcd6444001be0e2b828708002eea036550e401c73b408caa0a400d9bd849c36150c0197ceca1e8508002af612735921000656b26e4a1840008ff815d9428c001d9b02b1a42100032fe1d64192100066f98ee8b1c2000add849c56308001d6ce6a1ac2200037ca017190a300076ab1ee2a1c2000cbf764c540100019eee320ac8990037360973d09210066fb9c86b242000a7e868c465480018fcec32a6290003374c77650f210057ac0c843026200dcd73d8e42484cbbacc3b9a431800376dcd70486300065ebb6e89088000cdd7358c52840019db053b264880032f9d964d0d210066f40ee6b122000bcd81dc9438c801cb86232ec6900033e8c37650e100065ea08eca1a2000ed4639913148401f1f04a1a84988023fe1d43584200063b30cebb0c6000a7e851d163840019da43ba2c50800337cc67650d21007e3c0a8719242008ff845d8524c40157b093b282980023fa1c3058a100076743ac69084000cdd839d931500015eb0c98a4220003375cf32181210056fc1ac8a1c2000cf571d8450480015ef0e992c220002bb60a75d85200063f3aac5b0c6000e9e63d9143840016db0b210c0908123f61c3058a10006af3aa873026200b7a85dc630480011fb0f990c0908023f61b724c7400056ec26e6b1c202ad5d831d56150c015f301314c098943e520543509310057dc3ac030286008fd878876348001ada643aac6908023f21d634844000757c22c4a142000aef825d932100019bb073b2869080297a177358e1000752b2262908402bc7e655ca508407f9deec90c60100de9fa1b654c5400047f438ec90c6000f978150d424c4011fb0f992c3a00033bdca7258e100067a3aee2b226200cbd439c362504019ef02bb286908023fe057650f200066eb9ac72142000adf815d163080016db05298ca90802af61030587420055ec20c6b024200aef81589428c0019bee6b1a422000ebda0543584203af4f98ac8a1a4200cde435c763480011f90ea1ac3900026fe1173486400063e3b0ca98a8000a7d8518e60484015bb06082c790002b76067058c540072eb1a86a88a000abd849c5648c0015a90ca1a62908029fe15611814307cdfc3a87b0c8000af7815c9618c0017af02b828698802e7e0d7550e400ed4ec20eab1e8400afa8014f6148087d3ec2a1a8298002f360e644c9210066f21cec98a8000cf47358521100011ff06ba0c090802afe0d64d
  | 32 => 0x19eccbb8ac0a18031fe157650d21005f8402e6a0a2000abd8414d62840a59eee6b0a43181777598f7150e1000676996e2b1460008fe8714f61500015eb07ba2c229003ab5916250a100067a98ee4b0c6052ed473585218c0015f50128ac918002dd215744c521004dfc3ac83224200b5e859c9434c40157d0ca1e8490803375d943909310075bba2c29088000cf9641c1548c0111fd0c382a4908027b61e32981211563f438caa1a80008fe87145628c0017d307b824310002bd60473d8520004fcc18e090c40008ff825d94384001ecaa4a8ec0908033e1da7050d101b6bb438caa8a42008fe870c76448001d5ac6a1243a00033bdd931480202f76a38ac6a1c2000dd5815ce64484019eee330ac89900357197735453007e6e39ec890c6000cf7719c5648c001d3b09382c7a10023fa1c30591210043fc3aca32c2000c7c7558d6048401ec8eaa9242880e38fd4d64504500063e32ee498a8000ced215cb63840015f700b14c098803abd8d42485401ffe239a6290c4000ecd634c921100019f700bb28690802bb60871d89430066f43ac6a084000cee325c76250c014fb0ca1aa2280023f61d431815100772a12c290c60008fd86dd132840013f30238286a00031f60f76540500067cb1ae0214204af9a53dc1439006f8fea8bb0a4988033e8437358321007c2a1a8498a42008fd81dd162140011fb0db9262200db1fa1c65485200057d40483b1a8000dad7450a60484011fd0fb22c690802fc604654c210006f9398e090a2000abd878c5640809bbcc65b8a8690837379cf63d85400053fc2ac63024236e7476545211404ffa10690c60880023fa1d4358720005dc402a8b028600cf771885644c8013bd0ea1aa298013b960b6148520007e2c128698a42008fe8714f625000197e83bb28708002f560c544c5210047fc1aeca1c2000c7c75d9163484552fb0dbaa86280032fd0d74d8d210072ec18cbb1a8066eb743585418c08ff4c62a1242a0002b360a4158c2007d5f430eaa1c8000eac5159121080015bb0918ac6100033d5c471d8d40007e3b1a65a0a4200add8650d311400197ae8b226228142eb60a6450d210047f43ec6b0242008fe87147624c0011fb05386c2a18023f60773588500055ec2062b148000bad811c943508011fb0f212c3180033e8c37158343005ed404eaa1a6000abd84d8f428400197c63ba2c488002b76067058c200066fb1ee4a1a4200e9f31d9143480011fb0fb1a85080033761973082100047ec3860b0e8000cdd731cd64840119ece2b0c61900029fa166358a100046fc1aec908a000abd840c76488001abea7b9a42280023fe1d64d8e102865ebb286a1242008fd82dcd6114001d6f02a18c0a08033d4c7715913000757c22e2b108000afa801856050c015f50028ac7200033d98574d86300057c402c6b02
  | 33 => 0x6e000000c01a00520600000020060010450000062000821402000400d8120062023000000c02256900701400040680038074096036001011c05205b00000680001e0007001c01800000180380d800900602a42a6000040800000a00300300040e0001001000000e01100080a400606d0078a9c2e2004004008808400051580140d405100100980060b400d8dd407603900c80e80320190050688058005006002000000200b005c00028401900d400000405d07b800000000000640020051710004002001000803000400800100d000800c00300dc000008048085807600a0090010012008000804400800005e002c3ea004079801801c000000003c00000c014001010a01600380500002d5038800c04400c01d00000101bc00500005ce0330040000002012006028807400d0b5800c0086a104080d80020eb000000005a04a00280a80c0497002006c00c00a001000c000000006025c000002002802c00000800c800800000d00c006c1d8000019800c0dc01000981c80180010b280100e010b02d803c000002013000802e000025800008410100100f001200f0200054000004015001000000800280140100342b4001401000b011005404a0000000c6c0fa2bf006008800a02406000d4018000000000000800a0040114028000002812c6dc1b600b0a9c06246e000012c00a0e0006000003c0030c6002c000006035800002a00800d000000200000000080b404b006008401813001a8000204000002800c0e60500bb809007a04600100240021e4040a4e014008100b003001c01d049808002e012002802400000c0018028010000000000c01200200001f4000001000800404000f006002400250d00702c000a00004580000d800700000c002200100480140120fe000007c00a002039001c77800400981000a014e00980300e4003003006401202a01e8e6404a04803600e4b30003011810043201600781d007a08f3d70031f5d875486500053ec28c6b024200eae8050d62100015bb0638ac9180023f61c53d8520007673aac690840008ff865cf41140015f30c2146108002bd619314875000576c1063b028400cf9105cc604840157b09990c0a087773e0973d09320053f428c7b0242008fd815d3634400197ee9a9ac488003b98c564486200047ec18ec90a8038c7d8719541500015df0ca1a84909caf960d424c5210065fa0ee8b0c6000cdd8758c50100015db0530cc5180038f99543504200074eb1a86a08a000a7d8390665908019bb0cb9e85080a3ec50d418c1100047ec3a87b0a4077dad72d92644840197ae9b26c690802bea0243d85402ee7ab1ee2a1c20009ed831c142484015f50018ac5200033d4c476485300047ec36e299080008ff8758f42840015bf06bb263200032f61f6450e100056ec1ec49942000ced62dc532100
  | 34 => 0x19800c01e005072000800e006000815c000005011811807414701880200020060088008080002000800c008983031028c0061e6007808400000500080581dc000018804c00201e008813403c237048804c030000003876405003900c000047c0590008bb803000202a80000180001a10010006004006019c00000c017003000400103f800015400000009a000c034034812801001d001000410000003e000000e010000028828a00600280040fa000006801c0140000340000002012000801c04002300106a800c01b00b005c05c00800a00480040000000018194000003000401a04014480000221b90000000002000000001c3a4006004004590201c00400840b002c036036c00000b00081f404006c00e807c00a0070f0009805001c002809004a01d001809800a02300808a4018170001000402600d00000000800a3002926c0080000010068000013002009001000602c800401600a007800000201801400140860070208008176000008046401c004006048000002b00f004c05e00601b807c00001302705bc28615501a80c804400002c801002c00704f0020000000006001800a04601d803400600e00000c4010013004853800a000000000402a04f01286680a000c047090c00002c000006804803d0060000002028002005800001b01f816400001f000000000000b003005802a001000000003003901c01e0084000001800c0b8001001800400602704381b400800200d80000720350330048000012001813c0060cf000005c50801600a82f8078003017000001a06501201fc0120010370058002003000002000e03f00100ec00603a002800405209d007000c01200706b000c20a00000d84ec1ee00b001800005a05800d00000020092d9809807c038020804401400c00001d0006001000800401201c004006000600b029006c30a00600180140440c100200001520140028164cc806c00600e406a00807d80ec00000502500ac00404001e804c00000600b80140a805e00b00b42580020fa03d0018000016952402a007010007c00228d0020ec829006d01384c4aec009000009c08200008d80200a200001d800000200c01a8000024011003000c35806405b058c764005000003c75a02800080cc0005ee067003800004a002000c01e0110008b1400001d00009cc00200e11c004400200e005000804a00501c823000006800a800511a000000802004c0170000e24002006040001412e03a0e2800001094d05500500b205b001010c1ea00001d826c014015000025026a021000000000400300180000000230009bc400c04200a003400400400b007c05a002000000001a060118801801a01903a801001e00000080dc1e000003e801401a00a02000800120a600180000ae001004801c0002d20003d0403001b00280306aa0910000098
  | 35 => 0x8800c000002000000c01e000000000405c052000806c1ae01100187c400a0c000b000000a006009839401e07000b000c13406a0008560000001000001000a00000b00a0010003000000800000000000c408a0220060230126000038028c03a15c00a800400203c4a90000b080850028018002080059809802601202a8028014014000000400227a02f008800c00c003800000005b008004402e00200004ac010001002800400200a18c0000e18011047803000000000280f000000003c80000000510010000fb4000012800803200d00500640000550090b8006e02e018000217001600000d40b4127002000c00400005a0110012015002001c0040100028000b3201e008000000201f001809c058029012001c05802400000440080590058000042001000800001600a01b00140be04d005802c52806d001010801a000141000007a3b4008005801916d08601385080000008bac00400f0bd80040cc09200400c80060d502a0044058037039028c08a000000004000a4fb0b98398142000005003400200a0bb0e1c0420020178318024063000008802803a049806801e012008001406a000000801400a007001800029008304c0840002c46001845c00607100000c0000208002014c000009000003001803001f000400e0020250000044001067014000601e01c000000a00b07b000c00005502f01687b401c02e008c05400d000000007277c002000000400203c0a140180000711d6c06e00c00080000102e70048204000018001800007e00700000cc00a018001000000003a000004003a00a3b88038014000002000c0c200d00001480c616404480642be00001409f000400900180000060000058000150017000003800600000300083fe06901e029c4bc00e002006024e00000f000402000d02900dc00000b00917f4000003000000c73075400200040a800200014442120062380000000010009847000203d074000023c006000001c0100000010000018013014000800a0010048028004038000000000403e000001c000000002000c0389500d68610110015058000c01000200000080000ee
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc014d5919d76350d21005876503119763480018e582dc671592300061ee14805d943484014ad9498d72102100062e1d08058d60484010df985cc73592100049766031197634800161d9414c65d8d2100527e5d6350c40840019d0712017150d300070d59351dc543140014ad949cd62140400052b64851dd1624400187685dc461581430074555153dc56050c0189d84dce6358a10005996483119761500010ef985d862486300053ca4283dc5644c001cc5324c4764853000539e4565dc96050c010df985cc73d85200061ba17721856050c018e582dc461581430063518d811c14348401d0d5454f7258143005d8241525456048401a968350e705844000437e6176dcd218c0018b5845c431181420062b65c8650d42484014d59119773486301554725d5454d6050c0183f75e117058d210053aa4031dc9644c00129d989936350d21007a164d644c5210801b61c96551535814300599648511976150c01a8d8318c6450921005a5e456350f41140010f7985c47159132005a965062585218c001a979850d614c4400052de4d645c44084001b60752015248510006a961261189218c001571951cc7048510006a398d82191438400143d950c774589100052b65053dc9644c0011e597e05439092100539648319d9315000183f742156358141006b121a8250d3148401954732157348510005a624154d8d4350001c95414c47650d210061d1d7815d163484018ad841da7250d21005b824152d85214800145d9714c75d8d21006172177358d60484018e5825c471d8943005b164a718c763480014b59414f7159130007985495158060484018ad76610624863000729591714845008001cc8764ca70485300063361d6348450080018eb822017650d2105d27653865cc4084001c8e7350d6214040005a5650634c7604840186d85dc8615814300627613730c562900014f0905c471591320049d660311976150001e8543589314844000725507311d943440014ac9750d42587200053ce45701c1644c40149d940c571d8d20005a5650634c560484015949750d31486400052b65073d8921500018bb842017650d21007314ca311d9214c001c97975cd43584400055564c411d5634840164c9561d63484200052d65065dc543840017869650d424c521007318c521dcd628400147695e1b71581430063960b71985648c00191e972015454d43006176177318d60484014da9021973d09210072598d435c440840018f0712017650d21006a56508650d314840189f845cd63d0921006a92056450d2108001d46328c47558d2100786551535806050c01a978350d7258440006a94c48650d42484018d973a006399121285e164a6450d3148401e879650d424c5210073158d7148630080014e79259171909310043ba60765c943484016c69758d3148420
  | 1 => 0x41fa5c8558d60484012f29021d43586420052d6507358521100012ae96a1943509210043ee61701c36348401475950c5711814300671a45831c1424840185c75e0d72591310057125d434c521080014b5940c77159230005336487158d43080018af7661062486300053c241865c66250c0183c75e117058d2100639609711866250c0756497549511812100617dcc85591624c4018f371a0061581430072558d435c44084001cc6324c47650d2100437e61731cf64484014e5920c57118143005b8a5b724863044001c8e6350d72102100064d1c4855c543508014cd929c5638c02000517a5786dcd60484014cd92a07735891000732840764c9214c0018eb72a006158143006551c4855c5434c001ca671591218c0200052b259431c142484014b594a0d71181420053364831dcd6284001a9486591434c5210052d65073d8521500e578594a09434c521006b12198250d3148401c95414c47650d100060fe177458d6048401ca5645c5218c0200051b65431dc9644c0010ef985c872d85430060f6177418d604840107f985d475d8520006e42048050d414c00185f839d562981310061d217815d931d0001a2c855917348420007235cd4358850100010dd9819773486300059964a81d9761480014d89061f6350d2101d3964b8758630080016c49650d424c52101cb96488750d61080018ad87591218c02000627611731cf64484014cc97611634842000599648511d76150c014b79750d6114040004b52614358531c8001a948350d725844001cf8261521c121440018d4875cd4358642004ad261435c961100014b5949977150d210061b1d7825c1644c40185d86d4f7348450006e12048250d424c4018d48660573d0921007255d9434c521100018db832017650d2100556640321d56150c01559951c47050d300043de61711c763480010df9360676941200062bdd98219143840014cd929c563140200061d217815d943140015c5921c57050d310067160e311c142484018e5726047258e100043de6176dc543840018e5825c461181431b559e5d5254660484019a5811c47250d420061edd4805c9644c40189d845cc311814200659e1d5254460484014af9359172192100062ba5c8650d42484014e8905c872591310053964a85dc5644c0014cd929c56350c20007a150f3158931100018e582dc431591200052ba5e3159120080010ef985c8725863000533648315cc60484010fa981d970486300052e251701c16348401791912014350530006b158f8150d210800186c85dc9615814300636dcc8058d60484019d073201734851015547e5d5454e6050c01c4f53dcd62484500061bdc885585604c80107e9721563581410050fa5431dd162440012e596e0543484200052d650835c460508016c49161163484200051d65c511d76150
  | 2 => 0x4017398985507050d3000539e497458531080018f171a0061989430055c640411d563484011e5989cb7150d210042fe617619143840010df93618705512100725a0d435c46050801cc67158d21140200063358d81dc943080015c9921c47050d30006e150c80509314840164d920c465d8d200062be1d6448630080010ef985c87258e10004a7a606458d43840015949750d31484400052765f6350f424840186c75e097058d2100563e5d6450e324840107e9819573485400058d2558750d61100014ad929c56450c2000571648719c9434c4014b59750d61140400061e1d7805c9644c401aa564e0543484200052be5d4358850100018cf8758d21140200053c24186dc543484012e69818961486300259925952545604840149d940c6764c5200052d659435c4408400189d845ce63192100062d1d9811c14350401e8543605624c4400042fe61741d1618c0011f2981c57050e10005a924583591210800161d9414c75d8d2100674604711c1434c001bc1834c8704851000527e4d65dd160484018cf8758d43484200063960b71145644c0013c593201424c5210052d65283dc5644c0010df985cc7358a100052be4d645c84084001cd0314c171181430052be59435c840840014b8905d07458d21007340c5105cc6048401c957350d7258440006a3cc48650d424840149f9758d43d0a101b65921d525456048401e849650d424c521005b125943909314840147695a0f71591300043ee61701c1644c40185c75e0d655812100627613730c56448001ab086a0143505100041fa5c85585604c8018ad7460a6118a3000476a60735c1218c0010ee980c7725913000437e4d8759121140010dd980c6764c5200052b65031dc9644c001877819d564981310041fa60755c163484018e582dc671d8d200052d64f74585211000129e98d916350e100062d613710c564880015d0935d470485100062d61171cc460508014cd92a05731814200639609710c460508010bf985d07458e1000533648815cc60508018cf736083158a400052d6527358521100010f79161d4318152005a36486458d4384001c5753dcd614845000671645831c142484010df985cc73591210043ee61701c36150c014d5939977150d210041fe61751d5648c01f61e961d55350e4001d7825d321c121440015a79760943d0521007251cd435852110001a958350e705844000627613739cd64840012e69890961486300053364a75d8d43484010bf985d074d8d210062b21d6450d2108001d477354951581210062b61d644845008001c8f7350d624844000749dd15254560484016c79161163484200053964b635c6428400178593191424c52100647e1d5454c6050c01e878359131484201dcb964a80dcd619080189d845cc639912100725e1d7350d611000147695a1b7150e1
  | 3 => 0x2100671208715c1434c4014d8906197399121006276137318d604840145d950c573181210042fa6076591434849329d94a037158f4200536241731cd644840189d84dcc535912100627dd1839d16348401695932116150630007259cd4358450100010f5989db7150d210052b6507358921100014d89061973d09210061d1d7815c9644c401a546321563d052100539648315cf61500012f09061d43586420042fa6031dd162440014b7945cd614844000559e5d52547604846d5649754951581210062761173d8f428400147595e1b715814300627613739cf61480116649654951d81210063960971984628c00183c85dd16358121006b12056350d21080018b874a006358121007a158d424c521d000189d84dce7358a10005a9e4583591210800107e98195744c5200061ddd7815c1644c40159a97d91434c2100053964831dc5648c001c947418d315812100617a177318d60484010ef98dc861581430052b6487159143080010df985cc73d8540005a125943509314840187475e0573590500042fe637414d6244001d1741cc47558543006171d7835d163484010ef98dc8515913000536a4281dcd62440012e698d8961486300052b25d6350921d0001c8d6350d7210210005b16468058d210800187b75e017458d210063358f815ca30080010fb985c07058d210063ce04805d943484014cd9219773486300043de4587cc96414001a9781cc56450c5005d276508758d21100014cf925d1634c420004a7e6164d8d4348401476959d77159131006b1e0e3158921140014ad929c5648c0200043de61711c5628c0014d5931977150e100052724d65dd1604840187586d477150c500061bdd7825c1644c4010df9361e41588500064d1c4855c54390001a8f8350d7158840006551c4855c5438c8018ad766086450e10006a320d435c562100012ac9850d7158840006171d7835c562140018e7726067259131006c61d480551434c0018ac87d9143486200042f2617650d211000145c9561f6350d210063960b719c5628c00149d96dcd434844000617217835d931c800146e950c772591300051d65683dc5644c0019997460f428c2100052b64831dd1624400189d845cc631812100574245751c1434c00145d95e1b73581210062edd28018d604840189d84dce73d85400041fa60755c1644c4010bf98dd063581210052b25d8359121080018db73a006358121006276137314d624400186f85dc961581430052765285dcd624400185c85e0d7650d210052b64a71590500800161d94a0f65d8d40006335cd820c460508014b69750d61484400067460c731c12144001bc23160c70486200057125d434c521880012d696a19434c521007a1591434c521080014cd921c76350d200043b25d8650d21080a1b858450e424c521006b1e0e32585211
  | 4 => 0x480010f79160e7694140005b1a468058d21080014e8925c070591310072550f31dc5648c0014ba900c7745891000479e6172dc5434840199543604705093100539648835c460508017849650d424c5210043d66065dc543840010fa981d97050e10006ac8c08650d414400187875e017458d2100517a5681dcd6244001aa6312194350921005b1659434c52108001ae162606428c21000517a5c631d563484010f5980c6764c540006a521a6450d314840149d942057318142007a1d91434c521880014cd92147735891000555245751d5434c00187b75e0172591310052be517358921100010f6972056558143007a1e45435893110001ac79860563484200052ba5f3158940100010f7985c47159230006176157318c60484014e7965c5218c0200052b65d435885010001875855c4611814300437e4d82dd161140015c5921c77050d310058b2558150d6210001c97414c47650d21006352077350d6284001a4c6321563509210053525d634c521d00018e872a00615814305e6621c8050d414c001cc5324c47650d210071558f51dc54314001966972015254521007a118c6450931484014ad9650d72102100041fa5c855856050c0187585dc461581430043de61711c7635000185f85dcd63581210063960b719c763500113669620152545210051d25586dc543484018ad646077250c20005a565273cc7615000145d95a077358910007a150d4258531c80018b584dc43159120006275d1831d1618c00183c85dd16458131006b16118158d21080015b1941cc704851000527650315cc60484016959418e644c5210052b25d4358921100018af87591211402003599a587554521880017609054951981210053964a83dc5644c02161c9655153d8143007255cd4358450100016949650d424c52100633dcd820c564480016949650f424c52100527e518758d21100010f7985c471d89430058d6503119761500018af8759143484200052d65273584501000107f985d475d8d4000617217835cb644c4018bb875516018143007299c56448450080014b59498d7110210005c62415454d6050c018cd7360a311814200517a5687d8f53484113e29720152485100043de4584dc96314001c8c7350d62484400062b5d381588628c0014ad949cd62484400061d1d7815956050c1751c9755153181430062b60876991434840185c85e0d7648450084e6a5c80551434c0014ad93dd162484400061e217805d94348401cc5635c52114020006a34c48650d42484014769718475585430043766376d8d4348401555910c8755854300547e5d5454f6050c014e4915977258143005e16448250d424c4018e582dc431592200061d217815d3624c4018e87220161581430072550d71cc4605080187475e0570591310063618c805d943484018d4815cd43181
  | 5 => 0x800005001470002b000020100b000380000607d1b0a808000780000017c1401c000180a17c0467c00004194a0000acdd001e4030000c8b0020010010400003000041043b038030640001c0a0242a0000e0041c0003b08010000000000f2b00001c0005083938000001d01c0200c00004001f00000c0002c0f03c110a0020a400000000080000007004000149846c050045f024030400100007010016640200004010000280900002038b300c070140e0680e0000003c03000a70a00000078004131fc01034001bc1c1fc064a0000ac2305c0e00d500004d00801014390600302403000020000600884000000340b01837010010500000000078012140026403030211a8080240700c00020180f00904411000140040b4500e0580900401000000082b038220000356808001370004700002008000000009c0900c3601c021700d000050100200c00008000e00a0083d16c390fc010710203d0839043000250180d0000200c1701c2e00c0a0055524d751d5214402131e962015454d43007319c5634863008001dc0734c87048510006e4cc5811c143900017189055153981430047ca63715c1438400187485e057650d210052765281dcd62440018e582dc451591320061edd4805d1634840194c7321573486200052be498759131080010ef985c872591310072560d435c460508016c591209634ca10006351cf81591218c00187b85e017650d21006b16488650d31484011da98dcd70486301564721d5454d6050c018ad64e05728c0200063361d63486300800183e85dd0635812100517a5686dcd218c00149d940c77358a100041fe61751d56284001c977350d61484400061de0475591624c4014ae9750d62484400043de458759132140010de9720d6558121007a1593734c521080010bf985d07458d210052b652635c86484001ac68760563484200052b64871d9143
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x4000000479d676a00b0055094ca1900a1262908031c09760d321c1214400164253b26b22629084000ca164886991434c52100650b2843504a1a62908031919460c731c1214400164253a86b126290880009252a57650d31484400058a34a18a60b88c0a180315195604711c1434c00146253b08c0ac69084000c6421d9120143505300049894ecb28698a4210002c91a40c5105cc604840134254a86c0ac49888000c70649811c47050d300062a32ac18e63824288002c51a50c5105cc6048401a424bec8a1a6290c4000aa12a143509614c72000650d504b286a126290803285a825943509314840164253ac6a126290e80009a1a9a9650d424c5210069092eb228698a4210003094985cd435c96110001056d412ca18e0a124200b30688314c17118143
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x4285b929943201424c521
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x94c
  | 2 => 0x124c
  | 3 => 0x8a
  | 4 => 0x98a
  | 5 => 0x98c
  | 6 => 0x128a
  | 7 => 0x128c
  | 8 => 0x150a
  | 9 => 0x9ca
  | 10 => 0x12ca
  | 11 => 0x10c
  | 12 => 0xa0a
  | 13 => 0xa0c
  | 14 => 0x130a
  | 15 => 0x130c
  | 16 => 0x180c
  | 17 => 0x14a
  | 18 => 0x14c
  | 19 => 0x198a
  | 20 => 0x198c
  | 21 => 0xb0c
  | 22 => 0xb8c
  | 23 => 0x184c
  | 24 => 0xcca
  | 25 => 0x15ca
  | 26 => 0xd0a
  | 27 => 0xd0c
  | 28 => 0x160a
  | 29 => 0x188c
  | 30 => 0x44a
  | 31 => 0x1a0a
  | 32 => 0xe8a
  | 33 => 0x74c
  | 34 => 0x1a8c
  | 35 => 0x124954
  | 36 => 0x94e
  | 37 => 0xa0954
  | 38 => 0x130954
  | 39 => 0xb0954
  | 40 => 0xb8954
  | 41 => 0xcce
  | 42 => 0xe8e
  | 43 => 0x98e
  | 44 => 0x9ce
  | 45 => 0xa1254
  | 46 => 0xa0e
  | 47 => 0x131254
  | 48 => 0xd0e
  | 49 => 0x98092
  | 50 => 0x128992
  | 51 => 0x128994
  | 52 => 0x9c992
  | 53 => 0x12c992
  | 54 => 0xb0e
  | 55 => 0xb4e
  | 56 => 0xb8e
  | 57 => 0xd0992
  | 58 => 0xd0994
  | 59 => 0x160992
  | 60 => 0x151292
  | 61 => 0x9d292
  | 62 => 0x12d292
  | 63 => 0xb1294
  | 64 => 0xd1512
  | 65 => 0x12c9d2
  | 66 => 0xcc9d2
  | 67 => 0xe89d2
  | 68 => 0xa0114
  | 69 => 0x130a12
  | 70 => 0x130a14
  | 71 => 0xd0a12
  | 72 => 0xd0a14
  | 73 => 0x188a14
  | 74 => 0x181314
  | 75 => 0xe9312
  | 76 => 0xd1814
  | 77 => 0x184b14
  | 78 => 0xd0b14
  | 79 => 0xe95d2
  | 80 => 0xe8d12
  | 81 => 0x1292d2
  | 82 => 0x94b14
  | 83 => 0x130e92
  | 84 => 0x989d2
  | 85 => 0x992d2
  | 86 => 0x95254
  | 87 => 0x9d2d2
  | 88 => 0x124a14
  | 89 => 0x9ccd2
  | 90 => 0x98d12
  | 91 => 0xa0d12
  | 92 => 0x99612
  | 93 => 0x185254
  | 94 => 0x9ce92
  | 95 => 0x129512
  | 96 => 0x161512
  | 97 => 0x8992
  | 98 => 0x9292
  | 99 => 0x128b14
  | 100 => 0x189294
  | 101 => 0x15d2d2
  | 102 => 0x94b94
  | 103 => 0x95314
  | 104 => 0x98d14
  | 105 => 0xa0d14
  | 106 => 0xa1894
  | 107 => 0x131814
  | 108 => 0x189814
  | 109 => 0x10a14
  | 110 => 0x11314
  | 111 => 0x161312
  | 112 => 0x180d14
  | 113 => 0x150992
  | 114 => 0xb0d14
  | 115 => 0xb1854
  | 116 => 0x15ccd2
  | 117 => 0xd0e92
  | 118 => 0xd1612
  | 119 => 0x160d12
  | 120 => 0x15ce92
  | 121 => 0x184b94
  | 122 => 0xd1894
  | 123 => 0x188d14
  | 124 => 0x180a14
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 10 => 1
  | 9 => 41
  | 8 => 907
  | 7 => 4727
  | 6 => 4625
  | 5 => 622
  | 4 => 28
  | 3 => 1
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
  | 3 => packedAt gbK3 (i*92) 83
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
  | 3 => gbHint (packedAt gbK3 (i*92+83) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 10 => 2*((h/1+packedAt gbK10 (15+(h % 1)*1) 1) % 1)
  | 9 => 2*((h/41+packedAt gbK9 (1066+(h % 41)*6) 6) % 41)
  | 8 => 2*((h/302+packedAt gbK8 (33559+(h % 302)*10) 10) % 907)
  | 7 => 2*((h/1589+packedAt gbK7 (226896+(h % 1589)*13) 13) % 4727)
  | 6 => 2*((h/1541+packedAt gbK6 (272875+(h % 1541)*13) 13) % 4625)
  | 5 => 2*((h/291+packedAt gbK5 (43540+(h % 291)*10) 10) % 622)
  | 4 => 2*((h/16+packedAt gbK4 (2268+(h % 16)*5) 5) % 28)
  | 3 => 2*((h/1+packedAt gbK3 (92+(h % 1)*1) 1) % 1)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffff1c387f0fc07fe1c0701ffc8183fe3334cf
  | 1 => 0x1f0fe03f87f1ff80fe007ffe01464c4e4dc8fc
  | 2 => 0x1ff0ffc007fe0000ffff801ffe7870718e0f0f
  | 3 => 0xe000fffff8000000ffffffe003807f81f00ff0
  | 4 => 0xffffffffffff0000000003ff8001fff000
  | 5 => 0xffff0000000000000000000003fffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x2511041809024126a0421142a80081961114c5
  | 1 => 0xb8a200883909302720124d41842444a05485c
  | 2 => 0x12a8684006a4060854950099505850608e090a
  | 3 => 0x400096b550000814892a4b0023802a817006a0
  | 4 => 0xdb2664492c58000c020043ad0001eaa000
  | 5 => 0x9ccc02044080306010300c1183f7ff7c000000
  | _ => 0
def gbRaw : List Sig := (rawDecor 63 gbPos gbNeg).map Prod.fst
def gbPools : List BoundPool := [(0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555, 5, 0, gbRaw),(0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333, 8, 0, gbRaw),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 7, 0, gbRaw),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 8, 0, gbRaw),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff, 7, 0, gbRaw),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff, 7, 0, gbRaw),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 6, 0, gbRaw),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 5, 0, gbRaw),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 5, 0, gbRaw),(0x555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555, 4, 0, gbRaw),(0x330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033, 5, 0, gbRaw),(0x3333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333, 5, 0, gbRaw),(0x333333330000000033333333000000003333333300000000333333330000000033333333000000003333333300000000333333330000000033333333, 4, 0, gbRaw),(0x33333333000000003333333300000000333333330000000033333333000000003333333300000000333333330000000033333333000000003333333300000000, 5, 0, gbRaw),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f, 5, 0, gbRaw),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f, 5, 0, gbRaw),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f, 4, 0, gbRaw),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000, 5, 0, gbRaw),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff, 4, 0, gbRaw),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000, 5, 0, gbRaw),(0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff, 4, 0, gbRaw),(0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff00000000, 5, 0, gbRaw),(0xa0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a, 4, 0, gbRaw),(0x330033000000000033003300000000003300330000000000330033000000000033003300000000003300330000000000330033000000000033003300000000, 4, 0, gbRaw),(0x3333000000000000333300000000000033330000000000003333000000000000333300000000000033330000000000003333000000000000333300000000, 4, 0, gbRaw),(0xf000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000, 4, 0, gbRaw),(0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f00000000, 4, 0, gbRaw)]
def gbAtlas : Atlas := ⟨10,rawDecor 63 gbPos gbNeg, 0xfefefea8feeefca0fefefea8feeefca0fefefea8feeefca0fefefea8feeefca0fefefea8feeefca0fefefea8feeefca0fefefea8feeefca0fefefea8feeefca0, gbN, gbR, gbH, gbI, gbPools⟩
end PEqualNP.Outside.L_meta_36366
namespace PEqualNP.Outside.L_meta_36366
open PEqualNP.Outside.L_meta_36366.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_2_0 : Interval s1Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 4 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 25 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_96 : Interval s1Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_192 : Interval s1Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_288 : Interval s1Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_384 : Interval s1Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_480 : Interval s1Atlas 4 480 59 := block_range (n:=59) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 539 := (concat (concat bs1_4_0 (concat bs1_4_96 bs1_4_192)) (concat bs1_4_288 (concat bs1_4_384 bs1_4_480)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_96 : Interval s1Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_192 : Interval s1Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_288 : Interval s1Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_384 : Interval s1Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_480 : Interval s1Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_576 : Interval s1Atlas 5 576 88 := block_range (n:=88) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 664 := (concat (concat bs1_5_0 (concat bs1_5_96 bs1_5_192)) (concat (concat bs1_5_288 bs1_5_384) (concat bs1_5_480 bs1_5_576)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_6_0 : Interval s1Atlas 6 0 40 := block_range (n:=40) (by decide +kernel)
theorem alls1_6 : Interval s1Atlas 6 0 40 := bs1_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_7_0 : Interval s1Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_7 : Interval s1Atlas 7 0 1 := bs1_7_0
theorem alls1 : ∀ k ≤ 7, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
  · exact alls1_6 i (by omega) hi
  · exact alls1_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_0 : Interval s2Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 3 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 21 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_96 : Interval s2Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 99 := (concat bs2_4_0 bs2_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 46 := block_range (n:=46) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 46 := bs2_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 1 := bs2_6_0
theorem alls2 : ∀ k ≤ 6, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_2 i (by omega) hi
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 4 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 25 := bs3_3_0
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
theorem bs3_4_480 : Interval s3Atlas 4 480 59 := block_range (n:=59) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 539 := (concat (concat bs3_4_0 (concat bs3_4_96 bs3_4_192)) (concat bs3_4_288 (concat bs3_4_384 bs3_4_480)))
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
theorem bs3_5_576 : Interval s3Atlas 5 576 88 := block_range (n:=88) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 664 := (concat (concat bs3_5_0 (concat bs3_5_96 bs3_5_192)) (concat (concat bs3_5_288 bs3_5_384) (concat bs3_5_480 bs3_5_576)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 40 := block_range (n:=40) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 40 := bs3_6_0
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
theorem bs4_2_0 : Interval s4Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 3 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 21 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_96 : Interval s4Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 99 := (concat bs4_4_0 bs4_4_96)
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
theorem bs5_4_0 : Interval s5Atlas 4 0 60 := block_range (n:=60) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 60 := bs5_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 40 := block_range (n:=40) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 40 := bs5_5_0
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
  · exact alls5_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq6_2_0 : Interval q6Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq6_2 : Interval q6Atlas 2 0 1 := bq6_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq6_3_0 : Interval q6Atlas 3 0 11 := block_range (n:=11) (by decide +kernel)
theorem allq6_3 : Interval q6Atlas 3 0 11 := bq6_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq6_4_0 : Interval q6Atlas 4 0 10 := block_range (n:=10) (by decide +kernel)
theorem allq6_4 : Interval q6Atlas 4 0 10 := bq6_4_0
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
theorem bq9_3_0 : Interval q9Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq9_3 : Interval q9Atlas 3 0 1 := bq9_3_0
theorem allq9 : ∀ k ≤ 3, ∀ i < count q9Atlas k, checkRow q9Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq9_3 i (by omega) hi
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
theorem bq12_3_0 : Interval q12Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq12_3 : Interval q12Atlas 3 0 1 := bq12_3_0
theorem allq12 : ∀ k ≤ 3, ∀ i < count q12Atlas k, checkRow q12Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq12_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq13_2_0 : Interval q13Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq13_2 : Interval q13Atlas 2 0 1 := bq13_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq13_3_0 : Interval q13Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allq13_3 : Interval q13Atlas 3 0 5 := bq13_3_0
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
theorem bq15_2_0 : Interval q15Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq15_2 : Interval q15Atlas 2 0 1 := bq15_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq15_3_0 : Interval q15Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allq15_3 : Interval q15Atlas 3 0 5 := bq15_3_0
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
theorem bq16_3_0 : Interval q16Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq16_3 : Interval q16Atlas 3 0 1 := bq16_3_0
theorem allq16 : ∀ k ≤ 3, ∀ i < count q16Atlas k, checkRow q16Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq16_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq17_2_0 : Interval q17Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq17_2 : Interval q17Atlas 2 0 1 := bq17_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq17_3_0 : Interval q17Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allq17_3 : Interval q17Atlas 3 0 5 := bq17_3_0
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
theorem bq20_3_0 : Interval q20Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq20_3 : Interval q20Atlas 3 0 1 := bq20_3_0
theorem allq20 : ∀ k ≤ 3, ∀ i < count q20Atlas k, checkRow q20Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq20_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq21_2_0 : Interval q21Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq21_2 : Interval q21Atlas 2 0 1 := bq21_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq21_3_0 : Interval q21Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allq21_3 : Interval q21Atlas 3 0 5 := bq21_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq21_4_0 : Interval q21Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq21_4 : Interval q21Atlas 4 0 1 := bq21_4_0
theorem allq21 : ∀ k ≤ 4, ∀ i < count q21Atlas k, checkRow q21Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq21_2 i (by omega) hi
  · exact allq21_3 i (by omega) hi
  · exact allq21_4 i (by omega) hi
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
theorem bq26_3_0 : Interval q26Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq26_3 : Interval q26Atlas 3 0 1 := bq26_3_0
theorem allq26 : ∀ k ≤ 3, ∀ i < count q26Atlas k, checkRow q26Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq26_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 1 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 28 := bgb_4_0
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
theorem bgb_5_576 : Interval gbAtlas 5 576 46 := block_range (n:=46) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 622 := (concat (concat bgb_5_0 (concat bgb_5_96 bgb_5_192)) (concat (concat bgb_5_288 bgb_5_384) (concat bgb_5_480 bgb_5_576)))
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
theorem bgb_6_4608 : Interval gbAtlas 6 4608 17 := block_range (n:=17) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 4625 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_96 bgb_6_192)) (concat bgb_6_288 (concat bgb_6_384 bgb_6_480))) (concat (concat bgb_6_576 (concat bgb_6_672 bgb_6_768)) (concat bgb_6_864 (concat bgb_6_960 bgb_6_1056)))) (concat (concat (concat bgb_6_1152 (concat bgb_6_1248 bgb_6_1344)) (concat bgb_6_1440 (concat bgb_6_1536 bgb_6_1632))) (concat (concat bgb_6_1728 (concat bgb_6_1824 bgb_6_1920)) (concat bgb_6_2016 (concat bgb_6_2112 bgb_6_2208))))) (concat (concat (concat (concat bgb_6_2304 (concat bgb_6_2400 bgb_6_2496)) (concat bgb_6_2592 (concat bgb_6_2688 bgb_6_2784))) (concat (concat bgb_6_2880 (concat bgb_6_2976 bgb_6_3072)) (concat bgb_6_3168 (concat bgb_6_3264 bgb_6_3360)))) (concat (concat (concat bgb_6_3456 (concat bgb_6_3552 bgb_6_3648)) (concat bgb_6_3744 (concat bgb_6_3840 bgb_6_3936))) (concat (concat bgb_6_4032 (concat bgb_6_4128 bgb_6_4224)) (concat (concat bgb_6_4320 bgb_6_4416) (concat bgb_6_4512 bgb_6_4608))))))
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
theorem bgb_7_4320 : Interval gbAtlas 7 4320 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_4416 : Interval gbAtlas 7 4416 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_4512 : Interval gbAtlas 7 4512 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_4608 : Interval gbAtlas 7 4608 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_4704 : Interval gbAtlas 7 4704 23 := block_range (n:=23) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 4727 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_96 bgb_7_192)) (concat bgb_7_288 (concat bgb_7_384 bgb_7_480))) (concat (concat bgb_7_576 (concat bgb_7_672 bgb_7_768)) (concat bgb_7_864 (concat bgb_7_960 bgb_7_1056)))) (concat (concat (concat bgb_7_1152 (concat bgb_7_1248 bgb_7_1344)) (concat bgb_7_1440 (concat bgb_7_1536 bgb_7_1632))) (concat (concat bgb_7_1728 (concat bgb_7_1824 bgb_7_1920)) (concat (concat bgb_7_2016 bgb_7_2112) (concat bgb_7_2208 bgb_7_2304))))) (concat (concat (concat (concat bgb_7_2400 (concat bgb_7_2496 bgb_7_2592)) (concat bgb_7_2688 (concat bgb_7_2784 bgb_7_2880))) (concat (concat bgb_7_2976 (concat bgb_7_3072 bgb_7_3168)) (concat bgb_7_3264 (concat bgb_7_3360 bgb_7_3456)))) (concat (concat (concat bgb_7_3552 (concat bgb_7_3648 bgb_7_3744)) (concat bgb_7_3840 (concat bgb_7_3936 bgb_7_4032))) (concat (concat bgb_7_4128 (concat bgb_7_4224 bgb_7_4320)) (concat (concat bgb_7_4416 bgb_7_4512) (concat bgb_7_4608 bgb_7_4704))))))
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
theorem bgb_8_672 : Interval gbAtlas 8 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_768 : Interval gbAtlas 8 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_864 : Interval gbAtlas 8 864 43 := block_range (n:=43) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 907 := (concat (concat (concat bgb_8_0 bgb_8_96) (concat bgb_8_192 (concat bgb_8_288 bgb_8_384))) (concat (concat bgb_8_480 bgb_8_576) (concat bgb_8_672 (concat bgb_8_768 bgb_8_864))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_9_0 : Interval gbAtlas 9 0 41 := block_range (n:=41) (by decide +kernel)
theorem allgb_9 : Interval gbAtlas 9 0 41 := bgb_9_0
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
  · exact allgb_3 i (by omega) hi
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 5 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 20, 52)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 8 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 0, 16),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq8 (cert : Complete q8Atlas) : Lower true (roots q8Atlas) (target q8Atlas) 5 := by
  have ready : Ready q8Atlas (asRow q8Pos) (asRow q8Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 0, 4),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq9 (cert : Complete q9Atlas) : Lower true (roots q9Atlas) (target q9Atlas) 4 := by
  have ready : Ready q9Atlas (asRow q9Pos) (asRow q9Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq10 (cert : Complete q10Atlas) : Lower true (roots q10Atlas) (target q10Atlas) 5 := by
  have ready : Ready q10Atlas (asRow q10Pos) (asRow q10Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 20, 52)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq11 (cert : Complete q11Atlas) : Lower true (roots q11Atlas) (target q11Atlas) 5 := by
  have ready : Ready q11Atlas (asRow q11Pos) (asRow q11Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq12 (cert : Complete q12Atlas) : Lower true (roots q12Atlas) (target q12Atlas) 4 := by
  have ready : Ready q12Atlas (asRow q12Pos) (asRow q12Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq13 (cert : Complete q13Atlas) : Lower true (roots q13Atlas) (target q13Atlas) 5 := by
  have ready : Ready q13Atlas (asRow q13Pos) (asRow q13Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq14 (cert : Complete q14Atlas) : Lower true (roots q14Atlas) (target q14Atlas) 5 := by
  have ready : Ready q14Atlas (asRow q14Pos) (asRow q14Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 16, 18),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq15 (cert : Complete q15Atlas) : Lower true (roots q15Atlas) (target q15Atlas) 5 := by
  have ready : Ready q15Atlas (asRow q15Pos) (asRow q15Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 34, 35),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq16 (cert : Complete q16Atlas) : Lower true (roots q16Atlas) (target q16Atlas) 4 := by
  have ready : Ready q16Atlas (asRow q16Pos) (asRow q16Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq17 (cert : Complete q17Atlas) : Lower true (roots q17Atlas) (target q17Atlas) 5 := by
  have ready : Ready q17Atlas (asRow q17Pos) (asRow q17Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq18 (cert : Complete q18Atlas) : Lower true (roots q18Atlas) (target q18Atlas) 4 := by
  have ready : Ready q18Atlas (asRow q18Pos) (asRow q18Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq19 (cert : Complete q19Atlas) : Lower true (roots q19Atlas) (target q19Atlas) 5 := by
  have ready : Ready q19Atlas (asRow q19Pos) (asRow q19Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq20 (cert : Complete q20Atlas) : Lower true (roots q20Atlas) (target q20Atlas) 4 := by
  have ready : Ready q20Atlas (asRow q20Pos) (asRow q20Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq21 (cert : Complete q21Atlas) : Lower true (roots q21Atlas) (target q21Atlas) 5 := by
  have ready : Ready q21Atlas (asRow q21Pos) (asRow q21Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq22 (cert : Complete q22Atlas) : Lower true (roots q22Atlas) (target q22Atlas) 4 := by
  have ready : Ready q22Atlas (asRow q22Pos) (asRow q22Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq23 (cert : Complete q23Atlas) : Lower true (roots q23Atlas) (target q23Atlas) 4 := by
  have ready : Ready q23Atlas (asRow q23Pos) (asRow q23Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq24 (cert : Complete q24Atlas) : Lower true (roots q24Atlas) (target q24Atlas) 4 := by
  have ready : Ready q24Atlas (asRow q24Pos) (asRow q24Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq25 (cert : Complete q25Atlas) : Lower true (roots q25Atlas) (target q25Atlas) 4 := by
  have ready : Ready q25Atlas (asRow q25Pos) (asRow q25Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq26 (cert : Complete q26Atlas) : Lower true (roots q26Atlas) (target q26Atlas) 4 := by
  have ready : Ready q26Atlas (asRow q26Pos) (asRow q26Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) (pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p) : Lower true (roots gbAtlas) (target gbAtlas) 11 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact pv
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfefefea8feeefca0fefefea8feeefca0fefefea8feeefca0fefefea8feeefca0fefefea8feeefca0fefefea8feeefca0fefefea8feeefca0fefefea8feeefca0
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certq6 : Complete q6Atlas) (certq7 : Complete q7Atlas) (certq8 : Complete q8Atlas) (certq9 : Complete q9Atlas) (certq10 : Complete q10Atlas) (certq11 : Complete q11Atlas) (certq12 : Complete q12Atlas) (certq13 : Complete q13Atlas) (certq14 : Complete q14Atlas) (certq15 : Complete q15Atlas) (certq16 : Complete q16Atlas) (certq17 : Complete q17Atlas) (certq18 : Complete q18Atlas) (certq19 : Complete q19Atlas) (certq20 : Complete q20Atlas) (certq21 : Complete q21Atlas) (certq22 : Complete q22Atlas) (certq23 : Complete q23Atlas) (certq24 : Complete q24Atlas) (certq25 : Complete q25Atlas) (certq26 : Complete q26Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 11 := by
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
  have q0 : Slice true (roots gbAtlas) (target gbAtlas) (0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555 : Sig) 5 :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have q1 : Slice true (roots gbAtlas) (target gbAtlas) (0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333 : Sig) 8 :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have q2 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f : Sig) 7 :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have q3 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff : Sig) 8 :=
    slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
  have q4 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff : Sig) 7 :=
    slice_correct (ms:=fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds4 certs4)
  have q5 : Slice true (roots gbAtlas) (target gbAtlas) (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff : Sig) 7 :=
    slice_correct (ms:=fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds5 certs5)
  have q6 : Slice true (roots gbAtlas) (target gbAtlas) (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000 : Sig) 6 :=
    slice_correct (ms:=fixRows 0 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq6 certq6)
  have q7 : Slice true (roots gbAtlas) (target gbAtlas) (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a : Sig) 5 :=
    slice_correct (ms:=fixRows 4 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq7 certq7)
  have q8 : Slice true (roots gbAtlas) (target gbAtlas) (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa : Sig) 5 :=
    slice_correct (ms:=fixRows 16 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq8 certq8)
  have q9 : Slice true (roots gbAtlas) (target gbAtlas) (0x555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555 : Sig) 4 :=
    slice_correct (ms:=fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq9 certq9)
  have q10 : Slice true (roots gbAtlas) (target gbAtlas) (0x330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033 : Sig) 5 :=
    slice_correct (ms:=fixRows 10 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq10 certq10)
  have q11 : Slice true (roots gbAtlas) (target gbAtlas) (0x3333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333 : Sig) 5 :=
    slice_correct (ms:=fixRows 18 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq11 certq11)
  have q12 : Slice true (roots gbAtlas) (target gbAtlas) (0x333333330000000033333333000000003333333300000000333333330000000033333333000000003333333300000000333333330000000033333333 : Sig) 4 :=
    slice_correct (ms:=fixRows 34 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq12 certq12)
  have q13 : Slice true (roots gbAtlas) (target gbAtlas) (0x33333333000000003333333300000000333333330000000033333333000000003333333300000000333333330000000033333333000000003333333300000000 : Sig) 5 :=
    slice_correct (ms:=fixRows 2 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq13 certq13)
  have q14 : Slice true (roots gbAtlas) (target gbAtlas) (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f : Sig) 5 :=
    slice_correct (ms:=fixRows 12 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq14 certq14)
  have q15 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f : Sig) 5 :=
    slice_correct (ms:=fixRows 20 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq15 certq15)
  have q16 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f : Sig) 4 :=
    slice_correct (ms:=fixRows 36 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq16 certq16)
  have q17 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000 : Sig) 5 :=
    slice_correct (ms:=fixRows 4 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq17 certq17)
  have q18 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff : Sig) 4 :=
    slice_correct (ms:=fixRows 40 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq18 certq18)
  have q19 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000 : Sig) 5 :=
    slice_correct (ms:=fixRows 8 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq19 certq19)
  have q20 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff : Sig) 4 :=
    slice_correct (ms:=fixRows 48 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq20 certq20)
  have q21 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff00000000 : Sig) 5 :=
    slice_correct (ms:=fixRows 16 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq21 certq21)
  have q22 : Slice true (roots gbAtlas) (target gbAtlas) (0xa0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a : Sig) 4 :=
    slice_correct (ms:=fixRows 20 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq22 certq22)
  have q23 : Slice true (roots gbAtlas) (target gbAtlas) (0x330033000000000033003300000000003300330000000000330033000000000033003300000000003300330000000000330033000000000033003300000000 : Sig) 4 :=
    slice_correct (ms:=fixRows 10 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq23 certq23)
  have q24 : Slice true (roots gbAtlas) (target gbAtlas) (0x3333000000000000333300000000000033330000000000003333000000000000333300000000000033330000000000003333000000000000333300000000 : Sig) 4 :=
    slice_correct (ms:=fixRows 18 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq24 certq24)
  have q25 : Slice true (roots gbAtlas) (target gbAtlas) (0xf000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000 : Sig) 4 :=
    slice_correct (ms:=fixRows 12 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq25 certq25)
  have q26 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f00000000 : Sig) 4 :=
    slice_correct (ms:=fixRows 20 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq26 certq26)
  have pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p :=
    List.forall_iff_forall_mem.1 (show List.Forall (fun p => ValidPool true (roots gbAtlas) (target gbAtlas) p) gbPools from ⟨build_valid q0 [] rfl, build_valid q1 [] rfl, build_valid q2 [] rfl, build_valid q3 [] rfl, build_valid q4 [] rfl, build_valid q5 [] rfl, build_valid q6 [] rfl, build_valid q7 [] rfl, build_valid q8 [] rfl, build_valid q9 [] rfl, build_valid q10 [] rfl, build_valid q11 [] rfl, build_valid q12 [] rfl, build_valid q13 [] rfl, build_valid q14 [] rfl, build_valid q15 [] rfl, build_valid q16 [] rfl, build_valid q17 [] rfl, build_valid q18 [] rfl, build_valid q19 [] rfl, build_valid q20 [] rfl, build_valid q21 [] rfl, build_valid q22 [] rfl, build_valid q23 [] rfl, build_valid q24 [] rfl, build_valid q25 [] rfl, build_valid q26 [] rfl⟩)
  have low := boundgb certgb allCuts pv
  have lift := lift_ok (u:=true) (ms:=fixRows 0 0) (raw:=fullRoots) (T:=fullWord) (xs:=[]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 0 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4278124200 * 2 ^ 32 + 4277075104) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36366.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,2]⟩,⟨.or,[1,5]⟩,⟨.and,[4,7]⟩,⟨.or,[3,8]⟩,⟨.and,[6,9]⟩,⟨.or,[4,5]⟩,⟨.or,[2,11]⟩,⟨.or,[3,4]⟩,⟨.or,[6,13]⟩,⟨.and,[0,14]⟩,⟨.and,[12,15]⟩,⟨.or,[10,16]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,17⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 11) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124200 * 2 ^ 32 + 4277075104) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124200 * 2 ^ 32 + 4277075104) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36366

open PEqualNP.Outside.L_meta_36366 in
theorem PEqualNP.Outside.L_meta_36366 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124200 * 2 ^ 32 + 4277075104) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124200 * 2 ^ 32 + 4277075104) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allq6 allq7 allq8 allq9 allq10 allq11 allq12 allq13 allq14 allq15 allq16 allq17 allq18 allq19 allq20 allq21 allq22 allq23 allq24 allq25 allq26 allgb)
