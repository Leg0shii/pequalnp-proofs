import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, children closed at the parent by
-- restriction pools (closeChild of the model), and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36370.Model
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


end PEqualNP.Outside.L_meta_36370.Model

namespace PEqualNP.Outside.L_meta_36370
open PEqualNP.Outside.L_meta_36370.Model
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

def SBf (j : Nat) : Nat := [6, 7, 7, 8, 6, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36370

namespace PEqualNP.Outside.L_meta_36370
open PEqualNP.Outside.L_meta_36370.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x3000000bf42dd32df32bd42bc43be43
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x25aa421e350932
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 6
  | 3 => 2
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (i*5) 5
  | 4 => packedAt s0K4 (i*16) 16
  | 3 => packedAt s0K3 (i*27) 27
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/9+packedAt s0K4 (96+(h % 9)*3) 3) % 6)
  | 3 => 2*((h/1+packedAt s0K3 (54+(h % 1)*1) 1) % 2)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x3ffc0ffffc1fc1ffc1ff07fc3ffc0fd8f33f3
  | 2 => 0xfc0fff03fffe0fe0ffe0ff83fc3fff02f1ccfc
  | 3 => 0xfffffffc1fffffff0000ffffffc3ffff01ff1f
  | 4 => 0xfffffe0000fffffff0003fffc0003fe0fe0
  | 5 => 0xfff0000000000ffffffffffc00000003fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x48644628849284052d093424c0664258871171
  | 2 => 0x19248a19091094a0552854a1442a9608b144b4
  | 3 => 0x208910405221094a0210894a2a8128a300aa0a
  | 4 => 0xb2ca249243a52a739a520843b3100c335a0fc0
  | 5 => 0xc30c38e39c39cf9ce39cee70222230c3edf000
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcfcfc00fcc0fc00fcfcfc00fcc0fc00fcfcfc00fcc0fc00fcfcfc00fcc0fc00fcfcfc00fcc0fc00fcfcfc00fcc0fc00fcfcfc00fcc0fc00fcfcfc00fcc0fc00, s0N, s0R, (fun _ _ => 0), s0I, []⟩
end PEqualNP.Outside.L_meta_36370
namespace PEqualNP.Outside.L_meta_36370
open PEqualNP.Outside.L_meta_36370.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x860003d500048030104108f24f0000440020c108030cdc43df43fc32fc31fe42ff31fd21dc31fe43ff40fd32dd30fc30fc40fe30df32ff21fc10fe21fd40fd30ff43fd41ff42fd10df30de31ff32ff41fe41fd20fe20bf42ff20fe32bd42ff30fe31fc42fe10fd31fe40fd42fc20fc41fd43fc21fc43ff10dd32
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x4920f89800201c80200000480998300030488800012858182838000000301800483088180138c368807820001000000028619898036af098784d02e00020598800086019a000516019406806750831aea90633f54442bca9995794c40af298415e510c6daa421dd94420bd280439f420c738a89857d4d42cfa12619d42cca7ca810d7151328f2a4635d530829aa421e710f42afa9a438d424cabaa7205794e20cfa1a859f42ccb3aa918cf55231aea96615e5390e78a8886710d42af29e433d540867aa990e7d4f42aea9a413d548cb3ea8984f55010ae29a219f5350b38a7a16b509209f2a4655d539075a8410e750a31ae2a0635c54cc2bca7215794e41ae29a85ad428cb3e87a14f55320b6a90815d538cab8a6a0d714f10ce21c816e52d06eaa2105b948109f2a6415d50ccabca6184f55020afa8265db504c2baa6205714530af298855e530427aa9215795130af288875c514cb3a84995794f20ce29a855e53902baa790d715231e6a12655d53086dca4205754c42af298655f53c42bca39867d0a31aea80635d5210ebea710d7d4d40e6a90873d540cb3a85984f95032afa9a83ad424cb3886a0cf95231ae2a2615e548c678a89857d4930af2a0633e5410abca610d754e30baa88815d538835a85904fd5130af29a415d508c6b8a690d795330b7290876f524433887a0e7d0932aea86875d5390abaa6085754f41b6a96831c544c3aca218d795132cea12615e518c73ca918cf95020af29c215e51ccb3e859857d4d10ae29a815d538427ca990d754b43aea80875d53c82bca821d754a319f2a0215c538875ea4a16b50a21bca80436c52442daa4085794743e7a9265ce424cb3ca821dd94440af29e83ce5210eb8a9996710c40
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x273f3084240340300043d8e24200b00004301f01100600b0002c0003640000000001040c354d420868d6210e408799251cc28d629523193588540c61e64d4e2187993534861f6550a3187992544c3294254021c3588544c21f65d0a31c39915210f0c655093287191538821c6550930a598753d0a1c6454d2093588544c21c645433293195424ca1e6494431c310d521030c4354b4187197424c2546154d20a358853d0a1c6454e10c3d95424ca8d6210f41c398a548c61d6295231c3d4d428868d6210c408b58a548c70d5250b30c350b504cb0e62151308799353c42566195132c3549420c62d621513083588544c21c6454031a3588544c31443544408799251ccb0d4214532a3588435061d621513096580540c70d5350b20c39515210f0d62952318358a548c64d6215330a3592424cb0d5350920a358b53d0a4d6295231
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0xc0081068338ecaa1265415c8435444081ae4322a018c0d7299353c428238aa6a1241035ca64d4d2181ae4322a70840c7654d4248282b8cc8a9087035ca6494730
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
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
  | 6 => 2*((h/1+packedAt s1K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/30+packedAt s1K5 (800+(h % 30)*6) 6) % 50)
  | 4 => 2*((h/76+packedAt s1K4 (4455+(h % 76)*8) 8) % 165)
  | 3 => 2*((h/48+packedAt s1K3 (2280+(h % 48)*6) 6) % 60)
  | 2 => 2*((h/10+packedAt s1K2 (490+(h % 10)*4) 4) % 10)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xf0ffffe0fffc3fc1fe1f87fff0ffc1fe8cf3cf
  | 2 => 0xff07c3ff0fffc3fe1fe1f8707f0ffe1f734cf3
  | 3 => 0xfff803fff0fffc7fe001ff807ff1ffe1838f3c
  | 4 => 0x3ffff00007ffffe00007ffe0001fc0fc0
  | 5 => 0xfffffc000000007fffffffff80000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x10108022000840002202009110124044041145
  | 2 => 0x224104442450040a0c20882221049418314492
  | 3 => 0x44222a8842a220d4c11155044aa12981828a28
  | 4 => 0xeb5b312aa3aa967775444097cc80ccddc0fc0
  | 5 => 0x88c6221cccc332799999e64e08803111ebe000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfafafaaafaa0faa0fafafaaafaa0faa0fafafaaafaa0faa0fafafaaafaa0faa0fafafaaafaa0faa0fafafaaafaa0faa0fafafaaafaa0faa0fafafaaafaa0faa0, s1N, s1R, (fun _ _ => 0), s1I, []⟩
end PEqualNP.Outside.L_meta_36370
namespace PEqualNP.Outside.L_meta_36370
open PEqualNP.Outside.L_meta_36370.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x1118606c0400c02182ca1001150030400c0fd41df30fd43fd40fd10bf42ff31fe32fe21ff40fd31fe43fc32dd32ff21ff20fe20fd42dc43ff43ff32fc42fe10fd30fc31ff10de31ff30fc43fc30fe42fd20fc21fc41fe41df43df32ff41fd21fe30fc40ff42fc10fd32dc31dd30fe31bd42fc20fe40
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x10500038000000002040003178280800200828303010004800d0d9c0781020100003c990402028b2e9c8200028884084d3a8800828496830302848e80808000802002008e12098980088180d714530af28e613e54c867ca91957d4d10d6a14439c43d06baa7196710c40ae29a855c53486bca7215b54843b6a9081ad424827aa9905794c10ce21c819e548c73886a0d794c42b7a92213d54086bca790d7145329f2a6415d5310aeca2205714d419eaa4655f504cab8a6884f55242aea86655f53c43b6a0985794f20ce21a855e53903aca218e714f42aea98215e510c67ea8885b94840af28e879c5350abaa018e750932af2a2615e530875a85195754843aea9463cd424cabca7a0d794631aea84633c544c2bea6a07354843aea9c617551102b8a8984f95032afa9c439d42cc2b8a7884f95042aea9c213d54042bca221cf950109f2a0435d53882bca69057d49308e2a2615e54cc35a8410d754831cfa16619f424cabaa1a1d794732aea9c856d52042bca6195d944209faa2619d420c6dca421d715031af2a4633e548c6dca4085795132a6a90875f534879ca421cf95020ae29a819d424c27aa8195754f20af2a0875e53842eaa2106b50b20d7a92855e540c73ea6a173d49329eaa46379500873a8518db54b41cf2a0875d5010ebaa720e710f42cfa9e859f420c6b8a8994795231ce2a2615e530839c84995715332af2a6655e53102bea6a16b50932c6a12653d54c86baa790e7d0930cea16656e52d073ea8985e94021aea96875d53082bea6a0cf15110cfa14635e53882baa62067d0d42ceaa4635c53886baa5985754e40ae2a6615d530873e87a15754f41b6292215d53482b8a918e7d0b32af298613d54082bca720d794e43
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x402ca006580c800c30402800040401400020401800000d00003013c300b040000040000c354d424821e64d4f10a3588439020d621513087d97428c70c4354b41c358a548c68d6210c4087588544c28d621513096580540c70e5454843c354d42c830d525083193588540c62d621513095986544ca1c64543329358a548c68d62d4f428799251cc30e62952319358854cc21e64d4e2187992510c729425402187992544c28d6214f42a3588435061e6494732c510d511030d6215130c39915210f0c655093287191538828d6295231c3d4d428861d629523193195424ca1c6454e10c310d521020d629523187191534821c655093087197424c21e64d4d2193588544c28d6210f41c3508514cb0f6550932a598753d0b0d42d41328b58a548c70d535082187191500c70d5250b3095185534828d6490932c3988544c21f6550a31
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x8004188a06b94c9a9a43415c6645484381ae4322a70840c7654d4248282b9086a8881411c5535092081ae5326a78840d7299251cc28338ecaa1265035c86454031
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
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
  | 5 => 2*((h/23+packedAt s2K5 (800+(h % 23)*6) 6) % 50)
  | 4 => 2*((h/76+packedAt s2K4 (4455+(h % 76)*8) 8) % 165)
  | 3 => 2*((h/48+packedAt s2K3 (2280+(h % 48)*6) 6) % 60)
  | 2 => 2*((h/10+packedAt s2K2 (490+(h % 10)*4) 4) % 10)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xf0ffffe0fffc3fc1fe1f87fff0ffc1fe8cf3cf
  | 1 => 0xff07c3ff0fffc3fe1fe1f8707f0ffe1f734cf3
  | 3 => 0xfff803fff0fffc7fe001ff807ff1ffe1838f3c
  | 4 => 0x3ffff00007ffffe00007ffe0001fc0fc0
  | 5 => 0xfffffc000000007fffffffff80000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x10108022000840002202009110124044041145
  | 1 => 0x224104442450040a0c20882221049418314492
  | 3 => 0x44222a8842a220d4c11155044aa12981828a28
  | 4 => 0xeb5b312aa3aa967775444097cc80ccddc0fc0
  | 5 => 0x88c6221cccc332799999e64e08803111ebe000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaaee88ee88eeeeeeaaee88ee88eeeeeeaaee88ee88eeeeeeaaee88ee88eeeeeeaaee88ee88eeeeeeaaee88ee88eeeeeeaaee88ee88eeeeeeaaee88ee88, s2N, s2R, (fun _ _ => 0), s2I, []⟩
end PEqualNP.Outside.L_meta_36370
namespace PEqualNP.Outside.L_meta_36370
open PEqualNP.Outside.L_meta_36370.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x400020400010002881910020000c024004124010cfc30fe31df30fd20ff32fc21fc20ff43fe30fd41ff20fe21fe32ff10fc10fd21fe41fd32fe10fe40fc43fe43ff40fc31ff21fd43fc32ff31fe20ff42fd42dd30fd30ff41fc41ff30fd40fd10fc40fd31fc42fe42
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x6637d50cc77a83a0770c930bea9e417c524c6faa7a05fd5331f6196433d54043d8a4985f94842bf294617c504c7baa7085f14141ef982417c524c2faa8907dcc521bf28021f651102fea6a0df94343bfaa041df30843b882985f95131bfaa061de434c3bc60985f94910baa8c65ee42486f8a2996fd0441f721665df320cbba80987d94632beaa487ed52d0efca1995f15332beaa4637e52cc2fca8905f54232bfa9c21de53903bc85985f54042ef29c215e53903b8a690fed0240deaa041df214c2faa421df54440bfa8a877c5150aeaa2207b50832bf280877f53087ba61905fd50109f2a4657e5110fbe86a1fbc8720ef29c417e51086fca7905f55230ef982217c5050ebca6105714d21be29c41dd310c6faa7887750930bf284617c54443da64197ec8120df21c817d53843ea8220fb0c820ef296617d52906f8a9985fd5110fa90a217e5410fb884985fd5130f710a43f541cc6eaa2105f54021bea8e817d52cc2daa4205f54332bea8063de21cc3de40105f95330de21e855f5350af8a6885f54b40bf2a6417f50486f8a918fd44010aea9841bd42d07be60187b50b21bf29861f641443de4210df54420bf29c217f540cbba60106f55010eea0a617551d0fda8590770c530bea8c417c54486faa0197514530f721241bd40103ba8621df54840bea9c433d54086fea810df54f42ee29a85dc514c2faa9197d54440ef2a661df43cc2fca8085d94632fc90041f651082f8a9185f15132eea92617d51d0efca9186f50c43fb20c437f52442faa021db94b43bb28e877f548caf8a6a0df15331f7a14856e528c6faa610df94a31bea9a21fa40103baa7105fd4810bf29a43ed52103b6a0986715130bf29c877e50c87da84215f54730be2a021bf42506faa898ef90f41bea9e837d53043ba64985f94a10bf29687dd30c42faa598fbcca32bea9a437d50d0bbc659873d4930ee29a83ed528c6f8a5085f95032dfa1887ec32883bea3985f54343bf2a2437e544caf8a4a0df14f10aea9c417e520cbbca8985f15021ee21e617f54ccafca3a1ef90541bf2a463be43102fca120fb54841fb98a637e5310af8a898df94f419eaa041f6310c6f8a9905b54841deaa4637e53082fca8885f94c31bf29a217d54882fea790f74c220dfa0481bf42502fca790f7d0e32ef202617e54086f8a690774c530fb08221dd51cc37c87a15f54e31ee28e617d52c43eca2217b50921ef90e617d54907ee4290df94e40bf28c61fb10843ea8218df94a32bea94637f54c43f26018770cb30fd180617e50087de411077d0530efa0261df31cc33ea8985754e30dfa0e81fb10442fea4a05f94641fba0a837e52cc6faa3a17b0c921bf280615f53486faa2185f15210ae29a837f54883bea4985f94740efa18657d5090f7aa9197ecc230be28a417d5490af8a818dfd4e21
  | 1 => 0x4514c2baa7205f55031b729021de514c3eaa3195fd5230fa18c43bc544c3b885985fd5121bf28081ee420cafea0a1dfd5131f799265df30c43ea8290df94410bf29481cc524c2baa7087710e31ee982417d53906f8a8195f94810dfa1683df41cc3de42905fd5132dfa1681dd30842daa4086f95021be29821f7318437ca9195f54e20ef194637d54087bc84985f95130ef292617f5050be862087b94b43ef190637e52106faa7197b94810bfa9c417d50d07b8a4985f54c42de21a837d54cc67ca8107d90431bea9021de4310fdc8590df55020efa1a61df30883dca4207dc4010bea9687f55110afea098f74c110bf28c877d5290ef8a610df94020f721641f521c42faa8997bc8621be29e437c54887da84907dc8621f799441dd434c3ba65985f95321df2a4637e508c7da40107bd4930fb98c43de214c2f8a6105f94221ef98c636f524c3daa40877d5330bf2a083ef4250afca6905f94642bf2a0817d538c2faa399770ca31fb28e877f54c86fea918dfd4d10bf290637d54ccbec83887790330beaa221dd31cc2fca910df94e21ee980617e530cafaa7215f54041efa9a835e53102fca0215f14132bfa92617e52c42faa420f7cc431bf28e417d52887bea8985f14e21be29021dc320c77a8220dfd4d21efa96615e530c2faa5205f94b40f7210857e50902bca7087d505109eaa4657e51cc3bc64995f94031bf2a4213e54042faa8985f94a439faa2617d54cc2faa3185f94c10bf284217d54486fca7a15d94440efa82617f524c67ca918df94f10bea84857f54cc2fea9085f94b41fb20a437d54842fca7a06d50441beaa641bf544c2fea2a16b50842de21c817e53907dc64195f94341fd90441f431843de6490df15120ee90e61bd42502faa2215f54321bea84437d53102fca220dfd4530bf28c81de51cc3be65985f94331baa88857e510cb7a82a07e88020eeaa661de41cc3f680a05dd4530be29e41f7419067aa918f710330bfa92877f53082baa6087b88120be282437c5350bbaa29877cc010be2a643f7514c3b886987d88421deaa0437d5190bf280205f95220bea9461dd320cafca2205f54231dea16817d528837887a0fdc4210b7290837e510c37a84a0df54e40ef29841f541886fca9886fd0a42be28a817c544c2fca620df94e42beaa6217d51c82fca9995f54a10df202817f54483bc64987714b30efa9a857c54c42fca6205f15030ef98a617d52442bca710778c531be292877f53c43b842985b14930df2a0217e5410bdca518ef90d42bfa96217f53482f8a2a1df15232eea1e61dd53083baa60857d4d41eea96617e51ccafaa8184f95021efa1661be43506faa2196fd0540ef18a617e520c2fca81077cca32f690a41f621c42fca818fdcc631faa88417d51842fca421df54241bea88877e5090afaa3195fd4f20bf2a
  | 2 => 0x283688956000020007e00026110620700a121000e89027876130020b8a80900000862010400081601a4605000000136280c008400e0000a016031180406a1585a460040180c14004288ae058bc00a0a4b83e170040d0007600019b10048380f882000f200000000000e81241800008040400200018110eb05022011161800231800091aa0a000030980388800018068042d8060f018168020003200002000040e8003e818008641a00a248520016a22002158000d81604910178060180200003000080480a220015f8a60284c1183a7b00a0190e0001a0c03c2e8144d1460200e0b0c4068120105e0002a0480d3f06808000040000b04008800728024109a1b8000d0e035800030184282e1400631000088001401c1300a038984e80a020de0000601812009e602896e602c0684c0201c000000983e1600c0100400800510945080401a9801d794c10bea98837e548caf8a7085f54643fb10a217e52086faa8085fd4c10dfa1085dc41cc2faa8197710e32beaa481be4250afca2105fd4520dfa0c83de414c3ea83885d94420fa18a437e5310fba85986fd0040bf2a061dd214c3de6590fdcc410bf29041df324c3b8a9985f94620de21a85f5310c6fea2a05f54640f690e41be54083be61905f54830fb20e635d53103bea690df94442ef98461dd544c2f8a0a15f94232ee980217e53086fea5085f14910eea0661ed21086f8a690df94632bf28e857f54887b886195f15220ee202617c52502fca218df54f21ae29a857e5010678a8986f90d43bf286857e51887bea2987d54743ef29821d7514c2fea6a15b54a31fb20883bf4390eeca2215fd4532bf294857d53483f420085d14530bf29c417c514c2fca0195f15020efa18637e50882f8a6a07b94841bf28c637c52c43be8718fb50b32ef18e61df30083bca6205fd4132eea9c816e52102faa6107715130beaa6437d54886fea9907948421bfa9a817d520c6fea4a0ef10c40f799041fb304c2fea818f7d0330ee10e617e52906fca121fd48421ef21e617f50507b88618ef50842b6a96877d52d07b8639877d0930eea9881f910043be8721df94840eea0e61f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x5544c26d6215031b6582524c31c5414930e6153504c33554944209d986544c25d6394020c7d53504c3345450510e310d420cb665294743d354d520434c52945309798e508871e5494c10cb951520427561951309b988540425f6548530cd552518ca766115030f4147504c277654c431d358b5350a3d64d4d21d554f310423c6454d20a7592324c38f6350842b398a524c29f64549309798c548825d63141419e580540cb2d5494a31cb551200825c65507309798e50c874d5394810b918941486d66195130d994a511035654145309d98454086d96014b30cd547401023c64549109798f528427661d5232cd54941106ad62d0c43b5586544c27a6015031b5584404c33554484218f191538826d6295131e550441cc25c63551218f191538426d6215310a7992524c32d5250040ab58b4390f4c528c5309bd89534425f6548730b318d42486756115032cd151410c79b54d41308f990504872e5494810b5984424c2776155130b5987430ca6f6548020cd153514c2e5618c832d954a51102d66194930cd553318c66e62d4c10b658351cc23f65500409b98a54cc6d5618c831a7191524c34c4394a319798c540c2ae6290d429758e509072e5454a318f59053042d960d5330d398b53506d763504319758f54c867765484219d58454c834f4394a3197d8d544c6d76155130a759232cc26d62d5010d518d5110b3554c40109758e50886d66110b309d586544c63e64947309758c504863e6414c21b3d89514c23d64d4c219798f548873754d45309798f54883c852d41308f59252cc25d639402197d9530042776154e40b5987438ca3d6494730c754c439026f6254d209ed81544874f520c930c755153043a552504419d584548825d6394321d354d521034e5414930c758f544c25e639402197994404c2d561d0d30c755130082ce62d0f309d9865290e3e64d4c20d5d0e518ca6d6214c10c755153082756194b30d554e511025d63152109d58753c823f6550441ad986435079454d45309b58a544c32f6550842cb5095010a3d6595020e994941106cd6295130b6582544c2b46150941b6d81524c3a54294442d914b514c27b6550040b5586524c31c54145308f59051482da60109309d997314876551c80209798c505079754d4530975835350ad561d0f309758e50d0a5e6314a10b3d8d420cb2d54cca328f59052842ce628c530cdd9541107655290441d514e414865d6394010cb549411074d53948409b588548c74d520ca319b588548c3565214530d358b535065d6394042b658054cc27661d5020b6980214c25c6354740b5586324c31d64d4d21a759251cc36552547439758c540826d62946439b58850507354154041cb149425066c6255130b518d41886da6010530c7152524c25e6314c20f114b514c23e64d4d219718d5110b2c4354840
  | 1 => 0xc74e5354810b658352cc2d960945309b58a51cc2d66110130b3588404c38c6350842d5147314c26c65509209d586544cb4f43149309758e50d063e64947329758c528429d648c53097d8d52c423d64d4f21c7150324c3645248710d3148314c26e6295131d3d8d52106ce62d0e318f993530431d544c010e5d8d411063d64d4e21d954b31042cf6255130b5987434c32c54509218f990514823d64d4f20cd550310425f6354b40d9d9521086d46155130f24c1200825e6394241d5587535072c5450b219dd85538826e6295330cb94d4210a5c6355110c7d8d54086d46154930b3988404c3d351d41309718d521065d6314142b958a21087546154e409d587540823e64d4e21a759252cc3355444010f10c8314871d54cc010c7150314c2db60545309798f548434c6254e10d9d48514c2d661d0f30f148421cc33454507109d584540c34e5394810cb54b401029d6494930d9d51210874c6254e409798f540432c54d49309759653042cd62947308f593530836432544209d9845050a796015031b398840cc33654946329e980540cb2f54d49308f99054042766194b3097d954310fc521085309798c5050b6552947438f593520423f6454e20c714f425065c6354910b398a54cc2756194a438f59052c43c752145309b18953442d561103309758e501067a6014c21cb151424825c65485309b98854c433451505409798f540825c63547209bd89544c23e64951309d58654ccad561d0c319b58b548c735545463297195434c2766114c209d58452502cd62103309b98a544c25e639424297d8d544ca75650c410c7951300429c6350b419d185534823f65508429798e50d063e6515130b998b314863d6595021c7552530433554cc410e3d53524c31c63550218f59053086cc6254530cb55152042e9600c820ad592411079443504319d584544829d6408530cb551528c69e648ca31a7992320c66e6214141f118d210869e648cb30c7152514c25d6395121c7953300425d63d4a109758353486d66194530b598652cc3a65448421d914d210871c6454e10f44c1100434f530c921cb54b411066e62150319d9875350a5f654c8328f993520425e65901309758f540823e6414b10d3d89538832d54c8020a7992544c2f1600c410d5147504c25d63d5220a759021cc29e6515130d314b504c34f6254e4097d8d524425f63547209d98753c826f6255110975805350a5e63951218f592520cb2d5494810d318d521065c6550b309798f520431e548ca31d954b100423e64d4f20d5994514c2b765504418f99053082b5648c431e5504414c31c548c5309b18953842746550510a759231cc3545214530b518d41487c763484219718d5408754439463297d95300834c6254c20cd90d511026d650c8208fd91534825c63553109d5875350ad960109309d18
  | 2 => 0x6550842e5d50514c27561152329b988544423e64148109798e5010755514c0209d195214433554884219d98454c83576154e108f99252cc25f6054c109b58854442cd628c7309b58b53c427561d52329718d54c823e64150219b58b53043c45214530b598632cc36552cc6318f59353c431f6454e209758f54043645214530d510c514c32c5450b20d9d4b514c26d6215210e3150524c32c5414930c795253082cd6295330c7953300831c5490d3097d8d544873454506219758e5090b5653944409d98654cc31f5410d30d5d44314c31e6515130d55875350b5553544409758f520425e6314810d1148514c25f6355110c95095110a746155120c7550438c65d63d52108f99353c431c53509419b98b53c426d6295132cbd50524c2cd6294530a7592514c2756115020cd95141cc63e6494431b558652cc31f6355232cb550320823e6494b31b658051cc23e6414a109798e500829e6494b30d694d300c2766115032d5d8d5110a6e6215030cd10d511026d659481097594430cb654254442b398b430c67661d4c20d5547300826c6550921c3150524c34f6254e109798f540c2786055121d594d51082766115220cd151414866c6254e40cb14942503c752d453097994534878f541493097d8d521067b6544010d3150524c2cd62d0d309d984548c34d62d4d219b988520435453505218fd954310e6f6548421ab5924210ace628c730cb151420ca3d6414c20b3588414c29e6408730cd5095110a3c6454d109798f54c878d4210930d99095110b4e5394840c95512108675619533097d95424c3a54250521d9548310425d63152208f59251ccb2d54c8421d3549300423d6494b319b988530425d65cc010c954941106cd62d0f30cd951518ca5c6548730e350842cc25e65d0d30a799231cc27b65480209d98654cca776154d109d986544ca9c6454530b358841cc357530c5219d587530825c6550930b598654cc23e6414910d994d2108765525044197d8d54c43655448421d9cc9510826d6215010b3988414c2b561d0c43d354b300425e6394010c7550438cb6552440109798e5010a3e6494832d394d521032e5494a319b988548c65f654c431d50c8514c25f6354442d314b324c25d63d52218f593530426d659083297583535074c5350921d5d0c514c2d66514530d3949300434c5390921c7d8d548c6e46150921c7d4c43506b561d0e4397594430c71c6454e209758053486746154e40b398b434c25d6014d419d98454042ce6295130b398841cc3565354440b558654cc2b96010c40d9485500866e62d50108f993530869e648c930c7153504c25c6354b409dd85544827765440109b98b548c65f65505309e580530863d65950109bd89539035751d4130d394b30042d661103309b988540826f6254e109d596410c6746154e208f592510
  | 3 => 0x541e2980500c080000a09003760060a40100163010700400502003028670002b004020000a02c0201c27610030c00100c070000000018158000d8372d4070100001c0402c0f008000000700c161a024000060380300c0004800a2c7b0b40200c00344080b40300c2f064110040501019224000b8000110637c000007900000030e00340e040010000404c03078000e8260040b0200007c0200072010470482c00c0e4f85e0e4180008200c1e0580001414068100500534800000000d44a0480d00c0003c2a01c122ac120001c3c86900c75000b4214072ad540885242865004030149b0a02629014028540149ec003b0000801cb50041c22405000030003604171010000680b03400000211a42d0200f000150b89d02c0320c1211c08008020040237c050dc7b0ac010440501c0201853000051340a00097060190000a00c8b028009758c54042d5618cb309d19541487555394420c7951530427661148109b98a5190e776154d2097d8d540872d425444297d95300c355530c61097d8d51d031d54cc020cd551510823f6454910e9551210871d5494c20d354f32082d96010530b6580214c29e6494730b3994524c34c4314930c7d91538433551500409718d52c42cc62551309b98b53087563214530cb95142ccb3654944209b58a54cc65f65507308f590520423e6414c10d5945300826e6215230d9545200825e6394342b5584424c31c548c9309ed95300c26e6215021d3148514c27661152329d584530825f6550b30b318d42c869e640853097597300826e6214540d5185530432e43548409798c548439940101309d98454482af6550842c758c544c25c65505309b98a51cc29f6454530d518553882ad648c832b5d85524c3645148520a7992314c2766114940d5150514c2e5628c431d5d85538829e6494530b558442cc3555354420b6d81544c34d530ca209798c530435651cc020cd94d41107565394420cb553320831e64d4d219b588515033742544429d984540833454145309758c520436732546329e596100425d6594c20d59875350b6652544409d98753087645248510b358b430ca6e65cc9219b988548426e62d4d41c7950328c7576154e409798c54043946350441d3d4b504c26c6255110d5587534865c63551208f590524429c635094197d8d544832d54484218fd91534431f5310d42c754e431023e64150208f99353c865e6394d2197581530433754145309798c54083665254743c7951530834e6514930b9d9521087a54254442e5150514c2ce62945309b58a54cc25f6355320c795130082cd628c530b5986324c2756114142d9549511023d6414121b398a51cc38c54d4930cd951510825e6314121b9987324866d62150309b58b535066f654c832c5150514c23f6454e109dd9541106756115230f2d4b504c26f
  | 4 => 0x40500c0601001744380381713833000000b4000048a0bc01018b70503603411000030300a020010
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x21005040004f000014c40000200201000c0060001703027831d00d4000000148108028230400700143c051475504414c2a3394a828a61511d52108530e0ee6a928220f0773551210860e3aac810a61831906254e10a8ce3a18a4984a57198a4350b0631a84a8885495c65450b32a62e02a28218e9161500404c2a33968628a61c114d4250521d12c4a00809870473551210878231a84a8885891954250521b08e6a128290d2571151420cba0a8a6090041911886154e40a4ae229284a060c5498a514c3062a4c518a61495c45450b20c52a8b00641070754148514c22a3aac221261495d65448421a4ae828a429070454d48514c330a92c018821a45056010530a48eaa128290c4c75588414c252ba4c399243495c85150540a4ae22a284906315458031043a0a926088021459d25414530a62e021aa2205297010d5210292b90a8a0863585c05348421c28a930c649870454148514c38239a84a8885439d25414930c28c830aa7106854258442cc2a3394a428a61495c85450710a18eaa108498525741492144307320a518a61495d05248710e0aa831a4210e856448421cc292ba0a690843c1dcd4254442e22a89822008709544c1200828a39aa4a0883519c65414930d0ac4a088398704635494110692b94a8a0e63a118d4250521a52e02a28419707635095110a52b94c321a83c1d8d5250441d1284b008498544735512108782aa6c690843c11cd525044194ae93166290e8542584424c292b90a8a0a21585c03254420d0ac4a088298516748c8514c30a2a4c329261c115052d4530d0ac890842986c121580214c28b3a4a428a61839905294530
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x100400000000000000062000000907875536348421a0485591210853090687d8d5250441a04855894110530c0475589411053090687d8d4254442a0686dcd4254442a0686dcd5250441c04755096110930a04855096110930a0686dcd5448421c04755912108530
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 42
  | 5 => 741
  | 4 => 794
  | 3 => 91
  | 2 => 12
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
  | 6 => 2*((h/28+packedAt s3K6 (672+(h % 28)*6) 6) % 42)
  | 5 => 2*((h/261+packedAt s3K5 (20007+(h % 261)*10) 10) % 741)
  | 4 => 2*((h/292+packedAt s3K4 (30172+(h % 292)*10) 10) % 794)
  | 3 => 2*((h/51+packedAt s3K3 (4459+(h % 51)*7) 7) % 91)
  | 2 => 2*((h/32+packedAt s3K2 (720+(h % 32)*4) 4) % 12)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffffffe0ffffff81e1e1fffffc3ffffc07f1ff
  | 1 => 0x3c0fc3ff07ff0ffe01fe38783fc7f07e394e73
  | 2 => 0x3ff003fff83ff0fffe003f803ff8ff83c18f9c
  | 4 => 0xc00003ffffc000ffffffc0003fff0003fe0fe0
  | 5 => 0xfffffc00000000ffffffffffc0000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x44100220002000020204088880912100210a5
  | 1 => 0x8922a6443294989610d21c511642a16a194652
  | 2 => 0x10a4aa8851a889aad2102d422690cd0ac18b18
  | 4 => 0x82cb1112a50e224d65648004b92406316e0de0
  | 5 => 0x230c221cc630ccf19999366702008843b5e000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xfefeaaaae8e8a8a8fefeaaaae8e8a8a8fefeaaaae8e8a8a8fefeaaaae8e8a8a8fefeaaaae8e8a8a8fefeaaaae8e8a8a8fefeaaaae8e8a8a8fefeaaaae8e8a8a8, s3N, s3R, (fun _ _ => 0), s3I, []⟩
end PEqualNP.Outside.L_meta_36370
namespace PEqualNP.Outside.L_meta_36370
open PEqualNP.Outside.L_meta_36370.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x10000032050300000002f621ed21bf41bd41f521bc40be40bf43bf42e521bd42bd43ef21
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x1712000700150011d290881a7414874a43204b54840d3a1a43a7424874ca890e9505219aa8881a5424863aa6204b54b43d2a1a43a5544866aa3a1d954a21
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x218959521103055348440a158e544862565d0d21
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 13
  | 3 => 16
  | 2 => 4
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (i*5) 5
  | 4 => packedAt s4K4 (i*16) 16
  | 3 => packedAt s4K3 (i*27) 27
  | 2 => packedAt s4K2 (i*38) 38
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s4K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/25+packedAt s4K4 (208+(h % 25)*4) 4) % 13)
  | 3 => 2*((h/19+packedAt s4K3 (432+(h % 19)*4) 4) % 16)
  | 2 => 2*((h/8+packedAt s4K2 (152+(h % 8)*2) 2) % 4)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xc7fffff878787fff0c30ffffe1c387ff83f07f
  | 1 => 0xf8f0f0ff807f8e1ff03f1c3c3e03f9e3cd4993
  | 2 => 0xff00ffff800fe1ffc01fc03ffc01fc718e1c
  | 3 => 0xff0000fffffff001ffffe0003ffffe007e0fe0
  | 5 => 0xffffff0000000001ffffffffc00000007ff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x40100008008080000000204400408020001025
  | 1 => 0x922629911534153132190e28b209314b454892
  | 2 => 0x34426aa234152913564816a134981199518a18
  | 3 => 0x884444040004488a24002092244002a0540
  | 5 => 0x268cc88766664d99ef3c9b33903065127fe000
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xfeaafeaafea8fea8feaafeaafea8fea8feaafeaafea8fea8feaafeaafea8fea8feaafeaafea8fea8feaafeaafea8fea8feaafeaafea8fea8feaafeaafea8fea8, s4N, s4R, (fun _ _ => 0), s4I, []⟩
end PEqualNP.Outside.L_meta_36370
namespace PEqualNP.Outside.L_meta_36370
open PEqualNP.Outside.L_meta_36370.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0xc30814000108008510010000000b30008000102c142bc42fd41ff21ff40fd30fe20fe40ff10fc10be41fe42fd20ff32fc42fe43ff41fd31fd21fc31fd43fc41fe10fc32ff43bd40fc30fc21fc20bf40fe32ff30ff42fd42fd10bc41be42fc40ff31fd32fc43fe30fe31fe21fe41bd43fd40bf43ff20
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x2617e50d0f7a86885f55241bea8c877d5490f7883985fd4131ef29841bf4390e7ca9106fd5320dfa1a817e530877c86a1efd0220f719065f930882fca8885f14121dfa8a877d53903f620885fd5021bb28841bc43502fca6905f94041bfaa241bd43106f8a2996f50130df28a87be420c37c87214f55221df214617d53d077ca020ef90b41dea0883bd548837886215f54640de212817e518c2fca890efd0c43f7994657e51d02faa818df94843f719641fa30842faa6085f94a30dfa1a617d5310afea6a0ef55020de21261ef218877a8420cf94a41dea1a637f5150bbc64994d94642bfa9e217c548827ca8086f50e109ea80833e540c778a810ef50110bea8443be420c6dca418ef90421deaa6657c540c6faa518df15131f790e413e548c3788490ef55221bfaa2657e548437ea9886f90631b729021bd43486dca41877d0d43df216217d510c2fca1a15fd5020de98a81bf4310b7ea8995f55240eea18877d544437a86997bd0942be294217d540caf8a998cf55230bea8643be42902fea0a1ef14c41de20a81bc535037ca0215f55330fd88421be540c37e86886b94a41bf2a0437d538c37885995f15330dea8c857d540c2f8a9185f94620bf2a465be50d0feaa3216f50c30bf2a087bc21d035aa520ef94743bf29c87bd438837e80905f94d21df20a41bc52502fea710ef90410dfa1883bd525037e8698ef15131bea9c217c5350b7c63a04f54042df20e81bc43107f680a05f54043de214217f54ccb7ca9085f54c20fd18061bc414c37a86105fd4c21bfa9287dd320caf8a6086f90a20bea86657c504caeaa3216f95321be29c433f544c67ca910ef54b43fb10e21bd215037e80206f54a41bf28e41bc54443f260907e50040de212217d528437c82205f94a42de992817d540437e80085fd5220fba0c437d548cafaa5a06f50210de210837c5250efaa9887b54830dea1863f6310c6f8a8885f94a31bf284857c52c437a87185f54831db28883be540cb7e8690fe88020df292817d508cb7c84905f54610bea9c63dd31cc378a1a1df95330be29e217d51c82fea2996fd0e10df29a81bf434cafaa4886f50f41bf28e87f6210867ca5a1f7cc431de20a213d5310a5ca520dfd4b10bfa8a87bc424caf8a6a06f54242bf2a6637e5390bba65984f54242fb98c633c51502fca320ef54543de296813e54c87dc84217e44010be29c21be32907788498dfd4810dea0041bd53907da4210ef90731de21041bf42907788398df151209e2a0437d544837c43a06f50f10baa8865bd5390afca5a0df94331bfa9221be420877a80186f54f40bf296813d5390af8a4a05f15310de21063bc414877e86105f94c41bea8841b65190b7e6520df15132df21483bf50907788298fe8c220de29c83be43502fea790ef50e409f2a6657e51ccb7862a06f90721
  | 1 => 0xd53c437ca818cf952109faa2657e50087f661185f94e10be2a065bf21502fca9996f50f20de20a413c544c77c8298efd0f42fa88021bf4390afea998ef10740bf298217c540827aa9206f90930df212817d52d06faa198df94031de2a2417d52cc67ea0a1df54a41bf29e41be41842fca6106fd0f21df296817e50903be63986f50f30be29841bf5010bf2a0195f94640bea86837e52843ea4210f948421df29085be42486eaa2185f55220dfa1e65bf52502fca6205f54440df29483bd31d037887216f4cb40f790441bc42cc67ca320df14520de21465f631486faa720df94042df10a817f504cb7e84215f94432bfaa2437e54c8376a0a07e4c210be29263bd43507f641106fd4743bf2a085bd21d02faa51877cc832be2a6417f548cbd88490df94a40be2a643bf408437c8720df94840beaa421ef210877e8710ef14241beaa2617e52d0efca4196fd4e41df2848579500c6fca7205f94a43df208417d50d0e7aa8186fd0c32dfa1083bd40c83788590efcc940df19083bf548c77ca420cf550109f294853c5250edaa4085d94430df20c617e50c87dc64905f14910be29e413c54442f8a0a15f95120dea1a85bf5310b7aa998ef90910dfaa243ee520437e87905f946439f28e873e54cc2fca7a0ef10832bea9e817f54c42fca6196fd0030bfaa0637e5010f78a3a05fd4f20dfa8a81be5390afca410d754c10bea9a417f528437e80106f90431bf2a263bc418877ea520df94241de20e43be410c2faa68877ccb30ef18a633d54cc7788510fbc8520df2a663f441886fea6106f55210dea06617e508c77c83885f94b30be2a4657f5384378a0a1ef509409e2a2417e508cb7e86a16fd0230dea1a81bc321067aa9987bd0b21bf288437f534827ca8106fd4343dfa1e613c525037ea0a1ef94e41fc98061bc42c837c87a07dcc5319eaa065df314c2f8a2a1db54a41df212633e52d037ca8987d88510df2a0213c544cb7a82a05f94e219f2a663bf41906fca4085f94a32deaa661bf5190b7a86215fd4e20bf284877e520c3da6490efd5110beaa6433e5110b7883905f95030bf290637e520837a86986f90a10df212657d5110f7c83206fd0740bea8865bf43506fca221fd8c710bfaa2219f5350fea8220ef94c429f2a065bf5250fee8320ef0c740bf28c653d531077e6420ef10b30da20a437c548c7be64986fd4c41be28287bd540cafaa9905f15210fd1822175510837e81887dc8521dfa8485ef4290bf640905fd4d42de29c857e530c3dc6590dfd4540dea9885ae5210afca6214fd5320df2a661be41882f4a018eb10b21df29e81b55190b78a4a1df55020dfa0481ed520c678a9886f54540fb880217e50ccafaa7105754c20de21283be42082fea8985fd4940fa98c437c534877aa3a06f508429faa4633d54ccafaa9214f15121bf2a
  | 2 => 0xb7e85215f94442fca8063bf32d037c8620dfd5221dea04417e508c37883185f54241df21465bc429037c839877cc631bea8083bd430877882186f90b21bf2a021bc42d077885886fd0e20bea8e877d54cc67aa1a1fe8c120f699643bd43906fea6086fd4b439ea9c83be54ccbf660986f54041beaa2637e548c378a890cf54f40faa88417e540c778a9195e94032bf29c83bc52906fea0a0df55230df20a83bd438c77c84a0dfd4121bfa8a613e521077ca0a1ef95020bea9e853f54c42f8a8985f95041be29a21bc410c6fca2086f50f40dfa0661bd42907bc8621ef10710bea8885bf41106fca988778c130bf28081bc428837e8720efd4f40dea1887bd43042fca7a06f15320dea1a417d508c7eca2195f54f20f710a43be42c83baa6104f15232bea8c85bf438cafaa3184f54241de28485bc41903ba60186f90832dfa90837d500cb7a83a05f94910dfaa2417c53506fca0105fd4d21df214433d54c877842a04f55243bf2a0655e53042f8a6907dc8621fa98863bc5310bda84215f54d21df20a81bd42d02f8a098fb4c832f690e41f6510837a86206f90530bf28683fb40902faa4185f543429e28a87bc53d02fea6885f95132dfa8e81be51d02fea898fb4cb20dfa1e81bf43086faa521fb88120dea1e437f524c67ca8186f10620be2a4437c524c37c85996fcc540df18a81ef324cb7aa990df54021dfa02617e53c86fca6886f540429faa221fa401037aa6a07d4c710dea0241be5250ff4a018ef4ca41bea9621b441886faa3984f15231de21c83bf43483ee8290df54a40be28a61fa500cb7a80087d48710dfa1c63ef20082faa8995b94a41fb88421f6510c378a9885f54042dfa8281bd43cc6faa710ef50e32bf28881bf535027aa8106fd5131bea9087be511067ca821ef50f42df28c85be42cc3788410ef908419faa043bf43042fca618df54242bf2a6433f54482f8a8086f94540de21463bc5110b7a80205f540319f28c85bc42906fea0a15f94b10dfa1e63bc410867aa818df95231dea96817e5290778a3216f10f40bea8e85ed520427ca8986f50e42bfaa4617d52cc378a020ef95230bea9c8579500cafca310df54f21bf28443bf431037ea2217d94642be28a81bc42102faa3995fd4d40be2a043bc411037aa8986f90510bb28c857e5210bdca4185f14542bfaa061bc52106faa4085f14941de21021bd548c2fca7a16f90942bf28e857e511077aa8086f90521beaa463bc42482fca1085f94e20fb20883bc42d03ec62886f14042bf28863f930443be65196f543439f28e81dd310c6fca910df54243bea8c41bc32502faa810f64c030df19281bc418c6f8a790dfd5210de29687bd43886fca7886f95220dfa1281dd530437882086f50f32bea9441bc5150f7e80886f50c32b6a9061ee520c77ca5a1df95040f6a94837
  | 3 => 0x8ccee8030280000009b1c000001800002000028010000580400f032000048050100040080501a0000103e0be0000102b16001416808000050098040020442283a000004848050120740180b00c0580a81006e39c068210900085680207e0100100b00201802010042084330420060500104b00201c0e000006ad0080070ec0046c01c09ccb80e00f000080010500021682a05b0860000000300c0200200202400c000480060540681f0762082c0060660040381e01a070428c00020e85e80000800c0d003152c780180508c03c000dd13e2186280502c0cc3681011800c0000228a01465803008000018093a0d2c2380108e2f8070040040240400001c00000803006000008713f602c1f0060000941180018805000000018094068030000780302b00c02c340000640400500001202800001002f040903d00c04c0800005a07c0101201e0000500f00009c00008014034038060180001380900c0183580400629c3f8080421dc3e86a00e0a4470000000000000a00e0a0008480080041e0be00e00c4c80100011010872124000248000385d40008d1b20080280300601c0380d09c0082c8120080f80980a0740100001003e09c1a0ce01a04c0003c0380081a85600a02c0080805495c0100f00201c138590c201c000090020e0001e108405805009000009a6002bea98437e540827ca220ef54841df19681bd408c3ee82a0ef90a31dfa1681bf31d02faa510df54e32dfa1861dd314c37ea9197d4c510df21021be50906f8a9997d54432df216637e50043da64907d10521f690a41f5510c3be61186fd4b40fa90a217c540c37aa120ef10610beaa243bf438c2faa620dfd45209f2a0817f52507dca520ef4c841fd08021bd53106faa3195f94b31df90e81f610442fea9986f90b40efa1c877d52102fea9905f54c40bb288657e500ca7ea6a06fd0540df20c43bd51d0efea8196f55030dfaa0437e50883d88590ef0ca41de20841bc428c37c862177cc030b6a90637e51082fea990ef50310be282837f54042fea918df54b43bf28861be42103bca6086f15132f6900417d54ccb7c83906f94c41bfa9261bc51d0f7e87886fd4041df20281be548877e87206fd0c31be2a243bc51503de8490efd0f41dfa9c85bc420c2faa420ef94442dfa9a877e521067aa9107d8c621fa98a43dd324c378a918ef55031dea9287bc32d02f8a610df952209faa2435e53082f8a7105f14810bf28e61f9200837aa2215f552219eaa4217d51d037e81906f541439f290853f548cbdc6490df94c439e2a6417e500c2fca318eb109219eaa2617e519
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x45310a3e65d0d31ea501200823f6355220ce552500cab960d47408f59353c86b96010a10c754e420423e61d5132ae580418c23d6550c209798f520423e6510520ad58c414872e5290a418f597400c23d6414e21cbd82529071f6355130ad988418863c64542318f992500c65e6314c20cdd91510c32f6494a41cd18554887354394430ad18543042e4614c921cd551510823e6494c31cb54a410423f6454720ab98831d023e650c841d91512108749524c0309798c540863e6415032cb548410c7723154031d9549510c23d65108108f19153c823d6015231ad185438872d52904318f592530c27a6014c10ad5875090a3c6550c21cb54b509063d63947408f58254cc7a4424c521cb548410433661d53108f18550d0e3d64148108f990534863f6510832cd594418873663946429798f54043a442c8521a758e420cb2c62551308fd95329063e65104219d987540823e6414e108f9885150e6e65d09218f590524c26e6214c10c799153082ba6014e41ab98a411027960150318f197434833651d0020cd94441d023d6094841ce109500cb2e5454830ab98a41082b960106208f19442c426d6214c10ae980521063e6494821e9191210863e61952208f59432d023f6550e218f59253c42366194b408f596540423d63950209bd89534432e6294740ad987438c6ac644c9218f996424c63f65487408fd9421d023c6454810e948421d02ad62905409b588514c32d62d5231e998442c86ba600c540cb94b400c25e6314c108fd95400823e6414c21ab988509063e6590b10ab984424863f654c540c794d40082ad6214c419d58453c827561150308f595438863e6295330c794d40042ae6290921cd58754486b56114e42cd144315033442944328f99053c863d64940318fd94428c23d65cc841e9106214863f6510a108f597438823f6510b31cb50d520c73551144428fd96329063e6414530cd10e5190bc9524c030ae58031d023e61d5120ad5875390a3d6414f10cb50d520432d5290830cb988540876753484218f185540c33b4354032c7552530823e62151108f99253887a75448421cb54950907346494420ab98a41c87245448421ad986428823e64141329798c540823f6055130cd109510823c6454a319b988540c32d5454810ce58054c833642544328fd95430433451485408fd8d54c872c6454810dc546300c2b5618c841cb552520c2b960d0e30d394d5204365528c431cd951510831d5350c219b98a51d0eb96090530ab58042486ae6290531d554e510831d6315021a758c42cc2b56114242b9987424872e528c841cd50e5190a3f6355210cb94842d023c65905208f191520c65e6315010ae58353d023e65d0d20ab98a41cc63e6494331cd98652d02b46150110a798c5110a3e64d4a108fd9642cc27561d5030c795253082b46155130
  | 1 => 0x42b96014e418f986548c3355394642e6909300c23e650c940cdd50414872e52904318fd9152cc33764944328f993514c23d63d5110d6549300c3365110420ab98a51502b661909218f59621d02756115032aed8152502b661909108f59253c833841540318fd91518c33642544308f59053c825d6314810cbd89544c26e62150109e98053486ae6290410c7d4d435023d6414f218f189548c23e64940328fd8d540c23f65107308f990504c66d6214131e950d210863e6590520cb98854c823e6414810cb14a425023f6550c40d9485500863e6494c10ad987404423d65cc9408fd8d509063d6015132ab988418872e62d53109d58453082b66190a40ad993218863d6494e20cd94641082776550441ce552500c63f6054c418f592518cb3a4154031a758c428cab66190b32c7992530823c658c940e910921c423d64944218fd8154c863e6494720f4545300c2b661d4e42b9189314872e52904308f984548cab661909208f597438423d6094b438fd9152c431d6494c208f99353c86b66190932cb948410c23c64549108fd9532106b96094940d654d1004351514c0308fd91520423d6094a41cd944410c32d4394831cb14b215032e52942418f594418823f64540218f98b544c6b56190b408fd9642042ac6250e20cbd0d520c75953880208f597430ca3d6590832d354e520432d6294740ced81544c23c65085408f197434863d65c8540cb94942907374394642e958a5110678654c1208f98b5050e3e6494421ab98a41c432d52d00309e980538872f43548108fd91510ca3e65cc540cd9475090a3f64548308fd9641cc2b96015021ae580325033651104408f19152cc73a54940318b98b54c429d6310b318f58c54c823e65905219718d524423e6415010e9905210867561141328f19543c423d6590630cd9465090b3543944208f595430423e61149409ed95200823d650ca418f99441486b5610cb40ae5805310a3d650c841cd951510ca3f6454f208f18554cc23e6414a108f58e540423e65151209b58b548c69d6390b30cb15121483a441484218f99254487346394642d594e51083394354031ad98432502766114c21cbd91520423d6590440cd946410c2ae6214e418f185548c2b4644c6218f593538423c6254e418f59431d03715194032cd191510c31d53d0c418f195434cb2d4394830d514d314863d64d45308f592530869d6310930a758e424c36a52940318f596420c23f654cb40cd94441c82766194b40cd58652d023d6355030cb551520c27661d5032cd15121c4279601503297d95310c6b66190941cd947400c23c61151108f596420423e6414d10ab1895050eb66190b20ae582424c32e54548108f993538863e61d4143ec501100423d6395220cd545400823e61151108f1855310a3e65107209d19521442746154d20ad58
  | 2 => 0x654c030cbd0e520c7595348020ce591500c69d6310730cd547400c31d53d0f40cb54940042ac6250d32b95864210ba441487209ed95401031d63d52328f992544432e5210830ad986424c23f6550c318f596410c2ae62906209dd95100431d5350c108fd81540c6ad620c5409b596520432d4394a41a758c414c37151540328f99543c823f6510830cd5825190a3d63d5310cb9532188799644c030c798c540863f65104308f195315023e65d0110ad58041486ad6214e418fd9641882ae65109218f19153482b56190841c7d4d4350a3e64940308f592500425e63d5020ad987434c73764946428f19543c823d6394b408f582548863d6494e108f592500863f6590831e6551300c2b66190b418f58e5110a3d650c5409d987540873464544208f997321071d5454c10ab98841087355454430ad98642503355494432a758c5090a6e6214f10ce551500ca3d6414d10cb94a420426e62d50109d584534823d60953328f996414c7366194b43cbd8e529072e6510921ad98442c87a442484218fd9153c438e424c8328f992508cadb654c0308fd97438832d52104308f191518ca3d65d0010cd147315023f65904318fd9151cca3e6510932cd10a510c3a76110921ad986420ca3e6494910cb54a410c23c654ca41ad5845010a3e65d0f20cdd91510caad6310b218f990538823e64d4c20ab98a41d029d63150219b588540c73743944208f986540c2b5610ca418f98754c829d63109318fd9531d031d5390820ad984424c63c64548308fd91534863d6015232cb54e529063e6494c328f984540867b65440108f997434ca3e6415020cd984540863f658c740ced0d500c6b66190a31ae580521063d65908408fd9542106b6618c841c754f40043366115231ae9805390a3c6215120d9d95210863e6295230d94c9510ca3d64942318fd9743c872f43948308f9973250277654c4318f189540c23e6590a319d98453c823e6494c218f59441cc2bb6050e30cd944410863f6550c328f596420823f6510810cd50d510caae62906308f592528c63e64d4931cb15121c823c6454a30cb548420c76a3254032ab98a410872e52104318f185544c26e62d4c10cb50d520c2b661d4e418fd91508c79a544c0308f996424867b6054d218f596428c3376155130ad986420c25e63148109dd85534832f6454830e9d0d21086b66194943ad5865250eb960108208f990504863d60d5231cd951510c2ae62d0e32cb98b540863c65909108d987540863c65501208f59642842b66190831cd54441c833454484218f19521d03354354642ad19231487376094642da549300c3555344010cdd8e5190b2e4394a418fd96420823c6155220cd1825190a3d63d5320a758c410c69d6314041cb54842042ac648cb21ae58041482a56194842cdd0e510c2ba60144429b98b54c
  | 3 => 0xd218f59442cc3346155130ab588501072f6554a41ad584421072c6454830cbd0e52906b561949409d984520423d64943328d98652d0e3d65c87408f992530827561d4c208fd9632d023f6510410ab19132c863c6255031ad98841486ad62947408f592524432d62d5121cb548420c23f64546328f59253483365150020e99865210b695254031d6cc5500c73563946428f191510cb2e52d0010ae58052d02b561948429b98853082b96090710ab98a41c82b66114c428f59053082e56290441ce58054c427960d50319b189544c2ae6110b21ae582420834d52cc030c794e42082ae6290541ab98b539063e6494e20cd109510ca3e65d0120cb948420871e5390810cd552510823e65151318f997329063e6195130cb949400c2b96010a30cd50d510c33a42940318f99250c863e6550d20ae5805110aba6008540ae58031502b66110b10dc545300c2af6254143dc4c5500c6b960d0d30ab98a5150e3d65904318f59641082b46150d21cb55342c8678654c110ab58042c863d6494f218f58c544831d53d0020d9549310c7c9324c120d3549300c23c654c740ab189535023e6194b40b6181314c23f65d0e21c7951530433661d5231cb98252906766114c20ad9845390a3f6454d208f59250886756194b409d98453043a44210521cb948421026e6215031c7591530432e6394a41ad984531063e61151208fd81548863e65d0d108f993538427661149308f19152c42ac6250d218f98b54c423d64145308f19153c43376454420ab9885390a3d6314940cd5475090a5d6314121e948421502e56288421d614d304423d60149438f993514ca7561150208fd8d5010a3d60946428f594410423c654cb40a758c52107366115310cd945400c23d65907308f593528432c64948308f19743c826e6214d109b195324863d6494720e9105214823c658c5408fd91528c23e6495132cdd0d5190b1f5350d41add855050f2f4354830ce109500c63d6494232ae580414c23e6414c208f594428c32e52108318f990530432c54484219e596100423f65108318f99254483345394642c754c41043345110530cb548421063c6454d21cdd0d510ca3f6590830ae580215032c5394a418f590504c6ae62944419e583540cb1d5390410ad98452907365154242ad9875090a3d60550108f194414833960951308f99253c42a56294441cdd0a5190b3964940328fd95404c2ae6294740cd10a510823e6510920e9588418865e6314a108f593524436452487108f5964310a3e6494e10ad98642cc33a4294032b998b414862c62551309e983540c73654944209bd95200833561d53208fd96428c23d6510430e6d01300c23f6590410ad98652d0e3c6454a10cd192510c33964540328f596540823e65cc7408f992500863f6454c218f59250c869d6390a329e980540875b
  | 4 => 0xe909500ca3d650c940ab98a418c6ad6290740cb94842107a662106218f189544c23d6494c31d954a510c23c65909318f18954cc71e53d0020cb949509063e6515110e6d0d300c2b46154143cb94841043394394032e350d320ca3f6454620cd58652d0f1e53d0010c754f43d066c654c920e94c8414872c6094a41ab58b509072e5290410c758c548cb374354430e9d88414863e65d09409d987548ca3d6494030cb153214823d60d5132a758c5110a3e6414e218fd91510c23e6510921c754e410823e6550d109d587548caae6290431a7d8d40cc32e524c8418f992508862e62d5021a758f40cc31d53104208f994414423d6595031ab98a419023d64d4e20d554d51083375394642ae582418c2b66190a328f98b535032d52500309b58b540c33a54500408fd97438423e64d49108fd91528c67661150328f99252c427a6014c21d354d200823e6494d109b98b540c2796015021c754f43d0a9d63d01309d195314863f65d0c20ad58642502ae6290521ad18540c42b5610c940cdd92510c23d63151218f58251d0f3451885408f596424c32e6510b218f58e54842b96014f408f993530423f6590430c754f431023d60151318fd815310b6452485109d587540836a5254031c754c420433665105218f596540cb2f5394a41c759253042796014d218f997435073642944329b58b540c6ac62503208f590504872d6510b218f195434872e6294842cbd50424863661d5232cb50e52042766194b438f597430432e52cca41d394e520432f64948318f58e529063d6494821ad98642cc63e62950308f990540c63d6550e10ab98a414432e52142418f992528c6b4644c521cb54842c423e65105318f59253082b960904108fd95430826f654c832ab58a51d0f2d5494810c754f430423d6414c218f191510833a6454032cb98a511063e65d0d42ab98a414823f65d0c10cd98651106776548421c754d430823f63550208fd8154ccbaa4248020cd909510831d5350e418f590538823d6510b31ae98032d032d5210a318f191508cab66190a108f59250cc63e61151328fd9442cc23e65d0f10ce952500ca9d63106319b98b540c6ad6214241cbd92520c23c6454021ab98841c825d6315010e6105300c33454885108f58f544823d639464297d95320cb2c4394a41e6905300c32c64948318fd95411072e54548319b98853087674254642cd544410c36552c4010d995121086766114132d994a510c23d65104208fd95438823e65ccb40d654e100423f6590b318f98a548434d53c80208f59052842ae620c540cd546410c23e6414d208f995434871d639513097d954310e6c6254d108f997415023c62553308f994329063d65cc5408f99621d023f65108208f597430c2b46150e31e650d300c27561d5320ab98a41886ac62551308e580540863d6494
  | 5 => 0x53482b5610c8418f99642482b66114e41a798c5090ab9600cb40cd9865210ab96010910d614d308432d5454831cdd44414c23e61d4d40d954720082ba6014c42cb94b429072c520c9408f58e544c23c6254f40ad98754c833a54540328f596420c63e6510941d954b419063f6454232ae58352d02b661d4c418f594420c72e5210a318f593538872c5210930cd94e5190a3e62951308fd8d544c2ae6294743cd551510cab563106219b58b53043a442d0521ab98a415023c65485409d584524c32e52d0641ce106500c71d63d5231ad9845090a3d6414e109b58a51d0e5f654c030ab98a414c32d54948318b98a51d023d60d5021ce906500c63d65109309e58053c866f6548421ab98a41cc23c6254c41cbd0e52042af6254d409dd85544c31e5350c21ab98b54c423e6494d219b588540c32e5290a408fd9540102b76154d40bc181214432d4354a41ad98642082b6610cb40cb54d52906ae62d5231cd952510ca3e64943328f194424423c64546308f594414c2b66190521c794d430823d64d4c208f98854c431e5350c10cb952520c759514c030c754d400431e5450c43ad98652d029e63140418fd8d501077251940329b58b54042b661148419758c54086b66190b21a7d8d404c23d6550e20ad98642102b56194b439d987530833a6015021cb15321c823f6454d109d587540cb2e62d53208f99442c4398424c0308f592538871d5494c10c754f430823f6550c438fd9152cc6796014e21cb58a51d0e3f6550842e9151210865d6594c10ad984420872f5294a418f99053c423e6494f21cd547400832e5210b41cd109510c23d6510a108f18950d0f663254432ae58042c82ba600c841cd18a5190a3e6550c219b98b540865f6354910cb149215033943940318f592500822e62d5231ae582428c2766114d208f98a54cc7a74210521cbd92520427661150308f58e54c87a4428c5219d984540823f6550e10ae980329063f6355010a758c509063c65104218fd94410c66f6255130aed81434c31d63152318f594420ca3f6054e42cd9825190aac62501208f590504caae62105208fd96420cb5551cc0308f590534823c6154042c7591530823e65905108f59743c872e54948108f98754087355154242ad986424c63f6590630cb988548ca3e6588540cb94b509073553546428f596410432c52cc940ce951500c72e520ca41ce551500c65d63d4810cd15221c423d60145438f59642cc33464544328f1974344355514c030cb98b548c63c6255010d64c5500c6ad6194842ce592500c63e64d4810ae98053106b661d4a41d354d520427b654c030cb949329063c61550209d99741486ba600c740ad99321486bb6054540e910921442bb6054d409d987540c21d63150219e580530863f6548540ad58a511063c6454620ab98a410c23d60d5232c
  | 6 => 0x29d63907309e980540ca5d6594c20cb191520c63e6415030ae5805390a3d63150218d98754c82b46150d31ab98a41842346155130ab58c42487a63210521d6cc9500ca3e6494c308f99250043a76448421ae58242c833a4254031ab98b5310b2c54c84218f593524c25d6315020a758e414c23d6095032d9949510c31d5350020cd55341887376494420d614d304823d65cc740ad9843210796414c431ab98b434ca3d64d4c10cb58e529063f6510630c794f430823e650c7408f59743082ad62d4e418f994435033561d5232ce10a500cab661109109d58652d0f3661d52328fd8153906b6610ca41c794f43042b661d5232ae58253502b960107108f19151cc35932540328f58f544871d5454c208fd9151cc3d2514c030cd90a510c23c65109318f992508c66d6214e10d554f100431e6494c10cdd4d5190b3661948418f990524c23c65d0f10cdd955190a3c61542428f98b54443a56110b218f58f54086ac6250f218f59543c86b4648c6218f994544863e64d4930ec905100423d64940328f98b54086b56194b40ce50d500ca3e6590910d314d324863f6550010cb18954c87355110420a798c509073551904208f99352c423e6494f208f993514823d65d0e218f997434863d6494b108f99543c432e6194a418f99641c8358534c2208f988544833b4394031c799153042b661909428f992518cb655148020e95865210b2d6094a418fd95430c3345488421ba181214833451905408f994424c76451485208f98654ccb3665106218f597329072c5290941cd192510cab661d0310ab988531071e5494c108f58e5488795434c431c754f32107a46210521ab58a5150e9e6314841ab192324865d63d5010ad98642c4369528c030ab9885310ad9638c030cd50e510cab565106218f195434423f658c841cb98b548cb1d534c8418fd8d548863f6454a109b98a51d033661d53208f99353883a662944418f99053c823c6590b10e6501300c22e62947439d195314423f64544208f994428c63d6095130c754d439029d63906318fd96410823d64d4810cb192520423e650cb40ab58a511072d5290831cd50d510823c6550d31cd545400c2756114e20ae580531072e52108108fd95325026d62150108f19153087d1314c110ced0e500ca3c64544308f593524c71e5454c20cb54a420423c6155332cb548521072e62947438f580544863e6195330c794c410423d60953218fd91524431e53904108f58e521063d60d5131ce992500ca3e62152318f597400826e62d5231c794c41082b66510521a758e410c63c6550110c754c420832d62944418f197430871e53904208f99721503375194642c754d4390ab46150e10a758c5010a3d6590c418f590530431d53d0c428f19153442786054d218f18553d03565354420ab189438cb9a644c0308f992
  | 7 => 0x10126a6000030000c60084480200000c0500400218c208000040ac3000009800c1684900101c0081211001c348dc04c014000000a40780002700210c0080000004c030090600280a00f08475c0782613e0540080a0060000200500e0b04080000c01c01057106060008000aa3b8278340060008580202c5e80d80000a0000181205a4180280600000800001000064008072040a005000004000050330721352b8070021280301820e0080192a00636809000002008000180ec248ad0010020040585e03c29401800014000000170080981a82e0640080a00024c0802c0300280001d00001c000038f19000bc0380102a1100102a0000002300d01c0963d60950318f189509063f6055010cbd48424c23c6154e42e918442486ae62d01208f994315023c6454732cd15121442e765484218f59642cc72f64548318fd95400c23e65151328fd91520c63d65106308f994424436952940318f18950106b960945408f996424ca3f6590a108f595404c33743944329d98754c827461551308fd8154cc66e6214e10cd552510c23e64951318fd8d5090a3d65d0c318f58354486ba600c9408f19152cc23e62950318f594420c2b661949408f59352c42766114e208f596215023e6294740cb94a329067a6014c20c794c420827a6014f21ab98b509063f6550f21ae58051d023e62145408f596414c3655348421ad185535023c6454720cbd4d529063d6015021ce10a500c72d5210a41cb952520c23d60944428f596418832e5290831ab98850107374354420ad987521063e62d52318f195434823d64d4520da4c9500ca3d65950308fd94418833960d5310ab58831d033960d53208f593514cb2c6194a41ad98642086b9600c841ad984428c72c6394a41cb94e529063d6510820ce992500c63f60550328f58c515023e65d0c21c794c420423d65104318f195325023e61149439798c504872d52d00108f590534863f6510420cbd0d52906ae62d4e428f592530ca3e6195032a758c420cab66190a30ce991500c63e61950209b58a51d036552440108f58c54c42ae64885218f189548423e6194b438f98454c82b960104108f987548cb725154032cd90a510823c654c841ad580418867a6015031cd98754086b960109309b988520425d63d50208f988544c63e62947439bd954210a3d6494c10b6181324c23e6215021f2949300c23d6494d10cd94641902b9600ca41ad98642d02b66194842cd5865210a3e62950109b988514c2b661140429b58853c426e62141318f185540ca9e63140428f59732d026d62d5310ab58a51503365114242cb94842c432e5290830ab98b40c833643946428f99250083a64248421cb949400423d63151109e983540cb3654944308f99721d02ac6250c20ad986420433960150219758c528426d6214d10cb58b54c4
  | 8 => 0x2d3c80503c08403001000018028140000080f90200e10807000020028018130000ec2403700e000000074f81e40b00700a0800594f000054030040000000b8620180180186f0d20683f00503c00004802050010010010000000000400a3102a017112be00c07300c05c008120141283383400007009003012004090000020282a8000120400000200202c13812048040d6001000020068050285080b00300006c010093ee00008801080008060000000000281101e07c3e83b00c0040098d4fa104000227c60141c0932280f003804046000068090002540b0040181401c0040040040900f0180901e00b00c0783f07a0020100381502c2c4000040011ec080781a66bc000130520080a00402a11c0d80000201c0580200605c0982001a00400010006018050a80040a40080000803800001010000008010f402c590060023ec538030040100100a0b00340782401e000518090320c062a4c202050030e100002c0602f07a026f800007a0440001c0160c4750890080080000000208c004050100002500818000c0100f06801c0200c0260e4038040060d40c05a0140440100709400807002000070198001720400100017c33c000250103402780700c01c0101e05c02c008b90042e00004402c2781800707009c0004606a0100e8080fe0040a0190002c80300000405401c6200e2900885a01200000009042000000270b407c00000024010005ce1580040582c06e17c1080e0000300a8080100000180002607c0103601
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x90d0e7318652906a4b90a698221c454e414401086ce3314a89852170151210861cb80ca212638a9896015021858e4b2a870842d7598a410c384a948298061c49053154031c4ac530ea98870874549300c217bb2a5208614a5c054c842194cec2a24210c2e761512108617394c3a9a810b9ca6195230a32e720aa018d1973109500cb0b31ca228485c85454048020a4ae42888298616539864204217394c32a0614c9c64254031a4ce3b22a418c2d769485090784a908498061499cb649443286ced212a21071164545300c31930ac02a6214c9c05394642a1ae72906520f4252545300c30aa9cc32104146dd5644c030952e031286106a121580215020eb98ca208438358d5214841a62e02a44210f22701512108617396cb208218358e6215232a54e520ca018e156318e5190ad0b808490a21c4551514c030c48c5b0aa898629601825290668b98c090a210d9c66295010a4ce5b24a210632615805408713312a3208610bdda5290410aa2e029a6290c3575986420821b38ecb21661455cc6094642e228698aa018c367198b5350286b98c329483515cc5448421c2ac6288829852672d91510ca92b94c22a621c250d3254032a4ce3b24a418e15639445090a8b398c128c85435cc6094a41e2686a8a601862a52580329070aa98c2a1821c4545404c03086ce3316a0a1f0952105300c293396c8a88610d5d46150c10c48c430aa898721701512108686392c8a9841c85494044010c2ca730c841042e7299543c4312a94c3210210e5c0654c841b0ae62126290c3671997430868cbac8298061c254d4048020e20e8a8a60184a47258c414869338ec929021499c46394a41a4ce3b22a4184c9731812148293396a6a8c850b9ca65d0c21a62e0314a321514715915304217394c22a2210e5c06254c41c4cc4a8c82105a2719092008293396c928861465d6424c030b0ae63088490e31601825190ac2b98c420a43491d44248710a4ae3310a91960d5398a4104313312c3aa641499c86394642b44e520a2008709539092008292b8ca421681c4546414c030a92e429a610842e72d91510c385ba2a498061541d5314c11083ae6328829042e72d9641cc30ab1aa2288858c1456010530e14c8a92601862552986420c616392cb98a81491d54348421c4aa530c841843575986420c30ca9ac1210410d9da4254430a4ae3310a9904347159732502923ae86908430d5d66190810e1484992a01970952d01300c292b88a421261435cc520c940b42e020a4290619639805408686b98a8908434a9c05394a41c52a4b00a420d8672905310c6c2b98a8908430e1d5601091086ce3b2c65a05317018e5190b13312c3aa465459cc6294642a64e0314a3215297014e5290616392c9a8a61295c662d4c4286ce3b2c85185247250d51082923a88490a210d9c665d0f20
  | 1 => 0x510cb83398a8908438394e6290410992e4302629862452584325029938c8528065499c86094642c4cca2168290e2676151210861b3b48528861075cc6510b10a4ae5308a918e0e63948509070cb1ac02a0434a9c06394a41ac2e02a24210c34715954388388a8882980610b9ca6550c21c1aa73148210515731512108698b8084a8841891912154021c4ca530c84185247150d5204294b80c7294838358c5210930868e2b26a49862a52980329060eb98c4a80830b9ca619533085ce532e878852970186529070ab1cc22a4638c145600c54094ae530ea620d2675d884148695380c3294830b9cb658c740c1ac631ca520d0e731825290782a1aa4988630d9c66295030a4ce3a9aa520d1973105500c61b38cc52a661685c06110921e82a528a601852674d9521086523b26420a438358e6215021e1286a92601860e5398a410821b3b6a6a8c850d9da4254432a48e8a9a4210c9573986420c65238ac0212430d5da5114242a52e02a24210c1d73194424420eb98ca10a814c9c06394642b24e321260185a1701884148693388c1294834c1c56454031a0ae62a24210ca97098a4108216bacc52086389588510c540a1ae62a64210c2d7598a41043892a2a298061685c05448421948e4b008290c2e729875050e9338ec9290618c545601444286ce3b22a4185327190a500c706a98c4a18410b9ca6195130c1ac6a908218c2e72d96410c29539482a8063c4547404c030e24c8a8a601851975991300c29938c84a8065c2591524c030b10e4b2260184a4761093148713292c219483499d46110921c34c6b00a810d2672d915108384aa2a498061495c05448421c32a6b0084104a47158c4248712b14c3aa463495cc5448421872e032e8610d157315221086933a4a8908438a1496010930a2ae6212a21971374545300c258b80c2a18218558e611502186ce332a8610d2671d91520421cb80c2a98850d9d8544842185eed2948218624525864250312b10a320a810d9c46590910c52a4b00820843471594424c298b80a890843491d44148520e0aa6a1a4210ca676d512108714292c01928189195210854086ce3314a918685634c84148698b80a728c85c2549404c03085ce5b2c831862762185544c294392c8a80658554e6190810c4cc528c8218711535011004388a1aa298061d0549514c030e1686a9260185497014d32486c838ac8980610e5c06550c21e14a8a92601851973909500ca17bb2a520863c15cc5448421c32a6b04820858671909320ca16392ca20a61455cc510c540e2484a8a601851975109300c2c53948298061c254a424c030a32ea20a601860d639485090715312c02a6410d5d6619083286ce332a87905157318a5190aa8b88a6984410bdd9529041086ce3b2c84185517114d30482a43aa64982410b5d46250c20a4cea31082
  | 2 => 0x260a8754a005f0101e2447248060002844a233040000a0500801ea0106800001000064304b020ac007004004043f03004000001000060a3181400d815814020000098001c0000004cc0282414000300000023f0302200080481c021100004002b0006c01078f0000200388023604030001801010022f00004000d089e01e790a0004a00009948209020140c04078006a02000147000760202a014180404030420400010104000060521c6e44000587e001c0000a00159cc3a0f4b028001b05f1042545300c2173b6a6a9483499d8544842183ae630aa0215257294441d0268b88c0992612c5c26190810c32a6b008208705434c9
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x4e1048a503400d220c0020000581667468c02952050064010c11735806094642b0282dd1514c030a21829856015310921859c64248020d01539c64248020a0983149600c940a21809895190420d01735c05448421b0082591514c03091287909514c030905831d44248710921801c54354810d02735c05448421d0272546414c030b0281dd1524c030911859c6424c030921801d54348421a0583149610c940920855c04248510911839c64254031c05635ca6115231905859c6424c8329048754d4348421b02829053154031921859ca4144010c05635c66215232c09735806094a41921801d74348421c057354a61908318a1801c56310921a05831952108540a1183145600c540a21811496010930c09535c06250c20b0081591524c030909859ca414c030905831d4424851090887591524c030c09635c06394a41c05635c85110530c05635c45210930885831c96010521905831d44148520c11535c26190810c09535c26290420c0573588510c5408a1801c96310521d01739c05448421a21821456010530d01529c6424c030d01539ca4144010a0983949600ca41c11535c06150c108a1801d9321052190b8754a414c030c11635c06394642905859ca414c43191087591514c0308a1801d8424c521a21819896015320921801c94354420c21525c26190810b02819093254032a0583949610ca41885831c56010921
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 48
  | 5 => 1044
  | 4 => 1671
  | 3 => 343
  | 2 => 65
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
  | 6 => 2*((h/30+packedAt s5K6 (768+(h % 30)*6) 6) % 48)
  | 5 => 2*((h/355+packedAt s5K5 (28188+(h % 355)*11) 11) % 1044)
  | 4 => 2*((h/585+packedAt s5K4 (63498+(h % 585)*11) 11) % 1671)
  | 3 => 2*((h/170+packedAt s5K3 (16807+(h % 170)*9) 9) % 343)
  | 2 => 2*((h/28+packedAt s5K2 (3900+(h % 28)*7) 7) % 65)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf0fe3ffc3e3e3ffe1c71fc7f1c387ffe18f07f
  | 1 => 0xff1fc3ffc03fc78fe07e3f8fe03f8e1e673993
  | 2 => 0x1ffc3fffc007f1ff803ff1ffc00fe187ce1c
  | 3 => 0xffe0003ffffff801ffffc001fffff001f80fe0
  | 4 => 0xffffffc000000001fffffffe00000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x14028004084841000410481204082288085025
  | 1 => 0x2244188884940a106022148520930454232892
  | 2 => 0xa88099114049402a880252149810944858a18
  | 3 => 0x40012222202000251144800092244001500540
  | 4 => 0x8cd1b303b9392749de793a4803066199fef000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfee8fea8fee8fea8fee8fea8fee8fea8fee8fea8fee8fea8fee8fea8fee8fea8fee8fea8fee8fea8fee8fea8fee8fea8fee8fea8fee8fea8fee8fea8fee8fea8, s5N, s5R, (fun _ _ => 0), s5I, []⟩
end PEqualNP.Outside.L_meta_36370
namespace PEqualNP.Outside.L_meta_36370
open PEqualNP.Outside.L_meta_36370.Model
def q6K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q6K3 : Nat → Nat
  | 0 => 0x880000303b90f820e84378cbd905c32
  | _ => 0
def q6K2 : Nat → Nat
  | 0 => 0x10310c821e02108320c820
  | _ => 0
def q6N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
  | _ => 0
def q6R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q6K4 (i*4) 4
  | 3 => packedAt q6K3 (i*15) 15
  | 2 => packedAt q6K2 (i*26) 26
  | _ => 0
def q6I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q6K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/16+packedAt q6K3 (90+(h % 16)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q6K2 (78+(h % 8)*2) 2) % 3)
  | _ => 0
def q6Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffbf0fffc3fe3f
  | 2 => 0xffffffffffffffffffffffffffdff0fffc3fc7
  | 4 => 0xffffffffffffffffffffffffffffffffffffff
  | 5 => 0xefff0fffc3f8
  | _ => 0
def q6Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffff41e222e2661b
  | 2 => 0xffffffffffffffffffffffffff222e45662ac5
  | 4 => 0x4448988916e
  | 5 => 0x1888ee3323b0
  | _ => 0
def q6Atlas : Atlas := ⟨4,rawDecor 54 q6Pos q6Neg, 0xfcfc0000c0c00000fcfc0000c0c00000fcfc0000c0c00000fcfc0000c0c00000fcfc0000c0c00000fcfc0000c0c00000fcfc0000c0c00000fcfc0000c0c00000, q6N, q6R, (fun _ _ => 0), q6I, []⟩
end PEqualNP.Outside.L_meta_36370
namespace PEqualNP.Outside.L_meta_36370
open PEqualNP.Outside.L_meta_36370.Model
def q7K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q7K3 : Nat → Nat
  | 0 => 0x220205d32be6534cb7196d32
  | _ => 0
def q7K2 : Nat → Nat
  | 0 => 0x2350e32
  | _ => 0
def q7N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
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
  | 3 => 2*((h/8+packedAt q7K3 (75+(h % 8)*3) 3) % 5)
  | 2 => 2*((h/1+packedAt q7K2 (26+(h % 1)*1) 1) % 1)
  | _ => 0
def q7Pos : Nat → Bits
  | 1 => 0xfffffffffffffffffffffffbfdcf3e3f3e74cf
  | 2 => 0xfffffffffffffffffffffffdfef3cfc7cf9b33
  | 3 => 0xebf03f3f80fec3c
  | 5 => 0xf3ffc03fff00fc0
  | _ => 0
def q7Neg : Nat → Bits
  | 1 => 0xfffffffffffffffffffffff404104009020045
  | 2 => 0x208041042040112
  | 3 => 0x150aa0690a94c28
  | 5 => 0xe082ab24a14e80
  | _ => 0
def q7Atlas : Atlas := ⟨4,rawDecor 46 q7Pos q7Neg, 0xfcfcfcfcfcc0fcc0fcfcfcfcfcc0fcc0fcfcfcfcfcc0fcc0fcfcfcfcfcc0fcc0fcfcfcfcfcc0fcc0fcfcfcfcfcc0fcc0fcfcfcfcfcc0fcc0fcfcfcfcfcc0fcc0, q7N, q7R, (fun _ _ => 0), q7I, []⟩
end PEqualNP.Outside.L_meta_36370
namespace PEqualNP.Outside.L_meta_36370
open PEqualNP.Outside.L_meta_36370.Model
def q8K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q8K3 : Nat → Nat
  | 0 => 0x2800002f185c31ba6578c6f995c30
  | _ => 0
def q8K2 : Nat → Nat
  | 0 => 0x296418c251053298404ca690231
  | _ => 0
def q8N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
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
  | 2 => 2*((h/15+packedAt q8K2 (104+(h % 15)*2) 2) % 4)
  | _ => 0
def q8Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffddf1ff3f1ff0f3f3
  | 2 => 0x6efe3fcfe3ff0cfc
  | 3 => 0xfffffffffffffffffffffff7ffcffffc7fff1f
  | 4 => 0x78fff00fff800fe0
  | _ => 0
def q8Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffa21c824304926171
  | 2 => 0x11258415212624b4
  | 3 => 0x840280848488a0a
  | 4 => 0x7892eae920ccfc0
  | _ => 0
def q8Atlas : Atlas := ⟨4,rawDecor 30 q8Pos q8Neg, 0xfcc0fc00fcc0fc00fcc0fc00fcc0fc00fcc0fc00fcc0fc00fcc0fc00fcc0fc00fcc0fc00fcc0fc00fcc0fc00fcc0fc00fcc0fc00fcc0fc00fcc0fc00fcc0fc00, q8N, q8R, (fun _ _ => 0), q8I, []⟩
end PEqualNP.Outside.L_meta_36370
namespace PEqualNP.Outside.L_meta_36370
open PEqualNP.Outside.L_meta_36370.Model
def q9K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q9K3 : Nat → Nat
  | 0 => 0x8000080437996c32dc43b0876906f20
  | _ => 0
def q9K2 : Nat → Nat
  | 0 => 0x808c434829907328e43886910520
  | _ => 0
def q9N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
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
  | 3 => 2*((h/23+packedAt q9K3 (90+(h % 23)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q9K2 (104+(h % 8)*2) 2) % 4)
  | _ => 0
def q9Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff3ffff1ffff1ff
  | 2 => 0xffffffffffffffffffffffebfc79ffe387fe4f
  | 4 => 0x72ff81cffc070f8c
  | 5 => 0x7cfffe0ffff80ff0
  | _ => 0
def q9Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa018100104912095
  | 2 => 0x142322862122c64a
  | 4 => 0xd49751b48546b8c
  | 5 => 0x38241ac92608d60
  | _ => 0
def q9Atlas : Atlas := ⟨4,rawDecor 53 q9Pos q9Neg, 0xfafaaaaaa0a0a0a0fafaaaaaa0a0a0a0fafaaaaaa0a0a0a0fafaaaaaa0a0a0a0fafaaaaaa0a0a0a0fafaaaaaa0a0a0a0fafaaaaaa0a0a0a0fafaaaaaa0a0a0a0, q9N, q9R, (fun _ _ => 0), q9I, []⟩
end PEqualNP.Outside.L_meta_36370
namespace PEqualNP.Outside.L_meta_36370
open PEqualNP.Outside.L_meta_36370.Model
def q10K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q10K3 : Nat → Nat
  | 0 => 0x6500002f995d31b86174caf185f31
  | _ => 0
def q10K2 : Nat → Nat
  | 0 => 0x4048d420c25504308d42cc6550732
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
  | 0 => 0xffffffffffffffffffffffdff7fcfc7ff8f3cf
  | 2 => 0xffffffffffffffffffffffedf99f3f8e3f3d33
  | 3 => 0x76fe1fcff03fce3c
  | 5 => 0x78ffe00fffc00fc0
  | _ => 0
def q10Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa010010012080045
  | 2 => 0x1224284484922512
  | 3 => 0x941501921248a28
  | 5 => 0x7851aae4986af80
  | _ => 0
def q10Atlas : Atlas := ⟨4,rawDecor 45 q10Pos q10Neg, 0xfaaafaaafaa0faa0faaafaaafaa0faa0faaafaaafaa0faa0faaafaaafaa0faa0faaafaaafaa0faa0faaafaaafaa0faa0faaafaaafaa0faa0faaafaaafaa0faa0, q10N, q10R, (fun _ _ => 0), q10I, []⟩
end PEqualNP.Outside.L_meta_36370
namespace PEqualNP.Outside.L_meta_36370
open PEqualNP.Outside.L_meta_36370.Model
def q11K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q11K3 : Nat → Nat
  | 0 => 0x20001dd32be6534cb7196d32
  | _ => 0
def q11K2 : Nat → Nat
  | 0 => 0x2350e32
  | _ => 0
def q11N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
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
  | 3 => 2*((h/8+packedAt q11K3 (75+(h % 8)*3) 3) % 5)
  | 2 => 2*((h/1+packedAt q11K2 (26+(h % 1)*1) 1) % 1)
  | _ => 0
def q11Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffbfdcf3e3f3e74cf
  | 2 => 0xfffffffffffffffffffffffdfef3cfc7cf9b33
  | 3 => 0xebf03f3f80fec3c
  | 5 => 0xf3ffc03fff00fc0
  | _ => 0
def q11Neg : Nat → Bits
  | 0 => 0xfffffffffffffffffffffff404104009020045
  | 2 => 0x208041042040112
  | 3 => 0x150aa0690a94c28
  | 5 => 0xe082ab24a14e80
  | _ => 0
def q11Atlas : Atlas := ⟨4,rawDecor 45 q11Pos q11Neg, 0xfafafafafaa0faa0fafafafafaa0faa0fafafafafaa0faa0fafafafafaa0faa0fafafafafaa0faa0fafafafafaa0faa0fafafafafaa0faa0fafafafafaa0faa0, q11N, q11R, (fun _ _ => 0), q11I, []⟩
end PEqualNP.Outside.L_meta_36370
namespace PEqualNP.Outside.L_meta_36370
open PEqualNP.Outside.L_meta_36370.Model
def q12K3 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def q12N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q12R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q12K3 (i*3) 3
  | _ => 0
def q12I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q12K3 (3+(h % 1)*1) 1) % 1)
  | _ => 0
def q12Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffbecf
  | 2 => 0xffffffffffffffffffffffffffffffffffdf73
  | 3 => 0xefbc
  | _ => 0
def q12Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffff4205
  | 2 => 0x2412
  | 3 => 0x1828
  | _ => 0
def q12Atlas : Atlas := ⟨3,rawDecor 13 q12Pos q12Neg, 0xfaa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0, q12N, q12R, (fun _ _ => 0), q12I, []⟩
end PEqualNP.Outside.L_meta_36370
namespace PEqualNP.Outside.L_meta_36370
open PEqualNP.Outside.L_meta_36370.Model
def q13K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q13K3 : Nat → Nat
  | 0 => 0x8002c02f98dd31bc6170c2f995d32
  | _ => 0
def q13K2 : Nat → Nat
  | 0 => 0x9541cca350b3195410c2350830
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
  | 2 => 2*((h/8+packedAt q13K2 (104+(h % 8)*2) 2) % 4)
  | _ => 0
def q13Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff7fcfc7ff8f3cf
  | 1 => 0xffffffffffffffffffffffedf99f3f8e3f3d33
  | 3 => 0x76fe1fcff03fce3c
  | 5 => 0x78ffe00fffc00fc0
  | _ => 0
def q13Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa010010012080045
  | 1 => 0x1224284484922512
  | 3 => 0x941501921248a28
  | 5 => 0x7851aae4986af80
  | _ => 0
def q13Atlas : Atlas := ⟨4,rawDecor 43 q13Pos q13Neg, 0xeeaaeeaaee88ee88eeaaeeaaee88ee88eeaaeeaaee88ee88eeaaeeaaee88ee88eeaaeeaaee88ee88eeaaeeaaee88ee88eeaaeeaaee88ee88eeaaeeaaee88ee88, q13N, q13R, (fun _ _ => 0), q13I, []⟩
end PEqualNP.Outside.L_meta_36370
namespace PEqualNP.Outside.L_meta_36370
open PEqualNP.Outside.L_meta_36370.Model
def q14K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q14K3 : Nat → Nat
  | 0 => 0x10000c4d32dc65b4cae995f32
  | _ => 0
def q14K2 : Nat → Nat
  | 0 => 0x2350e32
  | _ => 0
def q14N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
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
  | 3 => 2*((h/8+packedAt q14K3 (75+(h % 8)*3) 3) % 5)
  | 2 => 2*((h/1+packedAt q14K2 (26+(h % 1)*1) 1) % 1)
  | _ => 0
def q14Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffbfdcf3e3f3e74cf
  | 1 => 0xfffffffffffffffffffffffdfef3cfc7cf9b33
  | 3 => 0xebf03f3f80fec3c
  | 5 => 0xf3ffc03fff00fc0
  | _ => 0
def q14Neg : Nat → Bits
  | 0 => 0xfffffffffffffffffffffff404104009020045
  | 1 => 0x208041042040112
  | 3 => 0x150aa0690a94c28
  | 5 => 0xe082ab24a14e80
  | _ => 0
def q14Atlas : Atlas := ⟨4,rawDecor 43 q14Pos q14Neg, 0xeeeeeeeeee88ee88eeeeeeeeee88ee88eeeeeeeeee88ee88eeeeeeeeee88ee88eeeeeeeeee88ee88eeeeeeeeee88ee88eeeeeeeeee88ee88eeeeeeeeee88ee88, q14N, q14R, (fun _ _ => 0), q14I, []⟩
end PEqualNP.Outside.L_meta_36370
namespace PEqualNP.Outside.L_meta_36370
open PEqualNP.Outside.L_meta_36370.Model
def q15K3 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def q15N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q15R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q15K3 (i*3) 3
  | _ => 0
def q15I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q15K3 (3+(h % 1)*1) 1) % 1)
  | _ => 0
def q15Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffbecf
  | 1 => 0xffffffffffffffffffffffffffffffffffdf73
  | 3 => 0xefbc
  | _ => 0
def q15Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffff4205
  | 1 => 0x2412
  | 3 => 0x1828
  | _ => 0
def q15Atlas : Atlas := ⟨3,rawDecor 11 q15Pos q15Neg, 0xee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88, q15N, q15R, (fun _ _ => 0), q15I, []⟩
end PEqualNP.Outside.L_meta_36370
namespace PEqualNP.Outside.L_meta_36370
open PEqualNP.Outside.L_meta_36370.Model
def q16K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q16K3 : Nat → Nat
  | 0 => 0x14200000004002f195c31b86578c6f985d30
  | _ => 0
def q16K2 : Nat → Nat
  | 0 => 0x200c8c424c25906328e428c6510530
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
  | 3 => 2*((h/23+packedAt q16K3 (90+(h % 23)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q16K2 (104+(h % 8)*2) 2) % 4)
  | _ => 0
def q16Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff3ffff1ffff1ff
  | 1 => 0xffffffffffffffffffffffedfc7f3fe3f0fe73
  | 2 => 0x76ff8fcffc7f0f9c
  | 4 => 0x78fff00fff800fe0
  | _ => 0
def q16Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa0180202049440a5
  | 1 => 0x122324452122a652
  | 2 => 0x9416819484a2b18
  | 4 => 0x78a4eae920ccde0
  | _ => 0
def q16Atlas : Atlas := ⟨4,rawDecor 23 q16Pos q16Neg, 0xe8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8, q16N, q16R, (fun _ _ => 0), q16I, []⟩
end PEqualNP.Outside.L_meta_36370
namespace PEqualNP.Outside.L_meta_36370
open PEqualNP.Outside.L_meta_36370.Model
def q17K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q17K3 : Nat → Nat
  | 0 => 0x8006521ea43bc87690f621
  | _ => 0
def q17K2 : Nat → Nat
  | 0 => 0x2950a21
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
  | 0 => 0xfffffffffffffffffffffffbfd99fe39cff07f
  | 1 => 0xfffffffffffffffffffffffd7e1e4fc1f73993
  | 2 => 0xe7fe073fe07ce1c
  | 3 => 0xfbfff83fff80fe0
  | _ => 0
def q17Neg : Nat → Bits
  | 0 => 0xfffffffffffffffffffffff404220008410025
  | 1 => 0x289509244a2a892
  | 2 => 0x19115069424aa18
  | 3 => 0x60002921000540
  | _ => 0
def q17Atlas : Atlas := ⟨4,rawDecor 15 q17Pos q17Neg, 0xfea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8, q17N, q17R, (fun _ _ => 0), q17I, []⟩
end PEqualNP.Outside.L_meta_36370
namespace PEqualNP.Outside.L_meta_36370
open PEqualNP.Outside.L_meta_36370.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x142542004008001fd10007fd0801ff41007f10001fd40006f50001fe40007f48001fd41007f84001fd42007f48401ff40006fd0001fe20
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x38a83800002039600008381008c00800087038b9000818b010006928222b4848080023b0a8b85800d000003000b0081008001028080a507000181828010801e832fd65484017fb0a4000bfd891001ffaa488003bd21d0019ff32a4202bf58d1005ffac690807fc6244005dea1a2002fe8c11002fda6490003fd6148007faa8a200bdfd4d21067feca9082ff53148413dfb2a8008efd8d4006efea6a081bfd65480013fb2a8000cfd9540007fec29000bf93044001fe902200eff4c34105dfac690803ed21480015e3224208df54d40007fac090802fd6188001fe3024200ef4854000776c0a002fff534840bfea9a4006ff54520017fa6488003bf4044019f6a924205efd0d200057ac9100233f5350015dea8e800fdfd4d4207ffca6a1033fd504840fdea9e8007af990400057ac90803b7d53d0405fa98a2008ff54d40045fec6a0016fd6348003ff1922000bf58a100477e86a002ffd3048417fea9a4200af9921002f7a8690026ff6550019faa8a420befd0d210577aa5a002eff634840b7fb1a400bfb4c921016fea688043fd30d0803ff3122004ffc412002ff46090017f9304800bfe98a400cffd4121067fca0908377d535041bfea9a8207cf54f40007fec09081ebd63d00115eb24800cff1412100ffe4088023bd325000d7fb2a4004ff9452001ffeca8801fbd31d0019fe32a4200efd012005efaa690803bf6448401dea022008afd8d40005fec09083f7d5350811dea9a8002ffd8d1003f7a65a0033fd65484197fb2a4208cf54d4001dfeca88027bd5150009fe30a4000af99220007fac4880437d53d08057fb1a2005ffd8d2007ffaa6a1003f5214400bbea9a4005dfd4d2004f7aa4a0017fd63480017eb122010ffcc34203efaa7a002fbd4348401ff3024206fb54920035faca90013fe61480139e32a8002df54d10037feca90022bd63500077eb2a2000ef1912103d7ec7a000bfd534400f9fa9e8008dfd4d400057ec89082ffe3048405dfa1a2002ff58d1005ffec690807fe5244009ff18a4008ef4c5400077a809000ffd6544013df2a28000ffd8910
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x42118121006fa30d8910006be53d9121006bd53d9121005bd7319121004bd70191210f73f53485400073d53d9121026f4615852000fe720485100c6ef654852008fb743485100afe421d8121006bd43d81210deee32d81210b6ef21d89100beef63485200b6ed21d8910006ed52d8520006bc63d9121004fd75d8121005bd70d9121007b551191210067e73d95400073f53d91210ef3953d8140006bd6519121006bf4358910006f531d8910006bf764874008f755348510006bf74d81210e6ee52d8520007e76148520006bd63191210047f7558910006f551d89100067d5358910004fd7358910006fb60981210073d73d9540007e87048520027e6314852000eef20d8910005df7358121004bd73d91210657c7558121004bd7319121005bf7048540096f7654851008f775348510006f930d8520004fd7558910006bc53d91211173f5348740007eb70485200067f53589100e6ee32d8520006bd43d8520006bc63191210ffad52485400b7e42198121006ed32d8121026f65158910007ad32191210047d73d95400057d75181210c6ed6548520006bf64d8121007ad52d9121024fd7648110006bf43d89100073d53191210bfe93048520006bf53d9121006f531d8121006bc64181210057f75585200063f63d9540006bc74589100d5ef75485200bfad4348520006be63d9121006bd63d91210053f73d9540006bf6150120006f551d8121004fd75d89100067f75589100067d53d89100073f5319121006bd4358910006ed52589100063d53d9121007f07048510005bf7048740006f77158910006fa30d8520006bc64d8121006f96018121006ed32d8520004fd73d85200067f53d8910006bc6458121097e5524851010dbf7548540026f621d85200067f73d954011fad5248740006bf7458910026f631589100b6f651d8910007ad2150120007f370485100b4ff725891000fe65248510006fb70589100067c73d9540006bf61d01200073c73d95400b6f62158620006bf65d912108ff1304851000eee52589100f6bf6348540026ed2158a10026ef2158a100073e73d9540007af7448520004ff73d8520004df73589100defa20d8121006f93058910005f77148110004fd75d852008fb54348510027e42158121006bd3019121007ad52191210f7ad32485400057f7558910006bc74d812100fe63248510007b94048110007ad32d9121006be631912100eee32589100a5f775485100adfb70589100ddfb7058520105bf73485400b6f631d891012dbf75487400063d5319121007e521481100bfe53148520006be65d91210cdef7348520004fd73d8910007ad21d01200bfea3048520004ff73d891008ef5634851000eec62589100073f73d9540007e762485100053d73d9540117ad3248740096f56548510007b521501100063f43d9540
  | 1 => 0x40008940040085c08000404400050082c0ae600004780003800020a0180404010003cf44f0201000050a000220603b9002068580c06250382000000380c16030382802001a00028030a0080400008141601098d40044000180c250100c002800004089d1b0a1202c0a8101a000080c0a060504c120600810000300070ea14018000200005dd7318121006bf43d8121006ef7258910006bf6458121006bd6250110006bc6498121006bc301912108fe53248510006f930d8910006bc7648540125bf7348740006bf63d91210057f75581210067d53d8121006bf65191210067d53d8520006ed3258910007b77448510006bd43d8910004ff75d8520005bd7019121007ac7448520004ff7358910006df7358910006fa30589100c7e55148520004ff73d81210067f53d81210f7b531485400d5ed75485200aef651d81210cded734852009df77348510006bf43d85200acff705891008ff230485100067d73d9540006ef62481100067c7558910006dc735891010dbd75485400e6f521d85200ffb5514854000fe46248510007b521d0110007b531d9121105bd7348540006bf3019121027e4614852000ef52158620006bf625011011fb55148740006bd62d0110026f710d85200657e7518121027e71048520004ff75d8121004ff75589100bfaf4348520007b551d9121024ff7158910006be3019121006bd65d9121005df73589100067f53d85200beed6348520004fd73d8121005df7358520117b53148740116bd63487400aef631d8121006f531589100aefa10d8121005bd73d912108ef763485100deee52d8121026f661d85200bf6d53485200a5f57548510007b47448510006ed52d8121006bf63191210047f73d95400063f53d9121125bd734874012dbd75487401173d5348740004ff75d8910006bc65d9121004bc76485400f73d53485400bf6f534852000eee62d8910006f5515891009df57348510006bf62d0110007b53119121027e65148520137e
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xbc9831c1214800183ac7b9ecaa0003c954951191210064e398c8b024200e1c7354f6448451c5ae4a9ec8908a7c908753191211479210aa7b224200a3d8598f644840157300318c8908022f61e30191210047dc3ac03024200c5e43dcf6550001cb2a6986c48800317e1773589100061f426e7b2a8000cb9708c064484018be61b9ecaa00030fdd153d81210045e43a87b02420093e871cf655000117d0fb22c090802f460c7048510007d090a809022000c3f73d4f6448401c3ae7b1ecaa00030fdd764581210076898a60b122000a3f8558b40440010fd0e39ecaa000347cc373d95400064e3a0e6b122000d3b60dcf6550001c3a8639ecaa0002a7e0d62d01101561f3b6a63224200e1d5350d624400187d0cb9ecaa00030f5cf53d91210070ea9a87b0a40009ac87485404800193ae6980c8908022f61f30191210064fb26e6b02420087e87d4d624400187eeaa1ac48800387d8d53191210061ea98ec90a80009b487485404400153b0732ec8908022f61c30191210060ea1ee7b2a8000e6552547604840183ee6a9ec890803171d773589100061eba6e7b2a8000c9f7350d624400147d0db9ecaa00030fdd153589100068fb9ce7b2a80008bd874c0644840117f0eb28c8908024f61e73d954015f1ab8aa7b224200c3d63dcf655000187ae6a98c890802ae60074d81210045f43e87b024200c9f7354f644840147d0c39ecaa00031750f73d95400054f41ccbb22422be2e7254f644840193ee839ac4880034ed8173d95400051ec3aa7b224200e1d3054f644840187ae0a9ec8908030f54d70191210064eb98c63224200c5f739cf6550001d28c6988c8908030f61573d912113f9210aa632242008bf831d9215000187ec1b9ecaa00035908775581210045f43e86b1220008bf8758c64484018b90bb9ac4880021f61e73d95400055cc06e9b024200dc421dcd604840187eeba1ac488002ab60830191210051ec28c63224200c9d73cc0644840193ee7a1ac4880028f61663191210051ec28603224200c5f73d4d624400147b0a31ec89080387d8d53d91210070f39ec7b2a8000c3d635cf6550055c6ce3a9ec89080317dd773589100068fb1ae7b2a8000c3d845cf6550001c3aa6a1ec090803075cf63d95400061fb9ec7b2a8000c3d43dcf6550001da262986c4880030fdcd53d91210070e31aa7b224200d1f7354f644840187d0db9ecaa00a30f9d953191211579210ea7b224200e1f7354f64484010fd0ea9ac4880030fe1f63d95400055cc00c7b224200c5f7354f60484010fb07baac4880038754d43d89100064fb9ca7b224200dc4215cc6048401e4aa4a8ec8908030f5d173d95400049f436e7b2a8000e8c634cb6448401ac842ba8c090803271cf64581210061fba8c8b024200e1f3054f644840157300320c0908ab8b5cb53d9121
  | 1 => 0x40a220014020a041002162e000002051200005a3a06001218021402061a0170060000000c04000a240236360230000426080006025800080200060a802884000e001e000642060202d72a100204021c00000250083a506e0a0200080218000a1e06a2101800040a1a0226000800c3f605cf655000187ae6a9ec8908038758f73d95400064e326e6b0242008bd831d92150001a3ae6a98c890803365cd60181210061fb9e87b2a8000c9d73d8c6448401cb2a6982c4880022fe0173191211671ab8ea7b224200c3f74d4f6048401cb2a6986c290003275cc63d91211471b38aa7b224200c3d435cf6550001878ebba2c488003a318d32191210064e322e63024200e1d534c0644840117f06b80c890803b24c930589100061fba8e8b122000c9c74dcd624400187d08b9ecaa00021fe1573589100051ec2e603224200ec9324c361480011bd0e39ac4880030f5cf43d95400062fb9aa6b1220008bc8750d624400187ae7b1ecaa00030fe1570191210061f3a6e7b2a80008bd8798c64484018bf06b9ecaa0003279cc64181210061fbaee8b122000a3f855894044001c3a87b9ecaa00030f61373d95400064fc26e6b122000c3f531d9215000187cedb9ecaa00028fe1f53d91210054fc1ac4a022000c3d75190604840157500318c8908039954951589100061f42ae7b224200a3f8754f64484018beea39ac488002ad60430191210051f42cc7b224200e1f8354f6448401a3a61b9ecaa00030fdd353589100046fc1aeab122000d1e63dcf655000147d0a31ec8908022f61e53d91210061eb86a7b224200d1f835cf6550001c38c6a98c890803075cd53191210074a31a63b22420087e871d5624400147b0fa9ec8908022f61c53d91210064fba6e6b122000c9c84dcd6244059c5ce5a9ec8908030f1d764581210070ea9e603224200d1c635cf6550001972e0980c8908030f9d173d95400068eb1ee7b2a8000e1d631cf65500018ba61b9ecaa0003275cf63d91210061f3b2e7b2a8000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x30000b8002000300e44034580400100040006ad840212e828508000154595087735812100507e6163dcf6550001619901cd53d9121007065c13054f644840141f9850f73d954000607613835cf655000151b9058f73d95400070364b7354f644840181c8754d43589100050764e865cf65500016899018d32d912100706e4163dcf6550001c0f9258f73d95400050764f87d8f655000141f9058f73d954000526640645cc6048401d04215cd53191210060761573cc06448401c0d72dcd53d9121005a2640634c8644840181d8354c76485400050764e845cf65500018997360063d91210050765e73d8f655000141f9361173d95400060761d53cc0644840141f9361573d9121005866406354f64484013a09848540481100050764f60dcf655000181e98dcd53d9121007056477354f6448401c19535c1301912100551654215cc6048401c149158f73d95400054664263dcf6550001d0421dcd53d912100607a1d5350f604840141e97cc153d912100507e5f6354c644840181d83dcf43d95400048766273d8f655000121e98dcd53d9121007055c77354f644840181d855cc63191210060761d534c0644840116598085751812100607a1d5350d624400181d98dcd53d912100459a6021dd5604840141d90dcd53d912100607e1784dcd624400141e9754d435891000703a4b7354f644840141d94cc373d954000570640215cc6048401c1691dcd53d912100607613739cf6550001c0c9258f73d9540005a4640634c7644840181d83dcf63d95400050764e855cf6448401c179158f73d954000507e4d7054f64484016199018d531912100507e417354c644840181f9858f73d9540006265cd8018c64484016919018d31191210050765c6354c64484018397560064181210060721d5350f604840111e9818d73d9540
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x80034049224563dcf6550001482d4042b9aa63224200a416a021dcd53d9121
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x94b
  | 2 => 0x94c
  | 3 => 0x94e
  | 4 => 0x98a
  | 5 => 0x98c
  | 6 => 0x98e
  | 7 => 0x180c
  | 8 => 0xa0c
  | 9 => 0xa0e
  | 10 => 0x180e
  | 11 => 0xb0c
  | 12 => 0xb0e
  | 13 => 0xb8c
  | 14 => 0x184c
  | 15 => 0xd0c
  | 16 => 0x188c
  | 17 => 0xb0954
  | 18 => 0xb0956
  | 19 => 0x94b14
  | 20 => 0x94b16
  | 21 => 0x150a
  | 22 => 0x128a
  | 23 => 0xb0994
  | 24 => 0xb0996
  | 25 => 0x98b14
  | 26 => 0x98b16
  | 27 => 0x138b
  | 28 => 0x124b
  | 29 => 0x180a14
  | 30 => 0xb0a14
  | 31 => 0xb0a16
  | 32 => 0xa0b14
  | 33 => 0xa0b16
  | 34 => 0xb1814
  | 35 => 0xb1816
  | 36 => 0x180b14
  | 37 => 0x180b16
  | 38 => 0x8a
  | 39 => 0xec412
  | 40 => 0xed612
  | 41 => 0x1a4412
  | 42 => 0x1a5612
  | 43 => 0xed493
  | 44 => 0x1a5493
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 15
  | 7 => 151
  | 6 => 269
  | 5 => 223
  | 4 => 73
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
  | 9 => 2*((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 1)
  | 8 => 2*((h/12+packedAt gbK8 (390+(h % 12)*4) 4) % 15)
  | 7 => 2*((h/64+packedAt gbK7 (5587+(h % 64)*8) 8) % 151)
  | 6 => 2*((h/117+packedAt gbK6 (12912+(h % 117)*9) 9) % 269)
  | 5 => 2*((h/109+packedAt gbK5 (13157+(h % 109)*8) 8) % 223)
  | 4 => 2*((h/31+packedAt gbK4 (5110+(h % 31)*7) 7) % 73)
  | 3 => 2*((h/8+packedAt gbK3 (243+(h % 8)*2) 2) % 3)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x83ffffe1c387f87f0e0703ffff20307e18f07f
  | 1 => 0xfc38781e03f87f8ff007fc3c1f51c9a8673993
  | 2 => 0x3f801ffc007ff1fff8003fe09e0e3187ce1c
  | 3 => 0xffc0001fffff8001ffffffc000e00fc1f80fe0
  | 4 => 0x1ffffffffe0000000000fff001fff000
  | 5 => 0xffffffe0000000000000000000fffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x408840408090120201008484001002085025
  | 1 => 0xa41c508601082c85901258285a10c8a8232892
  | 2 => 0x202d410a84004d21a4b0083342160a30858a18
  | 3 => 0x4a8002112a5500004944a30000e00541500540
  | 4 => 0x4200045df3e67248006031818ceb7001fef000
  | 5 => 0xf3366780204404008180c22210fdaffc000000
  | _ => 0
def gbRaw : List Sig := (rawDecor 63 gbPos gbNeg).map Prod.fst
def gbPools : List BoundPool := [(0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555, 6, 0, gbRaw),(0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333, 7, 0, gbRaw),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 7, 0, gbRaw),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 8, 0, gbRaw),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff, 6, 0, gbRaw),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff, 8, 0, gbRaw),(0x550055005500550055005500550055005500550055005500550055005500550055005500550055005500550055005500550055005500550055005500550055, 5, 0, gbRaw),(0x55550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555000055550000, 5, 0, gbRaw),(0x555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555, 5, 0, gbRaw),(0x330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033, 5, 0, gbRaw),(0x3333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333, 5, 0, gbRaw),(0x33330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333000033330000, 5, 0, gbRaw),(0x333333330000000033333333000000003333333300000000333333330000000033333333000000003333333300000000333333330000000033333333, 4, 0, gbRaw),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f, 5, 0, gbRaw),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000, 5, 0, gbRaw),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f, 4, 0, gbRaw),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff, 5, 0, gbRaw),(0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff, 5, 0, gbRaw)]
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfefefeaafee8fea8fefefeaafee8fea8fefefeaafee8fea8fefefeaafee8fea8fefefeaafee8fea8fefefeaafee8fea8fefefeaafee8fea8fefefeaafee8fea8, gbN, gbR, gbH, gbI, gbPools⟩
end PEqualNP.Outside.L_meta_36370
namespace PEqualNP.Outside.L_meta_36370
open PEqualNP.Outside.L_meta_36370.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 2 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 6 := bs0_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 1 := bs0_5_0
theorem alls0 : ∀ k ≤ 5, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_2_0 : Interval s1Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 10 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 60 := block_range (n:=60) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 60 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_96 : Interval s1Atlas 4 96 69 := block_range (n:=69) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 165 := (concat bs1_4_0 bs1_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 50 := block_range (n:=50) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 50 := bs1_5_0
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
theorem bs2_2_0 : Interval s2Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 10 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 60 := block_range (n:=60) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 60 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_96 : Interval s2Atlas 4 96 69 := block_range (n:=69) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 165 := (concat bs2_4_0 bs2_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 50 := block_range (n:=50) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 50 := bs2_5_0
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
theorem bs3_2_0 : Interval s3Atlas 2 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 12 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 91 := block_range (n:=91) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 91 := bs3_3_0
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
theorem bs3_4_768 : Interval s3Atlas 4 768 26 := block_range (n:=26) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 794 := (concat (concat (concat bs3_4_0 bs3_4_96) (concat bs3_4_192 bs3_4_288)) (concat (concat bs3_4_384 bs3_4_480) (concat bs3_4_576 (concat bs3_4_672 bs3_4_768))))
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
theorem bs3_5_672 : Interval s3Atlas 5 672 69 := block_range (n:=69) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 741 := (concat (concat (concat bs3_5_0 bs3_5_96) (concat bs3_5_192 bs3_5_288)) (concat (concat bs3_5_384 bs3_5_480) (concat bs3_5_576 bs3_5_672)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 42 := block_range (n:=42) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 42 := bs3_6_0
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
theorem bs4_3_0 : Interval s4Atlas 3 0 16 := block_range (n:=16) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 16 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 13 := bs4_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 1 := bs4_5_0
theorem alls4 : ∀ k ≤ 5, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_2 i (by omega) hi
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 65 := block_range (n:=65) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 65 := bs5_2_0
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
theorem bs5_3_288 : Interval s5Atlas 3 288 55 := block_range (n:=55) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 343 := (concat (concat bs5_3_0 bs5_3_96) (concat bs5_3_192 bs5_3_288))
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
theorem bs5_4_1632 : Interval s5Atlas 4 1632 39 := block_range (n:=39) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 1671 := (concat (concat (concat (concat bs5_4_0 bs5_4_96) (concat bs5_4_192 bs5_4_288)) (concat (concat bs5_4_384 bs5_4_480) (concat bs5_4_576 (concat bs5_4_672 bs5_4_768)))) (concat (concat (concat bs5_4_864 bs5_4_960) (concat bs5_4_1056 bs5_4_1152)) (concat (concat bs5_4_1248 bs5_4_1344) (concat bs5_4_1440 (concat bs5_4_1536 bs5_4_1632)))))
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
theorem bs5_5_960 : Interval s5Atlas 5 960 84 := block_range (n:=84) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 1044 := (concat (concat (concat bs5_5_0 bs5_5_96) (concat bs5_5_192 (concat bs5_5_288 bs5_5_384))) (concat (concat bs5_5_480 (concat bs5_5_576 bs5_5_672)) (concat bs5_5_768 (concat bs5_5_864 bs5_5_960))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 48 := block_range (n:=48) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 48 := bs5_6_0
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
theorem bq6_2_0 : Interval q6Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq6_2 : Interval q6Atlas 2 0 3 := bq6_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq6_3_0 : Interval q6Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq6_3 : Interval q6Atlas 3 0 6 := bq6_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq6_4_0 : Interval q6Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq6_4 : Interval q6Atlas 4 0 1 := bq6_4_0
theorem allq6 : ∀ k ≤ 4, ∀ i < count q6Atlas k, checkRow q6Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq6_2 i (by omega) hi
  · exact allq6_3 i (by omega) hi
  · exact allq6_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq7_2_0 : Interval q7Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq7_2 : Interval q7Atlas 2 0 1 := bq7_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq7_3_0 : Interval q7Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allq7_3 : Interval q7Atlas 3 0 5 := bq7_3_0
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
theorem bq8_2_0 : Interval q8Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq8_2 : Interval q8Atlas 2 0 4 := bq8_2_0
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
theorem bq9_2_0 : Interval q9Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq9_2 : Interval q9Atlas 2 0 4 := bq9_2_0
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
theorem bq11_2_0 : Interval q11Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq11_2 : Interval q11Atlas 2 0 1 := bq11_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq11_3_0 : Interval q11Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allq11_3 : Interval q11Atlas 3 0 5 := bq11_3_0
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
theorem bq14_2_0 : Interval q14Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq14_2 : Interval q14Atlas 2 0 1 := bq14_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq14_3_0 : Interval q14Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allq14_3 : Interval q14Atlas 3 0 5 := bq14_3_0
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
theorem bq15_3_0 : Interval q15Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq15_3 : Interval q15Atlas 3 0 1 := bq15_3_0
theorem allq15 : ∀ k ≤ 3, ∀ i < count q15Atlas k, checkRow q15Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq15_3 i (by omega) hi
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
theorem bgb_3_0 : Interval gbAtlas 3 0 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 3 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 73 := block_range (n:=73) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 73 := bgb_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_0 : Interval gbAtlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_96 : Interval gbAtlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_192 : Interval gbAtlas 5 192 31 := block_range (n:=31) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 223 := (concat bgb_5_0 (concat bgb_5_96 bgb_5_192))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_0 : Interval gbAtlas 6 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_96 : Interval gbAtlas 6 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_192 : Interval gbAtlas 6 192 77 := block_range (n:=77) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 269 := (concat bgb_6_0 (concat bgb_6_96 bgb_6_192))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_96 : Interval gbAtlas 7 96 55 := block_range (n:=55) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 151 := (concat bgb_7_0 bgb_7_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 15 := bgb_8_0
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
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 18, 50)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 36, 52),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 34, 50),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq6 (cert : Complete q6Atlas) : Lower true (roots q6Atlas) (target q6Atlas) 5 := by
  have ready : Ready q6Atlas (asRow q6Pos) (asRow q6Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 20, 22),(inputs.getD 2 zero, 18, 22),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 18, 50)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq7 (cert : Complete q7Atlas) : Lower true (roots q7Atlas) (target q7Atlas) 5 := by
  have ready : Ready q7Atlas (asRow q7Pos) (asRow q7Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq8 (cert : Complete q8Atlas) : Lower true (roots q8Atlas) (target q8Atlas) 5 := by
  have ready : Ready q8Atlas (asRow q8Pos) (asRow q8Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq9 (cert : Complete q9Atlas) : Lower true (roots q9Atlas) (target q9Atlas) 5 := by
  have ready : Ready q9Atlas (asRow q9Pos) (asRow q9Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 36, 52),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq10 (cert : Complete q10Atlas) : Lower true (roots q10Atlas) (target q10Atlas) 5 := by
  have ready : Ready q10Atlas (asRow q10Pos) (asRow q10Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq11 (cert : Complete q11Atlas) : Lower true (roots q11Atlas) (target q11Atlas) 5 := by
  have ready : Ready q11Atlas (asRow q11Pos) (asRow q11Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq12 (cert : Complete q12Atlas) : Lower true (roots q12Atlas) (target q12Atlas) 4 := by
  have ready : Ready q12Atlas (asRow q12Pos) (asRow q12Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq13 (cert : Complete q13Atlas) : Lower true (roots q13Atlas) (target q13Atlas) 5 := by
  have ready : Ready q13Atlas (asRow q13Pos) (asRow q13Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq14 (cert : Complete q14Atlas) : Lower true (roots q14Atlas) (target q14Atlas) 5 := by
  have ready : Ready q14Atlas (asRow q14Pos) (asRow q14Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq15 (cert : Complete q15Atlas) : Lower true (roots q15Atlas) (target q15Atlas) 4 := by
  have ready : Ready q15Atlas (asRow q15Pos) (asRow q15Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq16 (cert : Complete q16Atlas) : Lower true (roots q16Atlas) (target q16Atlas) 5 := by
  have ready : Ready q16Atlas (asRow q16Pos) (asRow q16Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq17 (cert : Complete q17Atlas) : Lower true (roots q17Atlas) (target q17Atlas) 5 := by
  have ready : Ready q17Atlas (asRow q17Pos) (asRow q17Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) (pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact pv
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfefefeaafee8fea8fefefeaafee8fea8fefefeaafee8fea8fefefeaafee8fea8fefefeaafee8fea8fefefeaafee8fea8fefefeaafee8fea8fefefeaafee8fea8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certq6 : Complete q6Atlas) (certq7 : Complete q7Atlas) (certq8 : Complete q8Atlas) (certq9 : Complete q9Atlas) (certq10 : Complete q10Atlas) (certq11 : Complete q11Atlas) (certq12 : Complete q12Atlas) (certq13 : Complete q13Atlas) (certq14 : Complete q14Atlas) (certq15 : Complete q15Atlas) (certq16 : Complete q16Atlas) (certq17 : Complete q17Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
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
  have q0 : Slice true (roots gbAtlas) (target gbAtlas) (0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555 : Sig) 6 :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have q1 : Slice true (roots gbAtlas) (target gbAtlas) (0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333 : Sig) 7 :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have q2 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f : Sig) 7 :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have q3 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff : Sig) 8 :=
    slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
  have q4 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff : Sig) 6 :=
    slice_correct (ms:=fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds4 certs4)
  have q5 : Slice true (roots gbAtlas) (target gbAtlas) (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff : Sig) 8 :=
    slice_correct (ms:=fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds5 certs5)
  have q6 : Slice true (roots gbAtlas) (target gbAtlas) (0x550055005500550055005500550055005500550055005500550055005500550055005500550055005500550055005500550055005500550055005500550055 : Sig) 5 :=
    slice_correct (ms:=fixRows 9 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq6 certq6)
  have q7 : Slice true (roots gbAtlas) (target gbAtlas) (0x55550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555000055550000 : Sig) 5 :=
    slice_correct (ms:=fixRows 1 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq7 certq7)
  have q8 : Slice true (roots gbAtlas) (target gbAtlas) (0x555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555 : Sig) 5 :=
    slice_correct (ms:=fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq8 certq8)
  have q9 : Slice true (roots gbAtlas) (target gbAtlas) (0x330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033 : Sig) 5 :=
    slice_correct (ms:=fixRows 10 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq9 certq9)
  have q10 : Slice true (roots gbAtlas) (target gbAtlas) (0x3333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333 : Sig) 5 :=
    slice_correct (ms:=fixRows 18 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq10 certq10)
  have q11 : Slice true (roots gbAtlas) (target gbAtlas) (0x33330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333000033330000 : Sig) 5 :=
    slice_correct (ms:=fixRows 2 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq11 certq11)
  have q12 : Slice true (roots gbAtlas) (target gbAtlas) (0x333333330000000033333333000000003333333300000000333333330000000033333333000000003333333300000000333333330000000033333333 : Sig) 4 :=
    slice_correct (ms:=fixRows 50 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq12 certq12)
  have q13 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f : Sig) 5 :=
    slice_correct (ms:=fixRows 20 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq13 certq13)
  have q14 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000 : Sig) 5 :=
    slice_correct (ms:=fixRows 4 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq14 certq14)
  have q15 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f : Sig) 4 :=
    slice_correct (ms:=fixRows 52 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq15 certq15)
  have q16 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff : Sig) 5 :=
    slice_correct (ms:=fixRows 40 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq16 certq16)
  have q17 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff : Sig) 5 :=
    slice_correct (ms:=fixRows 48 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq17 certq17)
  have pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p :=
    List.forall_iff_forall_mem.1 (show List.Forall (fun p => ValidPool true (roots gbAtlas) (target gbAtlas) p) gbPools from ⟨build_valid q0 [] rfl, build_valid q1 [] rfl, build_valid q2 [] rfl, build_valid q3 [] rfl, build_valid q4 [] rfl, build_valid q5 [] rfl, build_valid q6 [] rfl, build_valid q7 [] rfl, build_valid q8 [] rfl, build_valid q9 [] rfl, build_valid q10 [] rfl, build_valid q11 [] rfl, build_valid q12 [] rfl, build_valid q13 [] rfl, build_valid q14 [] rfl, build_valid q15 [] rfl, build_valid q16 [] rfl, build_valid q17 [] rfl⟩)
  have low := boundgb certgb allCuts pv
  have lift := lift_ok (u:=true) (ms:=fixRows 0 0) (raw:=fullRoots) (T:=fullWord) (xs:=[]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 0 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4278124202 * 2 ^ 32 + 4276682408) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36370.Model.Repr at out
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

def mono : List Gate := [⟨.or,[3,4]⟩,⟨.or,[1,2]⟩,⟨.and,[6,7]⟩,⟨.or,[3,7]⟩,⟨.or,[5,9]⟩,⟨.and,[1,2]⟩,⟨.and,[0,10]⟩,⟨.or,[5,11]⟩,⟨.or,[3,13]⟩,⟨.and,[8,14]⟩,⟨.or,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124202 * 2 ^ 32 + 4276682408) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124202 * 2 ^ 32 + 4276682408) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36370

open PEqualNP.Outside.L_meta_36370 in
theorem PEqualNP.Outside.L_meta_36370 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124202 * 2 ^ 32 + 4276682408) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124202 * 2 ^ 32 + 4276682408) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allq6 allq7 allq8 allq9 allq10 allq11 allq12 allq13 allq14 allq15 allq16 allq17 allgb)
