import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, children closed at the parent by
-- restriction pools (closeChild of the model), and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37471.Model
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


end PEqualNP.Outside.L_meta_37471.Model

namespace PEqualNP.Outside.L_meta_37471
open PEqualNP.Outside.L_meta_37471.Model
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

def SBf (j : Nat) : Nat := [5, 4, 7, 7, 7, 8].getD j 0

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

end PEqualNP.Outside.L_meta_37471

namespace PEqualNP.Outside.L_meta_37471
open PEqualNP.Outside.L_meta_37471.Model
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
end PEqualNP.Outside.L_meta_37471
namespace PEqualNP.Outside.L_meta_37471
open PEqualNP.Outside.L_meta_37471.Model
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
  | 3 => 2*((h/1+packedAt s1K3 (5+(h % 1)*1) 1) % 1)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xfff01fffe03ffffffc07ff81ffe07ffff38e3f
  | 3 => 0xfffe01fffc03fc07ff81ffe07ff81f01cf3cc
  | 4 => 0xf000001fffffc0007fffe00007fffe001f03f0
  | 5 => 0xffffffe0000000007ffffffff80000001ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x12108144220484901058a2a288a8a2154534d5
  | 2 => 0xa4aa528a51a9292a2e055511554455aa928a2a
  | 3 => 0x88c954d294a3b20aceac19d4467511c0d8d34c
  | 4 => 0xce8d9b1d193223b377367061879e78831f03b0
  | 5 => 0xf0e1c1e1e3c3c3c7bc79e79e418610c1fec00
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xaaa0aaa0aaa0a0a0aaa0aaa0aaa0a0a0aaa0aaa0aaa0a0a0aaa0aaa0aaa0a0a0aaa0aaa0aaa0a0a0aaa0aaa0aaa0a0a0aaa0aaa0aaa0a0a0aaa0aaa0aaa0a0a0, s1N, s1R, (fun _ _ => 0), s1I, []⟩
end PEqualNP.Outside.L_meta_37471
namespace PEqualNP.Outside.L_meta_37471
open PEqualNP.Outside.L_meta_37471.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x8b4d304000068708e000312003045003015440501fe42bd43fc43fe20ff40fc42ff32ff41fd41fe21fd21ff21fc10ff20fc41ff30fd10fd42fd31fe10fe30fe41fd40fc21ff42ff10bf43fe31fd32fc30fe32fd43fe40fc32be40ff43fc20fc31fe43fc40ff31bc40fd20fd30
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x81808000160000000044001260100020010902000000200000210820106041870400002060c00304080801808000002c000177651082bea6904f15110af298813d539027ca821d7d4d21cea1a615c53486dea4885d14520cea9881b45150f3ca6205714d209eaa6213d540c77081984f950319eaa663b8400c27ea890d754c40aea9e835e53d0a7ca9994f940409f2a6613d54cc33a87985d145309f2a6633c5050e7ea8885d14543d7a92876d528c6baa7a14f54c409e2a2433d540ca7aa8185ed4121d62928777514c27ca9904e14143cea1c656d52042f0a090db149309e2a26175518cb3a86194f151209eaa487bb5050edea4a1f9484219f284816c52442b8a6886e94040b7a92613f544c2bca7a0e750e31dc28287b75150e7aa9904754c40bb28c657751482dca518cf953109f2a0659d430c6eaa2105b149439faa461785050e7ca8184f55332cfa9a877b5050edca4084f152309f286875f534427ea8905dd4543
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x10000101c50000009452010200021d6395320c5185531030d4314930ca1485050f186054c40c3d8953102986050e31c550c514c21c6550d30ccd445050f0d4394a31cad485050e396510030cc1445050ee06048421c550e518ca996310330a6181438cb245214543c318953102986050c32a618143cc21d6395310c5d8553102986050c31
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x100001811886154c40a10e0a1ca518e086218153102883828728c65841846054c40
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 91
  | 3 => 25
  | 2 => 5
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
  | 5 => 2*((h/28+packedAt s2K5 (704+(h % 28)*6) 6) % 44)
  | 4 => 2*((h/58+packedAt s2K4 (2457+(h % 58)*7) 7) % 91)
  | 3 => 2*((h/22+packedAt s2K3 (950+(h % 22)*5) 5) % 25)
  | 2 => 2*((h/8+packedAt s2K2 (245+(h % 8)*3) 3) % 5)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffffffffc07ffff03fffffffff01ffe3ffe3f
  | 1 => 0x3fff01fffff80ffffc0fff01ffffe07fcf1fc7
  | 3 => 0xc07ffe03fffff01ffff03ffe03ffff81f3e3f8
  | 4 => 0xff800003ffffffffffffc00003fffffffc03ff
  | 5 => 0xfffffffc0000001ffffffffffc000001fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x429114288471224500b2cb4a94b08aaa156e1b
  | 1 => 0x13224c514890e48b2c0555295956a24ccb16c5
  | 3 => 0xb244289a512241d3555026ac526ad30963a368
  | 4 => 0x2470b163a244891c9a6980c1838d1c71bc01b6
  | 5 => 0x3878c183c3870e1ee38e38f1e00e1861fed800
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xee88aa88ee880000ee88aa88ee880000ee88aa88ee880000ee88aa88ee880000ee88aa88ee880000ee88aa88ee880000ee88aa88ee880000ee88aa88ee880000, s2N, s2R, (fun _ _ => 0), s2I, []⟩
end PEqualNP.Outside.L_meta_37471
namespace PEqualNP.Outside.L_meta_37471
open PEqualNP.Outside.L_meta_37471.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x4400000014fb1134000139528930e04dbf42fc43fc42fd41fd42fe43fd10bc41fe42fc32fe40ff40fc31fc41ff42fd32fd31fd30ff32ff21de31bd42fc20bc40dc31ff41ff20ff10bd43fd21be41fe21fc30fe10ff30fc21be40fc40fe32fc10fe20fd40fe30bf43fd43fe41ff31fe31fd20ff43
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x113802d010003018100000083818d004e000004878781820081808080078182048002000081040004820600c99800070f8002820080000002030580810506800c038005078d8180870089075754c409eaa0439e53d0aeea2986710631ae29a833d531033e8718dbd49309f284835c53442eca3195d14543d7a92853d54c867ea4a1cf15131b7a9221d6510c67ea918cfd5131cea98813c544867ea88857d4d219ea9883745148278a910e70c4409e2a0213d544cba8620857946319e2a2616c524c27ca3a1e7950319f2a0853d521027aa818db14910bba8a87d431886e8a2984d145438ea98813d5490ebaa7084f553309f28c815e53d0738632057944319faa4439c548c7a88218cf944419fa9a853f544867ca8994f95032da208633e54cc27aa520678c440aea9e433e5408768a2a1cf950309f2a6633f544c27aa998d754c20cf18c819d43cc27aa9995794e10eba08635f534827ca9996750c31db288837551082baa7a14f54f429f2a0873e54082bca790cf940419f28c8394410c67ca9194754f429f28e853d5490af6a090d794f42cfaa4639d540c67ea8904f54e419ea9c819e53102eca2106e940409f288813e54842bca6204f54a419f2a6219f420c7a863084f94342dba8a873c548833c8218cf145439eaa4219d434c27ea9184f548419e2a2415f5350678a9186750e319e2a2213d540c27aa8106d107319e282879f5350e7ca9905754f41cea106375518cb3e8518cf55032cf20c633c548c67aa9904fd5220ae29a433e540c7388218e750c329e282859d438cabea6884f552329f284819f430c67aa988750c521cea1463785048678a2a14f940409ea96873e50d0e7ea8084f95321af298419d53d0aeea2905714d20
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x1a0004f04aac5bc408a162300080100002003142c5d8553103154394632a5987548c62d6215010c518553d0a966010431d40c450487154314530c5185531031753145438758c54882946150e32a3588548c61f6354a40a5185531021d63942418d594410c6946150f3087195434c2966190431c5150318863661d5230c5150314869661152318b588548c70d43149308d185544ca1d63953208718553d0a386055132c595031842546154c40a5d94410c61d63150109518553d0a94615083187597420c61d6395132c515031043176154f428518553d0a1c6154c40a5185430ca1d6314142c5d8c5150e946154f428758e54086146154c40a5588410c61f6354a41a5594410c61d650c4408d18553d0a946150d308d185531021f658c4408758c548861d6395310c5944319021e65d0a31
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x400000000000000000da82b90a818821055d8540c410a08e2a18a4984147158e54c8283396c628a87051c5631414282ce3b1aa5204147158c5488242b96ca20863051c56395021
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
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
  | 5 => 2*((h/23+packedAt s3K5 (800+(h % 23)*6) 6) % 50)
  | 4 => 2*((h/76+packedAt s3K4 (4455+(h % 76)*8) 8) % 165)
  | 3 => 2*((h/27+packedAt s3K3 (2280+(h % 27)*6) 6) % 60)
  | 2 => 2*((h/24+packedAt s3K2 (490+(h % 24)*4) 4) % 10)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffffff81fffffff81ffffffff03ffffe3ff1ff
  | 1 => 0xf01ffffe03ffe07fe0ffe07fffc1ff01ce7e7c
  | 2 => 0xffe07ffffc0fffffff03ff81fffe0ffff38f8f
  | 4 => 0x7ffffff0007ffffc0001fffff001fc0ff0
  | 5 => 0xffff80000000007ffffffffe00000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x1142108c48824810052ca8a25012915414b0b5
  | 1 => 0x24c52914392484a960556454b6412a0cca565c
  | 2 => 0x42894a209069144aaa0255112aa40ca9630b0a
  | 4 => 0xb1674492241d974d3981861cd39c031bc0de0
  | 5 => 0x8c187871c38e1e7f1ce39e780e3188c1ffe000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xe8e8a8a8e8e8a0a0e8e8a8a8e8e8a0a0e8e8a8a8e8e8a0a0e8e8a8a8e8e8a0a0e8e8a8a8e8e8a0a0e8e8a8a8e8e8a0a0e8e8a8a8e8e8a0a0e8e8a8a8e8e8a0a0, s3N, s3R, (fun _ _ => 0), s3I, []⟩
end PEqualNP.Outside.L_meta_37471
namespace PEqualNP.Outside.L_meta_37471
open PEqualNP.Outside.L_meta_37471.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x1c128e00268400001a001280010280002352040000fd43fc20fc21bc40ff21fc40fd42fd30ff10fe43fe30fc32fd31ff40fd32bf42fd21ff30fc43fe31fe32fe42fc10ff31fd40ff41fd10ff43fc41fe21fe10fe41fd20fc31fc30fc42ff20ff32fd41bd42be40ff42fe40fe20
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x4e2500e4293005c080000000000004b710540800250500040a7380005780124cc010a000bc10000000e281009e2a2635d539036ca3206e141429f2a0853d521027ca1206e10020afa9a21b75150a7ea898ddd45309e2a2615f5350776a0a15d14543cfa9a853d54c43aa6218e714d42cea9c816f524c2eca2184fd5220aea9c433f544c37081904f950329e2a2417651902b8a6905b14930b629221775150aeea2904f95321bb28c657551902f6a0a16d14542bb28e656f52442eaa2185d54420baa8c6574514827ea8885754c10ba28a615c5350a7aa9985d54732bc282855e530427ca0205794e219faa2415e53c867aa990cf953209eaa6415f5350ab8a6a0cf55020afa9a413e540867ca9884f151109f286853d5490ab8a6886d546409eaa465765108374a0204f95020bba8a873d540ca7ca9195794c20af29c819e53902baa790cf550219e2a4413c5050abaa6104f95330d7a9285385050a7aa5205d14542
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x200180000000c514c5150b1b5314142a5191310c7185314142c594e51902396510020ccd445050b305114142
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
  | 6 => 2*((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/28+packedAt s4K5 (704+(h % 28)*6) 6) % 44)
  | 4 => 2*((h/51+packedAt s4K4 (2484+(h % 51)*7) 7) % 92)
  | 3 => 2*((h/16+packedAt s4K3 (304+(h % 16)*3) 3) % 8)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfffffff81fffffe07ffffffffe03fffe3ffe3f
  | 1 => 0x3f80ffffe03f81ff83f03e0ffffc1f01d89fcc
  | 2 => 0x3fff03fffffffffffc003ff03fffffffe0e3ff
  | 3 => 0xc00003ffffc001ffffffc0003fffe001ff03f0
  | 5 => 0xfffffc00000001ffffffffffc0000001fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x848a1008c489082014b14a114a2129540b2e15
  | 1 => 0x9526299143922ae58155168d96e51a0cd896cc
  | 2 => 0x22144aa20924614aa80825a4254a54a960c16a
  | 3 => 0x3458b34492074db34e6d810939b38831bd03b0
  | 5 => 0x3860c3871c3871dc738e39ce01c210c1f6f800
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeaa8eaa8e0a0e0a0eaa8eaa8e0a0e0a0eaa8eaa8e0a0e0a0eaa8eaa8e0a0e0a0eaa8eaa8e0a0e0a0eaa8eaa8e0a0e0a0eaa8eaa8e0a0e0a0eaa8eaa8e0a0e0a0, s4N, s4R, (fun _ _ => 0), s4I, []⟩
end PEqualNP.Outside.L_meta_37471
namespace PEqualNP.Outside.L_meta_37471
open PEqualNP.Outside.L_meta_37471.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x3031000400404c000b1ce09e0040801c0543200fc42fe10fc41fc20fd31fd32ff30ff21ff10fc40fc32ff31fe20fc43fc31fc21fe30ff42fd30fe31fc30fd43fe43ff43fe42ff32fd40fe21fd42ff40ff20ff41fd21fe40fe32fe41fc10fd10fd41fd20
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xa61de314c6fca5195f94232bfa8265de43ccb7aa819778c932dea1681bc41102d8a4885e14142be29a857e500cbeca2186fd0a41de2a2635f53506faa690df54b10bfa92817e544ca7aa8195f94f41be28a415e53082faa3995f54841bfa9c437d5110fbe87195f14540ae29a83ee5210e7ea8885f94042bf29e437e50087ec20885f94631ba28a877e53d02faa620df14543bfa92637d52cc7ee4290efd0841bf288837d54042fea918f710e31df21c837f504c6fca618f74c831be29281f4410c6f8a918fdcc631bf2a0877e52842baa7205f14c21bca8063bf41907be8618df94c30bfaa643dc438cafea7105f14530be29e437e500c3e88390df55131fda0041bf4390fdc4290df94621fa208437e508c6faa3185fd5230bf284217e54103be61185d54420bfaa6417f5250fb88618df94041bf28c65bc54442fea0a1f70c630ee996617c53886fea2905f15031bf290637d538c2fca3985fd4121beaa487f710043bea6a0df94431df21a87f741442f8a6106f90640bea86657e54cc2fca3185fd4d21fc28285fb10842faa418df54830efa1e617d54882fea4085f54420fa20a21fa40102fca4105b94843f790843de434caf8a7107e50040be2a0657e548c7ba86995f54a21beaa661df438c7be86a1fbd0a42bea8c65f631c43ea4210df54743ee21a61bc43106e8a2a1774ca31ee992617c53c83dc43105f54843bea84637d54c86fca321f7d0d30fba0e437a500c6faa5185f95230bf286637e52902faa6105f14121efa9a21de304c3ee8210f7cc431bf2a6657d540cbb887985f54241fd902417e510827ea898dd94420be2a243de318c2fca610d794f21beaa6657c54cc6fca3a17b14910de21c83f7410c6fca1a15714d42ef29c817d5190efca7205f55241bfaa2217e52cc3f220087e8c110be2a0617d54842f8a6a07ed0240bf28881f531442fca9106f90942fd100417e5290beea2a1dfd5030dea08837b5050b7c80a05fd4542be29283df31cc3be65195fd4b10bfa9a41775150afca6195f94e41bf29883bd40102fca1997794c20fba0c83be54c87ec8220f710c32bea84437e508c2fca3217e4c110bf290817e54c82fca2085f55331f710241df314c2fca608774c8329f2a041ee320caf8a6085f94842bfaa6657f54086faa5205f95210bf29e21df318c6faa3a0770c430bfa98217d54886faa4087d94640bfaa241bf42503eaa3205f94b31be2a241f45150bbe6418dfd5232bea8e417e52442fea6886f50841efa1865f621442fca5185f55242be28285be41103f6a0a15f54f41ee29a857d5290efea790f7cc030bea8c417e50907ea43885f94732fda02817d5310afca690df15020fba8a85f840c82fea8107714d10eea1e657c54086f8a098df54840be2a661ed320cbdea4885f54442bfa9a85bf40902fca0085fd4910
  | 1 => 0xd300c3de84a15dd4543bfa8a877d52442fea899778c430baa88617d53043eaa2105f54430fb90c43df32cc3da40105f54742bea86837e51c837e80207dd0731be282657d52843dc85195f54031be29c217d52d0efca6215fd4530bfa9e417f52843ea6218fec4110fd98461f441cc6faa9187dd0541f6a9087f5510c278a898df14910bfa9a81fb304c37e85a05f55110aea98417d544c2f8a8995fd5031bfaa441df328c77a87a177cc930bf2a061ed424cafea7085f94a41faa08833c544437ea8885fd5121bf29c41f6510837e8220df95041eea9e43ee4210bde64995f14b10be29261bd54c87baa6085f14d10bf280637d51cc2fca5a05f94f20bea84857e528c6fca4084f55020ef298217e52d0efca6205fd4141bf28e877e5390efca8105f94641bf284417e5090ef8a4a1fb90932f7108417c53c42faa9905f94c43df218837e520c2fea610df54f21fba0e217f514cbf681907750c43f690843f510043baa7205f94f42bea8487f621086faa7a16fd0f42fa20e217e544437e8621f7d0e43df20a837e54886bca7207790c43bf2a4657d50d0e7ca8196f95020dea1a857f5050af8a2a15f54d20be292637d50106daa421df14d21bea9e817e54086fea4986f95032af298857e53082f8a6a0d7d4d109f2a643f631443d843107e48020ef99065bd4210afca021df94442bea9a21bd4310efea2a05f94620fb98a637d53842fca710dfd5131beaa0437e52106fca7215fd5010bea86857c54886fea9885f94843aea98857f52506faa0215f94443bf2a2417d52882faa1195f54e40bf288657f54cc2faa9885f14532bf296837d52d06faa190d7d4d42bf286437f53507ec6218df15220fd180617e50d0fde41105f54021dea12817e51902faa520d754c10bb28c817f54cc6fca110df54e41be2a641bf4210af8a898df14143bea9e41dd5310afaa0195f15230bea8c857c53482faa8185f55120fa98e217c54842faa718d794c10bea8087dc53506fca5885f14a10be2a0216f52442faa5985f54e42be290217d538cbf260185f54610ae29a217c544c2fca898f74c431be2a221fa10042fca1205f94341dfa1a85bf4290afca998df55020eea98417d51102faa5a05f94421f6a10857c54c43d842107d14543bf29a417e540c6fca410df94a43efa9a85de5310af8a9997d88710fd280637e5090afaa818df54f10beaa265f9500c7f261087e10020bf280817e54c42fea7885f55232dea14837551902faa9206fd5131ee98e617e53843f461085f95042aea9e437d548c6faa7105f15232bf2a643bd54082faa198dfd5130bf29a21ef21886fca890df54640bea98437e520cafea8197bc8020bea98817e540cafaa518df94430be282837c54c86fea6107d485109eaa6437f54842faa890df95130bb28861de53c877883207ec8220ee98
  | 2 => 0x20b8fc08816168090400b014015c41900000000002100717c0604002004470480000400314040001400c010080000c030a80f45c0f0ac020154d0800202c020040e0020b00c4301003004020000001011000320c00504cb200c0d0885e000002741700001008b900006000000041233c0e000003903d00017000bd000001dc6005cb10e00300800068000000003c000040f01c0e00000000010700010001000080200b00c0092c01000050380400095008c4000560280f050163b804000000018c0cc6405c000000d094010181a0080502802018af000030180410cb80a000008050041606c010005c05402000001c0243f8000540a00400008dd0d40c02002044220100100004001330dc2e22006004100000648c05008880c4000044f2ec9b09c0107402004283640000007009e21804b19c000000000c060106902c410001d110a150c0018c37074431482d0000204c050080019048030140bc0a0002500037000000003000400f6a14657e51d03ee21085f94020bf2a021ef328cafaa710dfd5221bea8865d
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x5411074e43548439d987548825e63150108f990524c2d46150f329d1855348358538c1109798f540c27661d5020cb150524423f6454910c7153534425f63549109758c504865d63943418fd9153442b86050a419e58354cca3d6414930cdd91510c26e6294d109dd85544823e6494b109798c528425e65cc5309bd89544c25d6394b109dd85544875953440108f590530865c63551209d584504cacd6210e318f99052043595384010cdd85540ca7661148108fd91518826d62150309718d518827661d523297997434c27561d52209d987540435b4354031d614c5050b584354031c714f4350b2f4354843bc983414425e6394b10cdd50414431d544c832d594d510827561150209e980530875b5314142c754f4210a6e62150109ed81544827661943439d18554c82776544010b3588430ca5d631494097594430c72d4354843c7952530832c54d4910b5587320c71d5494f21d9584524425d63d52109798c54086cd6210f30cd191510c357431454397d8d51d0a5d6315021dc8c5500c67661d5230c7152314c71e5454c209718d51d0a3e6414f209d58754cca3d65950329e980538863e6414a10d914a214433554107218f59053c82d46150c439d587548ca3d6494910dcd05500c73761553219e98354cca6c6550932d5d4c5150a5d6510c329758f54886cd6210e3297d8d544ca5e63141218f990530866e621503297d8d540872c52509409dd95210867561d5230dc1475050b5551cc030c7553430ca5f63546209d584530825d63153219d195214423e64150209b189544c2b860508418f992544c63e64d4e10d554f100435932540318f19151cca9c644c7309d195314432d548c8329758e544427561d4c209bd89544434d53908429ed95200825e63943419ed95100423f6550441ad191314435453105109dd85544c75453145429798f54c86786054d2197d95300c25f6354440c7150534436551884209e583548863e64d4c208f992534425e6590d32ad191310c63d64d4f21b3588430c6746155120d3149324c25f6550c439758c5404371518c0309758f520433554944209798f548823e6414f219718d540865d65d0c32b6580318c26e6215330d914b41442b46150c43d594e519027860551218fd91510c23f6454d209d185544c25c63549109bd89534425d63d53219e580530866e6215331cd587544434f53149109d584540c27665d05108f990540ca3f65508429758f540429c644c4318f1915188278654c110d5544310c26f654c8329798c54c873461550329798c540cad8604c930c755043cc25e63d4810d594c41c863e6414c209e580538865e63d52108f590528427b654c030cd55151083556114d109ed81544875853d4142d554e519034d5350842ad1854350a5d6314a109dd85534831e53906408f592528c66f6550842
  | 1 => 0xb040042e000400044000585c1a0c138046c150304d16110d8ac3003170e024063280e0c390903022000c80c123103004646d0180000010285c0c03003a80a39000202c000c829543b0101000000382804009758f54882d463504419bd9520082766114e209798c540832d544c8329b98a524427565104319d98454082b86050b40dc4c5500c67b65500409b189544425d6394a4197994534426d6215331b5185434cb2e5250a41d5d4f5150a5e63951109e580540874f53d49109e5944008277654c4318fd954310e7a60150318f994544c71c53905419e583540c63c6454430c7553320cb2f54149109718d511025d6314810c7d53534425e6314c209b58a53443596014d109798f548865f6355131dcd475050a7661d4c209d984530827661141329798e529067561d5020b6580310c25c63553109e983540c65c635512197596530827a6014c109b988540c73654944209dd85540ca3d641481097d95310c67a60d5221d514f5150a3d6494b10cd90c5150e7761551328f191524423e64948219d984530425d6394910dc1445050a5d63153208f994544434d6214d428fd95401038d43509329d584538831e53106408f593530823c6454d208f59053c86ad6210e418f592534429c6350a419d98754cca6d6215330f48c6304433454cc531d594d519027a60150219798c525027965840109b9945244354538c51097d8d544426f6548421cbd53524435b53d41428f99353c874c53149108f992524435453d0510b3588434c25d63d5020ad19131c42cc6350a329e580540c71c63550329758c540835b32540319d18554cc23d649482197d8d54c425e63153209ed81544ca7561d5030a7191314c2766194342dc105500c63d6414c208f191534425e63148109b588540c78f4350a329b58a544431d5410c32a718d41107d1314c1109759653042f06048510d5545300c27761553309d59441086766115030dc545300c336545442097d8d54c825d658c430add8542106776155320d554d519023d64d4e109d58650d0f1e5454f219798c53043593154031ad18543d0a5f6355120d554d100435653d07219798e534427b6054d219b98a544426c6254d1097d95320cb1d5494c20ce181540825d63948218fd9151cca5f63551219d987540c31d53508429d185544cb1e5494f219e181544ca7561943428fd91534874c53d49108f19153486ad6210c41d594e51082776155130ce553400825d63943428f992528c65e63948219b588540425c63551109b988540c31f5414d109d185540ca5e6394342c75515308355518c430d6cc5500c75453d0541a718d421063d65950209798f540423e6495110cd544419025c6355320e510c410c77351141429798f54083555394420c755153c87645210510d350d5210e5c6550d329798e524435553544209dd9
  | 2 => 0x160000000000b83c02020e05412f30005c00000180002030b028083b000e1d8000001c0800008fce80600160120e0600038200481050000d3309c03000c41a1b0081c045809828224504008c215031409a070e148000800864000000038000204814001e00840360
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x80048094000448158080780611001451d1510c4309a2e7306828851471550430cac83a26298221461d13154031c28c630aa8194d17318121442c2b908620863435cc5250940a28e2aa0879871043105500c668b88c099261945856014d10a28e8b08a6885247150d5210e86ba0a499261545c73254031a88e2a1aa421e0d5458843cc2a4b9086a8063611c54350932a1ae72928520d30744c5500c706aa2c421865251d161cc831
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x10910845c73254031a04815516210c32a10845856014d10a04815516210f30b018210c4154031
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
  | 7 => 2*((h/1+packedAt s5K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/27+packedAt s5K6 (640+(h % 27)*6) 6) % 40)
  | 5 => 2*((h/289+packedAt s5K5 (16632+(h % 289)*10) 10) % 616)
  | 4 => 2*((h/166+packedAt s5K4 (15732+(h % 166)*9) 9) % 414)
  | 3 => 2*((h/29+packedAt s5K3 (1225+(h % 29)*5) 5) % 25)
  | 2 => 2*((h/8+packedAt s5K2 (300+(h % 8)*3) 3) % 5)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf03ffff03ffffe07ff07fe1fff07fffb1c7e3f
  | 1 => 0xffc07fffc07f07f83ff83fe1fff83c05e39fcc
  | 2 => 0xffff81ffffffffffc0003ffe1ffffffe03e3ff
  | 3 => 0x1ffff8007ffffffc0001fffc007fc03f0
  | 4 => 0xfffffe00000007ffffffffffe0000007fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x94850811891222014b214a02a54265510c2e15
  | 1 => 0xa193142287242a5815291620cb4a28316196cc
  | 2 => 0x420a2544124884aa80842554129492a602c16a
  | 3 => 0x8b2c5989240eb734e6b581109ce720c7b403b0
  | 4 => 0xc30610e3870c5c738c6399900840306db7800
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xeee8e0a0eee8e0a0eee8e0a0eee8e0a0eee8e0a0eee8e0a0eee8e0a0eee8e0a0eee8e0a0eee8e0a0eee8e0a0eee8e0a0eee8e0a0eee8e0a0eee8e0a0eee8e0a0, s5N, s5R, (fun _ _ => 0), s5I, []⟩
end PEqualNP.Outside.L_meta_37471
namespace PEqualNP.Outside.L_meta_37471
open PEqualNP.Outside.L_meta_37471.Model
def q3K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def q3K3 : Nat → Nat
  | 0 => 0xcd32
  | _ => 0
def q3N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 1
  | _ => 0
def q3R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q3K4 (i*5) 5
  | 3 => packedAt q3K3 (i*16) 16
  | _ => 0
def q3I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q3K4 (5+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/1+packedAt q3K3 (16+(h % 1)*1) 1) % 1)
  | _ => 0
def q3Pos : Nat → Bits
  | 0 => 0xc3fffe0ff0ff0f87e1fc3fff0fe0fe0f49f673
  | 1 => 0xfc1c3ff0ff0ff0f8fe1fc383f0ff0ff0b6cb9c
  | 2 => 0xffe03fff000fffff001ffc03ff000fffc70c1f
  | 4 => 0x3ffffff000ffffe00003fffff000f80fe0
  | 5 => 0xffffc000000000fffffffffc00000000fff000
  | _ => 0
def q3Neg : Nat → Bits
  | 0 => 0x48400222010010002024048901222222005231
  | 1 => 0x8940446240140110620c4119104a24a212c294
  | 2 => 0x108aa8842aaa88ab1112a822aa04494cc50c0a
  | 4 => 0x32933108a882aacd95422042cc94c044e80d40
  | 5 => 0x231a21ccccccccf6d99b327088188188ffa000
  | _ => 0
def q3Atlas : Atlas := ⟨4,rawDecor 55 q3Pos q3Neg, 0xeeeeeaeaeeeee0e0eeeeeaeaeeeee0e0eeeeeaeaeeeee0e0eeeeeaeaeeeee0e0eeeeeaeaeeeee0e0eeeeeaeaeeeee0e0eeeeeaeaeeeee0e0eeeeeaeaeeeee0e0, q3N, q3R, (fun _ _ => 0), q3I, []⟩
end PEqualNP.Outside.L_meta_37471
namespace PEqualNP.Outside.L_meta_37471
open PEqualNP.Outside.L_meta_37471.Model
def q5K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q5K3 : Nat → Nat
  | 0 => 0x40046d32ba6534caf996e32
  | _ => 0
def q5K2 : Nat → Nat
  | 0 => 0x2350e32
  | _ => 0
def q5N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
  | _ => 0
def q5R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q5K4 (i*4) 4
  | 3 => packedAt q5K3 (i*15) 15
  | 2 => packedAt q5K2 (i*26) 26
  | _ => 0
def q5I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q5K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/8+packedAt q5K3 (75+(h % 8)*3) 3) % 5)
  | 2 => 2*((h/1+packedAt q5K2 (26+(h % 1)*1) 1) % 1)
  | _ => 0
def q5Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffbfdcf3e3f3e74cf
  | 1 => 0xfffffffffffffffffffffffdfef3cfc7cf9b33
  | 2 => 0xebf03f3f80fec3c
  | 3 => 0xf3ffc03fff00fc0
  | _ => 0
def q5Neg : Nat → Bits
  | 0 => 0xfffffffffffffffffffffff404104009020045
  | 1 => 0x208041042040112
  | 2 => 0x150aa0690a94c28
  | 3 => 0xe082ab24a14e80
  | _ => 0
def q5Atlas : Atlas := ⟨4,rawDecor 15 q5Pos q5Neg, 0xeee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8, q5N, q5R, (fun _ _ => 0), q5I, []⟩
end PEqualNP.Outside.L_meta_37471
namespace PEqualNP.Outside.L_meta_37471
open PEqualNP.Outside.L_meta_37471.Model
def q7K3 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def q7N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q7R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q7K3 (i*3) 3
  | _ => 0
def q7I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q7K3 (3+(h % 1)*1) 1) % 1)
  | _ => 0
def q7Pos : Nat → Bits
  | 2 => 0xffffffffffffffffffffffffffffffffffbecf
  | 3 => 0xffffffffffffffffffffffffffffffffffdf73
  | 4 => 0xefbc
  | _ => 0
def q7Neg : Nat → Bits
  | 2 => 0xffffffffffffffffffffffffffffffffff4205
  | 3 => 0x2412
  | 4 => 0x1828
  | _ => 0
def q7Atlas : Atlas := ⟨3,rawDecor 28 q7Pos q7Neg, 0xfff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000, q7N, q7R, (fun _ _ => 0), q7I, []⟩
end PEqualNP.Outside.L_meta_37471
namespace PEqualNP.Outside.L_meta_37471
open PEqualNP.Outside.L_meta_37471.Model
def q8K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q8K3 : Nat → Nat
  | 0 => 0x18000036105c30e82178c37107610
  | _ => 0
def q8K2 : Nat → Nat
  | 0 => 0x20003808010d03004320c020
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
  | 2 => 2*((h/8+packedAt q8K2 (78+(h % 8)*2) 2) % 3)
  | _ => 0
def q8Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffbf0fffc3fe3f
  | 3 => 0xffffffffffffffffffffffffffdff0fffc3fc7
  | 4 => 0xefff0fffc3f8
  | _ => 0
def q8Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffff012222c444db
  | 2 => 0xffffffffffffffffffffffffff42e44562aa2d
  | 3 => 0x244e89aa3346
  | 4 => 0x1888ee3323b0
  | _ => 0
def q8Atlas : Atlas := ⟨4,rawDecor 30 q8Pos q8Neg, 0xccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000, q8N, q8R, (fun _ _ => 0), q8I, []⟩
end PEqualNP.Outside.L_meta_37471
namespace PEqualNP.Outside.L_meta_37471
open PEqualNP.Outside.L_meta_37471.Model
def q9K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q9K3 : Nat → Nat
  | 0 => 0x18000036105c30e82178c37107610
  | _ => 0
def q9K2 : Nat → Nat
  | 0 => 0x20003808010d03004320c020
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
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffbf0fffc3fe3f
  | 3 => 0xffffffffffffffffffffffffffdff0fffc3fc7
  | 4 => 0xefff0fffc3f8
  | _ => 0
def q9Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffff012222c444db
  | 2 => 0xffffffffffffffffffffffffff42e44562aa2d
  | 3 => 0x244e89aa3346
  | 4 => 0x1888ee3323b0
  | _ => 0
def q9Atlas : Atlas := ⟨4,rawDecor 30 q9Pos q9Neg, 0xccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000, q9N, q9R, (fun _ _ => 0), q9I, []⟩
end PEqualNP.Outside.L_meta_37471
namespace PEqualNP.Outside.L_meta_37471
open PEqualNP.Outside.L_meta_37471.Model
def q10K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q10N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q10R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q10K3 (i*4) 4
  | _ => 0
def q10I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q10K3 (4+(h % 1)*1) 1) % 1)
  | _ => 0
def q10Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffbfcffcf8fff873f3
  | 3 => 0xdbf19f3f1c3f8d9c
  | 4 => 0xffffffffffffffffffffffeffe1fffe03ffe1f
  | 5 => 0xf3ffe03fffc00fe0
  | _ => 0
def q10Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff40640108248920b1
  | 3 => 0x24ac285909932594
  | 4 => 0x1101502242244a0a
  | 5 => 0xe091ab493064f40
  | _ => 0
def q10Atlas : Atlas := ⟨3,rawDecor 57 q10Pos q10Neg, 0xffaaaaaaffaa0000ffaaaaaaffaa0000ffaaaaaaffaa0000ffaaaaaaffaa0000ffaaaaaaffaa0000ffaaaaaaffaa0000ffaaaaaaffaa0000ffaaaaaaffaa0000, q10N, q10R, (fun _ _ => 0), q10I, []⟩
end PEqualNP.Outside.L_meta_37471
namespace PEqualNP.Outside.L_meta_37471
open PEqualNP.Outside.L_meta_37471.Model
def q11K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q11K3 : Nat → Nat
  | 0 => 0x42e995e30ba6370c2f995f31
  | _ => 0
def q11K2 : Nat → Nat
  | 0 => 0x209541cca5504308d42cc6350830
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
  | 3 => 2*((h/2+packedAt q11K3 (90+(h % 2)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q11K2 (104+(h % 8)*2) 2) % 4)
  | _ => 0
def q11Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff7fcfc7ff8f3cf
  | 2 => 0xffffffffffffffffffffffedf99f3f8e3f3d33
  | 4 => 0x76fe1fcff03fce3c
  | 5 => 0x78ffe00fffc00fc0
  | _ => 0
def q11Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa010010012080045
  | 2 => 0x1224284484922512
  | 4 => 0x941501921248a28
  | 5 => 0x7851aae4986af80
  | _ => 0
def q11Atlas : Atlas := ⟨4,rawDecor 53 q11Pos q11Neg, 0xfafaaaaafafaa0a0fafaaaaafafaa0a0fafaaaaafafaa0a0fafaaaaafafaa0a0fafaaaaafafaa0a0fafaaaaafafaa0a0fafaaaaafafaa0a0fafaaaaafafaa0a0, q11N, q11R, (fun _ _ => 0), q11I, []⟩
end PEqualNP.Outside.L_meta_37471
namespace PEqualNP.Outside.L_meta_37471
open PEqualNP.Outside.L_meta_37471.Model
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
  | 5 => 0xf3ffe03fffc00fe0
  | _ => 0
def q12Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff4061010824892131
  | 2 => 0x2088281109124486
  | 3 => 0x1523506a42a52b18
  | 5 => 0xe0a1ab493064ec0
  | _ => 0
def q12Atlas : Atlas := ⟨3,rawDecor 45 q12Pos q12Neg, 0xfaaafaaaf0a0f0a0faaafaaaf0a0f0a0faaafaaaf0a0f0a0faaafaaaf0a0f0a0faaafaaaf0a0f0a0faaafaaaf0a0f0a0faaafaaaf0a0f0a0faaafaaaf0a0f0a0, q12N, q12R, (fun _ _ => 0), q12I, []⟩
end PEqualNP.Outside.L_meta_37471
namespace PEqualNP.Outside.L_meta_37471
open PEqualNP.Outside.L_meta_37471.Model
def q13K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q13K3 : Nat → Nat
  | 0 => 0x5ef20da41e483d106920
  | _ => 0
def q13K2 : Nat → Nat
  | 0 => 0x2a50a20
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
  | 0 => 0xfffffffffffffffffffffffb7c99ce39df3873
  | 2 => 0xfffffffffffffffffffffffdff1e7fc1e7f19f
  | 3 => 0xe7fe073fe07ce1c
  | 4 => 0xfbfff83fff80fe0
  | _ => 0
def q13Neg : Nat → Bits
  | 0 => 0xfffffffffffffffffffffff48632120c51a831
  | 2 => 0x208408040820086
  | 3 => 0x19215069414aa18
  | 4 => 0x60002921000540
  | _ => 0
def q13Atlas : Atlas := ⟨4,rawDecor 29 q13Pos q13Neg, 0xfffaf0a0fffaf0a0fffaf0a0fffaf0a0fffaf0a0fffaf0a0fffaf0a0fffaf0a0fffaf0a0fffaf0a0fffaf0a0fffaf0a0fffaf0a0fffaf0a0fffaf0a0fffaf0a0, q13N, q13R, (fun _ _ => 0), q13I, []⟩
end PEqualNP.Outside.L_meta_37471
namespace PEqualNP.Outside.L_meta_37471
open PEqualNP.Outside.L_meta_37471.Model
def q14K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q14K3 : Nat → Nat
  | 0 => 0x300000000000004000402f985d30de41dc436907510
  | _ => 0
def q14K2 : Nat → Nat
  | 0 => 0x480344c110e12044324c120
  | _ => 0
def q14N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
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
  | 3 => 2*((h/30+packedAt q14K3 (90+(h % 30)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q14K2 (78+(h % 8)*2) 2) % 3)
  | _ => 0
def q14Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffffffeaef1b77c27
  | 2 => 0xbf333e3ba0da
  | 3 => 0xdfc3cfc3c31c
  | 4 => 0xeffc0ffc03e0
  | _ => 0
def q14Neg : Nat → Bits
  | 0 => 0x0
  | 2 => 0x42444211044a
  | 3 => 0x241814820914
  | 4 => 0x1801a92012a0
  | _ => 0
def q14Atlas : Atlas := ⟨4,rawDecor 29 q14Pos q14Neg, 0xfffafaaafffafaaafffafaaafffafaaafffafaaafffafaaafffafaaafffafaaafffafaaafffafaaafffafaaafffafaaafffafaaafffafaaafffafaaafffafaaa, q14N, q14R, (fun _ _ => 0), q14I, []⟩
end PEqualNP.Outside.L_meta_37471
namespace PEqualNP.Outside.L_meta_37471
open PEqualNP.Outside.L_meta_37471.Model
def q15K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q15N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q15R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q15K3 (i*4) 4
  | _ => 0
def q15I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q15K3 (4+(h % 1)*1) 1) % 1)
  | _ => 0
def q15Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffbfcffcf8fff873f3
  | 1 => 0xdbf19f3f1c3f8d9c
  | 4 => 0xffffffffffffffffffffffeffe1fffe03ffe1f
  | 5 => 0xf3ffe03fffc00fe0
  | _ => 0
def q15Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff40640108248920b1
  | 1 => 0x24ac285909932594
  | 4 => 0x1101502242244a0a
  | 5 => 0xe091ab493064f40
  | _ => 0
def q15Atlas : Atlas := ⟨3,rawDecor 51 q15Pos q15Neg, 0xeeeeaaaaeeee0000eeeeaaaaeeee0000eeeeaaaaeeee0000eeeeaaaaeeee0000eeeeaaaaeeee0000eeeeaaaaeeee0000eeeeaaaaeeee0000eeeeaaaaeeee0000, q15N, q15R, (fun _ _ => 0), q15I, []⟩
end PEqualNP.Outside.L_meta_37471
namespace PEqualNP.Outside.L_meta_37471
open PEqualNP.Outside.L_meta_37471.Model
def q16K3 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def q16N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q16R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q16K3 (i*3) 3
  | _ => 0
def q16I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q16K3 (3+(h % 1)*1) 1) % 1)
  | _ => 0
def q16Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffbecf
  | 1 => 0xffffffffffffffffffffffffffffffffffdf73
  | 3 => 0xefbc
  | _ => 0
def q16Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffff4205
  | 1 => 0x2412
  | 3 => 0x1828
  | _ => 0
def q16Atlas : Atlas := ⟨3,rawDecor 11 q16Pos q16Neg, 0xee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88, q16N, q16R, (fun _ _ => 0), q16I, []⟩
end PEqualNP.Outside.L_meta_37471
namespace PEqualNP.Outside.L_meta_37471
open PEqualNP.Outside.L_meta_37471.Model
def q17K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q17K3 : Nat → Nat
  | 0 => 0x101003b98ec32f661bccba18f830
  | _ => 0
def q17K2 : Nat → Nat
  | 0 => 0x40340c430c8320c310c831
  | _ => 0
def q17N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
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
  | 2 => 2*((h/8+packedAt q17K2 (78+(h % 8)*2) 2) % 3)
  | _ => 0
def q17Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffbf0fffc3fe3f
  | 1 => 0xffffffffffffffffffffffffffdff0fffc3fc7
  | 3 => 0xefff0fffc3f8
  | 4 => 0xffffffffffffffffffffffffffffffffffffff
  | _ => 0
def q17Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffff41e222d1561b
  | 1 => 0xffffffffffffffffffffffffff222e45551ac5
  | 3 => 0x1444e9999368
  | 4 => 0x8888e2221b6
  | _ => 0
def q17Atlas : Atlas := ⟨4,rawDecor 27 q17Pos q17Neg, 0xee880000ee880000ee880000ee880000ee880000ee880000ee880000ee880000ee880000ee880000ee880000ee880000ee880000ee880000ee880000ee880000, q17N, q17R, (fun _ _ => 0), q17I, []⟩
end PEqualNP.Outside.L_meta_37471
namespace PEqualNP.Outside.L_meta_37471
open PEqualNP.Outside.L_meta_37471.Model
def q18K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q18K3 : Nat → Nat
  | 0 => 0x120000af195c32ba6170c6f18df30
  | _ => 0
def q18K2 : Nat → Nat
  | 0 => 0x40008c424c25906328e428c6510530
  | _ => 0
def q18N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def q18R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q18K4 (i*4) 4
  | 3 => packedAt q18K3 (i*15) 15
  | 2 => packedAt q18K2 (i*26) 26
  | _ => 0
def q18I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q18K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/9+packedAt q18K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q18K2 (104+(h % 8)*2) 2) % 4)
  | _ => 0
def q18Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff3ffff1ffff1ff
  | 1 => 0xffffffffffffffffffffffedfc7f3fe3f0fe73
  | 3 => 0x76ff8fcffc7f0f9c
  | 4 => 0x78fff00fff800fe0
  | _ => 0
def q18Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa0180202049440a5
  | 1 => 0x122324452122a652
  | 3 => 0x9416819484a2b18
  | 4 => 0x78a4eae920ccde0
  | _ => 0
def q18Atlas : Atlas := ⟨4,rawDecor 27 q18Pos q18Neg, 0xee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88, q18N, q18R, (fun _ _ => 0), q18I, []⟩
end PEqualNP.Outside.L_meta_37471
namespace PEqualNP.Outside.L_meta_37471
open PEqualNP.Outside.L_meta_37471.Model
def q19K3 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def q19N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q19R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q19K3 (i*3) 3
  | _ => 0
def q19I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q19K3 (3+(h % 1)*1) 1) % 1)
  | _ => 0
def q19Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffbecf
  | 1 => 0xffffffffffffffffffffffffffffffffffdf73
  | 2 => 0xefbc
  | _ => 0
def q19Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffff4205
  | 1 => 0x2412
  | 2 => 0x1828
  | _ => 0
def q19Atlas : Atlas := ⟨3,rawDecor 7 q19Pos q19Neg, 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8, q19N, q19R, (fun _ _ => 0), q19I, []⟩
end PEqualNP.Outside.L_meta_37471
namespace PEqualNP.Outside.L_meta_37471
open PEqualNP.Outside.L_meta_37471.Model
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
  | 0 => 0xffffffffffffffffffffffbfcffcf8fff873f3
  | 1 => 0xdbf19f3f1c3f8d9c
  | 2 => 0xffffffffffffffffffffffeffe1fffe03ffe1f
  | 5 => 0xf3ffe03fffc00fe0
  | _ => 0
def q20Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff40640108248920b1
  | 1 => 0x24ac285909932594
  | 2 => 0x1101502242244a0a
  | 5 => 0xe091ab493064f40
  | _ => 0
def q20Atlas : Atlas := ⟨3,rawDecor 39 q20Pos q20Neg, 0xeaeaeaeae0e0e0e0eaeaeaeae0e0e0e0eaeaeaeae0e0e0e0eaeaeaeae0e0e0e0eaeaeaeae0e0e0e0eaeaeaeae0e0e0e0eaeaeaeae0e0e0e0eaeaeaeae0e0e0e0, q20N, q20R, (fun _ _ => 0), q20I, []⟩
end PEqualNP.Outside.L_meta_37471
namespace PEqualNP.Outside.L_meta_37471
open PEqualNP.Outside.L_meta_37471.Model
def q21K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q21K3 : Nat → Nat
  | 0 => 0x1000005c31e86378c6a18f731
  | _ => 0
def q21K2 : Nat → Nat
  | 0 => 0x2590631
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
  | 3 => 2*((h/15+packedAt q21K3 (75+(h % 15)*3) 3) % 5)
  | 2 => 2*((h/1+packedAt q21K2 (26+(h % 1)*1) 1) % 1)
  | _ => 0
def q21Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffbfc7fffe3fff1ff
  | 1 => 0xdbf87f3fc7e0e7c
  | 2 => 0xfffffffffffffffffffffffefff8ffff8fff8f
  | 4 => 0xf3fff03fff00ff0
  | _ => 0
def q21Neg : Nat → Bits
  | 0 => 0xfffffffffffffffffffffff4071020a092a0b5
  | 1 => 0x24972456424665c
  | 2 => 0x110268249094b0a
  | 4 => 0xe244eb92418de0
  | _ => 0
def q21Atlas : Atlas := ⟨4,rawDecor 23 q21Pos q21Neg, 0xe8e8a0a0e8e8a0a0e8e8a0a0e8e8a0a0e8e8a0a0e8e8a0a0e8e8a0a0e8e8a0a0e8e8a0a0e8e8a0a0e8e8a0a0e8e8a0a0e8e8a0a0e8e8a0a0e8e8a0a0e8e8a0a0, q21N, q21R, (fun _ _ => 0), q21I, []⟩
end PEqualNP.Outside.L_meta_37471
namespace PEqualNP.Outside.L_meta_37471
open PEqualNP.Outside.L_meta_37471.Model
def q22K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q22K3 : Nat → Nat
  | 0 => 0x14200000004002f195c31b86578c6f985d30
  | _ => 0
def q22K2 : Nat → Nat
  | 0 => 0x200c8c424c25906328e428c6510530
  | _ => 0
def q22N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def q22R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q22K4 (i*4) 4
  | 3 => packedAt q22K3 (i*15) 15
  | 2 => packedAt q22K2 (i*26) 26
  | _ => 0
def q22I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q22K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/23+packedAt q22K3 (90+(h % 23)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q22K2 (104+(h % 8)*2) 2) % 4)
  | _ => 0
def q22Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff3ffff1ffff1ff
  | 1 => 0xffffffffffffffffffffffedfc7f3fe3f0fe73
  | 2 => 0x76ff8fcffc7f0f9c
  | 4 => 0x78fff00fff800fe0
  | _ => 0
def q22Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa0180202049440a5
  | 1 => 0x122324452122a652
  | 2 => 0x9416819484a2b18
  | 4 => 0x78a4eae920ccde0
  | _ => 0
def q22Atlas : Atlas := ⟨4,rawDecor 23 q22Pos q22Neg, 0xe8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8, q22N, q22R, (fun _ _ => 0), q22I, []⟩
end PEqualNP.Outside.L_meta_37471
namespace PEqualNP.Outside.L_meta_37471
open PEqualNP.Outside.L_meta_37471.Model
def q23K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q23K3 : Nat → Nat
  | 0 => 0x40046d32ba6534caf996e32
  | _ => 0
def q23K2 : Nat → Nat
  | 0 => 0x2350e32
  | _ => 0
def q23N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
  | _ => 0
def q23R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q23K4 (i*4) 4
  | 3 => packedAt q23K3 (i*15) 15
  | 2 => packedAt q23K2 (i*26) 26
  | _ => 0
def q23I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q23K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/8+packedAt q23K3 (75+(h % 8)*3) 3) % 5)
  | 2 => 2*((h/1+packedAt q23K2 (26+(h % 1)*1) 1) % 1)
  | _ => 0
def q23Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffbfdcf3e3f3e74cf
  | 1 => 0xfffffffffffffffffffffffdfef3cfc7cf9b33
  | 2 => 0xebf03f3f80fec3c
  | 3 => 0xf3ffc03fff00fc0
  | _ => 0
def q23Neg : Nat → Bits
  | 0 => 0xfffffffffffffffffffffff404104009020045
  | 1 => 0x208041042040112
  | 2 => 0x150aa0690a94c28
  | 3 => 0xe082ab24a14e80
  | _ => 0
def q23Atlas : Atlas := ⟨4,rawDecor 15 q23Pos q23Neg, 0xeee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8, q23N, q23R, (fun _ _ => 0), q23I, []⟩
end PEqualNP.Outside.L_meta_37471
namespace PEqualNP.Outside.L_meta_37471
open PEqualNP.Outside.L_meta_37471.Model
def q24K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q24K3 : Nat → Nat
  | 0 => 0x40046d32ba6534caf996e32
  | _ => 0
def q24K2 : Nat → Nat
  | 0 => 0x2350e32
  | _ => 0
def q24N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
  | _ => 0
def q24R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q24K4 (i*4) 4
  | 3 => packedAt q24K3 (i*15) 15
  | 2 => packedAt q24K2 (i*26) 26
  | _ => 0
def q24I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q24K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/8+packedAt q24K3 (75+(h % 8)*3) 3) % 5)
  | 2 => 2*((h/1+packedAt q24K2 (26+(h % 1)*1) 1) % 1)
  | _ => 0
def q24Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffbfdcf3e3f3e74cf
  | 1 => 0xfffffffffffffffffffffffdfef3cfc7cf9b33
  | 2 => 0xebf03f3f80fec3c
  | 3 => 0xf3ffc03fff00fc0
  | _ => 0
def q24Neg : Nat → Bits
  | 0 => 0xfffffffffffffffffffffff404104009020045
  | 1 => 0x208041042040112
  | 2 => 0x150aa0690a94c28
  | 3 => 0xe082ab24a14e80
  | _ => 0
def q24Atlas : Atlas := ⟨4,rawDecor 15 q24Pos q24Neg, 0xeee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8, q24N, q24R, (fun _ _ => 0), q24I, []⟩
end PEqualNP.Outside.L_meta_37471
namespace PEqualNP.Outside.L_meta_37471
open PEqualNP.Outside.L_meta_37471.Model
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
  | 2 => 0xffffffffffffffffffffffffffffffffffbecf
  | 3 => 0xffffffffffffffffffffffffffffffffffdf73
  | 4 => 0xefbc
  | _ => 0
def q25Neg : Nat → Bits
  | 2 => 0xffffffffffffffffffffffffffffffffff4205
  | 3 => 0x2412
  | 4 => 0x1828
  | _ => 0
def q25Atlas : Atlas := ⟨3,rawDecor 28 q25Pos q25Neg, 0xfff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000, q25N, q25R, (fun _ _ => 0), q25I, []⟩
end PEqualNP.Outside.L_meta_37471
namespace PEqualNP.Outside.L_meta_37471
open PEqualNP.Outside.L_meta_37471.Model
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
  | 2 => 0xffffffffffffffffffffffffffffffffffbecf
  | 3 => 0xffffffffffffffffffffffffffffffffffdf73
  | 4 => 0xefbc
  | _ => 0
def q26Neg : Nat → Bits
  | 2 => 0xffffffffffffffffffffffffffffffffff4205
  | 3 => 0x2412
  | 4 => 0x1828
  | _ => 0
def q26Atlas : Atlas := ⟨3,rawDecor 28 q26Pos q26Neg, 0xfff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000, q26N, q26R, (fun _ _ => 0), q26I, []⟩
end PEqualNP.Outside.L_meta_37471
namespace PEqualNP.Outside.L_meta_37471
open PEqualNP.Outside.L_meta_37471.Model
def q27K3 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def q27N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q27R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q27K3 (i*3) 3
  | _ => 0
def q27I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q27K3 (3+(h % 1)*1) 1) % 1)
  | _ => 0
def q27Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffbecf
  | 2 => 0xffffffffffffffffffffffffffffffffffdf73
  | 4 => 0xefbc
  | _ => 0
def q27Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffff4205
  | 2 => 0x2412
  | 4 => 0x1828
  | _ => 0
def q27Atlas : Atlas := ⟨3,rawDecor 21 q27Pos q27Neg, 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0, q27N, q27R, (fun _ _ => 0), q27I, []⟩
end PEqualNP.Outside.L_meta_37471
namespace PEqualNP.Outside.L_meta_37471
open PEqualNP.Outside.L_meta_37471.Model
def q28K3 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def q28N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q28R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q28K3 (i*3) 3
  | _ => 0
def q28I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q28K3 (3+(h % 1)*1) 1) % 1)
  | _ => 0
def q28Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffbecf
  | 1 => 0xffffffffffffffffffffffffffffffffffdf73
  | 3 => 0xefbc
  | _ => 0
def q28Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffff4205
  | 1 => 0x2412
  | 3 => 0x1828
  | _ => 0
def q28Atlas : Atlas := ⟨3,rawDecor 11 q28Pos q28Neg, 0xee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88, q28N, q28R, (fun _ _ => 0), q28I, []⟩
end PEqualNP.Outside.L_meta_37471
namespace PEqualNP.Outside.L_meta_37471
open PEqualNP.Outside.L_meta_37471.Model
def q29K3 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def q29N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q29R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q29K3 (i*3) 3
  | _ => 0
def q29I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q29K3 (3+(h % 1)*1) 1) % 1)
  | _ => 0
def q29Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffbecf
  | 1 => 0xffffffffffffffffffffffffffffffffffdf73
  | 3 => 0xefbc
  | _ => 0
def q29Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffff4205
  | 1 => 0x2412
  | 3 => 0x1828
  | _ => 0
def q29Atlas : Atlas := ⟨3,rawDecor 11 q29Pos q29Neg, 0xee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88, q29N, q29R, (fun _ _ => 0), q29I, []⟩
end PEqualNP.Outside.L_meta_37471
namespace PEqualNP.Outside.L_meta_37471
open PEqualNP.Outside.L_meta_37471.Model
def q30K3 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def q30N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q30R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q30K3 (i*3) 3
  | _ => 0
def q30I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q30K3 (3+(h % 1)*1) 1) % 1)
  | _ => 0
def q30Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffbecf
  | 1 => 0xffffffffffffffffffffffffffffffffffdf73
  | 2 => 0xefbc
  | _ => 0
def q30Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffff4205
  | 1 => 0x2412
  | 2 => 0x1828
  | _ => 0
def q30Atlas : Atlas := ⟨3,rawDecor 7 q30Pos q30Neg, 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8, q30N, q30R, (fun _ _ => 0), q30I, []⟩
end PEqualNP.Outside.L_meta_37471
namespace PEqualNP.Outside.L_meta_37471
open PEqualNP.Outside.L_meta_37471.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xea014016842600151007f90001ff10007f4c401fe10007f50801fd30005f55001fe31007f48401fd40007f880017d52007f48001fc10007f8c001fe41007f50401fd43007f4c801fe21005f94001fd10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x14000964000020086c1470000c04001800002c3c20009408040000004400041084002800000824680028001008100c10000804040000d0440068101c00001400449c000000440184004418004c100000140434006401fea18200adfd4930007fa85080027f65500017fb1c4200bf58a10037f88290003f621c40017eb1c4200ff18532007fec0990377c50884017eb182000fd8c710037f8c89002f7f4094001beaa46207df19520076f8a099002ff63c40013eb2a8400dfd9530004fac928017fc634801bbfaa44201ff908100057ec8880037d528c417bfa1ca000ff5081000ff884080037e2194001bf18ca000df55130006fca098003fd43c4015be2826006ffd0d20004f8c0aa0033d54500017e30a8000bf58810005bec68803f7f40548013e302a4009f58a50005fec58800ffe42c4001ff18a4000df4ca50007fa858800ffc42c40013fb12a800df54930004feca98002fc614c80dffa024000cf55241047f88710003fe614801dbfaa2640adfd513007efe86a9002fc6150819fe3244200ff4c120017fe8408033fc41884017fb026400ff1813202ffcc690002ff624c401fb10a2005ff10d20005fac690003fc614c0015fb226200bf58241017fe8608033ff43884017e30a4000bfd8d20007ba6518813ff42c400177b1220009fd9520006faa8900027d65c4003ff1902000bfd814303ef8a090003fd6348001bf2824005ff0c52002ffe6090003fc6148001ffb1a40009fd9640027fe8788003fd32040017e30a6000dfd9520007fec71080ffe32c4001fea122000bf18543007ba649802b7c654c0013fb2c400cffd0221004feca88002ff6050801beaa26400ffd8221004feca98802ff624c001ff10a6007dfd5120005fac1108037d54884016eb182000bf58a3004ffe871001bfe6448001fe996200fdf1055205ef88328002fd63880017fb1220009fd9152
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x17160801f8b18244181c0c400042e48000087861e499001208800102c0050800019002400300163000a002880814003004fc7650f100047c76551200067f54d81320057f7255130005fb704c81005e7e6494130004fc768853000eee4258810004ff764c810004fc7158d200867f52d81320043d7418152005f471508100067c5058d2005e7c64941300067f65d8d200067d628c65002edf30d8d200057c714ca50005f77388710006ef74d89100057c7055132004ff7650a10004ff7650c100067d63941200067d541853202edc31d8d20004ff7650810006f43118520006ef62885300067c50d8132006f671d8b1007e7c64549300067c65d8d20006f44118520004fc76509100967d52185320075d3294130085fb7058d2005d7c748c6500067e75d81320057f704ca50004fd7018532004fe71d814300ef62118520006dd63508100047d72181540067d54d8132006ed62508100057f7388650004fc764cb10005ef724c120006dd3218530004fc7650b10005f47158d200067f62941300057f72552310057d72941300867d52d81320067d54d89300067c50d8d20005fb704cb10004fd72185300057c7655120005f47150a1009e3c41d8954005f4714c810004fd7018543005f47150c100067c6558d20004787059542004fd70d8e21086fa20d81320067f6558d20005f57388710004fe71d8142004ff7058e21004fe71d813209e3f40d89540057d738865002ede63d8d20084ff7058d20006ef62509100067f6394120007d5328c710095f671d8e21035bc7458d200075d328c650004fd7018542006df63509100067c50d8930005f67118132004fe71d8d2008f5c504c93002edc6358d200067d75d8132004f47158d200047c76551300067f54d8930
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x401c000200338f0480000c000100100000600010fb0faa6c0990021f21d54d89300a61e320e0aa26400a3d84143604c801878e832ac6900021fa1c5058d200063bb28e2b1a400087e87d53624c0010ff0eb1ca090002bc60031185200053c402a9b026400c74651c563480012db04382a8990021f608765513000537c12a9b126000a3d84143624c0014db05aa6c4980028f61275d81320043fc32e710ca000c3c74d956348029878e8282c690002bc600411852005d1e422c7282400087f87553604c8011df04b80c2a18027c6007150c1000536c10a1b126000a3d84141634800147b08286c6900029d20563941200066a318e2b1a4000c747114163480018dae5b14a0980033558c7150810
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x80a40f25d841416348001835841c45058d20
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x4b
  | 2 => 0x4d
  | 3 => 0x138b
  | 4 => 0x138d
  | 5 => 0x98c
  | 6 => 0x98d
  | 7 => 0x98e
  | 8 => 0x128c
  | 9 => 0x128d
  | 10 => 0x9ce
  | 11 => 0x134d
  | 12 => 0x140d
  | 13 => 0x140e
  | 14 => 0xcce
  | 15 => 0xd4d
  | 16 => 0x168b
  | 17 => 0xcc9d6
  | 18 => 0x24b
  | 19 => 0x1a0d
  | 20 => 0x14d
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 22
  | 7 => 130
  | 6 => 99
  | 5 => 34
  | 4 => 2
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
  | 8 => 2*((h/14+packedAt gbK8 (572+(h % 14)*5) 5) % 22)
  | 7 => 2*((h/85+packedAt gbK7 (4810+(h % 85)*8) 8) % 130)
  | 6 => 2*((h/54+packedAt gbK6 (4752+(h % 54)*7) 7) % 99)
  | 5 => 2*((h/32+packedAt gbK5 (2006+(h % 32)*6) 6) % 34)
  | 4 => 2*((h/7+packedAt gbK4 (140+(h % 7)*1) 1) % 2)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xf80fff00fff01ffff00fffff463c7ffb1c7e3f
  | 1 => 0xfff03fff01ffe07ffff03e00b9cfb13de39fcc
  | 2 => 0x1fffc00001ffff81ffffffffc1f3c1c603e3ff
  | 3 => 0x1ffffffffe000001ffffc000fe03fe07fc03f0
  | 4 => 0x1ffffffffffffffe00000000fffc0007fffc00
  | 5 => 0xe00000000000000000000000fffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0xa8014b044a5008aa508252aa021416590c2e15
  | 1 => 0xc8b0156508b6204cb692340618c9b1296196cc
  | 2 => 0x155a8010212b55012b2ca954c162c18602c16a
  | 3 => 0x9e6ce6b6ac010409cdcf1018ec037a07b403b0
  | 4 => 0x178f38d8f1cd9e7001040060f7bc0006db7800
  | 5 => 0x40800e0c00e18600e082180ffffedf0000000
  | _ => 0
def gbRaw : List Sig := (rawDecor 63 gbPos gbNeg).map Prod.fst
def gbPools : List BoundPool := [(0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555, 5, 0, gbRaw),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 7, 0, gbRaw),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 7, 0, gbRaw),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 5, 0, gbRaw),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff, 7, 0, gbRaw),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 5, 0, gbRaw),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff, 8, 0, gbRaw),(0x44444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444, 4, 0, gbRaw),(0x555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555, 5, 0, gbRaw),(0x55555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000, 5, 0, gbRaw),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 4, 0, gbRaw),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 5, 0, gbRaw),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 4, 0, gbRaw),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 5, 0, gbRaw),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000, 5, 0, gbRaw),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00, 4, 0, gbRaw),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000, 4, 0, gbRaw),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f, 5, 0, gbRaw),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000, 5, 0, gbRaw),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 4, 0, gbRaw),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 4, 0, gbRaw),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff, 5, 0, gbRaw),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000, 5, 0, gbRaw),(0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000, 5, 0, gbRaw),(0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000, 5, 0, gbRaw),(0x444444440000000044444444000000004444444400000000444444440000000044444444000000004444444400000000444444440000000044444444, 4, 0, gbRaw),(0x44444444000000004444444400000000444444440000000044444444000000004444444400000000444444440000000044444444000000004444444400000000, 4, 0, gbRaw),(0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc, 4, 0, gbRaw),(0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000, 4, 0, gbRaw),(0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f000000000000, 4, 0, gbRaw),(0xff00000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000000000ff0000, 4, 0, gbRaw)]
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeee8eaa8eee8e0a0eee8eaa8eee8e0a0eee8eaa8eee8e0a0eee8eaa8eee8e0a0eee8eaa8eee8e0a0eee8eaa8eee8e0a0eee8eaa8eee8e0a0eee8eaa8eee8e0a0, gbN, gbR, gbH, gbI, gbPools⟩
end PEqualNP.Outside.L_meta_37471
namespace PEqualNP.Outside.L_meta_37471
open PEqualNP.Outside.L_meta_37471.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs2_2_0 : Interval s2Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 5 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 25 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 91 := block_range (n:=91) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 91 := bs2_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 44 := bs2_5_0
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
theorem bs3_2_0 : Interval s3Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 10 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 60 := block_range (n:=60) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 60 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_96 : Interval s3Atlas 4 96 69 := block_range (n:=69) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 165 := (concat bs3_4_0 bs3_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 50 := block_range (n:=50) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 50 := bs3_5_0
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
theorem bs4_3_0 : Interval s4Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 8 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 92 := block_range (n:=92) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 92 := bs4_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 44 := bs4_5_0
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
theorem bs5_2_0 : Interval s5Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 5 := bs5_2_0
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
theorem bs5_4_384 : Interval s5Atlas 4 384 30 := block_range (n:=30) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 414 := (concat (concat bs5_4_0 bs5_4_96) (concat bs5_4_192 (concat bs5_4_288 bs5_4_384)))
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
theorem bs5_5_576 : Interval s5Atlas 5 576 40 := block_range (n:=40) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 616 := (concat (concat bs5_5_0 (concat bs5_5_96 bs5_5_192)) (concat (concat bs5_5_288 bs5_5_384) (concat bs5_5_480 bs5_5_576)))
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
theorem bq3_3_0 : Interval q3Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq3_3 : Interval q3Atlas 3 0 1 := bq3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq3_4_0 : Interval q3Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq3_4 : Interval q3Atlas 4 0 1 := bq3_4_0
theorem allq3 : ∀ k ≤ 4, ∀ i < count q3Atlas k, checkRow q3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq3_3 i (by omega) hi
  · exact allq3_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq5_2_0 : Interval q5Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq5_2 : Interval q5Atlas 2 0 1 := bq5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq5_3_0 : Interval q5Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allq5_3 : Interval q5Atlas 3 0 5 := bq5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq5_4_0 : Interval q5Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq5_4 : Interval q5Atlas 4 0 1 := bq5_4_0
theorem allq5 : ∀ k ≤ 4, ∀ i < count q5Atlas k, checkRow q5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq5_2 i (by omega) hi
  · exact allq5_3 i (by omega) hi
  · exact allq5_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq7_3_0 : Interval q7Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq7_3 : Interval q7Atlas 3 0 1 := bq7_3_0
theorem allq7 : ∀ k ≤ 3, ∀ i < count q7Atlas k, checkRow q7Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq7_3 i (by omega) hi
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
theorem bq10_3_0 : Interval q10Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq10_3 : Interval q10Atlas 3 0 1 := bq10_3_0
theorem allq10 : ∀ k ≤ 3, ∀ i < count q10Atlas k, checkRow q10Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq10_3 i (by omega) hi
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
theorem bq14_2_0 : Interval q14Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq14_2 : Interval q14Atlas 2 0 3 := bq14_2_0
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
theorem bq17_2_0 : Interval q17Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq17_2 : Interval q17Atlas 2 0 3 := bq17_2_0
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
theorem bq18_2_0 : Interval q18Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq18_2 : Interval q18Atlas 2 0 4 := bq18_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq18_3_0 : Interval q18Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq18_3 : Interval q18Atlas 3 0 6 := bq18_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq18_4_0 : Interval q18Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq18_4 : Interval q18Atlas 4 0 1 := bq18_4_0
theorem allq18 : ∀ k ≤ 4, ∀ i < count q18Atlas k, checkRow q18Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq18_2 i (by omega) hi
  · exact allq18_3 i (by omega) hi
  · exact allq18_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq19_3_0 : Interval q19Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq19_3 : Interval q19Atlas 3 0 1 := bq19_3_0
theorem allq19 : ∀ k ≤ 3, ∀ i < count q19Atlas k, checkRow q19Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq19_3 i (by omega) hi
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
theorem bq22_2_0 : Interval q22Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq22_2 : Interval q22Atlas 2 0 4 := bq22_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq22_3_0 : Interval q22Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq22_3 : Interval q22Atlas 3 0 6 := bq22_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq22_4_0 : Interval q22Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq22_4 : Interval q22Atlas 4 0 1 := bq22_4_0
theorem allq22 : ∀ k ≤ 4, ∀ i < count q22Atlas k, checkRow q22Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq22_2 i (by omega) hi
  · exact allq22_3 i (by omega) hi
  · exact allq22_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq23_2_0 : Interval q23Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq23_2 : Interval q23Atlas 2 0 1 := bq23_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq23_3_0 : Interval q23Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allq23_3 : Interval q23Atlas 3 0 5 := bq23_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq23_4_0 : Interval q23Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq23_4 : Interval q23Atlas 4 0 1 := bq23_4_0
theorem allq23 : ∀ k ≤ 4, ∀ i < count q23Atlas k, checkRow q23Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq23_2 i (by omega) hi
  · exact allq23_3 i (by omega) hi
  · exact allq23_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq24_2_0 : Interval q24Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq24_2 : Interval q24Atlas 2 0 1 := bq24_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq24_3_0 : Interval q24Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allq24_3 : Interval q24Atlas 3 0 5 := bq24_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq24_4_0 : Interval q24Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq24_4 : Interval q24Atlas 4 0 1 := bq24_4_0
theorem allq24 : ∀ k ≤ 4, ∀ i < count q24Atlas k, checkRow q24Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq24_2 i (by omega) hi
  · exact allq24_3 i (by omega) hi
  · exact allq24_4 i (by omega) hi
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
theorem bq27_3_0 : Interval q27Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq27_3 : Interval q27Atlas 3 0 1 := bq27_3_0
theorem allq27 : ∀ k ≤ 3, ∀ i < count q27Atlas k, checkRow q27Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq27_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq28_3_0 : Interval q28Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq28_3 : Interval q28Atlas 3 0 1 := bq28_3_0
theorem allq28 : ∀ k ≤ 3, ∀ i < count q28Atlas k, checkRow q28Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq28_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq29_3_0 : Interval q29Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq29_3 : Interval q29Atlas 3 0 1 := bq29_3_0
theorem allq29 : ∀ k ≤ 3, ∀ i < count q29Atlas k, checkRow q29Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq29_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq30_3_0 : Interval q30Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq30_3 : Interval q30Atlas 3 0 1 := bq30_3_0
theorem allq30 : ∀ k ≤ 3, ∀ i < count q30Atlas k, checkRow q30Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq30_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 2 := bgb_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_0 : Interval gbAtlas 5 0 34 := block_range (n:=34) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 34 := bgb_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_0 : Interval gbAtlas 6 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_96 : Interval gbAtlas 6 96 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 99 := (concat bgb_6_0 bgb_6_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_96 : Interval gbAtlas 7 96 34 := block_range (n:=34) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 130 := (concat bgb_7_0 bgb_7_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 22 := block_range (n:=22) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 22 := bgb_8_0
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
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 18, 19),(inputs.getD 1 zero, 17, 19),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 17, 19),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 6, 14),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq3 (cert : Complete q3Atlas) : Lower true (roots q3Atlas) (target q3Atlas) 5 := by
  have ready : Ready q3Atlas (asRow q3Pos) (asRow q3Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq5 (cert : Complete q5Atlas) : Lower true (roots q5Atlas) (target q5Atlas) 5 := by
  have ready : Ready q5Atlas (asRow q5Pos) (asRow q5Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq7 (cert : Complete q7Atlas) : Lower true (roots q7Atlas) (target q7Atlas) 4 := by
  have ready : Ready q7Atlas (asRow q7Pos) (asRow q7Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 4, 20)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq8 (cert : Complete q8Atlas) : Lower true (roots q8Atlas) (target q8Atlas) 5 := by
  have ready : Ready q8Atlas (asRow q8Pos) (asRow q8Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq9 (cert : Complete q9Atlas) : Lower true (roots q9Atlas) (target q9Atlas) 5 := by
  have ready : Ready q9Atlas (asRow q9Pos) (asRow q9Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq10 (cert : Complete q10Atlas) : Lower true (roots q10Atlas) (target q10Atlas) 4 := by
  have ready : Ready q10Atlas (asRow q10Pos) (asRow q10Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 3 zero, 16, 24),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq11 (cert : Complete q11Atlas) : Lower true (roots q11Atlas) (target q11Atlas) 5 := by
  have ready : Ready q11Atlas (asRow q11Pos) (asRow q11Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq12 (cert : Complete q12Atlas) : Lower true (roots q12Atlas) (target q12Atlas) 4 := by
  have ready : Ready q12Atlas (asRow q12Pos) (asRow q12Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq13 (cert : Complete q13Atlas) : Lower true (roots q13Atlas) (target q13Atlas) 5 := by
  have ready : Ready q13Atlas (asRow q13Pos) (asRow q13Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq14 (cert : Complete q14Atlas) : Lower true (roots q14Atlas) (target q14Atlas) 5 := by
  have ready : Ready q14Atlas (asRow q14Pos) (asRow q14Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 4, 20)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq15 (cert : Complete q15Atlas) : Lower true (roots q15Atlas) (target q15Atlas) 4 := by
  have ready : Ready q15Atlas (asRow q15Pos) (asRow q15Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 16, 18),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq16 (cert : Complete q16Atlas) : Lower true (roots q16Atlas) (target q16Atlas) 4 := by
  have ready : Ready q16Atlas (asRow q16Pos) (asRow q16Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq17 (cert : Complete q17Atlas) : Lower true (roots q17Atlas) (target q17Atlas) 5 := by
  have ready : Ready q17Atlas (asRow q17Pos) (asRow q17Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 18, 19),(inputs.getD 1 zero, 17, 19),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq18 (cert : Complete q18Atlas) : Lower true (roots q18Atlas) (target q18Atlas) 5 := by
  have ready : Ready q18Atlas (asRow q18Pos) (asRow q18Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 10, 26)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq19 (cert : Complete q19Atlas) : Lower true (roots q19Atlas) (target q19Atlas) 4 := by
  have ready : Ready q19Atlas (asRow q19Pos) (asRow q19Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq20 (cert : Complete q20Atlas) : Lower true (roots q20Atlas) (target q20Atlas) 4 := by
  have ready : Ready q20Atlas (asRow q20Pos) (asRow q20Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq21 (cert : Complete q21Atlas) : Lower true (roots q21Atlas) (target q21Atlas) 5 := by
  have ready : Ready q21Atlas (asRow q21Pos) (asRow q21Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 17, 19),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq22 (cert : Complete q22Atlas) : Lower true (roots q22Atlas) (target q22Atlas) 5 := by
  have ready : Ready q22Atlas (asRow q22Pos) (asRow q22Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq23 (cert : Complete q23Atlas) : Lower true (roots q23Atlas) (target q23Atlas) 5 := by
  have ready : Ready q23Atlas (asRow q23Pos) (asRow q23Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq24 (cert : Complete q24Atlas) : Lower true (roots q24Atlas) (target q24Atlas) 5 := by
  have ready : Ready q24Atlas (asRow q24Pos) (asRow q24Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq25 (cert : Complete q25Atlas) : Lower true (roots q25Atlas) (target q25Atlas) 4 := by
  have ready : Ready q25Atlas (asRow q25Pos) (asRow q25Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 4, 20)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq26 (cert : Complete q26Atlas) : Lower true (roots q26Atlas) (target q26Atlas) 4 := by
  have ready : Ready q26Atlas (asRow q26Pos) (asRow q26Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 4, 20)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq27 (cert : Complete q27Atlas) : Lower true (roots q27Atlas) (target q27Atlas) 4 := by
  have ready : Ready q27Atlas (asRow q27Pos) (asRow q27Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq28 (cert : Complete q28Atlas) : Lower true (roots q28Atlas) (target q28Atlas) 4 := by
  have ready : Ready q28Atlas (asRow q28Pos) (asRow q28Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq29 (cert : Complete q29Atlas) : Lower true (roots q29Atlas) (target q29Atlas) 4 := by
  have ready : Ready q29Atlas (asRow q29Pos) (asRow q29Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq30 (cert : Complete q30Atlas) : Lower true (roots q30Atlas) (target q30Atlas) 4 := by
  have ready : Ready q30Atlas (asRow q30Pos) (asRow q30Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) (pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact pv
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeee8eaa8eee8e0a0eee8eaa8eee8e0a0eee8eaa8eee8e0a0eee8eaa8eee8e0a0eee8eaa8eee8e0a0eee8eaa8eee8e0a0eee8eaa8eee8e0a0eee8eaa8eee8e0a0
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certq3 : Complete q3Atlas) (certq5 : Complete q5Atlas) (certq7 : Complete q7Atlas) (certq8 : Complete q8Atlas) (certq9 : Complete q9Atlas) (certq10 : Complete q10Atlas) (certq11 : Complete q11Atlas) (certq12 : Complete q12Atlas) (certq13 : Complete q13Atlas) (certq14 : Complete q14Atlas) (certq15 : Complete q15Atlas) (certq16 : Complete q16Atlas) (certq17 : Complete q17Atlas) (certq18 : Complete q18Atlas) (certq19 : Complete q19Atlas) (certq20 : Complete q20Atlas) (certq21 : Complete q21Atlas) (certq22 : Complete q22Atlas) (certq23 : Complete q23Atlas) (certq24 : Complete q24Atlas) (certq25 : Complete q25Atlas) (certq26 : Complete q26Atlas) (certq27 : Complete q27Atlas) (certq28 : Complete q28Atlas) (certq29 : Complete q29Atlas) (certq30 : Complete q30Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
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
    slice_correct (ms:=fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have q1 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f : Sig) 7 :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have q2 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff : Sig) 7 :=
    slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
  have q3 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00 : Sig) 5 :=
    slice_correct (ms:=fixRows 0 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq3 certq3)
  have q4 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff : Sig) 7 :=
    slice_correct (ms:=fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds4 certs4)
  have q5 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000 : Sig) 5 :=
    slice_correct (ms:=fixRows 32 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq5 certq5)
  have q6 : Slice true (roots gbAtlas) (target gbAtlas) (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff : Sig) 8 :=
    slice_correct (ms:=fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds5 certs5)
  have q7 : Slice true (roots gbAtlas) (target gbAtlas) (0x44444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444 : Sig) 4 :=
    slice_correct (ms:=fixRows 33 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq7 certq7)
  have q8 : Slice true (roots gbAtlas) (target gbAtlas) (0x555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555 : Sig) 5 :=
    slice_correct (ms:=fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq8 certq8)
  have q9 : Slice true (roots gbAtlas) (target gbAtlas) (0x55555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000 : Sig) 5 :=
    slice_correct (ms:=fixRows 1 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq9 certq9)
  have q10 : Slice true (roots gbAtlas) (target gbAtlas) (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c : Sig) 4 :=
    slice_correct (ms:=fixRows 4 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq10 certq10)
  have q11 : Slice true (roots gbAtlas) (target gbAtlas) (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc : Sig) 5 :=
    slice_correct (ms:=fixRows 8 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq11 certq11)
  have q12 : Slice true (roots gbAtlas) (target gbAtlas) (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc : Sig) 4 :=
    slice_correct (ms:=fixRows 16 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq12 certq12)
  have q13 : Slice true (roots gbAtlas) (target gbAtlas) (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc : Sig) 5 :=
    slice_correct (ms:=fixRows 32 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq13 certq13)
  have q14 : Slice true (roots gbAtlas) (target gbAtlas) (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : Sig) 5 :=
    slice_correct (ms:=fixRows 0 34) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq14 certq14)
  have q15 : Slice true (roots gbAtlas) (target gbAtlas) (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00 : Sig) 4 :=
    slice_correct (ms:=fixRows 4 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq15 certq15)
  have q16 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000 : Sig) 4 :=
    slice_correct (ms:=fixRows 36 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq16 certq16)
  have q17 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f : Sig) 5 :=
    slice_correct (ms:=fixRows 36 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq17 certq17)
  have q18 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000 : Sig) 5 :=
    slice_correct (ms:=fixRows 4 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq18 certq18)
  have q19 : Slice true (roots gbAtlas) (target gbAtlas) (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000 : Sig) 4 :=
    slice_correct (ms:=fixRows 40 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq19 certq19)
  have q20 : Slice true (roots gbAtlas) (target gbAtlas) (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00 : Sig) 4 :=
    slice_correct (ms:=fixRows 16 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq20 certq20)
  have q21 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff : Sig) 5 :=
    slice_correct (ms:=fixRows 40 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq21 certq21)
  have q22 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000 : Sig) 5 :=
    slice_correct (ms:=fixRows 8 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq22 certq22)
  have q23 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000 : Sig) 5 :=
    slice_correct (ms:=fixRows 32 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq23 certq23)
  have q24 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000 : Sig) 5 :=
    slice_correct (ms:=fixRows 0 48) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq24 certq24)
  have q25 : Slice true (roots gbAtlas) (target gbAtlas) (0x444444440000000044444444000000004444444400000000444444440000000044444444000000004444444400000000444444440000000044444444 : Sig) 4 :=
    slice_correct (ms:=fixRows 33 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq25 certq25)
  have q26 : Slice true (roots gbAtlas) (target gbAtlas) (0x44444444000000004444444400000000444444440000000044444444000000004444444400000000444444440000000044444444000000004444444400000000 : Sig) 4 :=
    slice_correct (ms:=fixRows 1 34) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq26 certq26)
  have q27 : Slice true (roots gbAtlas) (target gbAtlas) (0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc : Sig) 4 :=
    slice_correct (ms:=fixRows 40 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq27 certq27)
  have q28 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000 : Sig) 4 :=
    slice_correct (ms:=fixRows 36 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq28 certq28)
  have q29 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f000000000000 : Sig) 4 :=
    slice_correct (ms:=fixRows 4 48) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq29 certq29)
  have q30 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000000000ff0000 : Sig) 4 :=
    slice_correct (ms:=fixRows 40 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq30 certq30)
  have pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p :=
    List.forall_iff_forall_mem.1 (show List.Forall (fun p => ValidPool true (roots gbAtlas) (target gbAtlas) p) gbPools from ⟨build_valid q0 [] rfl, build_valid q1 [] rfl, build_valid q2 [] rfl, build_valid q3 [] rfl, build_valid q4 [] rfl, build_valid q5 [] rfl, build_valid q6 [] rfl, build_valid q7 [] rfl, build_valid q8 [] rfl, build_valid q9 [] rfl, build_valid q10 [] rfl, build_valid q11 [] rfl, build_valid q12 [] rfl, build_valid q13 [] rfl, build_valid q14 [] rfl, build_valid q15 [] rfl, build_valid q16 [] rfl, build_valid q17 [] rfl, build_valid q18 [] rfl, build_valid q19 [] rfl, build_valid q20 [] rfl, build_valid q21 [] rfl, build_valid q22 [] rfl, build_valid q23 [] rfl, build_valid q24 [] rfl, build_valid q25 [] rfl, build_valid q26 [] rfl, build_valid q27 [] rfl, build_valid q28 [] rfl, build_valid q29 [] rfl, build_valid q30 [] rfl⟩)
  have low := boundgb certgb allCuts pv
  have lift := lift_ok (u:=true) (ms:=fixRows 0 0) (raw:=fullRoots) (T:=fullWord) (xs:=[]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 0 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008241832 * 2 ^ 32 + 4008239264) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37471.Model.Repr at out
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

def mono : List Gate := [⟨.and,[0,1]⟩,⟨.or,[0,4]⟩,⟨.and,[2,7]⟩,⟨.or,[6,8]⟩,⟨.or,[0,1]⟩,⟨.and,[5,7]⟩,⟨.or,[3,9]⟩,⟨.and,[10,12]⟩,⟨.or,[4,11]⟩,⟨.or,[2,14]⟩,⟨.and,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241832 * 2 ^ 32 + 4008239264) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241832 * 2 ^ 32 + 4008239264) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37471

open PEqualNP.Outside.L_meta_37471 in
theorem PEqualNP.Outside.L_meta_37471 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241832 * 2 ^ 32 + 4008239264) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241832 * 2 ^ 32 + 4008239264) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allq3 allq5 allq7 allq8 allq9 allq10 allq11 allq12 allq13 allq14 allq15 allq16 allq17 allq18 allq19 allq20 allq21 allq22 allq23 allq24 allq25 allq26 allq27 allq28 allq29 allq30 allgb)
