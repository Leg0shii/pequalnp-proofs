import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, children closed at the parent by
-- restriction pools (closeChild of the model), and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37465.Model
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


end PEqualNP.Outside.L_meta_37465.Model

namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
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

def SBf (j : Nat) : Nat := [5, 3, 7, 6, 8, 7].getD j 0

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

end PEqualNP.Outside.L_meta_37465

namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
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
end PEqualNP.Outside.L_meta_37465
namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
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
  | 2 => 0xffffffffffffffffffffffffdfc7fff87ffe3f
  | 3 => 0x6bf878ff8783cc
  | 5 => 0x73ff80fff803f0
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffff8041102888a8d5
  | 2 => 0x20b2245455522a
  | 3 => 0x1517459d461b4c
  | 5 => 0xe2476e66463b0
  | _ => 0
def s1Atlas : Atlas := ⟨2,rawDecor 45 s1Pos s1Neg, 0xaaa0aaa0a0a0a0a0aaa0aaa0a0a0a0a0aaa0aaa0a0a0a0a0aaa0aaa0a0a0a0a0aaa0aaa0a0a0a0a0aaa0aaa0a0a0a0a0aaa0aaa0a0a0a0a0aaa0aaa0a0a0a0a0, s1N, s1R, (fun _ _ => 0), s1I, []⟩
end PEqualNP.Outside.L_meta_37465
namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x30006c11061400c00000800800000000400000070000401000001000240012450000040000010822001c0fd32fe20fc32fd31dc31fd20df30fe43fe40dd30fd10fe41fe31fe30ff40ff20fc20ff10de31fe32dc32fc40fe21ff43fd43de32ff42fc21ff31fc30fc41fd42fc43fe42be40ff41fd41fc42fc10ff32fc31ff21fe10bc40ff30fd30fd21fd40
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x1300000005030100130009030105050f3c000008003b0000000000000b0200090b00000000150002063b000003000000000000150009000000000400030300000100035800000000000200011602050100000b1d012d05050503014000000009000004231800420d00010100af29e85cc32882dea4a0e78c840b7a92215e538877080985754f42af298817b5050ab8a7885754031b6292835c514c27ea8885e14142af298415e530433864206e10320cf206615d53c86baa610750c610b7a9261775148278a890f30c820bda82439d53102bca6185754e219e2a261cc524c27aa9884f94040ea28a615f534433c632075d4530af288655c53c82f0a0a0cf55320ce18881745150b74a0205754032eb288635e510c7a862084f55330afa9a439c404c27aa810ee10010cf298813f544c37081885714d20cf194815f53c43b6a0986754e409f2a6215e520cbca4210d314930ae298435f53086e8a2904f950219e2a24154514c2baa7204f95320ce19481795090eb8a6a15714930afa9a415e518cabca518d754e20bba8a853f54482bca51957d4d41aea84657850486f6a0a0d794f21b6292615c53506bea6a15754c40ce2066177514c2baa7a0d794e20af2966174514c2f4a121cfd5121e7a92619c319027ca12057d4f209e2a2219c544c2bca7205794e10cf202615d538433aa9985794631cf188815c534433ca9985794730b6292215d538c39ca4196e10230cc202619f544c3b680985754c10cf29c815e520c77080105754231ec202613e54cc2b8a690d794f41
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x114006c62c3000009086503012784002140c654c40082e06048421c3150524c3105110130c6d4c40c825661d4f20c6d4c40c424c6254031965805308655650c410e20c8400831a6510130a6580321034452d45308e18154087903110010a91912108699600c440c5150514c2546154032d214b404c30c5210130c6144404c3935110130a658e50103485210130e2148404c3505110130e2d48404c35051d0130ca148404c21e6510130c6148404c3175414530c3d50524c30c5290130a6994404c3445214530c5144404c3475214530c654c400431451901309398b53c43305110130a6993504c39051101309359432083085210130a6982404c21e6590130
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0xc00025c0d485110130e00a42888098509750c84008288ba86220021429cb5310310e00a5a88809851271d4c40c824838ac019081221c9600c440
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 136
  | 3 => 50
  | 2 => 9
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
  | 5 => 2*((h/58+packedAt s2K5 (768+(h % 58)*6) 6) % 48)
  | 4 => 2*((h/108+packedAt s2K4 (3672+(h % 108)*8) 8) % 136)
  | 3 => 2*((h/23+packedAt s2K3 (1900+(h % 23)*6) 6) % 50)
  | 2 => 2*((h/10+packedAt s2K2 (441+(h % 10)*4) 4) % 9)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x7ffffffffffc07ffc0fffffffffc03f1fffc7
  | 1 => 0xf80ffff01ffffffffff03ffc07ffffffe3c7ff
  | 3 => 0xfff01fffe03fffffffffc0fff80ffffffc78ff
  | 4 => 0xffffe000003fff80ffffff00000fffc0ff80f8
  | 5 => 0xffffffffffc00000fffffffffff00000ffff00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xc0912591428847122c02cb2d2a52c6190d9bc3
  | 1 => 0x4e8448a4c514892454b0155485655a6a62c55d
  | 3 => 0x922d114289a512489955409ab109acb4b468ae
  | 4 => 0xe4c99d8b163a240eee69a603264e3718df80f0
  | 5 => 0x70e1e0c183c3870f38e38e3c7803820fb7600
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xee88aa88cc008800ee88aa88cc008800ee88aa88cc008800ee88aa88cc008800ee88aa88cc008800ee88aa88cc008800ee88aa88cc008800ee88aa88cc008800, s2N, s2R, (fun _ _ => 0), s2I, []⟩
end PEqualNP.Outside.L_meta_37465
namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x10004003010000000004dc31be40bf42de32bd42df30dc32bc41bc40be41de31dd30
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x202756518ca70a0a165104319a28a854c524c2a8a2984d94640
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 7
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (i*5) 5
  | 4 => packedAt s3K4 (i*16) 16
  | 3 => packedAt s3K3 (i*27) 27
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/25+packedAt s3K4 (192+(h % 25)*4) 4) % 12)
  | 3 => 2*((h/9+packedAt s3K3 (189+(h % 9)*3) 3) % 7)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xfffffffe07fffffe07fffffffe03ffff1ffe3f
  | 1 => 0xffc07ffff80fe03ff83ff81ffffc0f80e79fcc
  | 2 => 0x3fff81ffffffffffffc0ffe03ffffffff8e3ff
  | 4 => 0xc00001fffff0003fffff00003ffff000ff03f0
  | 5 => 0xfffffe000000003fffffffffc0000000fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x4a4508423122490a014b2a294a2194aa0b2e15
  | 1 => 0x929314a450e485565815591596e48d066596cc
  | 2 => 0x210a252882491424aa809544254a2a54b0c16a
  | 4 => 0x3a2c59d12481d9bb34e6061939b3c418df03b0
  | 5 => 0x3c3061e1c70e1e3dc738e79e01c30860fef800
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xe8e8a8a8e0e0a0a0e8e8a8a8e0e0a0a0e8e8a8a8e0e0a0a0e8e8a8a8e0e0a0a0e8e8a8a8e0e0a0a0e8e8a8a8e0e0a0a0e8e8a8a8e0e0a0a0e8e8a8a8e0e0a0a0, s3N, s3R, (fun _ _ => 0), s3I, []⟩
end PEqualNP.Outside.L_meta_37465
namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x1c128e00268400001a001280010280002352040000fd43fc20fc21bc40ff21fc40fd42fd30ff10fe43fe30fc32fd31ff40fd32bf42fd21ff30fc43fe31fe32fe42fc10ff31fd40ff41fd10ff43fc41fe21fe10fe41fd20fc31fc30fc42ff20ff32fd41bd42be40ff42fe40fe20
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x843bf42c87bca6107dcc410bfa92877c53082fca610df94c41bf290617f504c6faa2105fd5032bea8065f5310c6fca321efd0820bea80873e50d0b7e85215f94d20be29021fa40103e8a2905f54243dfa12617e530837e84a077cca32bf29661fa300c3de41107dc8610bea9021bf50d0a78a8905f54e42df298817f544caf8a8986f10c41bf29621bf4010378a2a16f10110f7a12853d54c82fea7087d0c610be2a421bd424877aa2207b88620bfaa463bc544437ca9985f94442de18c81bc40842f8a610df94821deaa6437e530c77aa9906fc8640ee29a217f54c83b864186fd5120bba8a87fb409037ca8106f90640beaa041bd42043f660985f94441bea98417f520437e65205f54221bfa9e21f621087bc65186fd0a32bf29c41ef320837aa3204f55031de2a241bd32102fca018f74ca31bf284657d54c877a86a16f55021f7102417d518c3bc60985fd4d42bea96877c540c6fca0186f10310efa1c877e51882f8a710ef50931b7a9221bd539037a8410df54f41bfaa4417e52d03ee6298df94630bf28e657d53c86f8a9986f90230bf280813f54482fca9104f95310bf29087bd42102d8a4985f54b41dfa9481bd420cb7884205f94e10bf29c43bc544c7be64985d14530ee99065af5250b7c62205fd5332bf298657c540cafaa720df54f40fba8a616f524c2faa7205f15121bea8643dc318c3ee63087bd0a42dfa1881bf41906faa910ef10220f7994657c54083dc42105f54830bea8483ba50102faa1197790c43de206617d54882fea6a0efd5131bea94613c544c2f8a0995f55210dfa1483f621442fca3905f95331df98c817d53d0afca3196f50910bf2a083fb308c3be86a1dfd4542ef98863bd420c37e8220dfd4f20dfaa2213d54c86faa8085f94641be2a641be41506fea8084f55020df28c81df320c77e832057d4d10baa8c657f53087eea2a1df95042dfa1461f521087eaa2107b48020bf28843be219037a85a05f94b41dea18877e5010efea9195f14d21f7900417f5148378a3206fd0a40f6990657e52843e8a2a1df55241fb10e217c530437883205f94c42dea0c81f7318c6fca7a17b08620bea90817e540437a85087d08410dfa1665bd428c7baa790dd14543df206417e5310ef8a7086f50932beaa261d5310c6faa1215f54a20bf29e417e52102f8a4886fd4d42bfa9a413f5488378a6a16f94542dea9e85bf42cc77c8720cf940409f2a085de314c6fca810778c430bf29a43bc400837ea6205f94820df210817d50d0b7a80206fd0b41df2a643bd42c42fca1995f55032bf2a0657f540837c80905f14520bea9883be51102fca5185fd4b10bea8e417d52cc2f8a918f7cc030de21881ec32883f220085f15221bf296877c54c437e86a15f94a43dea10857f5050778a2207d48510dfa1283bc52902eca2106fd0a21
  | 1 => 0xf54086fea6085fd4132bfa9281bd428cb7aa91957d4d20de29081fb104437e81206f10440df20221bf31102fea8185fd5221dea12617e5190bee8218df94010be2a061fb10842faa010fb908429f2a0437c52843bc64995b14910ee19461df53482faa9995f94b31dfa0881f741906faa6905d54420ee988637d511037c81085f54843df10881dd324c2fea890df15131bea9c657d540c37c81886fd0832bea8887f431887dc4290efd0840df18c81bc53103bca790fdc8621bf2a641f710843bc63185f94410bea84637d52d037e84185f14d42de994817f524c2f8a9997b14930be28283f641106b8a6a0df15220bf28083bd41102faa9215714d20dfa12637d53c42fca818ef50a41bf28065bd521037a8418df94a42ef99065bd42c86fca2105f152329f284813f544c2fca518fdd0731df28e857c524c6fca4196f94840bf2a241bf42442fca218f714d20bfaa221be40cc37ca818f74c831dfa1063bf42842faa1a0df94341bfa9e437e548ca78a8886f10320bf2a087be40882faa7105f54d10de20241f940102fca0106f50a21ae29a217f544c6f8a4a05f94740be29e437e530c37a85186fd5220fa18a437f53486faa9986fd0e40df282857c50486fca8885f94e41beaa243bf42c42f8a0a15fd4910dea1481fb40503ee6310df54e30dfa1265f441cc6faa9885f54432f7992657c548c2f8a4986f90c40bf28e61be4350b7aa8195fd5031bea9885f7214877a85996f14f42bfa9c41bc43906fca0216f4c440df2a6417e54ccaf8a4a0df14540bfa8a613c5050bbe8618ef55020beaa465be5350afea710f7ccb30bf29c857d5010b7a8598ef50841fba0a83bd211037e87a0fd50441bfa94217e50d0b7ca810fdc8410bea8e617d548c2fca221efd0f42dfa8c817c53c427ca9905f94831de10881bf428c6f8a990dfd5330be29287bd42d06faa3a15f54732bea8c857d50107de65106fd0a20fa188217e5090eeca3195f55320ef99463bc40042fca1106f50c40bea9083bf42cc3dea4987d14530de2a261bf5250af8a8905f94842bfaa4215e53c877887206fd0d41fc98061df308c3eaa3194f55021df20041bc50d0afaa8905f14e20dea12837d52842fca6884fd5110df214817c53502eea2905f94e43bf28643bd540c6faa9204f952329faa2637f54c42fea2a077cc631bf28881bf52102f8a8085f551329e2a441ec524427aa9217d94420f690843be40502fca7205f54a43bea8687f751482fca910cf55330bf29483bd53103ee6290df94242bfaa241dc430c6fca7885f54c10dea1241bd51d0afca8995f54b10df286857d518837c65206f94e40bea9a43bd42c82fea6885f54b31fd10041fb20482f8a7906f10f42eea9841bc400c27aa9885f54640ba28a41bc32102fca9885f54332beaa063be404c2fca110efd4f42bea9
  | 2 => 0x5401e1b94000000b483024016010180500001800003200105a080000000000000000000004200008010020901602000020200ab200600c050000283c0800204834000055200a3c00008882020080c01e03012000000880401800b480200800018101200e030060004a000220108a008480500c038000b800260000480a168460b1700000e011640780c01018248400711e010007380a000000f00a004020103c1b8000b03004000038002a006020020187601800010040a8140b18c00a8c008241881c202da1100027816270220080c2800202844108000008c2044c02800138600980c000360002a0000a07000378060f8ee2981c0e8044884400004008220114e0180217804048060d800050000400e0280c000010983a043d20384e010029db2a000080e80003804098640380001004198127a00861144e600e0b800298020b0003d052000002b394000060089c0000a0182c0049c0302e0a83c2e8068681a058140200003036010003200a10022115f14542eea18877d53c82fca990ef55310dfa1083ef218877880986f90e40dea08835d530837ca7a15f14d41beaa4637e50cc6fca9985f55131bea9443be32102fca9085fd4543bf284635e53082f8a6907ec8220bea9c21bd4288378a9106fd5130dea16617d51d0efaa5207e84010bf2a461f510042fea0a15f95131bf28e87ec210837ea2a16f55330dea8a85bd219037ea0a14f55232df2a065df53506fca1085f94432bea9483bc5050afea4a0f74cb30be2a0437e540877aa5206f54342dfa1241ef52442faa718efd0b209ea90817d500c6fea6105f95231fa90e217e50907b8a6a0df54442ee21c637e518c678a898cf95031beaa2217c53442fca7a0df55243de10c8177514c37c80087d10431df21883f4218437ea7207d8c431bf2a243bf51102f8a2a1f7d0e31f6190417e518877e42205fd5230dea1c813e540837c87a15f54430dfa1681f710042faa710d7d4d41dea1281bc31102fca420df94f40bea92217d54086faa198df94021bea8e817f514ca7ca8196f10a40be2a6637c52c42fca1a1fb8c832be2a265be41102fca1206f14742dfa12437c504c6faa518d754f21bfa9263be54c43da84215f14530bea9881bd42083f240106f90942dfa10857e5190378a720778c8309f2a643bd5050afca5194f55032bf2a261bf4390f7e8621df14532beaa663f6518cb7a87a0df94c40de21a857f53502faa418ef10230df99081dd300c37865204f95330bf2a0817e52442fea990efd08109ea94817f504877ca5205f94230df280817e51d0afea8985f94810bf288617e540c3bea6886f95232be2a221bd43d0afaa3195fd5331bea8c87be4350fec20886f4c640be282877e53c877c8018770c430dfa1043ef21086fca5205fd4143bea8c21bf51d0b7aa6a15f94c10dea1a837
  | 3 => 0xc0085800018cb8a2018d4000000584e1c80c00000034400208e018023d02a0005c
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x5424427661d5020ab58b53d0ab661d4342e54c4311023d65950208f590534872f5250930aed815350a9f63545429b58a53443365110020a7d8d5050a3e65d09108f59421102ad62144408f195424c71f5394e40cb590524c2b46154142c795153c863d6550831c794e400826f6550842cd544400833542145209d587530823f6590020cb14a404423e6414c21aed815150a7565c84108f593504872e6414910cb54b42d023f64542318fd95411063d6550b10c794f42c863c6055021d554c318865c6354910ae983529031f53101208f99252cc2ba6014e408f19150c863e64948328f99743506b66114a40c7d4d425072d5250a318f58a540c63f6454331ea101200825e6394910b5185300c23e60d51318f99353c425d6510c31cd153314c67860551329758e520871d5350820b5d95310c63e60950319b189500c6786055121c7d4f424431d5494f219d997314873751101308f191534872c54149109dd8553d0a5e6395110cb9514210a7661951309b588530423f6454221d9148514c23e65901308f592528c63d64d41318f18154c871e53100208f59353c875453885108f596540866e6295110cdd0a518ca3f65508219758f54082ba60d0a20cb94942cc69d63c8640ad185425063e6494c30cbd50524425d63d53219b58a544432c5210110ae98053102ba60d44408f59721102b5618c840ad18543d0ab46150d418f597219023e6494a31d594e510823e64d41319bd95210863e64946208f592520caba6014a40cdd53514c23e6494e20c714f425071d5454c20d594d510823e6095321cd509510829e63d43429718d500869f6350640d958452443345414530cd50a51082b5618ca409798f548425e65cc9308f990540c6b56114c40a758c52903365494632ae980521025f63546209718d54483645188120cd945419023d64948208f59632102b86050b308f191530432f52d09108fd91534863d64944108f993530863d658ca40c7d4d424834f53d49108fd9542cc2776154d208fd953190395424c431add85431027b6550040ae18142c423f65d0b30cb14b424c32d52c8440b5986320c23d6414930ab58a5350b1e5350820b598f214873a60d52209758c528429e63d4640c7d50534823e6414810cd551510825e6315010a758f211023f6550b10cb588548823d650c840c754c43d0a7561d50209ed95300c2756195130ae983521023c6454232cd552510823c65509308f992520433542d45309bd89544c25d63d4b108f59353c423d6494e10ae181424823e6414532c754c5350a3c6454e208fd9150ccab56114840cb590524423d6510020d514f514823e6494a109798f540825d63949108f99053c863e6494b108f994544c72c52509108f590538863d6494910d354f320832d5250a408fd9742c423f6454d10cb54b42d06bb6048440
  | 1 => 0x825f6354440b5986328c23d6494a10cb54942042d563104318f992510427661d523097d8d51d0a3f65508329798c540833454d452097d95310c71c5350d419758e52c434c524c930cb54b421071c5414d108f995424c23c64540219d594210425f6355120ad18543d063e6414931a7191310c6b46150d428f980544429c63544408f590514ca3e64149108fd95311025d6315010d554c310426e6295130e5191310c63e64951209ed81544863f6454620cbd49424425e63d53219ed95200833454145208f59252c431f5414d10d554c314863e6414a10ab588400823e65509108fd9151ccab76154f428f593530832f5290130cd153514c2746154d20cb149424c25d6594c20c714c40442b661d4e408f994211026f6254d10cdd44404823d65950318f59432902746154032cd146404823e64951108fd95420823d6414f10c7d5353482b8604c840cb54a321023d62d51309718d51883374254632d5d95310c72d524844097d95300c23c6055232c754c53d0ad663c86218f597420ca3e60950218f59052c435732946328f99353c82b66114c40cb549321023d65d0b10d5d4f514832f64d4930ae98353902ae62144409b588548c6ad6214f42c754e400827661d4f208fd91500863f64549108f18054442756194b308f59431102746154e208f996321025e6315221d3949328c63c6055031d9149214432f5210130b5584430c63f65500408f99353c876551884209718d51d0a3c65d09109b588540427661148108f99053c82d5638c431a7d8d51102746548510cd552518ca3d62d5131cd951518ca5e6514d209d984530823e65151309ed81534869e6314840cb949428c63d64d4c218f990540cab761541428f997424c73451101209ed81544cb1c53d0d418f59742cc357530c6109bd89544431d5454f218fd95420c63d64948318f994404c23e65c8640cbd49425023c64544308f197424c69d63144408f592518823e6095032cbd53524c23d65950328f592520423d64148108f990530831c5350910d314b324c23d64149108fd91508cb4c5314910cd946400833551900208f59252cc23d6508640cd50b51482ae6214c40ae983519035453841108f993538423f6550c438f181540cae461480209dd95411071d5310020e510c410c75553944208fd954210aad62902209dd85534435753145208f992534823e65101209798c530823f62553108f996329031f5390120cdd08514c23f65100208f191534823c64543319d5865448395310c640d554d510826e62949109758c548865c63551108f990534866f62540319e980530873751901308f592520c2b86050a209d584540c23e6590110c714f42482756115332add8543d0a3d6255020c7153534836752d4530b518d10042756114c20cd553410c795544c431ab58840882d4604c4318f19
  | 2 => 0x54d4520ad587421063d6550b309bd95200823c6454332cd952510831f53901109b988530429f6354742cd54441102796014c21a718d5050b3654544208f5905308694644c431e3509320ca9c63547428f592534433754145309758c54c871c54d4d109b98b53c42b860484408f99252cc63d6494b318f195311023d6494630ad986329031d53d08208f990524c32c54d4910c7152314c63c654c640c754f42c866e6514910cb549420c23d64948219758f548426f654c8329d185544cb2e52508308f992544c6cc6348020cdd465190397644c4319798e52c426d650c8209d98652cc29e63c84408f191508c63e6414c108f590530826c62551108f592528c3545348510c795253082b46150e408fd91530423f6454d208f58a54cc26e62152319d98454cca7661951208f58a54c42ad6214c40cb54942cc63d65d0831c7553430c63f6454321c7d53534426d6215331cbd4a404431f53101108f19542483355454632a798c51d0a776154c40cbd93524435532145308f59352c42b661148408f992520c71c53509208f997424839743d04318f99431902b6618c8409d586534831c6355031cd185540c66e6294d10c714d4350b35511444097d8d544872c52901308f99052c433742544208f590530423e65d09309dd95100423e6495130cd508514c27461551308f997425023c65d0930cd90c5150f1f53d09209758e54442b76154d42cb153524c31d5314c409758c54082746154f428f594319025d658c830b5d89310c74c6254c208fd91500ca3d65d0821d5146304c397424c431a718d411023e64d4c208f980544c72c64d49309718d51102b76150d42ead09200832c52101308f99440442d46350441ad185431029f6350440b998b314863d6590c418f992520823f64540319798e534432f54d49108fd89540c6746155120d3d4c52442786054d219d587548c2b46154c408fd97420c63d6215110cdd0b514c2d46150c43d514f415063e6494821c714d42506d663c86108f596421031e5350b218fd91510c32f5210110a758c51d0a5f63551319dd85524431c5390541cdd5051483375190120ce98250102ba60d4c40b5991310c69d6314840c794f42082d4644c4318f992528c32c64d49108f59053c863d62151308f191534423d62d51108f588544c72d52d08408f992518c32e5250810cb14b42442b56114f428f994311023d6414a108f99432902d6618c932c7d4d424431e5350e409d984540c2b561d4e408f59253483573214530a718d5150a6e6215010c714e40442776155120a718d41106b46154d42cd50a518ca7965840109bd89534823e6508640cbd50524c36452d4530d314a304c2d663c84109b988540c23d6494e208f992524423e6414f108f994544425d6395120add85531027765484218f993504cb4c5388120ab58a400
  | 3 => 0x200d0184a0000503c000085b02c0600006000190680d0346a0400400405018780200100804208000bc09004291900109c5a01c05114400140a00c0100c0200c0095813000042400700e98012be0781e0f00e120170000607002000420002a1440500000000000440101800040a70041001c230001105c0026001014100280006c010040500028020090100808c201a4085040002c01004050a0561302f0180401c0f025101880000095024616603506400001bc0100a09000014060000900400014290080200063000df0011700095000050040604c0c328030501974c0f1e40700010004e0000000100b0040f144430000009aaa000080441300c0f00004020070100703c03004010793001c16004010880004c00098000000d00410000012182501c0002000028130140006c0101107000036ac00010d50040e0680702c000040e004010100a0002b008526340f004000141f0ac180f4000785b000010001e0481f0100b06808018d70008d00c00018b20a400000080901778c00060011bc090026d62951309758c520436452841109b58b53c425e6314a10d5d0c5150e75650c410ae1815350a3e6415020ae980519023d6494c30cdd0b514829e6314a40aed8132102b56114a40b3189300c23f6454e219dd85544cb1e5494f219b189544c31d5310c409d984548cb1f53d0941ad191310c65e6394d209dd85544c72e64149308f191500c72f52d0930d514c514823f6454e209798f52c425f6354910ad18553d0a766194d20d9d48514c31d5350b21cbd49425063e6550931e9509210871c53d09109d584548ca7561150208f992520c2af6254d42c755253082756510431b91891004355510c4309dd85544c3345190130cb58b548825e6395120add85439023e6494e108f982548ca3c64549108f593538423d65d08209dd85500caba60d09208f994544823d65900208fd89540825e63948219798c52042b46150c438f99352c431c53901209d987530829e6314440ce980548832c5414930a718d419025e63153218f992534427561d5232cdd0a51082b66114f42ad58750d0b1e5454c209b588540c396544c431b5587320c66e62153318f191500ca6c6254d109d987530869d63d46408f996404831c53101208f191538871c5414d20d314f5244277654c4319d185531025e6514d10d914a21442776154e209718d54486b860545429d98454083345110130a798f219027661d52329ed95100423d6414f20ae181420c23e65c84408f994321033551147429d58753c825f63551108f19151ccb355114542cd509518ca5f6550c438f191518823d6414931cb549429063d64d41329d996214429d63d434297d8d500873742145208f990540863e64d41218f59353c823e6414e21ae18142042ba601444097d95320ca3c64542218fd8954cc337
  | 4 => 0x1fc020d0880080b00c730481d0d40e01000000000fcde03c210000f0852d0000005000
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x70244900008002b0073532484015c014020a00010104201ea28e6a88a3a1615535845310314a90c0a1061451cd5114542a28e8a98620849476509310c64b3a4c8988638518c6155031c1aa6b1080106156354451d0b443188090041459d3530c610d40c2202401061463945419030ab1aa2288810b5c8654c440a2ce7a8ca32061853181424828a39aa220881895895114440c28a630a84a0d30705085148312b12a220041451c55314d42c52c5306a91049670191310c64a39ac3a1083251da544c431a2eea98863206155358453d0b06a9ac429881251d9544c431a30e0a98a6a151575d09310c698382a228a85451c55314c40a2ce3a9ca7205147154c43d0a4ab90c89886389549618c840a28e6a88a2205147154c53d0b0ab2a62188810e1c16550831a28e8a986290c9474587320c68a38aa6218818514c6150d42c2ca630a8720514754c43110306b1aa590881451d1510c430c52a4302840849476d09310c6a8382a618a43451d1530c621
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x4181487595310c440905821d5310c440a048154d6214c40885821da544c431c04735895114440814865d7424c431
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 801
  | 4 => 781
  | 3 => 56
  | 2 => 6
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
  | 6 => 2*((h/28+packedAt s4K6 (704+(h % 28)*6) 6) % 44)
  | 5 => 2*((h/323+packedAt s4K5 (21627+(h % 323)*10) 10) % 801)
  | 4 => 2*((h/337+packedAt s4K4 (29678+(h % 337)*10) 10) % 781)
  | 3 => 2*((h/32+packedAt s4K3 (2744+(h % 32)*6) 6) % 56)
  | 2 => 2*((h/9+packedAt s4K2 (360+(h % 9)*3) 3) % 6)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffffff81ffffffe07ffffffff81ffffc7ff1ff
  | 1 => 0xf80ffffe03ffe0ff83f07c1fffe1fe03a27e7c
  | 2 => 0xfff03ffffc0ffffffc007fe0fffe1fffc38f8f
  | 3 => 0x3ffffff000ffffff8000ffffe003fc0ff0
  | 5 => 0xffffc000000000ffffffffff00000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x8a1008c4882400014b09421280222a80cb0b5
  | 1 => 0x926299143924896581542d1a5b215419a2565c
  | 2 => 0x2144aa20906918aaa8084b4895541952c30b0a
  | 3 => 0x858b34492241d2d34e6d0210e6998063740de0
  | 5 => 0xc60c3871c38e1cfc738e739c07111183fbe000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xeaa8eaa8e8a0e8a0eaa8eaa8e8a0e8a0eaa8eaa8e8a0e8a0eaa8eaa8e8a0e8a0eaa8eaa8e8a0e8a0eaa8eaa8e8a0e8a0eaa8eaa8e8a0e8a0eaa8eaa8e8a0e8a0, s4N, s4R, (fun _ _ => 0), s4I, []⟩
end PEqualNP.Outside.L_meta_37465
namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x58c1570cf2875000131d5001280141fe10fc42fd41ff40fd32fe42bd40fc41fd20fe41bc41fe40fd10fc30fe30bf40fd30ff21fc20ff43fd40fc31fe21de31ff10fc32ff30ff41be41fc10ff20fc43fe31fc21fd43ff42fc40fd21ff31ff32fd42dc31fe43fd31fe32fe20
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x30c006823c106000e0010100400011a08100000000606002001b6c0000c3c100060c92128153800000a010000001279e418c6eaa3185e14121ae29a2178504ca7aa9206e54041aea9c2176510827aa8184f950109f28e819c31502baa6216790431ce20c6375510827ca220cf553319e2a2435e53d06d8a4884f55010bca8083d431c86b8a690ee50020ea18e21b651107288218d794c209eaa4615e53842baa6105794c429ea84837950d0a7ca320cf55220ce20863d431443688398dd94630da208633e54cc774a020d7d4d41af28863745150e7ca9186e503209eaa4213f54c43aca218cf15310b7a92213d540827aa990dd14532cf18e815f53442bea690d794f21bd286853c515027ea899670c7409f2a0813e540c27aa8195794631bda8243d7410c6eea2995754f21dda82813c544c67ea890d714d419ea80833c544427ca9104f95321ea208635d53d073c62a04e540419e2a2653e54082eea2a1ee50210ea18843b9404427ca9085ed41329f2a0653f544c67ea8885e94041
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x6000020000002000010023000c08180000b44520c510ca1494044316540c721c515031c42956010431a5986410c6396095321a6580410c6d16010431a4580410c714540c510951855310b926010431e40c540442b16010731a6580418c6b160104318e19540443916010431c514431503315150020
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x2400700520c54044288b84a818e43841943150110
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 99
  | 3 => 21
  | 2 => 3
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
  | 6 => 2*((h/1+packedAt s5K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/22+packedAt s5K5 (736+(h % 22)*6) 6) % 46)
  | 4 => 2*((h/54+packedAt s5K4 (2673+(h % 54)*7) 7) % 99)
  | 3 => 2*((h/28+packedAt s5K3 (798+(h % 28)*5) 5) % 21)
  | 2 => 2*((h/8+packedAt s5K2 (147+(h % 8)*2) 2) % 3)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xc0fffc0fffffff81ffc0f83ff87ffffde231ff
  | 1 => 0xff01fff01fff03fe0fffffc0ff83fe027fce7c
  | 2 => 0xffffffffe07ffffff000fffffffc1fff83ff8f
  | 3 => 0x1ffffff8003ffffff0000ffffe003fc0ff0
  | 4 => 0xfffe0000000003ffffffffff00000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x5214c4624412618052d82a19282732a8e210b5
  | 1 => 0x864c48a1c924249605495a48588154182ec65c
  | 2 => 0x82911048348822aa02094a295480953016b0a
  | 3 => 0x2cb1a249120ecb4d39b20430e6728063d40de0
  | 4 => 0x30c1c38e1c70f3f1ce3ce73c04631183fbb000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xece0e8a0ece0e8a0ece0e8a0ece0e8a0ece0e8a0ece0e8a0ece0e8a0ece0e8a0ece0e8a0ece0e8a0ece0e8a0ece0e8a0ece0e8a0ece0e8a0ece0e8a0ece0e8a0, s5N, s5R, (fun _ _ => 0), s5I, []⟩
end PEqualNP.Outside.L_meta_37465
namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
def q1K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q1K3 : Nat → Nat
  | 0 => 0x6023d085f31da43e442e98ef21
  | _ => 0
def q1K2 : Nat → Nat
  | 0 => 0x344c510c531487848510
  | _ => 0
def q1N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
  | _ => 0
def q1R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q1K4 (i*4) 4
  | 3 => packedAt q1K3 (i*15) 15
  | 2 => packedAt q1K2 (i*26) 26
  | _ => 0
def q1I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q1K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/9+packedAt q1K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/1+packedAt q1K2 (78+(h % 1)*2) 2) % 3)
  | _ => 0
def q1Pos : Nat → Bits
  | 1 => 0xbea673b7606e
  | 2 => 0xffffffffffffffffffffffffffff3bbc3bbc93
  | 3 => 0xdfc3cfc3c31c
  | 5 => 0xeffc0ffc03e0
  | _ => 0
def q1Neg : Nat → Bits
  | 1 => 0x424880910426
  | 2 => 0x0
  | 3 => 0x241415020918
  | 5 => 0x18016a2012c0
  | _ => 0
def q1Atlas : Atlas := ⟨4,rawDecor 46 q1Pos q1Neg, 0xfffcfffcfcf0fcf0fffcfffcfcf0fcf0fffcfffcfcf0fcf0fffcfffcfcf0fcf0fffcfffcfcf0fcf0fffcfffcfcf0fcf0fffcfffcfcf0fcf0fffcfffcfcf0fcf0, q1N, q1R, (fun _ _ => 0), q1I, []⟩
end PEqualNP.Outside.L_meta_37465
namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
def q2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def q2K5 : Nat → Nat
  | 0 => 0x1010007aa14014058700100910008300400010500000efc10fc20dd30bd41ff20df30bc40ff31ff42fe42bf42ff41fe43fc32fc42fe21fd21fc30fd42be40fd40fd43fe20fc40fd41fd30ff30fe30fd20fe10ff43fc43fd31fe31bf41fe41ff10fd10ff21ff40fc41fc31fd32fe32fe40bd42fc21ff32
  | _ => 0
def q2K4 : Nat → Nat
  | 0 => 0x10a031b05000501000000003229023a010204001f003202000200131509046503000006000001001631010921830100012200000600000405003b000a0005140200000000040000000004000203000000400052001a069f2a2435e530867aa98867d0530af298813e5408278a8885b94840cea0a61ad424836ca2204f953109faa2619d54cc278a9084f950219f280813e54886f2a010d754e20b7290213f54483b261085b548409eaa4839f42cc2f4a018eb50b209e2a4413551102f2a0195794c30ce202613d540ca7ea9104f95042cf20661b5414427aa810d754c20af298413f525067aa3a14f14141aea9c21d9308825aa42076d4130ec982213c5050b3a84984f55020bb28881b8408c27aa5204f54b41d7a92853d54c867ea8886b54840ec20261d9304833aa6204f95041af298215d53042f2a018cf953219ea8c819f544c27ea2a179484219ea90819e404c2bea690e715130b7290633c544827ca1a176d0130ae29a43b5511033e83985d54432aea9c8175510836a83884fd5210aea9c619d53902bca7205e94243cea0e61ae521027ca818e794e409eaa02198404c27ca1205d944209f28683795090e7aa2204f55121cfa12613d548c67ca9984f95010ce206615d53086daa418d754c409f2a4653d548cb7080984f55242bd280653e548c67aa818de94021dba8a8376510cb3ca6204f953209f2a0659e54cc27aa9905b54810baa8881ba50102bca7085794e209eaa6613d548873a85984f15130
  | _ => 0
def q2K3 : Nat → Nat
  | 0 => 0x191c410600004006a0660cc0043401000000990020000c1000603064d848550086596014d218b588548422d621414187996404c3255254440e2588404c21e6510130a4584404c30d5354840c394d52102a962101308b19542483455348421ac584408c318544c210b2588404c3155354440c594d51102b16110130a6993504c389424c1208e18154486956110330c615130482346550510b4584404c31a65101308d5845050b255294440e4984404c28d6210330aa588408c2986050930c6151304428d6210130a6982404c391414c110a6181414c3265254440e2988404c29a6510130e4584404c2356115220a6584404c2956110130a6588404c2896210130a658e5010318544c220
  | _ => 0
def q2K2 : Nat → Nat
  | 0 => 0x20008000a1421d5424c120d02c53088098511711513088244b90c0a0a61425c8544c210d02c4b088098510755053044248b88c0a1261a09896110130
  | _ => 0
def q2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 136
  | 3 => 50
  | 2 => 9
  | _ => 0
def q2R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt q2K6 (i*5) 5
  | 5 => packedAt q2K5 (i*16) 16
  | 4 => packedAt q2K4 (i*27) 27
  | 3 => packedAt q2K3 (i*38) 38
  | 2 => packedAt q2K2 (i*49) 49
  | _ => 0
def q2I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt q2K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/30+packedAt q2K5 (768+(h % 30)*6) 6) % 48)
  | 4 => 2*((h/87+packedAt q2K4 (3672+(h % 87)*8) 8) % 136)
  | 3 => 2*((h/37+packedAt q2K3 (1900+(h % 37)*6) 6) % 50)
  | 2 => 2*((h/10+packedAt q2K2 (441+(h % 10)*4) 4) % 9)
  | _ => 0
def q2Pos : Nat → Bits
  | 0 => 0x1e3f9fffc1c71e3f1c71f1ffe3870e3f0cf90f
  | 2 => 0x1fc7e1e3fe07ffc7e07e3e383c07ffc73341f3
  | 3 => 0xe007fe03fff81ff8ff803fc03ff80ff8c38e3c
  | 4 => 0xfff80003ffffe000ffffc0003ffff000fc0fc0
  | 5 => 0xfffffffc00000000ffffffffc0000000fff000
  | _ => 0
def q2Neg : Nat → Bits
  | 0 => 0x428084404408244004104048a0912212041905
  | 2 => 0x84110804881208082022121104024484114052
  | 3 => 0x1220089108050014880248209200920428228
  | 4 => 0x488055522504049295548004b254a012ac0d80
  | 5 => 0x9134598039a69924fa6939270060c1a4fbe000
  | _ => 0
def q2Atlas : Atlas := ⟨6,rawDecor 61 q2Pos q2Neg, 0xfffafaaafff0faa0fffafaaafff0faa0fffafaaafff0faa0fffafaaafff0faa0fffafaaafff0faa0fffafaaafff0faa0fffafaaafff0faa0fffafaaafff0faa0, q2N, q2R, (fun _ _ => 0), q2I, []⟩
end PEqualNP.Outside.L_meta_37465
namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
def q5K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def q5K4 : Nat → Nat
  | 0 => 0x70000060000000000000400000000001de31dd32be40dc31dd30bc40bd41df30bf41bf42bd42df32
  | _ => 0
def q5K3 : Nat → Nat
  | 0 => 0x90800054d52cc31a84994b54b419aa88814d520c6b2a018cb54840
  | _ => 0
def q5N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 7
  | _ => 0
def q5R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt q5K5 (i*5) 5
  | 4 => packedAt q5K4 (i*16) 16
  | 3 => packedAt q5K3 (i*27) 27
  | _ => 0
def q5I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt q5K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/32+packedAt q5K4 (192+(h % 32)*4) 4) % 12)
  | 3 => 2*((h/9+packedAt q5K3 (189+(h % 9)*3) 3) % 7)
  | _ => 0
def q5Pos : Nat → Bits
  | 0 => 0xf8ffffc1fc3e1fe1fc3f0fffc3f8387f4cf70f
  | 1 => 0xff0787fe3fffe1fe1fc3f0e0fc3fff87b349f3
  | 2 => 0xfff807ffc03ffe3fe003ff00ffc03ff8c38e3c
  | 4 => 0x7ffffc0003ffffc0000ffffc000fc0fc0
  | 5 => 0xfffff8000000003fffffffff00000000fff000
  | _ => 0
def q5Neg : Nat → Bits
  | 0 => 0x8110044004420002404012240488812041305
  | 1 => 0x10400888101002040841104404121204114052
  | 2 => 0xa22255108aa9106ac222aa08aa812560c28c28
  | 4 => 0x86b566252a0d54b376a88812f3258132ec0f80
  | 5 => 0xc4c64439b331993d9b33cc9c22060644fbe000
  | _ => 0
def q5Atlas : Atlas := ⟨5,rawDecor 55 q5Pos q5Neg, 0xeeeeeaeaecece8e8eeeeeaeaecece8e8eeeeeaeaecece8e8eeeeeaeaecece8e8eeeeeaeaecece8e8eeeeeaeaecece8e8eeeeeaeaecece8e8eeeeeaeaecece8e8, q5N, q5R, (fun _ _ => 0), q5I, []⟩
end PEqualNP.Outside.L_meta_37465
namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
def q7K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def q7K5 : Nat → Nat
  | 0 => 0x54428000c00009208705910c09a3892c0ff10fd41fc21ff20fd40fe31fe32bf42fe30ff31fe43fc42fd32fd21fd31fc31ff32dd32fd30fc43ff40fc30fc40fc10bc40fd20fe10fe41df32fe42fd43fd10fd42fe40ff21fc20fc41fe21bd42fe20fc32ff41ff42ff43be40ff30
  | _ => 0
def q7K4 : Nat → Nat
  | 0 => 0x1001428f10c708810058077c00011002d34d6c9c0000400000002118110042040020106000c0070000001001c00e2d5e53c833e652057d4d10e699041bb5050abca790d794c42cfa12653d540ca7aa9214f152209f2a065af5250a7ca810cfd51109faa2413f544c79ea4994f953109f28481ba501027aa990cf151209f2a4655d538caf2a018de94031bca80435d53c873a64206350932b6a9661ce424cabca6194f943429f2a0853e54cc2baa7904f54840dc20221b84084370a0a14f95321cfa16656d5210e7aa9984f55232ae29a216e52cc27aa8105d94420d6a14653e540833a65205b54831bd28483cd424ca7ea8985d54420afa9a836e520c678a8985754c42cea1265785050abca6106e10020b6292213e5010270a0a1734ca20e6996433c5050adca421cf54a40aea9841ad424ca7ca818e7cc840e6992437950906bca610cf953209eaa0637a500867aa9884fd5220aea9c855e5390ab8a6a0cf151319eaa0435d53086dea4884f55320cea16657b5050a78a8886e10320
  | _ => 0
def q7K3 : Nat → Nat
  | 0 => 0x3002300000105e00024d6214d41e2d81424ca386055321e2181424cb453254420c354932102a86050a32a3181424cb0f544ca20cc54440082a86050932a618142ccac86050932e24c840082986050932c355132083285210110a3592424cb0d544cb21a2181424ca396510020
  | _ => 0
def q7K2 : Nat → Nat
  | 0 => 0x205087055132c8780992a220041825953210020
  | _ => 0
def q7N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 99
  | 3 => 21
  | 2 => 3
  | _ => 0
def q7R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt q7K6 (i*5) 5
  | 5 => packedAt q7K5 (i*16) 16
  | 4 => packedAt q7K4 (i*27) 27
  | 3 => packedAt q7K3 (i*38) 38
  | 2 => packedAt q7K2 (i*49) 49
  | _ => 0
def q7I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt q7K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/22+packedAt q7K5 (736+(h % 22)*6) 6) % 46)
  | 4 => 2*((h/54+packedAt q7K4 (2673+(h % 54)*7) 7) % 99)
  | 3 => 2*((h/14+packedAt q7K3 (798+(h % 14)*5) 5) % 21)
  | 2 => 2*((h/15+packedAt q7K2 (147+(h % 15)*2) 2) % 3)
  | _ => 0
def q7Pos : Nat → Bits
  | 0 => 0x7fff03ff0fc3e1ff87f87fe1fc0e0fd39f793
  | 1 => 0xf81fffc1ffffc3e0ff87f87fe1ffff02c679fc
  | 2 => 0xffe1fffe00ffffff0007ff8ffe00ffff078e1f
  | 3 => 0x1ffffff0003fffff8000fffff0003f80fe0
  | 5 => 0xfffe0000000003fffffffff000000003fff000
  | _ => 0
def q7Neg : Nat → Bits
  | 0 => 0x50c4118c41284005380980960246225818b391
  | 1 => 0x12402284804004404882882220924a084250b4
  | 2 => 0x210944102a9222aa04445509540894a3050c0a
  | 3 => 0xa5958921281aab339550440d992c0433a80f40
  | 5 => 0xc6190e39cce333dce6676641103018c3f7e000
  | _ => 0
def q7Atlas : Atlas := ⟨6,rawDecor 47 q7Pos q7Neg, 0xeee8eee8ece0ece0eee8eee8ece0ece0eee8eee8ece0ece0eee8eee8ece0ece0eee8eee8ece0ece0eee8eee8ece0ece0eee8eee8ece0ece0eee8eee8ece0ece0, q7N, q7R, (fun _ _ => 0), q7I, []⟩
end PEqualNP.Outside.L_meta_37465
namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
def q9K3 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def q9N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q9R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q9K3 (i*3) 3
  | _ => 0
def q9I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q9K3 (3+(h % 1)*1) 1) % 1)
  | _ => 0
def q9Pos : Nat → Bits
  | 2 => 0xffffffffffffffffffffffffffffffffffbecf
  | 3 => 0xffffffffffffffffffffffffffffffffffdf73
  | 4 => 0xefbc
  | _ => 0
def q9Neg : Nat → Bits
  | 2 => 0xffffffffffffffffffffffffffffffffff4205
  | 3 => 0x2412
  | 4 => 0x1828
  | _ => 0
def q9Atlas : Atlas := ⟨3,rawDecor 28 q9Pos q9Neg, 0xfff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000, q9N, q9R, (fun _ _ => 0), q9I, []⟩
end PEqualNP.Outside.L_meta_37465
namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
def q10K3 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def q10N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q10R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q10K3 (i*3) 3
  | _ => 0
def q10I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q10K3 (3+(h % 1)*1) 1) % 1)
  | _ => 0
def q10Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffbecf
  | 3 => 0xffffffffffffffffffffffffffffffffffdf73
  | 5 => 0xefbc
  | _ => 0
def q10Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffff4205
  | 3 => 0x2412
  | 5 => 0x1828
  | _ => 0
def q10Atlas : Atlas := ⟨3,rawDecor 42 q10Pos q10Neg, 0xffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00, q10N, q10R, (fun _ _ => 0), q10I, []⟩
end PEqualNP.Outside.L_meta_37465
namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
def q11K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q11K3 : Nat → Nat
  | 0 => 0x6023d085f31da43e442e98ef21
  | _ => 0
def q11K2 : Nat → Nat
  | 0 => 0x344c510c531487848510
  | _ => 0
def q11N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
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
  | 2 => 2*((h/1+packedAt q11K2 (78+(h % 1)*2) 2) % 3)
  | _ => 0
def q11Pos : Nat → Bits
  | 1 => 0xbea673b7606e
  | 2 => 0xffffffffffffffffffffffffffff3bbc3bbc93
  | 3 => 0xdfc3cfc3c31c
  | 5 => 0xeffc0ffc03e0
  | _ => 0
def q11Neg : Nat → Bits
  | 1 => 0x424880910426
  | 2 => 0x0
  | 3 => 0x241415020918
  | 5 => 0x18016a2012c0
  | _ => 0
def q11Atlas : Atlas := ⟨4,rawDecor 46 q11Pos q11Neg, 0xfffcfffcfcf0fcf0fffcfffcfcf0fcf0fffcfffcfcf0fcf0fffcfffcfcf0fcf0fffcfffcfcf0fcf0fffcfffcfcf0fcf0fffcfffcfcf0fcf0fffcfffcfcf0fcf0, q11N, q11R, (fun _ _ => 0), q11I, []⟩
end PEqualNP.Outside.L_meta_37465
namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
def q12K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q12K3 : Nat → Nat
  | 0 => 0x6023d085f31da43e442e98ef21
  | _ => 0
def q12K2 : Nat → Nat
  | 0 => 0x344c510c531487848510
  | _ => 0
def q12N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
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
  | 2 => 2*((h/1+packedAt q12K2 (78+(h % 1)*2) 2) % 3)
  | _ => 0
def q12Pos : Nat → Bits
  | 1 => 0xbea673b7606e
  | 2 => 0xffffffffffffffffffffffffffff3bbc3bbc93
  | 3 => 0xdfc3cfc3c31c
  | 5 => 0xeffc0ffc03e0
  | _ => 0
def q12Neg : Nat → Bits
  | 1 => 0x424880910426
  | 2 => 0x0
  | 3 => 0x241415020918
  | 5 => 0x18016a2012c0
  | _ => 0
def q12Atlas : Atlas := ⟨4,rawDecor 46 q12Pos q12Neg, 0xfffcfffcfcf0fcf0fffcfffcfcf0fcf0fffcfffcfcf0fcf0fffcfffcfcf0fcf0fffcfffcfcf0fcf0fffcfffcfcf0fcf0fffcfffcfcf0fcf0fffcfffcfcf0fcf0, q12N, q12R, (fun _ _ => 0), q12I, []⟩
end PEqualNP.Outside.L_meta_37465
namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
def q13K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q13K3 : Nat → Nat
  | 0 => 0x18000036105c30e82178c37107610
  | _ => 0
def q13K2 : Nat → Nat
  | 0 => 0x20003808010d03004320c020
  | _ => 0
def q13N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
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
  | 2 => 2*((h/8+packedAt q13K2 (78+(h % 8)*2) 2) % 3)
  | _ => 0
def q13Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffbf0fffc3fe3f
  | 3 => 0xffffffffffffffffffffffffffdff0fffc3fc7
  | 4 => 0xefff0fffc3f8
  | _ => 0
def q13Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffff012222c444db
  | 2 => 0xffffffffffffffffffffffffff42e44562aa2d
  | 3 => 0x244e89aa3346
  | 4 => 0x1888ee3323b0
  | _ => 0
def q13Atlas : Atlas := ⟨4,rawDecor 30 q13Pos q13Neg, 0xccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000, q13N, q13R, (fun _ _ => 0), q13I, []⟩
end PEqualNP.Outside.L_meta_37465
namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
def q14K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q14K3 : Nat → Nat
  | 0 => 0x18000036105c30e82178c37107610
  | _ => 0
def q14K2 : Nat → Nat
  | 0 => 0x20003808010d03004320c020
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
  | 3 => 2*((h/9+packedAt q14K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q14K2 (78+(h % 8)*2) 2) % 3)
  | _ => 0
def q14Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffbf0fffc3fe3f
  | 3 => 0xffffffffffffffffffffffffffdff0fffc3fc7
  | 4 => 0xefff0fffc3f8
  | _ => 0
def q14Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffff012222c444db
  | 2 => 0xffffffffffffffffffffffffff42e44562aa2d
  | 3 => 0x244e89aa3346
  | 4 => 0x1888ee3323b0
  | _ => 0
def q14Atlas : Atlas := ⟨4,rawDecor 30 q14Pos q14Neg, 0xccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000ccc0c000, q14N, q14R, (fun _ _ => 0), q14I, []⟩
end PEqualNP.Outside.L_meta_37465
namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
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
  | 3 => 0xffffffffffffffffffffffdff39fff1c3ffc9f
  | 4 => 0xebfc1f3fe03f8f1c
  | 5 => 0xf3ffe03fffc00fe0
  | _ => 0
def q15Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff4061010824892131
  | 3 => 0x2088281109124486
  | 4 => 0x1523506a42a52b18
  | 5 => 0xe0a1ab493064ec0
  | _ => 0
def q15Atlas : Atlas := ⟨3,rawDecor 57 q15Pos q15Neg, 0xffaaaaaaff00aa00ffaaaaaaff00aa00ffaaaaaaff00aa00ffaaaaaaff00aa00ffaaaaaaff00aa00ffaaaaaaff00aa00ffaaaaaaff00aa00ffaaaaaaff00aa00, q15N, q15R, (fun _ _ => 0), q15I, []⟩
end PEqualNP.Outside.L_meta_37465
namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
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
  | 0 => 0xffffffffffffffffffffffbfcffcf8fff873f3
  | 2 => 0xffffffffffffffffffffffdff39fff1c3ffc9f
  | 4 => 0xebfc1f3fe03f8f1c
  | 5 => 0xf3ffe03fffc00fe0
  | _ => 0
def q16Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff4061010824892131
  | 2 => 0x2088281109124486
  | 4 => 0x1523506a42a52b18
  | 5 => 0xe0a1ab493064ec0
  | _ => 0
def q16Atlas : Atlas := ⟨3,rawDecor 53 q16Pos q16Neg, 0xfafaaaaaf0f0a0a0fafaaaaaf0f0a0a0fafaaaaaf0f0a0a0fafaaaaaf0f0a0a0fafaaaaaf0f0a0a0fafaaaaaf0f0a0a0fafaaaaaf0f0a0a0fafaaaaaf0f0a0a0, q16N, q16R, (fun _ _ => 0), q16I, []⟩
end PEqualNP.Outside.L_meta_37465
namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
def q17K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q17K3 : Nat → Nat
  | 0 => 0x6500002f995d31b86174caf185f31
  | _ => 0
def q17K2 : Nat → Nat
  | 0 => 0x4048d420c25504308d42cc6550732
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
  | 2 => 0xffffffffffffffffffffffedf99f3f8e3f3d33
  | 3 => 0x76fe1fcff03fce3c
  | 5 => 0x78ffe00fffc00fc0
  | _ => 0
def q17Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa010010012080045
  | 2 => 0x1224284484922512
  | 3 => 0x941501921248a28
  | 5 => 0x7851aae4986af80
  | _ => 0
def q17Atlas : Atlas := ⟨4,rawDecor 45 q17Pos q17Neg, 0xfaaafaaafaa0faa0faaafaaafaa0faa0faaafaaafaa0faa0faaafaaafaa0faa0faaafaaafaa0faa0faaafaaafaa0faa0faaafaaafaa0faa0faaafaaafaa0faa0, q17N, q17R, (fun _ _ => 0), q17I, []⟩
end PEqualNP.Outside.L_meta_37465
namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
def q18K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q18K3 : Nat → Nat
  | 0 => 0x10025930f46174c3c985f30
  | _ => 0
def q18K2 : Nat → Nat
  | 0 => 0x2650e30
  | _ => 0
def q18N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
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
  | 3 => 2*((h/8+packedAt q18K3 (75+(h % 8)*3) 3) % 5)
  | 2 => 2*((h/1+packedAt q18K2 (26+(h % 1)*1) 1) % 1)
  | _ => 0
def q18Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffbbc933e39cef90f
  | 2 => 0xfffffffffffffffffffffffdff1fcfc1ff31f3
  | 3 => 0xeffe3f3fe0fce3c
  | 4 => 0xf3ffc03fff00fc0
  | _ => 0
def q18Neg : Nat → Bits
  | 0 => 0xfffffffffffffffffffffff44626420c62a905
  | 2 => 0x208401040840052
  | 3 => 0x110080490080228
  | 4 => 0xe202ab2520ad80
  | _ => 0
def q18Atlas : Atlas := ⟨4,rawDecor 29 q18Pos q18Neg, 0xfff0faa0fff0faa0fff0faa0fff0faa0fff0faa0fff0faa0fff0faa0fff0faa0fff0faa0fff0faa0fff0faa0fff0faa0fff0faa0fff0faa0fff0faa0fff0faa0, q18N, q18R, (fun _ _ => 0), q18I, []⟩
end PEqualNP.Outside.L_meta_37465
namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
def q19K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q19K3 : Nat → Nat
  | 0 => 0x300000000000004000402f985d30de41dc436907510
  | _ => 0
def q19K2 : Nat → Nat
  | 0 => 0x480344c110e12044324c120
  | _ => 0
def q19N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
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
  | 3 => 2*((h/30+packedAt q19K3 (90+(h % 30)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q19K2 (78+(h % 8)*2) 2) % 3)
  | _ => 0
def q19Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffffffeaef1b77c27
  | 2 => 0xbf333e3ba0da
  | 3 => 0xdfc3cfc3c31c
  | 4 => 0xeffc0ffc03e0
  | _ => 0
def q19Neg : Nat → Bits
  | 0 => 0x0
  | 2 => 0x42444211044a
  | 3 => 0x241814820914
  | 4 => 0x1801a92012a0
  | _ => 0
def q19Atlas : Atlas := ⟨4,rawDecor 29 q19Pos q19Neg, 0xfffafaaafffafaaafffafaaafffafaaafffafaaafffafaaafffafaaafffafaaafffafaaafffafaaafffafaaafffafaaafffafaaafffafaaafffafaaafffafaaa, q19N, q19R, (fun _ _ => 0), q19I, []⟩
end PEqualNP.Outside.L_meta_37465
namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
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
  | 1 => 0xffffffffffffffffffffffdff39fff1c3ffc9f
  | 4 => 0xebfc1f3fe03f8f1c
  | 5 => 0xf3ffe03fffc00fe0
  | _ => 0
def q20Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff4061010824892131
  | 1 => 0x2088281109124486
  | 4 => 0x1523506a42a52b18
  | 5 => 0xe0a1ab493064ec0
  | _ => 0
def q20Atlas : Atlas := ⟨3,rawDecor 51 q20Pos q20Neg, 0xeeeeaaaacccc8888eeeeaaaacccc8888eeeeaaaacccc8888eeeeaaaacccc8888eeeeaaaacccc8888eeeeaaaacccc8888eeeeaaaacccc8888eeeeaaaacccc8888, q20N, q20R, (fun _ _ => 0), q20I, []⟩
end PEqualNP.Outside.L_meta_37465
namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
def q21K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q21K3 : Nat → Nat
  | 0 => 0xc000003b085e30e82170c37106c20
  | _ => 0
def q21K2 : Nat → Nat
  | 0 => 0x3808010c83008340c010
  | _ => 0
def q21N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
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
  | 3 => 2*((h/9+packedAt q21K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q21K2 (78+(h % 8)*2) 2) % 3)
  | _ => 0
def q21Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0xffffffffffffffffffffffffffbf0fffc3fe3f
  | 3 => 0xffffffffffffffffffffffffffdff0fffc3fc7
  | 5 => 0xefff0fffc3f8
  | _ => 0
def q21Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffff012222c444db
  | 1 => 0xffffffffffffffffffffffffff42e44562aa2d
  | 3 => 0x244e89aa3346
  | 5 => 0x1888ee3323b0
  | _ => 0
def q21Atlas : Atlas := ⟨4,rawDecor 43 q21Pos q21Neg, 0xaa88aa8888008800aa88aa8888008800aa88aa8888008800aa88aa8888008800aa88aa8888008800aa88aa8888008800aa88aa8888008800aa88aa8888008800, q21N, q21R, (fun _ _ => 0), q21I, []⟩
end PEqualNP.Outside.L_meta_37465
namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
def q22K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q22K3 : Nat → Nat
  | 0 => 0x400001000007830b06178c2e187b30
  | _ => 0
def q22K2 : Nat → Nat
  | 0 => 0x2690230
  | _ => 0
def q22N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
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
  | 3 => 2*((h/15+packedAt q22K3 (75+(h % 15)*3) 3) % 5)
  | 2 => 2*((h/1+packedAt q22K2 (26+(h % 1)*1) 1) % 1)
  | _ => 0
def q22Pos : Nat → Bits
  | 0 => 0xbbc3ff3e3fe03fc
  | 1 => 0xfffffffffffffffffffffffdffc7fffc7ffc7f
  | 3 => 0xfffffffffffffffffffffffefff8ffff8fff8f
  | 5 => 0xf3fff03fff00ff0
  | _ => 0
def q22Neg : Nat → Bits
  | 0 => 0x4479224e09261bc
  | 1 => 0xfffffffffffffffffffffff208b0412424a455
  | 3 => 0x111068249094a8a
  | 5 => 0xe224eb92418f60
  | _ => 0
def q22Atlas : Atlas := ⟨4,rawDecor 43 q22Pos q22Neg, 0xee88ee88cc00cc00ee88ee88cc00cc00ee88ee88cc00cc00ee88ee88cc00cc00ee88ee88cc00cc00ee88ee88cc00cc00ee88ee88cc00cc00ee88ee88cc00cc00, q22N, q22R, (fun _ _ => 0), q22I, []⟩
end PEqualNP.Outside.L_meta_37465
namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
def q23K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q23K3 : Nat → Nat
  | 0 => 0x120000af195c32ba6170c6f18df30
  | _ => 0
def q23K2 : Nat → Nat
  | 0 => 0x40008c424c25906328e428c6510530
  | _ => 0
def q23N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
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
  | 3 => 2*((h/9+packedAt q23K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q23K2 (104+(h % 8)*2) 2) % 4)
  | _ => 0
def q23Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff3ffff1ffff1ff
  | 1 => 0xffffffffffffffffffffffedfc7f3fe3f0fe73
  | 3 => 0x76ff8fcffc7f0f9c
  | 4 => 0x78fff00fff800fe0
  | _ => 0
def q23Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa0180202049440a5
  | 1 => 0x122324452122a652
  | 3 => 0x9416819484a2b18
  | 4 => 0x78a4eae920ccde0
  | _ => 0
def q23Atlas : Atlas := ⟨4,rawDecor 27 q23Pos q23Neg, 0xee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88, q23N, q23R, (fun _ _ => 0), q23I, []⟩
end PEqualNP.Outside.L_meta_37465
namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
def q24K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q24K3 : Nat → Nat
  | 0 => 0x4d00002e995c30bc617ccae18de31
  | _ => 0
def q24K2 : Nat → Nat
  | 0 => 0x109a408c661013296418c2510532
  | _ => 0
def q24N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
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
  | 3 => 2*((h/9+packedAt q24K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q24K2 (104+(h % 8)*2) 2) % 4)
  | _ => 0
def q24Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffddf1ff3f1ff0f3f3
  | 1 => 0x6efe3fcfe3ff0cfc
  | 2 => 0xfffffffffffffffffffffff7ffcffffc7fff1f
  | 5 => 0x78fff00fff800fe0
  | _ => 0
def q24Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa21c824304926171
  | 1 => 0x11258415212624b4
  | 2 => 0x840280848488a0a
  | 5 => 0x7892eae920ccfc0
  | _ => 0
def q24Atlas : Atlas := ⟨4,rawDecor 39 q24Pos q24Neg, 0xe8e8e8e8e0e0e0e0e8e8e8e8e0e0e0e0e8e8e8e8e0e0e0e0e8e8e8e8e0e0e0e0e8e8e8e8e0e0e0e0e8e8e8e8e0e0e0e0e8e8e8e8e0e0e0e0e8e8e8e8e0e0e0e0, q24N, q24R, (fun _ _ => 0), q24I, []⟩
end PEqualNP.Outside.L_meta_37465
namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
def q25K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q25K3 : Nat → Nat
  | 0 => 0x86000ae98dc30be657cc6e995e30
  | _ => 0
def q25K2 : Nat → Nat
  | 0 => 0x200009541cca350b3195410c2350830
  | _ => 0
def q25N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def q25R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q25K4 (i*4) 4
  | 3 => packedAt q25K3 (i*15) 15
  | 2 => packedAt q25K2 (i*26) 26
  | _ => 0
def q25I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q25K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/9+packedAt q25K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/15+packedAt q25K2 (104+(h % 15)*2) 2) % 4)
  | _ => 0
def q25Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff7fcfc7ff8f3cf
  | 1 => 0xffffffffffffffffffffffedf99f3f8e3f3d33
  | 2 => 0x76fe1fcff03fce3c
  | 5 => 0x78ffe00fffc00fc0
  | _ => 0
def q25Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa010010012080045
  | 1 => 0x1224284484922512
  | 2 => 0x941501921248a28
  | 5 => 0x7851aae4986af80
  | _ => 0
def q25Atlas : Atlas := ⟨4,rawDecor 39 q25Pos q25Neg, 0xeaeaeaeae8e8e8e8eaeaeaeae8e8e8e8eaeaeaeae8e8e8e8eaeaeaeae8e8e8e8eaeaeaeae8e8e8e8eaeaeaeae8e8e8e8eaeaeaeae8e8e8e8eaeaeaeae8e8e8e8, q25N, q25R, (fun _ _ => 0), q25I, []⟩
end PEqualNP.Outside.L_meta_37465
namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
def q26K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q26K3 : Nat → Nat
  | 0 => 0x14200000004002f195c31b86578c6f985d30
  | _ => 0
def q26K2 : Nat → Nat
  | 0 => 0x200c8c424c25906328e428c6510530
  | _ => 0
def q26N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def q26R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q26K4 (i*4) 4
  | 3 => packedAt q26K3 (i*15) 15
  | 2 => packedAt q26K2 (i*26) 26
  | _ => 0
def q26I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q26K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/23+packedAt q26K3 (90+(h % 23)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q26K2 (104+(h % 8)*2) 2) % 4)
  | _ => 0
def q26Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff3ffff1ffff1ff
  | 1 => 0xffffffffffffffffffffffedfc7f3fe3f0fe73
  | 2 => 0x76ff8fcffc7f0f9c
  | 4 => 0x78fff00fff800fe0
  | _ => 0
def q26Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa0180202049440a5
  | 1 => 0x122324452122a652
  | 2 => 0x9416819484a2b18
  | 4 => 0x78a4eae920ccde0
  | _ => 0
def q26Atlas : Atlas := ⟨4,rawDecor 23 q26Pos q26Neg, 0xe8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8, q26N, q26R, (fun _ _ => 0), q26I, []⟩
end PEqualNP.Outside.L_meta_37465
namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
def q27K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q27K3 : Nat → Nat
  | 0 => 0x140a2f985d30be6578c6e18dd32
  | _ => 0
def q27K2 : Nat → Nat
  | 0 => 0x8000008d42cc235083199400c6650332
  | _ => 0
def q27N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def q27R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q27K4 (i*4) 4
  | 3 => packedAt q27K3 (i*15) 15
  | 2 => packedAt q27K2 (i*26) 26
  | _ => 0
def q27I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q27K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/9+packedAt q27K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/15+packedAt q27K2 (104+(h % 15)*2) 2) % 4)
  | _ => 0
def q27Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffddf39cfc7e39f70f
  | 1 => 0xffffffffffffffffffffffeffdff3f8ffe39f3
  | 2 => 0x76fe1fcff03fce3c
  | 4 => 0x78ffe00fffc00fc0
  | _ => 0
def q27Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa21829041288a305
  | 1 => 0x1020004084100052
  | 2 => 0x941501921250c28
  | 4 => 0x7891aae4985af80
  | _ => 0
def q27Atlas : Atlas := ⟨4,rawDecor 23 q27Pos q27Neg, 0xecece8e8ecece8e8ecece8e8ecece8e8ecece8e8ecece8e8ecece8e8ecece8e8ecece8e8ecece8e8ecece8e8ecece8e8ecece8e8ecece8e8ecece8e8ecece8e8, q27N, q27R, (fun _ _ => 0), q27I, []⟩
end PEqualNP.Outside.L_meta_37465
namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
def q28K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q28K3 : Nat → Nat
  | 0 => 0xc5431bc63dcc7a18dc31
  | _ => 0
def q28K2 : Nat → Nat
  | 0 => 0x2590631
  | _ => 0
def q28N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
  | _ => 0
def q28R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q28K4 (i*4) 4
  | 3 => packedAt q28K3 (i*15) 15
  | 2 => packedAt q28K2 (i*26) 26
  | _ => 0
def q28I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q28K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/8+packedAt q28K3 (75+(h % 8)*3) 3) % 5)
  | 2 => 2*((h/1+packedAt q28K2 (26+(h % 1)*1) 1) % 1)
  | _ => 0
def q28Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffbfc7fffe3fff1ff
  | 1 => 0xdbf87f3fc7e0e7c
  | 2 => 0xfffffffffffffffffffffffefff8ffff8fff8f
  | 3 => 0xf3fff03fff00ff0
  | _ => 0
def q28Neg : Nat → Bits
  | 0 => 0xfffffffffffffffffffffff4071020a092a0b5
  | 1 => 0x24972456424665c
  | 2 => 0x110268249094b0a
  | 3 => 0xe244eb92418de0
  | _ => 0
def q28Atlas : Atlas := ⟨4,rawDecor 15 q28Pos q28Neg, 0xe8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0, q28N, q28R, (fun _ _ => 0), q28I, []⟩
end PEqualNP.Outside.L_meta_37465
namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
def q29K5 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q29K4 : Nat → Nat
  | 0 => 0x40032c802144001022fc41f843e907c32fe65fcc7f90fd21fa65f4c7e107c21fe61f8c7f887d30fc61f8cbe087c31fc43f443f907c30
  | _ => 0
def q29K3 : Nat → Nat
  | 0 => 0x400000004018b24000000c1836cf20138400112790c20ad428c6d50732ae42042d906329c43482d90430b641ccab109309e4304354c431ae42cc6710d10ad420c2750f21ae428c6d10520cd320cad10530ac42442dd05309d430827d0d20b641082bd0910af424c2d50420ae420c2790e21b5418ca750e21b5410c2dd0520ad42042790f219f43442b50b31e521086750c10
  | _ => 0
def q29N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 24
  | 3 => 39
  | _ => 0
def q29R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt q29K5 (i*4) 4
  | 4 => packedAt q29K4 (i*15) 15
  | 3 => packedAt q29K3 (i*26) 26
  | _ => 0
def q29I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt q29K5 (4+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/15+packedAt q29K4 (360+(h % 15)*5) 5) % 24)
  | 3 => 2*((h/27+packedAt q29K3 (1014+(h % 27)*6) 6) % 39)
  | _ => 0
def q29Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffbff7fffe3ffff1ff
  | 1 => 0xffffffffffffffffffffffd5f8e73fc71c7e93
  | 2 => 0xe6ff07cff81f8f1c
  | 3 => 0xf8fff80fffe00fe0
  | _ => 0
def q29Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff4010000009040025
  | 1 => 0x2a264a4642496692
  | 2 => 0x1942d41a90932b18
  | 3 => 0x78486ad24c24dc0
  | _ => 0
def q29Atlas : Atlas := ⟨5,rawDecor 15 q29Pos q29Neg, 0xeaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8, q29N, q29R, (fun _ _ => 0), q29I, []⟩
end PEqualNP.Outside.L_meta_37465
namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
def q30K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q30N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q30R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q30K3 (i*4) 4
  | _ => 0
def q30I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q30K3 (4+(h % 1)*1) 1) % 1)
  | _ => 0
def q30Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffbbc79cf8fc38f793
  | 1 => 0xdff9ff3f1fff09fc
  | 2 => 0xffffffffffffffffffffffeffe1fffe03ffe1f
  | 3 => 0xf3ffe03fffc00fe0
  | _ => 0
def q30Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff44742918258a6391
  | 1 => 0x20940049089220b4
  | 2 => 0x1101502242248c0a
  | 3 => 0xe211ab49304cf40
  | _ => 0
def q30Atlas : Atlas := ⟨3,rawDecor 15 q30Pos q30Neg, 0xece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0ece0, q30N, q30R, (fun _ _ => 0), q30I, []⟩
end PEqualNP.Outside.L_meta_37465
namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
def q31K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q31K3 : Nat → Nat
  | 0 => 0x40046d32ba6534caf996e32
  | _ => 0
def q31K2 : Nat → Nat
  | 0 => 0x2350e32
  | _ => 0
def q31N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
  | _ => 0
def q31R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q31K4 (i*4) 4
  | 3 => packedAt q31K3 (i*15) 15
  | 2 => packedAt q31K2 (i*26) 26
  | _ => 0
def q31I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q31K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/8+packedAt q31K3 (75+(h % 8)*3) 3) % 5)
  | 2 => 2*((h/1+packedAt q31K2 (26+(h % 1)*1) 1) % 1)
  | _ => 0
def q31Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffbfdcf3e3f3e74cf
  | 1 => 0xfffffffffffffffffffffffdfef3cfc7cf9b33
  | 2 => 0xebf03f3f80fec3c
  | 3 => 0xf3ffc03fff00fc0
  | _ => 0
def q31Neg : Nat → Bits
  | 0 => 0xfffffffffffffffffffffff404104009020045
  | 1 => 0x208041042040112
  | 2 => 0x150aa0690a94c28
  | 3 => 0xe082ab24a14e80
  | _ => 0
def q31Atlas : Atlas := ⟨4,rawDecor 15 q31Pos q31Neg, 0xeee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8, q31N, q31R, (fun _ _ => 0), q31I, []⟩
end PEqualNP.Outside.L_meta_37465
namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
def q32K3 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def q32N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q32R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q32K3 (i*3) 3
  | _ => 0
def q32I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q32K3 (3+(h % 1)*1) 1) % 1)
  | _ => 0
def q32Pos : Nat → Bits
  | 2 => 0xffffffffffffffffffffffffffffffffffbecf
  | 3 => 0xffffffffffffffffffffffffffffffffffdf73
  | 4 => 0xefbc
  | _ => 0
def q32Neg : Nat → Bits
  | 2 => 0xffffffffffffffffffffffffffffffffff4205
  | 3 => 0x2412
  | 4 => 0x1828
  | _ => 0
def q32Atlas : Atlas := ⟨3,rawDecor 28 q32Pos q32Neg, 0xfff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000, q32N, q32R, (fun _ _ => 0), q32I, []⟩
end PEqualNP.Outside.L_meta_37465
namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
def q33K3 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def q33N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q33R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q33K3 (i*3) 3
  | _ => 0
def q33I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q33K3 (3+(h % 1)*1) 1) % 1)
  | _ => 0
def q33Pos : Nat → Bits
  | 2 => 0xffffffffffffffffffffffffffffffffffbecf
  | 3 => 0xffffffffffffffffffffffffffffffffffdf73
  | 4 => 0xefbc
  | _ => 0
def q33Neg : Nat → Bits
  | 2 => 0xffffffffffffffffffffffffffffffffff4205
  | 3 => 0x2412
  | 4 => 0x1828
  | _ => 0
def q33Atlas : Atlas := ⟨3,rawDecor 28 q33Pos q33Neg, 0xfff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000, q33N, q33R, (fun _ _ => 0), q33I, []⟩
end PEqualNP.Outside.L_meta_37465
namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
def q34K3 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def q34N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q34R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q34K3 (i*3) 3
  | _ => 0
def q34I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q34K3 (3+(h % 1)*1) 1) % 1)
  | _ => 0
def q34Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffbecf
  | 3 => 0xffffffffffffffffffffffffffffffffffdf73
  | 5 => 0xefbc
  | _ => 0
def q34Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffff4205
  | 3 => 0x2412
  | 5 => 0x1828
  | _ => 0
def q34Atlas : Atlas := ⟨3,rawDecor 42 q34Pos q34Neg, 0xffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00, q34N, q34R, (fun _ _ => 0), q34I, []⟩
end PEqualNP.Outside.L_meta_37465
namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
def q35K3 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def q35N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q35R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q35K3 (i*3) 3
  | _ => 0
def q35I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q35K3 (3+(h % 1)*1) 1) % 1)
  | _ => 0
def q35Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffbecf
  | 3 => 0xffffffffffffffffffffffffffffffffffdf73
  | 5 => 0xefbc
  | _ => 0
def q35Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffff4205
  | 3 => 0x2412
  | 5 => 0x1828
  | _ => 0
def q35Atlas : Atlas := ⟨3,rawDecor 42 q35Pos q35Neg, 0xffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00, q35N, q35R, (fun _ _ => 0), q35I, []⟩
end PEqualNP.Outside.L_meta_37465
namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
def q36K3 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def q36N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q36R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q36K3 (i*3) 3
  | _ => 0
def q36I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q36K3 (3+(h % 1)*1) 1) % 1)
  | _ => 0
def q36Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffbecf
  | 2 => 0xffffffffffffffffffffffffffffffffffdf73
  | 3 => 0xefbc
  | _ => 0
def q36Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffff4205
  | 2 => 0x2412
  | 3 => 0x1828
  | _ => 0
def q36Atlas : Atlas := ⟨3,rawDecor 13 q36Pos q36Neg, 0xfaa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0, q36N, q36R, (fun _ _ => 0), q36I, []⟩
end PEqualNP.Outside.L_meta_37465
namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
def q37K3 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def q37N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q37R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q37K3 (i*3) 3
  | _ => 0
def q37I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q37K3 (3+(h % 1)*1) 1) % 1)
  | _ => 0
def q37Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffbecf
  | 1 => 0xffffffffffffffffffffffffffffffffffdf73
  | 3 => 0xefbc
  | _ => 0
def q37Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffff4205
  | 1 => 0x2412
  | 3 => 0x1828
  | _ => 0
def q37Atlas : Atlas := ⟨3,rawDecor 11 q37Pos q37Neg, 0xee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88, q37N, q37R, (fun _ _ => 0), q37I, []⟩
end PEqualNP.Outside.L_meta_37465
namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
def q38K3 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def q38N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q38R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q38K3 (i*3) 3
  | _ => 0
def q38I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q38K3 (3+(h % 1)*1) 1) % 1)
  | _ => 0
def q38Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffbecf
  | 1 => 0xffffffffffffffffffffffffffffffffffdf73
  | 2 => 0xefbc
  | _ => 0
def q38Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffff4205
  | 1 => 0x2412
  | 2 => 0x1828
  | _ => 0
def q38Atlas : Atlas := ⟨3,rawDecor 7 q38Pos q38Neg, 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8, q38N, q38R, (fun _ _ => 0), q38I, []⟩
end PEqualNP.Outside.L_meta_37465
namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
def q39K3 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def q39N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q39R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q39K3 (i*3) 3
  | _ => 0
def q39I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q39K3 (3+(h % 1)*1) 1) % 1)
  | _ => 0
def q39Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffbecf
  | 1 => 0xffffffffffffffffffffffffffffffffffdf73
  | 2 => 0xefbc
  | _ => 0
def q39Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffff4205
  | 1 => 0x2412
  | 2 => 0x1828
  | _ => 0
def q39Atlas : Atlas := ⟨3,rawDecor 7 q39Pos q39Neg, 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8, q39N, q39R, (fun _ _ => 0), q39I, []⟩
end PEqualNP.Outside.L_meta_37465
namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model
def gbK10 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK9 : Nat → Nat
  | 0 => 0x1e28200a98304080100400210918030d5c00000401001000c01c41c70c0007f4c801be41007f50c01fd41006f10401bf40007f8c001ff30007f08401fc10007f50001fe31007f0c401fc32007f48001fd10007fd4401fd54007fc4001fd30007fd4801fc52007fcc401ff21007f94c01fe20006f50001fd53007f08001fd31007fc8001fe50005fd4801fe40007fcc8017e50007f90801fe52007f90c01fd42007f94401fe32007f84001fc51007fd4001ff54007f0c001fd50007f48401fe21007f90401ff53007f14001fd51007f54801fc53005f140017d52
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x1a8000ff0c45000678caa0003bd40cc001dea9a8005ffd08310077e65a000f7c4114001ff1824000f74c831006fea510803bd6290401bfa924000fb4c832006fecb10003bf400c001fe2864000efd0320027f88110803fd2148001fe28c4200bf98253007fa6510802f56108001dfa9e8000ff14520005fac1298037c65480015eb26a201ff10c10006faa6298037f52cc8017f31e4200ff0c410007fc43180037d6114001fe9966006ff10732005fcc628002bf6448401de20c4200ef50120007faa5188037c508c001763122000ef4ca41005fcc318003fe518c4019e2828000efd4740005fac5200037e319400bfe2006204ff10621007ee6318802ff62c40017f31c8000ffc8010006f86528003fd3248001dea006000af5902003ef887a90037c6588001fe18c6000df08450006fea418003bc4148001beb2e6000ffd8e21005fcc728003ff3214401fea142000bf98450006fca108003bc3150001be990a0009f99720007ba8699003fd428c4017f3082000df195300057ec988002fd60c8401ff9946000ff58a30027fca910803fc51c8001beb10a000df50a50006faa5a8003bf3250001ff1864000cf94340005fac690002fd63c80017eb046200bf18153005fac6108037d52c4001fe1884200af58041006faca188037f5248401bf298a000f714e310077a8190003fc324c401bfb2a4000bfd8953007fa8608003bf5350001ff29a4000ff4c831006fa87a9002fe63904017fb02a802ff10430007fea610802fd6388401ff29c4200df94110007fc6310003fe418c401fb8842000ffd4540005fec4aa003fe3108401fe1086000ef107200077e6420803bc410c001bf2844000df90650007fa6418003fd4348401dea948200bfd8931007faa4990037c5354801df20c6200ef946410077ea2a00037e42140015eb20a000bfd8142007fac910803fe3108001dfa988200cf90650007fa6520803df324c001bf2828000f78c630005fcc118802fd6390001ee9806000df94020007f863a8002fe61940017eb1c2000dfd4950004facb880037d51140019eb20a000df90c5000778a1a0002fe6190001bfa928000ff8c5400077c63a00037f2194001deb206000df98450007fac518803ff3148001be2826000ff886500077c62a0002dc6354401df3246000dfcc450005fcc710002fd6094801deb2c8200dfd8d520077a8010002fd63c4001dfa042000df14310007fca090003fe31040017f3066200dfd8952007ba6518803fe3154001bf300a000ff988100077e43a0002fd63948017f30c4000ff88530004facb90802fd62940017f3006200df98c50005fac429802fc6148007bf2a0a000df0c850007f8c298003ff604c801fea8a4000dfd4250006dea529002fe60cc801fea10a000ef90620005fcc190802fe6314801ff10e20009f19531
  | 1 => 0x3fd424c4017e31a2000fd88710007fe6508003bf52500017fb026400cf54a4100ff884080037f5290001ff18e6000bf580530077ecaa00027d6508401bfa906200ff8c430007bea718802ff604c4017fb102000bf98c10007fac0188033d64940017eb14a200bf98021006fca198003fc510c401ff9842000bf58a10007fc8498802fc6304001bfa9aa200df54850007fc4228003be3210401ff28a4000bf18d40005fac5988033d52d0001bf288a000ff98831007faa510802fd60904017f306a600ff54920005fcc1080027d6508001ff28c4200ef14c41017fe8418003bf52104015eb202000df50850037fe85990037e2194001bf188a000ef14a410077ec8990037f5394c01bf2824000bf58c50005fcc690003fd2084001ff31c4200af58241005f8c690802fd60884013fb2a8000ef14d40007fa87080037c5084007bfa18a000bf18e20006faa4080037f5194001de2968000ff50a21007fa6520002fe6090c013eb14a000df486500077ec9880027e65148017e302a800f7cc230005fcc110802bd64c8401df2086200df58c50007fc6218803ff65884017fb122000ff14c21005f8c6a80037d52500017e3024200df0c650007faa298003bd31d0001bfa928200df54921007facb10803bd5390401ff9946200df98752006fe6528003be410c007bfa00a000ef90730005fcc0180037d52144016f31e4200ffc82100057ac920003fc3188001ff18e4000df94030005f8c0a08037c5044001df3148200df54a30007fc4310003fe32cc401bf2864000cf54940005fcc22981f7e64d4801ff98020009f195200077c83108037f5394001be2844000df90450006fa8728002fc6154001bf31ea400bf98632007b86318003bf40cc001ff9902000cf14340027fe85108037d63940017eb1c6400bfd8e210067c8228003be4148001bfa926200df58f52007f8a198013ff4088401bea926400bf98f20005fac728803be21d00013eb286200df14020007ba6598003f510040017f300a400df99431006facb880027e650c801ff99220009f59730007fa62a0002bd648c0015eb244000ff1822100778c2a0003bf40480015eb242000bf58850007fe64908037f21140017fb128600ffcca200057ac818003bc5250001de18e8000ffd8530007fa85a88027f6548009ffa1c4200bf987200077a62a0003fd60cc801fe1884000ff14120007fa4008003bc5210401ff10aa005ffd0031004feca88003ff614c801fe90e6003df100500077e65208037f52cc001ff9926400df54050004fcca1000f7f4214001bfb0aa400bf18d42006faa7a9002ff6250001be908a000cf10450006f8a008003be41c8001fe28e6000bfd8c100077ea720803fe21040017eb1c6000ff88540017fe80180037d524c001feb044200ff4c941007fe6118002fd6014401dfb
  | 2 => 0x30005fec6a0003fe43840017eb066200ff98332007fe64988037e4394001b7b12a400ff88730006fac528003bf62500017e30264009fd9620005fcc219002fe610c001fea9c4200df54b51007faa690003fe3284001df31c8200dfd4b31007fac399003bf40c4001bea98a000bf98652005f8c2a10037e65c4001feb0e6000ef18940007f86408003fd3004001fc98060009f58850037fe81990037f5294001fe98e4006ff10332007fc4290002ff63480017e30a6400bf18142005fcc398002fd60084017eb06a200bf98420006fea498003dc310c001feb106200f7d4c31007fc63200037e21140019ea908200df94240006fcc328003fd214c0017e31a4000ef94140006f8a090002fd62d4001fe190a200bf18553004f8cb100037e62940013eb2c6400bf98e51005bec6a8802fc60544017eb18a200ffd4d20006fca628803be6590401df3048200bf98e42005fec4a0803bc3250001bfa962000ef50130007f8c299003bd63904015eb266200df54b31007f863108027d650c801fe9966200df99730006faa5208037c53940017eb1c8400ff0c520006fac3280037f3214001dfa948200ef0c841027f887108037d5284001be188a003df10c50007fa652801f7e54d4801ff9944200bfd8d210077a8188003ff3248001dfa828000ef8ca41007f86090003fe210c001eea1e6400ff94a31005fac121802ff6344001bea946200dfd49510077882980037c500c0017e31aa400ffd4730007fea710803bc410c4016e31a2000bf98431006f8a190002fd600c409fe3244200ffd5221005fac1a9003fd54884017e302a400df18d5200778c8990027e6014001dfa968000bf58810007fc8310803be32d00017f31ea200bf98051005fcc710803fe60884019f324a000bf9835202ff8821880f7e6414001fe9962000bfd8930007f86390003bc41c4001be302a400ffd4520007d843100037d5414001be2828000ff98730007bc8699002fd6388001de20ea000ef54540005fac598003fd4388401df2928000df4c65000778c6a00033e6414001bea928400bf98241005fec0a901f7f41d4801df10a8000ff90c1000778a720803fc30c8001bfb02a400df50c50007fc6408002fe6194c01bea0ca000ef10730007fcc418003fe3148001afa9ca600ff8c621005fac1a9802fc6150c01fe992a200ffd4f20006fac3a9002fe6384001ffb1a40009f99431004fccb190037d52880015fb226200bf98020006fc87a90037d5244001f79946400ef14f40006f8a528003ff314c0013f32e2000ef94a41005fac608003fe43484013eb2c8400bf98f10005fac7a8003be3250001ff996a200bf58332007be6518803fc63480017fb12a0009f59720007fcc518003ff64884015f3088200f78c430006faa9a9003ff51c8009fe2a44200ff94130007fe642800
  | 3 => 0xfa0e6400bf18d54004f8c0a9003ff5288401fe30a4000ff90e21007fac808003be418c0017eb1ea200bfd8951004f8ca88007ff43040013e32a6001ffd08100077aa0a0003ff52480017fb1aa000ef99220005fec6a0803bd64040019fa968000ff8c6500077a43a0002be61d00017f30ea600ff4ca20007788310003fd408c00fbfa1ea407dfd0b52007f8cb10802fd63d4801de28e8000efd02300077a8008002fc61500013fb2a6200ef90421005fac720803fc5050001be2848000ff8c831006fc8528002fd63080017fb02a200cfd9540007fc4320003fc328c401de2828000ef59220007fcc0188033f5250001bf310a000ef10420006faa4a08037d524c401bfa902000afd91100077843a00037f31940017eb00a400ffd4831005fac510002bc6150001fe29c4200ff8c830007f8ca90003bc6550001fea002000bf98251004fccb21003fc21140015eb24a000ff54930007f8a690002fd620c401ffa966400ff18e21007fca2980037d52cc001bf2826000bf98c300077a65a0003fe6588401be30aa400fe8c030007f8650801f7c40d48013f3284200ff58e21005fcc3a8002bd640c8016f3184000ef10450007fa42a001f7c41d4801fe28a8000bf58b53007fa6108003be5390401fe992a000dfd4a300077a42a0002fe63d4801ff18e2001ff1041001ef8842801f7f40d4801de28a8000ff98732005fcc318802fc6154801fe1082000df98e50005fcc729002dd63c84017e31e2000bf984210077ec2a0003bc4104001bf290a000ffd9520006faa510802fe6314401bf2862000ff4c810005f8c2980027e6094001bf21aa400bf58c520077a8118002fd6294c01bea924000bf58232007fc84288027c65500015fb22a205ff10831007f8a7900033f5210401bfa926400bf58a43005fac5a8802fc6155001fe2884200ef14441005fcc7a80037d520c401bea1aa400ff4c730007fa64a0003fd3248401fe10c6000ef4c9400077c8328003fd620c0017f30c8600ef10421007f66098002fc604c401ff210a002ff108300077842a0003fd608c4017fb1c4000bfd8153007788318002fe63080017fb1aa800bf98242007fcc518803be414c0017f3186400bf58a30007be64188027f654c001ef9966000ef0ca41006faa599002ff63508017eb1ca000bf982300077e63a00037d64d48013f32e6000ff4c520007ec62188037a6014001ef1826000bfd8d51007be6018003bd648c001ff3046200bf58251007fc84080037d4114001bea906000df8ca50006fa6228002fd600c8017f308a400ef94d40006fea6a9003bc32d0001df3206000fd88510005fac790803bd32104017eb148200ff0ca300077c8388003bf404c001df98a8000df14330007ba6498003be41d4001dfa868000bfd8121007f86428002df6344001fe2906200ff90a
  | 4 => 0x14000534d4080703b02408004c20080a014340088104c0201c0508c300107002c140741000d9217800124b847000000125400003012004000680619800000330040600c0202c3db8800004000000328405088ad03c26214050180023c0303b800018d26403000000b00001db90a00b78c000db990b406008070740000103008a72fc0100039000390340002402005fe01109029ab000010005d0400d00c07000000005e510a3000000200a00000002ec004650080218405000070083a0241a02c48000600900300000010000000504436008000480001805000000000d3bc04024010145d02c39344010909302004000640740100c92c9400150350002300000064030080200c2f498000301600800260022ac0c00402411af62ccf044085341300c000005303c0000c03121780347d000131500202c05004000200a344000e0af00c000dc760381d0b0b200c00020010d000ac404052341b805008075007b021cc0e8040480100401064010142301834000284ec0401802f2000000000ac040040fc3c2c034004cc000040d128000000002404038040180405001010838c82c0000300003090050081f0240c784010000c01c0400c000e40004c4901405268001601004055374980040103c090000156c000e08a0286e01408408c3007ea6218803ee2108001df208a000bf18143007f8c099002fd628c401bf2802000df146500077c82100037f52944015fb226400efd0110006fea518803fc314c001f710c4000ffcc7200077e8110002fe608c8013f32e4200df58352007fc43a8003fd4248401bfa942000bf98732007fa8408002fe6014c01bf306a400bf98351007fc85a8803ff324c001bea948000ef54940006fea4a1003fd4084001ffb044200fb88120005fec0a0802fc6388401bfb2a6000ef945400077a8108013fe64884019f2828000bd98420007fa6018002fd6214403ff3202000df94230005fcc610802ff6050c01feb102000efd0020007f86388003be4104001fea10a200bbd8910007fe6588003de43cc801fb8802000b758c20007da40100037c53944017fb1e2000ef90550007fc8208003bd6090401fea146000ef99010006fac828003bc418c401bfa922000ff4ca51006f84328002fc6350401de3262000ffccb50005fec6a9003f521c4001ff2142000ff0cb51005fac1210037f5290401bfa944000ff58c10004facb290037e53d4801df90a8000df4ca50006788328003fd3284003ffa002000ff90a31005fac5880037d53d44017e31aa200bf58830005fcc321002fe600c801f79044000ef50110007fec290002fe61d4801ffa966000ff5093201efe82280027e60d4801ee2986200cfd4a41006fc6428003fb308c001ff20c6000fbcc932005fcc129003bd4088001ff3182000ef14641007fa6488003bf400400df
  | 5 => 0x4cdd0080204c187480000
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0xe758cb400065f6394110006be6310621006fc71588530063f6550220004ff7258f50004ff7688430005f47150d21006ff63885400067d62d4831005fd7388620005bd740c8500063e6510710005787054a20004fd76d47200047d72994310053d749805004eff2018532007f27088710007ec7388620005fd73982210047f7654c53006fc7058831005f9700ca100047d76084500067d6298050007de634c810006fd1058831006fc631822101e3c6414110005ed720c6210067d654cb100067c7654a31005fc714ca40004fe76cc9310075f328c650006fc7688540005fe710c810005fd73d82210067f6218552005f9708c4100063d6550320006fd628c431007df320c4100057c7354450006bf7218540005bc764c940006ff32986300067e611432004f7e650c421007bc624c5400063d6290450005fe73143200067e6398450006fc610c520006bd6290430004fc7158e2004fde630c7200057c7358450007bc714ca41005ff724c7300053c7054841027be7310621006bf63185400067c658852000ebf42185400067d62944500047d76d48310079d3210431006ff7398421004fe7198e40007f6310c520006bf644c921005fe71181320057e710c8500067d628c6500067d7614330006bd3258241004fd729864304efc42588310073c4188450026be6488450006bf6390520006be64588300077e3114120005fe71908100077d32884500077d7688650005fe7394120004fd7218d500073e73141400047f72594310067e7558831007b4410c621005fc714c810025bf7688740005787048450007f671d8e210067d75588310067d658c730006dd6318e21004fc764853002ebf600c5400069e63904200063d6454a30006bd6350320005b970904100059e731894000fbc4150c100073d3290450006fd32181210067e63d4a21006bd6458830007bc744ca100057e750c4210073e7614140006ff74d89310057c7054a31007bc744c810006ff329805101d3f76104500047d7219531006dd620c6300057e71908500067d654c831006bc6150120004fc7654e21006ff65d8d20007be418c720005fc7150a310379c4150f320063d6494020006be63104100053d74983520066d6248450005f97008410004fc764c9400067d73983520077e31086500057a70d4920005ff7358221007bd3290410005bd7090631007ef324c8100075d634ca50005fc714ca100057c714c850036be64cca100069c6350110007bd708c540006fe6298031005fd71d81320067e6314210006bc7218540005be71cc94003f3b60d4940005bc7648540007bc3150120007be414ca100057e7394850005fe71d8d200059d73189400047e70997210077d7518e21004fd7688730005fc73549200077f7388650006fc6598e21006dd630c420005ed7214f20005fd708c831
  | 1 => 0xf32006fc3298630026bc6488710004bf764c841006ff6558e21005787054a400077c7354a21007f9104c8100079c744c8310057e70d4b32005fe7198332005bd7090621005ff7354a210077d62d4831005fc71583320077f52cc8100057e750c7200057c73587520053d750ca41005ff7388520004fd7694a310072f52949400067f52987300055f73584500067c63141400057d7590a31005fe7398810007ef32886200077d3294210006fd32181510059f73545400075d524ca31025be7498e210077d32940100063e6458a5004efe5218532006fd62cc850006fd63884500079f328c7400067d62d4810006ed62884100067e760c45002fbd72104310067d6254b310077d520c621006fd628c410005fc7154932005ba700c5400047e70d95310067c63d49100073e4188450007bc76885400053d7010450004fe71d8d20006fe7358a10005fe70d8532005bd72143400067d624ca50005b671d031004f7d650c421007ac62885400079d3290431007f77388510007dc704c831005bd741822102dbc74588310077e7388650005fe7018532027ad6288740007bf6388540057f4410c621005fc760c5200067d7518532006de638c4210077c71588500063d6590710007bc628c540006de638c7200053f754c5400047e76d493104fdf320c720006dd7218d100047f764c4500077e3194320006fc70185320067d654cb300053d758c940004fc764c5200063f645491004efc20185320077e750c421006fc4058831004fd72d8c10006bd6458c100067d62d4a30006df6398e21004fe7198e52007bf7388540005fc7654d20005fd72982310063d6590431006bd62104310063e65907200067e7158a500057d7518e21004ff764c810007dd32980310077c31143200063f6590530005fd764ca10007dd634c810006fd62884300067c73588500067f63d8552006dc634c9410077f5354a21006dc634c9510063d6494210005bd7398a41005ff7058831005fd73884100053e70d4a4103e3c41996420067d62884500053e750ca4100578705481003d3e7514841006fe4218131006bd6488450006dd63cca21006b4611052003e3c64d4951006bf644c951005bd7218540006ff7688730006ff6388520005be710c841005fc714cb310063d6210650004ff7650e100067d6354a100063d5218540036bc64cc931005be7118940005bd7314a410067d6258650004ff7654a31006bd63904500047d760c650006fd3298650006fe63c82100077f7654a31005fe7190a3103e3e64d4810007be31087400067d7158850006ff764cb10006fc71588300073d6510431006fc6498e210073d52106310077d5258231004fd7218540006ff62cc810007df320c620007bd700c740004fe760c931007df328c5200057c7054932006bd644cb31004fd76084300053
  | 2 => 0x63e61143400047f72597300067d62584500053d740c850006bd6290431004fc764c910006ff624c540006fd614cb30005fc714c910006bf64185320057d750c6210047f765405004efe42185320047c7059431006ff6348520007bc73502100073d52185400077d5314e21007bd32d02100057f7558e210067d6398050016bc4218d40004bd7690630005fd7314120006fd629803101d3e7190450004fe7118d40006bd6210630007be31d03200057c7054a21036be64cc8500077d520c520007bd74d85320065c6354910005f8704c7200063d6290650006fd624c8100067f62d49310077c650c520007f4714ca100063c65d01200073d52ccb40007f47388710005bf744ca100063d64d4a20006ff7218540006fc63185200047c70596420077c7054932005fe71cc851007bd62104310067e7518532006fc73185200067e7058850004fd760c810005fe73d52210053f744c450005bf744c8100057e758c83100fb970104100077d7688450006fe63884100379d63cc841005fd73185200067d6254a10004fd729825100fbe6490c100077d76d4831006df32185300073c63141400057d7214030007be7388740007ec73884200066f6294110005fd728c410006dd63ccb510053d75c85400047e76941100063e65907100067c6114130004f47158d20007bf3210410005ff704cb31006be6110730025be741822104efe620c450007df328c7100057d7690850005fe7614d20006ff4298732007f67118e21006ff6348540007dd320c621035bd76ccb400073f32104500067d62940300077f528c621005bd740ca10006f6618c4200077f53549200077c714ca50006ff7218543005bd74d85320067f6394120004fe71d81320047e7614130007f4510c421004fd7298331006bd62104100057d728c450006df3298431005dd72d4e310067d5298732004fc7158f52004bd76104500059c7354540037bd76ccb40005be718c8410067f65885300053e758c9400063d6498050005fd728c62000fbc4359010005fe714c921005fd7319621006bd63904100053f744c850006df63cc910007f4714c8100073f529063104fdf320c420005ed720c520006fd7058853007f6310c7100067d65887100047d72d95300067e7058a50006fc315822100fbc4350c10006be6108740006fe42982310067f65d8d200067d52185400073d648c6500065e639402003e3e64d4a3004fdd630c7200067f658c5400073d5288540007766188450006bc63d01200077f52cca100057f7388650005bd7019132004fd7218d10004fe71d8143006ff6318e21006bc74984320063e65d0330005fc7350010007ed720c621036bc4198e42005bd740c810006fc32980510069f63d0110006fc764c921007ed320c81001d3e74980500057d760c450007777154a21005dc715
  | 3 => 0xf7654b100057c70594310053e76549400071f5394d40004fd7298e51005bd740c9310077c73884500067d73588500073d5290621006fd7318520006bd6290410004fe7198c20006ef6288540005fe73d9621007be73885400047d72d9540004ff7688730005be718ca41006fe604c810004ff7258f51036be64ccb51006ff628c540007f461cc520005ff7348520006bd6458a30006fd64d8e2103e3c64d4910006bf764c9400063d64d4a50007f8704ca20005b97010450005b4715031000ebf7018540005be71d03200057f76d48310063e65104210065c63d4d510067f53d8951004ff7258c51006bd644ca200047d76d4b30007be720c740004fd7218131005ff7050b51006dd760c6300077c6554d200077d728c650005fe73d8520006ff61d8132006ef62cc910007bf624c5400073f654c9400063e6550330005fc7348520006bd6290630005fd720c6210077d630845003d3c7458752004fd768c420006bc62185400063d74983520063d6590730005fe7690e210067d62cc850006fe618c7200077d7319520006ff6318520006fd7358810007be31085400063d64140100053f7690650006fe6348010006af62d01100067c63d4951006f46188520005bc714c841005dd7214c31004fc7688540006fd620c450005fd728c6400053d72143400075f52cc8310075e638c650006bd62d00300077c53549200077f528c5200053f7448650004fe7198e42005fd738c8100057f7254c500057c754c7200069f6350110004fd760c8500063f6454b10005ff73549200067c65cc920004fe7198e200055d73c86500075d320c65003d3d76d4b400057c7350450005ff7388710006bd6390420006ff6254530007dd320c5200067d62cc450005be7118d40007f7714c921006bd648c620007bd32d0010007bc7350010007bd72185400077d73d95200057f76cc850005fe7190e210053d7090650005fd72d45200067d6588730005fc7150c100079f328c540004fc7654d20007bd64cc8100077e750c7200073e648c6500053c7054a410057c7558732005fd7098a310067c6518520005fc714cb300057d76886500067e63140200073d644ca50005f671cca210067f654c940005bd74181320077d750c6210057e739885001f39701045000778500c3200069e63d00200077d760c450006fd3298730005bd72141400067e6588710007bf72185400057d750c520007bf634854001f3a70104500077d3248450006fd705883104f7f520c4210057d7314a50004bd7690620007ed720c5200057c7150c50006ff7688630006fd6458c10006bd645881000fbd73104100057d72142300073f658c5400077c7354920006b661104200067d52185200057d72d46500067d62484500073f5210621006b461cc5400066d628c850006fd63884100073e3114140
  | 4 => 0xc45000fbd73d0010026be64886300073d321414000ebf4318540006af6250110006fd4298051004fd7614c21007de63cc8100069e63500200057c735885003e3e64d4a50027bf4390e21005fc714ca51004fd76886500063e65104310077d7314320006ff620c710006bd644ca50006ef73d89100067f6599621006b4610c54000dbc744c810006bd6250030006fe6188730005fd7090931025be7498221005fd73d95200067c63d49400053e750c841006b6619042001e3e64142200077d750c520006ff76884500057e75988310057d7294030005ed7214e21005fd720c5200067f65885400057d720c650005bc73487400053d72141400073f524ca41004be76d0110007dc314c921006f67688510026bd76106210075a50cc230006bf63501200075f320c4500066c62141100073d520c740004ff764c831007bc714c940006ff631822101d3c744c8500273e658874001d3c7448450005ff724c520007bf32904100063d64142300073f744ca50005be71d01300073f52906210063f6518540006fc63d8221006fd62884100073c658c540005f87048730006be63d00100067c650c5200075e634ca500077f32884500057c7558031035be749833202ebe640c420004fe7118d52005fc7650e210079d320c740005f671cc921027bf43d9221005bd7010631006bc7398740006fd4298630007bd3210621006ff321812101e3c4119540006ff63582210063f52580410059d73c8740004fd76908100053d74cc650007bd32500100073e211434002ebe640c450004bd76d00100047d72195400047e76d4d510057f7348650006fd62ccb510063e65d0320007de634ca1000ebf76590100053d72d9540005787054b30006be6110720005ff704c8310077d7518532006fc415883104f7f520c720006fd7418532006bc6108540006fd6288630027bc6450e21006f66188630006fc6518d20007be644ca1001e3e6414030005fd764c8100047e7019531005bc768c5400057e7190e50005fe7388520004bd7690420006b47498420005bc7688540007bd3250210004fe7614d20006be6190730005dc7354a310077c5354a2102f9d73104310057f724c6500063c65501200063e7694140005fe73d9221006ec73d8910006bf32582410067e7318152036bc64ccb100073f32904500057d7298e500047d72195100063e7418152006bf7418532007f9700c520005bf7358241007bc418c5200067e63d4a100073c418c650007f8704c810004fd768c8310067d658c420004fc764c920005dd76cca310077f6354a21007ef21d8e2101d3c7458450006bd648c650006fd6348010026be64884100053d75949400047c76549200067d6394010005bd72d47400067d658c4210077d6388650007be31503200077d5314d200067e7694120007dc638c5200047
  | 5 => 0x67e650c720006dc638c520005ff7650c10007bc744ca21037bd76cc841006bc7358041006ff614c940006fe4298351005fe73d4520006be6190720027bc4150e210077f32942100067d62cca500057e75d82210057c754c730005bd70904310075d52cca3102ebc640c7100077f3294010004ff7688630007be418c5200067e6194330005fe718c830035bf76cc8410077d768c650007f9700c710004fd7298e500063f7558241004fc7158c50007ef324ca21026bc4398642005b97010410005bd720c7400063f64d4932004be7694140006be618c7400063f52987400067c76549200057f7259431007dd3258031004fd7218153007f4610c5200073e65104310057e73983520063c6510530004bd76d4740005fd7090a31007bd3290621004fd76c80100077a21980500067d6294010005bb70549400077e7358850006fd6388650004fd7614f200067e65ccb10006fc31580210073e410c450005bd7314940016bc4118d400053d7294340006fe638845002fbe7210431007385050020006bd3258041004fd7690a31005397010450007ef7388620006bd64886200047d76140200077f7354a21036bf4098e42004bf7648740006bc6418532004fd76cc850005b97010620006f461cc5200053d750c540004fd7218d510067d62cc650006dd63cca10007bc410c720007df714c831004ff7258e1000ebd76d00100057c7054b320067e7614120005bf724c7400067d6558031005bd72d45400067f52185300067c65909310067c6518530005fd720c630007dd63cc8100063f65501300067d7358a500047c76549100079f32104310073f6588540005ed728c6210067d620c4500057d7688450005fc764c9210073d750c740004ef764c8320073850502100063f64d4931004fe76cc9300067d62d4a310073d3210650005be7388740005bd7214c41005b9700c540004fd760cb51007bf744c92104ffb200c6200073a41980500063e65d03100073f52cc841004ff76884500047f7259710005bd740ca31007ee214c921005b970107500067d6358650005bd73141400047d760c8500047f7654b30007df638c520006fe71588300057d72942300053e7110450006f461485200073d62104500073c410c4500067d62486500053f74587520067d6394020005bf7388540006bf7498432006de638c6500063d65d9310007dd320c7100055e73c86500067f75d89310077f764ca500077d7394120005fc714ca500077c71549320073850503200077c7558031006fc6118132005bc714ca41007f43188710005fe71cc8500053d72195400057e7108450005dd738c8310067d6288650004fe7614e21007af6288540006fe32984300073d6488650005ff704ca5104efc620c7100053c7054b400053d74d46500379d63ccb400063c611414001d3e74c
  | 6 => 0xc41886500077d524ca100057d76084500073f524c940007bf32d0210006bf7398740005fc7388410005bd7298e410063d64d48300067f5358a50006dd7218d510053d72941400073f5210431004fd72d8d100373e65ccb40005fe73c8010006be61d0330007ef324c9200067c6518d200073f52cca410073e418c650004bf7059331007bc704ca41004fc7158332006bd62d0010005fc714c9200066d62c84500077c63d4a21005f4714c810004fc7158853006bf7650210007be70ccb40006ff42984300073d32906500066d62548300077c704ca50005bc7150130006ff6318d20007df320c6210063d65503300057e750c6210073f3214340005fe7308410006bc63d01100067c6588540006fd614ca50004fc764c921006de634ca50006ff7358810005be718cb40006ff3298450006fd62d4730005bf724c5400067c6114140005fe71cca20005fe7314120006bf62185400063c6518540006ff7418532004fc71580320063e6550310007be410c720007f431084100067e6314320005fd720c7100057c7388450006bd6350010005ff7050851005ff715493202f9d630c740006fd760c42002fbd620c740004fe76cc910004bd760ca41007bd644ca100063d64d4810006bc61105300057e7308450006bd648c4100059d7398a41006f96018221007ef328c810007be768c5400063e65503200067561940200067c63d49410077f735492004dff720c421007de314ca100067d6294230006ed628c810035bd76cc841007dd328c410005fe71ccb50006bd62d0230004fd76cc720005f87054920006bd6390621007ed3248520006fc7098642005fd70988310077e31886500067661940200063d6454a100073e21141400077d73886500057c7150f52007bd73887400047e76d49200057f768c650005fc73886200077e71cc8500063d6590420005bd73d85400077f3248450007bf628c540004fe76941200053c70549400077f5394e2103e3f40996420057f7258c50004fc76549300063d6550310004ff764c010005fd700cb51036be64cc810004fc7158a300072f7254a41005bf7348540006fd32982210063d6414030005dc7354932006ff63d82210077c3188450005bd74d8e21005fc714ca210059e73c87400066c75d8910004fd760c4200057d72cc45000cff7650210005be71d03300073c654c940007dd328c620007b9404c2100073e6488650004bd76106200063f64141100063e65d93100065f635491004dfc72580310073f528c540007bc414c9210063e65904310067d5358850004bf764cb40005be710ca41005fe73887100063c6559220006ff32181310053e75c87400063d6590421007bd728c540007bd32d8540005bc71503200053d750c940005ed7214d20005fd730841004efd62148310067d6358450006fe1058c21
  | 7 => 0x853004dff760c72004ff72118e210067c7058850006bd62106310063f521854002ebe640c410004fd7298c1000fb671104100057e750c52002fbd7010431005bc714cb400077e750c6210053d74d85520063f6414310006fc7018543007f4714ca21005fd73d96210047c7059432005fe7319520004fc71588500047d768c8500067e6314650005fd73c8210004fd7298e100067c65cc9100047e70994320067e7694130005fd728c650026be64886500053d7690450004ff7654e2101f36711045002fbd761043101e3f6014140005fd73c801000dbe740c810037bd61ccb40006bd62502300059d73c854003e3c64d49320053e75c85400063f75580410075c7354a31005fe730c810006fd62cc8100079f638c540007bc3108740006fc6388540005bd7010621007bc744c921005bd7214e41005bd720c540007fb104ca1002dbe7498031005fc73545200066f62549100053c7654940007bd73885400067e6194320006dd7018d51006fc75984320067d6214210005fc714c95003e3e64d4a20006fc764ca10005fc714c921006bd644c8100077d5218532006bc764ca41006b561d0020035bc7458732006bd6350020004ef7648020005ba7094540006fc32181310077c31086500067c61141200059e73c8540006fe63182210063c65905300047e7694120007f773887100073c6588540004fd768c4100077e319412004f7e7598831007df320c52004dff720c720004fc7158b530053f7458450004fd76988100057e7114d52006ff40588310073f5288740005f87048520006b661d0020006bf64181320077c31141200077c7358850006fe7558831006f4610c520005ff7358810005b97010530006fd62946310063f52984410073c6114140007e970886200067d62d4650004ff7258c10007bc6310621005fd768c8100057e730c850004fd760c7200047e76141100076f7254a21006ff72185320077a70141200047d768ca500053d74c84500065c6314110007dc714cb30036be64cca30006de7198c200077f76886500057e73c8450007ef7388420004ff764c030006fd7058b510057e7190a50006fd6258031006fc7158810006bd3298740004fd7298f10006bd648c4300077d524c810006fc7558831007bf32d0010006fd721854300fbc4190c10006bc7418532006ff64d8e21005ff7359621004bf76500200379c4190f320075f5354a31004bd760c8410073d62904500063d6494220007385050110006fd760c6200063c65d0110005ff7359221005fc714c8300065d6314020006bc7458831004fd76cc010006dd628c430006dc634c920006fe6348210005ff764ca100067e650c7100073c744ca500057d7598a31004fe76cc9200077e6308450004bc7159020005fe71cc810004fd76cc810005ff7354520004fc71582430073
  | 8 => 0x7bc6390621006fe6518e21006bd70185400273d65887400067f6354a210047d72d9531036bc64cc910007bf714ca4103e3c64d49210067f63941100057c7154c53006fd7358a10006fc7098432007bf3250010007bc7458831004fd768c83000fbf435901002ebe640c630005fc7150e2104fee720c421006fe63d8221005fe710ca30007ed72d8e2100578704c85004efe620c6300063f64d4910005b97094540006be61887400077d3258650004bf7650010007bc644c9210057c735485102f3e650c7400053d740ca500047e76d4940005fe768c5200047e70996420075c7354932006b66150020006be6310420005ff72545300073f5288540007ef324cb10004bd70d9132006fd614c8300057d7214e50006ff63d8520005fd7214d200073e3194340004bd7610420007bd74d8e210057e70d4a310057c70548310077e731432004fde624c831006be61d0320007bd32887400053d70106500063d64d4a300057d7214e510055f7354450007dc634c921005fc714cb10005b87054940005be710cb400073e4188650004fd760c4210063f6454921005fd7318221004fe768c12001e3e64142100063f6559220007df634c9210053e709414001d3d76143400073e6488450006ff614c9500075d524c831005fe76d4d20007be31d01200073f5290431004bc71590320077f7388450006fd620c410007bd720c7400053e7199250004fd7608630006fd760c621006fd760c7200067f6354920007df764c8310077661886500067d5358b51006bd3298441006fe7158850007df704c8310047d76c8650006fd6318e21007bf764ca41006ff7398720007ee7388620005be718c940007ed624c8100067d65196210057870549200379e63ccb400063c6550110006ff5298732007bf3250210005bd7318940027bd76887400077c3194320006bc7298740006fc7398720006f66188430007bf7359010005bc71503300077f5394d2003e3e64d4830006fc6188530005787054830026bf4098642027bd73106210057c714ca500057e7118d5200fbe73d00100077c6594d200073f3214140006be63d02100067f7654a21006ff3218532005fc714ca41006be6150330006de638c410006fd620c630007ed524ca210063d525824104efd628c831006fd32980310067d6254830007be414c9210075c5354a310057e710ca50006ef6288530006fc63982210077c3258450006fc42980310047c7654930005bf744ca21006bc618c540006bd644c830027bc4350e21006bc6318540006bd6250010006bc61905300076f7254920004bc764c540006fc3298450004fe7118d420057d73886500067c5358a50004fe7198d20005fd72cc5300063d64588500057b7048450005fd73885200043e7694140005fe7694e21004fe76885300066d6254810006ff721
  | 9 => 0xd73990100057c7150e5004efc3218532007f6310c62004efe620c420004fd768c430006bf644c910006fc74588310067c75d8931005f47150c100076d524ca21006bc6418132006fd72185300077f7154932006fd329833102ebc4318543005be710c9400067d62548310053e7694140016bd7610430007bc6388540006fe7158831004fd768c720005bd7214f40005fd7388710007be3150120005bf744c9210077d62cc8500067e63986500067f5298732007787054920007bf32906210053e70d4841005be71d0120005f4714ca10005787054b1004ff42118e210057e70d49320073f64549320077d6388450007dd634ca100057a70d4a20004fc764c5400047f765483101d3c744c450006fd751853201e3f601954002f9e630c740006f661886500073f32106500073c31141400073f52ccb400077f6514e210063d64140200067f5218532006fd760c4210073c3114340005fd728c520004be76c85400067f5218540006bf3258041007f4714c921006fc618c5400077d700c4500053e7508740004bf764c7400073d3294340006ff62945300077e3108450004f77644010006df764c831027ae6288740005fd700c851005ff764c8100057f764ca500047c7059632005fc714c941007fa214c030006de638c6210077e728c6500077f658c5200053e7508540007be3188540027bb60885400067e7158850006ff6398e21006fd62147300057e71988500047e76d49100067c63d4a210063e6510420006dd72d8d10004ed7218c10005fd73d4520006dc634c9210047e76d4950005bd740ca30005ff704c951006dd630c720006bd64884100047e76d493002dbf760c7400067e73983520057c754c5200067f71588500073a7014140007bc31d0320006bd62906310047d7219530004fe7690931006dd768c430005b97008540005fd728c5500057d73d46500067f62549310057e7190d52007bc73590100057d728c650006fe74588310053d75189400055c73584500057c73548500053f744ca500077c76549320067e6358a500057d7318152006de634c8100053e750cb40006fd6290631007df320c710005fc7358221006f6610c4200063e65904210063c65106200077f520c6210077d3248650005f97008630006dd76cca310073b705494001c7e76941400067d6354810004fe7694130007bc704c940005de7390a310073d6488450004bd70d9131006ff7058853005fe710c520005ff7258231007ed524c9200067d62d4b310053e750c7400053f744c6500055f73587520057d75d8132007be76885400073d6390450005fe73996210056d72142200047d72d9510007bc3108540006ff7688650007be31887400077f3258450006fc6518e210067f658c520005b970907100067f63549210077e750c520005b6718c841006b56150020
  | 10 => 0xc9210077d65d4e210067d6298450006bd6390421005bd74982310063d6414210006bf32987400047e7099632004fd76ccb510073d7214140005fc714c940005ed720c4210063d6494030007fb704c8100067f658c6200073c410c650006fe6418e210063f64d4b10006ff32982210076d524c920005fc73480100067d6354850006ff764ca10007b4410c4100047c70594210077d73141200073e64cc8500073e31941400067d62548100063c7558241007756188450006fc76885300063c6590620004fe76cc530016bf6018d40006fe610c720007be70cc8410067e53588500073f5218540005fd73941200077d71cc8500056d721402002dbd760c740006bd6488430007f7714ca1003f3661d48410077c7388650006bd6488630026bc64592210053e7614140007bc3150320006fd321854004efe620c4100063e65193100067c6314120005fd760c810006fd42181310077f714ca50005bc764c540027bd6388740004fe768c520007dd315883104fdf214c831006ff3218530007f7714c8100065f63141100053d74181520073b50941400053e750c940007bd32487400053c76d4940005fe7694d20007f7610c520004fd7298253004fd760c4500067c65cc931026be6488620006fc40987320067d6254a3001e3f7659050007df328c410025bc744ca210067f5218520006bc61d01300077f76884500067f6318152006fc618c5200053c754c740005fd7214e210077e620c4500047d7694c510067f654c910006bc63106210063d65500200053d7508540005bd728c7400067c5318552005be71cc841004bd76cc740005bd73885400072f72549400053870549400057d75d8221004fd7298e41004be76d45400067e6558031007bc618c540006bc764c940007be644c810004ff764c7200055c7358752005fa70cc9200053d76104500073d524c8410067e65987300079d320c5400075f328c4500057e73980500077f520c5200077e75588310053e750c5400067c65cc9300075d638c6500065c63d4910007ee624c810004ff76487300067d625445000ebd7610410006fd6214431007f6310c410006fc715885004dff720c420006be6310421006fd52185320057e71cc850004f7764c431005fe76d452003e3f60d4940007df328c620006ff42588310063d6454b510047f764c650006fc6418e210067d6214650006ff764ca210063c65d0130005fe7190a30005f47154a21007de314c910026be64884300073e750c74004f7d650c720004bd76d00200067f73588500067d62d4a1001d3e74c8450006be6310720005f47150e100057d76d4831007bd32885400067c76549300075d654c831006bf764ca41006f77398420007f67388710004bd76d00300057f760c4500067d6358850004fc7158232006be61503200057f768865000fb
  | 11 => 0x57f7254450006fe31582210067f654ca20007ed7388620007de720c630005fe76d5221004fc7158d200077e628c65004eff2158831005be76885400073d524ca410067c65885300053c754c5400077d5218132006dc7158c200047e76941300066c629411004f7d520c421005bd728c540004fe76d4520004bf7059321006fd4298231004fc7158830006ff6118532006fc7098632005bc714c94003d3f76d4b40005ba7008540015bc744c8300063d6454a20004fd76d47300065e63140200067f65885200057d73d8552004fd7218c10007fa21cc230006bf63d89400067c619413004fee720c720004fd760ca100067f654c920006fe4298630007bc7388740006bf7358241005fc768c5200067d7158a500057e70d4a210047d760ca50006ff5158831005fa7088520006bf7358041014ff76502300067d7318152005ff7350210006dc634c910005de7394a31007bd3218540027ad721062103e3e64d4b31004fc7654530006ff72987300079d3290631006fd3218520004ff7688650005ff735001001e3e6414020006fd7058b310063d649423000fbe7310410005bd740cb5103e3e64d4a10007bd3248540004fc7158f20007725044010005ff7388410006dd32987300379e63cc8410067d620c650005be710c5400077f3288650005fe714ca100053e75149400077d528c621006fe31580310077e6554e21005bd72d4c410067c63181520063c65501300077f63d4a210077d3214210006ff7518532035be730c8410067c658862002ebf40185430077d32140100057d760c850004fe768c540004fd76148310057f7558231006fe7018532004fb764c030005fe760c52002ebf4018d410073f52cc940004fd768ca100077d620c450016bd76d00300067d65588310063e4198050004fd7218d41006bf64d8532004fd76908500073f520c740006bf6350110027bc4359221006fe7358b510073d3294140007bc410c520006bf648c7100075f7354a31005bd7010431007f8704c920006ff6250931007dc630c520025bd7688740004ff764ca50025be74d8e210373d65ccb40006dd628c630006bf74588310063c65992200056d7294220007b940482100067d658c720006bf76500100077e7388450004bf76500300069d631042004efe6258831005bd7214d400073d64cc850005ff7388620006be63d0020004fd7690a300077e31143200063f6590520006fd624ca10005fd728c710006f661884500063d64940100077c7654a21006bc6110520007be728c540004fe7688540006fd6318221006b46108540004fd760c4100077d52cca100063e65904200067d3298050006fd70185320057d768c650006fe6358c100077e7319520006bc61885400077d52cc810005dc7354530006ff70d8931006ff32983510067d5298730004fe76c
  | 12 => 0xd73d922104ff6210c421005ff7258031036bc64cc921006fe6358810006df764cb3004ff9200c4200053f7454450005fd7390a1003d3e749835202f3d650c740007dd624c831027bc4190e21007bc764c9400073e63904500047d76908500056d72940200067e6598831007dd320c620006de634ca10005fd720c450006fe4298051004fc7158c20005fd7390810036bc64cc932006bf7318540006fd4218532004fd7298053004fd7218d540063d7418152005fe71cca210073d640c450004be760c940006fd63d82210063f6494110036be64cca20006bd6390720006fc3298351005ed720c7200073d5290631005f9700c410005be71191320073e2194140004fd768c650006b46110530006ac62d01100073f520c540005bd738c9400057d73086500053d7090450005fe76d4e21006bc6190520006bc32987400273e54d5221006fd6254a31006bd648c420005fd7690810005be76d4540006be7218540005ff70509310053f74586500077c658c5200077d528c520005ff7359010004bf7059351007f8704cb10006fe6308410006bf72987400073e640c450007bf328874001e3c6414310006be610c74004fdd320c421005b671d01100047d760c450005b97010520006bd32185400067d63544500043e761414002ebd7610431047f4410c410005fd7090b51006ff3218132006fc6188540004fd7298730007be410c5200077850c80100053d7598a410077e720c450005f4714ca210063e6458850007bf7350210004fd7298231006df63cc9200069d63904200066f75d89100057d7298050006bf644cb100057d7214010006bf7650230006fc73984210047e70994310067d52185320075f735493204ffb200c5200047d76c8450005bd7498e21007bf7350010036bc41d894302fbd760c740006bd7318540004bd70d9121027be76106210067c63d89520067c650c9310057d73c86500063d6454b31006fd6348210004fd76cca10005bc71501200057d75185320067d6394210006de634ca21004fe7198f200065c63d4951004fd72185430057d7214210006fc61d81320063c7558041004fc764c941005be768c540037be61ccb40006ff65d8e21006fd760c410005ff73480100053f7690450005bd7498a31005787054940006be6498c100067c650c5300066f621411000fbe6450c10007ed424c921005ff73482100073d5210621006ed62084100057e7514831007bc63485400073f63141400067d621403000ebc4318540007dd328c621006fe70185430047d72997100073870549400067d6298650005fd728c6210047c7059721006fc4198732007ed720c4210067e2198050005be71cca410063c6194140004be71d9132007df630c5200067c7158850006b461c8540006bc6150130006ff62cc530005bd73d4540027be6490e21
  | 13 => 0xc750006de76cc930005de7190f32005bd73c85400057e7388450007bf3288540006fe6498c100063e74983520067c63d49200079f3210631006fd73185400057d76cc8500077f65d4d20007f9700c410007de314c9210053d758ca4100fbb7050010006dd620c430005bd72d85400063e65d0020007f57388710005fc7654e21007ed720c7200063d64d4a100057f724c450006df630c520006bf6488710006fc42984300065d6394020006dd63cc810006ff628c710006bd6210450005fe73d8221006ff620c530004bd76104100067f65886200067c65cca20005fe7388620005fe71cc920027be638874004dfd720c4210077e7518e2101f3b60141400047e7099421007bf6390621007dc714c8310047d7690a5001d3c7454450006fd62cc8510055c73544500077d628c6500073d528c7400063d76143400073f32943400075e63cc8500075d63cc8500063e7619540004bc7159230005fc7359221006df63cc9210063d5258041005fc765452001d3e740c8500063c65d0220007747154a210047d7694850027b671106210057e7198e500057e718c4500077d62884500077561886500065f63d4910007f9700c620005ff7050a310053f74484500067d760c450005fc7359010005dd7214e310077e6388450006dc638c5400067c63185520065f63d4951006be32987400077d750c4210057d7398a500053d74cc450006ff70185320067e31980500075d328c6500055d73c8450004bd760cb40006fd635881004f7d520c720007f47388510005fc73885200075f52cca31004fc71582420057c754c540006ff764c810006dd63cc850006ff41588310079f320c7400063e61943400073e2194340004bc71590300073d7214340006ff6458e21006fc6188520005fd7690c10007dc314ca10005fd728c540004fc76885300067e650c4210067d6354a210057c73484500077c3188650005f970884100057f7688450007ed21d8e21006ff32987500073d7314140006ff624c8100063f65906200077f3248650004ff7650e210066d624c850005fd7118132006bd64886500077d76cc850007dd320c410007bc4158031007bc61885400057c7158f52005df764c831006bf7098740005fe7318221005b970106300067e63140100047c7654940007dd328c5200077f525803102f9e7310431005fd72d4e21006bf321854000ebc4218540004fc7650d210067e6358850004fe760c520004fe76d45400063d6590720005fe7118d20007bf714c940005ff724c5400067e63d4a500053e7518940026bf60885400053e76d49400075d320c450007bc738854003e3c64d493104dfe7298031006fe7158a30005fd72cc520004ff7648010004bd76104300053e758c841005be764c9400073c6454932006ff73185200073c63d494004efe760c720005f
  | 14 => 0x7bd71ccb400073d524cb40004fd7614e210077e7314120005fd73d8520004fd7690b510077d750c720004bd7690430006bd644ca1004fdd630c4210063d52987400063c6550220005ed7214c21004bc764c9400055e73c8450007f631887100063f64943100053e7598a410069d63d0020006bc73582410067d6358a50004bc715922000ebf60185400067c6194120005fe73982210063c6510520005be71ccb40004fe7118d200075e654c8310071f5394e41006fe6398810005be73087400067d7614320006ff6398221006dd630c42104fdd320c720007bd73185400057e7198a5004fdd320c420005fc714c951006bc610c540007bc418c720006ff768843001e3e6414010006de638c420004bf764ca410077f6514d20004ff7258c50005b471501100079c638c5400057e718ca5004eff21185320057e71cca50006fd65d8e21005ff76cc810006bd6350210007ed628c810005fd708cb310077e63886500067d52185300057d7294210005fd720c410007be64cc810005bc7388740006fe32980310057d750c530006fe73588500053e758ca410057f754c5200073e644ca500057f72586500057f735865004eff2018d210057d72940100067d6354b510072f5294a4102ebe640c6200077f524c8100063e76141400067d6394320027bf76887400047d72997300057f7254c53007bf744ca10005fe7390810006be63d0320006ff73185400073d52cc841005fd720c620007bf744c810005fd73d52210067d53588530067d6254a310057c7558e210077f524ca1004efc620c530005dd7314831005fe71d8132026be64d9221035bf76ccb40005be71085400073c6194140006fd32982510057d72cc650005fe714c910006bd7218540006bc63105200067d5298431005b970107100047d7694020007be71ccb400077e73d9520004fd7218530006fd760c520007bf32487400065c63941100077d708c650004be76cc540005bd740c8510077d3288650006fe63c80100077c31941200077f3298450005fd72d4d20006fe760c520004ff7258f10004bc7648540007bc3188740006be6458810005f4714c9210047d76086500063e65107300067f65185200067c6194140006fd3218550004bc7159050004bc765454002ebf42185430063f64549310053d74c8650007ed3288620004fd72980310063d64548500053e70d4b40005fe73884100057e73908500067c76549320077f650c5200067d624c450005bd72cc740004ff7650c10006ac6250110004bd76c87400053e71990500057f7254f510057c7558332006fe735881004fdc3218532004fd7688450006fd628c640005fe76cc5200053f7558241005fd70ccb510053d7690650005fe7190c100067d65987300067d62942100057c7158c500057d764ca50006be7318540005fd720
  | 15 => 0xe70d48310077f3214210006df3298730007bf6310621005fe7319621004bd76906500067d658c710006fc7358850006fd7218540007be6210431004fc76485400063f65501100047e7614120005fe718c520005fd72d47300067f7654a31007bd644c81004dfd760c421007f6310c6210067c6550931005fe73d9520007bf744ca21006fe7058831005fc70549320063f64d4951006bd6290450006fd624c730007bd74181320077c6354a210063e6590730006b774984200067e7358a50004fe760c1200057c7158850004fd768c810004df764c030006fd42983510067d658c431007fa104c81001e3e6414230006fe7158853006bd6210430005bd7318540006ed7688420005bd7218d400077e70cc850007df714cb30007bc3188540005dc7150d32006dd630c4100047d76d4b1002fbe620c74004fde630c4210077f3214010007dd720c630007bf32485400077e71588500063d6454810006ff321852000fbf4390c100079d328c540006fc73588100067e650c4200063f5258241004fd7608450005df7354520005f47150e210063d6210450005fd7399621006f47398420006ff624ca100077d720c450005fe710c850036bf60cc940004fc764c951005fe71ccb1003e3c64d4b100079f3290631005ff7258c10006bc61d0120027ae7210621005fb704c810005fe718c810006bc63189400053e7014140005ed728c4210057b704c850005f8704c920006fe3158021004ff764ca100067e611433004dfd720c7200077e7394120005bd72cc540004fd768c4210063f64549320053e70d4940005fd73988100066d6254b3102dbc744c831006fd628c650006be32185400067c63141100073e418c4500063f6550120007ee720c62104f7e62d4831005bd72d4f400069e6310420005fd72980310069c63d0110007bc31d01200067d6214010007bc414ca1000fbe73990100073c3194340004fc7654520005fd76cc8100057d720c4500057e718c850007bf3210621004fd7298051004fc7650e21006dd630c621005bd7498221004fe7198e50006fd62cca10004fd7690a10007bf73185400057e7518e21006bc73185400063e6550020006fc7158831006fd3298430005fd7090851005fc7388710006fe10588310066f62d4910005fd700c931005bd73085400067d628c450005fa700c5200067d621423004f7e650c720006fe32983310057c7150d52004fd7298353004fd7688430007f7318c520006bd62d0210006fc764c810006fd628c4300073f63d4940006fd6250a31004fd7298351005fc7354a210067f63549100057c75582210067d62d48300057f7258450004fd7218d40006fc764c910006be6458a30007dd328c710007bd3210410006bc3218540007be74d8e21005fe7318520004bf70590320073d528c5400059e7398a41
  | 16 => 0xd00200909f00002d10d02a00800604307201066a0000033e400700303b1f601701787801300700100001d01302177a00e00405200000002200900356702408e0f600000300200003c00000200503000000d00003204c01900500500200300223800100228300401407f16e01000700200c00200219f00000b02500000700e0000065990294a400535900502701a59700305600004904405a3020360000160527a00190fa02350e02102a00001503100000200202e01104b00e0040320050210070063a805500000a00c0c400000001729c00f00054c0009a302304d01f0110140810ae00c05804503e0070da00701700700c02c00b15200700600701f00100800000000400000500b0f501501f0020120c701100506400e00002300000200100e09800801d00d01500001e00400202100e00125c03b01e00b00502245900000681949003f01300000000300003700b00200000f00006d01793800201501c00d00400807a2ce06a00202700015a0210100010020a703700402200001100000000104000100001000200413101400f00700300a00003d1b005800000702701f00b005fc7058732007bf7388740006ed624c8100057f7558221006ed6288730004fc7158c520073d5288740006fd628c7300053c7159050006fd3158831006ff614c9200047c7654931005fd7319520006fc6388520006ff40987320063d52984410067e6588730005fc7359621006bd6250210007ee720c52004fdf320c421006bf63906210063d64d4b31005fe73d47200063c6590520007ef324ca20006dd3218530006ff70588310063e6510720005fc764c520005fd70cc8510067d624c650007fa700c5200075f5394e21006ff4298031006fc6358221004bd7610630006fc764c920006fe7318520005fc714ca200063d64142200077c3298450004fe71d81420077c3108450006fe63886500067c63d4921004fd7218151004fe76cc520005fc7358810007bf74185320076a50c8220005be73c8740005fd7298c100067c650c620007f7714ca210057d750ca31005fe710c851004fd7608410005dc73545200057c7154f52007bf644c92104dfd760c720006ef624c910007df328c621006ff7398642005fd720c530006fb60982210069d63500200077e31884500067e7619520006fd62884500073d524c9400063d64548300067e63d4810006756114020006fd62d48310063d6458a50004bd7690450007ed7218e21005fe7614e21004fd76886300079f744c831007f5310c5200067e65588310077c6594e210077d32986500067e7358850005fd700ca310073d52104310063f64d49210067f65185300067d624c850007dc314c91004dfd720c4200053c75582410067661140200075f5394d200077d7388450006fe63084500077d52d85320075f524c8310057
  | 17 => 0x301505a00000000000000834005006400e00000200d00000802600404000400c00000300300200700e00600400000e01c01423601200004c13e08000600b00000300400500200026c0000d601101200a01b08c0260090000930236a600000001b09700306001400100500100700800500a03400200000200418501104800002200080e0620080411d900400600000101831500210b00b31800600300200000100109b00017902a00d39d00000000700000100302300305304403200100102200000000000d0de0000080f100400a1a900000505a00000000809f06140a02500400d00e3c800000115a00045f02300000000402401104601f0012700010040c500000101401503300200d14709201200a00500203800200102a03903041762754500904a1bc0bd00001700000167d00003200802302d0ab0700050781dc0f300100601500100000001a00b01400f01e03a02d0070046d600800f00d0ae0020420080680580020a300707304f08c0010000050000491b800900002800003c0410d501000c00b0b500b2060000094f24d300011501100100f02004803700501000000a02e00100203a0000029db02f22704207201800200000008d00000801a0000cc4fd00b0030011ec2820000034790390e300801700b00702e00a09d0010000060090090010011e902c0040040050082e783b00000c0050020aa00000602600000300700e00800d72100001b00000903c0000470060020280020070131840320052c8439020002a430100003c300a88100600005005b02f0030004f919800127801000001302031f03200329201c01000008205301800100802d00501d0040000080d600a0c102329f00000004300003600b00318a00901a0580390020e30d100500000e0020b30090862440010c629504300200000102a06f0020010100043400040000000160040381870910100010000050020100c165a00907906a0060000180000000002570040e500002204f00d01c00200500100139084302900300200100a01500b11400b10000401101c14a00b0210960bd00a3070010190030bd0000060050060150472aa00500700106300101700b0000000021379170e218200f00e00000300300000602201a00d00100402e00014d00b01600802107a00000101900000000200203e00e06602c0074ab01209b01700000400000006f01b02506200055600d0050004bf00000300314e00104a06501604a01803504102100302d00300001e00400403200400002500116a06500f01400000503b01b00000b6070000070000010bb06700305a0000bd2ca01202b02401800300d00200000012c0570df02c04606d00500701c0000a40a300400000000217600702148900300001400000b00e00200600002400300b2fd02800408202a00000003d01804a03203
  | 18 => 0x3f0005000000001
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xcbe645c83104001aeb0a38a65080038f5d47418532006afb9ce7108a000d6d755c83108401c7908b12a4188031f5cf715885004f6b990e73084000add87588318c001c730c2828190027f1c85320c6210065ec1aec208200097d821cd51140011fd0e18ac1108035b9d5720c7200072fb2ec718a4009cee625c831140016bd01a966518802b760a638c650006d6b90c518a8000aef824c5620c4131fd0fa0ac4188273b989720c6300055ec3665a002000e3c6318450500018fb06bb042280038f5cf5218540004df438829924200e3d7699031140018fd073b4a09000317dce7358850006bd3aae018a40009bf825cc50500018faeab1ec110803a7dcf3298740004be43aa4b046200c5d7318c6054801b5ae420863900025f60a750c5200055f43063a024000ade81dd932cc013f886438a6490802afa0473185400063f32ce710e2000ead8218621500014ff04b1ca108003a7cca610c7400075a40a6430a8000d6e835c8500800157d0fb2264908034f213764ca500055e40a64b008200f9531588410c4015bb07324c608003a7591634c8100065e43ac42086200a7d86cc850840018fd02bb042280031f594714cb300071ec2ac42086200cbf76cc940040019e8e2b0a6598026b760c74588310055fc12e630a8000e5e634c850040011fd0fb1a42900031fd9671d8d20006dc3a0e099020009be86dce21500015db0531cc4080038fd4b329874006e9ebb0632868000abd8298c41040018d2c4382a4180032f21a71191320056ec18853086000cbc761c532500019eec438a65080031f58c7054a210063ebb2ea18842008fe861c1524c8017690299242a0003675cc7388740005b6402a49944200c7e8758951140011ff0eb1062280023fa07764ca5000718b08a0a004000f973210431884018ff0db9263280030e99570107100071fb22a430a6400abc8158e41c8001e3ea5990821880379588714c8100055fc3264a04200097d869c3520c401abce699442280029f60a75185320071fa966430a8000b74814ca61940014790c994a0a0003ab1d1624c81000576c14c69042000bad828c421500012fb0d3886428003e5104314c9210063ec32e429ca000cbf825d8410c001cbd06328c69002797549630c421004de40ae431a8000cf7615c83148001b38e699243a00031f209760c45000537c12e6b10a000db9325c241040018faecba863900038edd850502100043ec3cca18e200097d821c1650c40157d02320c0990037c1c6104c8100071ea966530e8000de5729c46388401c7cebba0c2990033758d720c410005bb40865308a000ced821d9438840137b0c39c43a000f0e1d850501100041f43ecab244000e3c8318450500019bd0c39aa2900038f58a418c450006ceb9e6510a8000adf8258c3104001a7d0ab9062a0002bb60b4058831
  | 1 => 0xa6418ca1a00035be0d7214020006dac18e2a022000cb471185404c001add0ab9063900038f98d629045000756b22c49902000adf87588318c001aeea438a64080032f58970106310063f3b6ca29a4000cee615c831084011ff0cb9842080031fdcf715885004e6e992ec1884000cbf761c5329040197b04bb082080032fa0c7648540005bb40e65108a00097d878c421140011f90e990c2a00038f5cb52185400065f31ae020c4200eb4611063148001adae5a9063108023fe1973884100053e40ae6b10a000ed73218431480011fd0f194c218002db60831141200071cc00c22828000d39625c0411400187aec2086228003175d9320c6500063e39ac4b08a0008fe87d85324800197b023b264a00031f9d772185320053f430e0a926400abd869c33210401c7d06b1083280029fe1570185320049fc3a6420ca000deb805c831480139eaec39c4388003abd8f6288540006da3a0e29944200d6e729d431c8001968e230a8090003ab58932104100059fc12ea18e8000c6f865c85008001b68e320a6508002fa201524c9200074e3a4c69944200e5d654ca31c40138fee532863900031f1457218d5104e76310e29922000abe864c861500018fb04bb06228002cf61c63141400047e43ec498a8000abe8118f40480018fd063b2a4900035760873544500067dc16ec9806000a3f864ca50d0001cdac4a926508003d3e0d524c9200077830ce018a4000cdd7398f20040015f300194c0288034f61c31143400053e42a62b106200d6e755c8638840197f0d38e81900025fa047358850005dcc008218a4000a7c80548614c8016db0539eca900031fe0e76941200074e39e6530e8000c7e7358a2114021a7aeca9063a00032f5917388620005ba40a6490ca000a388054960104013790e9928108002afa04764c9400078eb98c62828000c75711c562140014fb0e3286310003ad608610c5400053ec14c730ca000e6d821cd6214001e3ae6b2882188029fe1b32984500051f40cc8b10a000a7f864ca508400137d03ba26408002afe1932487400055ec3463a064000cbc649c4604c8017730020ac0188033b5c9620c4100055ec10c630a8000c3e7618f5250001b6ee9b8a6408002af60b73987400055f4386430a8000ea5821842150001abae799443280026fe0973d45400065fc32e418e8000a7d85dd0614c801a7ecbb9c42a000e0f21d65503100073641ac5908a000cbd825db40040014f902b1ac4280023f2057298e500057a4326218a4000a7e868c450480016db0518843280038f61073588500075b418c220a4000e5d624ca319400167d03994a1a00039798d329865000576c1062b004200cbd641c53288001c7ac8b1463280035798d728c6500059c402a510a8000d6d835c850080019bec6b9062900030e58970104500063fc0aec190a000
  | 2 => 0x8714c8500072eb1264188a000e4c8358932140135dd04202c41880357a087358450004dfc3a65a042000aed82105620c401ce902b1062280032f21172185430069f42ae418e8000c7d7258a31140014fd0738ac42802737dc9630c420047cac18821882000f94410c532840014fb0432a84988038fcca61143400066f3b66418a4000cdd765c8318c001d58c631442a000357dcf324865004eb6b2ae4188420097f865ce219400157d03992c0208025fe1d63084500047ec3c20b106200e5f658c532440018fac538e64280031f1cd6254450006d6b948218e4000e3c64548614c80707f0cb8083280025f21d32986500066fbb0e29966000ed463184314800157d0f190c2a00034f9d5720c7400053e40ac72864000f398314140c80014fb0bb80c29900397194638c5200074ec18c218a800bdb58710431040014fb0c39c4228002afa127058831004dec14e231a8000af781548614c801cbaebb186290002f3e0931588310043fc3ac4188a000e3e75dd1620c4018fd06b90ca98003376187354520005f2c10e710a20008bd8718c4148001b5ee431262a00030f9da31141400075b418c210a8000c7e811d9524c0018f8ed32aa7108030e5907054a20004bec3cc518ca000d3c73d4a21d0001aed0a38a64908032f2137650c100074e4326418a8000cbd645ce210400197f04bb082080031f5cd62d46500065eb20e29902000a7d869ca31940018faed3a8639000367e0d70104310051f40ec8a926400e5f654ca3148001bacc638a64080031fe1d62cc4500067a38ec2992a000f3b731414084001e3ac79948228002af20532987400071e3b2a49928000c7e635c85004001a7ae5188a0a00038fdcb521854004e3eb14eb3106209cee621c53204001a7ccb39c43a00031f5cc705885000636b92c418ca00087d87194314800187cecb90a0a0003ad18431085400072e28ae431aa200e7765184314800127f0e9948328002cfe0963904500055f434e518a8000bad8218621500014f100b9ac4280031f195720c5200063ec2aec18e4000c7c651ce218800197f053b6a2a0003ab188618854004d6f43cc69944200b3e8118f525000137f04b98c2a0037c758c3194340006bb10cea1884200e5d654c9600c40197ec938a64880032f5d8410c7200063e41ae432a60008fe8798d20840018fccb38e65880026fe1a71ccb400063eb10e0a946200db4641c53248401cbaeab1863108031fdcd62586500063eb14e1a9062008fd87d05620c40197eed32264080031fa15760c720004bec3862286400097d82dcd6194001c7ec6308a0a0002dd205620c450005da40a6420c4200cbf645c4604c8016750e28281080027d61c3108410005bc402a418a400097f825cf51940018feebb1ac1108027de1d310c5200055e40ac6a064000abd831886150001e3
  | 3 => 0x2322640ce9e64cc83188001a7acab9063a0002ed600410c621007b4a90e09924000a7d829d8311400197c82bb06210803c7cc8410c4500063f3b4e4188a000c7f731c1621400197ac9b9c4310002af20532185400065eb22e51882000d3e735c8505000197ce730c43a00032fd9270d85320063ebb06210ca000c7f631c15288401c7e64308a0a000a2f21d63503200065fb18e2a024000d6e729d43108401d6f0430862a0002eb60a31087400047f43865308a000ece6398932040012fb0d39842280023f608764c5400069ebb665208a000b788054b3204001a790838a6528003cb54932106210078e41aa499680008ff865c83114001d3cc699082080032f9d8618c54005f5bc00c218a8000d3d521c532104017cb05b9c43880030e59070548100057a40a6430a80008fd8758b51cc001960c2b808298002cfa1b528c5400053f41cec32a4000cdc631c532440015df04882c4188025f61a71cc850004bfc3ac4188a000abf864cb40840016e902994a1080029fa0473588500069f32ce39968000cbc869c4325000157b0f31882080029fa006550931006b6b92a418c4200cf9701c1620c401be0e288264080036edcd40482100057a40a6430a4000c7d75d8f6088401aeaa438a64080039d5da61886500056f40cc6994a000aed86c8763884018fcedb2862900031f615760c4210047fc3ac631c4200c6d7258b51940015bb0431c62a00036ecc970104100069e422e531ca0008fe861c532440019f6e1382c418803da201524c9200065ec30e2a066000c3e769cc505000197d0c38a80980030f9d863141400061ebb482188a000c7c811d952480019dae4994c198802bee0132980310073a40ac5108a000d5e738c4211400176d0399242a000357dce63886500071eb92a430a8000c7f7258931140014fb0c39c4328002de201750c7200072f32a64b006200deb805c85348001a78ea31262a00032fd017298e50046da218e2a182000c7d865c85004001aeb0a38a65108031fe1976884500055f40c6530e8000e5c63d4a3148001d5ac499482080029f60e7058a500065f39ae030a8000cbf7659132840015df04b0a6528003cecc85050210006b6baae418a4000a748158d6114001cbaeab1862108033edda214c03000576c1062b044200eb78318441480138fea43b264908031fa157298e500074e41ac8b182000add83d01620c40187cec308a0a00039d5c47158850057d34108218c42098ff865c8318c001b3a64b8082188026fa1c414ca100053e42a20b106200c7d865ca508c001d3f06b22c608002e7219328c54000676b96c418e2000e5d7558c6388401b6ee838a6408006ae60072185400043ec14e13286200cb9625c0418c001e58e8a9265108038f1d864549320072fb9ce6b10a000e3d73548615000197d043b262a00031f61
  | 4 => 0x8400157d03190c2a0003c7cca31943400071f40ac4208a000cbd731842150001c7aca3a2c41880397e0d521853200756b1264a002000abc844c5620c40197ce8b14c0188022f21d644c8100074f31a65a042000a7f8258e601400197ac838a6418002eda0732106210063f40aed210a000b3f825cc50500015f300190c0988039b60d62548100077830ae018a4000cbf831c5640c00197ac9b92c6080033d1c7614c940006cec3e6518e8000e3f65dcc61500011fd0e18ac0108029fe1d535885000774b10e09902000c7d851c56214c010fb0e32862980024e20175c8540007a7c1aa49944200af681d8f6148001a7ac838a65280029f60a63d4a100072fc1ac4188a00087d829c3654c401d38e931a64080031fddb524c810005b6c106328640008bd869ce21d0001b3ee799242a00033b5ca610c7200067ac30e29942000e9c415c86354401b3a64b8483188031fa187054932006aec18e0a966400bad820c540c80019e8e2b0a652800367dd8744c8310073bc0aa430a6409ecc620c53244001a7ceb39063a0003d3549328c5200071fbb2a49948209c7d521c563148018f902b94cb880032f5cc61885400059ec3665208a000abf835c0615000117b0e190c2a00034f9db528c540006cfc3a6418a8000c7c76d963148013cbaa4b1863900023fa1e63886500065ec1aeda002000c7e631c56214001cbf06ba8c299002af21932885400065fc10ec98a8000cbf749c0614c801b5c82b906210802ed20532487400054ec18e430a8000e77719c562140017690299483108039720d620c4500065eb9ec430a8000add8298e310400197ce8318c1108023fa187354920006cfc0ae631280009bd829da31500014fd0da946290002bee014218131005b4402a49924000cbf641c5324840197ec8b9c43880036d1c431501200063fc3ac4188a00093d829d431d00014f900a94c3990029f6183108450006da418e2a062000e3d831845050001a790ea926420802dda0732486500047f438ec9902000d5f874c831940015df04b80c299002af21d6350210005bd406a518a4000b5c80549320c401a7ea438a65208033da0776884300065ebb48218e4000cbf641c532c4001e3ae7990a0a00031f9d663d82210063f3b2e4188a000f67815493288401adae531062280035ba15720c4210055cc00e830a6400cb5871872150001b6f0838a64908025f60a750c6210063ebb2c6108a000c7c815d83214001cb906ba8c2990031fe0d7608450004bfc12ea18a6000abc815913294001d6b0630e42a00032f1057218d510063f39ce2b14a0008bc865cc2150001a7cc8b9463280072fe1871503300066ec3ec731c42008fe811d932500014fd0032e64988029f219520c5200071f3b0c62828000e9f735cc61500015bd07b2ec6900038fdc952185400365fb14e
  | 5 => 0x29fe1971cc8500074eb22c69942000cbe739c86150015f4b042086310802cf20e21143400064ec18ec9928000d3e641ce211400175b0518c42a00026f205740c8510053fc326530ca000cbc76d8e2150001c7d02b148228003291887150110006ddba4209902000a5f835c56214001c7d02b108328003c71d2634ca5004f6b994c21884000e5e8358a31940011fb0f31e41080033b60876885300072eb1a64b0ca000cbf73dca61d0001e70622828190002afe1d32185400065fb80e630a8000cbf645ca31c4001c7f04308a0a00039b589329401004f6a990e73084000bb4814cb40840015ed03994c228002bd205329822100774b16e09902000c3b641c152c400197ac9b9ac4080030f9db6314140004bec30e2994a000b3e8118c5050013cbe6532863900039758d628c650004dfc3a6420c4200ecd624ca31040014ff04ba8c299002afe193288740006dab20e29942000eb56210431040139d8c4b9062980034f5d9750c7400071e41ac4208a000c7d87588319400167b0418ca1a00031f6147158c5204f67312641882000e9f64d8d32484014fd07382c428002be60262980310065eb90c318a8000cbf764c9400400197b0438ac8180032fe18714cb40006bc402e4188a000b2982141400800197ac8b9463100026f61c31085400069fa94e39908200cde73d8c614800117f0cb9063a0003e54c8410c621004be432ea18a4000b3d87d4831d000197cec30c42a0002af618315032000736b126490ca000a3d86d48410c401e38e8a9264188032f5d06118132005bb40e64b08a000cbd7298631d0001e3a6520c6328003cb54932906210072ec1ac418ca000d3d521c5329040197ec1388c6a00035b9d5720c5200065eb26e71082000ed76318431480017690299442a00035b54d7214d20006eab986310e2000e3d62d4a418c401b5ae420862900032fd8d7218540005ba40a642802000c7f825d831140010fd0eb126228002afa0732987400053a40ac4b08a000d9f874ca410c401c7ac4a9083188036798e71ccb40004be40ae7314a000ade83d9763884014fd0c39aa4900032f9d063982210069eb22e710ca000b6d820c6211400157d07b94c3a0003ad20c61105200053ec14ca18e2000c7d63dc9619400147100a90c2a0002af21d644ca200067b398c310a4000aed861ce2108001aed0a38a65080031fe1b7258c500065ebb2642082000a7e80196424c401c7b04308a0a00025f61a750c42104ef3c0ae418c4200cbf76dd132040018faebb80c2990039b60d62c8450004bfc12ed18ca0009bc8759132040015db0db9c4210002a7a0c72185400049ec38622828000abd87cc861500018f8e738ac4280029fe09658c7300071ea926530e8000cb6861c54044001cdf06b1642280271fdca650c4200067710ae531c2000bb4814c94
  | 6 => 0x74e990c218a8000c7d769cc50c80016db0418843280031f9d9731412000736a926430a400af968310431884010fb0d386a4188031f20572195300074f20ac618842008fc815db32140018f8cb398c2900035d14c7154a210051cc30a0a004000cbc76dd1328400175b0418e81900021fe1d53588530063eb92c5988a0009bf805d032d4401e3a6518ca0a0002afa073218540004bf43865308a000abe81dd932500016e902b144228003a71cd3298740004f6c14e72824000e5e63cca611400157b0531e80080021f60870594310065e320e710e2000e9d7318c4188401cdd02b1464280027d618714ca100061eb94c32868000cbd821d931500018fccab9063880031f205760c4500053ec28e030a6400e3d524c8615000197ee630c42a00038f19572185400067bb10e29902000c6f7258961940016db0518c4328003e5cc8410c4100078fa966418e8000cdc639c53244001d38c630c62a00034ecc97010450006d6b948218a4000c7d865c850840018f902bb042280039920562484500055fc12c72082000a77815cd621401da7b0e20863280039d58d61886500055f41ee130e8000e9d3298431d0001a7ea538e6520837c760c410c6500055ec14e630a8000bad8718a215000176d0399483108036758c73887400061e3b6ca99280008bf874c861500012fb0e188a090003ab9c9621043100636b92c5188a000d3d529c732104011ff0eb18c1108023f21f6254530006dbc20e29942000d6e855c831480015f50030ec099002bee19104c810005bdc02e4188a000e5c65cc831880014f902994c0280035b5c9321401000737392c4188a000d3d720c650d00138fee532862108036be11720c7200071fa926430a8000d6d755c83188401c7cca3a2c4188034e60c70549400063ebb2e0188a00097d87d94314800157908b82c418803795c8610c5200066e39ec690a4000a7d860c650c8001978ec31a42a0003ade0c6108540004de40ae03226400aed82186214c001979023b264a00033d1c5614c8300069eb22e518ca009d6e655c831c80019ecec39c42880034f990714ca500063f3b4632824000c4d7358b2114001a7ee9b8a6528002eda073248740005ba40a6510ca000b3e81993321400167b0f990a0a00038f195731854000576c1080b106200adf864c831040019f6e1380c299003cdd48410c6210066f39ec7b044200aed82841620c401adceab906210802afa1f32185400077240ac51082000c39641c1520c0018fcebb80c2990038f5d764185320055ec2065306a200bad820c4215000197cec31c42a0003a79cd32185400074fb1c8218a4000a7f8754d62d44014790ca90c2a00032fe0976d00300065fc18e2b244000d3e768c45050001adceb39062900034fd48714c9400062e39ac6a88a000c7f765493204001adb0ab90639
  | 7 => 0x3e835ca50d00011fd0db8aa4990033b608768854000767b14629922009cf5211c563c8001d5ac499680080026f61c63885400063ebb2c7108a000a7d828c660140014fb0d994a1080025f608755803104fe2108629924200fa5721043188401a7908b9062280031358d721402000576c14e6b142000a74815cd6214001af306382a4900021f21d624c450004bec3ac518ca000cf5760c421040018fb0cb94a0180032f1db63485400066f3b26418a4000e7465184314800137b0dba265080037c600714c8100075a3086310a80008fc8758d2004001c7cea3a2c4188036ee0d7010410004dfc3ac42086200db6831c540440012f90e99242280029fe0965580310063eba8e2b106200ab6811cc61500019b8e6b1c4208002afa0474185320063eb10e0a906200f4d524ca318840157b09b08c2990032fa04764c9400062fb9ac4a88a00097c874c96194013cbea431a6490802af61b32502100063f43ac4188a000cbc845d831c800157d06394c3a0003cd548410c6210063f39ce2b10a000d3d64dce21940019dae5b1462a00021fe097694c51006da3a0e29902000a6f8254d6214c01cdd06b1642280032f1db714ca410072eb1665188a000abe868c540480012ff0cb9062280029fe193214010007573b6c510a8000d9d730c621500019f103bb260180026f219728c5400065eb12e020862008fe87d8532500012f902bb265280039798d62cc850006b7b2ae429a4000c94631c54044001a7ee838a65280031f618714ca500053f40ee6b10a000d3e731062114001b3ee739c42a00029f61f52185320071fc22ea30a6400d76851c5328840197ae6b90c2a0003b38c773d8910004bec16ec188a000e3c65dc861500012fb0d3a863900035edcc70549200043f43ac498ca000abe84841620c4018facbb82c4188039b5c9620c4500063e3b0caa9a4000e9f630c54048001a7d02b90a0a00032f219720c5400072e31c622824000cbf64dce21c4001c7ac4a9483188031f5c9620c4500063f43ac4988a000ed532184314800157d0331e8190027d30c95218532004df43e6490a8000abe84d8c638840197cc939c43100033de03764c4310078f31a6420ca000a7e81d8d52480011ff04bb46218002cf20532904500045f43ec89962000f1d524c8410c4014f90ca98a710803c7d4932904310047dc3ac03044200cbc84dd9328400187ced990a0a00032fd92714c921004df436e690a80009bf874c861500016b900a9665188031f5d83108450007a641aa49924000d3d7354a21500011ff0e990c0908031fdd9620c4500053e41ae2b10a000d3d521c5325000197aed32664080026fa1c63485400071e41ac5208a000e74815896114001cdf02b1264280038f9cf521854000636b92c5300a000f2d524ca21500011fb0e194c1a88034f5cb528c5400
  | 8 => 0x39944328002ad2053298740006cf39a6510e8000f1f524c831500018feca38a6510002ce201521854004d7641220b106200eb66110431c800197cc8b9063180032f99271cca200047f430ec18a4000abc864cb61500010ff0eb1ca0080032fe18714c940005bb40e65308a000c7d769883114001c7b0a3a2c4188038fdcf52185400059e40a642828000b388054a315000175b0518c43a00029fe0963940100065fc3ac52086200c7d765d43148001adceab9063108031f1967118d200065e410ec98a8000db5641c53204001ceea430862900030f5da640c4500063f3b6a418a4000c7d635ca5084001a7100b90a0a00022fa077059032006ae398e2a926400b5f82595320c4016f100a9264080029f618714ca500078eb28e89906200d3d729063114001a7ae4a9462a00030f5d8410c6500071eba8c830a6400daf845c83108401b6b0638a81880029f61e650c7200056f408c69924000e9e638c740c8001a7906b90a0a00029fa1853549200065eba6c73044200d7773dc5528840197b0638ac8180025fa077258c500065e3b0e89924200cbe641ce2104001f4ce42086310803975d9320c450005da40a642082000e3d6210631940018fb073b4a09002b6d1907150e210057a40a6430aa000abd86dce21d00018fd0bbb265080031f1d463582210065eb20e29942000abd860c740c8001abee7b8aa4990039d98e61886500053e432ea18a4000e75625862114001cbae7318a1900025fe1d5314d20005bbc3ac3108a000cdc73d8e21480014fd0d18ca090003675cc3108540006afb9ce710ca000dac415c83188401c7a64308a0a00038fa0d62104500072ebaac618e4000c3d721865050001c7ced990a0a0003abdca72185400071e39aa530e8000abe86dc532500015bd0c18a6488026bba0b4158831006aebb26518ca000bb4814ca21d0001abae618c4328002cfa0732104500047f43ec6b044200bad820c5404800107d0fb2a81100029f201654c8310071fb1aa520c4200c7d859c76348001adb0ab9062108034f615720c7400069f32ae418e8000cbd73dc8615000197b063b242a00035721d524ca310047ec10e2b18a000cbc74dc8614c801e38c7a9462a000397d8c31941200045e43a6430a8000af6861ce21440019bce2b90c6a88032b5c87218540006d620ae41884200cbe731c8615000167d0d188a0a00034f1057298e5000726b1264188a000a7d8298c50840019bae6318c1108023fa1e634801000676bb2641902000f393214140840139d8c4b9063880072fe1871503200051e40ac8b10a000cbc874c9609040157908994c2180024f61c31143400063f40ae432a6000cbf741c5620c4014fd013a8c2990031f9d8650c5200075b3086210e8000c3d7658e41140018bb0c39aa2280021f61c650c6200055fc12c6a002000d
  | 9 => 0x76084500071e32a6430a8000eba80cc9601040157d0f194c3a00031f19673886200065ec12ec2086000d9f325c0418c401dcac5b8a64080038f2056210450005f340ee710c4000a7f8259631c400157b0f190c2a00031f19473885200065e31ce23128000f1f654ca3150001b3cc6b9063a00032fe0976d00100057dc0265306620087d861c1520c401e3aca99082188034fdcd52885400069f39ea510e8000cde631c53294001d3d07324c6080023fe1d329825100676b94c53006200ead721c86150001b6f0638a80880035d614714c810006b741ae52844000fb0415c03104001add0ab9063108030e19570105300065fbb0e6a042000c65725845008001870cab8083100031f20d729971000736402c4990a000c7e769ce50480135bd0d18a6490802d721531588310065e3b0829924200e3d6358a4114001c7d0839ac4280038fa0d62904500063fc36e4b0ca009cee625c8310400197ae530863a00031f99770588310063e43ac4988a000e3c845cd62940017cb0439c43880029fa0463d49200072f314ca9906200d7b805c83114001c7ac5a90821880357e0f725943100576c16a2b106200c7d635ca500400197887bb2871080297e19524c83100772b90c218a4000d5d831c1524c8018feca38a64a00033be19720c720004dfc02e8194620087f87594658840197eec3a264080021f6187388450006ba398e2a9442008bd8718f40480018fee4b12c228003ab5c962104310057a40ac510860008fd8790a6014401c7f0ab98c2a0003cd10431884500055f408c631280008fe869c532440018fb0cb94a108003c7993320c450006b73ace418c4200e5c8358a311400173f0e99063a00032f58c7150320006dc18ae010a80008fc865ce21480012fb0e18ca190003575cc31086500073aa90c218a4000dcf724c9600c401978e9380c2990036d210714c9210053f43ec6a924000eac7618a215000187aecb2062280029fe1973886500055ec386430a8000cbd74d8e63884016b900b2a64188032fe19701043104f2f994ca1884000e3c855cc6150001c7e6530ca1a00035b54d7214e210074fb18c318a8000cbf845d831084012fd0339c84280029f60b658c540004bec16ed18ca000cbf73dc261d000157d093aac4188038fdd352185320065fc20e2b1e4000af686dce2144001a7ea538e64a0002eda0732885400063cb10e0908a000cbc76cc921500016db0418ca0900031f18e70d4a2100676b92c53006200bad820c421d0001abee6382a499003f14c5720c4210063fb2ae710c4000db7841c5328840137f00ba06428803a7cca618c74000636b92c42802000adc83548614c801bccc438a6408003a560c610c540006dc992e02082000c7d8758a31940014fb0eb106228002afa04721854000737b2a6510c4000cbf835d841040016ed
  | 10 => 0xb106200df371dc13204001e6aea2086310833a7193320c71000637b92c4a88a000c7f865c850840018facab9c43880032fe0876485400066e31ee0992a200cbc845c863544018feca38a64880025fa07764ca500073bc0ac4188a000d387114140c800187cebba0c299003a7d92314c910006ae39a64908a000d5e738c621140015bf04bb063180032e5897010410006dbba6e29924200ab4814c861500015bb0d99062080031fa1d628c65004c7e43a62b106200d3d735c850500018f8ec3286290003ad1863108540004df40ee89924200e3f74548614c80197ce9318c1108036be11720c5200055fc32642082000e7776586219400173d023a264188032f99271cc8500063e41ced2824009ed5329843108013b98e4992c018802cfe19750c7400055e43a6430a8000eae724c8615000153b06310c2a00034f194714c9400047f430e690a4000cbe835db400400193ae6398c2a003ee761b320c7400054f418c430a800097d861ce21140014fd013aac418802afa1a31d01200063f432e4188a000e3f7354a61d0001cb8e731ac42803acf61831943400053f436e2a926409e5f3299431084018baed9906228002b7e193158831007a641aa49944200a7d8718c5048001cb906a90c299003739cd328862000677b96c498a8000abd8798c41884019eae430e6290033a75db32104310078ea966420c6200d9f739ce21d00015db0531c43280031fd95728c6200063f3b0622824000de4718853248401c7ee6a90c2a00038f99271588500045f434ec9928000e9e73588410c401adb0ab9062900026f21d32500100057a40a6530ca000c7e7654831480018fac438a6528003ada0c61c8540004bec36e710ca0009f4815cf20840018f9033b4a0980033b5c932185400071f418c22828000b3e81191524c80117d023b264a00027e61b704c8100063f42ae431aa2009be86dc9315000197b043b242a0002cf60a3114140005bc402a518a4000f1d3290431140015bd07b26c7108033b5c8610c5200063ec30e0a966400dae625c831d000176902996c2a0003a798d32d00100047f438c710a80008fe87d916388401d9ac6b90c7108038f58a418c6500065ec30e2a064000cfa81dd9300c0017690299482080032f5d163182210057dc0264302a200c9d7318c6150001d6d0430e62a0003a7dce73185400063ec3ac5188a000c3c76d49325000137d033b264a00025f20576cc85000796a926510e8000c5c735896114001a7908b906328002af60b73185400055e422c53006200e3d83588419400157b0d9968108002ee600418c5200063fc36e4b286200dae415c831884014fb0da92c0188029f61831884500069ea90e29968000a7d829cc605480167d0399482280034f614714c8410065fc3ac42086200f1f320c450d00019dae4b1062280031f20d
  | 11 => 0x500010fb0c38a64280032fd8271cc9400046fc3ac631c4200e3c845d4614c8018f9033b4a090003c718e31141400069eb94632828000d9f741c1320c40157d0db9c42a0003d954b714ca210053f42e8130e6400f1d320c4505000197cc839ac4080029f20d65196210069e32ae518a80008bc815c3644c8139ea42bb062108038f58b52904310072eb1e64b08a000e3f7254a61d00012f902b94c7280038f20562904500063f42ae531c2000d5d731ce21140014f100b8ac428003ab5ca32185400063ec3ac598ca000a7d82194314c001769029928008003371d8314c9100047e432e12126200c7d651c532c40019bee731a41080029f21d6354a21006d6422e418e4000c3c7654932500015ed02214c2180032e185700c5400047ec3c85304620093e81dd13294001a7906b90a1a0002b7e1d630c62104d77416a2b106200abf845c0614c80175b0418c42a00034f614714ca410047e40ae431a80008fd8790a60d4401a7b06b90a0a00033d61c61cc520004de43a6430a8000a7f8258d611400156d03190c2a0003e54c8410c4100045ec3cc620c4200cbc731ca61d000167d03990a0a0002d760a638c6500069e3a0e2994a0008fe8798132040018f2c4382a4080275dd48714c921004bf400eab0e6400e3d831865050001978e8380c2990037ca007150c100057cc06853006200db9801c532500015df04b0a64180025f6087158c500065e426ec9902000c7f655ce21480018fac6b94c0280031fddb524ca1000536c14e6b14a000e5e855c863544018feca38a6490003b9588714c810004dfc02e81926200e9c845c863544011ff0cb8065a88023f61e63182210073ab14c3108a000a7c815cd62940018faeab18c7108038a188505011000e5e430e2a024000db4841c5328400197882b94c7080032f5d9644c8100056ec18853006200bb681cc84104001d6902b90c2a00032f592714ca10005d6c1063a024000a7d85dc8614c8019ed033b0a7108029f21570588310065eb90c218a8000d3e835c850500011fd0f214c318003275cc6318940005bc402a43026400cbf749c5620c401abac638a6528003a758e410c7200063e43ac4188a000e9f321863150001d3cc931e64080036758e71ccb400073bc0ac5108a000aae821cc61500011790cb9062a00034fdd8744ca500065e422e531c20009ed821c543884018faed3a862900038fe0d62904500065fc26ec9942000c7f655ca315000137b0d39c43a0003371cd63480100071f320e6b10a000e6d62cc92114001d9906b1264080032fd017218d510055ec10e730e8000cf57218431480018f8e638ac4280031f19671cca20006ce41ce232264009bf865c831d000197eecb2264080271f58a758c8310065fba0e0b106200e9d7398f4004001d3e80b90c6a88031fa14764c9210056fc1a20
  | 12 => 0x8035761f328c4500674f3266418820008fc874ca6194001e6cea20863108275b995720c4210069eb9082188a000cbc761c132500018faecb1463280023fe197090b510072f31ea49942000add8319463884018f9023b2a4980026fe1f628c5400065f31ce3a064000e3d641cd62140011fb0f320c7108263fa1f51588310047ec3ac4188a000cbe645ca630400197ec9380c2990034f21d524cb400069eb96a418a8000c7d768c42194001a7aa538e65a0003a758c3150320004ef408e6a926409cf6211c563c8001cd902b146428002af2053258241006af39ac6108a000a7c8654c53480010f90eb1aa510803a71d0634c9210063ec32e4188a000cbc43dd94304001cbceab18c7108036b589720c740005ba40a652802000c7f20dd9520c40b56d03b9cc3a00031fdcd6248650004bf40ce7310a000be6811ce2188001d3ec7b1462a0003379cf63182210071ec1ac5208a000cbf76dcd4084001cdac4a9664080037a5ca700c5200047fc3ec598a6000c5c7358d521400137f0e99082080029f2156318e21006dbba0e29924200c6f8758b21140018dae4b1062280032fdd270588310075a40ae630a8009cfa205d831c800187cecb98a0a0002db60831886500073b31cc3108a000a7c805d5620c401a7f0838a6428002eda0732887400073a308622824000add87d8c31480011fb0f210c098802bb60870185320071ec10c32828000c3e7688650500011ff0e98ac4188039d20575185320075a410c398a8000b5d86d49320c40197ae9b18c1108032fa18768854000772b0ee71084000c7d7658e219400157f0c99482080032fddb744ca100059ec30e8994a000de5729c7638840147f0ca9082188031f61972940100063eb2ae518e2000e9d731cc61500018f8ebb1262a00277ad81720c5200053fc12ec188a000abd861d132840018fcc5bb6a4188036720d70104310053ec36642802000cbc429c463500013790fb1262a00025fe1d63884500078fa966518a8000abd840ca60144019ece2308c099003ade0c61c85400071fc18c22828000d3e815ca50d000197883bb286080031f9d5705883104fa7902a49906200cbf835db40040014ff0cba863900034fd4a71ccb400053ec306210ca000abc87cca61d00019b8c638a6490002cfe1932106500071e432652828000e7575184314800127b0fa9063a00035758d728c65000756b96c430a8000e3d621043114001c7b0a39cc3a0002b7a0676cc9300063fb9ce0b10a000a7e831c5621400187cec990a0a00038f58952104310062e39ac4a88a000abf865c732d00016bf0eb1e6428002a7219320c5400056e40ac7990a000b5c80549328c401b9ee739c43100037a4c87048520004dec32e418e8000d3e815c850d00018fecbb9c4310003971cd6254a31004dfc3a65a002000eb58018431
  | 13 => 0xe7c902ec18e4000d6f655c85388401dab063086290003ad20c61085400063ec2eec99420009ed821cd5148001adb0ab9063108032f2117298e50006d6ba243b1c4200de4815c85388401a7e80b94c72800267e1d32104310067a38ec29924000eae8218621500018fb0cb90a0180038f1977318540006bba90e29942000d75759c463884018feed31c43280032f60871592200069eb9062282800087d875883194001a7f0e99483280035e1cc705492000636b92c42806000ab6811d0614c8014fb0d188a1900026fa04764c9400063fb2ce29922000cbc735c061500014790c990a0a00039b20d62484500061ebb2c4208a000e5d630c650c80018f90b3b062900032f5db32d00100063eb2ee710e2000cbc415c86350401978ec99242a0002af610321813100637c3ac5190a000c7d769c831140018fb0cb90a1180025f61a73884500065fc18ec90a8000c7f725893194001b5908b9062108032fddb32487400074eb226518c4000ee67218431480014fd0c188a0900037c1c4704c8100073641ac4a902000cbd635c24188401ecaa438a65108029fa0463d89520057b40ee630a4000aed82186215000137b043b262a0002be6023298031004df43cc89942000a7c80595620c4018fce638ac4280031f9da750c7200078f39a652868000a7e8118f5250001b5ce8b96c7108030fdd9524c8410065e434e3a02600097d8719431480018fee6b1443280031f9d9750c5200145e43ac89906000c7d629c7329400167d07108a1a00023f61b7050b510062f39ac7300a000c3c655d0324c4018fcedb2c62900025f61c31941200065fb20e2992a200bb4814c861500015ed03214c3180037a9ca700c5200071eba8e8b1062009bd869c732d0013bd04038a6490023e5a0c410c410006b6b92c4188a000c7f7658a31940019daedb9c42100026fa1c624c5400061fbb2a499680009bf825cf61500018f8cab8484988031f5ce70588500053fc12c6a88a000cbe645c83188001cbecbb1862900034f99273884500069ec28e29928000d6c835c850880039790c38a80980032f60c71592200067b40eed108a002cbb865c0418c0018fecab946290002e7608638c5400069fc1ae42828000c7d765c8311400197908b90c6a08034f20572141400066e39ac6b1020009be81dd132840012fd0d3a862900023fa1b70509310071fc10c32828000d9e738c421d000187cebba2c418803672057318940006dbba6e29942000cbf865c0418c4015bd07082c610803c7549320c740004dec10ed18a8000c7d755c0614c8014fd02318a090003a54c8610c5400063e39ac4908a000aed829cd62040015f501b0ec0990023f61c429803100766b1ac49902000df071dc132040012fb0fb28a710802cf2053210650004dec38c518a80008fd87d45620c401b6ce938ec710
  | 14 => 0xf864c850840018f843bb2a4188027d205708cb3100656b90c430a8000cdc874ca61cc0014fd0c39aa510803375cc63d8221005ba40a64908a000c3e760c45050001d3b0630c62a00025fa1e63886500053fc32652802000e5c6518c31480011fb0f31842080039d9d4610c520005da40a65a002000d7b321c121140014fb0531ea4080035d0867518e2100676b10e29902000bad820c621d0001979063b242a0002e761f328c5400074eb98c630a80009bc815d0604c801c7cc939ac4280035bd95720c5200045e43ac89944000cbe861c54048001b6d0638a818800337dcc63885200063eb2ee09906200cef7258931cc0015bf0c99462080036de0e71d0310004eec10e6a8a6000c7d75d8c638840197f0438ac910002ce60041884500063eb9ae2b10a000c7d75dc1620c401978c939c43880038fa1474588310059e40ac8994a000c7f8758a3114001978edb1262a00020f61f64943100067cc16ec9806000d3d73906219400357300398c2a0003c7211320c65000637b92c4b08a000ab681cc861500018fce7382c528027d3085524c8310071fb2ae630a8000b7880549608c401a7ae520862280036d20e71d03100074eb9ec630a8000b3c814ca4194001d38c631462a0003379c57218d10006e6c10e6a8a4000eb6821843150001970c2b8042a00034f5c9528c740004bf43ea4b006200a7d8799431c400157b07b90c2a0002bd205321812104e3ea90e2b1e40008fc815d83214001a7ae420c63280037ca00714c81000736c10e2b10a000b3980104311400153f0c99063a00037318d720c5200063eb2ee4b006200e3d85dd0614c801e746228281900038b5893290450006b643aa49924000e3c76d9532500011fb0f31e400800397589320c650006da420e29944200e3d3298650d0001d68c220862900031f99473887100065e434e231a8009f672118d5288401a7d06b90a1a00032f58970906310063fb2ee710a400097e87cc96114001cdb02b1464280036be11720c621005af406a5990620097d82dd5608c4019dee4b12c018802af60e72185400063fbb2a499420008fd8799463884016bd0331a6528002af6087318540004dfc02e93146200e5c65cc83148001aed0a38a64080034f99271cc85000556c10c63128000c7e815d83214001ceeecb0c42280032f5d9644ca100065fc08ec9928000a7f865d431084011f90eb1c4228002d7a0473549320061fbb2a49948210f1d6354831d0001c7acab108218802afa0763905200065fc34e3a066008db6641c54304001d38c620a6490803a7591328c4100053ec3664b08a000e6e815893214001c6ea430862a00029f61f63941200047ec10eca8a6000a7880595600c401cbb06b146328002afe1932500100076b40ec731c4200abd840ca618c0019e8e33026408003ab991624c81004
  | 15 => 0x2bb464180031fa09760c4500069f328e710e800097d8798e21940019dae6b1042080032fd81720c5400074eb9e6430a8000ced724c860544015f700994c1288029fe0973588500069eb96a418e8000dad745cb63884011fb0c38a65280031f195700c9310067ab10e29902000ced629c632040018faed18842280036b211720c52000757b92e430a8000d9d325c2410c401c7a6430ca0a00029f20175185320055ec2065308a000d5d76cc83114001c7ac520862280034f59271cc85004df340ee71084000a7c8154d6214c01c7cc838ac4280032fdda644ca10004bec14e7300a000c7c761c5524c80157b09380c299033675db320c7400074e39ac6a002000db774dc5328840197aecb266408002d761f328c6500045e43a64b0082008fe861c532500015790c990c2a00023fe1970ccb510055b408e430a8000ed763d84314800167d0399083280026f61f63106210071eb24e6b10a000cbf635c241884016db051884228002afa0763501200065e3b0c89924200cbc76d8a31500018f8cab906310002afa0732582410074e990c318a8000e3c74548614c801e3e65188a0a00031f1d5624c7300043fc32e710ca009af681dce61c80011ff0e994c110802cfa0732143400063fc32ed10ca000e3f655c8615000197f0438ac818002dd20563084500063fc36e4b08a000abd86cc841040015bb0620ac4188034f9d97314140006dbc20e29902000cbf735c8615000187ced108a0a00032f9d8628c5400063e3b0e6a924000cbc649c732c4001aeaa438a65080031f5d973143200055f434e710a8000a7d8298c5194001cf4c628640080023f60a768c5400065e434e3a024000db5749c7638840197eec38265208032f9d8410c5200065f322e4188a000bd6811c1320c4138fae532863900021f61e63142100047fc12ed18ca000c79861c152cc0016b902b1e64280029720d71588500069d438a0a064000e3f8458b520c401a7ae518ca1a00031f1cd6288450006b6b92a518a4000c7d865cb51940016e902992c3280039760f65d8d20006dbba0e29942000b3c8759132940018fac7b92a2280021f61d620c4500043e432ea18a4000cbf874c8615000197ac838a6528003175d9320c4500053ec3064b08a000a7d864c961940011fb0d39c4208003cea0c50503200055f4386530e8000e9c7358d40840014ff0ea90c2990023fa1b704c9510043ec14e032a6200ced72588318c00147b05b28c2a0002cf61032584500049ec38632868000a788054a61cc001878ec32a64a00029fa03521853204eb6b2ae418e4009cf5729843108001ab8e6382a4990032f18d70106210056f434629922000e9e84d8e63884019dae6b144208002afa18744c92104f37902c5a906209cec72589600c40117d0e194c3a00032f1db744c8100055f408e8b106200a7
  | 16 => 0x51043104e3eb94ca18840008fe8718d6088401e3e6520c622800337dce63480100063ec3ac4188a0009bd86dd13204001e38c839aa4990033bdcb62545300053f408c628280098ff8758a600c401978823b28710802bee0162980310043ec3cec188a000e6e835892114001d690430862a00039758d62cc8500078eb226518ca000cbd641c532cc401b7106b808208003cd10431886500069e40ae42868000d2d724c850500014fb0c18c4328003b3e0d624c81000736c1ac4908a000f1d52cca31d0001a7ae4188a1a00025f61d620c45000576c14c79042000af6810ca618c0014ff04b98c0a9003a759163cc810006dd992e12082000cbf761d13284001c7d093aac4188031f99772580310055cc00c8302640aeb4640c621c40139ec42bb06210803d3549320c520005cec38c718a8000c7e639c352884018fced3a862900032fdda64cc810006dbc18e2a062000cbd645ca319400157b003a2c418803375ce63988100053ec38ca18a40009be8799132040018f8cab9062980023fe09760c4500063eb14e1a946200e3e85dd0614c8018faed31842280039d2056298450006ceb98c710a8000d6e835c850880138fea4bb06390002be6004298031006f4b92e018a4000de572d8431480016bf0c99463280038f99562104310063ebb2c5a906200d7681dda2114013aeea438a6510802ee600744ca10096dac388218c4200cbf76dc5325000197cc939c4208003975cc63141200065fb9ee430a8000b7a80d4831480019e8e630a42900034f614714cb400053f42e80b106200b3c814ca505000157b0e990c2a0002cf60e21941400069ec1ae52868000d6d835c850880015790eb2264080029fa0763941200078e9908218ca00083d87d9050c40011790e994c3a00039798d3214210006eab98e710e2000c7d755c1620c401c7ecbb90c2a0027b91887388510006ceb1ae418e8000cbc739c86150001d9cc6b126408027375c9630c4200059fc12ca2086200ecd72588318c0018d2c438242280031b5c962cc4500063f39ac5300a000a7e85dc1620c40192ce630e42a00031fa0676941300053ec3cca1884200e3e645883114001d38c718e8090003ad186410c520006ce3a0e09906200a6d8214d6294001d3ec89946388002cf608311414004fe41026418a4000eb5831842150001b5ee910a64908032f21a71189400078ebaa6418e8000aed82d05620c4015db0d312640800337e1d32987300063cb10e0a906000c7f735c56214001a7ae520c63280039b58b524c8100071ebb082188a000e6d624c921140015790eb2265080032f1d070588310062fb9ac4b08a000c7e819da5048001d3cc931a6408003a7d92314c92100756c10c210a8000cbf709cc61500014fb0f318a1900025fe1d521853200537c12a6b16a200c5c835d831140011f90
  | 17 => 0x26410e3d76548410c401d9ac499062080031fa0d72997100063fc2cec18a4000d6d835ca50880018fcec32c6290002cf60a31941400066e39ec4a8a6000cdd731cc614800157b0c3a2640800397a0f65d8d200063f3b2e632a400097c815d832140015ed02398c290003a7992634ca100065e39cc310e8000c5d731cd6214001960c2b8062a00273bd81720c520004fd434e018a4000e5f8358b32140019bcec9946290002af21d32987400063f3a8c7b044200dcf635c8314800197ec9388c099003c7d4b32906310071f32cc42086200abd861c132904019ece3b0ec0990039d58d618845000676b96c598a6000cef7358a21040018faeca98a7108032f608764c940006cfba6e29906200abe841c1620c4016db0539ca0900031f5c9620c65000737c1ac4908a000b7681cc92114001d68c218a80900036edd0704c8100055ec14c7a042000cbc749c1620c40137d0e3226490802eb6086348540006b6baae431c42008fe819db324c0019bae4b80c6a88029fe1d535885300e5e43ac8b182009cdf325d831080018fb0cb94c728002dd20532142100071f42ac42086200b76810c96114001b6ee838a65108039b589524c8100071e41cc32868000d6c875493288401d3d0630c62a0023ec600410c410006d6c10ed10a8000e9d84d8e638840157d02194c3a00032fdd873500100071e39ea430a80008ff874c860544019b8c638a64a88034f5c9520c7400056fc02e431aa200e3f8398650d00014fb0d39062280031f19770509310073b388e2b10a000d3f739062194001c7ac838ac4280020f61e6519310004be43ac7108a00083d871974088001c7ec8a96c2990034fa14714c9400076b418c218a4000bb180104310400197908b94c6080027b60873596210065f324e39902000adc8359163040019dec438a64880025fa0776cc850006d6b96c518a8009cec211d93248401c7aebba0c299002af60c7218540004dfc3a65b0a8000cdd7398f20840018f8cb39c42900025f60a750c72000577c12e6b102000eaf7458932040019eae2308c0990031f5c962cc650006b7c1ae428440009bc815cc62500011fd0d39c42900035ea0c7054920057cac188218c4200abd80190614c8012fd0e192c2280029e20175588310055ec36652082000e3c63d48418840187ae5308a1a00032f9ce61087400055e40ac89944000cbc649c0614c8012ff0ea9062900038f18f5218540004bec3cc4188a000ced728ca60cc401cdd00b12642802779985720c4210078ea926520c6204ab6811ca61d00018fceab80c299003b5d85320c5200065fc26ec9902000abf864cb400400197ced20862900033798c714c810006da3a0e29924200a7f8758831140013f10e8826408003171cd635885000767392c418c6000f1d635d431d000157d09a8ac4188028f60a6
  | 18 => 0x40018fd023b2a4900038d18431141400063fc32e42806000e9d63cc94084001cb8e6b1ac4280029fa1474588310075bc10c398a8000c7f86dc93114001c7eca990c2a00021f6187348450006b6b92a518c4200ced72d88314c001a7f08b906228002af60374588310055ec3ac42086200d9f7318d2150001d6b0630882900031fa18714ca5001c1f434e02828000b3d82d96315000157b0f31e8008003b38857218d510072e41ac4990a000cbc415ca639400157b0d18a81900022fa1b73885400053ec14c62802009e6c21589520c40157d09b1cc7108032f1db714c9400053f418e0b10a000abd86cc940040012fd0f32aa7108030f5c861141400063f3b6a518a4000c7c659c732480011ff0e882c418803b5205329873000757b10c310a8000d76759c46388401e3aa499462a00035b195720c5200049fc3aa418e8000cbc731c861500013f50f08264080032f5d932d0010006f4402e418a4000e5e65cc831c4001e3906a9264208039ba0d62548100063f3b4622824000abe81dd1620c40167b08194c2280034f991720c4500055f43062a024000c7d75187604c815b688638a87108033d1cc61885200055f43ec899620009df874c5620c4014fd03318a1900032fdd932487400055f40ee6b00820097f8754c53884018fb0eb1662280035b5c932142100063eb9ae2b14a00097c805d4614c8016730428281080021f618714ca500053f406a530e64008ff874c8615000197eec39ac808002bd20570588310063ec28e2b1e4000ead724c86150001870cab8082900023f21d614ca500055f43e6530e8000a7f82596310c40157f06b90c2a00039758b328c6500065e430e29928000db4711053248401ceaed30c4228002db60831143200065c30ae020a60099ef865c831c80012fb0538cc7280039d18431941200045e43a64b0482008fe87d956388421e3ae6a908218802ce201524c9400067b388c3b026400db4831c54044001b3ae639c42a00029fa0f715885004d7ac08e0b106200c7e635c85084001bc902b9063108031fe1972140100065f324e7b244200c7d7658b32140138faa4bb062108032d61c61cc54004d7741680b106200e9d63cca41040012ff0cb9463280036d990714ca100074e3a4c69942000ed7814ca61cc0016bd01a92641880357a0c70549320063ebb2c4188a009c7d525d831c80018faecb1442280039798f524c81000537c12eab106200a7d860ca6114013cde40b12a4188031f9d95314d200056fc12ed1886000e5d8319463480019bae73184208002b760c6518d200057b40865308a000cbf761053284001d6b0430e62a00036ea00714c9400056fc3ac631c4209d75521c532884019bce7b1ec2900027be1d320c8100055e40ac89906000cbf761c53250001c7ac8b1062280023f61c32980510053ec28c3b
  | 19 => 0x29f20d62984500063ebace2b106200abd801d0614c8014fb0738ac5280026fa1b744c9210069c41ae0208a006cbd76cca41040018facab98cb108039758f32942100069e3aec498a8000a788054861480014fd0a38ac418802afe0963904500074f418e8b106200c7c831d952480018fcebb82c4188025fe09760c4500074eb1e64a002000d9f325c2418c4019bee731c4208002dd2053288450006da38c829924200a78805486150001af26438242280273b9c962980310057a40a6530e6000c7f865c8508c00167b0da908218803ade0532185400057a40ac4188a000a7d868c650c8013cd842b16a4188032f60976d003004e3eb94ca18842009ed87c8763884019ef05bb26218802b760c6418e210041f438caa044000f1f32106319400197eed20a65080031fa0572997100072e39ec6a944200cbc874c86150001c7ec7a90c2a00275d548714c9210059f408e8994a000a7d86cca50040012fb053a86210802bda047058831005dd400e29928000abd80dd0614c801d3cc620a650800397e19524ca31006b7b9264b0ca000aad821cc6150013bcd0438a651080337dce7318520004f643a6490a4000e5e6358a31940018feed31c42280036e8c570085400063eb92c518ca000d6d755c831c80012fb0439ac2280032e58970104500063f43ac498ca000e748158b31140018fb0cb9063280021fe09760c4500053f430632824000e3e6458a3194001a7ecab9c42a00036758e71cc84100537c12a6b10a000cdf739cd62040019df0eb1464080031f5cd62886500065c30ae020a4000b3d820c450d000157b0d39c43a00038f5927158850006b6b96a418a4000d75851c532484019d901bb264190039b58932140100047f43e80b106200e9d8399263040018fced398a0900032fd027198e420065e3b0e89902000e6f8358952040014fd0339ac5280039d20562484500047e43ac29966000c7e760c650480013e902b846418802b7a1e634c8100053fc1ae2b14a0009f4815cf20040015e902994c2180029fa0673588500069fb28e29928000c7d815d83214001b5908b9063108035ec82750c5200063f32ae13106200b3c814ca50d0001c7d0ab148218803979cc7358850006d7b96c498a8000e5c8358b3214001abae639c4328002afe19720c7400065e3b0c498a8000a7f865ce21140018f8eab12c018803a7190634c921006cf992e02086200abe810c8615000197f0d38865a00033b0857298e10006da3a0e2994200097e87cca6114001e5ee8a926510802af21d63500100053f40cc6b14a000af481548614c80187aecb1482280035b5cb528c6210063eb1ee4b08a000e5f76595320c40157908994c0188020f61e65d03100059fc1c432828000b3f874ca50d0001cbac599062280035b20d72140200065e41aeda002000d5d821cd611
  | 20 => 0x5e432e418e8000cdd731cd6204001c7aecb2882188036d990714c810006b6b92a418a4000c7d75d88314c00356d03b84c3a00036d1c431503200071eb108218ca000a3e86d486150001c7f0530ca1a0002db608310845000736b1265108a009cdf721c56308001b6ec838a64908031f588714c8500055ec20e030a6400cbe641ce21880018fd06bb042280036d1c4414ca100074eb9a6430a8000b6d8298e21940011fd0fb0a64a80032fdd070185320059ec14632868000e6d815893214001d690630e42a00033d588714ca1004e7c902ec1884000c7c87548614c8019d903bb264190021f21d635481000737c0ac5190a000de5821c543884015bd03b1e64900034fa14714ca41005afc3a64188a000d3f655ca31500015390c99462a00032f210764c9210072eb1e6528020009be861c532500013790cb9c42a00036b5c932185400072fb2a6518c40008fe8710a610c00197f08bb063900037558c714c8100069ebaae418e8000c3d765c850d0001cbae639ac4280033d5c461d8132005cec00e89906200cbc639c740480014fd0a382c4188033b5c962d47300057b40c65308600097f875483188401978c8b9063880030f9d861941400069e39883108a000d5e631c5329400197ec838a6488002f5604704c8310069ebb26420ca000c79621c132140018fcecb9ca090003ad18431d01200055f43a6430a8000e3c8458b520c40117d0e190c2a0003d9205524ca2104ef4102e418a40098fc87441620c401cbce7b1ca090002afa1271588310047f430e6a8a4000d9e738c621d0001a7ac8b906228003ab6087458831006da420e29902000e3d849d5620c4135dd05082c418803579cd63884500055fc22ea30a6400ecf620c532440015bf04b80c6a8826bba0841588310073a40aa430a6400d3d7210431940019f2e0380c299003371da314c910005b6c1463108a000e3d764ca50d0001b3906b808318802be60232983310678f32e6418e8000a7e80194324c401c7f0630ca0a00032fddb73500100076618ee7b122000c7e7654a314800157f04b1a81080026fa1c63885400041fc3ac92844000a3d8219461500019dec538a64880029fe09755883104c7f43c20b106200cbd625c2410c401a7acb38e65a0003a7592314ca100066eb98c630a4009aec824c5620c4011fb053b66298003d3549320c6210055e42220b106200e9d831d1620c401e70e628281080039798e31143200063e394cab006200d79755c03148001d3ae6b1082188029f618311432008d9fc32a418e8000af48158a21140018fecab98c2900033eddb104ca100069fc20e2994a000c5c7358d6114001d5ae4310c2a00027d2057214e210055e4326490a8000e5f6354831480011fb0fa02c41880337dce63588100055f408e6b00820fb9d87cc8410c401cd902b1264280
  | 21 => 0x800200808a01f00d00c00206101200700c00100103401100000405a00100500b02f1a501601d02b0000040000030000b903b0f53aa03000200200000500e00203705e00400f0070170000a800d00e00002f06a0000000c20151f102700407100004e00800a00100700402a00b0200924ff0030150080a201d00015031d0020c000601302c0041b526d0770000177b405601800301000500921a00901900100200c00601f00000c00603900b0020010040060060460000430090000ab00e00218200500002c0050240c603100000500017d00001e00000001600501e00200102513b01701300900d0c800001700427900f00108a00100004907601c00100f00031d01202c00001300000903200001400000f0591eb02b00093000b00600002b5074a905000005400b04f01006303105b05e0000d600e01f00e02114200000300000400400a04500b05910200005305f02b0030780002ca0280051e000601118603a00200000408d0000000970050e40000132af0010041b811703813b00402305f01a0202070ae0003712a20110390c600200011e00a00100302305c00100422909900502904900b0000111fd0f00540084eb01000800900001b00100f08900002003300800200301500200000301b01a01c38d00203000a00200000e00000e04b1bd1a600c05b0080010960040f300d0260060000b800100001e00110402700007204801302a0370110031a001908d01d0060050050000090020dc19d0070660870050380060000130d700302001d00504000303e00b03e0020060440000200500002a706500006e03001000140902202100108b00000504b03a1d800100403800100700002101d04903200100a05800705b04e07205600600200103e00114507c00c01300402e29104d00303200008f0090e900011601302603200103500e05400412808e04a0180000000310020001391f500007803600600002400000e14701600d02900000300008301801b0d400501100001f03400004904400300601900f01700a02200000100300202519d0060731a500003900300103200400200200c0030461bd4332540000000130020000010070030000400080070a601c00d0600560d70040070000010252e800000001100e00001801200c00300f0022590f800100002f00001602300606100400100503300200000100001c00d00308c00b00104a01312e0050c200000114f00000300020500c00109902606a44f00300702627800000e01700e05b01800003701512d00000200223b00500a0050a42851631031e800500600839f04e00101c00101603236912c01202d00000000400103c00200900a00400700001303d00000805700800200200000300000300f00106c01e0001be0010250400000dc03e0140000110b90d105302500f00900c02e002006
  | 22 => 0x3c2e004117c00200500000106e04700308000200217d07000f00002a01600692400000000c00103900400500002e50a00401202c00a00200004700a00a00a00500402000100c00600000000302d03a00000007f00000000301b02008c00801102d2aa0c800400203f02300e00000000e02405f00a00e07500101500900708204a0050ab00b00501008001e51d00203300e05200200100b0031140060010594f700a00200303700100a00200a0200020050cf00500007300b00037f00002201810c02e00005b00600e03000b03500000701301500100101200314200000000000a0020010000033ea00000102102300500200202e04800801300002400f00002a00707b08f1840000100060030000323521f40000bf01505800425c00d04003e0140a40023e800600a02b00100a01a08101301000013004d01400100000300000200100305100004400610700007c1130010390040a900600d00600700100600401907701a00b06c01c00000c0a20060540b301005504800000900a00108317100d00200202d01900309101705201702100f01b00000c00f01600300006800410600006e00208a00303101d04411701616c0020
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x14b696210714c921004ada4687cca61d0001877722056258450005176487358d611400143f96614714cb400050fe5d62904311400193972600410c4500051d24d711c56214001c6b905c9620c4500049d658814c921140010be98dd932500100059524563cc9611400185e835ce70588500050f65b405ca6394001aa572a047218540007255cc610c621500010be9721932485400070ea45625c04114001c4e9720d624c850006a5245831c86150001c97974c8610c54000687219524ca3150001c1e7618e3114140006a560c83184215000183d8699073884500068de50815cd621400156890615720c4210066560c831c540440014ad9220d76d00100060f618845c8311400113c985cd5288540005a5e61321843150001a4d9220d71588500070d24572184505000185c7320563588500050fa5b7354a215000188d835c862185400060f21a851c5325000145f97589320c4500068d194814c86150001c6b93588704845000617e0e839da504800123f984c86194140007075d932904311400147a909d570185320055aa42855c83148001c2c945c9620c65000707a4e768c45050001e159318431141400069520c81548614c8014b996cc9701041000647e0e835c8505000189e94e1d6318e210045d65c814c85004001c4d63dc9325865000785255831843150001c1d769cd32943400062e219801c5325000187b9061d620c450004a7e6132186315000191d8320d72141400061d61c815883114001c1d76993320c4500052e658741c1320400187a76e01720c4500060f9d9828c4505000183e869da31141400043ee61701c1620c40155b9060873584500056c640741c5328400168d9218c628c540007195cb815883114001c547320562584500060fe1d6458831140014cf9758d7218e210051b259855c83148001c68905c9620c4500044f66273106211400119c984c970904310041f662760c4504800146f9760d62c84500056c640841c532884014b597208610c5400041fe61631c1528840189f861cd32487400066560c831c540c400149c97591634c8100068dd48814c861500014b990dd070588310048fa61764ca50d000185f83a0d76084500051d65c65184314800189d86dce73887400061760c835d8211400147691209760c450004e5e6132104310400183f8659173886500056c640841c53284001c4c835c9628c4500044f65c814ca50500012759620532884500051e241759c5620c4012789061461d81320041f660651ce2148001b2a9360850500200052ba5e645893204001ab290205321854000699588814c9211400143d97588410c4500062b60d72188615000146c9654d7214e210056a640845c831c800107f9261c650c5200060e5d980104311400187986201720c4500042f261625c0410c40193b84201720c450
  | 1 => 0x44fe5b8754831d0001c1e764c831141400054da44841c532940010bf9760a63d02100042fa62645c831040014b9901d270185320049d245860c9611400183d86210714ca500048f658814ca41940015b190210714c9210050fe597254831d00012759620532886500042f261764c84104001c4e76549328c5200046be5d820c7404800119c984c9709063100617619730c4219400186c865c9520c5200045d65c814ca508400189e8718c414c92100687e19754c831d00012b69121d321854000571e5d315c831084014b79760c61105200056c640841c53204001c979760c610c5400060f64d87d9050c40018b476a073248540006c624d80104311400156890615720c62100687e1a734ca50d000185d865cc73884500052b648739c86150001a355220532185400060f197805d0324c401d30710c450503200059324d8158a321400127992201655803100687e0e8358a411400143d96a15720c7400062b648874c86150001c95731843108540006ca609321414084001c8d735c962104310062e602731c8615000107e98d9573886200048fa607354a61d00018ad82208764c540005a5e4983184315000194d8320d72142200050f658845ca639400185d8660873544500052da47631c5404800119c984c970104310070b5c93218450500017289054932885400051765f65d8c31480018b6861c431501200051524d711c562140015349160d72141400070b5c962906311400113d9661c31943400068e5d5801d0614c801835871843114140006a560c831844148001c97631c431501200060f21f654c861500018757520570588310052da5b831c5404400143f9760d621065000783589329043114001b9332600410c4100051b64a769c8311400156890615720c5200051be59755c831c8001a4d8320d62548100048fa44864ca505000146d96a0d721402000517663739cd6214001c2c945c9620c4500058e65a3114140c80010be985d932d00100058b648831845050001c4e635c93214210006275cd821cc615000107d97219520c5200042fe5d8298f4004001714954c56210431007195c8815883114001a2b9660850500200041fe498799431c400191f8754932104310061761f630c6504800143d969cf52887400050fe5972d4831d00012759220563584500061760c839da504800153890615720c7400562da04731ca61d000193972201528c5400058be49751d1620c4010bc9161c63d01200048f259820c45050001ca583188715011000593a4c8158a321400143f965ce4188650007195d5721843148001ab162600410c4100052da58741c5324840157090614714ca1000707dd9651d1320c40185c73e09635845000497e61731cd621400146d97a05628c8500042fe6164dce2188001d277454b714ca2100417e61731cd6214
  | 2 => 0x163691a0d62106500060fe1a755c831d000183d86590714ca50004abe59820c421d0001c6a9358870484500056c643841c5320400183c9461d620c450004ce6603114140c8001a359520532987400061b5d9828c42114001b4993201524c9200052de5d83184215000183e76a0463141400044f65c8388450d000183876201524c9400070b60972184505000163996cc850502100049765880549320c40189e83dcf70987400052764f701cc615000183f865d9750c7400059a241524c8614800107d9899473887100058e64074548614c801cc4635c8610c5200041f662760c65048001c8d735c932185400061bdd98298e2194001b299360850500200065a5ca80d48314800183c94618714ca500060fa1b65dce215000107d97a006590931005a5e4d80184315000147890617764ca100058d2458358a4114001c657220562cc4500060fe1e85588410c4015649160d72142200060fe1f74548614c80156592a14714c9210064761f320c450d000151f97549320c7400062edd9801d1328400145d97194630c5200048f2613298650d00010bc985d932d00100042f25d860c540c8001a3b9560074185320055c241521c53204001a3962600410c4500062be18845c831c80014b491590714ca200042fa60645c831c40010be98dcd72185400070764e760c450500018749161d620c4500062761d84d8e638840143e909d774185320041fe5d86cca500400186f865c932140100052da44861c532500014b691e18714c940006a9608618c421500014ad921cd701854000566a40815cc625000189d9321d321854000707a4e764c8505000189d73a0463189400061ea1b805c8311400107d97e1932142100061b9d9820c4504800113f9261c31141400058e24185588410c4014b99019270185320065a5c88054831480018b69121d32185400042f261625c2410c40145f925cc73588500042fa60415c8635440143d96211720c450005a9e498318721500014ad921cc72185400068e20d8018450500018ae766086188540004a7e61731cc6150001a6962201524c810004abe59820c621d000189d831cc72185400061d61c610c45048001c4d921cd62584500068da54814c86150001a1d8320d6290450004a7a63644ca31c400187576205620c4500071c5d4615c0314800149f9661f328c7400069308786549320c40187976e01720c450006275ce811cc615000107c985d7620c5300042f261631c540c8001b9132600410c4100060fa54865c831500018af985c8721854000587259320c45050001ab190205321854000693c8386549320c401aa672205321854000517245731cd621400186d86dc932586500042fa4487591328800123c984c8611414000599a46835892114001ab061600410c520005ca6483114140c8001c67935c9611402
  | 3 => 0x100060fe19755c831d000183d865db32904500062edda801c5325000161f9654932104310049d24586cc961140018af8758932d0010006ca24d8214140080012b69121f32987400052b64876189315000146d921cd62544500858da477354a61d000187a76201528c5200051be4976988311400113f985c831143400042fa60415ca639400191d6361c319434000617a0f731c1621400143d9720d6210450005cc24532141408400129c98591328c62000665e1d31588410c40183f8799562104310042fa60639c740480015b0914c970904100042fa6043dd9430400183d76e0963904500052e640741c0614c80127596205324865000729e5d8218421500015a59220c71501100064e615801c53250001634914c86114140007a158932104310400147a961cc70549200046e261325c2410400183f9461d620c45000593a4c805893214001e17524c8610c5400042fa63405c863544011ac97608315032000695e0f81548614c801e86824c8610c54000517e49861cd511400145c93595731962100595245731cd621400113d985c831141400064e9cd80106211400119f985cc73887400052ee41821d9315000107d989cc71588500061d5d88158a2114001c1d731cf52185400062d5d8814c8410400189f8798d32d0010004a7a60415c8635440123c984c8619414000569648831c540c400161f964c831943400050fe497690431140018747320562584500050f259851c5325000107d9720563943200051b25d8358921140010bd98992738862000517e59730c621940014ad9220c76485400045d65c814ca500400185c83e09760c45000553e5d524c83188401a2c9460a7358a500062b21d624c9400400107f989d83194120007915493218431480018758718431941200055a64a831c1524800183d86990714ca5000617a1b73dc5524c801538974c8505021000713a4873589611400149e96dce73885400060fe19855c831d000162d92a0d621065000647e1d654c8410c40143f9760c61141400042fa5b805d0324c40183d86dd8744ca50005876587498d329400113e985d9321065000617a60735895114001c1d845cc73588500049de61711c56214001ca7831887150110006a5e458318861500019398320172141400060fe1e64588311400183e76a07321414000713e0d725883114001a5483205620c4500050fe49765903114001a1c86d95328c5400061724d87588311400154f97549320c5200064edcc8054a2150001c2d72588410c4500051d65f6518431480015a691e11720c4210050fe5d831865050001638905d474588310062b21d724c861500018ac865c932185400068dd94814c861500010be981057218d41007079db328c4505000152d92a0d729434000599a448358b2114001854732056258450006a360d721c8615
  | 4 => 0x1400185c835cd71588500058b64b7354a61d00011ba980c570085400050f658835c850d000143d96e10714c8500064ee5d801043114001a5663205329865000593a4f815893214001638905493218540006d220c805493248001c8d63589720c7400068dd4a81cc8615001ba3b96600410c45000699648815cd62140014759798e61886500060f61b845c831140016959320861cc5400050fa40655d0324c40183f87d4932185400042fa63405ca639400185e83dcf71588500050fa5a855c831500018bb86a00714c940006275cd8218c615000143d9758a410c4500070ea4d625c04114001478905977058831006a95c8814c8615000193884201720c45000587259328c65050001c4c735893248450005a566132184315000188d835c872185400050f65b841c53294001c2d645c9620c4500054be49835c85050001a9573a0473185400064b609720c4505000143f96615720c7400061720d825d83114001e319018431141400048f65a8388450d000129c9661f328c54000617a1b731c1524c80146e9720d62484500058da4473d486150001c4f97589320c4500061e5d8805d431c800146d92a1d628c6500050f658841c5329400169593208610c540005a96488318421500018b77620532500100042f65e868c7404800191d874c8319434000738588711c1320400189d87a136398e210060f61d645883114001a6562a0732484500068d548814ca61d000123e96e0e2194140004abe61721c8615000149c965cc31085400048fe59820c450d0001787924c562104310042f261641c5320c00164e93a01624c8500051e24175dc1620c401a9573a0732185400048fa63655cc615000145f985cc73588500042f66043dd9438840149e96e0573189400042f65b805d032d440129e98d017218d510060f21a855c83150001d0c935c932141400062b1d98218d2150001c66935c96114020005a564e82184315000185e73e096398050006d2a4c80549324800146f9261d620c4500051b64a655c831c40011b8984c970104100042f662641cd6204001ca483188715011000719dc88158961140014b5961d0714ca100050f65873106211400189f87219320c5400051765e634c8508400183d9521d3218540005c6241524ca315000185c8758d32586500052d658841c53284001c357218431141400041f660639c35288401a958320c61c85400062b60d721c8615000143f925da640c4500060f61b841c532140014ad929d8628c5400044fa63405ca63940014ac97591624c8100044f65c814ca50d000185d839ce7158a500041fe61635ca50040010be98d81720c5400061e5cc805c5621400146f92619720c4500060fe51861c53214001c1d76cc8410c4500052e64087588410c40183e95e19720c74000617e578758c63884014b596210714c8
  | 5 => 0x4500070be51725883114001a699220175588310065360c835c8500800189e83dcf72987400050f25972d48315000183e76e097314140006530cb87548614c801c2e645c9620c4500068d618410c6211400189d93219720c5400051b64a865c8311400107d972015218532006c6cc98010431140014b696e10714c9210042fe6174d8c608840145f965cf32886500068d5d6811d0614c801e1583d48610c5400059364a8358a31940012b89160064181320061d5d88158c2114001a3876201524c9400052765a738c621d000147a90205760c8500041fe5d82194314c001454915cc73588500062e600731c8615000145d97997320c7100071a64d621c1211400169596cc8410c4100051be59855c831c80015a9920c570085400060f9d580dd1620c40149d9310a7118d4000687e19635d431d000115f985cc73884500062721e734c8615000143e911d8654c9400062765c864ca315000189f8798d32d021000617e6176cc83114001aa49160873185400070764e76cc8505000183f8754932185400051ba5c835895204001c69624c87048450007239ce724c8615000123f966083194340005176487358d511400113d985c831943400061b5d9820c42194001a949160c62185400062760c831d9215000134d92201654c83100517e5987cca3114001e0c93589329045000517e5d63cca50040019387360041884500060fe51861c53294001c1d7658f32904500048f658814c841940014af92604764c9400060f61e645883114001474915cf71588500059c24152184314800162f9260d629045000617e1d764c83114001478905d570185320062e640874c8615000113e981057298e500062b1d1821c0614c8019397320152885400060f61b741c532940010be97205644ca5000596241654c9600c40193a97201524c940007079d97318c50500010df985cc73185200049b64880595320c401a3a96201524c9400051b259755c8314800143e911db524c9400070b5c962904311400185d8720d620c4500051b64a7358a601400164e9120d624c8500058d24532186505000107e98d9573185200041f663651c53248001a397220152185400052765c638c7404800189f9760c62185400071a58b321c12114001a1e8618f528c5400052e643741c0614c80149d9399273d92210061b9d9820c6504800187b76201524c8100060fa1a76d4a315000107d92e1d6394010004ada46874c86150001c8e739c962104310050fe5d62104311400153797548410c621004e5e6131588410c40183e7560374185320060fa54874c8615000107d97a0352185320060f24e87195408800189d83a04764c9400062760c835db4004001e4791589320c4500051be59855c83108401478905d471588310042fe6164dce210400183f87195321854000695e0f8158831
  | 6 => 0x388401f05524c8410c6210062ddd8814c921d0001a1d8320c61141400062721d734c8615000183f87d91521853200725591631c5320400193b8320172141400060fe1a655c831d000123f985d474185320051ba5c81589321400107d9898d72142100061d604815d8321400149c915cc63189400061da5c81589611400113e97205644ca5000713194635c831480014b9901d372185320041f2617654c53884010bd9819273887100061be0a825d831140014b59720c61c8540005a964b83184215000107e9898d721421000457e61731ce219400143d97588410c6500055a241855c831c8001478965d5700c5200041f65e80194324c40143d9720e619434000791245624c8311400173190104318845000527245831d93250001c67655c8610c5200041f6627518f6088401b9393600410c4100041f65c814ca601400185f875d56318e210071a24d621c121140010be98d8d7090621006d2e0c80549324800162d921cf52185400068d214815cc6150001b2b9360850500200068b219524ca2150001a3a8360061141400051ea42755c1620c4014b797608610c54004cb9259821ce2144001a1f861d1524c8310054e640841c5329400162f926156210431004c7e6132104319400149d93d827118d400044fe49870c450d000117997a03520c52000517e59731ce219400189d839cc72185400071325d624c8311400153a9120d70104500051d245735c56214001c1d764c8410c650004ae640844ca600c40183f86614714cb400041f660655c8314c00145d96a0873584500052d65c82187315000146f97605628c8500050fa4476549325000146d9298d72140100068ee5982141408400196487205524ca210062b60b701cc61500254b691dcf72987400041f262765483148001a397320152185400042f662731c861500012ac9160863189400060f251875883194001ce172185700c5200041f2627654c53480010bf9760a63104100052da4776dc5325000187586614714ca100069558c814c9619400183d879db32141400060f654874ca61d00018b4762053248540004ab259820c4215000145d93c83765483100565a5c410c5324840123f985d474588310051b65a855c8310840199774604704c83100593e49731cd62140014769120d76084500041f261655ce21c4001477985c471588500051b65a855c831c8001a8d7360873185400059964a63986219400185d839ce7058a500060f9d9820c4505000163b964c8505021000593a4e81589321400113d972053214140007136487358951140014b597e0861cc5400044fe5d8388650500010be97205644c8300064ea15801c53250001a4f87589320c4500052d65c8318421500014b990211760c720007836508358932140014749160d76084500051d245839da5048001c4c835c9620c
  | 7 => 0x200051b64a635c85084001c4e635c932140100059a2418158932140018ba9021d32185400056c245325c0410400146d921cd62584500061766073589511400183e7620532141400068ba55821cc6150001570914c870484500042fa61764c84104001a3976600410c4500062be6172188615000187b7320171588500069520c815d4614c8014b69620c71501100060f21c654c861500010df985cc73588100042fa5c844ca610c00143f925d8410c4500054ee49831c152500010bf9858c71503200060f618741c53294001c38915897010450007131ca654c9600c401a2d846087358850006c664c8054932500016649160d62484500050fe59835ca50d0001a8d835c86218540004a7e613218431500015b291e0d70104100070e6587114140c800107d98d94714ca200052765a734ca21d0001a3a9420175588310050f259835c850500016a59220c61c85400060f618845c8319400192d825c831943400051be59835c850080011759720532142100062b5ca811c8615000183e76a0463d4940006171cf8258d51140010be9898d7010621006ac245801d0614c80113d985c831143400041fe5d860c4211400125d96a0352cc83100719a5c81589211400119f985cc73885400048f658814ca4114001a8d836087458831004e5245801d1320c40185c95e1d6318e210063561e81d8e63884014b9901d070588310062b21e724c86150001c6572548610c520004ab259820c6215000186f9261d620c4500048f26173548615000183c87d4932185400060fe1f654c86150001aa572a0632185400060fe19655c831d000183d8699673887400072398e625c831d00014b596e10714ca100041f65e81d8e50480019a972600410c5200041fe5d8299431c4001474915cc7058850006a59cc814c86150001d28905c9321414000565a5c410c53284001c1e765cf32141400052be49831d9215000146d92a1d620c4500064b609728c4505000145d929cd63980500068be19524ca21d000185c93618714c8500072a589325c0410400153a91cc970104500062e1da801c532500014ae9718c62885400058da4474548614c801a4d8320d6248450007139cd624ca2114001cb0618c570085400048f662641cd6214001474915ce705885000559245835c8500800169593e08610c5400060f657865c831d0001e153218431141400062725d8318861500011af9760831d03200050f65b845c83114001c65935c961140200054be49855c831d0001c389358970104500068721b524c8315000145d9220d760c4500045ee61321c1211400183d86e10714ca5000627a1e631053284001568905d5720c7200046b25d820c5404800183c86614714c94000707255731cc6150001b9093600410c4100061e24187588311400197185600714c81000617e1e7558c6
  | 8 => 0x640a82000403c01807000324018050402d8048090360642700003a058040f800020c2b8010240002501f00001c0100702a000030030260000300001c0001a0273380140305827841c0000b33c05c010020100280200c05000009006018010000030040080680e066038028060440000000802003c040000000000a80f0000000b80500e0140001705c1980c00006e010158980020240001000c05c5d88805404c0c80b04a0980080100001c0180300000c0143e9620d7214140004ae6408458a600c401d0d724c831141400061720f735c562140014b49158c71503200048fa44864c85050001a1f86549320c7400060fe1d764ca50d000145d9308776548310060f21d524c8615000147890597704c83100693e0e8358952040010be9121d644c8100041f662655c831c400164c93605624c850006a55cc814c8615002749c9758c315032000556e41821cd511400182c865c932141400061d61f81588311400113f985c831141400068d654814c861500016979360861cc5400062e9d9801043148001a3b7220152185400061b5d9820c4211400186e7660a73941200051be59755c83108401a3586104318865000527a5e6498d32040014b5961d0714c810005d2241524ca314800117997201520c5200052da4476dc5325000143d9720c61141400064be1d524c84188401a3b732015218540005d1255315c83108401ca572184410c5200041fe498798c508400163691cc8611414000517658734c92114001ca68318871501100051e241755c1620c41d63691e0e619434000617a6073589611400143d96211720c65000517e5d62cc8311400149d93dd87359010005992458358b211400183c8754932987400051765c65cc8318800143e96a14714c9400059524d711c5621400149e97992634ca1000566640741c1320c40125d96a03524c8310070b5c96210431940018b57620532d001005dac64082184315000192d825c83114340065a5a4773cca61d000191d874c831141400069360c8358b211400185d8758c319432000627e61731cc6150001c1d76211320c6500051be498758a31940010fb985c070185320051b65e8358b2114001634914ca6194340006276538758c638840188d7360873185400041fa63735c56214001c6562548714c8100072558c710c540c800146f925da720c450005d2241524c83148001397984c8410c621007a1609321843150001639960c450503200042f261641c53288001aa58218431085400048fe6132184505000143e911db654c9400054e241521c53250001cc563588714c8100061761f83588311400143e909d774588310051b259535c8534800125f9661f328c6500058da448318450500014b597e0c61c85400051d25d635862114001c64935c961140200060fe1a855c831d0001a2182584505
  | 9 => 0xa84b026000090010044fc1180b00c000100010400f8008200100f80482a00000802803314000030110022e80086d0220000200a0360055e000180035ad025000008190420160140128700023c000030100400080002e00020805004000060580940200302b01a0a40000b27a2a81f835036000002e50000040000000200c3e0001c600c0104c0267f40801c0000bc180020000000003866801407802000000fd00411402c0e84e00000805001170030000030f2000008010360002484d00002c010040080383180109802c0b80001c0205e81b000060078480160800000200c008020fd040014280050fa0080002705e28c080180000040000000435c0e027046880048010000680c008002018000550060000003c0020082200a008000018000025e00039d0040140200f2521b0003b1014028282a30000280002d00a0440081b0000a00b000000094952bd0380ac1500000c0040200e0003701410a07e10c02800302000700011020001585601405400000044
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x8a000a0ee9d62600410c4500064310c482a499462a0002854a160c839da504800141cd3708402e4188a000a8a688836006114140005c8140a9264308629000286ba864d621c1211400143850ae6402e2b10a000ea058932600410c41000542942c1906b148228002497a766132184315000141d536e6402a510a8000a0ea9a85600714c94000427152b9300208622800282fa6609720c650d00018c2c1b24418e2a0220009296a483188715011000506f50b90c2188a0a000284ea825d624c8311400182b41922b9ce0b10a000a1329d8320d6248450007052e4b13002086228002a30a0548814c86150001918cab2040a6430a8000c0765d8320c611414000710ae6b9102990c2a0002331a8245321414084001c0cbb126c0082188a000964285901d0704c83100528942c1906b90a11000205fa960c839da504800184acbb06418c210a800081eea586201720c45000622f0e4aa62b10821880320d836488318450500018c2c1b24418e2a062000d1858890548714c8100070510c482e4990a0a00033099324d82141400800121ad3922990c32828000e88a8d825845050020004175524330038a64a0003c05724c8610c4505000141d504eac06e8b106200e0561d32184311414000443f52c1906b148228002839a6210805c83114001846c9b2443a6430a8000a4c2858320172141400060e1224830eb106228002528a76483114140c800152250b0641ac5908a000c2a649801cc72185400064510c482a499442a00038858320c621c54044001846c1b24418ec90a8000d18588914c8704845000423f52c1906b90a0a000283aa09d580dd0614c801a24c9926b10e0908a000a2a6807460870185320050c950c9ae4b08a010002a29a6a4d8214140080012a4d3920a926418a4000c0ee1c9054932185400052554e49b04282801000380c8624d724c85050001486d2065c3aa430a6400c0be61724c8611414000507744bb3002086228003845a21cc815896114001898cc0e2188a0a064000d129d890549328c52000688b4448ae639ac428002471a6245321c1211400159050b26c10a0a004000e1120d72205620c45000681ae6c90e7a90c2a0003a21a360961141400800141d53d2c402a49928000c0e21c9054932185400050734eb13002086228002914a160c835c85050001c0cbb664c0082188a000c0e61990210714ca5000603b0fcb26418ca1a000341584245731cd621400141d508ec402a49928000c07e93985cc735885000486b4e48a6530ca1a000380ca55cd821cc6150001854c932043a6430a800091c69c90548610c52000710ae648b04398c2a0003887a160d72188615000121ad3922990c22828000a98281922057358850007030ecc9900a9264a000282ca6609720c4505000142a50b0641aec108a00080fe99985c83194340
  | 1 => 0x251d00021209010258000c000700233d100501000a71190172000104020404080008090000010004004903020216013a02080a03001803050e0000250700010b00002003160f07000070630ec80c2188a0a0003884a160d72188615000140e5330641ae42828000a4a29d93608505002000603f30c22e639ac42800282fa6609720c450d0001d1051b04b08a0a004000c0761c964c8311414000660f30a92642086310802a2ba664d82141400800141c5330ac00e29928000e285c861600410c52000427350482a438a64a000340c965c9320c4505000182a49922c3ac4188a00090be9992a0d729434000611b06c9106bb68008003a23a3609611414008001942c1b24418c390a8000d1164c935c9611402000685728482e4b1062280038158764c610c45050001c074aae6c10e630a8000aa469b32600410c4100060770c4830ab9063a0003417a4245731cd6214001438502ea40ae0b106200c8c61990104318845000611b26c16e0398c2a0002839a61cd801062114001324d1120b2a64b006200817ea58320d760845000449f52c1906b12a40800203da72613298650d00011c854a64c00821882000a1368895e1d6318e2100708d4439902b12c228002944a160c835c8500800163050b26b10e090
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x65102005220b968d825845050020005822b728d825845050020005300b164c936085050020004c41b7281524c8610c520005108b764c936085050020006a01a328d825845050020005440b0688915cc7358850005044b864c935c96114020006085a960c831887150110005820b768d825845050020
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x1440192d1946c12c22828010002a0031da328d825845050020
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x4d
  | 2 => 0xcd
  | 3 => 0x14d
  | 4 => 0x140d
  | 5 => 0x24d
  | 6 => 0x170d
  | 7 => 0x1a0d
  | 8 => 0x24055
  | 9 => 0x24b
  | 10 => 0x25415
  | 11 => 0x4255
  | 12 => 0x170255
  | 13 => 0x25355
  | 14 => 0x134255
  | 15 => 0x25715
  | 16 => 0xd4255
  | 17 => 0x24d55
  | 18 => 0x140255
  | 19 => 0x240d5
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 10 => 1
  | 9 => 58
  | 8 => 1004
  | 7 => 2832
  | 6 => 2916
  | 5 => 1033
  | 4 => 140
  | 3 => 10
  | 2 => 2
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
  | 2 => packedAt gbK2 (i*103) 94
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
  | 2 => gbHint (packedAt gbK2 (i*103+94) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 10 => 2*((h/1+packedAt gbK10 (15+(h % 1)*1) 1) % 1)
  | 9 => 2*((h/40+packedAt gbK9 (1508+(h % 40)*6) 6) % 58)
  | 8 => 2*((h/390+packedAt gbK8 (37148+(h % 390)*10) 10) % 1004)
  | 7 => 2*((h/965+packedAt gbK7 (135936+(h % 965)*12) 12) % 2832)
  | 6 => 2*((h/972+packedAt gbK6 (172044+(h % 972)*12) 12) % 2916)
  | 5 => 2*((h/400+packedAt gbK5 (72310+(h % 400)*11) 11) % 1033)
  | 4 => 2*((h/74+packedAt gbK4 (11340+(h % 74)*8) 8) % 140)
  | 3 => 2*((h/10+packedAt gbK3 (920+(h % 10)*4) 4) % 10)
  | 2 => 2*((h/1+packedAt gbK2 (206+(h % 1)*1) 1) % 2)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xff80fff007c03ffe03ffffff471f1ffde231ff
  | 1 => 0xffff03ffffffc03ffc0ffe00b8e7e89e7fce7c
  | 2 => 0x3fffc0007fffffffff03fffc0f8f0e383ff8f
  | 3 => 0x3fffffff800003fffffc000ff00ff03fc0ff0
  | 4 => 0x3ffffffffffffc000000000ffff0003fff000
  | 5 => 0xfc0000000000000000000000fffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x158014b0c142164a009652aa030b032ce210b5
  | 1 => 0xd88b01564ada4216c40ab406186568942ec65c
  | 2 => 0x4255a80104aca8a56b202954c0b0b0c3016b0a
  | 3 => 0x8366ce6b90040c39b3cd0018ed00dd03d40de0
  | 4 => 0x13f8f38de7373f0021861060f7df0003fbb000
  | 5 => 0xe040800e00383001c2082180fefefef8000000
  | _ => 0
def gbRaw : List Sig := (rawDecor 63 gbPos gbNeg).map Prod.fst
def gbPools : List BoundPool := [(0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555, 5, 0, gbRaw),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 5, 0, gbRaw),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 7, 0, gbRaw),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 7, 0, gbRaw),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 6, 0, gbRaw),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 6, 0, gbRaw),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff, 8, 0, gbRaw),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 7, 0, gbRaw),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff, 7, 0, gbRaw),(0x44444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444, 4, 0, gbRaw),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 4, 0, gbRaw),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 5, 0, gbRaw),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000, 5, 0, gbRaw),(0x555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555, 5, 0, gbRaw),(0x55555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000, 5, 0, gbRaw),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 4, 0, gbRaw),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 4, 0, gbRaw),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 5, 0, gbRaw),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 5, 0, gbRaw),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000, 5, 0, gbRaw),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00, 4, 0, gbRaw),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f, 5, 0, gbRaw),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000, 5, 0, gbRaw),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000, 5, 0, gbRaw),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 5, 0, gbRaw),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 5, 0, gbRaw),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000, 5, 0, gbRaw),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 5, 0, gbRaw),(0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff, 5, 0, gbRaw),(0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff00000000, 6, 0, gbRaw),(0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000, 4, 0, gbRaw),(0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000, 5, 0, gbRaw),(0x444444440000000044444444000000004444444400000000444444440000000044444444000000004444444400000000444444440000000044444444, 4, 0, gbRaw),(0x44444444000000004444444400000000444444440000000044444444000000004444444400000000444444440000000044444444000000004444444400000000, 4, 0, gbRaw),(0xa0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a, 4, 0, gbRaw),(0xa0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a0000, 4, 0, gbRaw),(0xcccc000000000000cccc000000000000cccc000000000000cccc000000000000cccc000000000000cccc000000000000cccc000000000000cccc, 4, 0, gbRaw),(0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f000000000000, 4, 0, gbRaw),(0xff00000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000000000ff000000000000, 4, 0, gbRaw),(0xff00000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000000000ff00, 4, 0, gbRaw)]
def gbAtlas : Atlas := ⟨10,rawDecor 63 gbPos gbNeg, 0xeee8eaa8ece0e8a0eee8eaa8ece0e8a0eee8eaa8ece0e8a0eee8eaa8ece0e8a0eee8eaa8ece0e8a0eee8eaa8ece0e8a0eee8eaa8ece0e8a0eee8eaa8ece0e8a0, gbN, gbR, gbH, gbI, gbPools⟩
end PEqualNP.Outside.L_meta_37465
namespace PEqualNP.Outside.L_meta_37465
open PEqualNP.Outside.L_meta_37465.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs2_2_0 : Interval s2Atlas 2 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 9 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 50 := block_range (n:=50) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 50 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_96 : Interval s2Atlas 4 96 40 := block_range (n:=40) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 136 := (concat bs2_4_0 bs2_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 48 := block_range (n:=48) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 48 := bs2_5_0
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
theorem bs3_3_0 : Interval s3Atlas 3 0 7 := block_range (n:=7) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 7 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 12 := bs3_4_0
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
theorem bs4_2_0 : Interval s4Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 6 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 56 := block_range (n:=56) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 56 := bs4_3_0
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
theorem bs4_4_480 : Interval s4Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_576 : Interval s4Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_672 : Interval s4Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_768 : Interval s4Atlas 4 768 13 := block_range (n:=13) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 781 := (concat (concat (concat bs4_4_0 bs4_4_96) (concat bs4_4_192 bs4_4_288)) (concat (concat bs4_4_384 bs4_4_480) (concat bs4_4_576 (concat bs4_4_672 bs4_4_768))))
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
theorem bs4_5_576 : Interval s4Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_672 : Interval s4Atlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_768 : Interval s4Atlas 5 768 33 := block_range (n:=33) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 801 := (concat (concat (concat bs4_5_0 bs4_5_96) (concat bs4_5_192 bs4_5_288)) (concat (concat bs4_5_384 bs4_5_480) (concat bs4_5_576 (concat bs4_5_672 bs4_5_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 44 := bs4_6_0
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
theorem bs5_2_0 : Interval s5Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 3 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 21 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_96 : Interval s5Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 99 := (concat bs5_4_0 bs5_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 46 := block_range (n:=46) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 46 := bs5_5_0
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
theorem bq1_2_0 : Interval q1Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq1_2 : Interval q1Atlas 2 0 3 := bq1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq1_3_0 : Interval q1Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq1_3 : Interval q1Atlas 3 0 6 := bq1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq1_4_0 : Interval q1Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq1_4 : Interval q1Atlas 4 0 1 := bq1_4_0
theorem allq1 : ∀ k ≤ 4, ∀ i < count q1Atlas k, checkRow q1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq1_2 i (by omega) hi
  · exact allq1_3 i (by omega) hi
  · exact allq1_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_2_0 : Interval q2Atlas 2 0 9 := block_range (n:=9) (by decide +kernel)
theorem allq2_2 : Interval q2Atlas 2 0 9 := bq2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_3_0 : Interval q2Atlas 3 0 50 := block_range (n:=50) (by decide +kernel)
theorem allq2_3 : Interval q2Atlas 3 0 50 := bq2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_0 : Interval q2Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_96 : Interval q2Atlas 4 96 40 := block_range (n:=40) (by decide +kernel)
theorem allq2_4 : Interval q2Atlas 4 0 136 := (concat bq2_4_0 bq2_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_0 : Interval q2Atlas 5 0 48 := block_range (n:=48) (by decide +kernel)
theorem allq2_5 : Interval q2Atlas 5 0 48 := bq2_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_6_0 : Interval q2Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq2_6 : Interval q2Atlas 6 0 1 := bq2_6_0
theorem allq2 : ∀ k ≤ 6, ∀ i < count q2Atlas k, checkRow q2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq2_2 i (by omega) hi
  · exact allq2_3 i (by omega) hi
  · exact allq2_4 i (by omega) hi
  · exact allq2_5 i (by omega) hi
  · exact allq2_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq5_3_0 : Interval q5Atlas 3 0 7 := block_range (n:=7) (by decide +kernel)
theorem allq5_3 : Interval q5Atlas 3 0 7 := bq5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq5_4_0 : Interval q5Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem allq5_4 : Interval q5Atlas 4 0 12 := bq5_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq5_5_0 : Interval q5Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq5_5 : Interval q5Atlas 5 0 1 := bq5_5_0
theorem allq5 : ∀ k ≤ 5, ∀ i < count q5Atlas k, checkRow q5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq5_3 i (by omega) hi
  · exact allq5_4 i (by omega) hi
  · exact allq5_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq7_2_0 : Interval q7Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq7_2 : Interval q7Atlas 2 0 3 := bq7_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq7_3_0 : Interval q7Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem allq7_3 : Interval q7Atlas 3 0 21 := bq7_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq7_4_0 : Interval q7Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq7_4_96 : Interval q7Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem allq7_4 : Interval q7Atlas 4 0 99 := (concat bq7_4_0 bq7_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq7_5_0 : Interval q7Atlas 5 0 46 := block_range (n:=46) (by decide +kernel)
theorem allq7_5 : Interval q7Atlas 5 0 46 := bq7_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq7_6_0 : Interval q7Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq7_6 : Interval q7Atlas 6 0 1 := bq7_6_0
theorem allq7 : ∀ k ≤ 6, ∀ i < count q7Atlas k, checkRow q7Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq7_2 i (by omega) hi
  · exact allq7_3 i (by omega) hi
  · exact allq7_4 i (by omega) hi
  · exact allq7_5 i (by omega) hi
  · exact allq7_6 i (by omega) hi
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
theorem bq11_2_0 : Interval q11Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq11_2 : Interval q11Atlas 2 0 3 := bq11_2_0
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
theorem bq12_2_0 : Interval q12Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq12_2 : Interval q12Atlas 2 0 3 := bq12_2_0
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
theorem bq13_2_0 : Interval q13Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq13_2 : Interval q13Atlas 2 0 3 := bq13_2_0
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
theorem bq18_2_0 : Interval q18Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq18_2 : Interval q18Atlas 2 0 1 := bq18_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq18_3_0 : Interval q18Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allq18_3 : Interval q18Atlas 3 0 5 := bq18_3_0
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
theorem bq19_2_0 : Interval q19Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq19_2 : Interval q19Atlas 2 0 3 := bq19_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq19_3_0 : Interval q19Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq19_3 : Interval q19Atlas 3 0 6 := bq19_3_0
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
theorem bq21_2_0 : Interval q21Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq21_2 : Interval q21Atlas 2 0 3 := bq21_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq21_3_0 : Interval q21Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq21_3 : Interval q21Atlas 3 0 6 := bq21_3_0
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
theorem bq22_2_0 : Interval q22Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq22_2 : Interval q22Atlas 2 0 1 := bq22_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq22_3_0 : Interval q22Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allq22_3 : Interval q22Atlas 3 0 5 := bq22_3_0
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
theorem bq23_2_0 : Interval q23Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq23_2 : Interval q23Atlas 2 0 4 := bq23_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq23_3_0 : Interval q23Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq23_3 : Interval q23Atlas 3 0 6 := bq23_3_0
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
theorem bq24_2_0 : Interval q24Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq24_2 : Interval q24Atlas 2 0 4 := bq24_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq24_3_0 : Interval q24Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq24_3 : Interval q24Atlas 3 0 6 := bq24_3_0
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
theorem bq25_2_0 : Interval q25Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq25_2 : Interval q25Atlas 2 0 4 := bq25_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq25_3_0 : Interval q25Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq25_3 : Interval q25Atlas 3 0 6 := bq25_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq25_4_0 : Interval q25Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq25_4 : Interval q25Atlas 4 0 1 := bq25_4_0
theorem allq25 : ∀ k ≤ 4, ∀ i < count q25Atlas k, checkRow q25Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq25_2 i (by omega) hi
  · exact allq25_3 i (by omega) hi
  · exact allq25_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq26_2_0 : Interval q26Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq26_2 : Interval q26Atlas 2 0 4 := bq26_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq26_3_0 : Interval q26Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq26_3 : Interval q26Atlas 3 0 6 := bq26_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq26_4_0 : Interval q26Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq26_4 : Interval q26Atlas 4 0 1 := bq26_4_0
theorem allq26 : ∀ k ≤ 4, ∀ i < count q26Atlas k, checkRow q26Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq26_2 i (by omega) hi
  · exact allq26_3 i (by omega) hi
  · exact allq26_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq27_2_0 : Interval q27Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq27_2 : Interval q27Atlas 2 0 4 := bq27_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq27_3_0 : Interval q27Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq27_3 : Interval q27Atlas 3 0 6 := bq27_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq27_4_0 : Interval q27Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq27_4 : Interval q27Atlas 4 0 1 := bq27_4_0
theorem allq27 : ∀ k ≤ 4, ∀ i < count q27Atlas k, checkRow q27Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq27_2 i (by omega) hi
  · exact allq27_3 i (by omega) hi
  · exact allq27_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq28_2_0 : Interval q28Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq28_2 : Interval q28Atlas 2 0 1 := bq28_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq28_3_0 : Interval q28Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allq28_3 : Interval q28Atlas 3 0 5 := bq28_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq28_4_0 : Interval q28Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq28_4 : Interval q28Atlas 4 0 1 := bq28_4_0
theorem allq28 : ∀ k ≤ 4, ∀ i < count q28Atlas k, checkRow q28Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq28_2 i (by omega) hi
  · exact allq28_3 i (by omega) hi
  · exact allq28_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq29_3_0 : Interval q29Atlas 3 0 39 := block_range (n:=39) (by decide +kernel)
theorem allq29_3 : Interval q29Atlas 3 0 39 := bq29_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq29_4_0 : Interval q29Atlas 4 0 24 := block_range (n:=24) (by decide +kernel)
theorem allq29_4 : Interval q29Atlas 4 0 24 := bq29_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq29_5_0 : Interval q29Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq29_5 : Interval q29Atlas 5 0 1 := bq29_5_0
theorem allq29 : ∀ k ≤ 5, ∀ i < count q29Atlas k, checkRow q29Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq29_3 i (by omega) hi
  · exact allq29_4 i (by omega) hi
  · exact allq29_5 i (by omega) hi
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
theorem bq31_2_0 : Interval q31Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq31_2 : Interval q31Atlas 2 0 1 := bq31_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq31_3_0 : Interval q31Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allq31_3 : Interval q31Atlas 3 0 5 := bq31_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq31_4_0 : Interval q31Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq31_4 : Interval q31Atlas 4 0 1 := bq31_4_0
theorem allq31 : ∀ k ≤ 4, ∀ i < count q31Atlas k, checkRow q31Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq31_2 i (by omega) hi
  · exact allq31_3 i (by omega) hi
  · exact allq31_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq32_3_0 : Interval q32Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq32_3 : Interval q32Atlas 3 0 1 := bq32_3_0
theorem allq32 : ∀ k ≤ 3, ∀ i < count q32Atlas k, checkRow q32Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq32_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq33_3_0 : Interval q33Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq33_3 : Interval q33Atlas 3 0 1 := bq33_3_0
theorem allq33 : ∀ k ≤ 3, ∀ i < count q33Atlas k, checkRow q33Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq33_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq34_3_0 : Interval q34Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq34_3 : Interval q34Atlas 3 0 1 := bq34_3_0
theorem allq34 : ∀ k ≤ 3, ∀ i < count q34Atlas k, checkRow q34Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq34_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq35_3_0 : Interval q35Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq35_3 : Interval q35Atlas 3 0 1 := bq35_3_0
theorem allq35 : ∀ k ≤ 3, ∀ i < count q35Atlas k, checkRow q35Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq35_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq36_3_0 : Interval q36Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq36_3 : Interval q36Atlas 3 0 1 := bq36_3_0
theorem allq36 : ∀ k ≤ 3, ∀ i < count q36Atlas k, checkRow q36Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq36_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq37_3_0 : Interval q37Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq37_3 : Interval q37Atlas 3 0 1 := bq37_3_0
theorem allq37 : ∀ k ≤ 3, ∀ i < count q37Atlas k, checkRow q37Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq37_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq38_3_0 : Interval q38Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq38_3 : Interval q38Atlas 3 0 1 := bq38_3_0
theorem allq38 : ∀ k ≤ 3, ∀ i < count q38Atlas k, checkRow q38Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq38_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq39_3_0 : Interval q39Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq39_3 : Interval q39Atlas 3 0 1 := bq39_3_0
theorem allq39 : ∀ k ≤ 3, ∀ i < count q39Atlas k, checkRow q39Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq39_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 2 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 10 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_96 : Interval gbAtlas 4 96 44 := block_range (n:=44) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 140 := (concat bgb_4_0 bgb_4_96)
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
theorem bgb_5_960 : Interval gbAtlas 5 960 73 := block_range (n:=73) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1033 := (concat (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 (concat bgb_5_288 bgb_5_384))) (concat (concat bgb_5_480 (concat bgb_5_576 bgb_5_672)) (concat bgb_5_768 (concat bgb_5_864 bgb_5_960))))
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
theorem bgb_6_2880 : Interval gbAtlas 6 2880 36 := block_range (n:=36) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2916 := (concat (concat (concat (concat bgb_6_0 (concat bgb_6_96 bgb_6_192)) (concat (concat bgb_6_288 bgb_6_384) (concat bgb_6_480 bgb_6_576))) (concat (concat (concat bgb_6_672 bgb_6_768) (concat bgb_6_864 bgb_6_960)) (concat (concat bgb_6_1056 bgb_6_1152) (concat bgb_6_1248 bgb_6_1344)))) (concat (concat (concat (concat bgb_6_1440 bgb_6_1536) (concat bgb_6_1632 bgb_6_1728)) (concat (concat bgb_6_1824 bgb_6_1920) (concat bgb_6_2016 bgb_6_2112))) (concat (concat (concat bgb_6_2208 bgb_6_2304) (concat bgb_6_2400 bgb_6_2496)) (concat (concat bgb_6_2592 bgb_6_2688) (concat bgb_6_2784 bgb_6_2880)))))
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
theorem bgb_7_2784 : Interval gbAtlas 7 2784 48 := block_range (n:=48) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2832 := (concat (concat (concat (concat bgb_7_0 (concat bgb_7_96 bgb_7_192)) (concat (concat bgb_7_288 bgb_7_384) (concat bgb_7_480 bgb_7_576))) (concat (concat (concat bgb_7_672 bgb_7_768) (concat bgb_7_864 bgb_7_960)) (concat (concat bgb_7_1056 bgb_7_1152) (concat bgb_7_1248 bgb_7_1344)))) (concat (concat (concat bgb_7_1440 (concat bgb_7_1536 bgb_7_1632)) (concat (concat bgb_7_1728 bgb_7_1824) (concat bgb_7_1920 bgb_7_2016))) (concat (concat (concat bgb_7_2112 bgb_7_2208) (concat bgb_7_2304 bgb_7_2400)) (concat (concat bgb_7_2496 bgb_7_2592) (concat bgb_7_2688 bgb_7_2784)))))
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
theorem bgb_8_864 : Interval gbAtlas 8 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_960 : Interval gbAtlas 8 960 44 := block_range (n:=44) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 1004 := (concat (concat (concat bgb_8_0 bgb_8_96) (concat bgb_8_192 (concat bgb_8_288 bgb_8_384))) (concat (concat bgb_8_480 (concat bgb_8_576 bgb_8_672)) (concat bgb_8_768 (concat bgb_8_864 bgb_8_960))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_9_0 : Interval gbAtlas 9 0 58 := block_range (n:=58) (by decide +kernel)
theorem allgb_9 : Interval gbAtlas 9 0 58 := bgb_9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_10_0 : Interval gbAtlas 10 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_10 : Interval gbAtlas 10 0 1 := bgb_10_0
theorem allgb : ∀ k ≤ 10, ∀ i < count gbAtlas k, checkRow gbAtlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allgb_2 i (by omega) hi
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 3 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 33, 41),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 20, 22),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq1 (cert : Complete q1Atlas) : Lower true (roots q1Atlas) (target q1Atlas) 5 := by
  have ready : Ready q1Atlas (asRow q1Pos) (asRow q1Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 0, 4),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq2 (cert : Complete q2Atlas) : Lower true (roots q2Atlas) (target q2Atlas) 7 := by
  have ready : Ready q2Atlas (asRow q2Pos) (asRow q2Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq5 (cert : Complete q5Atlas) : Lower true (roots q5Atlas) (target q5Atlas) 6 := by
  have ready : Ready q5Atlas (asRow q5Pos) (asRow q5Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq7 (cert : Complete q7Atlas) : Lower true (roots q7Atlas) (target q7Atlas) 7 := by
  have ready : Ready q7Atlas (asRow q7Pos) (asRow q7Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq9 (cert : Complete q9Atlas) : Lower true (roots q9Atlas) (target q9Atlas) 4 := by
  have ready : Ready q9Atlas (asRow q9Pos) (asRow q9Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 4, 20)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq10 (cert : Complete q10Atlas) : Lower true (roots q10Atlas) (target q10Atlas) 4 := by
  have ready : Ready q10Atlas (asRow q10Pos) (asRow q10Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq11 (cert : Complete q11Atlas) : Lower true (roots q11Atlas) (target q11Atlas) 5 := by
  have ready : Ready q11Atlas (asRow q11Pos) (asRow q11Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 0, 4),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq12 (cert : Complete q12Atlas) : Lower true (roots q12Atlas) (target q12Atlas) 5 := by
  have ready : Ready q12Atlas (asRow q12Pos) (asRow q12Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 0, 4),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq13 (cert : Complete q13Atlas) : Lower true (roots q13Atlas) (target q13Atlas) 5 := by
  have ready : Ready q13Atlas (asRow q13Pos) (asRow q13Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq14 (cert : Complete q14Atlas) : Lower true (roots q14Atlas) (target q14Atlas) 5 := by
  have ready : Ready q14Atlas (asRow q14Pos) (asRow q14Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq15 (cert : Complete q15Atlas) : Lower true (roots q15Atlas) (target q15Atlas) 4 := by
  have ready : Ready q15Atlas (asRow q15Pos) (asRow q15Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 8, 24),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq16 (cert : Complete q16Atlas) : Lower true (roots q16Atlas) (target q16Atlas) 4 := by
  have ready : Ready q16Atlas (asRow q16Pos) (asRow q16Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq17 (cert : Complete q17Atlas) : Lower true (roots q17Atlas) (target q17Atlas) 5 := by
  have ready : Ready q17Atlas (asRow q17Pos) (asRow q17Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq18 (cert : Complete q18Atlas) : Lower true (roots q18Atlas) (target q18Atlas) 5 := by
  have ready : Ready q18Atlas (asRow q18Pos) (asRow q18Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 4, 20)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq19 (cert : Complete q19Atlas) : Lower true (roots q19Atlas) (target q19Atlas) 5 := by
  have ready : Ready q19Atlas (asRow q19Pos) (asRow q19Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 4, 20)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq20 (cert : Complete q20Atlas) : Lower true (roots q20Atlas) (target q20Atlas) 4 := by
  have ready : Ready q20Atlas (asRow q20Pos) (asRow q20Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq21 (cert : Complete q21Atlas) : Lower true (roots q21Atlas) (target q21Atlas) 5 := by
  have ready : Ready q21Atlas (asRow q21Pos) (asRow q21Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 3 zero, 3, 11),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq22 (cert : Complete q22Atlas) : Lower true (roots q22Atlas) (target q22Atlas) 5 := by
  have ready : Ready q22Atlas (asRow q22Pos) (asRow q22Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 34, 35),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq23 (cert : Complete q23Atlas) : Lower true (roots q23Atlas) (target q23Atlas) 5 := by
  have ready : Ready q23Atlas (asRow q23Pos) (asRow q23Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 10, 26)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq24 (cert : Complete q24Atlas) : Lower true (roots q24Atlas) (target q24Atlas) 5 := by
  have ready : Ready q24Atlas (asRow q24Pos) (asRow q24Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq25 (cert : Complete q25Atlas) : Lower true (roots q25Atlas) (target q25Atlas) 5 := by
  have ready : Ready q25Atlas (asRow q25Pos) (asRow q25Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq26 (cert : Complete q26Atlas) : Lower true (roots q26Atlas) (target q26Atlas) 5 := by
  have ready : Ready q26Atlas (asRow q26Pos) (asRow q26Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq27 (cert : Complete q27Atlas) : Lower true (roots q27Atlas) (target q27Atlas) 5 := by
  have ready : Ready q27Atlas (asRow q27Pos) (asRow q27Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq28 (cert : Complete q28Atlas) : Lower true (roots q28Atlas) (target q28Atlas) 5 := by
  have ready : Ready q28Atlas (asRow q28Pos) (asRow q28Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq29 (cert : Complete q29Atlas) : Lower true (roots q29Atlas) (target q29Atlas) 6 := by
  have ready : Ready q29Atlas (asRow q29Pos) (asRow q29Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq30 (cert : Complete q30Atlas) : Lower true (roots q30Atlas) (target q30Atlas) 4 := by
  have ready : Ready q30Atlas (asRow q30Pos) (asRow q30Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq31 (cert : Complete q31Atlas) : Lower true (roots q31Atlas) (target q31Atlas) 5 := by
  have ready : Ready q31Atlas (asRow q31Pos) (asRow q31Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq32 (cert : Complete q32Atlas) : Lower true (roots q32Atlas) (target q32Atlas) 4 := by
  have ready : Ready q32Atlas (asRow q32Pos) (asRow q32Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 4, 20)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq33 (cert : Complete q33Atlas) : Lower true (roots q33Atlas) (target q33Atlas) 4 := by
  have ready : Ready q33Atlas (asRow q33Pos) (asRow q33Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 4, 20)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq34 (cert : Complete q34Atlas) : Lower true (roots q34Atlas) (target q34Atlas) 4 := by
  have ready : Ready q34Atlas (asRow q34Pos) (asRow q34Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq35 (cert : Complete q35Atlas) : Lower true (roots q35Atlas) (target q35Atlas) 4 := by
  have ready : Ready q35Atlas (asRow q35Pos) (asRow q35Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq36 (cert : Complete q36Atlas) : Lower true (roots q36Atlas) (target q36Atlas) 4 := by
  have ready : Ready q36Atlas (asRow q36Pos) (asRow q36Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq37 (cert : Complete q37Atlas) : Lower true (roots q37Atlas) (target q37Atlas) 4 := by
  have ready : Ready q37Atlas (asRow q37Pos) (asRow q37Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq38 (cert : Complete q38Atlas) : Lower true (roots q38Atlas) (target q38Atlas) 4 := by
  have ready : Ready q38Atlas (asRow q38Pos) (asRow q38Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq39 (cert : Complete q39Atlas) : Lower true (roots q39Atlas) (target q39Atlas) 4 := by
  have ready : Ready q39Atlas (asRow q39Pos) (asRow q39Neg) := by
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeee8eaa8ece0e8a0eee8eaa8ece0e8a0eee8eaa8ece0e8a0eee8eaa8ece0e8a0eee8eaa8ece0e8a0eee8eaa8ece0e8a0eee8eaa8ece0e8a0eee8eaa8ece0e8a0
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certq1 : Complete q1Atlas) (certq2 : Complete q2Atlas) (certq5 : Complete q5Atlas) (certq7 : Complete q7Atlas) (certq9 : Complete q9Atlas) (certq10 : Complete q10Atlas) (certq11 : Complete q11Atlas) (certq12 : Complete q12Atlas) (certq13 : Complete q13Atlas) (certq14 : Complete q14Atlas) (certq15 : Complete q15Atlas) (certq16 : Complete q16Atlas) (certq17 : Complete q17Atlas) (certq18 : Complete q18Atlas) (certq19 : Complete q19Atlas) (certq20 : Complete q20Atlas) (certq21 : Complete q21Atlas) (certq22 : Complete q22Atlas) (certq23 : Complete q23Atlas) (certq24 : Complete q24Atlas) (certq25 : Complete q25Atlas) (certq26 : Complete q26Atlas) (certq27 : Complete q27Atlas) (certq28 : Complete q28Atlas) (certq29 : Complete q29Atlas) (certq30 : Complete q30Atlas) (certq31 : Complete q31Atlas) (certq32 : Complete q32Atlas) (certq33 : Complete q33Atlas) (certq34 : Complete q34Atlas) (certq35 : Complete q35Atlas) (certq36 : Complete q36Atlas) (certq37 : Complete q37Atlas) (certq38 : Complete q38Atlas) (certq39 : Complete q39Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 11 := by
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
  have q0 : Slice true (roots gbAtlas) (target gbAtlas) (0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555 : Sig) 5 :=
    slice_correct (ms:=fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have q1 : Slice true (roots gbAtlas) (target gbAtlas) (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : Sig) 5 :=
    slice_correct (ms:=fixRows 16 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq1 certq1)
  have q2 : Slice true (roots gbAtlas) (target gbAtlas) (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc : Sig) 7 :=
    slice_correct (ms:=fixRows 0 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq2 certq2)
  have q3 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f : Sig) 7 :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have q4 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff : Sig) 6 :=
    slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
  have q5 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00 : Sig) 6 :=
    slice_correct (ms:=fixRows 0 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq5 certq5)
  have q6 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff : Sig) 8 :=
    slice_correct (ms:=fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds4 certs4)
  have q7 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000 : Sig) 7 :=
    slice_correct (ms:=fixRows 0 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq7 certq7)
  have q8 : Slice true (roots gbAtlas) (target gbAtlas) (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff : Sig) 7 :=
    slice_correct (ms:=fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds5 certs5)
  have q9 : Slice true (roots gbAtlas) (target gbAtlas) (0x44444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444 : Sig) 4 :=
    slice_correct (ms:=fixRows 33 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq9 certq9)
  have q10 : Slice true (roots gbAtlas) (target gbAtlas) (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a : Sig) 4 :=
    slice_correct (ms:=fixRows 20 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq10 certq10)
  have q11 : Slice true (roots gbAtlas) (target gbAtlas) (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa : Sig) 5 :=
    slice_correct (ms:=fixRows 16 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq11 certq11)
  have q12 : Slice true (roots gbAtlas) (target gbAtlas) (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000 : Sig) 5 :=
    slice_correct (ms:=fixRows 0 17) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq12 certq12)
  have q13 : Slice true (roots gbAtlas) (target gbAtlas) (0x555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555 : Sig) 5 :=
    slice_correct (ms:=fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq13 certq13)
  have q14 : Slice true (roots gbAtlas) (target gbAtlas) (0x55555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000 : Sig) 5 :=
    slice_correct (ms:=fixRows 1 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq14 certq14)
  have q15 : Slice true (roots gbAtlas) (target gbAtlas) (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c : Sig) 4 :=
    slice_correct (ms:=fixRows 4 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq15 certq15)
  have q16 : Slice true (roots gbAtlas) (target gbAtlas) (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc : Sig) 4 :=
    slice_correct (ms:=fixRows 8 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq16 certq16)
  have q17 : Slice true (roots gbAtlas) (target gbAtlas) (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc : Sig) 5 :=
    slice_correct (ms:=fixRows 16 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq17 certq17)
  have q18 : Slice true (roots gbAtlas) (target gbAtlas) (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc : Sig) 5 :=
    slice_correct (ms:=fixRows 32 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq18 certq18)
  have q19 : Slice true (roots gbAtlas) (target gbAtlas) (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : Sig) 5 :=
    slice_correct (ms:=fixRows 0 34) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq19 certq19)
  have q20 : Slice true (roots gbAtlas) (target gbAtlas) (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00 : Sig) 4 :=
    slice_correct (ms:=fixRows 4 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq20 certq20)
  have q21 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f : Sig) 5 :=
    slice_correct (ms:=fixRows 20 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq21 certq21)
  have q22 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000 : Sig) 5 :=
    slice_correct (ms:=fixRows 4 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq22 certq22)
  have q23 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000 : Sig) 5 :=
    slice_correct (ms:=fixRows 4 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq23 certq23)
  have q24 : Slice true (roots gbAtlas) (target gbAtlas) (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000 : Sig) 5 :=
    slice_correct (ms:=fixRows 8 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq24 certq24)
  have q25 : Slice true (roots gbAtlas) (target gbAtlas) (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00 : Sig) 5 :=
    slice_correct (ms:=fixRows 16 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq25 certq25)
  have q26 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000 : Sig) 5 :=
    slice_correct (ms:=fixRows 8 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq26 certq26)
  have q27 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00 : Sig) 5 :=
    slice_correct (ms:=fixRows 32 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq27 certq27)
  have q28 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff : Sig) 5 :=
    slice_correct (ms:=fixRows 48 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq28 certq28)
  have q29 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff00000000 : Sig) 6 :=
    slice_correct (ms:=fixRows 16 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq29 certq29)
  have q30 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000 : Sig) 4 :=
    slice_correct (ms:=fixRows 32 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq30 certq30)
  have q31 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000 : Sig) 5 :=
    slice_correct (ms:=fixRows 0 48) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq31 certq31)
  have q32 : Slice true (roots gbAtlas) (target gbAtlas) (0x444444440000000044444444000000004444444400000000444444440000000044444444000000004444444400000000444444440000000044444444 : Sig) 4 :=
    slice_correct (ms:=fixRows 33 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq32 certq32)
  have q33 : Slice true (roots gbAtlas) (target gbAtlas) (0x44444444000000004444444400000000444444440000000044444444000000004444444400000000444444440000000044444444000000004444444400000000 : Sig) 4 :=
    slice_correct (ms:=fixRows 1 34) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq33 certq33)
  have q34 : Slice true (roots gbAtlas) (target gbAtlas) (0xa0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a : Sig) 4 :=
    slice_correct (ms:=fixRows 20 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq34 certq34)
  have q35 : Slice true (roots gbAtlas) (target gbAtlas) (0xa0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a0000 : Sig) 4 :=
    slice_correct (ms:=fixRows 4 17) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq35 certq35)
  have q36 : Slice true (roots gbAtlas) (target gbAtlas) (0xcccc000000000000cccc000000000000cccc000000000000cccc000000000000cccc000000000000cccc000000000000cccc000000000000cccc : Sig) 4 :=
    slice_correct (ms:=fixRows 48 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq36 certq36)
  have q37 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f000000000000 : Sig) 4 :=
    slice_correct (ms:=fixRows 4 48) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq37 certq37)
  have q38 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000000000ff000000000000 : Sig) 4 :=
    slice_correct (ms:=fixRows 8 48) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq38 certq38)
  have q39 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000000000ff00 : Sig) 4 :=
    slice_correct (ms:=fixRows 48 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq39 certq39)
  have pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p :=
    List.forall_iff_forall_mem.1 (show List.Forall (fun p => ValidPool true (roots gbAtlas) (target gbAtlas) p) gbPools from ⟨build_valid q0 [] rfl, build_valid q1 [] rfl, build_valid q2 [] rfl, build_valid q3 [] rfl, build_valid q4 [] rfl, build_valid q5 [] rfl, build_valid q6 [] rfl, build_valid q7 [] rfl, build_valid q8 [] rfl, build_valid q9 [] rfl, build_valid q10 [] rfl, build_valid q11 [] rfl, build_valid q12 [] rfl, build_valid q13 [] rfl, build_valid q14 [] rfl, build_valid q15 [] rfl, build_valid q16 [] rfl, build_valid q17 [] rfl, build_valid q18 [] rfl, build_valid q19 [] rfl, build_valid q20 [] rfl, build_valid q21 [] rfl, build_valid q22 [] rfl, build_valid q23 [] rfl, build_valid q24 [] rfl, build_valid q25 [] rfl, build_valid q26 [] rfl, build_valid q27 [] rfl, build_valid q28 [] rfl, build_valid q29 [] rfl, build_valid q30 [] rfl, build_valid q31 [] rfl, build_valid q32 [] rfl, build_valid q33 [] rfl, build_valid q34 [] rfl, build_valid q35 [] rfl, build_valid q36 [] rfl, build_valid q37 [] rfl, build_valid q38 [] rfl, build_valid q39 [] rfl⟩)
  have low := boundgb certgb allCuts pv
  have lift := lift_ok (u:=true) (ms:=fixRows 0 0) (raw:=fullRoots) (T:=fullWord) (xs:=[]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 0 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008241832 * 2 ^ 32 + 3974162592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37465.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,3]⟩,⟨.or,[0,4]⟩,⟨.and,[5,6]⟩,⟨.or,[3,7]⟩,⟨.and,[3,7]⟩,⟨.or,[2,10]⟩,⟨.and,[1,11]⟩,⟨.or,[0,12]⟩,⟨.or,[2,8]⟩,⟨.or,[12,14]⟩,⟨.and,[13,15]⟩,⟨.and,[9,16]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,17⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 11) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241832 * 2 ^ 32 + 3974162592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241832 * 2 ^ 32 + 3974162592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37465

open PEqualNP.Outside.L_meta_37465 in
theorem PEqualNP.Outside.L_meta_37465 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241832 * 2 ^ 32 + 3974162592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241832 * 2 ^ 32 + 3974162592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allq1 allq2 allq5 allq7 allq9 allq10 allq11 allq12 allq13 allq14 allq15 allq16 allq17 allq18 allq19 allq20 allq21 allq22 allq23 allq24 allq25 allq26 allq27 allq28 allq29 allq30 allq31 allq32 allq33 allq34 allq35 allq36 allq37 allq38 allq39 allgb)
