import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, children closed at the parent by
-- restriction pools (closeChild of the model), and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36386.Model
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


end PEqualNP.Outside.L_meta_36386.Model

namespace PEqualNP.Outside.L_meta_36386
open PEqualNP.Outside.L_meta_36386.Model
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

def SBf (j : Nat) : Nat := [7, 7, 5, 8, 7, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36386

namespace PEqualNP.Outside.L_meta_36386
open PEqualNP.Outside.L_meta_36386.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0xd0010417080800003010034031800463c0040044fe10bd42fd41fd30ff40ff32fd40fe20bd40fe41fc41fe21bf42ff41fc40be41fe31fe32fc42fe30fd31bc41fd42fc21ff30ff20fc32fc43fe40fd43fd20fd10dd32ff31bc43fc10fd21ff43fe43fd32ff42fc20fc30ff10be43fc31ff21fe42bf40df32
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x50d1788819882800102950400000e0d0014808280308085090201900f15800500838a818180869c9e0d0380040401018048820480000800018d0302020004359f0182140b00008500000025674c841aea9c853c54cc27aa521cf95331cfa1265ae5210e7ea818db54830cea1665bb50502dca598cf55331ce21e653e53d0abca6194f95230cf9968175510839a6510cf944419eaa0433f54ccb5ea4a14f94c419f2a4633f54486bca60873d49329ea96819f325027aa020e794e419f28e853d548c33a6520d794c21cea9c83cd32c82baa6084f95232e7212653c540c67ca8904fd5132ce21a6576510827ca810cf153109f288873f544c67ca8194f152219e2a2656e52042dea4886790f329e2a6653f52502bea6a04f946439faa661cd32483388798cf94f409ea84833d54c8278a890cf151309eaa643cd320873ca621e7d4d40af29e4376510c27aa420cf95030ce2a2659c434c6baa7904f151319f2a4415c534427ca9905754c20af29c833d548c73e85994f94e439f2a0815d539067ca720eb50a32db288836c52442baa790d794e42cf990833d5490278a6a15754e32af298853d540433ea8994f14d409f28e813f5050a7aa8105714d40ce992815e53c833a65a05e940219eaa4419f32906daa598dd544309eaa4659e434ca7ea9885754c219f298873d5490adca4184f145409e2a22179500867ca82157d4d10aea98859c535027ca320db54843e6a12653f54886bca6104794e419f2a4216e5210e7aa421e7509329ea94833d540cb5a84996b548438e29a813d540c33886184f55210ce21c613f544c338a9994f95020cfaa6653d5090e7ca990cf5512096a90873d50d0a7aa021cf14542b6a90213e540431a84994fd5110
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x1100004014d01c00434a00974000080700738400040a7c70808b195424ca8d6210c30a3588438c28c6150932a3588535021c635522087197325022d6215330a3588434c61d6294e418d98754cca0d6214d40c3588535030d544cb208798f54c421c635521087d95329062d6214d4093588535030c43548308d185544820d6294e41d24c9500870d6294e418b58a539070d544c920a358b54cca8c6550932a598754ccb0c4354b31c3988535028f6050932c3d51328861e639474087195325021c63540418718d50d0a4d6294e418798f544870d524c841c3551320868d62153328798f540c70d524cb40a358843cc62d6215031c394d5210f0e6294e418798f548868d649093287588535021f65cca418e580540c68e6550932c510d510c21d6510c30c398d5210e1c63551208798e51d0a8d6294e41
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x1808000e06b90c6a8083035ca63d512181ae531ca3a050471551324824338ccaa1265031d9544c920a0ae331aa421c0d7218d5484282b9086a8861035ca63d5310
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (i*5) 5
  | 5 => packedAt s0K5 (i*16) 16
  | 4 => packedAt s0K4 (i*27) 27
  | 3 => packedAt s0K3 (i*38) 38
  | 2 => packedAt s0K2 (i*49) 49
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt s0K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/30+packedAt s0K5 (800+(h % 30)*6) 6) % 50)
  | 4 => 2*((h/76+packedAt s0K4 (4455+(h % 76)*8) 8) % 165)
  | 3 => 2*((h/34+packedAt s0K3 (2280+(h % 34)*6) 6) % 60)
  | 2 => 2*((h/10+packedAt s0K2 (490+(h % 10)*4) 4) % 10)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xf07ffc3ffffc3fc1fe1fc3fe1fffc1fe8cf3cf
  | 2 => 0xff87ffc1f0ffc3fe1fe1fc3fe1c1fe1f733d33
  | 3 => 0xfff87ffe00fffc7fe001ffc7fe01ffe183ce3c
  | 4 => 0x7fffff00007ffffe0007fffe0001fc0fc0
  | 5 => 0xffff80000000007ffffffff800000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x14000408402040004402404802504088045045
  | 2 => 0x212108848148040a0a20841220849414312512
  | 3 => 0x421251102a9220d4a1112a8554092941828a28
  | 4 => 0xb556225281aa96733542207992c0c45d80f80
  | 5 => 0x8c6643b9cce33279dd99f32110303199eff000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcfcfcc0fcccfcc0fcfcfcc0fcccfcc0fcfcfcc0fcccfcc0fcfcfcc0fcccfcc0fcfcfcc0fcccfcc0fcfcfcc0fcccfcc0fcfcfcc0fcccfcc0fcfcfcc0fcccfcc0, s0N, s0R, (fun _ _ => 0), s0I, []⟩
end PEqualNP.Outside.L_meta_36386
namespace PEqualNP.Outside.L_meta_36386
open PEqualNP.Outside.L_meta_36386.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x1030003cf00400014100109c3c40d000000008164014cbc43ff20fd21bf40fc43ff31fc30fd32fe43fe40fe42fc40ff21ff40fe30bd40be43fc10fd41df32fd40fd30ff43ff42fe21fd10dd32ff32fe32fe41fd20ff41bf42ff30fe31bd42fc32be41fd42fe10fc31bc41fe20fc20fc41fc42fc21fd31ff10fd43
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x448104800f82000b0013030001070003848687008405810103879d01008c800107448a0691058f080001000004238b800229828083000206988009800d00011500011d868007218180000206828007001480004f153329eaa4853d529075aa421cf15131cfa12653f544867ea898cfd53309ea94873d54902daa4184f553209f298837a500867aa120cf94e439ea86853c5150b3c87996714d409eaa0657551082baa610cf153109f2a6419d321079a64906b948439f2a6633d540827ca621e790d32ce21e633f54c42baa62167d5332cf298873f544c27ea89967d0b329eaa4653e51106baa6104f55231cf29c833e541033e6420cf94e41b7290613d501067aa421cf54b409faa6655e5390678a2a04f95232af298413d540879a6410d754e41ae29a219d42ccabca61957d4d40b6a9663bb50502bca7214f951209eaa2415d538cb3a64a04f94742af29e433c544c33886184f95231aea98213d548c2dca4084f950209f28c873d5210678a910db94b319e29a853e5410b3ea6a0734cb209e2a24376510827ca810e715132cea12653d5090f388698cf550109f29e855e53c82daa4084f94f40b6a90873d54cc65aa421cf14d40cf992819f544ca7ca3a04794e41aea9e413e5110e7ea0a15b14910ce9968179500867ca8184f15132d6a12659c43ccb9a6510d754f219f28c833f540c79ea4994f952309eaa0613e540cb3886994f952209ea80873d54c86baa7215d944309f2a421b6511067aa9085794c219f2a6436e5210edea4884f55220baa88613f5250278a9985794c42cf994839d539073e65a067153329faa4438d424ca78a818d714d40d7a9285ce424ca7ca8084f151108e29a819d329075a85194fd5110afa9a215e530439a84996710e30
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x1420b10c20008000100b0201c044068004b98400004061b940c394d5210e1c6355120a3592424ca39601503187588535022d6214d40c310d520c30d524cb40c3988535028c6550932c398d5210e0d6214d40c510d510c28d6294e418718d548824d6214d40a3588535028c61509328798e51d0a8d6210d31a358b54cca2c65509328758a539061c65cc9408d185544828d6210e3087594430c21f65cca418b58854cc30d6294e4187d95329068d6210c30a3995424cb0d6214d408b58a539060d6294e41a3d81424ca3661d5332c398a539070d544cb208718d548428d6210f318b588540c70f544ca218798f544869661d53328798f54c421e6394740d24c9500861c6354041c3549321064d6294e41c3551324821c654c9408718d50d0a8d62153328798f540c70d544c821c310d52cc61e63d5221
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0xc00001409a06b94c728e81415c8435443081ae531ea98840d7298f54486063b2a899241415c6635484381ae431aa020c0d7218d548424338ccaa1265411c5544c920
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
  | 4 => 2*((h/83+packedAt s1K4 (4455+(h % 83)*8) 8) % 165)
  | 3 => 2*((h/34+packedAt s1K3 (2280+(h % 34)*6) 6) % 60)
  | 2 => 2*((h/10+packedAt s1K2 (490+(h % 10)*4) 4) % 10)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xf07ffc3ffffc3fc1fe1fc3fe1fffc1fe8cf3cf
  | 2 => 0xff87ffc1f0ffc3fe1fe1fc3fe1c1fe1f733d33
  | 3 => 0xfff87ffe00fffc7fe001ffc7fe01ffe183ce3c
  | 4 => 0x7fffff00007ffffe0007fffe0001fc0fc0
  | 5 => 0xffff80000000007ffffffff800000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x14000408402040004402404802504088045045
  | 2 => 0x212108848148040a0a20841220849414312512
  | 3 => 0x421251102a9220d4a1112a8554092941828a28
  | 4 => 0xb556225281aa96733542207992c0c45d80f80
  | 5 => 0x8c6643b9cce33279dd99f32110303199eff000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfafafaa0faaafaa0fafafaa0faaafaa0fafafaa0faaafaa0fafafaa0faaafaa0fafafaa0faaafaa0fafafaa0faaafaa0fafafaa0faaafaa0fafafaa0faaafaa0, s1N, s1R, (fun _ _ => 0), s1I, []⟩
end PEqualNP.Outside.L_meta_36386
namespace PEqualNP.Outside.L_meta_36386
open PEqualNP.Outside.L_meta_36386.Model
def s2K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x118006d32dc6574caf994d32
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x2350e32
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (i*4) 4
  | 3 => packedAt s2K3 (i*15) 15
  | 2 => packedAt s2K2 (i*26) 26
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt s2K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/8+packedAt s2K3 (75+(h % 8)*3) 3) % 5)
  | 2 => 2*((h/1+packedAt s2K2 (26+(h % 1)*1) 1) % 1)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffbfdcf3e3f3e74cf
  | 1 => 0xfffffffffffffffffffffffdfef3cfc7cf9b33
  | 3 => 0xebf03f3f80fec3c
  | 4 => 0xf3ffc03fff00fc0
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xfffffffffffffffffffffff404104009020045
  | 1 => 0x208041042040112
  | 3 => 0x150aa0690a94c28
  | 4 => 0xe082ab24a14e80
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 27 s2Pos s2Neg, 0xeeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88, s2N, s2R, (fun _ _ => 0), s2I, []⟩
end PEqualNP.Outside.L_meta_36386
namespace PEqualNP.Outside.L_meta_36386
open PEqualNP.Outside.L_meta_36386.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x140a72822c01400c01000cf0000c0000340058000000040040300000000015fe20fd41ff30fd42fd20ff42ff31fe31fd40fe32fc40fc42fc30fd10fd30ff10be43bc42fc21fd21ff20bd40ff40bf40ff32bd41fc31fe21ff43fe43fd43fe42ff41fc20fc32fc10bf41fe41fe30fe40fe10be42fc41fd31fc43bc43ff21fd32
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x8833f540cbbe86995fd4542de21c637e530c77aa6216fd5131df210653d51d037e87a0ef10a20bea98857e53082f8a9884f95031de280873d548c77ca9185f55120ef21887be32d077886886f10840de21e61be5010b7885906f54141f710a43bc430c2f8a098dfd4530bfaa4433f54cc6fca7205f55243bf290657d5288278a4a06fd0e43dea0e43ed320cbde4210ef90a41bfaa263f7314c77884907794c219ea8487be540433887994f15331be29a817d52106f8a2a06f90a30bf2a085df32cc77aa4a06f10a32beaa243bd41102fca310f754c10beaa661bc43c437a65a05f94243f7a14657c540cbec8220ef15130dea1885bc43507baa7216f10a30bea8c61f7318c7f261085f94821bf2a0617f54842f8a2905fd5320df2a443bc5290efca708778c531de288877d544c3788410f74c730bfaa2417e538827aa8884f55031df21a41bc43d0378a6214f15131bea8c85be42c43788590df54c21cf29c85bc32d02fea0a1ef10f32de28487bf408837e80205f152209ea8085fa30842f8a4087b8c832bfa9a81bf414877e81906f0c540dfa8c87bc5250378a3a06f50731bf29c83f52144378a3215fd4121f6992433c540cafca6196fd0731bea9c613e54042fca518df94c41df212857c54082f8a9195f54b43bfa92877c5050f7e82204fd4540aea9821be32d02faa9186f90b30dfa02413e52d037886086f90d43b6a9061bd515037ca221fec4110be282855d530877a87a07b94830bf288817d52cc77c8710efd0431df10a817d538c678a9985f94f40bea96217d54086f8a0996f95030bf280817e528cbf2a010cf54043de10e817e508c6f8a6106f4c940bea9821ed21c83be60185f95230bea9221fa50087ea43886f10930ef992637c548437e43a06fd0230beaa465bf215037a86a0df54231beaa421bc420cb7a83106f90931dfa8a817d529037c64a0ef10a40de21841bf5310bda42906f90c31dea0e417e51107dca521df54e10dea06417e50106fca5986fd0b40bea8e85be43102faa1a15b94a439f29e837d51902fca320df55320bf28061f53144378a890ef948429f29c87bd32d06fca6216fd0130de2148379500c7daa418df54c40dea0a413f54c83f220085fd5330dea9e81df32cc2fca420fb48421dea92837d534827ea0a0df55221bf28443de5304378a8996f90a31df29885bc438437ca421ef14042df210837f505073ca621ef10b31bea86877d5210fdca4085f54443bea9443be42442fca8886f50421bf29683be54883de85216f94242df2a221fb20883ea63886f15321df21061bc424877ca7a0df54643bf29483bc43d077ca7a06f0c940ee21a65bf54cc37ca0a0ef90d32beaa4417e518c37886a04fd5132dfa9487be5390b7ea5a0efd02409f2a465bf418837a80207d8c510dea04417e51882faa4085f54243
  | 1 => 0xe51502f4a018efd0430ef98a61be431077a82085f55331beaa265bc43d0afaa521efd5120efa1a877e5410f7ca9996f90e319f2a0817e540877ea2217d8c431bb288417e510c2f8a8904fd51219ea8885ed4210b7ca9085f94a42df21a213d5190afca4216fd0842df21e617d51ccbd884996fd0c42df218617e52d0efea2997b54810f7a12657c54c87ec428877d0e43beaa065bc53d077a81885f95020dfa0e21ae5210afca5206f10d30beaa6437d54c437e81085f94830bea8e81bc52d077a64a0df15231de21865f721486fca4085f94332bfaa065bf41d027ea8985f94d10dfa82817c530437aa3215f94f20de21c81f5210877a82106fcc940bfaa061be43c42f8a5885f55231bf2a0637c504877e65a0df94642dea9683be43d02f8a6a0df94031fb10e21bc43907b887994fd5131beaa0637e544c77c84995fd5331deaa46376510c2fea498ef90921de21c61bd54042faa520fb8c921bfa90213d54906fea810df54021bea8083be43ccaf8a4a05f15110fc98061bd54c42fea6a16fd0f409f2a4436d52043f660985fd4543bf29063bc424cb7e82085f15331df28683bc544c77887216f50010de21e63dd314c37a82a05f54f42df21081bd5010b7c85104f95332df216417c53c83f260885f15332dea0c217d54442fea690df94021f790c43bc540cb7aa810fe88020bfa9e21bc434877aa421dfd5232df28c877d53d0378a321df14c21be29e21be43042fca5886f54443deaa465df328caf8a898dfd4540dfa8a83be428cb7a80105f944219f29087bc53d02fea6886f90920bea80857d534867aa8086f551109f2a441bd548837863a06f90d41f699641b7515077c43a06fd0420df21043bc428877a87216f94941dea8e817f548c3f240104f15132fd182217c53443de41105f95010d6a94877e518c6daa418df54f109f29487ed32483ba60187ecc2309f2a083fa300c2fca3994f55240bf28663fb409037e86a0df54a10bea9c65be42c8678a8906f90c20bf28087be42cc77aa8105f94d20bea86437c54cc37ea1217e88210bf28e877d5010f788418dfd4d20f710241ee324837a81086fd0621bf290417d511037c8520778c932bfa9c43bd548867ca621ef94b40be29421df308c3f280205f94b40de2a641bf41842fea0a16f10d31dfa14853d54083da6590dfd4131df2a0417e528c27ca810fe48210ef98e613f54c87dc65906f15330ef29841ed520c3be6318fb8cb21bfaa665bf43502faa2195f94e43dfa0a813d54c42fca9195f54331deaa461be43d06fca7a0fbc8520df29a833c54c86faa7905f94640df21c217e54486bca6107bc8720dea0c43cd320ca7ca8106f54f41bf2a643df324c37ca521fe94031de218857c53882fea6105f54e20bf28481de5390b7c86a077cc832df212617e50082fea8996f50431de21
  | 2 => 0x42faa3085f14d21de216217e5090bbe6218ef10b30de214637e508c2fea5886f10841dfa8887f54110778a5a06f90820bfaa021be43d0b7ea0a0df14d42f7a12857e50d0b788488774c930fd200812e5290f3886997bcca329f29885bf414c27aa9195f55131de21061bc32d06fca998efd0640bea9a217c524c6f8a4986f4c740bf2a4633e5210b7aa9085fd5020dfa9e817e5110f7c86987e84010bf2a421bc50d077ca918df94410fb880213d5190f788710df95320dfa0c837c52442baa7215f55332df29a813c544c2faa3a1df542429faa6617d528c2fca3985d54430df218653e54442fea4986f14941ee996637d518cb7c82a05f54e41df18e81be43902faa2215f95120bf2a081bf418c27aa221cf94b419eaa441bf535077c85086f90b41dea04617d52d077885996f10c319e292837d5390afaa110dfd5121de20e81bd21503ec20886f90e41d621265bc42d037a85a05f15031df212817e50d0efaa620efcc540f7900417c5250f7aa2216fd0110dfa8087bd5090f5ca521efd0030bf28c87be438c37e81985f14141bf286837e5110afaa0195fd5031bf29a43bd5010f7886995f94210bfaa261bd414c77c87215f14e10deaa665bf50d077c8798dfd4f20f690041df43ccb7ea8196f90831df29683ee4210afca790efd0310be28a653c54c82faa1996fd0e42bea9c81bf5190b7ca2216f108109eaa0617f530877c8690efd4243dea16835e53087f2a018ef10c21beaa4833e54c43ba6218df94c43bd280437c5150b7ea5a0774c931de288857d51cc37aa321df947429e2a243bc42506fca820fdc4210bea8e41be51d037a8318eb10a32de214216d5290e7aa1a0ef50030de218817e508cb7a8220cf14d40bf28441bc438837a84a0ef10f20bf2a443bd41cc2fca7a15f94740dfaa265bf5250378a7216f50510bf2a665bf32d02f2a010efd5320dea0861be5010feca2185f54830de21041dd53082fca3906fd4941bfaa4417c514c2f8a790efd0010de21c65bc53503baa610df54620bfa9e43bf53d067ca5216f10d42df28c857d53887bc60985f14d20bf28065bc434837aa6a0fb94831dfa0a63bd31502fca9105f94843beaa021bf414437ea998ef50c43dea96815d530837c86a15f94420dea0e21fa2044378a6a0fdd0541bf29843bd42502faa9205f94010df21a637c53886fca8996ed4140f6a94877c548c3ea6218df15132bea84657d53d06fca7884f94e42df21885bd50d06fea918ef14843bf29487bd41d037c62a06f10f21de2a6637d5408378a0a0dfd4910dfa00417f54c86f8a810fe481109ea8485bf41cc37a80884f952319eaa4437d509077ea7216fd0631df99283bf411077882a04f55332bf29221bc425037885a0df94632dea06617d530827ca9085fd5110df214433c53506fea508774cb30fb28841b
  | 3 => 0x1800115807822000000030000000085d0028020082280a80a014084008000267d49780103a028030050020700080f0021785180a010004448060000082284600000c00000002304400d90003b800001042000fa111044004020030021901719c00e6440000700601c00002008164029c10000700402300000c048030380080b99d01801c628160c60600080605800c020000000040080d000004020050000001880100203400889008050018000300080001f02a018060660300b0080020300003000000001c020000000080001b0a400c0003106a0200400900083c0207200c0141d2010100040180d4d602c000010000000180102e024cd8ab040020070031300080300a0167d4008012940111b0010a204c000060020440d874034020000031780111a80007e0140d019000630060010c20543302709e0085a00520e03c0180d0080089e8150400082084002e000028040241245501d01c000000520220281d8020003f43180001200802aca726088058001b60ac1000202400001800012000028ed0080280401100000c6500408641c0000830e02c001a207e0040280002c0140f0000160000081707e0140a02c0001680001803a00cd400207017c0683b0020000e8005820040007e0000040500700e0880105907605c0002600801c3e80023a000038002300240008700c208078071d0000070070440444f88f00a24400024002080070420000800098400a004040000c80000218cdfa0e41bd5090beaa2185fd4e10bfa98217c52507ba64197c44010df20e81bc5090b7ca621df15130df21681be548cb7ca818fec8120dfa12835e53042fea6a0dfd4520cea9c857d510837ea421efd5130dfa0a417e52cc77e63a06f90e20bea94633f544837c64a06fd0c43dea02417e5010abca7215f15320dea0261be43c82fea4a05b94810dfa0843bd43d06faa8187d8c710df20a836e520c3de64996f50d40fba0c837f53883d885195f94840df216657e54c4378a2a06fd0721dea0a43bd414c37ea0216f90e32dfa8e817e544c2f8a890ef48740bfa8265fb108437842a05b94831de192833e548c2fca6085d54420eea18873e540c2f8a8185f94c40bea96817e530c378a8906f50640deaa061f5510837aa7216f94940bf2a661bd53503788498efd51219f29e81bd540c6f8a8084f55230bea9e43be42042f8a910df95032df21843be5090f7e84a05f94432df21e431e5390afaa1a0fd884219eaa043bd5290efaa2185f55242dea0c617d52cc37e85a0dfd5310dfa9a817e50c877c80a05f54831df2a6217d52103ee4310df54031bf288637e509077ea990ef95021bf29c437f525067aa9086f50842fda02817c5150efca7215f94a10df21283f5100
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x842cc7b15444010e3109324c23d6510b10ce991500c71e5390c218f196434823e64d4c208fd85540423c65109318f19153c863d6494020dc54910042b96094540cd945410823c64540328f99053843344354420cd591510c32c43548108f594420c73561951109e983540c63e6414d10da54a500c63d6590c108f5825210e3f6590910a358e5210a3c654cb418f996434829e63909208f596540c72c548cb20c794e5090aac6250320c794c43c835551cc0308f59732d023d6194f409dd95210865e63d5321c7d91530863f6055031c714f325072e5290a418f590538823e6294f41ce951500c63e64141218f5825290f2c5288540ab98a430c63e6510d42c798e52d06ae6290d42a798f5090aae6290e30cd10e510823c62550108f596540829e63909428fd94420863d6194b40ae58052d023f65d04308798f540cb364294420ab58a435023e64d4c21ad586535063d6590f108f992518c23e6494430dac85500863f65109108f594438433442544308f592510c32e6294f418f59250cc63e64944208f98f544869e63109308fd91520423d6494232cb15132c863e6494332a758e42d029e6390b419798f520432c64548318f194434872e52108408798e52d02ba60085408f58252d063e62d45408f99642cc71d5350421ce952500872c4354831c794d40082ae6290e40cd992510c23e64150318fd81548c63d61d513097596530423f6510a10d64c5500c66d62d53318f98e540863d6590c30cd984540ca3f6590810ec109100427661d4c208f99431d023c6510d20f848520442786548110ab98b5310b3954940218fd9150cc71c63551108f992500872e52500108f997414c23e63953108f990540c23e62153309718d544434e53948109b1953248277654c431a758c21d023e6494c32ab58b5090ebb6054d40a758e425063c63552208f19151cc29e6390b30e310a324ca3e6510d218f59431d031e6510d32ab988315033651d0430ab98a535077153440109b588514c23e6215130e3109320ca3d64942219b988540428d6294c43ab98a43c823d60d5321cb94a420c69e6310832cb90e520c23f6510c30ad58453d072d5250431a798f54c863f6454a30cb54842cc23d65506208f59642842b96090f30ab98a438866c62551108f99353c823c6254043a718d515023d64d49108f993524429e6310a32c758e5210b1f6194e42ce58354c829e6390a30ab98a43d0aae64cc932ad586430c63e6414e20a798c21d02b960146428fd95315023e65ccb40cd592510c23d6590820cb189544423f6590a318fd96428423e63d45408f586548cb6a5294031a758c5010b2d52d46438fd91500cb1e63d50329e980538872d52d04318f597410863d6094e429b596520423d6590e219d195214427960145328f593524c65d63145208b98a53d023e658c941
  | 1 => 0x31e5494c108f990514cb1e63d5331cd90e510823d61952208f1895190e3d6494f208f590528423d6414121ad584325074c534c9219b58853442ad6294d418f996434869e63d46428f18d548431c5390d408f19153487715148020c754d41042b960146438f99251cc32e52d42438f586540823c6215120cb9485190e3d6494c329758f540871e6394c438f594428c23e6590f20c75825390b3941540218f587540caae6214243c714c315023e62d5330a798e424872e5290a40cb54b400429c63504308f992510c72d5250430c754c5310a9c6354141ad58442c872d54548308fd91534879a434c030c79865390a3f6454f20cb54b5090f2e5494830d3149324c73a60150328f596438831d5390810a798e5210abb6050510cd547400823c6548540c719153082b56110a319e980530423c63553108f587544ca3c6454b108f988544c63c6454910ce909500869e63908408f583540ca3e6494010cb98a5310aba6014643ab580424ca3e65151218fd91538872e52d0430ad58442c423d6115120cb54a420c23d6494021cbd955290f8c43d0932c794c43c863f65d0630ab98a434831c63553328f195404823e64947209b98b540c67661150329b988520423e65885408f98e540836a52540318f58354cc74c534c920a798e42ccaae6294d40c755253043b25444010ab189505066e65d0932a798e424423c6354242cb152320ca3d64d4d20c798f54c869e63908108f196424c63c64547209798c530834c524c930c3151320ca3f6154242ad5845210f2d5250410ab98a43d06b56110d21ad9845310a3d6590a308f59251cca3d65cc941ae582434423e65d0940b3d95320ca3e6315032cd909510831d5310c108f189540c32c43548308f59353c823c6510f20a798e428cb344294430cb9865290f2c64948108f582548cab661140428fd954210a3f6155030ce10d50087365494420cb54a420423c6510f21c754d400823e65909209bd954210a3d6414c20a798e420ca3c6355021a758e52d023e63951108f584544ca3e62d5131ab98c428caae62d46439b98a53d063e650c5408f5825310a6e6214c218f992508cb2f52109108f596431023d6194843a758c5090b2d52108318f99052c42b56110d10cb5825290e6d6214e10e310c424cb3654504418f580540cb8f6310932ab98843c831d5390c218fd95418823e65d0d408fd95418c29e648c9329798c540878f644c832d314d32c863d658c9418fd91528c65d6314121cb94a5090eb56114b418f19532506d4614c9318f582548c63c62542438fd9151c831e5310810ab584428cb3651d00208f99252cc63e65151328fd9152cc73b4154031ab98c424ca3c6454b318fd9532d031c544cb308f99442cc6b96010e20ab98a43cc2ba600c5408f584544c23e64944329ed95200823f6155332cb54
  | 2 => 0x4354021ab58e5210a3c6255230cb15132c82ae6290c308f997404823c6454a30dc8c5500c72e52d0010cb189548ca2e62d5331ce90a50086b56114042a758e42d072f6094a43add85525065d6594c208f99054042ad620c540ce50650086d8604c930ab58b5190e6e6214e10b358e320cb1e53504208f992518827561d5030cb192520c29e63908418f19152cc23f6590f10c758f544ca9e6390a10ab988430ca3d6195332c794c43d026d62150308f98f505063e65087408f990524423e63d5120c7153320ca3c65909309758f520431f6494e42cb90d520c31c534c9419d584540c23e6414c21ae582430c27661150309bd95320cb1e53908208f99353c423d6494432ae58351d023d658cb40cb152324832e52504108fd96438427a60150329b58b540421e6394b418f594315032e5210830cb14a325038c434cb208f197315029e6394b41e950521086396015032cb98b54cc32c43948318f592500c6766114c208f990504c71e5354242c794d400426f6548421e318c424ca3c6454432cd54741d023d6508540ce951401023d6595010a758c5110aac6250521aed8141842b96014f408f997414823561150328f586540c31d53546428f988535063d65506308f592520ca9e63d53208fd9521d032e52908108fd96438863e6590930cb19152042b96010a309d987540c25f6354910cd90d510831e5394642da54910043a64248421ab98a43486796014c21bc181314431e53d04218f19153c423f6454b308f98a540c336545442097d95300c23c6454a108f582548872e43548108f59251082ae62909328f98a53d023d6510910ab98a43103595354021ab98a43ccb2c4394810ab988434823d64d4d108f59621d023c6354642a798c5010a3d64946309b98b54cc23f6454a10a758043cca3d6494730c794c430837221540218fd94430823e6394b408f590520427a60d50218f992500c23d6510c10cb594428ca3f6055332ae58243843355150030a798e420c23d65108108fd9443c432e6510932ab98a43042ad6210c428fd94428c7736544010ab58a53d078c544c832ab98a434433843940218f595410c25d63150208f594430c66d6214c10c754c43c823d64d4a10c758e52d032c6494831bcd95100423e6510540cb14a32506ac6250120ad584420872d52d0030cbd92520c62e62d50329e980520423e6510d31f494d100423d60151328f592510863e6494410ce109500c71d53d0010ec501100423d6194c428f191538863f6055021ae9805110b5a5354021a798e52507355150420c7d9153082ad6510a32ab98a430ca3e6550530ae58021d023d6494231a798e424c31f6454c10c798c540ca3e64145208f593530871e54cca328fd94420c2b66114843e5505310c6b96010b208f993524c38d320c9408fd97410834d53d0a428f994215
  | 3 => 0x131ab9885190e3c6454c20e310f324cb1e5390e408f99352c432e54548308f59353882796014e21c7153324c2ce62d0d328f594438863d6414c108f99443c863d6095110d9549100432c6094a43ad58443cc63d6095332c794e430829d6110f32a7d8d515023f654c740ae5805110b1c5310d108f18d540423f65504308f596430c63e6510b308f99250c863f6510c31ad984325072c544c832d3d95320ca5e6394b40c7d92530823c6510832a798e42c423e63153218f584525023e65ccb41cb948421065f654c832ce90e500873954940318fd9442c432e4394810c754f400831e53108218f18950d074d53548109b195324865e6314c10add8540443396095110ad5845010e3c65505309d587540823d6055010a798e42c863f654c941c715332cc72d5254243ab5885010f1d53908209b58b53042b96014c429e580540c63e6590921cbd91520423d65504208f597400c31d5350420cb90e520c63f6454432bc18530442ae620c7408f59732d06766115020ae9805190b1e5310c428f99053c42b56114c42c794d4390b2e62948428f191530423c65501308f596540863c654cb40ce591500c6b561909109b58b540c69e6390a31b9185324863e6415021cbd4a5290f2e5250431ad58740442ae62d0320e398a5310e3f6590a30c718a5390b384394031c754f410863d6588540cd545419023e65d0730c7952530833651d0420a798e424caac6250420ae582535023e65151309ed8153486ad6290d419b58a53d02af6254540ad586434423e6515131e310932cc6b960150328f996424ca9d6294c43cbd91520c23c6550521cd552510826e62150309e583540872d5494831ae58242c83695284010cb98854c87595394021ab98a430823c6354442ab58a5310e5e63d5020a718d40cc2b56115032e590d310c63d64940108fd815110e9e6390940aed81515023e6494832e310d324823c63550208f99632d063d6510e208f590538865d6394b41ab584424caad6290f409d19531442ba600c7408f98a54c42b960d4f408f98a54442b56110f10ab988434863e64145308f592510433a42940318f99353886ae6210f329718d52443595344010d5545300c23d6590b108f98f540ca3e65109218fd96430c73561153318f191538423f6510820c794f40082ae6290e10c758f54c863e65d0d41c7d92530425d6315010ab9885310a3e64946328f997325029e6310b31ce506500c63d6414f10ae9805210e3f6590e20a758c5190a5d6314810ab98a431073664944208fd95400826e6214530ec591100432c548c9218f593538429e63908208f99454482f161840109b98a53d023f6154243c754e430435a53940218f191520c25f654c431cd945400c26d62150319798c54042ba6008740c7d50434caae62d4e42ab98a434c23d6414b10c754c430833a
  | 4 => 0x798c540823d60d5132c71865390a3d60d5131cbd92520429e63109318fd94438421e63d5321ab98a43cc71f6355110cb151324823c6255210e3109324c6b96010a108f992544863e6494d218f19541c832e5210b31e358c428ca3e64d4810d954520082ae6290c218f596325027a6014c218f98b505063e6510920ecd01100433443944308fd96430c23e6494f208f593534863e6394b41ad9845090eae6294f408f994424ca5f6355110cb149325033551d0030c794e420423d6590c41d994a510c23d64141318f997425073a6494031ae58043cc2ac62507218fd95410823e6494732cd909510c26e6215031a798e4290678654c1109798c52c42ad6294d408f99631d03565354420a798c5090b2c544c9218f194325063d64d4f218fd95400c2ae62d4243a758f5190a3e6510d209e980540872e5210b308f586548c2ae62d0521ab98a43c872e52d4643cb58a5310f8d6210f32ae58051d021e63d5320c794c430425e63d50328f597410c31e6315331c7151320cb3561d53319798c52842b960144438fd96420871c544cb318f18d50d063e6395210cd545410c23d65108218fd91530829d6394940cd551510c38d320cb409e596100433442944208f595404431d5390c208fd9442042cd63908428f590534425e63d5010c754f410433551d04408fd954310ab96010930d654e100423e6588740dc485500863c6590f21ec505100432e5210b418f98b540ca1c6355110cb949400c33b4154021a758e525074d5348421c754c4310a6f62551109d587530829d6010d329b588504c72f6194a438f19150c873960153308f996434c72d52d0430d554d10042ce63d0932c794c431063f6550c43c794c5190b8d320c941ce58354cc34c534cb20cbd89544423d65cc9408f990504caae6290f10d3951320ca7765504418f59253486ae6290d43cb18e5290e3f6454f21ab98a438c72c524c941cb5495190fb242440108f99250886ae6214043c794f5190ba94048020dc546300c23d65d0431ced81544431e53d4242ad9845010f665254430e398e5210a3c62552318fd9731d031f5310d108fd855010a786054d218fd9532d066e6214d10c714e4350a9e6390b31ab98a434cb344354430c794c430ca3d64145328b189544425e63145208f59053843695254031e310d324863c65d05208f99643c876551c8020ab994424ca3f6590c108f194325023f61540438fd9541087565394420e3909320ca9e63908218f990520431d5310821ae580424423c6454f20a798843ccb8c434c8328f590514c2ad6214443a718d41cc63f6155020ec10d100431e5454c208f59252cc72d52d0410cd54741082cd6290c439bd9520082ae6290d40ce90e500c69d63948429d98453042b561109319758c524427661d50209d185534823c6548740c71825390a3d6015
  | 5 => 0x54cc38c6210d32c794e43042ad6214643a718d544437353440108fd96420c69e63909319b58b540c2ad620c7408f19541482ad6294f40c794c431023d65d0420a798c215023d6015331ae58043483515344010a798e52d023f6454c1097d954310f1d6510f328f594430c2f06148110ce58054c823e6510f208f596424423e64d4f21a7584434ca766114132ae98032502ae6294f418f994434c26e6214131a798e42d02b76154d41abd89505071c54cc931c758e52d063f6510c218f592500caae6294c43cb94a5190e9e63d03308f596420c23e63151218f995414823d64946208f98854482b56190b21ad584430c69d63909409b58854043396015032e358e5210a3c62550318f596420c66d62d53308f98f54c823f6550441ced06500c63e6494231cb551520423d6510f10cd945410c23d6590e10d354f200823e65909318f994434cb4d3254032d354b310c63e6395010cb952520c72e5210b40cb148215023c63547408f993528433a54940318f582540c71d54d0f32c754d5090a3e63149408f98e548871d53108108f590530863e64d4e20a798e425065e63149108f99053886b56190b10ad5845090e3c6454e20ab98a439071d5454c21ad58643c42756115020ce10950087356115032ec991100431e53d04208fd96420c25e6314121ae58352d02b561d0310cb548420c31d5494c20c799443ccb1e5310f428fd95400423e6214d40e3d0c424cbb243440108f98c525063e6414a109b98853c423f6510831c754c43c875553544208f191528c71e6315330a798c5110a3d658c540c798e5210b2d62d5132d8549100423c63151309758f54c823d61d5120dc4c5500c73b4194021c7552530871e53d0010ae582424423d65950308fd81548ca3e64943319b98b530432e52d04108b98a53d071d63d5320e390d320cb2e52d0431ce992500863d6194a438f596420429e63d0731d3d0d5290e6e6214c208f59632d077151880208f988540cb3664544208f191530863f6510a30ab98843c866c6254d108f593538878f544c8328f992544c31f6554e42a718d414c71e5494c218f99642cc23e64d4c10a718d404c26e62d50328fd91534833642944308f59251c82756114e20cd109510823d64d4b108f594428c63f6055221cd552510c38c644c832cb58a53d063d6510c21ae58042082ac6255110cb5865290f2d5210810d3151320ca5d63d5321ae580315032e62d53218f59642107356494420ab18941883555394420c794d410431f6094e428f18d5010a3f654c9408fd91524432e62d53318fd9152c423f6054643a798e428823e64951208f98a540c63c6550531cb994428cab66114242ab98b404823d65108208f59352042b561142428fd94434434d5394810c798a5390aae6290e209758c540872d52908318f583544863e6414c109
  | 6 => 0x23d65d0620cb9825290e3e65d01308f19531d032e6215320ad584438863e64951328fd9153c426e62d50108f98f54c87d153440109758f540423d6494b308f197414c33954540318f197215038d320cb418f58754cc23e63151308f992544c6b96010e109dd85534827a60d4c21f44c5304423f6590c208fd81544423e65108328fd9642c432c52909418fd94438823e65cc9418f992534831d53d4242c7d4e5390b2d5250010cd951510c3355150020cb948420c63c6590d21cd59151082ae6290d318f98a548423f6454831d9549510c23f6550040cb14a425031f6494c21ce10a500c72e5250430c714e435071d53d4642ab9885390a3d64946328f19153482b96010c30ab58a4310a3c6255310cb58b54cc63d60149418f98854cc63f6590d10ae58031d02ae6290f40c7192530832c6454830a798c42cc23d60153218f996325025e63d50218f99253c871c538c5408f5865390a3e64d49318fd91534423e6590d32c7951530425e65d0d328f594428423c6355110ab98b54cc74d53c8421c794e4390aae62d07218f59250c871e5310820cb9485090e6e62d5331ad58753d063d61550108fd91530871e5314242cb98a53d031e5454c2197596530871d5454c108f59253c863f6454e10dc545300c2b960908208f590514831e53d0e42e398c428cb3a6454021cbd92520c23d6510d10a7994434cb2c6194a43cb553428cb3842940218f59643086766114e20c719253043aa4248020a7d8d505063d65d0020cb948420427960d4c21cd90e510c23e6590d308b98b54cc35553c4010d6cc5500c73941540319798e52d073964940219e980540c67960150218f98a548c63c6254740c794e43907396454021ad58642087692154021e3d88434ca7561141329e580540cb7352440108f99054083e15244010ab98a435069e6390d328f996315025d6314b108f58754c823e64944218fd85548c38d6294c43cd58754c86b96090a10cd58454c863d64141328f596421029e6394940bc181214423f6054442ab9885110e3f6454e20cdd85544433651500209758c528423f60550108f994424c63d65d0630cbd50424ca3d6494030ad58643cc63d6590d109d584540cb1d6194e42e310d32c863e6295010ce909500c72e54548109798c530863d6115330ab58a43d072d5494830ae583414432e4354831c794c43d06ae62d5330c754f410827b6544010cb988540ca3d6014d418f594420c23c65109308f98b54cc69e6390831c7551530823d6510c20cb15232c863c64543318f98c544826d6294f41ce10d500c63c6355221e398843cca9e6210d32e6501300c2ae64cca328f58454c82b76150310cbd91520c76552c4010cd90d510c32d54548319e980514cb1c544c9308f593524c23f6590c21ae580434423f61552209ed95300c23d65d0410cb58b
  | 7 => 0x8f180a00204e0080a22e0e62440180d05a0000001700405c000068bc03c1296004800c2d80b0040200380223e0000e8170a61800086b0596740200a000de828000004004118013640005980200008c2701d7a80a4100030080282001200e028040a2018028008060140200190d476038220000020981e03e1201801e0000140900000101000c1b8010020681780100001c0000000e0040402526a0002a84d1f43b4308012a400c04009056008012a3836004488090005c02680000a0004b00000a3941384700002c00800000004030010006880881c2900000203e17c008000030341780000a0ea0682a87f000088000060000701580d0040f00a0170000023f650cb41ba181324823c6590f208f992500cb2e52546438f596430831d53908218f191534431c544c9318f195315025d6394b408f58254086b561d4b418f98a548c33751505408f992500c63f650cb40c794f410423d6114d409d584530831e53504218f592534834d524c0308fd91520c23f6454321ad586525072c5210910f8949100426d6214f10cd952510c3655294430c7192530872f6494a438f992500825d63d50208f98e548829e63d01308fd9151cc33964940318f99632d023e64d4d208f592510c6bb6054940cb951520c71d5310e429798c520423e64d4d21c714f32502ad6214243c794e420863f65504408f59353c42776544010c798f54cc26f6254d10cb952520431e53d0a42a718d418c23c64548318fd95410c63d64d4c108fd85544423c6255110ae580325023e6494b30a798c5190a3d6590821a798e42902ba6014c42a798e42c823f61552328f593530823c62544438fd97418823d61150328fd95410423e65d0521ad584424431d5310c218fd815190a3f6510c108f597400431c6454c108f990530823d61951108f59421d031c6454c21c79825390a3d658c740cb98a5310e9d6394b41c714d325023e65d05318fd9521503395454021cb98b540ca7960d5031ae9805110eac6254540c754d400432e52108329b98b540c26e6214c108f596428c69d6308540ce951500863e64d4d10c754c420827b6550040cd547410c25e63d5320cb94a420c2b960085408f19541cc23e64d4e10ce90d500c72f4394a438f590524432c4394830ae5805210e766114810cb549400c32e52d0030cb5485210e9e6390a21d3549310c63c6454810cd947400c23c654c940c798e52d034d52cc030a758f5090b4e5354810cb58a53d032e5254243cb98b54c82b96094940ecd05100423d6094f41c794c430873664544308f59250ccb2d5494810c798f54c823d60151218f98b544c23e65d07208f994424c29e63d05318f98c54c834d5348020c715332cc23f6510e21ae583418434d3254432c794d5190b8c424cb308fd9642083355454420ab580428ca3f65501108fd9721d0
  | 8 => 0x801006c4a8021260000003c000630048020000f00ea090020440087f00a5bc0001803438c0a04d02e0a412826070004db80000000057000ab80040d81b0121700900025a02c1e8000105f86a805000001a681d02c9740501a002000000140960180309f11c1ba108000042840202b000c406c829000020058755a00401c8020061f830000364510be00c00c0607f01d0601d4060013d401008002036004000ea05416801015088030100620040340d0010500080400a0820000501c0340780b0040000dd4800d0001280100400c0040180000814c06804005174008920021003d81706e0140480325e00000002000000018010260540027e00e0880106e05e038bc04101a02c000541360283281f090000008000200024801c14e00c008000b20380001623a0000282f16e02c0580f0000781780002c01000081000224008dc01600006810000394100110280a40004e0cc068320000160080008600072d208020080a00327300a5b0bc81b0840380c8040049f80201800602c0202f00600002868004254508ef00400c198090000503805b038058120100000f81d05c002008009c600c0040100f0660b42400b00c0065300004e0046fcf00f60880400700e1ec001590b20b00900d00a2e0018200001d017021008034000020080e41a80b01220c098a70021f000000006348078001100042682100000002807000068008a8180000000200080f0000b414a00c0c80e04
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x18c1e739885448286b9cc42a6414a5c06194a43a4ae229042a07126454d100420ebb4a628c858394e6290c10838e6b2c42a042d7598a430c2a8b9ea488021439cf645481083ce7b2c8408709535012008384b80a899065079ce65d0720e42a4212200852571151320ca0e39aca212218a5806094a43e24a8a9a200860d6398b54c870731ac5aa663619ce424842185ce531ca88872152505100420e39acaa0221431d4434c920a34e7214a010c2e7298e54c4298b8c86a806307dd9539081085ced21aa40861a539805190a94b80a8990654a5c0548c832a1ce6304a521d1a73909500870b31ac22a0658a94a6014643a1cea318849942e7298f515020f39ecb90e8183195320c941a34e0314a721439701944348698b8886a80638554d6114c4283ce7b2c8588685325843250785380a8990650b9ca6395020c1aa73148610f11414c5500c6c4b80a899065865806094e42e448490aa010e2662584540cb91212a290041255c66390831872e03288790f1153505100429339487288614c5c04254420e42c8a92200860d63148215030d31ac02a661c454c42440109a2e030a6498e0d531894108306b1cc5aa641439cb6454c20a1ce5b22a610f2154549100424cb80c6a08618594d61142429c2e230264905167390a510824639ac2212658314d620c540c4ca5308a121d167118a5390a0fbb4a721043641cd6444010a62ea21a200850e73d91520c617394c72a4210b1c96510d10c2cc6b08a998d8970188434cb06318c4aa2210b5d66290c31a52e021aa418519701865390a87396c8a98218398d529081083ce7316a0a0c1e7398a54c4382b88a899065c85454048020a1ae4298868842d769485190e68b98c290221465c06294e42c18ca99064a0741535491004390a948488021615c4424c931c1ac629484a0d4970151320cac939c8488021071cd64d4910a2ce2304a7217116454d100428d39c85280638654d6014c42e22a8a9a20086155358442087903a2a4880218a9896015320a4ae22a4641950d7398854c864639ac021265629ce4248020c4ca4b08a121f137454d100430732887a1265071cd6550620a1ae529887a042e72d9731d021ab88ca21a41439d76310932a62e021aa21850c7510d32c8312a92c2290870d5c46510f20a2ae229862a072152d051004388a9c84880218a989601503283aeb31c8410d8571151320ca54b80c4a0841295c66290c21870eab00869050e72d925308617390cb21a41615c4434c921858e4b26a6884e170185324861cb80ca212630b9da4354830a54e521ca010f0552505310c790a928088021079cf6590821a12e02a2641942c725954044287396c929841891895150420a4ae221aa418d2a7290d50086863a88499261d054e52440109c2e4302628850e73d92520420f39ecb21221c454f4144010
  | 1 => 0x5390b0ab08c329c858398e5290810c18c6a92821850d731484244287390c329c850b9d8544c832a62e1212a21058a7290d300c2953948728063625c06310932a32e02a66419528725915008686b9ca4216838518d5150430e0aa6a0a4210c2e7298e5404307b18c4aa2218a149600854083cec2a26419711535011004286b94a621e83c2549404c030a4ce521ca21063261580540ca0ebacc721021499c46094a43c28a6b08868842e72d964384268b88c099261079ce6295110a2ce7212a21853375591100428ab88c129c85515c4544c832a1ce5b24a60853171909500860f39cc52a421499c46394a43a28e6b22a21858970109324c216bacc5218210b9da4354831a34e7212a018f22435491004314a92c0290870b9cb6590d10a1ce7b24a41841f7694e420428b39c84a88414a5c06394a43b44e521a2008712434c5500c698bacc8880210b1c9658c540a30e6b22a018d3171109500860ebacc7210414c5d44244010a1ce7b22a41871151501300c217396cb21e21431d4434c92186ae231aa02143475584434868739ec929063c854b404401091cedaa26419616539845090b14292c0212218a9496014643a1ae02a26419439701895110f0632264a8865231c96010d3285ce531ea0a0c1e73d9152042d0392c888021435ca631533183ce7314a80842d7598a4308286b9ca421681439d3654c832a54e031ca521c1e73d964208306a9cc5218414a9c06194a4385ce532e839860e76151320ca0fbb2a7210414c5d64244010872e031aa22150d71151320cb0d29ac028c85c454e4344010b0ae23188499720435491004282b88a899065431d4434cb21a2ae22a6641950e731865290e4cb84c721061439d2544c832872e032864a0c1f7694e4208287390c129c858398d62d5330a62e121aa21841e73d964284388a9e80880218358c5290940a2ce7214a21851970151320cb0629ac521a838354e6290c1086ae2312a021e1a63580540ca17396c8a9821431d4424c931952e1314861050e76151320cb0c29ac021a21499ca4354430e428290aa010c1f7654e4208712292c221221469c06194e4291cec2a2641956175949100438921aa298061345cc6048510c18c8992a01941d7694c5090b912a2a488021495c46394a4385aed290a121e0c5358a4350217394c72a043c454c4344010c30a6b0062a051571151320ca17396cb218210b9da4394810a4ae2304a521e195358042082873a8c421a658318f6255110e20e8a9a20087226454910042a8baca688021385c8614c11086ae23288498689325803250391ba2a4880210b5d66290c21b0ce521a6218c35711943250318b0ac02a0658c5866015032a1ae5318a998625611865290f13312c22a643499ca4354420e0ce22a2641960e6354a420c692392c8a8841079ce62d4540a54e521aa0
  | 2 => 0x60005804000a81434090103060a80983c1c000980074050880006330008c060003a300c070200006030006000020082028050003800410003800d301004161c0180c10090882c0202108acbc0102d5426030187c0000028814000000f00800010d800000b00802690780000040000c4828000042233000dc00060c89006070400432260000808af0000402050595002f4000d818040898800090c05c060012c2c72595418c3a129aa488021231c96110d32a62eb21a20085897010d324830731aa521061615c46210d32ac2e5a9a20085157118a
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x2848006000820054182400430a0000189420c4000031ca20a7828e0200001909801d4434cb21b0282dd15344010921809ca4354420909859ce4248020c05635c45208540b02839092154021c21615c06194a43a098098d5290830905811d4434cb20a21801895150420904855c4434c921911819ce4254031909859ca434c030a058198d5290831909801d4424c931908855c0434c920a05839896115321d01719c0544c832a098214d6010d10a118018d5150430a05831496110910b00825915344010a098298d60153309138754e4244010a09839896015320b0283dd15244010c11615c06194e42a058298d6115331c11715806094e42b028290d3154031b02839095148020920875915244010c21715806094a43885811c96010d32910875915344010a058114d620c540a118114d600c540911859ce4244010d01715c0544c832d02715c0544c832a21811496008540a098018d5250430905811d4424c930a0980195320c941909801d4434c921c05535c66290c21c09535c06250420b00835915244010889801cd6110932b028290d514c030921819ca4354021d01539ca4344010c09535c26290c20a0581195320c940921859ca4344010905859ca434c431a09831496010910905859ce4248421885811cd6010932a058214d6110d10889801c96110d329228790d5244010d027354a4244010905811d4434c920911809ce4254430
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 48
  | 5 => 1044
  | 4 => 1671
  | 3 => 343
  | 2 => 65
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
  | 6 => 2*((h/44+packedAt s3K6 (768+(h % 44)*6) 6) % 48)
  | 5 => 2*((h/390+packedAt s3K5 (28188+(h % 390)*11) 11) % 1044)
  | 4 => 2*((h/571+packedAt s3K4 (63498+(h % 571)*11) 11) % 1671)
  | 3 => 2*((h/142+packedAt s3K3 (16807+(h % 142)*9) 9) % 343)
  | 2 => 2*((h/35+packedAt s3K2 (3900+(h % 35)*7) 7) % 65)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xe1fe1ffc3fe3fc7e1e38fc7f1f87f0fe0cf4cf
  | 1 => 0xfe1fe1ffc3fc7f8fe03f1f8fe3f87f0e333b33
  | 2 => 0x1ffe3ffc007ff1ffc01ff1fc007ff1c3cc3c
  | 4 => 0xffe0003fffff8001ffffe001ffff8001fc0fc0
  | 5 => 0xffffffc000000001fffffffe00000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x28028004088410800408241204821044045045
  | 1 => 0x408408088100a0104011088421202408112112
  | 2 => 0x1548449110494802aa40112148114aa0c28c28
  | 4 => 0x844155222240092532a2400192550221680e80
  | 5 => 0x19919983bb927249dd3c9e4800660ccdbff000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xfefee8e8eeeee8e8fefee8e8eeeee8e8fefee8e8eeeee8e8fefee8e8eeeee8e8fefee8e8eeeee8e8fefee8e8eeeee8e8fefee8e8eeeee8e8fefee8e8eeeee8e8, s3N, s3R, (fun _ _ => 0), s3I, []⟩
end PEqualNP.Outside.L_meta_36386
namespace PEqualNP.Outside.L_meta_36386
open PEqualNP.Outside.L_meta_36386.Model
def s4K6 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x40032c802144001022fc41f843e907c32fe65fcc7f90fd21fa65f4c7e107c21fe61f8c7f887d30fc61f8cbe087c31fc43f443f907c30
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x1805000142a161e0441000020c81a0100994f84c028101010010182a030500138010002810020a0000600bd43882f50021df31cc3b8cb20bf414c2f50f20bc43886f10c21be42087e90032bf42442fd0d20bd42042f90221f930442790c21ed32c82f90730bf43082f90910b940087bcca32bd438c3d44010dd32cc6f90231bd41cc2f10d21be420c6f10520df314c2f90031bf404c6f90630bc43083bcc932b5410cbd90430be420cbdcc531de43086f90d10bd43082b50810f930843c44010fa20843b48020be430c3e88110dd43042f50c10f610442e90031bd40887e50021e9200837cc931cd320cbb88120be40cc7dc4210b541082f50e32bd400c7d90432bf414cb7cc030bc43843d48710ef20083d8c710bc404cbbc8421be408caf10f20be41ccaf50430b9400c6f10f21bf430437ccb30fb308c3dc4010ef208837cca32b9400caf90032ee42043b48720bf4344374c030ee32c877cc431bd400caf90021be43c82fd0f20be43082b90831be42843d4c521bc424c6f90631be40082f50830ed420c3948421f721486f10e20f621442e90032bf404cb7cc930b6410c2f90d21be41882750c20bd41c83d48421bc42c4364c030bf43086f10d10bd43c87b4cb21bc42042f50e10fa30882750c10bc424c2f90810bf42842f90720be42cc7d4c510bf404877cc631b641083ecc130ed320cb7ccb31bd410caf50910ba400877cc230ed2148374c730bd43482f50331f920442b90810f910042f50c21bd42cc6790c20bd42886f50a30de304c2fd0931bd43c42f10532bd418c374c931ad420c3d50420b6410cbec8120be428caf50420fa10042f90632be430c7d88710fa40087b48421bd428c7e48210ed420c6f50b10dd314c2f50a10be410c7790c10bf43486fd0e10bf42042b50831be408c2f90c10be43087d88421bd40ccbe88020be42cc3d4c710bd420c6f50610f5310c7e90031bf43c86f90430be4084378c932bd42882f10530bc43042f10131bf42c43dc8621bc42443ec4110bc4348374cb30bd408c7e4c220f6310c77cc832be42082f10f109d43086fd0930f531887b88521bc40486fd0520be43c87d50430bf43887bc8621ee420c374c930be40043d50432f9400c7ec4210dd43082f90e21dd310c6f90830fa30442f90c32be41082f50632fa3048378c531be428c2f50620f641082f90f10ee420c774c832bd41ccaf50e21bf43882f90e20f920083ec8220bd43486f90410ed32487b8c832ef21482fd0f109e43043750c21fa30842f10a10ed42043e8c030be43482f50d10f7318c6d50430de43082f90a31bd40c86f90421d5310c6f90621be400c2f90432be40c87d8c621be43843b8c921be40ccaf50b30bd408cbbc8720be42c43e50032ae420c3e4c030be40883b8c920bd438c7d8c521f631443d48510f930483b4c920
  | 1 => 0x6060380000228f8aa0b0002c2a070c00c0200000100c000d83c0025198d40c0b1a000022e00000120100028000100148080e0f25408003a8780001758b80600000004e00000002c2c009540800033380e0f07818100c4d034060016878
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x631d5310910cb21a82106550f100425ca4218411e5310b10962a26490e350f210869aa71906554514c931d490a8010e390d420435285080219b31500319d28086086c505300c31a8498863c532904329ca808610e650d2008276a0a1a43954348421b4292609066509300c32a87108438e43908109caa420084794c43086e0a098a21e141480209729087886310d32c866ca221843b14244010f0a1220085954a210863ea8980612d52d0c10d5aa240104d94443483488290a41365110e20c69928019624c9400cb9265200658c434c921e2a1a4210d554e310c7a286880211c53509109729082986c506400cac8a498a43a141480208f298861053d51320cb9264a006597544c431e4a1260186610d30483c48488021e121481109baa24210c754f420425aa420263365110930d9a1a20086a90a400c7288698c43a12150021972908610cdd51310c66aa221e411d5490c2096a90878861509310c766a8880211e53d081096a908708724c9304834a64a08659b3250032c6a1a4210cbd51200826ea888021b241500329d28082995a54a20083a282980618d4348020ca98a8018f490d100431a8598061a5428c4318fa9a84886c485400866aa2212619541cc030cc21a610863509300c23aa9218218c434c920d4a128018e950910043288698a433b544401097296860869109214423aa62102196439042097290868855d51310c7928690041365110c10caa1a20087190d210866ca22102164514c921d5a1a40104754c404872a64a08651d5310520d4a1220084e151304425aa421821355110c209b28e86104b552420432a82980612c544c920cc98a8018c794c42843328688021675448421b828242886a4c9400cae0a298221d1314c110e521a40104e940430826aa3a1841854348421b5aa240106a109208426ca221e41aa3250032cca0a60186550e410834a8498863a64290430b428264906c506200825ca421021345150d20d9a1220084d15131442b0a0992611e53101219aa8887106690d40087c48290041b2215002196a9082986c505200825ea8908432d5210d10d52128018e250d2008274a021e4394414c53097290860866d51300c270a890221685048520cc21a6088714c9314871284980618d3250432c62126498ec906400ca3ca621821a14244010d8a0a80194e940424c7308698441375150d20d590a8010ce54043487488490e219131500319daa260186450d100425ca421c211e5310910e299282196650e4008752852006394434c510d3212821865509310c76462a006334544c521d3a1a4210cbd51320cb8a849886391414c030d2a14821847d51310c7a482980618c424c930adaa260184e94343086e2a3080213950105329ca808498ce94042043a26320063a54348421c6a166218e98c9410ca74a021a43395010e21
  | 1 => 0xe0020c118141c0e04800021d0d13410170000406010481ca81201034142700804083d1181846010f0060a0601074ac00330004812150f96403110000c00000785200080ac520a008c400030186c2e03028040222159ac02463906400310280c002a01008005b8001c04431a9a8000119664c9400ca74a0218431f544c832caa1a82104b14943443348720043a541c8020f090c8010d6141314c35285180618c434cb209c2a260906a10920442b2a7180618532504329c2828690e510d31c4268a890a21c6424c4319aa8886906350d420434a42a0043e12150021d3aa24210e650d400874a84a0861994388020d8a1a20084b948404c63ca620a41a9424c030c7aa26419744c5400c74a8290041a943480209daa2401065cc9410ca72a021e438d43c80209aa8880994794c420426ca2202653a5010e218ea9885886350e42043628318061a542c4010cca1c20084d9444308272a1a1843ca424c030d4a0a40104754c428423aa921843735444010b828a40884bd49434436262a
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x9022c280040180000148021cb40894a040a10a383ad282c88698588514c110c81512148110e04c94190032a1588434c710a4191314c110a85924244010a2588434c110a81912148110a4584434c12092588504c530e090d2150021a1584434cb20e050d4244010a1584424c930a158c4248710a158c424851098580524c521e0509414c030c1151324c521a4580434c621e050e424401094580514c931a45924344010a2580434cb21a158c4148520a2588434c210e050d21500219458c5048510c4151314c110c2151324c120a25924348020e05093150031e050e4148020e050d414802094584504c930a2580424c931a4584434c220e090d4148020a2191324c120a15924348421e090d424401098584524c12098588504c510e04c94150032a258c424821098580514c921a858343484219258c5048520a85874348020a2580434c921e04ca4150032e09093150031a1191324c521e05093190031a4580434c521a1584434c920e0909414c030e050a414c030a858b4344010a258c4248110a1588414c5309458c5148110a458f4244010a1588434c51098584504c920e050d2190021
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 24
  | 4 => 302
  | 3 => 279
  | 2 => 66
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (i*4) 4
  | 5 => packedAt s4K5 (i*15) 15
  | 4 => packedAt s4K4 (i*26) 26
  | 3 => packedAt s4K3 (i*37) 37
  | 2 => packedAt s4K2 (i*48) 48
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt s4K6 (4+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/15+packedAt s4K5 (360+(h % 15)*5) 5) % 24)
  | 4 => 2*((h/121+packedAt s4K4 (7852+(h % 121)*9) 9) % 302)
  | 3 => 2*((h/100+packedAt s4K3 (10323+(h % 100)*9) 9) % 279)
  | 2 => 2*((h/29+packedAt s4K2 (3168+(h % 29)*7) 7) % 66)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffdfd273c777b0cf
  | 1 => 0xffffffffffffffffffffffffefe39cf87bd333
  | 2 => 0x77fc1f3f83ec3c
  | 3 => 0x7bffe03ffc0fc0
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffa0448401108045
  | 1 => 0x10882108210112
  | 2 => 0x9014052020428
  | 3 => 0x6000aa4400a80
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 15 s4Pos s4Neg, 0xfee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8, s4N, s4R, (fun _ _ => 0), s4I, []⟩
end PEqualNP.Outside.L_meta_36386
namespace PEqualNP.Outside.L_meta_36386
open PEqualNP.Outside.L_meta_36386.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x118a0250010800000c10411004813110820190c1fc30fe21bf43fd31fc42fd30fd40fe42ff10fe30ff42fc32fc41fd32ff43ff21fe31fc10fd42bd43fe32ff30ff31fd10fd41ff41bd42bf42fc31fe41fe10fd20ff40fc21ff20fd21ff32fe40fc43fd43fc40fe43fe20fc20
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xe437e52d06fca2205fd45329f2a2657d53d02eca2196f55031bd28063ef218867aa8995f54620dfa8687bf425027ca998efd0c219fa9a857c514c33a87195f95330bf28443bf4350a7aa8104f95321dea1e855e53d0af8a4087bc8421dea1c219d43cc2fea4a0dfd4d20bea8841bd43902fea8906fd51109eaa465ed200837887a16fd0c10bf28843bd42c83f4a018df54043fca02217e51886fca4085f14d40dea12217d50d0efaa7a0dfd5320df28e85bf5150bbc8621ef50d21de29a85bf5050efaa8905f55220dea1441f541106fca818e7d4d43de28287ee42ccb7a87217d54432cea9e85bf434c67ca8084f55243be2a4657d54906fca710df15020f721065bc50d0efaa1216f95330f7a12857d544c6faa2214f55320fb90c43bd430c3ec6310ef50b32f6a1665be540c37a86a05f14142dea8a85dd300c37aa9986f94f42bf296879d430cafca820c754f42df2a6657d5390b7e84a0df95332deaa6657d53086daa4187b50832bfaa265bd420cafea9085f14e20dfa12617f504cb7a85207794f429eaa065f7318c7ba86987d50710bf29061f641443daa4185f94f2096a96877e53083eca2205f54241bf288637e50d077a8621efd0b21b729083be4350efca2086f50a41fd080217e544c778a7a16fd0c209f2a061df308c2fca3105f14941fba0a83be4250b7e83a05f95120bea9c817e54087daa418ef54343dfa1c437e518c2fca520df94743dfa1e63fa300c3f660985f95121ef21a617c540c6fca320de54041b6a9063ef20082fca0187d8c710de21a857e5010bba8621df15132dfa04817d54842f2a0195fd4141bf28865bf428c7ba86195fd4c21dfa1883bd41502fca8996f94143dea1a83bd424c73a8698df94b10de296873e5410efca3a15fd5321dea9287bf424cbf260886f95320bea94837c54086fca518fe4c220dfa1081f531442fca5085f95110bea8c85f510042fea890df15330bfaa665be52d0efaa9185f95320dfa8e87bd434c35a8490df54a43be29c217c544c77aa3a16fd0b32dea10217e54882faa1a15754c41bea8e65be54c877e84905f95020dea10417c53886faa3906fd0f10bea94217c5344378a1a16bd4942beaa6437e548c6f8a8194f55021deaa2653d540437e87186fd0b40fd28065f631486fca220cf95032bf29c81bd54cc77ca1a15f95321de292877d53c43dca5a1db54810fd90241be544cafca418df94021be28a413d54ccbf240885fd5220dfa1e8375511037e84215f94010bf280817c54842fea710d794c10bf2a085bd438c6f8a690dfd4c10b6a9081bd43c86faa1195794c40ef98061f621442fca998fb4c921bfa9263bf424c6fea0a15f54a40bf28c63bd42886faa2205f54640bf28e617e5190bf4a010ef50c40dea00817c54443ba64985f14930cea1e637d52886fca6907b48520
  | 1 => 0x6510c2fca9885f94732dfa1a617e53d06fca7a07b50921dfa1c63bf438caf8a610fe94041be28a85bd5150efca7217750f31fb10e21bf42cc6bca6106f50940bfaa021bf420837c82a0fe540329f2a66175510c2fca8206f90d42bf294857e501077c82206f50c10df2a0217d500867ca9995fd41319eaa6617c515037ca3a1ef950329f2a063fb40902f8a790efd0c40dfa1e43bc41903bc8798efd0841d6a1065be54cc7de43905f54c41f719643ed42c83dc64905e94041bf294657d544c2f8a6a0dfd4f20df2a0637f53502f8a4886fd0d32bfa9c417d50cc6fca021f754c20fc984217d53443f440106fd0b10bb28841bd43082fca6085f94d21f799465f541442faa3985f94242fa98a437d500c6fea898ef50930fd182417c54c86faa118df14543b729021ad42c837ea1a16f94542f7102417f53506fca4197b88521be2a6217e52082faa5a1f74c931ef994657e530c2f8a8085f14121dea1e639d434c3ea6218dfd4542dea1c43df32cc37aa990df54610dea12837c5350afea998fb48421be2a2437c53c42fca0105fd4540fc980617d51d037a8220fe48210eea98817e521037e86215f94443bf2a0657e5410fde64996f50c21bea8e85df314c2faa69077cc931fb884217551083dc8590ef50a31bf28487ed320cafca6196f55020dea18837a500cb7e87105fd5020d6a1665fb10442f8a6085f15331b6a9083bf428c27ca810df54e20ee996637e510c2fca610ef14743b7296877d52c42fea48877cc631bf2a465ee520c3ec62885f94c40be282636e520c3dca420efd0f20fd984617e53c42faa21877cc832bfaa621bd424cb7a87885f54910fd184417e508837aa1a15794c41bfa90217c524c6faa5985f14d20bea96837f5150f7a8590dd94440bf28465bf43cc2fca1995fd5031ef99663bd52d0efca4217b90920bf29c41ee32c82fca3906fd0540ef29821bd42102fca8987b90842deaa021bf43443da84214f55031f7904417e5190efca421fe8c1109f2a641bd424837ca9197d484219f2a0417e5310afca2105b94831bfaa465bd43d06faa690fe50040ee98e61bf51d0afaa910fb50b21dfa14217e50906fca190ef90f42fca80837d51d0efaa7a15e54021dfa1481bd430c778a2a14f95042f6a9021bd428cb7ea0a15f55330deaa0437d50107baa620dfd4121bea80655d530837e879977cc730dfa12433d540c2f8a2996b94b43bfaa2217d5210f7a87185f94210dfa18657d538c6faa420f78c130fd20221bf53d0af8a5086f50842fda02815d53042f2a018fb8c832bea9663ed42483f2a018df15320fd104217d5490bea43885f94b30ef29843ee42c82faa998fe4c120de208817e530c6fea7885f94b40bea9881ee520c77e84186f50b309e2a221bf43906fea8195f15221df202817c544c37e87216f55030bf29
  | 2 => 0x851441a0080039c330009dbd40107402008270d42f0180203c13058032cc000f96f1a0011ec01014002604402402004440240004dda15425034b5020270501400c10cb4030180808000120218500000030000090955005400dea1a65fb108437e85986f50b31dea10437d544cb7a86905fd4143dfa1c81cd320cb7aa0a15f54643eea1e617e53106faa121dfd4d42bfa9c21f621086bca610df94031dfa14653d52d0fba87196f50841beaa465bf41906fea9985fd4520bf284617d53042faa720df551109f2a4653d54c87dca4086fd0b20dfa1065de53083bc87987754c21beaa487df4350ef8a0a1df95010ef21c65bf5150f7e84886f50c42dfa1c217d549037c83206fd0f42fb18863bf42882faa710df54830dea1e817d540c2fca721df94640beaa641fa30842faa818fdc8521bf2a0617e5310fbaa7a15f94231bea86837e52442fea8187d94420de2a2217c53c83e220085f94343beaa243bd42c42fca198dfd5021ee98863ed32c86fca420ef14543efa1c873f5250efca5186f54143bf28481fb20883bc86195f54a31bf29481f641106faa918ef50b41fd10221bf430c6faa8106f55232be2a061bf5250f7e8690d754f42bf288857d53082faa8197b8c921f690e41fa408437a87906f50740faa88817e53d0afaa418efd4b43bfa9621bf42886faa221db54b43bfa9a437f54886faa3195fd5230dfa1483f5318877e86186f50f30bf2a421bd438caf8a0995f94342b729081bf42086f8a9186f55320be29281bd4350b7e85217d94432bf28e81bf42d077a85185f94e10be282835d531037a86887d90710dfa1a817d53c82fea918fdcc531dea1c41be5350afaa9886fd0831df286877f534437e8721ef95021dfa0081fa401037ca2a1df94a43deaa065bd53d0afea4a1efd4d43dfa18877d5010bee8320dfd5130f6996417c54ccafaa6215f54e30aea9843ed52107de85215f54840ee99661ed52d0f7a87995f54432bf296637d54ccaeaa2195f94821ef192657f53082fca31977cc930eea98217e548877a86197750d31ef21a637e500cbec20887b4c920ef18a63be5050afea2986fd0810faa8841ed52102faa5106f50a10f790a41ad42c86faa3186fd04419ea9e85ee42487f240106fd4942fca0421ad52d0f7a8720df95230be29287de53107ea63885fd4a10ef988637d53842fca6887dc4010bd28043bd420c6f8a8905f54810dfa1a837f524c3ea42885f55021df2a041bc51d0a7ea8886fd4d42dea1a637d54042faa7196794f42f729081dd314c2faa5a06f50830bea8643bd424877aa6a15f54221df29287ad42482f8a6107e44010dfa1a41f9500867aa9215f54a30dfa1e81f5510c2fea790cf55331bea86657e539077aa3a1f74c832bea9e4376510c378a0a15fd4940be2a441bd42d02f8a918df14b10ef29881f
  | 3 => 0x7050001cc04038140000311004410120f40517c00024032f422000000348d2c8000307502c002646e03c0300021058040500003c0404d980dc0f0500307004040000dc070140436870004700c8180081e1b80079c090941cc9c10014050005b02c08000031090911c0901800004141440c00ca7246c505c1e0042409e191540601010000127309d3c00000002389130000103c1d088b10880801e214283523002000bb0640b0242a020160e0000b01e0440000805014060040b06c000988b4f802044005d4050200c0104a00016000000080e0d40f0daaf01000014520345b09c0205804078230dc0050c220040400c0101026ba01f0041405c0500c0000061000000001a00c0007022018771bca50004401c620bc80000060501e9001e009
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xb204831e5350c419758c5050b1e53d0c10ab98b51d0f4d53948419b195324865d6314141ab58b43482796014f219d58453c831d6494c21ce580544423e64150329e983540c73554c4010c758153d0a3f65d0f21dc946500cb2c5350920c7d95430ca9f6250f30d5cc9510cb355190440d554e510823e6494a10cb14d424867a6014d21cb54a50d0f1e53d0821a758c41902ad644c8329d984540c31c6154f42ab58b434caf061481108f990538823e65d05409b58a544cb71518c0309b588548429d63d09409d984540831e6454c41d594e51083374354432abd8d42c863f65d0831c754f43d0a3c6454231cb551520c26d6215010a758f425063e6414910a758f429031d5310440d9509510cb2f6550832cb549428c31c5350d219b98a544c27561d4c20a758f420ca9d63d0931a758f428863e6494f20a7d89434c32f43548309e980530863d6295030ae98051d0f374394420e390d420ca3d6494c308f58e544ca9d63d0a1097596430caf0604c510cb992520c31c5350d208f59053842af6250e32cb949420c32d6154b43dc546401031d6494c20ab58a5350a3d6494d208f99052c43554354432a758c50d0b3742544308f994544431d5354742cb591520c29d63d0a418f592528c31e5350e40d354b310c76a52940418f191508863f6550830cd50d510823e6414520cd50e510c23d6414c208f58e540863d6494820a7d89430cb595348020cb551520426d6214131d690d500cab56114342ced0d500c71d4394832f14c9510cb9543cc5318f59252cc65e63149108f990540863d64948219d984504cb1d53d0c41c754d42103d253440108fd89540c31f6550f31cb54b420427661d5032c754d50d0a9f6250d31e350b32cc31d6315110c7991531031e5454c20a758c544429d63d09308f589540823d6595021e6181434c23f62551329758e544cb2d54c8020dac85500867b6548020da949500c71d5350441d94c9510ca8e63d4942ea50a500cb1e5450c43e398b5350e3d6550f209d587540c31d5350d108fd9543086ad62d4343d854910043555388421cd551510cbab42480208f593530866e6214530da549501071d548c932b358a430cb6932540329e980524c7994394032c794f421069d63d0b318f993504cb99434c1108f59253c423e6414a109798e544872e53509209798c548863d6494910d3149324c7394394032c7992530431d5454c20cb551200832e6054b43e950b214863e6494b1097d8d524431d5350c219e583540871d5314342c794d420431d5350e108fd95411072f5250930cbd9542c831e53d0c21cd551510c32c6154b43abd9542c832d52d0841cd50951103394394031ce50d50106b96010440ab592324863e65d0d10c755253082ad62145439718d524423d6414810cdd0e510ca5d63d50109798f54082b66114143
  | 1 => 0xca3e6494832abd95420ca3e6414e10d64c9500ca3e6494e209d984524c27960145439b988540873a5454021a398b5350ead62d0f31cb149424c69d64cca329b588534425d6594c20cb552520c31d53500409b988530425d63951208f596540c31d53d43428f59542042af6350b32a798c5150b1d54cc431cb50b504869d63d0b108f58f544425e63150209758c544432f5250931cb991520c6ad62d0c41a758f42cc399434c120ad98450d0e3d65d0c21c754c43d0a5e6314c2097d95300c3b14244010ce50950086756114e20c794d421031d4314931cb98a54c831d53508108f992530cb2e5494810a758f420423d6494d10c794f421033742544408f992528c23d6550830cbd9552d0e7765504418fd95420826e6215030cb98a54cc32d43948408f592528c6cd638c8328fd8d544cb715344010d554d100432e52509109b98853087564354432cb50d520431d5390440cb14d42c827a6014810cd15241442796014542cb54b42d071d5494c108f596540ca5d6594c10cb509500cb715148020b5185434c71d544c0308f1954344369528c0309b58a54cc34d53c8421e9509214432d6494831cb94d42c867b654c0309b98b540434e5354840ad5845050b3742944409d984548827a60d4c21c714d43c833551d0040cb94942106766114f20c794f420423f6454630ae9805150f1d43d41319b58a544c6b960147439758c540823f65508318f59742043655254440cb549428c63d64d4532ce551500c66d6214540cb549424427a6015021cd951510c32d52508319d987540825e6315310a758f420871d63950428f59542cc72c52509309e195204431f6554f42c795143cc36552944309d584540832c5350b21c798c544432e5250a40a758f428c6ae6214743cdd0a51082af6550b21ab59232c831d5350e20d954a511032d54487209758e54c86f161840108f59641102ad6210440cb50d521072d6494810dc546500ca5d63150109798e54c865e63145429798c505072c6550b32cb54b420c32d5214943cd551510825d6314520c750d50cc72d5214b43cdd0e511023e6494821e650d500ca3f64542219e980514cb493254032e9d09210871d4354032cd552510cb5953540418fd91518823d65d0b31dc55110042ad6490921cb54b41107394354032ced09500c73a5454031c758e548cace63d0a42dc549100429d63d08318f590504cb1d6494c10ab58b43c833551500409d98453482ad648c920d394d521063e6494c10c750c524c23d6414931c714d43c872f6550b328f990524c29d63d0b408f995434431e6395331cb551210873654544208f590530432d6295330cb50e52043374354440cb54b50d0e9e63d49428f59053c832d5254343c754f4210795434c6218fd95430c36952440108fd9742043374294432cb94d42486756114142ea50
  | 2 => 0x65440109b98854c42ad62d0f30cb591520c63e6494b318f59053c42766114c209798c544431d53d0840cbd0e52106ad62d0e10b6181434c2ad62d0d408f992538431d54cc030c7951430cb5a53940418f590538823d6494f20cd50d510c3355444010a758f42d072d52947438f592528428d644c8328f99353082ae6214143a758f420823d6494d21dc8c5500c72d52143439d584504ca5e6315220c794d430423f6550c42cbd0d520c71d6454c21a759331cc2ad62d0c32ab98b4350b1e5350f10cd50e51102ad6490920e3d89438cace63d0942cd50a510c32d6295043e3589430caba60145429798c54843d153440108758e544ca3d62953319e583540c71e5350e218f59253c876552c40108f191534429e6314742c758e54c878e544c832ab592320cb1d43547308f990514c29d63d08408f990504cb4e5394810e350e32c82ad64c8720cb58b5350a7661d4c208f590528431e5350e108f590534869e62d4d43d354d521067a6014c20e9509510cb1d6254f42ab58b434c72c65509208f990504873543944209b58854c427865501109e580524c63d65950108f592530867a6014c10c798e54c872e5250820cb98a54c871e6454c21f14c9314872f6550921ab58b43902af6350921cb58a54cca5d6315021b9185424866d6214141ab98b50d0e6d6590832cbd49425071d43d45308b588544423e6414d108f990540c73543544328fd89540823e64d4c10cd50e510cb8d438c920ab58b43886ad644cb21ce55210042ad64c8520a758f42c872e52d083097d95320cb394354031e550d510ca6e6215230a758e54c823e64d4810cbd0e520c23d65d08219b5885150f715154032cb95152043453254432c754d420826e62150108fd8d54c825d63d5021c794d430865d6395320cb95242ccb1f6550d309b98a54cc2ad62d0e418f596540c74d5354840c754d43c42796014e21dc945500cba942482109798e544825d63d50208f99053082766114e209758e544871e5350820e350e324869d63104408f592530c72e54548309b195424829d6314142ae5805150a9f6550f31da485500873a54940218f99353c867b6550040c754f431037121540218fd89540c6766114c10d994a510c3713154031ec505404425d6314121e950a510cb954394432ab58b434c2ad62d0c31e3509320ca7561150328f595430823f64549109b5885050f95434c710ced0a501071d53d04418f58a540c7595384010abd89434cb394294021ecd91100432e62953318fd97430432d62953318f59053c873742544328f595420c72e5250831ce552500863e6494d108fd8d540c23f6355010a7593314c23f63550209758f520426e6214f10c798e540ca3d6494c10ec906404426e6215031ea509304832e5250a109dd95310c62d62953318f990530427a60145429e583540
  | 3 => 0x32dc545300c29d6490d31d354d200823d64948108f99252083b154440108f593530431d5454c10ced09500863d6550c10c795153086ad62953308f590504c79943cc1308f992530c63d6550b30cb54a41103356115110a758f424431e5350841ecd09100432e54548319b988534423f6454231c754f420426e62d4c108f992534866e6214141e6d0d300c26d62152309b195424865d63145429b588538432d52547439d587540ca3e6414f218f58e540427a6014e218f191518832f6054b43c750d508cb1c6550d30a7592430ca3c65d0d10a7d9543cc31d5390f429798c528423d65d0c109758c548869d63d0a329b58b540c63d65d0c318fd9542042af63509208fd95424cb1f5350d42d454d100423d63953208f58d540c278654c1208f590514c2ad62d0f10cb50e520c36952940318f59743c863c65509109e980548871e53d0c20cb98a540ca3c6454910ca509500ca3d6295010ce50a500c73a5494032cd509510825f6550c43a7591324c66d6215231c7195438ca796014d21e358f5250b2d52d0831e3d0d320caad60d4942ab588544429d63d0a30c798e54c826e62148109798f540866d6214c10ab58b430432d5250a408fd8d540863d65d0c20a7591320cb1e6454c10cbd0e520c63d6550932c7d8d544cb3b4394021a798f51d0b1e5494c109d5845050e3d65d0831cb95142c874e5394840d354d210872e64548308f58c544425e6315021c7551530863d6414c21a7592434c33954540219b988538429f6250e32cb952520c25e63150318f990540c32d5454831c754f43d02796015221cd55251083695294041a758f42ccaad62d0f40c794d430c72d6494830e650d308425d6315210ab58b51d0f8d544c832c754f401035532544328f997424436652544409d9845050ead62d0c438fd9542cc32d4254321e6d81434c25e6314121cb992520432d6215110c7d4d434872d52d0b40d394d52042ad62d0c21ab9885150e3d6494830cd952510825d6594c21a758f420c31e5350c40c714d4350b3b4394041ce50e501071943540329758c528425d63153108f992530833b43540218f588544423f65d0b308fd97430823d65d0c309758c51503b34344010a7591324c26d62d4c108f995424432d5210440ab58b438c71c6054f42c754f430436652944408f59051483a46150921d9549510c31e63950428f590514ca7960150318f592538423d6395321cb553324cb4d3254432cb50951ccb1f6054f428f9944350b1d53d0f41c754d420863e64148109b58b540c2776548421cb951420cb3942540419d195214426f6548421a758f428834d524c431c7195434c72e5250a308f99253c426d6215030cb50d520c3354354440c7551310c63f6550f208f99253c869d60d4d438f99053c423d6414b108f593504caaf6254d42c754c5350a77
  | 4 => 0xfd9542cc69d64cc930c754f4310a5e63148109d987540c35653544409b588544423d65d0c32ab58853d0a74654c521c755253087315444010a758e54c865e6314520cdd0d510831e5350f42c754d4390b722154021cb50e521066e6214540d314d32482ad64908328f992520c6796014532ab58b430c23d6414d10ad98450d0a9e63d4342ab5875250b1f6550e329758c524432e5250840abd9542cca3d65d0832d5547300c25d6314b109e983540871d4354632cb50d520c72d42d4520d3549300c32542544329798c5050b2e5250a41e3989430cb2e5250b10ab58b438826d6295130cd509510c369524c030cdd0a510c33a5454032e9509314871f5350d20c7d4d43c863e64949108fd95420cb2d52d0840cb94d420ca3f6550c10a759332cc74c534c921f24ca500cb5653944408f59253887385490110ce50a500cb2d52508108fd95430c6ad62d0c20cb58a544ca3f6550821d394e52107a94254032c794d439066e62d5030ab58b435063f65d0830cbd9542c872e5450842d654d10042ae63d49429bd89534425e6314c21d9549100426e6295131ce5055010795434c5218f992544438c6250e32d654e200835953940218fd9543082cd63908329758c548831d5314f42d9549310c66d6295331c754f420829d63d43429d984530862d6295132c7591530831d53d0c219d584548c31543544328f59742cc33b4394032ae58041902ac6250d42ab58b431026e6295331d6cc5500c73b4354041ab59232c871e53d08208f59654082cf644c832ced0e500c63e6414f20c7992530863d65d0f20d554d21086ce62d0d438f99054042756115030da94a500c71f5350d41ab58b53d0b2d52d0040d9949510c29d6314542cd552510c32e6295043ea181424823d64d4810a758f42486f06048510cb58d52d0ead644c9218f99353c833954940328f9905408274654c510d654e501072e6454841ab58b43d071d6154f42cb19542486ad62d0f21abd8d42c838f424c832e350e420ca3e6494b30cb949428c63d6550f219b189534426d6594810c754f430831e6154f42da909500cb1e5350c309d584548831f6550d31ced0a500872e5494831dcd511004395434c5109e580540863d65d0820a758f4210b1f5350d40d3d95320ca6e6214131c758e544cb394254032d354f200829d63d47428f59252cc3695284010cb94b420c65e6314b10d354e521023f6550842e350e320cb2e6215110a7d8d42cca6d6215031d654d500872d52500408f590538871e6054f42cb549429063f6454d10cdd0e510c38e63508328f58b544423f6550040cb552520c63e6414d218f590524429d644cb309bd95200836a5254041cb94942042e860509209e980540ca6e6215020cbd0d521029d63d0a42d5545300c29d644cb319d584524c2f365440108f992538876a3254
  | 5 => 0x54c826f654c8328f992520423e6494d209b98854842ad6210640cd951510cb8d43508328f990530871e6454f42e950921c426d6214f109b988548c6ad644cb208f993514cbe121481108f58e54083b25444010e350b324c31d5350e419bd954210a756114c20cbd0e521023f65d0c21c795143cc7e152440108f590504865e6395320c7951530431d544c730dcd4d100427661152308f990504c72f4354841c794d430833542944409e580548c72d54c87209e983540caad6295331ab58b4390a3e6494c308f5935308399434c220e358d420cb5943540329b988544426d62d5010c754d430823c65d09108f992520c3365494430a758f42c829d64ccb30ad9845050a5d6314810c754e50d0ab960145439ed95100432f6255132ab58850d0e7a6015010e350b32cc6ad62d0d109b9885150e3d65d0830a758f5250b395444010cb549411078c6350b32dc545401032e5250821d354d520425e63150308f592520cb4d52cc0308f990534838d434c832cdd09510826e62d5031cb18152d0f394394021cd50a510832d52d47439d195414421d6315110c794d438833b4354032ab98850d0f4c524c930ab58b4390f4d3254032ab58b438cb365494432f24c9500cb8e644c832cb549420c31d5350841bc181414427a6014543cb54942c42ad644c920ab58851d0e5e6314540bc18540442ce62d0e43ce509500c6ad62d4d43ead8142483946150d31d314d32c863f6550c329d9845050a2d6295330d9909510cb2f43948109b588514c3555394440e950a314863f6550c43ce50d500869d61d4d43cb50e520c65e6314c108fd9543c87395454032cb991521029e6314142ab58b438c31d6454c10cb50950cca7661150108f59253883354254432e398f5250a7a6015031dc546200831d5350e218f58a544cb1d5314742c794d434437352440109d587540832e6454810b3591320ca6e6214143e3591320cb6551c8020ae98051d0a9f6550c328f592530caaf6350832ea50a304829d64cc931c7991530821d6395321c754f420869d64cc832c7d9543cc31d54cc730a758f424ca766114810cb50951c8365528c431ec50d10043395494031f8949100431d4354432ce952500c63c6454630a798c50d0a7a6014f21d98c9510cb1e5494c219798f540431d4394b30e5d85434c73b4254041c7992530838d62d4d43c7952438cb2d6054b43ab5885050e6c654c920ced0a500c71d5350c10d554d51082b561141439d984540cb1d53d47429e980548c72f6550920c794d4208678654c1108fd9742cc71d53947428f990524c71e6395330cb94d42c83655148020cbd8552d0f97434c431e9d85424863e6494a31c750e52cc6f0614c110d354e520425c6550d318f59353c825f654c4318fd89540432d54cca328f59253083565354420d64c5500c73542944328
  | 6 => 0x41708a0142bc8d860000004002790224400600200008800801054040098000000005200003c0000180835a030098000383c80100b00c2f8050030700000101100000c0092b10a0000002b000014098020ee1040000f0101b8028251ba404768060000e8040045800141905e9b6008018110000041c00f032134018605ee0102200200c03c070003a42980080b00016c0a00f0421500e8350061bc020081100540585d0d60001a8010020546cc6f0380100505b2fa00c000000140005d80000804c2780600600c220010e60043d03f0420800080c7080040000a01207c008260100100001308e078028000041b0090030da10400806004000008481fa05c0000000001800000014008002380660041400b128028000000182540a8150000000f000010000028158440140782a01c0008d800000010030000000180000001e0580000d0100b00b8120920140000a0000000006b000204118040000a8090040020000000000e0000100a00c2e0488000240240d80a0040240f80d07018c4a0450080200b9b11840280004c020000050610440404f000024074038790000dc040011b400c028581b42fc0000709604401057000155d280903a0640105100c01800804008020000003400100008e03e0145481001e01000128000030000000000004501d006008000002b4098030ec03e01c04a7300a00c0e8130f6000021400120100180006c0040200601a0000b80209200c1100604a190008140ce0040100a0d20081b84603c0a01e0020020646a1cb010004280000fe0085500100e03cb28090840080a80005811406002002018000000120d026016000020000000100b80500000c0bc0680239e068000053a80042d8450220280092cd694e500871f5350f208f595430865e6315010c754d439032e649483197195434c3736544010f14ca510cb355110440f44c530442b561143438fd8d54c872d6454810c7952530829f6350932a7d8943cc78d42cc931ced09500cb1f6254f429e580540ca5e63d48109e596100433b4154041e350b320ca6e6214c208f592520c63f6255330e3d8d42ccb2d5494810dc505501063d6494b108f99353087c9324c1208f590524c23d6295330d694d501072e52d0810a758f42482ae62d4d43da549500c6ad62d0d21cdd0d510c33942940418f990514cb5a53540218f59353c878d438cb21cb509510cba94248110cbd0d520432e6454b43cb95142c833b4294032cb55321086756114d20d314d32c832f52509408758e54c823e6494c21cb98552d0e3d6414d20a758f421075b3254032d554f100431f6154f42da509500ca796014c218f99053887724154041a758c51d0b2d43548408fd9743c83b06444010ae58051d0b2d5250a10b3d95320ca7960d4c21ab58b4310a3f6255331cb54851d0f555354440c758e
  | 7 => 0x70000300080802232800000004000010019c20240001304e19400002000068070020062c00001b00400402001004000170010540580002723a0880b836000258001bf00800c110300
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x851973d09500c692b88a6a16418358d52d083185aeda1ca420d1b7550d500ca94b9686a80658a195424c120e12e4a1aa0196316158054442d0b90c888021c250b3254032c2aa7308a1a152773509510ca92b9687288654a5cb4394031c32c6b00a88872142546500ca86b90c0a9e85345c06150d31a32e029a8690c1d7319742442983b2a888021385c8614c110e12e8992a01950d744c9500ca8d380c2a9e85645c06150d31a12e8992a01952572d0d511028cba264a80658550d6114930aa2e7a9220084e1711814248391a1aa4880214c9d95444010a32e029a8790f05438c9510ca98baa8688021439ce5450b21a1ae630aa5a1e0d635484110389a1aa298061515d13254432b22e2302869841d73195424430aa9ac228685c49515344010e20c8a9a2008705424c9510cb12a92c2286878a5896015110c2ac6b08a88850d729915304298bae8488021385c8604c510e14e8992a019625625845444216b94c929e21625d1324c12083aeca9e8410c2f75591320ca70b80c2a1243c85525244010aa2e7aa2200850d75991320ca92b968728881615d1324c521e1287212a01950d7299153102173b4a6a1243c29cd4254032a8ae229a6490585744c9510cb0731ac42a221c154f4248421a4ae5a1ca21050d7399252043a0994a2a8065439cf6550b21c1aa6b168608705544c9510ca46b96caa1e61451d5434c510c1acaa1c841941d73191508870ca9cc028e858358e6295320c1ac6b10a88841d7694f4210388a9e8488021495c4535092083ae7b12a81051973d0a500ca16b90c8a8c61c85494244010b0ae430a8698d1573d0a510c3a0a9ca488021625cc6050920e428528aa0195157114d43c8388a9a86880214a5cb4394021e0ce4a1aa21950e73d95424830c32a869824152dd1325403285aeda1ca40852b75509500cb88aa2a688021515ce4254432a4ae5a1aa21870b424c9500ca8ab88c0a9e850b5db4354830a92e02926498f23425452008384a1a64a8065d04c95194032e0ca8992a21941d73d89540420ebb4a7a1041615cc6150921a62eba1a200860d5358b430828bb9286a8865431c95350d1085ced29a849060d6354b42102943aa8490221465d7434c030a52e5a1ca020d1973d0a500c616bb686a9063435d66350832a1ce5b2a8798d3174d4d100420eb9cc9294214a5d74248020ac2e5aa2200842d76d0e5210287394a8a1e61075ce6494b10c1ac72968418e0d6398a54c86b0b96a6880218358d52d0810e12e6a12a0194b17418121442173b4a6a164145dd54354432a2ae9992a21951575d0d310c706b20a69924391195324c521c1ac829a6590c2d72191508c7a129aa488021625d1329403285ae5324a70852972d0d500c71232a8498a430bdd562d0c10c1ac6a968420d29744c9500cb0ab1aa220881495c46054b43
  | 1 => 0x5444383a1aa4988634a5d23254032c1aa6b1082206295258051d0e8cb9e84a8065435ca6454c41e228728aa01951573d0a510ca16b94c929a21465cf4254041c2ac230aa7a141d7319151882c2b9e8490843c45d15344010c1ac82926498d49744c9500ca94b80a4a1263315cc61509219a2e630a408848d73d9542c8384a1c64a8065c19cd4254432e12a7a1240104e1721814144307baac8990658394d62d0c10a30eaa1a608851573d095110270b90c2a0221439cb6550d3185ae5b2e86084c972181434c258ba0c098a21d04c95154032c1ac7296840860d6354b420c388a9a8488021465cf4294021c1cc6b14a99871143546500caa3ba264a8865235cb6550f31a92e521aa019706744c9510cb912a2a4880214a5cb4394032a52e030aa5a1e296018152d0f12b08c2a9687c15cd425443291ae9b2a641960d5358b4308790a12a2a80658654d6010440e1284992a01950d729925304391a1242a804349dd54254432a62eaa12200860d6414d3248217b92c7aa22185195434c521e22a929a200853174d491004383a1264a8865525c0534c921a2ae7a14a2207206454910042d0b80c2a12430b5c965d0c20a1ce7b2a8490cd171181434c286b9cc8a9083075d953d0810e0a86992a2195297014d4248692ba264a8865495c45250930b12e8992a01951573d0a5108258ba0c2982210b5c86550d10e1686a926018721745491004384aa264a8065439cf6550b20c1ac8292649854973909500ca46b9ecaa1643075d953d0820a4ae5a1ca2185a171181424820ebb4a7a108343dd5644c832a8ae521aa21960d5358b431020e3b2a6a1a210b5ca6494c10b0ae5a1a6218d85744ca510ca98baca8880218650d6014931a1ae7322a42054571149324c287baac4a1865c4d915344010a92e029a6590e255298450d0e0eb9cc929041c29c94354032a1eeab1a841972152d09100430731ac52a663435c86154f42b42e5a1a200842c76549424420eb9ecba10214cdcd5444010a48eaa124288625625444110294b80a6a1643c850d524401083ae7324a40851973d0a501070729ac5a1843499c46054b4383eeab22641952972d0d5008790aa2a488021865806054f42c32a6b00a3a170543909510ca8db9286a806507dd563d0810e2286a8aa01960d6394b420c2173b4a6a1643459c46054f4298ae430a8698d0e7395142c8306b20a699641545d65344010e14a8992a0194d1731812144286b9cc8a9021435d13254432a2ae7a12a21970643509510ca94b9686a8083c1d0d3254432e0a86a12a21958973d092008295380c2a9687495cb4354420a66e4aa220085457114d32c8216b96c6aa021495d2325443283ae7324a48851573d09510c32432a64982414adcd4254032b12e5a1a60185917319110042c4b90c0a1a61465d33254032e82a6a9220
  | 2 => 0x180a0600a6006080e0242e00078040601000fc000000805100105010106b00014201d070000c150e05c146a0383c78191e23800030206400471b8002c02000040404128080806020883e0d000ac0003148a03a000b80002190180008014203c0001001bc0a0a0883802000885800080021c02240303400060f1105c080c0000009000482c07060143c1202804101f0f1f814000c8540a073a800281b9283060030984c0b495d74248421a4ae5a1aa21960d5358b43106b0baca488021439cb6550d30e46c8a9220087057250d510cb82a1664a8865345cc6150110a18e6a92848841d7694f420868ab88a6a1a410b5db435481083ae7324a410e0e5358b430828cb9e84a8043c454f4344010e1286a12a019505744c9510cb913a2a488021075da53d0810962e830a40884c973181424820fb9ac5aa221645cf4244010a2ae7a12a21048d76551320ca16b90cba1a21455d13254432c52a5300a3a1d0d7318152d0f893a2a68802123dd5644c832c52a4b00822050e72d9543cc38521a84a8065c2d0d32540329a2e6302828850e7295143cc782ba264a8865465c06154f42e268698aa018e0d63988
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x400100200020000024000031730000000100000000301e0c00000030020800000000000000000000c00020000800800001030c0000b0182d0d315403192182dcd5444010c05645c4534c920b0183d095148020b01844c9515403290987d0d524c030c09645c0534cb21c05645c4534cb20905831d54248510c09735806054b439058754f4248421909831d542481109118754f424401091183dc95444010911871915344010c08655d1324c120c05645c4524c930b01829d15344010c04655d1324c521b0182d0d514c030b0183d092154021b018319152440109218719152440109098754f4248020b01844ca5154032c09725806054f42d01535cb4344010b01821915344010905821d5434c510d017354b4244010c05735846154b43c21615c06154b43c21715806054b43c11715806054f42c09645c0524c93190587d0d524c431c09645c0534c921909821d5434c11092187d0d5244010c11615c06154f42c05725846154f42b01839d15244010b01844c95194032
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 884
  | 4 => 1376
  | 3 => 377
  | 2 => 43
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
  | 6 => 2*((h/28+packedAt s5K6 (704+(h % 28)*6) 6) % 44)
  | 5 => 2*((h/301+packedAt s5K5 (23868+(h % 301)*10) 10) % 884)
  | 4 => 2*((h/514+packedAt s5K4 (52288+(h % 514)*11) 11) % 1376)
  | 3 => 2*((h/146+packedAt s5K3 (18473+(h % 146)*9) 9) % 377)
  | 2 => 2*((h/77+packedAt s5K2 (2580+(h % 77)*6) 6) % 43)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x77c3de7e7c7f1c63e3f311e3f1c71cf9c530cf
  | 1 => 0xbbfc1f9f9f8fe07c7c7c1e3c7e381f3e4ac333
  | 2 => 0x3cffe01fe00fff807f8fe03f803fe03fb30c3c
  | 3 => 0xc0ffffe0000fffff800fffc0003fffc03c0fc0
  | 4 => 0xfffffffff00000000fffffffc000003ff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x4202008100840400004090010408001045
  | 1 => 0x40404001201008080020420080810004112
  | 2 => 0xc1488148092448094015202904924025130428
  | 3 => 0x1e91080152489040092a5480092492802c0a80
  | 4 => 0xefe211515800da52524f99324d80c2853fa000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeeefee8feeefee8feeefee8feeefee8feeefee8feeefee8feeefee8feeefee8feeefee8feeefee8feeefee8feeefee8feeefee8feeefee8feeefee8feeefee8, s5N, s5R, (fun _ _ => 0), s5I, []⟩
end PEqualNP.Outside.L_meta_36386
namespace PEqualNP.Outside.L_meta_36386
open PEqualNP.Outside.L_meta_36386.Model
def q6K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q6K3 : Nat → Nat
  | 0 => 0x80008302e18df30bc6378cae985c32
  | _ => 0
def q6K2 : Nat → Nat
  | 0 => 0x3094414c25906328e428c6310930
  | _ => 0
def q6N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
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
  | 2 => 2*((h/8+packedAt q6K2 (104+(h % 8)*2) 2) % 4)
  | _ => 0
def q6Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffdff3ffff1ffff1ff
  | 2 => 0xffffffffffffffffffffffedfc7f3fe3f0fe73
  | 4 => 0x76ff8fcffc7f0f9c
  | 5 => 0x78fff00fff800fe0
  | _ => 0
def q6Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffa0180202049440a5
  | 2 => 0x122324452122a652
  | 4 => 0x9416819484a2b18
  | 5 => 0x78a4eae920ccde0
  | _ => 0
def q6Atlas : Atlas := ⟨4,rawDecor 54 q6Pos q6Neg, 0xfcfcc0c0ccccc0c0fcfcc0c0ccccc0c0fcfcc0c0ccccc0c0fcfcc0c0ccccc0c0fcfcc0c0ccccc0c0fcfcc0c0ccccc0c0fcfcc0c0ccccc0c0fcfcc0c0ccccc0c0, q6N, q6R, (fun _ _ => 0), q6I, []⟩
end PEqualNP.Outside.L_meta_36386
namespace PEqualNP.Outside.L_meta_36386
open PEqualNP.Outside.L_meta_36386.Model
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
  | 1 => 0xffffffffffffffffffffffffffffffffffbecf
  | 2 => 0xffffffffffffffffffffffffffffffffffdf73
  | 3 => 0xefbc
  | _ => 0
def q7Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffff4205
  | 2 => 0x2412
  | 3 => 0x1828
  | _ => 0
def q7Atlas : Atlas := ⟨3,rawDecor 14 q7Pos q7Neg, 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0, q7N, q7R, (fun _ _ => 0), q7I, []⟩
end PEqualNP.Outside.L_meta_36386
namespace PEqualNP.Outside.L_meta_36386
open PEqualNP.Outside.L_meta_36386.Model
def q8K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q8K3 : Nat → Nat
  | 0 => 0x108000002f98dd32ba637ccaf185c30
  | _ => 0
def q8K2 : Nat → Nat
  | 0 => 0x95410c25507328d420c2350b31
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
  | 2 => 2*((h/1+packedAt q8K2 (104+(h % 1)*2) 2) % 4)
  | _ => 0
def q8Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffdff7fcfc7ff8f3cf
  | 2 => 0xffffffffffffffffffffffedf99f3f8e3f3d33
  | 3 => 0x76fe1fcff03fce3c
  | 4 => 0x78ffe00fffc00fc0
  | _ => 0
def q8Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffa010010012080045
  | 2 => 0x1224284484922512
  | 3 => 0x941501921248a28
  | 4 => 0x7851aae4986af80
  | _ => 0
def q8Atlas : Atlas := ⟨4,rawDecor 30 q8Pos q8Neg, 0xfcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0, q8N, q8R, (fun _ _ => 0), q8I, []⟩
end PEqualNP.Outside.L_meta_36386
namespace PEqualNP.Outside.L_meta_36386
open PEqualNP.Outside.L_meta_36386.Model
def q9K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q9K3 : Nat → Nat
  | 0 => 0x4000025f329a65b4cb7195d32
  | _ => 0
def q9K2 : Nat → Nat
  | 0 => 0x2350e32
  | _ => 0
def q9N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
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
  | 3 => 2*((h/8+packedAt q9K3 (75+(h % 8)*3) 3) % 5)
  | 2 => 2*((h/1+packedAt q9K2 (26+(h % 1)*1) 1) % 1)
  | _ => 0
def q9Pos : Nat → Bits
  | 1 => 0xfffffffffffffffffffffffbfdcf3e3f3e74cf
  | 2 => 0xfffffffffffffffffffffffdfef3cfc7cf9b33
  | 3 => 0xebf03f3f80fec3c
  | 4 => 0xf3ffc03fff00fc0
  | _ => 0
def q9Neg : Nat → Bits
  | 1 => 0xfffffffffffffffffffffff404104009020045
  | 2 => 0x208041042040112
  | 3 => 0x150aa0690a94c28
  | 4 => 0xe082ab24a14e80
  | _ => 0
def q9Atlas : Atlas := ⟨4,rawDecor 30 q9Pos q9Neg, 0xfcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0, q9N, q9R, (fun _ _ => 0), q9I, []⟩
end PEqualNP.Outside.L_meta_36386
namespace PEqualNP.Outside.L_meta_36386
open PEqualNP.Outside.L_meta_36386.Model
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
end PEqualNP.Outside.L_meta_36386
namespace PEqualNP.Outside.L_meta_36386
open PEqualNP.Outside.L_meta_36386.Model
def q11K3 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def q11N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q11R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q11K3 (i*3) 3
  | _ => 0
def q11I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q11K3 (3+(h % 1)*1) 1) % 1)
  | _ => 0
def q11Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffbecf
  | 2 => 0xffffffffffffffffffffffffffffffffffdf73
  | 3 => 0xefbc
  | _ => 0
def q11Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffff4205
  | 2 => 0x2412
  | 3 => 0x1828
  | _ => 0
def q11Atlas : Atlas := ⟨3,rawDecor 13 q11Pos q11Neg, 0xfaa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0, q11N, q11R, (fun _ _ => 0), q11I, []⟩
end PEqualNP.Outside.L_meta_36386
namespace PEqualNP.Outside.L_meta_36386
open PEqualNP.Outside.L_meta_36386.Model
def q12K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q12K3 : Nat → Nat
  | 0 => 0x14202e98dd32b8617cc6f185f32
  | _ => 0
def q12K2 : Nat → Nat
  | 0 => 0x219541cca350b3195410c2350830
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
  | 0 => 0xffffffffffffffffffffffdff7fcfc7ff8f3cf
  | 2 => 0xffffffffffffffffffffffedf99f3f8e3f3d33
  | 3 => 0x76fe1fcff03fce3c
  | 4 => 0x78ffe00fffc00fc0
  | _ => 0
def q12Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa010010012080045
  | 2 => 0x1224284484922512
  | 3 => 0x941501921248a28
  | 4 => 0x7851aae4986af80
  | _ => 0
def q12Atlas : Atlas := ⟨4,rawDecor 29 q12Pos q12Neg, 0xfaaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0, q12N, q12R, (fun _ _ => 0), q12I, []⟩
end PEqualNP.Outside.L_meta_36386
namespace PEqualNP.Outside.L_meta_36386
open PEqualNP.Outside.L_meta_36386.Model
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
end PEqualNP.Outside.L_meta_36386
namespace PEqualNP.Outside.L_meta_36386
open PEqualNP.Outside.L_meta_36386.Model
def q14K3 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def q14N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q14R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q14K3 (i*3) 3
  | _ => 0
def q14I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q14K3 (3+(h % 1)*1) 1) % 1)
  | _ => 0
def q14Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffbecf
  | 1 => 0xffffffffffffffffffffffffffffffffffdf73
  | 4 => 0xefbc
  | _ => 0
def q14Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffff4205
  | 1 => 0x2412
  | 4 => 0x1828
  | _ => 0
def q14Atlas : Atlas := ⟨3,rawDecor 19 q14Pos q14Neg, 0xeeee8888eeee8888eeee8888eeee8888eeee8888eeee8888eeee8888eeee8888eeee8888eeee8888eeee8888eeee8888eeee8888eeee8888eeee8888eeee8888, q14N, q14R, (fun _ _ => 0), q14I, []⟩
end PEqualNP.Outside.L_meta_36386
namespace PEqualNP.Outside.L_meta_36386
open PEqualNP.Outside.L_meta_36386.Model
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
end PEqualNP.Outside.L_meta_36386
namespace PEqualNP.Outside.L_meta_36386
open PEqualNP.Outside.L_meta_36386.Model
def q16K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q16K3 : Nat → Nat
  | 0 => 0x118006d32dc6574caf994d32
  | _ => 0
def q16K2 : Nat → Nat
  | 0 => 0x2350e32
  | _ => 0
def q16N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
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
  | 3 => 2*((h/8+packedAt q16K3 (75+(h % 8)*3) 3) % 5)
  | 2 => 2*((h/1+packedAt q16K2 (26+(h % 1)*1) 1) % 1)
  | _ => 0
def q16Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffbfdcf3e3f3e74cf
  | 1 => 0xfffffffffffffffffffffffdfef3cfc7cf9b33
  | 3 => 0xebf03f3f80fec3c
  | 4 => 0xf3ffc03fff00fc0
  | _ => 0
def q16Neg : Nat → Bits
  | 0 => 0xfffffffffffffffffffffff404104009020045
  | 1 => 0x208041042040112
  | 3 => 0x150aa0690a94c28
  | 4 => 0xe082ab24a14e80
  | _ => 0
def q16Atlas : Atlas := ⟨4,rawDecor 27 q16Pos q16Neg, 0xeeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88, q16N, q16R, (fun _ _ => 0), q16I, []⟩
end PEqualNP.Outside.L_meta_36386
namespace PEqualNP.Outside.L_meta_36386
open PEqualNP.Outside.L_meta_36386.Model
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
end PEqualNP.Outside.L_meta_36386
namespace PEqualNP.Outside.L_meta_36386
open PEqualNP.Outside.L_meta_36386.Model
def q18K3 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def q18N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q18R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q18K3 (i*3) 3
  | _ => 0
def q18I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q18K3 (3+(h % 1)*1) 1) % 1)
  | _ => 0
def q18Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffbecf
  | 1 => 0xffffffffffffffffffffffffffffffffffdf73
  | 2 => 0xefbc
  | _ => 0
def q18Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffff4205
  | 1 => 0x2412
  | 2 => 0x1828
  | _ => 0
def q18Atlas : Atlas := ⟨3,rawDecor 7 q18Pos q18Neg, 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8, q18N, q18R, (fun _ _ => 0), q18I, []⟩
end PEqualNP.Outside.L_meta_36386
namespace PEqualNP.Outside.L_meta_36386
open PEqualNP.Outside.L_meta_36386.Model
def q19K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q19K3 : Nat → Nat
  | 0 => 0x8000005d32da65b8caf994d32
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
  | 3 => 2*((h/15+packedAt q19K3 (75+(h % 15)*3) 3) % 5)
  | 2 => 2*((h/1+packedAt q19K2 (26+(h % 1)*1) 1) % 1)
  | _ => 0
def q19Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffbfdcf3e3f3e74cf
  | 1 => 0xfffffffffffffffffffffffdfef3cfc7cf9b33
  | 2 => 0xebf03f3f80fec3c
  | 4 => 0xf3ffc03fff00fc0
  | _ => 0
def q19Neg : Nat → Bits
  | 0 => 0xfffffffffffffffffffffff404104009020045
  | 1 => 0x208041042040112
  | 2 => 0x150aa0690a94c28
  | 4 => 0xe082ab24a14e80
  | _ => 0
def q19Atlas : Atlas := ⟨4,rawDecor 23 q19Pos q19Neg, 0xeeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8eeeee8e8, q19N, q19R, (fun _ _ => 0), q19I, []⟩
end PEqualNP.Outside.L_meta_36386
namespace PEqualNP.Outside.L_meta_36386
open PEqualNP.Outside.L_meta_36386.Model
def q20K6 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q20K5 : Nat → Nat
  | 0 => 0x40032c802144001022fc41f843e907c32fe65fcc7f90fd21fa65f4c7e107c21fe61f8c7f887d30fc61f8cbe087c31fc43f443f907c30
  | _ => 0
def q20K4 : Nat → Nat
  | 0 => 0x1805000142a161e0441000020c81a0100994f84c028101010010182a030500138010002810020a0000600bd43882f50021df31cc3b8cb20bf414c2f50f20bc43886f10c21be42087e90032bf42442fd0d20bd42042f90221f930442790c21ed32c82f90730bf43082f90910b940087bcca32bd438c3d44010dd32cc6f90231bd41cc2f10d21be420c6f10520df314c2f90031bf404c6f90630bc43083bcc932b5410cbd90430be420cbdcc531de43086f90d10bd43082b50810f930843c44010fa20843b48020be430c3e88110dd43042f50c10f610442e90031bd40887e50021e9200837cc931cd320cbb88120be40cc7dc4210b541082f50e32bd400c7d90432bf414cb7cc030bc43843d48710ef20083d8c710bc404cbbc8421be408caf10f20be41ccaf50430b9400c6f10f21bf430437ccb30fb308c3dc4010ef208837cca32b9400caf90032ee42043b48720bf4344374c030ee32c877cc431bd400caf90021be43c82fd0f20be43082b90831be42843d4c521bc424c6f90631be40082f50830ed420c3948421f721486f10e20f621442e90032bf404cb7cc930b6410c2f90d21be41882750c20bd41c83d48421bc42c4364c030bf43086f10d10bd43c87b4cb21bc42042f50e10fa30882750c10bc424c2f90810bf42842f90720be42cc7d4c510bf404877cc631b641083ecc130ed320cb7ccb31bd410caf50910ba400877cc230ed2148374c730bd43482f50331f920442b90810f910042f50c21bd42cc6790c20bd42886f50a30de304c2fd0931bd43c42f10532bd418c374c931ad420c3d50420b6410cbec8120be428caf50420fa10042f90632be430c7d88710fa40087b48421bd428c7e48210ed420c6f50b10dd314c2f50a10be410c7790c10bf43486fd0e10bf42042b50831be408c2f90c10be43087d88421bd40ccbe88020be42cc3d4c710bd420c6f50610f5310c7e90031bf43c86f90430be4084378c932bd42882f10530bc43042f10131bf42c43dc8621bc42443ec4110bc4348374cb30bd408c7e4c220f6310c77cc832be42082f10f109d43086fd0930f531887b88521bc40486fd0520be43c87d50430bf43887bc8621ee420c374c930be40043d50432f9400c7ec4210dd43082f90e21dd310c6f90830fa30442f90c32be41082f50632fa3048378c531be428c2f50620f641082f90f10ee420c774c832bd41ccaf50e21bf43882f90e20f920083ec8220bd43486f90410ed32487b8c832ef21482fd0f109e43043750c21fa30842f10a10ed42043e8c030be43482f50d10f7318c6d50430de43082f90a31bd40c86f90421d5310c6f90621be400c2f90432be40c87d8c621be43843b8c921be40ccaf50b30bd408cbbc8720be42c43e50032ae420c3e4c030be40883b8c920bd438c7d8c521f631443d48510f930483b4c920
  | 1 => 0x6060380000228f8aa0b0002c2a070c00c0200000100c000d83c0025198d40c0b1a000022e00000120100028000100148080e0f25408003a8780001758b80600000004e00000002c2c009540800033380e0f07818100c4d034060016878
  | _ => 0
def q20K3 : Nat → Nat
  | 0 => 0x631d5310910cb21a82106550f100425ca4218411e5310b10962a26490e350f210869aa71906554514c931d490a8010e390d420435285080219b31500319d28086086c505300c31a8498863c532904329ca808610e650d2008276a0a1a43954348421b4292609066509300c32a87108438e43908109caa420084794c43086e0a098a21e141480209729087886310d32c866ca221843b14244010f0a1220085954a210863ea8980612d52d0c10d5aa240104d94443483488290a41365110e20c69928019624c9400cb9265200658c434c921e2a1a4210d554e310c7a286880211c53509109729082986c506400cac8a498a43a141480208f298861053d51320cb9264a006597544c431e4a1260186610d30483c48488021e121481109baa24210c754f420425aa420263365110930d9a1a20086a90a400c7288698c43a12150021972908610cdd51310c66aa221e411d5490c2096a90878861509310c766a8880211e53d081096a908708724c9304834a64a08659b3250032c6a1a4210cbd51200826ea888021b241500329d28082995a54a20083a282980618d4348020ca98a8018f490d100431a8598061a5428c4318fa9a84886c485400866aa2212619541cc030cc21a610863509300c23aa9218218c434c920d4a128018e950910043288698a433b544401097296860869109214423aa62102196439042097290868855d51310c7928690041365110c10caa1a20087190d210866ca22102164514c921d5a1a40104754c404872a64a08651d5310520d4a1220084e151304425aa421821355110c209b28e86104b552420432a82980612c544c920cc98a8018c794c42843328688021675448421b828242886a4c9400cae0a298221d1314c110e521a40104e940430826aa3a1841854348421b5aa240106a109208426ca221e41aa3250032cca0a60186550e410834a8498863a64290430b428264906c506200825ca421021345150d20d9a1220084d15131442b0a0992611e53101219aa8887106690d40087c48290041b2215002196a9082986c505200825ea8908432d5210d10d52128018e250d2008274a021e4394414c53097290860866d51300c270a890221685048520cc21a6088714c9314871284980618d3250432c62126498ec906400ca3ca621821a14244010d8a0a80194e940424c7308698441375150d20d590a8010ce54043487488490e219131500319daa260186450d100425ca421c211e5310910e299282196650e4008752852006394434c510d3212821865509310c76462a006334544c521d3a1a4210cbd51320cb8a849886391414c030d2a14821847d51310c7a482980618c424c930adaa260184e94343086e2a3080213950105329ca808498ce94042043a26320063a54348421c6a166218e98c9410ca74a021a43395010e21
  | 1 => 0xe0020c118141c0e04800021d0d13410170000406010481ca81201034142700804083d1181846010f0060a0601074ac00330004812150f96403110000c00000785200080ac520a008c400030186c2e03028040222159ac02463906400310280c002a01008005b8001c04431a9a8000119664c9400ca74a0218431f544c832caa1a82104b14943443348720043a541c8020f090c8010d6141314c35285180618c434cb209c2a260906a10920442b2a7180618532504329c2828690e510d31c4268a890a21c6424c4319aa8886906350d420434a42a0043e12150021d3aa24210e650d400874a84a0861994388020d8a1a20084b948404c63ca620a41a9424c030c7aa26419744c5400c74a8290041a943480209daa2401065cc9410ca72a021e438d43c80209aa8880994794c420426ca2202653a5010e218ea9885886350e42043628318061a542c4010cca1c20084d9444308272a1a1843ca424c030d4a0a40104754c428423aa921843735444010b828a40884bd49434436262a
  | _ => 0
def q20K2 : Nat → Nat
  | 0 => 0x9022c280040180000148021cb40894a040a10a383ad282c88698588514c110c81512148110e04c94190032a1588434c710a4191314c110a85924244010a2588434c110a81912148110a4584434c12092588504c530e090d2150021a1584434cb20e050d4244010a1584424c930a158c4248710a158c424851098580524c521e0509414c030c1151324c521a4580434c621e050e424401094580514c931a45924344010a2580434cb21a158c4148520a2588434c210e050d21500219458c5048510c4151314c110c2151324c120a25924348020e05093150031e050e4148020e050d414802094584504c930a2580424c931a4584434c220e090d4148020a2191324c120a15924348421e090d424401098584524c12098588504c510e04c94150032a258c424821098580514c921a858343484219258c5048520a85874348020a2580434c921e04ca4150032e09093150031a1191324c521e05093190031a4580434c521a1584434c920e0909414c030e050a414c030a858b4344010a258c4248110a1588414c5309458c5148110a458f4244010a1588434c51098584504c920e050d2190021
  | _ => 0
def q20N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 24
  | 4 => 302
  | 3 => 279
  | 2 => 66
  | _ => 0
def q20R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt q20K6 (i*4) 4
  | 5 => packedAt q20K5 (i*15) 15
  | 4 => packedAt q20K4 (i*26) 26
  | 3 => packedAt q20K3 (i*37) 37
  | 2 => packedAt q20K2 (i*48) 48
  | _ => 0
def q20I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt q20K6 (4+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/15+packedAt q20K5 (360+(h % 15)*5) 5) % 24)
  | 4 => 2*((h/121+packedAt q20K4 (7852+(h % 121)*9) 9) % 302)
  | 3 => 2*((h/100+packedAt q20K3 (10323+(h % 100)*9) 9) % 279)
  | 2 => 2*((h/29+packedAt q20K2 (3168+(h % 29)*7) 7) % 66)
  | _ => 0
def q20Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffdfd273c777b0cf
  | 1 => 0xffffffffffffffffffffffffefe39cf87bd333
  | 2 => 0x77fc1f3f83ec3c
  | 3 => 0x7bffe03ffc0fc0
  | _ => 0
def q20Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffa0448401108045
  | 1 => 0x10882108210112
  | 2 => 0x9014052020428
  | 3 => 0x6000aa4400a80
  | _ => 0
def q20Atlas : Atlas := ⟨6,rawDecor 15 q20Pos q20Neg, 0xfee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8, q20N, q20R, (fun _ _ => 0), q20I, []⟩
end PEqualNP.Outside.L_meta_36386
namespace PEqualNP.Outside.L_meta_36386
open PEqualNP.Outside.L_meta_36386.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x2001ff21007f48401fd20007f44001ff20
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x206000e4f00672a0f4f0001000400034649040a040314000f010201890341000106000004010707586b000f0600017d080301000004073007142f000a0c11100007057fc6090807fd434401ddea1e4204fe4c120007fac890002fd61c800dffa0a4002ff1091005fea6290803fd41480037fb1a2000bfd9120005fac88801bff4248003ff1922001ff58d10067fe8490812ff63480017fb22420aff1812100ff26088022fd63c800dff322400ddfd412105ffa6490802fd60c8403fa98a2000ffd8520007fcc488023bf43c801df69964200bfd9110017fe8488003fd424800fbe32a400eff4c321036f8a8900137d534800bfe20a400cff1912105ffa6090803f92044019be2a24202df1511005efaa69083ffe40c84017fb0a4005ff90520007fec488027fe31c8003bea9a200aff8812105fdc6490813ee324801dfea1e4200ff50910007da8590003fe42440017eb122005ff98520007fec090803ff644801fff1864200ff4852003ef8a490013fd3248011fe98e4000bf59321006fca490003fc6244009dfa1a4000df949210477a8790027fe41c8001bfb2a4205ff8c520006faca88013ff6348003fe992200bffd0d2106ef8ca90813bd4348007be2922000ff59110007f28088012fd6348001f6a12420bbf58d2100f7e8688003f54144001fea024200ff50321007da8490006fd6344001bf2922001ffd8d10007dc849003afd63c8409fe98a400bef50d21026fea690003ee4248401ffb224200bf5932002ffc4290017fc6148017bfa9a4201dfd4d10007fac290007bd4344001bea824206ff19120067fcc8908037f65480017eb224000fb48520007fec88802fff634840dbf2a24000df54520027fe8690002fd6448411fea1e4004fb4c92005dfec6908337e5448405fe3222000bfd891005fda6490803fd4248401feb024208fb4cb20007fac890807ff4344001f790a400aff981210777e8790802ff604840fbfa8a400cffd0121007fa839002bfe4048409fea1a4000ff58910016fca888003f52144009feb1a400aff1012106ef8a490803ed21c8001f6a16420bff50d2101efcca8802ffd6348417dfa1a4202ff99110
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xd73d812112eef20d8910006bd43d89100a7f2315011013ff010d91100576d504852017f793054520007ea4248110004ff7458321005ef7050921067ac6450921007ad4250720006bd435891002ef621d8520006bf7458910004fd73583210067d75d91201eef710591210067d53d85200067c75d81210173c54d91100c7b54348510006f930d852021ded73909210067d53d912118f6d53509200073d43d9520057e7204851013e7f50d911018fe930509201ffe531509210067d53591200067f75d81210067d64949100067f7559120006bd43d91201efad4150b21007e8624811010fea30909200067d53d812117f3d4354520006bf64909101ef6d515092118fad43509201ff6f5350921006bd43d852010efa10d9120006bd4358720006bd43d91210ef775350510057e87048520136ef21d89100576f5048520006ed64487200067d53d91100067d75d89100067e65d91101ef6f5150921004fd72d9110017b74350510007765248510007e12148110004fd73591100067d6294910005ef7448720006ef64c8520004fd76509100b77852501100076f7548520117753194910004fd73d91200067f62949100067d63d9520007b54250510007f12150110004fd735891002ff221481101f76c655092120fe710909211857f7354520004fd73593210aff131501100a7795150110054fd76989100877953481101de7d6354121006bd4359120017b8645011014fe9304852010ebf40d9120066bc40d91210372c545092012cfe7618910066bf43591211ecfd7650921067af435092110cff745912008f7a65481101bdef734872014f6d534852020ebf41d9121007f141481100153e7494910007af64509210a77b5150110006bd43d8121006be40d9121056fa10d81210e7f23050510107ea1050920106fa1059120106bd405932020fe63190921006ed3258321055f571989100067e52d8520006ed64c85200353e749492011d7d7394910006bd43d9110104fd765092017e7d6354520066be64d91210163c54d911022ded7350b210af7b5350110006bd6450321055ed71c8520016bc42d91100e77550505101df6d325412116eef63c85200067e75d9110037af415092007cff7158910087b9434811007df771589100067e52d81211df7531541211d5ed7350b201ee7d515912120cff74591210067d65591101173f4394910005f7744851002ef661d8520036bf4159120066bc6459121017bb4350110105ed74909200077531d9521006fb705891016faf43c85200077531595101ee7f51591210e7b540505100057d71d9520007b942501100067f64949100067d75d9110007f370485100d5f773485100067c54d8520004ff73d8520004fd7359320107af40509200076d4254121054ff7058910004fd74d812102feb21481101a7e93090920
  | 1 => 0x921006ed42d81210067c54d81210076f65485200073d4359510155ed7348520087e93248110057f23048510006ee32d812102f795148110004ff73d9121007e76248510006ef7258910016bc54d91101467f51d91100c6f56348510005f57448510005ed70909211676c5248520037af4350920006bf6450921136ed21d8910036bf4359120007e9424811012e7d50d89100073d43d952102f7b5148110004bf7458910057755048510016be64d911009f7a544811013ebd40d91100c6f763485100e7f2405051009f785448110066bf4059121227ad4350b21006bf43d812115f6e544852010e7d50d9120087ea324811014fe53148520004fe76501210067f53d91100877b534811002f6d5148520004fd73d8520006ed6290910007f37148110006ed4258321095fb7348110016bf43d911007efa30d8520004fd73d8910107ea30509200a7f24150110007e76148520056f8605812104dfb7058910007796550110004fe7690910006ed64485201eebd4159321006bf54d9110007e6424851015f6c544852010ebd40d912002f6f51485200057970949100067c7558910005fb70485200e67f5059110057f01058910057f07048510087bb434811007efa305832114f6f5348520016bf42591101076d505092007efa10583210077775485100067f64541210067d63d95210067f65581210047d769491014eef63485200057d70d9521006ed62189101676c75485201067d5059120107ad405092012e7f50d8910004ff73d8121007e4624851012ff010d89100067f75d85200567f50589100057d71949201de7f6354121125ee76c8520004ff73d89100577750485100567f6054121004ff7359120006bc7458910205ed7350921006ee42d85200e7f22050510006df735891014faf43485200067d5359110036bf42d9120007af6450920006f9305891010e7f50d91200057c765412102fe921481100067e65591100067d53d9120004fd71d912007e7f50d8520006bf74591100057d73d952113e7d50d9110004fd7358720017b464505100067d53589100cf766548510086f963481101076f50509200c7755348510005ed74c8520006bf74591201b7ad4348720005ed7448520007eb6248110127f0101891010ff01090910005df73581211efe631509210567f50d8121057ea30485200067c75591210c7f13048510006ee42d81210067f65d9121056fa60d81210077930d9520086fb63481100067d53d8910006f930d89100067e6558910007b14150110005bf7458121004ff7259110005f772505101067f50591200067f65d81210067c65d91210067f50d91210067e65d89100067f63d95210f7745250510037af4390920006bd43591100067e75d9121004ff7159120066bf42d9121004fd70d91210e4fd74d9110005757194910004f
  | 2 => 0x7eb70485200067d63595100057c7259510155ef7348520004ff7458720004fd73d91210067c65d8520015bc74589101976c65509201b6ed634872002ef461585200067f63595100a7f22150110117793094910036bf43d912002e7f5158910004fd73591201ffad4350921006f930583210af795350110136f631d89100067c52591100067d75d91210cf745248510004fd7359121005df73589100afb943501100067f655852016fe930c85200d5f573485100076d4254520007bb64501100067f505912119ded73509200077652505100b77a65501100067c6359510017f14150110016bc6459110004fd7650720006bf745912108f7875481100057d70949210a67d515911004e7d51d81211467d51d91101c6ef7648720006ed325891012efa30d8910006be41d91200a67f51591100653e74949210067c63d9521007ad42503210067c5258910006f53158910006ef62989100067f65d8520175ed73c8520005df73585200c7e53248510004fd74d852007e7d50d85200bdf973501100e7f010591100076d32d95201b7af434872002e7d5158910016bf43591100067d5359121004fe76505201173d43949100067c52d89100e7b7405051004ef631d81210df7654485100067e54589100067f6454520067af40509210067f53591100df7454485100c7775348510006f53158720006ed62509101367d51d89101367f51d8910006ed3258720007e54248510005bf74589101eded7490921056fa20d8121006bd64507200c7e632485100076f6550920006f77158910006bd43593210067f65591200067e54d891007ff010989101e57f73541210067f51d9120006bd64509100fdf773505100067c6558121005bf7458520006f761485201676c654852007fea10c8520006bd4358321006ed32d85200067c52d8520006ed32d81210067f53589100067f7558910057e71048520006bf435872018f6f53509200057c7654520036bc41d912020e7d51d9121006bf43589100077a525011002e7f6154520006bd43591210567d50589100153c7459510005ed7448720004fd76909101df3d43541210c7b743485100067f53d89100067d645452016eed63c85200073f43d95200067e54d8520004ff735912102ff071481100067f7559110006bf43d89101976f5150920066bf43d91210a7bb415011020e7f51d9121007756550510006f531d81210067c65d8121087f131481100057d7694910004df73589100067f53591200067f51591200173c5450910005f97090910006bf6450920005ed71909200067c52d911008f78524811017f3f4354520006ef64485200e67d5059110056fa305891002fe46148520005bd741891004e7f51d81210067f53d91210bdfb73501100067e63d95200067e54d81210067f53d8520007f12148110217ad439
  | 3 => 0xc000201a3800b00000000190140f474d7000000000a0040000000014323340c03c7e358050000100401098000080300003002161a80037000020da000e10600b0040f02867000280000704c0100c03014000000002001004b702008000b801c850508f0688c0b4321e4132090000d9301c0323dd504800008030000202c00000000040000000000254640f0000402001010660140002800028000001f1100200c0000009004030002103c0001c06084020001000808000b300000000050780a068000749e0340c064981167f639491014fad43485200067d6558910217e531909210067e63595100077a5248110007ad4250121006bf43583210067c65591210077565485100067d65d891013cff74591100067c63d9520146bf41d91100067f5359121006dc73589100fdf573505100057f735951019def73509200672c54509211efad4150921004ff73d9110095f97348110015be741891002df9709891007fea30c8520005dd7318910057ea10485201167d63949100076d32d95210067c75d8520006bd64501211df3f435412113ebf40d91100e7775050510017b742505101cfad4350b2004ef631587200057d73d95200067f65d9120004ff73d9120057e7104872020ebd41d91210067f53d9120004ff7458910004fd74d8910004ff7358321205ef73509210076e5248520004fd76503210067c6559120007ad42505200067c75591201a7ad4390920006bd64505200076f655092114eed63485201aded7390920006bf43d8520006ed42d852007ef710d85200067e75d9120036be64d912017e7f635452016fad43c8520067af43909210067c52d8121057e52048510057f24048510107ad4050b200ef7553505101f76f505092110fea109092004fe6314872002fe631485200eff13050510146bd41d911012eed20d8910004ff73587200067c65585200067c54d89100067e63d95210073f43595100067e75d89100077930595100067d65d9110007b76450510004fd73d91100f7766550510006f531d891002e7f51d8520006bd43593200067d6454121004ff70591210067c54589100073f43d9521006ee32589101bded7348720004fe7650910006ee32d85200067f7559121107f010509100cf747548510037ac6450920057f220485100067c65d9120005fb72501101ff6d5350921036bc64591200a7b941501100077b75481100067c755911017f6d32545200067f63d9520005fb7448110005ef7150920006ed425872002ff24148110035bc7458520004ff7358910004ff7359110005ef74485200077965481100efb543505100067f53d81211efaf4150921005f97448110056f7105872002ef631589101b7e5314872002ff231481101efe7105092120ef710d9121017bb4250110065bc74581210067f6559121005f57190910
  | 4 => 0xc8000040b031442500100400000b000c9a014000000000400000030a4000000f081071708e00413070df024491f01a20801024001e80b260000003904807080080e400000010802102c000f81f01028000cd028000000100c06004330a070008250b4c3220160002300407000c801000000010102e7a4002080b00003000041700a40a0800c003cd19364030607d000001fc022e403000000000001c0004c0400800000000244300803000210153a0140100021000020041c000130142b0
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xec9324c160c845765d0929242900038718d43d95210061f3a2c52922000e1f6350f65480014790aa1ec8880031dd8d71949100064fba6e6b1220008be8750d6244001ae262b84a488127d89512148110237d0a1a429022000e58634c165440017630890a80880021fa1f65591200076299263b024200f19434c165440010fd0fb2ac8908029e60252d81210074ca1a61b122000c5f7358d6544001d9264986c2900030f54374589100062fa8ee6b122000e1d5350d64c84014eb02292c888003171cf65585200046fc1ae5b222000e8e3250d61c80010fd0fa9ac8900021f61f53d891000656ba2c43122000c5f65dcd6148099e66a6a0a8088002da2096548110005e4c18c4902200087e8795162440018b8cbb9ac090803d24c930d95200064fc26e6b122000f45324c765484010fb0fa9ec89011bd8d4d21481100064fb9a86b224000e8d438c962440016e30129242880029ba0a54d81210069aa1ae32922000db1745052044001878cbba2c090803475cd4359510007d0a12829022000c5f85dcd62440014f300296c0908029ba0854d85200043ec1aed2922000a798014964440a5a76e0a1aca88003171cd6558910006d8082e83122000a3d8418d654400187ecbba2c2900030f9d76490910007a898a60b2a2000c3c7458d6544001e64a4a0a8088003d894921481100043f43ea6b224200be18090921440016e303292808812bd81d521481100061e3a8e8b122000c9f7350d64484018baa1b9ac48806fc915142485100070ea9a87b224200a3e8494b6048495ec4ca90a40880021fa1c6359510007162a285b024200ccd7358862440010fd0fa9ec09092fcc99541501100053ac0eebb0a4000f0e3250f65484010fb0fa9ec89080317dd473589100dd9b424a490a2000ed1314c36244001c3ec6a1eca908021fa1c52591100072c31a61b2a4000c3f51dd162440014d904b2ac488002e961062485100047bc0ae6b22400087f835da52440014db0431aca8800356dcd305951027e9c3a260b2a2000c5c54dcd62440016c904b2a42880038754d43d89100043f438a9b024200c5d51dcd62440014eb02296c88813aece0d415011000746a1c65b024200e54634c565440018b8e7b2ac0908023be0973591100052ec18a9b122000e8e3250d60c8401c3aa6a1ac9900030fdd0545891009d9c422ca9022000e4c634cb6548401ca8c698eca908029d60452d85200047dc02e6b224200c3d51dd162440018bae7b1eca900029e60054d85200053cc00a5b222000a3c84597624409bb62e6a0a80880030f1d363595100051ec20c7b2a4247de173485204400193ee6a1ec09080317d4373589100064fb9a87b0a4000f15434c56544001d3286982c4880038754d43587200051ec24c7b2a424af60854852044001878ebba2c8880038754d4359121
  | 1 => 0xd0f2a6c0908029b20953d89100074aa1a62b122000e8d438cb614800187ee8292c4881434d1d13159510006d9206e890a2000975835c652440014f3003aec090803d8dd521481100062fb9aa6b122000c9d7350f62440018becbb9ac0908021f61f62949100053ac08a9b1220008bf845cd6244001c3cc6a1aca88127d815121481100061e3a4cab12200093c8750d654400187ecbba2c0908021f61f6494910005f0c0c849022000c3c741956148001a3ee6a1eca900031e58d70949100061fba2a6b122000e95434c561c8001c58a8b12848800327dcd43591100061e2a2e7b222000a758194b614800187e86bb4a4880030f617745891000798b2a82a02200087f87597644409bb66e6a0a808811bb858d21481100074ca1a60b064200a798015362440018bae7b1eca908029760c54d81210062f2a6e6b12200087e879536148001d9264982c4880038754d43591100043fc3ac92922000bb38250540440018f260bb4a4880034ed0d70949100064fb9a86b12200087d8798f6548401878a93b2848806ecd2116548510006f1ba2429022000be1844852044001ba021b9ac4880030fdd254589100064eb9a87b222000f15434c765484014dd0532ac4880021f61e54d89100053ac08a9b024200a5d831536148001c3aa6a1ac1908029e60054589100053cc00c7b2a4200f616548520440014eb022a2c488153cc04343595100064e3a6e6b122000e4c634cb6548001b6021ba2c4880022f60f74589100061e3a0cab024200c75635c652440010fb0f31eca90003c650d30d952025f9829282a022000a3f8458a52440018bee7a9ac48804fca1514248110237d1a1a429022000c3c54dcf64440018f6c6b84a48800327dcd43587200069ba1ae3292200087e87151624400117f08bb28488133cc54d4150110005b8c04a4a0a2000c5c65dcd614800147b0831eca900031d4c576949100064eb9a87b224200c3e65dd1624402767509292408800317dce6359510257b0292429022000e1d5350f644800187ee9a9ac48800327dd073589100074ca1a61b0a4000c5e65dcd62440014bf06b14a4880029ba0854d81210053ac08c7b2a40008de871cd624400187ce9b14a4880028f61263d95200074aa1a63b024200ba98418920440010fd0fa9ec2900030f19774585200061ea1aed2922000d71305c6524408dec2a690a4088122f860d2148110007b1c2a429022046ee36348520440018bae631eca9011f78dcd21481100076299262b0e4000ec5324c562440aba76e1a1aca880038754d43d9110005b8c0ca49022000d39435c252440014eb023aec2900022fa1f43589100053cc06ebb02420087d8715362440a3e6020a1aca880029ba0a54589100070eb1a86b2a200087f8758a5244001b6483ba240880038754d43d85200043f43ea6b122000
  | 2 => 0x1d8004b18028040432000002c050903804060003400080e00000000f0d00206000840c131f12844060980c0802000585a060c008000608800321b0888ca43c0f9e004000002400010403cb21101000a6010a044062b00050001300000045800014003a000c4004c020180400179403a0f0601c140a02800020a03034a2020900006000708006001d00426000009c001400818481e0081806230607002000081014030046fc1aeca122000d1f7350f6548401c38c6a1eca90003275cd43d9120007d0a1242a022000c3f50dd16244001b66e4a0a8088003a550d31d89100076898a60b122000e1d5350f60484010fb0fa9ec888003175977358910006e8082e63122000979835c25244001c3aa6a1ac488003c38c943d95200061e3aee8b122053d377150d65440014bb062a2c4880030f59774589100051e422cab122000c5c75dcd62440014dd042a2c4880023be1d6218910005e2c18c490a2000c5f75dcd6244001bc2e890a408800327dcf4358910275d8c1a82a022000be384485204400187d0bba2c4880030fdd77458910007162a285b0a4000a3d8498d65440ada6ee3a1aca880029ba0a54d85200043ec38a5b222000c9f7350d60c84010fd0e2a6c290122f8e0d2148110006abb9a62b2a2000c5c85dcd624400193909b9ac4880030f15172d91100062fb98a4b122000c5d7318f6548401c3aa6a1ac8900028fa1252d85200051e422ebb12200087e87d4d64440010f
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x20081800a0c00000062c0103a4408d86101800400100001c708181430002440b743180000058364c5450b614800141d9315172d91100048764c8459562440016199018d43d95210070550d315da524400105e9815373589100058a6405450b6148001625911516250910005432497350d6544001a148650d31d952100591644634cb654800141d931d363595100064c0408750d654400181f8350d76949100048764c845d7624400103e989d1629491000607a1d5350d624400103e97211655891000474660105cc624400141d9315173d911000546e417350d654400160d9315162509100050ba48545cb6444001c196350d70949100048764e8494b6148001d11434c171949100048764c845976244001629901516250910005896445450b604840141c9459773589100054625d434c165440016499018d32d952100474a6010dcd624400160d9315142d81210050764e85dd16244001c156350d7194910005856446350f65480016459218d3159510006155cd8118f65480015919404373589100060721d6350d6544001951834c17194910006079d38358a5244001951834c5709491000646e0d435c2524400141d939d162949100050764c54dcf6444001c19434c1769491029744dc1434c565440afd10744c5305951000564650105cc62440015c1920437358910006165cd8018f654840141d9315276509100054525d434c56544001c51314c176949100050764c7458d6544001d10105cd43595100040fe6165dd162440011b198041741891000645e0d435c65244001d11434c570949100050764e74d8a52440016499218d305951000607153835cb644400181f7460c54589100048764e8494b604840160c9254d43d891000594644634c365480015a192041741891029f44dc5434c1654409372094595214811024dc8a5252485204400181f85e1373589100046ca6010dd162440015c19204173189100056464c105d062440016519018d31d95210056464c10dd16244001517915cd435951000686219434c365480015a1920437458910
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x400044400001000000100ed1f30b2ee8b122000d40248105cd435951000522350082e6a1aca88002921a20408750d654400100f54128b2ee6b12200084c6a41021d4359510004a2552082e6a1aca8800201ea99d38358a5244001488d182043a86b2a2000b40688105cd4359510
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x4501ba248105cd4359510006101a8248105cd4359510
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x94c
  | 2 => 0x94d
  | 3 => 0x94e
  | 4 => 0x98c
  | 5 => 0x98a
  | 6 => 0x98d
  | 7 => 0x98e
  | 8 => 0x150c
  | 9 => 0x150a
  | 10 => 0xb09
  | 11 => 0xb0c
  | 12 => 0xb0d
  | 13 => 0xb0e
  | 14 => 0x154c
  | 15 => 0x1549
  | 16 => 0x98954
  | 17 => 0x98956
  | 18 => 0x94994
  | 19 => 0x98955
  | 20 => 0xa0a
  | 21 => 0xa0954
  | 22 => 0xa0956
  | 23 => 0x94a14
  | 24 => 0xb0954
  | 25 => 0xb0956
  | 26 => 0x94b14
  | 27 => 0xb0955
  | 28 => 0xb89
  | 29 => 0xb8954
  | 30 => 0xb8956
  | 31 => 0x94b94
  | 32 => 0xd09
  | 33 => 0x1609
  | 34 => 0x164954
  | 35 => 0x95654
  | 36 => 0x209
  | 37 => 0x1409
  | 38 => 0x128a
  | 39 => 0x1489
  | 40 => 0x130a
  | 41 => 0xb0994
  | 42 => 0x98b14
  | 43 => 0xb0995
  | 44 => 0xb0996
  | 45 => 0x154994
  | 46 => 0x99554
  | 47 => 0xbc994
  | 48 => 0x98bd4
  | 49 => 0xd0994
  | 50 => 0xd0996
  | 51 => 0x98d14
  | 52 => 0x160994
  | 53 => 0x99614
  | 54 => 0xb1514
  | 55 => 0x150b14
  | 56 => 0x8a
  | 57 => 0xd1514
  | 58 => 0x150d14
  | 59 => 0xa4b14
  | 60 => 0xb0a54
  | 61 => 0xd0a
  | 62 => 0xd0b16
  | 63 => 0xd0b14
  | 64 => 0xb0d14
  | 65 => 0x160a
  | 66 => 0x160b14
  | 67 => 0xb1614
  | 68 => 0xd1554
  | 69 => 0x154d14
  | 70 => 0xb09895c
  | 71 => 0xb09499c
  | 72 => 0x9894b1c
  | 73 => 0xb09895d
  | 74 => 0xb09895e
  | 75 => 0xb8a095e
  | 76 => 0xb8a095c
  | 77 => 0xb894a1c
  | 78 => 0xa094b9c
  | 79 => 0x9c955
  | 80 => 0xb4955
  | 81 => 0xe8bd1
  | 82 => 0xe9992
  | 83 => 0xe99d1
  | 84 => 0x18cbd1
  | 85 => 0x18d992
  | 86 => 0x18d9d1
  | 87 => 0xb49c95d
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 5
  | 7 => 156
  | 6 => 649
  | 5 => 328
  | 4 => 82
  | 3 => 10
  | 2 => 2
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
  | 2 => packedAt gbK2 (i*92) 83
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
  | 2 => gbHint (packedAt gbK2 (i*92+83) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 9 => 2*((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 1)
  | 8 => 2*((h/8+packedAt gbK8 (130+(h % 8)*3) 3) % 5)
  | 7 => 2*((h/66+packedAt gbK7 (5772+(h % 66)*8) 8) % 156)
  | 6 => 2*((h/314+packedAt gbK6 (31152+(h % 314)*10) 10) % 649)
  | 5 => 2*((h/144+packedAt gbK5 (19352+(h % 144)*9) 9) % 328)
  | 4 => 2*((h/41+packedAt gbK4 (5740+(h % 41)*7) 7) % 82)
  | 3 => 2*((h/17+packedAt gbK3 (810+(h % 17)*4) 4) % 10)
  | 2 => 2*((h/7+packedAt gbK2 (184+(h % 7)*1) 1) % 2)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xc70e1fc7e610f8fc1f1c1c3f87f20c33c530cf
  | 1 => 0x380fe1f8f81f0f1fe0e01fc3f87430cccac333
  | 2 => 0x3ff001ff1fe00fe000ffe003ff89c30f330c3c
  | 3 => 0x3ffffe001ffff00000fffffc000e03f03c0fc0
  | 4 => 0xc00000001fffffffff000000000ffc003ff000
  | 5 => 0xffffffffe000000000000000000fffffc00000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x41020241200010240804041082200411401045
  | 1 => 0x8042088400101090020090120401044804112
  | 2 => 0x121001120a200a40424940025500c10a130428
  | 3 => 0x24a95400155aa000849292a8000e02a02c0a80
  | 4 => 0x808110001f9ccc92d600c088110f68003fa000
  | 5 => 0x3fcf99e48108800318030330666fbfffc00000
  | _ => 0
def gbRaw : List Sig := (rawDecor 63 gbPos gbNeg).map Prod.fst
def gbPools : List BoundPool := [(0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555, 7, 0, gbRaw),(0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333, 7, 0, gbRaw),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 5, 0, gbRaw),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 8, 0, gbRaw),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff, 7, 0, gbRaw),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff, 8, 0, gbRaw),(0x550055005500550055005500550055005500550055005500550055005500550055005500550055005500550055005500550055005500550055005500550055, 5, 0, gbRaw),(0x5555000055550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555, 4, 0, gbRaw),(0x555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555, 5, 0, gbRaw),(0x55555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000, 5, 0, gbRaw),(0x330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033, 5, 0, gbRaw),(0x3333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333, 4, 0, gbRaw),(0x333333330000000033333333000000003333333300000000333333330000000033333333000000003333333300000000333333330000000033333333, 5, 0, gbRaw),(0x33333333000000003333333300000000333333330000000033333333000000003333333300000000333333330000000033333333000000003333333300000000, 5, 0, gbRaw),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f, 4, 0, gbRaw),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f, 4, 0, gbRaw),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f, 5, 0, gbRaw),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000, 5, 0, gbRaw),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff, 4, 0, gbRaw),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff, 5, 0, gbRaw),(0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff00000000, 7, 0, gbRaw)]
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfefefee8feeefee8fefefee8feeefee8fefefee8feeefee8fefefee8feeefee8fefefee8feeefee8fefefee8feeefee8fefefee8feeefee8fefefee8feeefee8, gbN, gbR, gbH, gbI, gbPools⟩
end PEqualNP.Outside.L_meta_36386
namespace PEqualNP.Outside.L_meta_36386
open PEqualNP.Outside.L_meta_36386.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 10 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 60 := block_range (n:=60) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 60 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_96 : Interval s0Atlas 4 96 69 := block_range (n:=69) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 165 := (concat bs0_4_0 bs0_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 50 := block_range (n:=50) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 50 := bs0_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 1 := bs0_6_0
theorem alls0 : ∀ k ≤ 6, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
  · exact alls0_6 i (by omega) hi
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
theorem bs2_2_0 : Interval s2Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 1 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 5 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 1 := bs2_4_0
theorem alls2 : ∀ k ≤ 4, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_2 i (by omega) hi
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 65 := block_range (n:=65) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 65 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_96 : Interval s3Atlas 3 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_192 : Interval s3Atlas 3 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_288 : Interval s3Atlas 3 288 55 := block_range (n:=55) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 343 := (concat (concat bs3_3_0 bs3_3_96) (concat bs3_3_192 bs3_3_288))
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
theorem bs3_4_1344 : Interval s3Atlas 4 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1440 : Interval s3Atlas 4 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1536 : Interval s3Atlas 4 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1632 : Interval s3Atlas 4 1632 39 := block_range (n:=39) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 1671 := (concat (concat (concat (concat bs3_4_0 bs3_4_96) (concat bs3_4_192 bs3_4_288)) (concat (concat bs3_4_384 bs3_4_480) (concat bs3_4_576 (concat bs3_4_672 bs3_4_768)))) (concat (concat (concat bs3_4_864 bs3_4_960) (concat bs3_4_1056 bs3_4_1152)) (concat (concat bs3_4_1248 bs3_4_1344) (concat bs3_4_1440 (concat bs3_4_1536 bs3_4_1632)))))
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
theorem bs3_5_960 : Interval s3Atlas 5 960 84 := block_range (n:=84) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 1044 := (concat (concat (concat bs3_5_0 bs3_5_96) (concat bs3_5_192 (concat bs3_5_288 bs3_5_384))) (concat (concat bs3_5_480 (concat bs3_5_576 bs3_5_672)) (concat bs3_5_768 (concat bs3_5_864 bs3_5_960))))
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
theorem bs4_2_0 : Interval s4Atlas 2 0 66 := block_range (n:=66) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 66 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_96 : Interval s4Atlas 3 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_192 : Interval s4Atlas 3 192 87 := block_range (n:=87) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 279 := (concat bs4_3_0 (concat bs4_3_96 bs4_3_192))
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
theorem bs4_4_288 : Interval s4Atlas 4 288 14 := block_range (n:=14) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 302 := (concat (concat bs4_4_0 bs4_4_96) (concat bs4_4_192 bs4_4_288))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 24 := bs4_5_0
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
theorem bs5_2_0 : Interval s5Atlas 2 0 43 := block_range (n:=43) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 43 := bs5_2_0
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
theorem bs5_3_288 : Interval s5Atlas 3 288 89 := block_range (n:=89) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 377 := (concat (concat bs5_3_0 bs5_3_96) (concat bs5_3_192 bs5_3_288))
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
theorem bs5_4_1344 : Interval s5Atlas 4 1344 32 := block_range (n:=32) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 1376 := (concat (concat (concat bs5_4_0 (concat bs5_4_96 bs5_4_192)) (concat (concat bs5_4_288 bs5_4_384) (concat bs5_4_480 bs5_4_576))) (concat (concat (concat bs5_4_672 bs5_4_768) (concat bs5_4_864 bs5_4_960)) (concat (concat bs5_4_1056 bs5_4_1152) (concat bs5_4_1248 bs5_4_1344))))
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
theorem bs5_5_864 : Interval s5Atlas 5 864 20 := block_range (n:=20) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 884 := (concat (concat (concat bs5_5_0 bs5_5_96) (concat bs5_5_192 (concat bs5_5_288 bs5_5_384))) (concat (concat bs5_5_480 bs5_5_576) (concat bs5_5_672 (concat bs5_5_768 bs5_5_864))))
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
theorem bq6_2_0 : Interval q6Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq6_2 : Interval q6Atlas 2 0 4 := bq6_2_0
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
theorem bq9_2_0 : Interval q9Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq9_2 : Interval q9Atlas 2 0 1 := bq9_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq9_3_0 : Interval q9Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allq9_3 : Interval q9Atlas 3 0 5 := bq9_3_0
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
theorem bq11_3_0 : Interval q11Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq11_3 : Interval q11Atlas 3 0 1 := bq11_3_0
theorem allq11 : ∀ k ≤ 3, ∀ i < count q11Atlas k, checkRow q11Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq11_3 i (by omega) hi
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
theorem bq14_3_0 : Interval q14Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq14_3 : Interval q14Atlas 3 0 1 := bq14_3_0
theorem allq14 : ∀ k ≤ 3, ∀ i < count q14Atlas k, checkRow q14Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq14_3 i (by omega) hi
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
theorem bq16_2_0 : Interval q16Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq16_2 : Interval q16Atlas 2 0 1 := bq16_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq16_3_0 : Interval q16Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allq16_3 : Interval q16Atlas 3 0 5 := bq16_3_0
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
theorem bq20_2_0 : Interval q20Atlas 2 0 66 := block_range (n:=66) (by decide +kernel)
theorem allq20_2 : Interval q20Atlas 2 0 66 := bq20_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq20_3_0 : Interval q20Atlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq20_3_96 : Interval q20Atlas 3 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq20_3_192 : Interval q20Atlas 3 192 87 := block_range (n:=87) (by decide +kernel)
theorem allq20_3 : Interval q20Atlas 3 0 279 := (concat bq20_3_0 (concat bq20_3_96 bq20_3_192))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq20_4_0 : Interval q20Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq20_4_96 : Interval q20Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq20_4_192 : Interval q20Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq20_4_288 : Interval q20Atlas 4 288 14 := block_range (n:=14) (by decide +kernel)
theorem allq20_4 : Interval q20Atlas 4 0 302 := (concat (concat bq20_4_0 bq20_4_96) (concat bq20_4_192 bq20_4_288))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq20_5_0 : Interval q20Atlas 5 0 24 := block_range (n:=24) (by decide +kernel)
theorem allq20_5 : Interval q20Atlas 5 0 24 := bq20_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq20_6_0 : Interval q20Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq20_6 : Interval q20Atlas 6 0 1 := bq20_6_0
theorem allq20 : ∀ k ≤ 6, ∀ i < count q20Atlas k, checkRow q20Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq20_2 i (by omega) hi
  · exact allq20_3 i (by omega) hi
  · exact allq20_4 i (by omega) hi
  · exact allq20_5 i (by omega) hi
  · exact allq20_6 i (by omega) hi
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
theorem bgb_4_0 : Interval gbAtlas 4 0 82 := block_range (n:=82) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 82 := bgb_4_0
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
theorem bgb_5_288 : Interval gbAtlas 5 288 40 := block_range (n:=40) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 328 := (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 bgb_5_288))
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
theorem bgb_6_576 : Interval gbAtlas 6 576 73 := block_range (n:=73) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 649 := (concat (concat bgb_6_0 (concat bgb_6_96 bgb_6_192)) (concat (concat bgb_6_288 bgb_6_384) (concat bgb_6_480 bgb_6_576)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_96 : Interval gbAtlas 7 96 60 := block_range (n:=60) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 156 := (concat bgb_7_0 bgb_7_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 5 := bgb_8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_9_0 : Interval gbAtlas 9 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_9 : Interval gbAtlas 9 0 1 := bgb_9_0
theorem allgb : ∀ k ≤ 9, ∀ i < count gbAtlas k, checkRow gbAtlas k i = true := by
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 7 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 20, 52)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 20, 52)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 20, 52)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
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
theorem boundq6 (cert : Complete q6Atlas) : Lower true (roots q6Atlas) (target q6Atlas) 5 := by
  have ready : Ready q6Atlas (asRow q6Pos) (asRow q6Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 20, 52)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq7 (cert : Complete q7Atlas) : Lower true (roots q7Atlas) (target q7Atlas) 4 := by
  have ready : Ready q7Atlas (asRow q7Pos) (asRow q7Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq8 (cert : Complete q8Atlas) : Lower true (roots q8Atlas) (target q8Atlas) 5 := by
  have ready : Ready q8Atlas (asRow q8Pos) (asRow q8Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq9 (cert : Complete q9Atlas) : Lower true (roots q9Atlas) (target q9Atlas) 5 := by
  have ready : Ready q9Atlas (asRow q9Pos) (asRow q9Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq10 (cert : Complete q10Atlas) : Lower true (roots q10Atlas) (target q10Atlas) 5 := by
  have ready : Ready q10Atlas (asRow q10Pos) (asRow q10Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 20, 52)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq11 (cert : Complete q11Atlas) : Lower true (roots q11Atlas) (target q11Atlas) 4 := by
  have ready : Ready q11Atlas (asRow q11Pos) (asRow q11Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq12 (cert : Complete q12Atlas) : Lower true (roots q12Atlas) (target q12Atlas) 5 := by
  have ready : Ready q12Atlas (asRow q12Pos) (asRow q12Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq13 (cert : Complete q13Atlas) : Lower true (roots q13Atlas) (target q13Atlas) 5 := by
  have ready : Ready q13Atlas (asRow q13Pos) (asRow q13Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq14 (cert : Complete q14Atlas) : Lower true (roots q14Atlas) (target q14Atlas) 4 := by
  have ready : Ready q14Atlas (asRow q14Pos) (asRow q14Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq19 (cert : Complete q19Atlas) : Lower true (roots q19Atlas) (target q19Atlas) 5 := by
  have ready : Ready q19Atlas (asRow q19Pos) (asRow q19Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq20 (cert : Complete q20Atlas) : Lower true (roots q20Atlas) (target q20Atlas) 7 := by
  have ready : Ready q20Atlas (asRow q20Pos) (asRow q20Neg) := by
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 20, 52)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfefefee8feeefee8fefefee8feeefee8fefefee8feeefee8fefefee8feeefee8fefefee8feeefee8fefefee8feeefee8fefefee8feeefee8fefefee8feeefee8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certq6 : Complete q6Atlas) (certq7 : Complete q7Atlas) (certq8 : Complete q8Atlas) (certq9 : Complete q9Atlas) (certq10 : Complete q10Atlas) (certq11 : Complete q11Atlas) (certq12 : Complete q12Atlas) (certq13 : Complete q13Atlas) (certq14 : Complete q14Atlas) (certq15 : Complete q15Atlas) (certq16 : Complete q16Atlas) (certq17 : Complete q17Atlas) (certq18 : Complete q18Atlas) (certq19 : Complete q19Atlas) (certq20 : Complete q20Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) (SBf 2) :=
    slice_correct (ms:=fixRows 36 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have s3 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 3 zero)) (SBf 3) :=
    slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
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
  have q0 : Slice true (roots gbAtlas) (target gbAtlas) (0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555 : Sig) 7 :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have q1 : Slice true (roots gbAtlas) (target gbAtlas) (0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333 : Sig) 7 :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have q2 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f : Sig) 5 :=
    slice_correct (ms:=fixRows 36 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have q3 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff : Sig) 8 :=
    slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
  have q4 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff : Sig) 7 :=
    slice_correct (ms:=fixRows 48 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds4 certs4)
  have q5 : Slice true (roots gbAtlas) (target gbAtlas) (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff : Sig) 8 :=
    slice_correct (ms:=fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds5 certs5)
  have q6 : Slice true (roots gbAtlas) (target gbAtlas) (0x550055005500550055005500550055005500550055005500550055005500550055005500550055005500550055005500550055005500550055005500550055 : Sig) 5 :=
    slice_correct (ms:=fixRows 9 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq6 certq6)
  have q7 : Slice true (roots gbAtlas) (target gbAtlas) (0x5555000055550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555 : Sig) 4 :=
    slice_correct (ms:=fixRows 49 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq7 certq7)
  have q8 : Slice true (roots gbAtlas) (target gbAtlas) (0x555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555 : Sig) 5 :=
    slice_correct (ms:=fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq8 certq8)
  have q9 : Slice true (roots gbAtlas) (target gbAtlas) (0x55555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000 : Sig) 5 :=
    slice_correct (ms:=fixRows 1 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq9 certq9)
  have q10 : Slice true (roots gbAtlas) (target gbAtlas) (0x330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033 : Sig) 5 :=
    slice_correct (ms:=fixRows 10 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq10 certq10)
  have q11 : Slice true (roots gbAtlas) (target gbAtlas) (0x3333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333 : Sig) 4 :=
    slice_correct (ms:=fixRows 50 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq11 certq11)
  have q12 : Slice true (roots gbAtlas) (target gbAtlas) (0x333333330000000033333333000000003333333300000000333333330000000033333333000000003333333300000000333333330000000033333333 : Sig) 5 :=
    slice_correct (ms:=fixRows 34 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq12 certq12)
  have q13 : Slice true (roots gbAtlas) (target gbAtlas) (0x33333333000000003333333300000000333333330000000033333333000000003333333300000000333333330000000033333333000000003333333300000000 : Sig) 5 :=
    slice_correct (ms:=fixRows 2 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq13 certq13)
  have q14 : Slice true (roots gbAtlas) (target gbAtlas) (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f : Sig) 4 :=
    slice_correct (ms:=fixRows 44 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq14 certq14)
  have q15 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f : Sig) 4 :=
    slice_correct (ms:=fixRows 52 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq15 certq15)
  have q16 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f : Sig) 5 :=
    slice_correct (ms:=fixRows 36 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq16 certq16)
  have q17 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000 : Sig) 5 :=
    slice_correct (ms:=fixRows 4 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq17 certq17)
  have q18 : Slice true (roots gbAtlas) (target gbAtlas) (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff : Sig) 4 :=
    slice_correct (ms:=fixRows 56 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq18 certq18)
  have q19 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff : Sig) 5 :=
    slice_correct (ms:=fixRows 40 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq19 certq19)
  have q20 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff00000000 : Sig) 7 :=
    slice_correct (ms:=fixRows 16 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq20 certq20)
  have pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p :=
    List.forall_iff_forall_mem.1 (show List.Forall (fun p => ValidPool true (roots gbAtlas) (target gbAtlas) p) gbPools from ⟨build_valid q0 [] rfl, build_valid q1 [] rfl, build_valid q2 [] rfl, build_valid q3 [] rfl, build_valid q4 [] rfl, build_valid q5 [] rfl, build_valid q6 [] rfl, build_valid q7 [] rfl, build_valid q8 [] rfl, build_valid q9 [] rfl, build_valid q10 [] rfl, build_valid q11 [] rfl, build_valid q12 [] rfl, build_valid q13 [] rfl, build_valid q14 [] rfl, build_valid q15 [] rfl, build_valid q16 [] rfl, build_valid q17 [] rfl, build_valid q18 [] rfl, build_valid q19 [] rfl, build_valid q20 [] rfl⟩)
  have low := boundgb certgb allCuts pv
  have lift := lift_ok (u:=true) (ms:=fixRows 0 0) (raw:=fullRoots) (T:=fullWord) (xs:=[]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 0 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4278124264 * 2 ^ 32 + 4277075688) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36386.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,3]⟩,⟨.or,[4,6]⟩,⟨.or,[1,5]⟩,⟨.or,[1,7]⟩,⟨.and,[1,7]⟩,⟨.and,[4,8]⟩,⟨.or,[3,11]⟩,⟨.and,[2,12]⟩,⟨.or,[10,13]⟩,⟨.or,[0,14]⟩,⟨.and,[9,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124264 * 2 ^ 32 + 4277075688) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124264 * 2 ^ 32 + 4277075688) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36386

open PEqualNP.Outside.L_meta_36386 in
theorem PEqualNP.Outside.L_meta_36386 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124264 * 2 ^ 32 + 4277075688) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124264 * 2 ^ 32 + 4277075688) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allq6 allq7 allq8 allq9 allq10 allq11 allq12 allq13 allq14 allq15 allq16 allq17 allq18 allq19 allq20 allgb)
