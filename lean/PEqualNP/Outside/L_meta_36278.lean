import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, children closed at the parent by
-- restriction pools (closeChild of the model), and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36278.Model
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


end PEqualNP.Outside.L_meta_36278.Model

namespace PEqualNP.Outside.L_meta_36278
open PEqualNP.Outside.L_meta_36278.Model
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

def SBf (j : Nat) : Nat := [8, 6, 6, 7, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36278

namespace PEqualNP.Outside.L_meta_36278
open PEqualNP.Outside.L_meta_36278.Model
def s0K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K6 : Nat → Nat
  | 0 => 0x4000300308078228134408b0022025850006431400d8fc31fe42fc10fc43fd31ff43ff31fe21ff42ff41bc40fe30fd40fe20ff20fd21fc32fd42be40fe10ff30dc30fd43fd41fe43fe32bf41fc21fe40ff10df31dd31fc41fc40fc42fe31fd30ff21de30ff40fd10fd20fc20bd41fd32fc30ff32fe41
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x841df42cc6fca198df95031ef29c43de53c82eea2905fd4142de19283ee21883ba60186f55031f790c43be42506fca7106f10020bfaa041bc52103da43904f55031be2a4637d54c42fea99877d4d10cf988817e50042faa9086f50710bea9663fb20482fca9985f15010fc90041ed320cb78a89077d0f31bfa9a417e53086f8a098dfd52309f2a463de300837a64a0df94441fb88021df53843aea298db14910bfaa4637c53486fca5885f94630efa0e63be54c42f2a010f78c320beaa261bc51902fea5085f55320ed28061bf544c3ba87994f952219eaa4833c54442faa7a17790c30df28283dd50cc7ee4310df94031bea9c65df319037a8390efd0430bea8c657e52843be6318df95232de2a265bf414c2f8a990dfd5121efa9a85ef21482fca3215f94c31ef298857c548cb78a6205f55030ee216637e530c27ea9085794c21be2a6653e54c43dc40905f54740be29421dd310c3be6310f714b31de2a261bd548c6faa2217708430beaa241be400c3bca81857d4d20bf29e437e54086fca3a17dc4210dea1a835c504c7ee42086f50620ef988633e541067ca810de94021be29021bd43903de84a15fd5320ee21e637c5150efca918f7cc440de20c817c544437c80985f94a32df29481dd210c3ba62987710430bf290857e510cbbc64187e94021bf2a2417d510c2f8a890df55121bf296837c54c42f8a6885f94b31eea10617d54906fea70877cc410dfa1c87be54042fca910efcc941df21c819f410c2fca6207dcc631ef290617e5104378801877d4a30eea98837f534433c80185f94231eeaa461ee210837aa9907794931de21683de539077c87a0e710030efa00617d500c77e8298f7cc520bea9683bc425077880987790d31bf2a621de52cc67aa3205f54021bf28c413c54482fea9087794030ee29a417d54cc77c65205f14540df2a063de438c3be84187dc8610bea9c43bf53d06f8a6105f54630bea9621ee21486fea2a16f54e40ef98a217e521037aa910efd0421bfa82637f524c7ba8498df54f40df218815c53443bca5186f0c640ef2a2635f53442bea7085fd5131ef18261dd31086fca021df54b43bf29043dd319037c65a0ef50731de10c817e500837ca6a0dfd4940de98c815d510c37a82a077cc610beaa487bf41487be86185f54620ee29c21bd505077e8220f7d0430ef188617d519037e86a15f54a30ef98e21bd21903bc8398f714931ef98e617e530caf8a788778c931eea96637e54cc7da40105f94e21ee98a43fb40902fca9186f90c42cfa0a63dc414c77a85206f50b41ef200615d53886baa3187708630ef990657d53483bea8187755131de988813d54087ba86997b48421dfa9081bf41d033a63206f50420dfa0481dc430c37842206f94640dea0e415e50cc7ba63a05f54a40aea9e817e50d0e78a8995f54242
  | 1 => 0xe519027aa9985f94730bea9021bf51506faa7206f95231ef282637d53102f8a2986f90310bf29e81bc54843ba63885f94641bea88417e53c82fca4197bc8020bf29487bd43d0af8a4a05f94830aea9e217d544c77c84204f54440eea0a63dd324c77e83107d8c4319e2a261df308c3ba8698fb8c832bf29c217c538877864205f55242dfa8c81be54886faa70877d4131bf29a41bd41043de85217790f31efa9a81df52cc6fca820778c932bfaa265bd410c77a8310f7d4430bf294617f53c837aa8195754e31bf2a641f751483be62186fd0721bf28061bc40c43bc85185f54432de99081dc328c2fca5987ed0140bf2a087be53102f8a498f74c620eea0061f9300c3bea898ef14941dea08817e52d037886a0f714d40bfaa261dd31c877e43205f94910fba0c83ec52442e8a29077d4630ef21e65dd418c2fea4085794f20ef18621be408837ca4205f94021bf2a0836f52442fca40877d4830b6a9021bf32d06fca420f7cc530f7908437e53c42fca121df54730bf2a4215e53d03f62088774ca30beaa661df430cafaa1a1ef50c43dfa9481ec21882f8a898df94c10bf280817c540c6f8a8986f54a40ee18041df324c77ca9986fcca40ef28861bf21103bca7885f54831dea0a41dd518c3f621084f55032bea96817d52107b861905f54f41eea9e81bd43102bca0185fd4f10de20441bd519037ca7a0df94221de2a2217d5010efea2905f94431deaa043b751507be43187754a30eea1c61de30882fca9106f55310fa88021bd41443be65195f94e42efa9a417e51086fea8185f54331bf2a0657d50d06faa8996f95320bea8c857d52906fca0216f90541be28a657d5210ebca7885fd4132be29e43bd41843baa720df14142df99081df50cc67ea8887754931bea9661dc430cbee4290fbcca32af29821bf41502faa2207715030fd10221de548c2fca721e750c439e2a4216e52043be6210df15230bf28c63bf31903bea298f714d42beaa0657e5290af8a4a0df94c41dfaa4217c53087ba62a06f90140ef19663bf410837e8621f7d0d43ef994617e5210e7aa9887710731bea9c85bd41cc2fca8997750b31fd10421df31486fca1087e50040bf2a085f7415077e83907750c43bf298857e5190fba64197714430bfaa043dd31c827ca9986f50f41df28881bd521037c80105f149109eaa6417d53443baa710ef94e40bf2a643be40c83dc842167d0731be29287dd530877887a0df54042be2a0437d528837e62206fd0b41ee98841bf50d07ec20886f50040dea96837e528c778a5a0ef94341aea9c83bf52506faa720fe8c030ef98e819f31902fca5a1ef10320df292837d548cb78a7a0dfd5110af29883ec21083ba81186fd4b41bea8465bd52507ee6298f714630faa08837d520c3be63185f54610ee29a217f53086f8a9085f15331bea9
  | 2 => 0xc6baa7906f14e40bea9843dd5310afaa118df94032bea8e657e50883be85187754830ef218877c54083f480206fd0621ee182217e52082fea090f788630ef98e437e510c2faa790ef8c440de286837e51c82b8a7085f94321df10c817d54ccbbe83186f50430dea8881de54cc7bca610d714d20dfa08817d52843bca198ef50530ef210619c408c2fea4a1df14b10ee184217f54ccafaa121ef54341bea9487bf410c7ba8798efd04109f28683bc439027aa918f710d31ee98821be50103ba62205f54e20eeaa6637d50907bc82185f95121bfa9261dc424c7be63106fd4e40dea0e817e51d0efca2215fd41419f2a0637c54c837c42206f10a40ee98863be43506faa518f794c41df21c857f5350afaa9187790230df20021dd31442faa620d754c41beaa043bf41483b887195fd5032ef18c617e50ccaf8a8185fd5010ef996637d5190f7c80887d88421be29821dc320c2fea5886750430f6a90217f5050fbaa8186f10c40bfa9a81be40483e842085f54c10ee98a417d50107b8a9185f95010df192837e51ccb7880085fd5321ef98061ed4210afea7106fd0510fca8043bf5310378a6a0fecc230bf29a43bc42102faa0196f10c429eaa443bc31103e8a2907710230beaa6437d50c87baa7906f14141dea0843dc438c3de43907d4c431bf284617e520c6faa918f7c8430dfa0c837e50d0b7ea6a0d7d4d42bf28683bf41843de41105f14d40ef18021bc52903b885187b48520bea9c617d548837880906f50531deaa661bd41487b863185f15032bf2a2613e5090278a0a0f74c610ee28663be40842bea6a04f55010df2a0437e509077c86a1df94632ef182417e50106baa608770c310ef98a817d5110ff220085f14132dea0883ef52443baa218774c830efaa663dc504c77c83206f10110ef20a637d51c82fca720f750430dea9a837f5150e7ea8905f54910be29a83bf511037a83185f94420bfa9c437e518877a84a0df14542bea8443bf41cc37c82205f94a40fc90221ee520437e85217e84010efaa461de53042fea9885714d40beaa4439d414c7b8a4185f94740bfa9e43bf544cafea2996f10210af28461de30443be62105f54c42be28a41bc51102fea9195f54342eea1861df31c83f241084f95032bf2a665f641106fca621ef4cb419f2a6417d53c437c81985f94240ee19263dd31cc2fea6107d08610de19683bc4390a7ea8996f4ca40bf288877e54083baa788778c210efa92637d50ccb7a86a15f14141df216835e53907bca318770c220be29261dc54cc77e8398ef94b41bf2a2637f535077ea8885fd45309faa2617e53443bc83186f506409f280817c5050f7865205f15220ef21a657d538c6fca8185f55010de20661be429037e83887790931dfa1a83bd418c77ca8196750630ef990617f52442fea8905f54a21aea98857
  | 3 => 0x1180c010100b01e000103c880079560a014018060a81e001ea00a41a48080a04ef38000200c000ac002ec080100000208006000220480603000088260086a090000701c30a4e000780000a02042038a00c80006879b189003808830000b80000800168060c800061f234a04006bc03812008010600200c5200802780320001e0080000012198200001403800198120b000868106487e0701a018100d0000283c158281386a010041800611b580b000008000785e6d81c0109c0082201008000000480001030008201281c0408a0009e8b80007802718020000c040000e0040100002020010260103e030120c80405000068dc03160054ea008020102c0000405000018280080002014010004b03001002138061a0141784c0100c078023e07e418082680c0c04a2103a1486209810008e400802090da01888090541b002020181400e2001000026598041040201024020081681e8a9461101c01c85ce0142e2100a0121e0040000000026050121c094000140a02c030000180401004000e20300a05006000160081e0429a000060100800000148040b0000001c00004e70100000003ac8390d204800f780c000560003e10800428720503bc5800010021106e06000030460182a018000054e00810028060282620114020060004a0c80000800018051080806800018001185e275fd5220cea0e63bf43d0afca520efd0630ef10861dd530437c84a15f14d42be29c217e508cb7882206f8c840efa1263fa200837a42205f94242df20461de328c37ea0a0f710030dd280817e53082fca7a0f7d0e43ee98c61fb20882f8a8997714a30be2a2417d54903ba4318674c440af29c43bf42902faa7905f55020cfa0c61dc310c37e87205fd4941dea98817c53c83b884187d48421bea9a43fb304c37a84205f15221ee196637e53d0b7e87a0fbcc932bea9081dc418c2baa610ef55010ee18021dd31887bc8598df54743bfa8a81bf401037ea8907794f40bfa9821bd4210b7881185f54742bfaa6637c53483ba851877d0d31ee2a263bd53d06fca2205f14121af298857d54442b8a6a1770c120efa0461bf42102f8a7106fd0640eea8263df414c7ba6598df55031dfa0c637f548873c81186fd0c40af29863de314c6fca8887750731dfa12833e54042fea690f7d0e30bf29c81bf4210af8a99877d0e32df18c817f540
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x442cc6cd62d4331a798331102cd62146309759531d031d5350410c7d53318435763d4520a758c425071e5494e218f990540434f5294a308f98254886766115332a798e519033464d45209d984540c23c6454d209e983548ca5f6354910b6980518c2da60d46309e98052042d561150309758e544c23d6414931a7993528c33954540219b98a544423e64949108f592510423d6414f21a7586400c23e650ca40c7151430c26f6548421c714d415031e53900108f590514c355515043097996414c63e65d0510b5984520c2ad621464097995314839a50100309798f5050a9d6310a40c715331842db6048430a7592410c29c6454331a7d8d521031e54cc421ab988519025f635424197d8d50c865d6194c42d694e50087e32148210c755230c423e64d4121b6580210c3976150630c7150304826d6215331c714e40502786055121a7d91324c69d648c430b5587424c72c52d051097996410c23e6515132a7983410c2b86050730cd945410834d5354810ad984521025d63d4121cd15351482da60086308f19153486ba6014a408f587544cb1d53900109718d54442756114c20b558452cc65d658c010a798e219025e63d41419758f52c431c5414d20b6181310825e63148109e583548cb1e540c320c7550430c26f6254d10e5d85414c63d6595031a798c411031d54cc410d5d4c514834c52cc510d518f514831e54cc4318f992510429d648863097d8d52103a84048020ab18950506b56114c40a758c411027b6054d218f99052c431d544c621975875350b1e5350410c7d4c404831d4354443d354830042bb6048440c754c40c825f654c431dc58051483556114e1097181538865c6354b418f584544c32f52d0510c755131c423f6550040cd584548433551d0440e5545410c31f54d4d20d6d8e500872f5294a408f594311029e6010030c714d414834e5354810b5584308431d5454c21a7181410c29d63084408f58654c831e544c4109bd89544427661150208fd9541cc2b56190010d64c6500875551884308fd95410869c644c030c795230c42e461480208f995414c31e53507208f59252842b56114f41a7d91524c65c65cc520a7983414c67761551209d984530831e548c010ae580211025c63543418f191524433451901209d584540c3555148430ced91500865f63551208f59741cc398400c010c795131c431c53901208f990538865c6354a10b5d85544c65e63d5031c7d4f418432d5210010c795253c825f6550a309ed8154486796014c21cdd93514825e6394642c755253c423d6494d10e610030c42d56115331a718d42d069d6414b319e583540871f535051097195434c65d6594c21a7191524c69f644ca30ae181410829f6550c438fd95329025d63947208f592510826e6294d1097997315025d63948208f596400425e65cc520
  | 1 => 0xc71c5350d41ae980511031d4394043cb15052442796015021c794f41c4399419403097594418c31f5410e30c7950300429d6490c43a798c419034c528c110c715131842ad62144409758e524431e544c421c7952530865e65d0d3197994420c395414c721a718d4210a5f63550208f191500863e650cb418fd9153483976150430a7990218c31d54d0c328f592510c32c54d4910c754c40c425d639521097d96300423d6550720cd546311029e63144409798e510823d6588640c794f41d03692154021a758c511029e640c8309798c54c829e6310840d314c524425e6315031e6942400c23e65d054097594430ca7561153329798e518829e6390440ae181311031e544c431d354852cc63c64548309758f505071d41141319718d54c863c6454e10b6181544c69e6494a30ae582321032f54d4910b6980210c29e6390640b5987424c63e60151329758c52c429d6314b419758f548869d6488430c7552300429e6314b418f596211031d5494f209d986544825c63551218f994321025e650c1108f993530423c6454d1097596210c23c6454231a798e415074c524c510a758e211031e5454c10c755131042d5618c2109b588540425d654c720c754d41c831e535062197994410c23d61d5130d3d4a304425e6315010c795153c8277654c43197594424c65d63149419b58b530431d5350421c755030c429e640c6309e980530863f64542319758c540431e54cc730a7990524c72d5210840d314f52443345414520c7951438c2bb6054941d3d49314425f6154f408f993538863f6454d21a7593528c25d65906308f592520823f65504419758e510431c54d4d208f993538829d64149319b58a54443a54148421d5945311023d6115132d654d500863d6494910a758c419031e53d0431979825310b4e524ca3097d95320caba60d4840c755230c829d64cc230ce980548425e6315310a798c521031f5390120c754e40c829d6308640c7952530423d61d51209758e51d032d525041097982530872d5494810ad98453103645148520c714c408425d65cc7409718d50c87394154021c755131cc31f53505209798e51c825d6508630a7d91320c25d65d0c3297994418c32d5214941ae580219029e648c6309798e548425e6315021ce983548423e6494d10b5584520c23d64d4e208f592530c2b56114b418f99052042ba6008440ab98853d069d640c4309758e5108755514c440f20c1200823c6454032c5545410c23f65d0730da14a20442d56194931c7d4e539029c64541319798f504865e6395220cb54a400423d6508640cd587548435453145208f5935204395514c4408f994219027960d4c21c7d53314825d63d4810cd951411063d658c4409798f5408715514c440a7992210c23d6494421a7992314c71d5310f419798c540823e60950319759
  | 2 => 0x64944309758e51d0a3c6454b31cb14942506b56194941a758e419031d51d043097d8d544ca3d6494e1097596410c2d76154931d6982500c25d63d52208fd85540425f6154c429798e529023e64951209b98854cc71d5314d41a7d9152cc65d6314542a71814310e5e6395120a719152cc6776154d20ae1815250737515052097195315031e544c730c754e40c433754d4520a718d521031d540c0109798f54c823f65d0720c7153314429e64146309b99721483345150520b6d81544c65e6014d4297997314c23e64d4810b5584300431d53d0842b3588540c31c5450f31d3148304423d6414c10cdd44404831d544c72097195314423f654c8409758c54c831f54cc530c75525304357510c1208f195329023e6414d219e983530863e650c9418f990530863e6494820c754c431029e640c43097996304431f54cc510c7553320ca3e651512097d8d50086d561d4b319718d548433551484409b59621082e9600842097d95420c31e5454e21d3d48304433551d07409b58a534425e63d53109e983540863c6550530c754d418863c64542329798e51d0a5e63151219dd9510042ce6214630a7993308c25d61d4d209758e519023f6590010c795030c42b5611021097d8d501069f6354941c7552538863e6414931c71523084356631452097994424c65f6354341a758f50d063e6494420cb148404423d64d4f10a758f401025e631454097587535023f6454d109718d521023c645433197996218c31c5350610d654e500875561d4e10d3d4c524423e6494720a758e219023f6510010a758f409025d63d5021c794f410863d64d41219798e524434f52cc510c714f41442ad6214c40c7d06500c23f6454c20cb54852d076552c8410a7191520c31c5390210a7d9132cc75863940218f19150c86e462440108f992528c31d5350740d9185520431d540c320ce506500872f521011097d94300425c6054c218fd9150cc71f544c520c7547418c2b86050430ae980219023e64145329718d500871e53504418f990514c31c63550329d584540823e6590130cd546211031c548c932c7551310c71d5314c40ce552500865c65cc540a7990324c65f6354342c7d51318423d6590440a7992310c2b661cc94197596310c23e64150318f596540429e6414b31add85535071f5310210c7d4e405034f53d49109758e518832e5454810d394b310431f548c1209d185544825e63944429b98a524426d62150308f992510c71f5410e32a798f50d071d5410f319758c5448798604c440c7d52308425e63d5220a718d505063f6454a10a718d421032e52d0410a798f505071d5350441cb54842d065e63145209b994524425f654c740abd89505072f54149109798c540ca9d6390440a7983319029d64cc030e6cc6501025d6315021c7550434c71f53d0540e5d47414
  | 3 => 0x4309758e544831e5310310c7152434ca5e6510b31c7150534431c5450f329b58b548c27b6550040c754c53d0738649402197195434cb1e5454c219758c54c863e6414c20a758e519031c548c110c7550430ca3e64947329758c540831c544c51097597400c2da60d52308f99252842ae62d4341cdd45415023d6494a309798f540425e654c540b3189544c63d619533097584534825c6550b31c794f418871f548c1109718d508869e63d0040c755153c423d6414520a7993300c29d6390541c7d5053442b86048440b558754cc66e62148109798c525065e6395110b398854cc71d53d0410c7d51314431d4194331cb149414429e64104308f993504c65c6550a30c714f4350b1d5454e218f191508863e658c4408f99054086cd62d5230ce95150087c53148421c7d51314c25e6394421a758c5190356534c4318fd9541c823d6115120a7191320ca5e63944108f992510ca3e658c6408f59251cc397614c640a6181311023d64d4f20a719132cc6b561cc9419758f540423e64946328f992518c23d650c840ce982501023d6494632c7d52548c23f6454221bc580218431e5454f10a7592528c29e63109419718d50106cf6255131ae181535065d65cc7208f99051482d8604c7408f99353c825e63d4b10b6983510c3696014910cb551520425d6590c3097994304832f5250510c794f410425e6510531979963048355514c4209ed95200832c5290110d514731482ba60146408f590534871c53909428f596319033754145209758653d025d63153109798c54c866d6214c10a798f529023d6494431971815310b3451d0520a7590510c2f06148210add85525069c6350941ad58753d063e60950328fd8554cc31c53d05209ed81544c69c604c640b6980528c29f6350b41a759032cc6d8604c4408f994319025d65cc421a7990414c69f6350840c7d4d418433b6494021c7d50304829e630c4409758e511025e6508430ad584521032f5290110ae980521031d5454c109ed95100425d6315221e5945311031f540c2108f996219025e6510a30d9147214823e6508440ce191500874e528c010d5d47314829e6310a408f181548874e524c410a758f505065f654c030e64c6501025e6094e41c7553310871e53d0720e6980408c29e640ca309b988540c25d6510c308f99352c431f5390210f8086208423e6494c30d5547310c31d5415030cdd47414823c654cb4197d95400c31f5414d208f195414823c6454c209b98b530425f654c720c754d41c425d6395220c7d4f414425e631522197d8d544423e649473097195420c29c6350a40ad586535069c6354941a758c525071d51cc440a7992518c25c6355120c7544400c23c60552319758e5190b1d5454f208fd9532d063d65d04109798e51d031c540c210b5984540c25f6154c10a7990210c29d
  | 4 => 0xb98b548c23f6454021c794e40c429e649443097d95424c63d6508440d9146204823c6015110a758c521025f6354a108f181540c65f654c4109e181544c71d5415131a7d91520c23d65507308f592510ca9c6354b41ce952500863d65950329758f54c42d8604c5109798e511025e6394820d5945310835a60d4e109e181534869d640c931ae980531029e63d0240a7d8d429023c6550510b358854cc66e6214c1097d8d544c27761549108f992538423d659502197994534431d51cc640d354e520423d6414b108fd9150ccabb6054d41e6d8131102b56110010c714c404423e6588440e6980400c25d6314810c7153314836b2154021b3189504c6ad6214f418f5964310a3e6515110c794f4110754518c1209718d5010a3d650c94197d95310869d64146308fd9532506ad62d4341b6980548c25d6510430a7191328c25e6094c41b6d81410c29d64d4331a7590328c2ba60d0610aed81311031c53d0540c7553318c63d6494630a718d50d06796584010c7153534429f645433197d8d54c869e60d0731d5145314831e53d064197d8d5010a9e6394a40c754f411069d64d4131ae983519023f6454321a7d8d505069e6414830c754f410865d6114d42c754f41c833551506409bd9520082d56195131b6980510c25f65cc720c7953318871d5494c218fd9152cc71e53504318fd91520c398400c22097584535031f54d4d109bd954210ada60150308f997414c23f65504109758e544423e6495110d5d46304825d6588630d3948300431d5350842b398b548c29e63084409b189544c74d5214931a758e311029c644c931a7993504c63f6155320c7940400c23c645403197181539073b4154021d354b310432d52d0410d558c514835b31540218f992518836952840108f593530871d5110230b3588510c23d65d04218f996404423e64944309bd95320ca3d6414c20d394e520435551cc7308f994544c2da6014830a7590218c23e60950218f593538869c60507318f59251c831f53d05208fd91500c757514c520cd59051482776550441c7551310865f6550b318f992534829d6494630a7d8d50d06d5618c01097994218c23e65101308f59053886ba608c840ae181418425c6354242c714d4350b1d514c440c7545410c25e6314542c7d04504c6986050430c7151434c66f6255131cb949429023f6550c43b6181410c23e65d0d42a7584408c23f645423297195424c63d6414f209758c514825e6314c219798e534429f6354b419758f5050a9d6310b4197d8d548431c54cc530cb948400425e6014d10975855304336641452097997314431d51900308f5925388395414c510a799032cc63e6414f21b6181318431f548c130d3548520c397614c4408f195321029f63500408f593504cab56190210ae983511029d63d4a40d6d8d50086d86048
  | 5 => 0x4044335515042097594210c31d53d071097594420c25d6594c108f594400429d63944408f997414825e6314b10d914a104434d520c830e6181410c354510c120ae983539023e64d4c218f995414823d64d4b10b3988540c31f31940409718d540829d6190230b6983540c31d544c832c7545319029c63500409798e51902e96008620a798e21102ac6254d41d618d500863f6454032a7983418c31c544c520c795230c829e64d4331e6100304831c54d4e108f597410c74d520cb3197594428c31d31940409718d50d0a5e6394a109798f520431e5494f10ae18141c829c644c8308f993504cb1e5310010ad58752d065f6550c43c7152304823e6414f10c755331cc25d63145408f982548c63c6454f2197996210c23e650c440a7592318c23e649513097594300423e6414f20b618131c82d96090830cd545311026e62d5010a7990510c25d6394a1097d8d5090a5e6094e21c754f418871e544c72097d8d544865f6354b41c754e4310aba60d4c40abd89535071d54cc621c794d410865c6054c418f990540ca9e6488630a7982400c29d6490531c7951318866d62d5010c714d414423e60d5132c7953310431d4194030a7181418c25c654c520d6cc6500871c53d0610a7590320c31c53901109d185534823e6510120979835350a5e63d52218f590520435551904308fd95410c6d96008630ab988511035a5354021d3149324c71d5150630c755331c431c5310120d354a300429d6408430d64c5500874d524c410c750d5210ece6214430c7152304c3355150430a798c219033451101208f586540caba60d0510a7d91504c63e6590120c7942400c23d650cb418f59741c825d6394a408f99253882ae6214c4097180534425e6590630ced06500863d6494620ae980539029c6050531c754f41d025f6354221e5945410c3365150430b398b50cc6da60d4830a7584400c31d51902308f181540863f6155032b6983528c27765484219718d524435453d45209b18954442ad62d4e408f594329023f6454e108f59251cca9e6314941cb949410431d54cc4319ed95300c26c6254d10c755054cc66e6215010c7d954310f1e5350e408f191528431c5414e10c794c40c823d64d4c10da549100429e6394440c7d4d415025e6314c10e5d45414c69e63146408f197414c23e64d4f10c794d41c425d63d5320c795331c431c544c5308f593504c6ba60d4a409798e534831f5414e10c7150304431f41943319d594210431f5310110a7d91300c2da60cc6108f181540cb5a6014e10ae18141442d860549318f59053c432e5290010d5545318c23e6495132cb548521029f6350941c7d50304423e6414c10c794d41d025c63542419d98653482756194d208f590530863f6454910a758e529039b41940308fd9153c863d650c640c795331c829d64148309
  | 6 => 0x85e28050240140a8000080580996b0060840000500c05800000000109aa0d215a8a06300e04401c028002c80082e14a242130ac8000000940100000a00c0094800e011a28160000092fc880000080187c06a0140080000041817000006024000000000003d0000002080081f1160300b80201e0280101c07207c62c4700706000062082038f30003840540200755c06c02bfd0000881d809000108d380603a15c0a000004000598030040300300087a078099c35ee1542282e0060001a802458d1000000002001c580408660004000000000108170020281a8191206640000664c0301802804e5040402d000000028800480f00887400a2b0008048400800000c00801c0c01601a0080b010118278040015be0980021501e0e4058f70460041300b01c084ab819776004738000040000703a0000603780412e6f41341f00e00c05942094238310260040094204f0141640200c022030000000309ac2180f0000101200f01400cb800004a02d25000512010099301300083187b0060c0000000020a866009074010029350020100200f46601000001054000940460160a00000239800c018000040001700188aeac0388404e7fc010690f8054dc02f000000000050045e80782301e0cc34830004030189f01f029c0681f0e00102500a00a0543508606c0080000d0001041c82902200c070014d01e0008650042a00581b002004000325567641e00434c03000000002370048024bc058003af114970050050065e8960145860040281000a02036ae00160000e80e1440081c8260000840003605400800811018078338001300ac2101300003c17008000014000000040a0018330000940604c0a408000844000de8010020000040004b000cfc1501d0040d40308842c1bf5753d4520b6d81524c65e6590d32a7592314c65d6394420c754c400423c6454332a7590318c31e54cc631c754f4190757514c5309e19520443375190120e6d81410c31e53903208f99251086ae62d4e40b6982420c3976150731c754c4310a3d6155010a71894310e5f65cc740b3d89504c71f5390110cb95252042756195120a7d854310f1c5450d328fd954210b1d6315132c755331c825d63944428f195325065d6194f20b6983314427a60150218f197414823d6414532e5505310865e6514d20e550531c426d6594810a758c421023d6494d2097597310425f6154f20a7181311031f54d4e10a798c42d063e60151108f994
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x608ad204000000008e06005010004400c3748800008000027000116300800400b0f00002800418286400020a0a0000b0230290000080000000130244380a6001130c00000e22a2302821861853181414430c2a0c098a21261c16494430c22a2302622069161100300430cb28801802145dc54354443838ecaa264195157195131cc318a88c0988818354d6214f41e08a4a0a6288615535844004306b1aa429683835516215331a18e4a98a6a0e0c639494290306b22a419663431d15214931c2aa6b08a62050e72d52548c390a0a42a80438614c6050610c1ac6a908420514755053144306b1aa421683c4547604c440e20a2200609069151181410c306aa2c42a06185d4d6110210c18c9292651862552584521021ab88ca99081c45476050430930e0b1ca22061554584300424c382c710881431cd521494192ae3318a4a0d4870548524c70a32a8298a21461c15415131a30e0aa08698d9070505314424ab8cc829263455c45450c30c90a4302628860d6354852102873a6a529461439cb5394e40a1ce7a94a5205157194d41c830d298c0a0e41a81844048020c1ac8a90a598e4552584520c384a9080180218a1486050510a30e0a08a098e0c631494250749288c0a0861269c36454830c1aa6b10a6205157115143ccb0aa88c098881a4504604c510c2aa23028218691511813110294382a429283465d4400c010a34e1aa0871961561544400c30ca88c0a0861645c4400c010a18e4aa08698d187054c535061c382ca19283431c95415131c32a2302622060c64149324c788a0a62a8043855915188430c8aa4b0860084e276c85208430ab1aa310881855516115030ca2a2302622049a70d8d521028ab8ca6a0e81c4544604c440c22a2302821849870592210c30d2a0c098e4186150604c610a1ce5aa0871861754584308428c3828728087895496110010c1ac8a90a4185157195131c8286b90a8a1861d04c52154021ca2a2302821850d7215143cc62c382ca212638c54460504308aae232a8418692511813110306b22a419061b01843048020
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x30000800001d00521c1414c510e0152584400c010c11655c4400c010a108058d5188440c1175584400c010d01525c4400c010e0052504604c510a118194c6050720a1181950604c720a10805915188430
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 48
  | 5 => 1017
  | 4 => 1345
  | 3 => 112
  | 2 => 10
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s0K7 (i*5) 5
  | 6 => packedAt s0K6 (i*16) 16
  | 5 => packedAt s0K5 (i*27) 27
  | 4 => packedAt s0K4 (i*38) 38
  | 3 => packedAt s0K3 (i*49) 49
  | 2 => packedAt s0K2 (i*60) 60
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 7 => 2*((h/1+packedAt s0K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/30+packedAt s0K6 (768+(h % 30)*6) 6) % 48)
  | 5 => 2*((h/395+packedAt s0K5 (27459+(h % 395)*10) 10) % 1017)
  | 4 => 2*((h/469+packedAt s0K4 (51110+(h % 469)*11) 11) % 1345)
  | 3 => 2*((h/79+packedAt s0K3 (5488+(h % 79)*7) 7) % 112)
  | 2 => 2*((h/17+packedAt s0K2 (600+(h % 17)*4) 4) % 10)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffff81ffff83f07ffff83ffc1ffc0fcf9f3f3
  | 2 => 0xf07fffe0fffffff81f07fc3ffe1fffff463c7f
  | 3 => 0xff81ffff03ffc3ffe007ffc3ffe1ff0387cf9c
  | 4 => 0x1fffffc0003fffff80003fffe0003f80fe0
  | 5 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x210c08c42890400165098044c022425818d1b1
  | 2 => 0x44109102412221280a422429121494a1422446
  | 3 => 0xa22522481a440652a084ca8265412a0a854a98
  | 4 => 0xcb59c4929076ab9cd3d06223b9980c33e80f60
  | 5 => 0xc61871ce38733e71ce77330311030c3f7b000
  | _ => 0
def s0Atlas : Atlas := ⟨7,rawDecor 62 s0Pos s0Neg, 0xfcccfcc0fcc0f0c0fcccfcc0fcc0f0c0fcccfcc0fcc0f0c0fcccfcc0fcc0f0c0fcccfcc0fcc0f0c0fcccfcc0fcc0f0c0fcccfcc0fcc0f0c0fcccfcc0fcc0f0c0, s0N, s0R, (fun _ _ => 0), s0I, []⟩
end PEqualNP.Outside.L_meta_36278
namespace PEqualNP.Outside.L_meta_36278
open PEqualNP.Outside.L_meta_36278.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x1000b0000200100004bf42dc30df32be41bc41be40bf43bd42dd32bd43bc40de30
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xa6a90611d531066ca3204d14542
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
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
  | 4 => 2*((h/18+packedAt s1K4 (192+(h % 18)*4) 4) % 12)
  | 3 => 2*((h/15+packedAt s1K3 (108+(h % 15)*2) 2) % 4)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x3fff83fffff07e0ffffc1ffc1ffff03e79f3f3
  | 2 => 0xc1fffc0f83ff87f0f83fe1ffe1e07fc1a67d9c
  | 3 => 0xfe1ffff003ffffff003ffe1ffe007fffc78e1f
  | 4 => 0x1ffffffc0007ffffc0001fffff8001f80fe0
  | 5 => 0xffe00000000007ffffffffe000000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x840088a200808002284c02240229109408b0b1
  | 2 => 0x9449186425240a505a15214d21432584a25594
  | 3 => 0x89221014a4844a50422541254044a29450a0a
  | 4 => 0x295c4249606d57399683111b99960309f00f40
  | 5 => 0x3198738e738e67cee73b998311180c31ffe000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaafaa0faaafa00faaafaa0faaafa00faaafaa0faaafa00faaafaa0faaafa00faaafaa0faaafa00faaafaa0faaafa00faaafaa0faaafa00faaafaa0faaafa00, s1N, s1R, (fun _ _ => 0), s1I, []⟩
end PEqualNP.Outside.L_meta_36278
namespace PEqualNP.Outside.L_meta_36278
open PEqualNP.Outside.L_meta_36278.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x8be41bc41f510bd40f710bf40
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x272a020ec50110
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 6
  | 3 => 2
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (i*5) 5
  | 4 => packedAt s2K4 (i*16) 16
  | 3 => packedAt s2K3 (i*27) 27
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/2+packedAt s2K4 (96+(h % 2)*3) 3) % 6)
  | 3 => 2*((h/1+packedAt s2K3 (54+(h % 1)*1) 1) % 2)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x3ffc1fffffffc0ff83ff07fc3fffffd8e31ff
  | 1 => 0xfc0ffe03f07e0ff0ffc1ff83fc3c0f02f3cecc
  | 3 => 0xfffffffc007fffff0001ffffffc00fff03ff0f
  | 4 => 0xfffffff800ffffffe0003fffff003fc0ff0
  | 5 => 0xfff0000000000ffffffffffc00000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x48244448841084022a12542440652948861055
  | 1 => 0x19648c3924a494b05a50b4a1c4286a18b2c6cc
  | 3 => 0x20c91090694909550421294aaa8084b3016b0a
  | 4 => 0xb28a2122480d2a6994a408433312c023580da0
  | 5 => 0xc30c39c38e71cf8ee739ce70222308c3efb000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeeeee00eeaaaa00eeeeee00eeaaaa00eeeeee00eeaaaa00eeeeee00eeaaaa00eeeeee00eeaaaa00eeeeee00eeaaaa00eeeeee00eeaaaa00eeeeee00eeaaaa00, s2N, s2R, (fun _ _ => 0), s2I, []⟩
end PEqualNP.Outside.L_meta_36278
namespace PEqualNP.Outside.L_meta_36278
open PEqualNP.Outside.L_meta_36278.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x14000801491c01c0240080000055000780444141fe41fe10fc21fd41fc20fe30ff10fc30ff21fc31fe20fe40fc32fd43fe43ff43fc43ff31fe42fd31fd40ff32ff41fc41fe32ff42fd30fd21fe31fc10ff30fd20fd32ff40ff20fd10fc42fd42fe21fc40
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x10010053c23ca8c000410534400120021c0410404c0352380422bc282875f534427aa9905754c219e2a2213e540ca7ea890db948309faa2653d54086e8a2a15b94843aea9e4176510c2f4a010db54b31bca84637551882bca6215e141329eaa4637950106e8a2995ed41329eaa0613e54086baa6215d54430b6292216e52cc67aa9104f55331ae29a813f5444278a8985bd4910ae29a213e5488278a8995e54021b7a92833f544c2d8a4a0db548309f2a4635e53c82eca3105794c219e2a2437651102f4a118dd54440bba8a653e540c2eea2a15ed4143bd280833d54042bea6a05b548439eaa0653e54cc67ca9904f95010
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 40
  | 4 => 64
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (i*5) 5
  | 5 => packedAt s3K5 (i*16) 16
  | 4 => packedAt s3K4 (i*27) 27
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/27+packedAt s3K5 (640+(h % 27)*6) 6) % 40)
  | 4 => 2*((h/35+packedAt s3K4 (1728+(h % 35)*6) 6) % 64)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x7ff03fffff8307fe0ffc1ff0ffffe018e73fc
  | 1 => 0xf83ffc0fc1ffff83ff07fe0ff0f01ffef38ccf
  | 2 => 0xfffffff001fffffc0007ffffff001fff03ff0f
  | 4 => 0x3ffffffe003ffffff8000fffffe003fc0ff0
  | 5 => 0xffc0000000003ffffffffff000000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x309118a290425014a849d0930194d21886315c
  | 1 => 0x52922864129212816942528510a154a8b284c5
  | 2 => 0xa1245101a524252c1084a52aaa028953015b0a
  | 4 => 0xc52882492034a9ca5290210ccc4b0063580ea0
  | 5 => 0x630e38e39c73e739ce739c0888c1183efe000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeeeee0e0eaeac0c0eeeee0e0eaeac0c0eeeee0e0eaeac0c0eeeee0e0eaeac0c0eeeee0e0eaeac0c0eeeee0e0eaeac0c0eeeee0e0eaeac0c0eeeee0e0eaeac0c0, s3N, s3R, (fun _ _ => 0), s3I, []⟩
end PEqualNP.Outside.L_meta_36278
namespace PEqualNP.Outside.L_meta_36278
open PEqualNP.Outside.L_meta_36278.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x2d80410000001802000801c9001000000240082ff42ff32ff31fe31ff41fe30fd30fc43fc41ff43fd40fe42fc30fc32fc31ff20fd21ff40fc42fe32fc10fd10fd42fe21fd20fe10fe41fc20fd31fd43ff10ff21fc40ff30fd41fc21fe20fe40fd32fe43
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0xc6375510c2faa7905f94221bf2a6637c54882f8a9985f94e43ba28a65be42d02f8a9995f15310f7290617e54442faa6105f94630bf290437d54482fca1085f94032fb288617d52902fca2215f94331be298217f514837e87a15d94432de208817e5190bbe6498cf95231be29a817e52d06fca1a1fdcc421bea9a417d510cbda65905f15020ef994657f514c37ca918fd08510bf2a041fa200837ca9105f55130fd104217d5210efca620df95043bfaa0617c514837e82a05f94242fa18843f930483f4a1217790c43dfa1a85bd540877aa8195f94c10ee99065f7314c6fca1a16fd0840bf29c43bd54cc6faa321df14e20df21e837d50c86f8a4a1df94420fba0c63bf41106f4a1215fd5021bea9661bc435077e85215f54f40df21c85be540877885a07d54432be294213d548c6f8a0a0ef50840bea9e433f544c3ea62885f94e40be296213c544c2fca2205fd4141bfa9a41ef21886f2a020fb48020bf28481bd548c77aa8185fd5331be28a855e53087ba60185f94842dea1a817e5390b7887215f94030be2a021f721486f8a4a07d8c621fc980617f5350b7e84215f54242f7a1285df318c6faa120fecc130bfa9a21fb40902faa3907dc4210df21285bd43106fea790dfd4132fda02417f54843f0a0995f95232f790041f641442faa021dfd4940be2a0617e528c6faa1a16f508429f2a0657c53086f8a6a17d10421bfa92637e53d0afea9196f15132bf29e837d53902fea4a0ef90140be29a413d54c82faa8185d54432beaa661be4350efca1a0df94232fda00617e51d0bea83887ed0330beaa4657e50906faa518fe50040dfa0c837c50486fca5086f10c40eea18877c534877ea8995f54041bfa9e217d538ca7ea890fe0c320bf28c43f4414c6faa1a0df94c31bea8c857d51842f8a0a15f55032bea9c857e53086faa9207e10220bea88817e518c6f8a810cf95331bb28c87bc41902dca4187794c21bf29485f9501077ea89877cc030df2a061df310c7ee20085fd4542beaa441ed520c2faa6887dc8710fd902417e50107ec8220fdd0421fd204217f53882f8a6a0fecc210bea9081f631486faa3187dd0641bea94617a50106f8a7886f50e41fd98041fa30882f8a898df54910bf28c837d54442f8a4987e48020bea9e217f54c87f060106f90e40fc904217f540c6faa910df95332dfa0e81df4350efca898fd14542bf2a061fb30c82f8a998df94d20bfaa463f940442f8a4085f94d21bfa9c437c54486fca0106f95331fc184217c524c6fea9985754c21be2a641fa500cbea6310dd94430fb108437c544cb7e8721fdd0531de21885f610442fca8205f54e20bf28e617e52c42faa2215f95210ef18a63f95090afca418df54420bf298417f52c42eea2995d94620bda82657f548877ca8196f15121bea9883be41902fca8085e54242
  | 1 => 0xd538c6faa921df54f42fba8a857e54106faa8106f95320fb288657d54c877a8220df55021beaa4217f53c82faa998ef15130bf2a261fa401037ca8085f94d10dea1683f731c86faa198df94e10ba28a85f541443be8721fe14143fb28c877f54c83ba6218df54032fd280837e510c6f8a9196fd0240bf28e873d540caf6a0a1de94021fd080217e53d02fca9906f90541bf288837c514c37c86a0df54841baa8c877e54c43f080185f54243dea1e857e53c86fca9185f94640faa88617d538c2fca990fd44010bea9663bf43107f080905f94021bea98217d52d07f081985f94f20bf288437c51502faa720dfd5131bea8043f721442faa3a07e8c120bf290617c514cb7a86a15fd5032dea0081bd54042faa6207d94440ef98461f5314877887a0dfd4143bc282657f53083dc64195f94220bf2a6617e530cafea9184f95030bfa82637d54c42fca910df14f21ee996637e52903f460185b54830bfa9c217651102faa3995f94a32bea96817f524437c84a05f95231fa28a65bd41d02faa690fecc2309faa2657e5190ef8a710df54640bfa8a873c544cafaa521fd0c7219eaa441ee20482faa520ef50a409e2a2437d528837c8420df94332df21881785050efca021fe90110bfa92877d500c77e85207b484219f2a0217f524c2f4a118cf15110fa10e21bd4310ef8a7905e54231bf290217f5050afca8907e48110beaa0637d5010afaa890df54443fd284633e54883ea8220df94040bea9063f9508c6f8a0995f94321dfa1c83f9500867ea8885f94a41bfa9a43ef328cbee6318df94841f719241bc43903f660887d54620be282637f51503f060885f14e10fa20e43df32cc6fca121fd94620f7904417d508c6faa510ddd4542de21281f631442fea090df14543beaa463fb40502fea890df15231fa98e217e508c2fca4106fd0941bea9843f93088378a8884f55010bf284633d54086fca6185fd5130be282877d518caf8a8987b8cb20de210837f53502fca521ef90440fa988637e540c6fca598ef90a41bfaa4417e5410a7ca810fe94021bea9c43f641c437e87a07d8c431faa88817e53c437ea8885f94b40eea9843f741507f681105f54b10bf280217f54483ee8390fb88521bfa94217d5490b7c86214f95320f6990657c540c6f4a0195fd4d41bf290877e510c3eaa321dfd4532dfa18877d50d0efca8196f55320fba8a657e544cafaa7a0efd5121bf29885bd41502f8a6105f55241de214837e5010bba6498f78c932bea90617f540437aa9105f94b30be2a065df320cafea6087ec8220fd88221ee4210bf281084f55331dea12837d52d0efaa3105f94620f790843fb504cafaa3a1df54232fc880217d54c83de64997ed4143bfaa6217e51042f8a990dfd5020f699241bf40103ee4310df94e20be29a217e52103f2a0195d54440fa20
  | 2 => 0x3dc0713016008b003c09050770381a0b45000c0c0c0090400b03c1d204160000100807064060ec000081307443034ee06c6f004021501202c02000261b01b020022dc020041d0180b01c00160000dc0401041005011942d07c0600c0203c480100007051000230000100c770cc020a00000000000000bc020342b004b50059309c020000001406018410ec000002a0640200004178336d80a02483024000100000d8d000020000105c036b0000e95211c0110c0216400000020f4010f0020000305400000330080006c01238010082302055020470fc2f6f00f024340a0340f022024140000200c010087903816004000a9331141609000004100c0ce098000044501c061b80f01c020091c07c0603c030282000c1301c010640012417bfa9021fa20442fca5a1df54a10bf28e417e51d02f8a8885f54730be2a4437d510c2f8a4885f54332bf28063bd43d02fca9104f55030dfa16837e54086fca890dfd5110beaa2637e5310efea9995f54810bf28c657f544cafca4885f54c42bea8e85f521086fca720de54032bf28e657e528c2fca221f78c130beaa265ed4210af8a4a0efd0d40bea9c217c54842f8a8905f15230f7a14857e53102faa8085f55332fd88421f631c42fca4195d54620bca80437d50886fea610df94432beaa4617
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x640442796094b43ae592204433a5454231ce551508c63e64150109798c530863e6414c208f992530c67a60152219e583548ca7761551209e983540ca3c64540319e58354c867561d50328f992534863d6414b108fd95421025f654c0308f592510c63e64150219d98754cc276658c5219d98454043365494432d5185530863c6454b30ce551100423e65d05409e980540c66e6214c208f592530c73543145429d18552cc3724154041ad993318c63d65904409798c52c427a658c120cdd0e5190f2d54548308f994544863e64d4810cd552518823e64d4f2097d95320cab96010440ce50550106786550110cd553410873454145328f990540c27a60148109e98252d06b66190d439e98251ccb7251540329d984530863c6454f21ce952508c73843942428f994425023e64942328f990530863d64d4f208fd91518c26c6254d109798f54086f16010721ad9864390ab96488210da54b400c3344354440ad59231442746154843cd15021442f161100309d195314425d6594c219b988540c67661d4e20ae191304835553104219ed95100423e6495130d554f310867661d50308f590538427a60d4c109d58453c823e64951328f59250082b86050c419e59730082b46150a40ae18143906f260085109d185534823e65151308f99251cc33954840108f99353c42b664cc721ad18542506b5648c7109ed9540102ba6090b40cd547401037351141328f19152c423e6510d419d58454082746155120b558c214423d6494910cd552510c2f160105319d584530827561152209d986544ca7a60d53219d9875204334548c5109798c5408755530c4219e18153d076860548308f990524c63e6414810bc584408826d62d5210ae993208827a60d5021ad986439026f6548421c7552530867661152309d9865090a7b6054f419e583538863e64d4e20cd551518827661150209e980540cb2d54948308f99053c863e6414e108f990514823e6414d209d584548c2f2608c510ced50504cab461508408f993530867a6095132bc58440cc23f6454420ae1814350a766114c20dc9805150a7865481109798f54c426e62d5210ce15120442746154b40ba588300823e64951108f994544427561d53329ed81544c6776155132cd152414423e6414c10ad993314c6d563087109e98053c865f6550c439d5865090a3f65504418f596540423f65500409e18153486b86050d408f99250c867761551219d594410863f6454f219e997404833a4394242cd153214427461551328f59251cc23c6454c20cd952518833954940219ed95300c25d63150209d997414c6b46448421dc546500ca7960d50218f191510827a60152318f19153843355454430ae191300c33754d45328f19153482766194232ba18132c823c6454332ae590304427661150309d594310873554d0631
  | 1 => 0x71e5494c219e1815310ae9620c110d694e50086796014f21cd15231486766114d208f993538863e6494e21ae982421073461550218f191508877161141438f592534867b60551309d587548833860550309758c540863d64942328f590530872e54948309d58653d0a3d6494f10da8c9500ca6e62d50309d98754cca3f6454b30ce952500863c64548319d9845050f3743145429ed81544ca3c64546308f59053c823d65950308f592520827a6014c21ce181548833551104408f59353042766115032cd54641102f2610c1108f990504c63d64d4e218fd9152c423d64d4a109e98353086b46150842ae1814310e756114143cd951518823e64d4a108f992544873854cc110dc982510c37161942429e583530863d64d4c21dc5805150a3d6494732d654e500867661d50329e58053086ba60909429e580540cb705114132c7951530867461552328f9974350b665254430cd153214866d6214e10b518532cc73954942318fd9150cca3e6414f209e98353886796015031ced0d50107695210030cd58454442e9620c2108f596540875553884218fd91500c63d6414931dc545401027561150329d586544ca5f654c431cd951510c33a540c320ce50d50106776154b308fd954310eb86050f409ed8153c863d6494e218f5964310a3f6550842dc9865090a3d64d4e208f99353042766194f409dd85548ca79650c0209e181544ca5c6355120cdd09511033542544409e9825190e7a6015021ced53504cb3854d4132d694d500863c6454632d554d210867a60d52319e582544cb3642145428f590514827960d5231ad590214437260946438f19152443726114143cd151314863f64549109bd95320cb3b42942429e98354082ba60909409758c520433a5454021ae191308827b6054c428f99052c427561d4e209e98252d0f3554944329e980540435732544328f992524427a65cc110dc982518833a54940329e980530825f63549109bd89544c737541453297d8d544833954d00309dd95210877351d4132cd545401023d6590c40ce580544423c6454d109b58853042776154d219bd954210a796094b419d98453c827960145428f99251cca5e6315020bc584404827960152219d195414433a4314143bc580410866e6215030ae580419023d6494a108f992528c33554544329b19532482756194f40ce552500ca3d6414d20ce95330c82b564087109b98853042f261881108fd91534867860551319d1953148769528c0309e58251cca5e63148109d58453483715154032cd951510cb595354021d54c9510ca3e6515132da149204433854881109d58754cc2786054f21bc580418c67565cc421ce15240442b664cc421ced05501063f6454d109d984530433461552318f992534423d64141319e580548c63d64148108f593520426c6255131ec90
  | 2 => 0x2fc0002400060000005d0480002c470141a1140b0e01800007010000a0080000d0280903c72014a9000a60041302004040000500004400178290000300078000080080d000000001e0080100c0304c020000206818024003c80a0205f05806000330000c03c02684080103622c2d064040000200c860001601804004000400401017010bb00003014050041a008020cc1b00000054000e40400c4c00015024000441102c200100202427010052ac2603800578c5000160042100c430100000056034000089e04c0003c342241500406135130140000c4f0340001c1516c04010000dde53840b0240001401000060001001c00000030c8020480701800005530f00d0900204c0f000020001e02809474040801f01b3954540218fd91518cab86050f429d98653d0a776154b409e594400c26d6215031ad986431031d5454c21ad9864310a7a6014542cd90d51103716094643ce553408827761548439d987540c67a60d52329e18154ccb3842540418f5905304278654c1209e58054087655294430ce150504ca3f6550c41dc147504cb693254032cd551100423d6414e20ad18542d067960149319d587540c2776154d209b588540c23d64d4f109dd95310c63e65d09418f590530827a60149318f592528c25d63d5310dc505501063f6454c209e596100435553d0421ce1503044334544c510ae590308427b60553329d584538833954540328f596540cb3a5454032ba58830c823d6494d109d9845388369524c0308f990540ca7b65480209d987548823e65d0d40cb951520c37251940329758f540863e6494a108f99253c423e6494820ad98643d067960d50329758c52c4354534c5109d586508ca6e6214e108f990538827b6054d209bd95200823c6454d21ce153304c23d64943219e5825190e6f6254d10ae993204833554c40109dd95100427b6054d219d584540c23f6454831d994a510c27665c85109718d524433a42540418f59053c876552544308fd9153482766115220dc54640103b141501109dd9541106b66190d41cd153514ca3f64542218f992510c73654944308f992500823f6454e109b58b540c23d6590841ae982429
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0xd000000000003000014200000100000400b4c9c24214542962e130c86a0e146454d210869938c87284858c5856015110962e330484a053170185540861abb0a918a214c5c46055030872ec2a060884b170185425061abb0a810a218a951620c320c28a8b184288439761522044330a92c2200618a151620c110a64e3218a0a1cb1711814350298b80c2aa4638599153cc421a62e2302a9105307050c5150b28a9ac0208438a191524c030
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x831861c14314542831869c64394242831869c64314143831869c24214542
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
  | 4 => 2*((h/221+packedAt s4K4 (20482+(h % 221)*10) 10) % 539)
  | 3 => 2*((h/29+packedAt s4K3 (1225+(h % 29)*5) 5) % 25)
  | 2 => 2*((h/1+packedAt s4K2 (240+(h % 1)*2) 2) % 4)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfc0ff81f8fffc21e3e1ff0fe383fff008e74fc
  | 1 => 0x3ff0ffe00f87ffe03fe1ff0fc03c0ffcf388cf
  | 2 => 0x3ffffffff007ffffc001ffffffc00fff03ff0f
  | 3 => 0xc000fffffff803fffffe000ffffff003fc0ff0
  | 5 => 0xffff0000000003fffffffff000000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x856288c5134126060b12789608a5691886345c
  | 1 => 0x88a69143244aa2601730998a4128aa68b288c5
  | 2 => 0x104022880114008a400122249280449101550a
  | 3 => 0x288441208008930a444000925128022580aa0
  | 5 => 0x230c871c4e6733dd3999ccc0062308c3efe000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfee0fee0fac0fac0fee0fee0fac0fac0fee0fee0fac0fac0fee0fee0fac0fac0fee0fee0fac0fac0fee0fee0fac0fac0fee0fee0fac0fac0fee0fee0fac0fac0, s4N, s4R, (fun _ _ => 0), s4I, []⟩
end PEqualNP.Outside.L_meta_36278
namespace PEqualNP.Outside.L_meta_36278
open PEqualNP.Outside.L_meta_36278.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x3031000400404c000b1ce09e0040801c0543200fc42fe10fc41fc20fd31fd32ff30ff21ff10fc40fc32ff31fe20fc43fc31fc21fe30ff42fd30fe31fc30fd43fe43ff43fe42ff32fd40fe21fd42ff40ff20ff41fd21fe40fe32fe41fc10fd10fd41fd20
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xc817e5010afca3a05f54a40fd882217651103eaa321df54e30bf296217d528c2fca018df55132bb28865bd540cafea9987d10721f6996417f544c3ba86985f54b31bf288617d52442faa8904f95032be296217c50506fea7885f94630eea1887fa30482f8a2a15d94643de2a2217e50082faa988774c832be292217e51886fca7a05f15032be29421f6310c7f680a06f50d40bfa9a81bf4350af8a910df15321bf288653c54443bc60985f54840f6900417e51d0efaa7a17d50710be29c417e5410efaa6887dc4010dfa1c87dd310c6fca321df94e21bf2a0217f54087e86390df54630bfa8a87df4350efea4a1df94443af298437a500cbee6298df94241bf298877e518cb7a8220df94f42dea16837d51d0efaa7a0774c931dea18837e50902fca2205f55240f6a10857c53502fca820fb88720df2028176518837a84205f94341df21a87bd43d02f8a6a0df54740bea8e857e54c82fca9985f94820fba0843f631886faa7215f54e41bf298816d520c2faa5a07bcc821fb20a217d53486fca998df94a41dfa14857e53d06fca421df55320be28285f631c427ea8985fd4f20dea1c83ed320cafaa010fe88210df2a663be415067ca810df55221bf29e21f651883ee43886fd0c43bf2a4417c548c6dca5085f94620bf2a6657e50ccafca598de94021bf28c837f53086fca021df54332ef298437c50486fea4887b90b20bea9c817e50106fca8205f55332bf28c817e51106faa418fb0ca21f719641f9300c2fea6a0df94b40fc90041f721887ea6290efd0240bf290817d53843bc87987b88120be2a441bc41903e88210fe44010beaa2637c54c437ea8987b08520df21c817c53c43eca2205fd4d20bfaa441f920442fca318df95120fa98a217d53102faa7a0df94d21be282877f548c7bc8621f78c932bea80877e53842f8a9995f94732bf284857e52902fca5195f55021ef990657f5050afea9906f90640fd98261bd43d0b7e84a0ef95021fa18843fa50086f8a9195f94e41dfa0c837d538cafea9197d94643bf298856f524c6f8a4085fd4143de218817f548c2faa01977cc931bea9843f610442fea5884f55320bf29821f9500cafca8105f94421b6292637d52042fca1a1df54242fb288657f50486fca420df54c209f2a6417d508c6faa5987bc8421fc982417d538c6faa620cf95331dfa0883f8400c2fea998f7cc431beaa421fa30882f8a4a0df95321fba0c83bf43502bca6205f94a43bf288217e5410bdc64195fd4d42baa88817e51082fea2996f95032fba8a85bd40103de64995f94742bf29e417f540c7f081987b50b20bea88417d51902fea0995fd4e10ee99663f6411077aa8185f55220beaa261ed52843e843887b48421beaa065bf42902fca0085f54a10f7994437d54442fea6885f94830bba8a657d52906faa3217e94032
  | 1 => 0xd5010bf080905f14c10fb98c63bd540867aa8195f15331bea90877e500877c84a17ec8120dfa10857e52cc2fca5a1fe94242be28a656d52102fca6107d44010fda0661df328cbf621085f54c42dfa18837c540c2fca4195f15130f790041ed32482eaa2196f55320bf284617e54443f2a1215f54e20beaa661bf43d02faa6907d50510bea88857c51482fca7205f14d20fa20a637d51103dca4185f94c32ef18a637c53086f8a690f7cc030fd10041f6510c37ca9907bd0942be29e417e5190bbe61185f15320dfa1c837d53c83f680905dd4542de208817e530c2fea2985f54221fd20081be431037c82207e88110bea8865de434c3de41105f94c31dea1a857d548cbf6a0a1efd0040fb18a437e544cabaa6207b88520fa988637f54886fca9885f94442fb90a437d54906baa610dfd4c20bf280617f51503ec83885f14540bfaa2217e520c6fea5085f55243bfaa0617f525037a84a0fbcca32bea86857e50842fca818fd8c510bfaa6217d50906faa5105f14530baa8c877d520c2fea2a15f55030dfa16837d5090efea710df95030bf29c417d5490bbe8721dfd5120beaa643dd43cc2faa890fe4c220bfaa643df32cc678a8985f54041be29e437c5150ff0a0a1fed0240fb90a217f504c6f8a8105f95121be2a0217c53887dca5086fd0f42be29c217c504c7d843905f54643bf294217f54043bca6205b94840bea8c657e5390afca610dfd4f21bea8e617e53107daa4206f55331beaa663f551102fea8197b90920bf29e43ee324837a85207bc8621fa28a857c52502fca1197dcc421bf29a217e54842fca1a17d4c710bf28863ed520c2fca0205f94821bfaa665ef524c6fca918df54b41dfa10817e51c83ee82a0df54720de2a2617d53042eaa3106fd5110fa98c43fa10042fca518f754c40bf2a2637d540c6f8a9085fd4931bea9e43f920842fea2907b14931bf2a4437c54086eaa2184fd5110bfaa0417e540caf2a010dfd4141eea98437c524c6fca5215f94220fb88421ee21487ba60185f55230bea8c417d528c6fea8995f54a219eaa0617f54842f8a4a1ef50842dea18873e540c2f8a890df54031be2a2417f544c6f8a8887e10220bfaa243fb20882f8a0995f14d10faa08837e50cc6fca9185f94231ba28a857e50886faa3995f15330beaa021fa300c3ee8318fb0c821bf286437d51842f8a6105f54841be29a85f521086faa1a0dfd4d21bd28485f551883be6318db54a10bea88877e548cbdca4207d14532f7210857d53c42fca8985b94830bf29c8776510c2fca4085f54b43faa8865f741c87f280205f54232bea8861f421442fca5185f15031fba8a65f950086fea4085f15230bda8287ed42483f661185e54032bea9621fb40882fea4a0df94b41be292617e54086f0a0a1fd10631bca84857d50d0efaa710cf55331de21
  | 2 => 0x4110001701c1b0981e010000000d00800000040440012009000040000401809000011b4120001201c23010000302f018140000105843158050006a00c0239805008060143300160000070200300c000040500000000000d412014030f0000082b0000736c000000100000010300140404801004100000a02c310002a07c0c0100e0041d050300040401c1504800060cc000010002301d2b0c002000ba028000041d018000f000000000180600802000050300111c00000000200700001004120000d0000004800004000200c078000980906c0000c1d0480b01837004000841101c0c0042d010060ac210200f0100501c0e17c01024010040500c0000c001200c00000008192100413c0100c11354060300e03c0504c0906c160300400004000090301d008050141a0000e0953923c0c0000205800000010a414018b20001222000010080140601c040500002c4b01c0001425070000001500c000803d024000100b0002e0080001c05000000085c000120101d0042b00029058030001701c08bea8663f621086fca3985fd4c10ba28a657e5090efea4987ed0030f7a14857e500cafca4885f55231beaa0417d5290efea7106f95030be2a2657c544c7eaa2187dd05319eaa0437d50c86fca4215f94d20fb98e437
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xc548826d6214c109798c54086766194242ce551500863c64549108f99353c82746550510da549300c27860551328fd9153442b86050e419ed8154ccab664cc421d954a510c27461552329d586508ca776548421cb951520c27b65480208f191534426f6548020b918931c431d5350840b9185424823f6454630b558c214433551904409798c52c425d63d5310ea508404834d53cc8219b98a544c67661d53309e181544c73a4314143b658c408823e6414f219e580540ca3e6494e219d984540cacd6308520ce55250086766114c209e983548c6f261881109bd89534423f64540319b9885050e6e6294241cd584544425e63152109d987538827b65440109758c540427a65d0120c7551300c3365454430d3189530867b60551328f191500c76a6014931cdd0e5190eb66190d4397d954310e7960d50219dd855210f55530c421cb952520c33b42942429d98754ccaba64c81209d594410866c65509208f59052042786055332ce551500ca7960d52329dd85544ca7561d53309758c548433654944329759653086776154d209d984538823d6414c218f992520831e5350e41c7551530865f654c4319798c540426d6294241ba98840483355494430d654d50086d86050f30ae181431073454085109d586544ca3d64d4c218f590530423e64d4f10ba580328867661d50319e580530863f64542219b58a508c7716194242d5185530867561d50329718d544826e6214c109b58b540c27761551209d18552d027461551329bd95320cb555388421d994a510c36651c82208f59253886796014f21ce153304c36452d0531c79515308769528c030ad99331c863e64150309e980540ca3d6494d219718d524433554544309d984540825d63150219bd89534867561d5220da548400c27b6055130cb551520c36552544309b988540835953940219d9845050e7561141438f994544c3553254432cd951510cb3461550219d584548c2ea60909208f59052c427561150329758c548823e6414c108f990540cab664cc531c754c43102766194f42da9885050e3e6414b109758e54486b564087109d58653d0ab960104409798c53086e9600c8219b988540c6e5610ca219d98653d02766114f209b189534433454905109dd8552d026d6214e109d185534835553484219e98354082766114c108f99053083586054c40b598f414c75553cc421ad18542d073a54540329b988540c36932540328f596431026d62150108f99052042d963101208f592524433554944328f59053c833743145429d987540c25e63148109e983540876a60948408f590534825f654c0308f99353087645210531d9549511027b60551319e580540871d53d0040ce952500ca7661d5032c754d401032d5494830cd153214434e53548409e98252d0e6c654c92097195434c3665254430
  | 1 => 0xca6c6255131dc9845050ed4614cb319d987520435a5354021b9588410866e62940109798f54c423d6494d109d5865090a3d6595030d994951103e0214811097d8d524423f6550c438f590524c674654c510ae1814350a756114d208fd95401037161141439d984530865f654c8329b588540c74c52cc9319b58b538426f6548421ce553400c36561149318f99253442b8644c220b9189314423e6494d21c7952530866e6214c20cd509511036652944409bd8951cc27761551218fd9150cca3e6494c31dc945500ca6f65508429d98453482796094b438f59253c42e4624c4319dd95310c6766115230d694e500879943d0330bc584408835732544329798f5408734548c5108f592520825e6395121dc9865090a6e62d50309e983540cb726094620da982528423c6454630ce552500cb3543145428f592528c2746154b309dd85548cb1d63151309b594320867a6014c21c754c411027a6014f218f990534823c6454332b9185324837251940329d986544cb3554d04218f590538423d6414c209d195314871d5494c218f992528c2756114e20d554d51102d96310330ab59021c8276658c5219b988540436962141439798c540823d64d4f209e59610042786548110d9cc8514caf260085109d587540c27a60d5232cb98a54c835653544409d98754882746154843b918931886756194f409b58b548432d6494a109b988538427a6015021d554e51103365494430c7553300c2ea6008520ce151204427960d4c218f997435037151540329b98854843386055030cb9925284278654c1209b588548c35653944409e980524c675650c4219758c52c42776154b30da580524c6776154d218f191508863f65508429e98053082b86050d40ce951500863e6415021f1ccb310863e6495110dc546500ca756115030ae993208834d53548408f990524c6756114c20e690c40cc27461551209e980520426d62150308f99053c826e6215230cb95142c826e62d5210d914b314c63e6494f109e98252d067960149319d58754ccab86050c43ae191300c23d6414e209758c540827b6550040ad185421034e5394840d554f410876a3254032cb94942102ad64085209e58252d06b8644c120ae9824250ab56408510b918542c827960d50329758c520426d62951319d984540436652c42109e98354c875553104219e580540c67661150308f19153482b46150a40b358c21c827a60d4c21b918931486b66190c408f99454442b86050f409bd89544c63e6414e20bc584404833a54940218f592528426d62152108f992524427665d05319b58a500432e64149318f992544c23f655044197d8d544823f6454d208f990530863d65950219e594400c27565cc4219b98a508c63e6494a10ad98643903c7324c621d354e521023d64d4f109e583548c71c5490d309798
  | 2 => 0x80300c0100054082f0100c0049018fc0067030048a022c870143b07800080306800060710800a8080200006070a8012600028031400b80307a00098a41430010100002028082c19048199c11008240203040600200720180a000301c000b098000e570080000010181d620a003740001000282a00015400016000080063010080c01006640209009b0003200808000000001281601af44c01002c147080700c0c087f0356ec20e3d42209068000000018000017e20000400001380a000001002000b8a4020000000ba070c0a404000481c274c0284424080000412006e0342ce70a0080421000131d53d0840ad993318c67661152209e980540c65d63d5021ae18143d0a776550441ce152204426c62547309d986508cae662841109d584548827b654c0309798c540c26e62d4e10b99862048354534c510c754e411023d6414f218fd91524436552944409b5885050e7561150209d58453c823e6414e10b9185320ca7561d4e209d997214436a5248210b918532c82776544010cdd09511023d6494c31cd15131442d56308710cb590524c63d6595032c714d4350b6952d0030c754e431027960d5321cd551510
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x440c020284608c18554e6190c40ac0e2992a0196145458c2144314322a498061525c06254c2186aec2a0428861a531814390750a12c2202414c9c64314143c2aa630a84205307050c5150b22b2e6598843265da4310330e40a810a40886195358041102a4b90c0a98818a5916014931b40e2a1080906266414b314c6e0b9842902219154d6210421c2cc8a9e6210da174085204430c298c0a1a859198c52d0531cc2c4b08a0a1e89635084048322298c498a2189150624c510
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0xd00545cc2148110c81631c54210120921871502148110
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 632
  | 4 => 473
  | 3 => 29
  | 2 => 3
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
  | 5 => 2*((h/308+packedAt s5K5 (17064+(h % 308)*10) 10) % 632)
  | 4 => 2*((h/206+packedAt s5K4 (17974+(h % 206)*9) 9) % 473)
  | 3 => 2*((h/16+packedAt s5K3 (1421+(h % 16)*5) 5) % 29)
  | 2 => 2*((h/1+packedAt s5K2 (180+(h % 1)*2) 2) % 3)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfe0ffff03e3ff80e3c7f1fffc707ff0013f4fc
  | 1 => 0x1ff0f8ffc03c7ff03f8fe381f80707fcecc8cf
  | 2 => 0x1fff00ffffc07fffc00ffc01fff807ff0f0f0f
  | 3 => 0xe00000ffffff80fffff00001fffff803f00ff0
  | 4 => 0xffffff00000000fffffffffe00000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xc2621011844801020413048cc111311801545c
  | 1 => 0x44a621228c90b0301c8521154822526864c8c5
  | 2 => 0x8840524510094046400a4828925024910b050a
  | 3 => 0x188a48828201298a920004124a4c022b00aa0
  | 4 => 0x110cc00e313264ed324c927000c080c3dea000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeeafac0feeafac0feeafac0feeafac0feeafac0feeafac0feeafac0feeafac0feeafac0feeafac0feeafac0feeafac0feeafac0feeafac0feeafac0feeafac0, s5N, s5R, (fun _ _ => 0), s5I, []⟩
end PEqualNP.Outside.L_meta_36278
namespace PEqualNP.Outside.L_meta_36278
open PEqualNP.Outside.L_meta_36278.Model
def q2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def q2K4 : Nat → Nat
  | 0 => 0x61000009000200000ed21f910fa40bd40b940f940df31bd41bf41bf40dd31fa10ef21
  | _ => 0
def q2K3 : Nat → Nat
  | 0 => 0x890008090b3262a0714c521cd98a813950d072a8298ce551109caa421a9215034a8290f44c510d590a813954903c242884ed4540
  | _ => 0
def q2K2 : Nat → Nat
  | 0 => 0x7215448510e04c52150311544c510
  | _ => 0
def q2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 13
  | 3 => 14
  | 2 => 3
  | _ => 0
def q2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt q2K5 (i*5) 5
  | 4 => packedAt q2K4 (i*16) 16
  | 3 => packedAt q2K3 (i*27) 27
  | 2 => packedAt q2K2 (i*38) 38
  | _ => 0
def q2I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt q2K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/18+packedAt q2K4 (208+(h % 18)*4) 4) % 13)
  | 3 => 2*((h/11+packedAt q2K3 (378+(h % 11)*4) 4) % 14)
  | 2 => 2*((h/8+packedAt q2K2 (114+(h % 8)*2) 2) % 3)
  | _ => 0
def q2Pos : Nat → Bits
  | 0 => 0xbca67cb68f393923b31e3e89c9cc3b7bc2486e
  | 2 => 0xff3bbf3ff03e3e3fc3e7cf0e0e0fc39cfc0c93
  | 3 => 0xffc3cfc7ffc03fc3fc07f0f00ff0fc1f00731c
  | 4 => 0xfffc0ff8ffffc003fff800fff000ffe00383e0
  | 5 => 0x3ffff000fffffffc000000ffffff000003fc00
  | _ => 0
def q2Neg : Nat → Bits
  | 0 => 0x46488949818c4c44a62441886866094a864826
  | 2 => 0x0
  | 3 => 0x8141010120090090048021002805010081118
  | 4 => 0x1001600224100092000094228000a2001082c0
  | 5 => 0xe2000aedc8a424002a9529cd2d2a0042a36c00
  | _ => 0
def q2Atlas : Atlas := ⟨5,rawDecor 61 q2Pos q2Neg, 0xfffffff0fffafaf0fffffff0fffafaf0fffffff0fffafaf0fffffff0fffafaf0fffffff0fffafaf0fffffff0fffafaf0fffffff0fffafaf0fffffff0fffafaf0, q2N, q2R, (fun _ _ => 0), q2I, []⟩
end PEqualNP.Outside.L_meta_36278
namespace PEqualNP.Outside.L_meta_36278
open PEqualNP.Outside.L_meta_36278.Model
def q6K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def q6K4 : Nat → Nat
  | 0 => 0x20205550601f710bf40bf43bc41df30dd30bd40ef20ed20be41bd42bf42bd43f510
  | _ => 0
def q6K3 : Nat → Nat
  | 0 => 0x183f24c1208ea98831d53d0ba260884b548419ca8083b140443c240884b54b43
  | _ => 0
def q6N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 14
  | 3 => 9
  | _ => 0
def q6R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt q6K5 (i*5) 5
  | 4 => packedAt q6K4 (i*16) 16
  | 3 => packedAt q6K3 (i*27) 27
  | _ => 0
def q6I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt q6K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/11+packedAt q6K4 (224+(h % 11)*4) 4) % 14)
  | 3 => 2*((h/3+packedAt q6K3 (243+(h % 3)*4) 4) % 9)
  | _ => 0
def q6Pos : Nat → Bits
  | 0 => 0xfdeef8773e7cfc733e7f988e3c718cf3f8a427
  | 1 => 0x7e777f87cf9f1f83c78e60f3cf8e0f3c8158da
  | 2 => 0x9f879ff80fe01ffc07f07f03f00ff03f06631c
  | 3 => 0x1ff81ffff0001ffff8007ffc000fffc00783e0
  | 5 => 0xe0001fffffffe00000007ffffff0000007fc00
  | _ => 0
def q6Neg : Nat → Bits
  | 0 => 0x0
  | 1 => 0x8080008102002404081000104402041008084a
  | 2 => 0x28382910a40949205402a9029124a02a126114
  | 3 => 0x5003d2220152924200a552a402494a802582a0
  | 5 => 0x1b5dfc44a958036aa549fccb2b60628a47f400
  | _ => 0
def q6Atlas : Atlas := ⟨5,rawDecor 47 q6Pos q6Neg, 0xfeeefeeefeeafeeafeeefeeefeeafeeafeeefeeefeeafeeafeeefeeefeeafeeafeeefeeefeeafeeafeeefeeefeeafeeafeeefeeefeeafeeafeeefeeefeeafeea, q6N, q6R, (fun _ _ => 0), q6I, []⟩
end PEqualNP.Outside.L_meta_36278
namespace PEqualNP.Outside.L_meta_36278
open PEqualNP.Outside.L_meta_36278.Model
def q8K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def q8K4 : Nat → Nat
  | 0 => 0x10002041000bd43bf42bd42fa10f910f510bf43f710f110
  | _ => 0
def q8K3 : Nat → Nat
  | 0 => 0x8010808800004b54b43d82a221b1434436684886cd51108ea9e85b142442e2a3086cd0d10
  | _ => 0
def q8K2 : Nat → Nat
  | 0 => 0xa458c54442a16215110a858b434429163d0910
  | _ => 0
def q8N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 9
  | 3 => 9
  | 2 => 4
  | _ => 0
def q8R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt q8K5 (i*5) 5
  | 4 => packedAt q8K4 (i*16) 16
  | 3 => packedAt q8K3 (i*27) 27
  | 2 => packedAt q8K2 (i*38) 38
  | _ => 0
def q8I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt q8K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/24+packedAt q8K4 (144+(h % 24)*4) 4) % 9)
  | 3 => 2*((h/24+packedAt q8K3 (243+(h % 24)*4) 4) % 9)
  | 2 => 2*((h/8+packedAt q8K2 (152+(h % 8)*2) 2) % 4)
  | _ => 0
def q8Pos : Nat → Bits
  | 0 => 0x3de3f8fc7f0f18f8e631f1f87c71c7e38b3273
  | 1 => 0xc1fc7f1f8ff01f1f183e3e3f8781f8fc15c39c
  | 2 => 0xfe007fe00fffe01fffc03fc007fe00ffe60c1f
  | 3 => 0xffff80000fffffe01fffc00007ffff00780fe0
  | 4 => 0xfffffffff00000001ffffffff80000007ff000
  | _ => 0
def q8Neg : Nat → Bits
  | 0 => 0x4290a40812221010010504914105229011231
  | 1 => 0x40491240122240202012121114809249014294
  | 2 => 0x88122009244402500a4024822124009226040a
  | 3 => 0x108004924888100254a4800442492400580940
  | 4 => 0x2112449800cc94949f292926600c24127ea000
  | _ => 0
def q8Atlas : Atlas := ⟨5,rawDecor 31 q8Pos q8Neg, 0xfeeefee0feeefee0feeefee0feeefee0feeefee0feeefee0feeefee0feeefee0feeefee0feeefee0feeefee0feeefee0feeefee0feeefee0feeefee0feeefee0, q8N, q8R, (fun _ _ => 0), q8I, []⟩
end PEqualNP.Outside.L_meta_36278
namespace PEqualNP.Outside.L_meta_36278
open PEqualNP.Outside.L_meta_36278.Model
def q9K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q9K3 : Nat → Nat
  | 0 => 0x8010037905d30ea21b482f987710
  | _ => 0
def q9K2 : Nat → Nat
  | 0 => 0x324c120d130443848110
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
  | 2 => 2*((h/1+packedAt q9K2 (78+(h % 1)*2) 2) % 3)
  | _ => 0
def q9Pos : Nat → Bits
  | 2 => 0xfffffffffffffffffffffffffffeaef1b77c27
  | 3 => 0xbf333e3ba0da
  | 4 => 0xdfc3cfc3c31c
  | 5 => 0xeffc0ffc03e0
  | _ => 0
def q9Neg : Nat → Bits
  | 2 => 0x0
  | 3 => 0x42444211044a
  | 4 => 0x241814820914
  | 5 => 0x1801a92012a0
  | _ => 0
def q9Atlas : Atlas := ⟨4,rawDecor 60 q9Pos q9Neg, 0xfffffff0fff0f0f0fffffff0fff0f0f0fffffff0fff0f0f0fffffff0fff0f0f0fffffff0fff0f0f0fffffff0fff0f0f0fffffff0fff0f0f0fffffff0fff0f0f0, q9N, q9R, (fun _ _ => 0), q9I, []⟩
end PEqualNP.Outside.L_meta_36278
namespace PEqualNP.Outside.L_meta_36278
open PEqualNP.Outside.L_meta_36278.Model
def q10K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q10K3 : Nat → Nat
  | 0 => 0x101037107410bc61b082e187610
  | _ => 0
def q10K2 : Nat → Nat
  | 0 => 0x320c020e02004340c010
  | _ => 0
def q10N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
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
  | 2 => 2*((h/8+packedAt q10K2 (78+(h % 8)*2) 2) % 3)
  | _ => 0
def q10Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 3 => 0xffffffffffffffffffffffffffbf0fffc3fe3f
  | 4 => 0xffffffffffffffffffffffffffdff0fffc3fc7
  | 5 => 0xefff0fffc3f8
  | _ => 0
def q10Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffff012222c444db
  | 3 => 0xffffffffffffffffffffffffff42e44562aa2d
  | 4 => 0x244e89aa3346
  | 5 => 0x1888ee3323b0
  | _ => 0
def q10Atlas : Atlas := ⟨4,rawDecor 58 q10Pos q10Neg, 0xcccccc00cc000000cccccc00cc000000cccccc00cc000000cccccc00cc000000cccccc00cc000000cccccc00cc000000cccccc00cc000000cccccc00cc000000, q10N, q10R, (fun _ _ => 0), q10I, []⟩
end PEqualNP.Outside.L_meta_36278
namespace PEqualNP.Outside.L_meta_36278
open PEqualNP.Outside.L_meta_36278.Model
def q11K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q11K3 : Nat → Nat
  | 0 => 0xc000102e195e30b86178cae98df31
  | _ => 0
def q11K2 : Nat → Nat
  | 0 => 0x3089a408ca31093198404c6390a30
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
  | 1 => 0xffffffffffffffffffffffddf1ff3f1ff0f3f3
  | 2 => 0xffffffffffffffffffffffeffe7fffe3fffc7f
  | 3 => 0x76ff8fcffc7f0f9c
  | 5 => 0x78fff00fff800fe0
  | _ => 0
def q11Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffa21c2243049261b1
  | 2 => 0x1021040421248446
  | 3 => 0x9446819484a2a98
  | 5 => 0x7894eae920ccf60
  | _ => 0
def q11Atlas : Atlas := ⟨4,rawDecor 46 q11Pos q11Neg, 0xfcc0fcc0f0c0f0c0fcc0fcc0f0c0f0c0fcc0fcc0f0c0f0c0fcc0fcc0f0c0f0c0fcc0fcc0f0c0f0c0fcc0fcc0f0c0f0c0fcc0fcc0f0c0f0c0fcc0fcc0f0c0f0c0, q11N, q11R, (fun _ _ => 0), q11I, []⟩
end PEqualNP.Outside.L_meta_36278
namespace PEqualNP.Outside.L_meta_36278
open PEqualNP.Outside.L_meta_36278.Model
def q12K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q12K3 : Nat → Nat
  | 0 => 0x21b02e995c30be637ccae98de30
  | _ => 0
def q12K2 : Nat → Nat
  | 0 => 0x4009541cca5504308d420c2350b31
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
  | 1 => 0xffffffffffffffffffffffdff7fcfc7ff8f3cf
  | 2 => 0xffffffffffffffffffffffedf99f3f8e3f3d33
  | 3 => 0x76fe1fcff03fce3c
  | 5 => 0x78ffe00fffc00fc0
  | _ => 0
def q12Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffa010010012080045
  | 2 => 0x1224284484922512
  | 3 => 0x941501921248a28
  | 5 => 0x7851aae4986af80
  | _ => 0
def q12Atlas : Atlas := ⟨4,rawDecor 46 q12Pos q12Neg, 0xfcccfcccfcc0fcc0fcccfcccfcc0fcc0fcccfcccfcc0fcc0fcccfcccfcc0fcc0fcccfcccfcc0fcc0fcccfcccfcc0fcc0fcccfcccfcc0fcc0fcccfcccfcc0fcc0, q12N, q12R, (fun _ _ => 0), q12I, []⟩
end PEqualNP.Outside.L_meta_36278
namespace PEqualNP.Outside.L_meta_36278
open PEqualNP.Outside.L_meta_36278.Model
def q13K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q13K3 : Nat → Nat
  | 0 => 0x2f185c30ba6378cae195f31
  | _ => 0
def q13K2 : Nat → Nat
  | 0 => 0x8e428c26101318c424c6690232
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
  | 1 => 0xffffffffffffffffffffffddf1ff3f1ff0f3f3
  | 2 => 0xffffffffffffffffffffffeffe7fffe3fffc7f
  | 3 => 0x76ff8fcffc7f0f9c
  | 4 => 0x78fff00fff800fe0
  | _ => 0
def q13Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffa21c2243049261b1
  | 2 => 0x1021040421248446
  | 3 => 0x9446819484a2a98
  | 4 => 0x7894eae920ccf60
  | _ => 0
def q13Atlas : Atlas := ⟨4,rawDecor 30 q13Pos q13Neg, 0xfcc0f0c0fcc0f0c0fcc0f0c0fcc0f0c0fcc0f0c0fcc0f0c0fcc0f0c0fcc0f0c0fcc0f0c0fcc0f0c0fcc0f0c0fcc0f0c0fcc0f0c0fcc0f0c0fcc0f0c0fcc0f0c0, q13N, q13R, (fun _ _ => 0), q13I, []⟩
end PEqualNP.Outside.L_meta_36278
namespace PEqualNP.Outside.L_meta_36278
open PEqualNP.Outside.L_meta_36278.Model
def q14K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q14K3 : Nat → Nat
  | 0 => 0x108000002f98dd32ba637ccaf185c30
  | _ => 0
def q14K2 : Nat → Nat
  | 0 => 0x95410c25507328d420c2350b31
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
  | 2 => 2*((h/1+packedAt q14K2 (104+(h % 1)*2) 2) % 4)
  | _ => 0
def q14Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffdff7fcfc7ff8f3cf
  | 2 => 0xffffffffffffffffffffffedf99f3f8e3f3d33
  | 3 => 0x76fe1fcff03fce3c
  | 4 => 0x78ffe00fffc00fc0
  | _ => 0
def q14Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffa010010012080045
  | 2 => 0x1224284484922512
  | 3 => 0x941501921248a28
  | 4 => 0x7851aae4986af80
  | _ => 0
def q14Atlas : Atlas := ⟨4,rawDecor 30 q14Pos q14Neg, 0xfcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0, q14N, q14R, (fun _ _ => 0), q14I, []⟩
end PEqualNP.Outside.L_meta_36278
namespace PEqualNP.Outside.L_meta_36278
open PEqualNP.Outside.L_meta_36278.Model
def q15K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q15K3 : Nat → Nat
  | 0 => 0xc0008000005d30f461e4c2c985f30
  | _ => 0
def q15K2 : Nat → Nat
  | 0 => 0x2650e30
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
  | 0 => 0xfffffffffffffffffffffffbbc933e39cef90f
  | 3 => 0xfffffffffffffffffffffffdff1fcfc1ff31f3
  | 4 => 0xeffe3f3fe0fce3c
  | 5 => 0xf3ffc03fff00fc0
  | _ => 0
def q15Neg : Nat → Bits
  | 0 => 0xfffffffffffffffffffffff44626420c62a905
  | 3 => 0x208401040840052
  | 4 => 0x110080490080228
  | 5 => 0xe202ab2520ad80
  | _ => 0
def q15Atlas : Atlas := ⟨4,rawDecor 57 q15Pos q15Neg, 0xffffff00ffaaaa00ffffff00ffaaaa00ffffff00ffaaaa00ffffff00ffaaaa00ffffff00ffaaaa00ffffff00ffaaaa00ffffff00ffaaaa00ffffff00ffaaaa00, q15N, q15R, (fun _ _ => 0), q15I, []⟩
end PEqualNP.Outside.L_meta_36278
namespace PEqualNP.Outside.L_meta_36278
open PEqualNP.Outside.L_meta_36278.Model
def q16K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q16K3 : Nat → Nat
  | 0 => 0x10188af18dc31bc6170c2f995d32
  | _ => 0
def q16K2 : Nat → Nat
  | 0 => 0x9a408c661013294414ca590630
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
  | 2 => 0x6efe3fcfe3ff0cfc
  | 3 => 0xfffffffffffffffffffffff7ffcffffc7fff1f
  | 5 => 0x78fff00fff800fe0
  | _ => 0
def q16Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa21c824304926171
  | 2 => 0x11258415212624b4
  | 3 => 0x840280848488a0a
  | 5 => 0x7892eae920ccfc0
  | _ => 0
def q16Atlas : Atlas := ⟨4,rawDecor 45 q16Pos q16Neg, 0xfaa0faa0fa00fa00faa0faa0fa00fa00faa0faa0fa00fa00faa0faa0fa00fa00faa0faa0fa00fa00faa0faa0fa00fa00faa0faa0fa00fa00faa0faa0fa00fa00, q16N, q16R, (fun _ _ => 0), q16I, []⟩
end PEqualNP.Outside.L_meta_36278
namespace PEqualNP.Outside.L_meta_36278
open PEqualNP.Outside.L_meta_36278.Model
def q17K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q17N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q17R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q17K3 (i*4) 4
  | _ => 0
def q17I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q17K3 (4+(h % 1)*1) 1) % 1)
  | _ => 0
def q17Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffbfcffcf8fff873f3
  | 2 => 0xdbf19f3f1c3f8d9c
  | 3 => 0xffffffffffffffffffffffeffe1fffe03ffe1f
  | 4 => 0xf3ffe03fffc00fe0
  | _ => 0
def q17Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff40640108248920b1
  | 2 => 0x24ac285909932594
  | 3 => 0x1101502242244a0a
  | 4 => 0xe091ab493064f40
  | _ => 0
def q17Atlas : Atlas := ⟨3,rawDecor 29 q17Pos q17Neg, 0xfaaafa00faaafa00faaafa00faaafa00faaafa00faaafa00faaafa00faaafa00faaafa00faaafa00faaafa00faaafa00faaafa00faaafa00faaafa00faaafa00, q17N, q17R, (fun _ _ => 0), q17I, []⟩
end PEqualNP.Outside.L_meta_36278
namespace PEqualNP.Outside.L_meta_36278
open PEqualNP.Outside.L_meta_36278.Model
def q18K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q18K3 : Nat → Nat
  | 0 => 0x14202e98dd32b8617cc6f185f32
  | _ => 0
def q18K2 : Nat → Nat
  | 0 => 0x219541cca350b3195410c2350830
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
  | 0 => 0xffffffffffffffffffffffdff7fcfc7ff8f3cf
  | 2 => 0xffffffffffffffffffffffedf99f3f8e3f3d33
  | 3 => 0x76fe1fcff03fce3c
  | 4 => 0x78ffe00fffc00fc0
  | _ => 0
def q18Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa010010012080045
  | 2 => 0x1224284484922512
  | 3 => 0x941501921248a28
  | 4 => 0x7851aae4986af80
  | _ => 0
def q18Atlas : Atlas := ⟨4,rawDecor 29 q18Pos q18Neg, 0xfaaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0, q18N, q18R, (fun _ _ => 0), q18I, []⟩
end PEqualNP.Outside.L_meta_36278
namespace PEqualNP.Outside.L_meta_36278
open PEqualNP.Outside.L_meta_36278.Model
def q19K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q19K3 : Nat → Nat
  | 0 => 0x4000012e98fa10f2217cc7790ed21
  | _ => 0
def q19K2 : Nat → Nat
  | 0 => 0x314c521d131443848510
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
  | 3 => 2*((h/9+packedAt q19K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/1+packedAt q19K2 (78+(h % 1)*2) 2) % 3)
  | _ => 0
def q19Pos : Nat → Bits
  | 0 => 0xbea673b7606e
  | 2 => 0xffffffffffffffffffffffffffff3bbc3bbc93
  | 3 => 0xdfc3cfc3c31c
  | 4 => 0xeffc0ffc03e0
  | _ => 0
def q19Neg : Nat → Bits
  | 0 => 0x424880910426
  | 2 => 0x0
  | 3 => 0x241415020918
  | 4 => 0x18016a2012c0
  | _ => 0
def q19Atlas : Atlas := ⟨4,rawDecor 29 q19Pos q19Neg, 0xfffafaf0fffafaf0fffafaf0fffafaf0fffafaf0fffafaf0fffafaf0fffafaf0fffafaf0fffafaf0fffafaf0fffafaf0fffafaf0fffafaf0fffafaf0fffafaf0, q19N, q19R, (fun _ _ => 0), q19I, []⟩
end PEqualNP.Outside.L_meta_36278
namespace PEqualNP.Outside.L_meta_36278
open PEqualNP.Outside.L_meta_36278.Model
def q20K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q20K3 : Nat → Nat
  | 0 => 0x405203b98f431ee43d443a10f710
  | _ => 0
def q20K2 : Nat → Nat
  | 0 => 0x8000a442442990b319643c86510d10
  | _ => 0
def q20N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
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
  | 3 => 2*((h/9+packedAt q20K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q20K2 (104+(h % 8)*2) 2) % 4)
  | _ => 0
def q20Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff3ffff1ffff1ff
  | 1 => 0x6afc39cfe3870ecc
  | 3 => 0xfffffffffffffffffffffff3ffc1fffc07ff0f
  | 4 => 0x7cfffe0ffff80ff0
  | _ => 0
def q20Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa018800104912055
  | 1 => 0x152b9297213266cc
  | 3 => 0xc41350a4844cb0a
  | 4 => 0x38221ac92608da0
  | _ => 0
def q20Atlas : Atlas := ⟨4,rawDecor 27 q20Pos q20Neg, 0xeeaaaa00eeaaaa00eeaaaa00eeaaaa00eeaaaa00eeaaaa00eeaaaa00eeaaaa00eeaaaa00eeaaaa00eeaaaa00eeaaaa00eeaaaa00eeaaaa00eeaaaa00eeaaaa00, q20N, q20R, (fun _ _ => 0), q20I, []⟩
end PEqualNP.Outside.L_meta_36278
namespace PEqualNP.Outside.L_meta_36278
open PEqualNP.Outside.L_meta_36278.Model
def q21K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q21N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q21R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q21K3 (i*4) 4
  | _ => 0
def q21I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q21K3 (4+(h % 1)*1) 1) % 1)
  | _ => 0
def q21Pos : Nat → Bits
  | 0 => 0xafc73f38e3ff04fc
  | 1 => 0xffffffffffffffffffffffcff833ff0387f8cf
  | 2 => 0xfffffffffffffffffffffff7ffc3fffc07ff0f
  | 3 => 0xfbfffc3ffff80ff0
  | _ => 0
def q21Neg : Nat → Bits
  | 0 => 0x5072605828b1645c
  | 1 => 0xffffffffffffffffffffff309686291152a8c5
  | 2 => 0x92028124824450a
  | 3 => 0x60402a492408aa0
  | _ => 0
def q21Atlas : Atlas := ⟨3,rawDecor 15 q21Pos q21Neg, 0xfac0fac0fac0fac0fac0fac0fac0fac0fac0fac0fac0fac0fac0fac0fac0fac0fac0fac0fac0fac0fac0fac0fac0fac0fac0fac0fac0fac0fac0fac0fac0fac0, q21N, q21R, (fun _ _ => 0), q21I, []⟩
end PEqualNP.Outside.L_meta_36278
namespace PEqualNP.Outside.L_meta_36278
open PEqualNP.Outside.L_meta_36278.Model
def q22K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q22K3 : Nat → Nat
  | 0 => 0x400007110f221d443d087710
  | _ => 0
def q22K2 : Nat → Nat
  | 0 => 0x2c50610
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
  | 3 => 2*((h/8+packedAt q22K3 (75+(h % 8)*3) 3) % 5)
  | 2 => 2*((h/1+packedAt q22K2 (26+(h % 1)*1) 1) % 1)
  | _ => 0
def q22Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffafcc9ce3b9f3273
  | 1 => 0xcff0e73c3e7c39c
  | 2 => 0xffffffffffffffffffffffff7ff07ffc07fc1f
  | 3 => 0xfbfff83fff80fe0
  | _ => 0
def q22Neg : Nat → Bits
  | 0 => 0xfffffffffffffffffffffff506921208d1a231
  | 1 => 0x30aa0864152a294
  | 2 => 0x9005009004040a
  | 3 => 0x60002922000940
  | _ => 0
def q22Atlas : Atlas := ⟨4,rawDecor 15 q22Pos q22Neg, 0xfee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0, q22N, q22R, (fun _ _ => 0), q22I, []⟩
end PEqualNP.Outside.L_meta_36278
namespace PEqualNP.Outside.L_meta_36278
open PEqualNP.Outside.L_meta_36278.Model
def q23K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q23K3 : Nat → Nat
  | 0 => 0xc100002e986d20ea21bc82f987710
  | _ => 0
def q23K2 : Nat → Nat
  | 0 => 0x2007848110c93048344c110
  | _ => 0
def q23N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
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
  | 2 => 2*((h/8+packedAt q23K2 (78+(h % 8)*2) 2) % 3)
  | _ => 0
def q23Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffffffeaef1b77c27
  | 1 => 0xbf333e3ba0da
  | 2 => 0xdfc3cfc3c31c
  | 3 => 0xeffc0ffc03e0
  | _ => 0
def q23Neg : Nat → Bits
  | 0 => 0x0
  | 1 => 0x42444211044a
  | 2 => 0x241814820914
  | 3 => 0x1801a92012a0
  | _ => 0
def q23Atlas : Atlas := ⟨4,rawDecor 15 q23Pos q23Neg, 0xfeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeea, q23N, q23R, (fun _ _ => 0), q23I, []⟩
end PEqualNP.Outside.L_meta_36278
namespace PEqualNP.Outside.L_meta_36278
open PEqualNP.Outside.L_meta_36278.Model
def gbK10 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK9 : Nat → Nat
  | 0 => 0x23c00002001512c000318c2042c01ff20007f0c401fe43007f08401fd21007f48001fe32007f4c401fd32007f8c401fd41007f54401ff32007fcc001fc32007f94801ff31007f50c01fd50007f90801fd53007f55001fd30007f88401fe53007f50001fd10007f50801fe51007fc8401ff10007f54801fe41
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x2a6400bfd9421005fcc390003fd21480017eb24640dff1072104ff8a398002ff63544017e30a6000bf59543005fcc321003fe43948017eb1ca400ff54942006facb90003fb20480017eb048205ffd0f20005fac319003f631484017fb128200ff0c9400dffca19902bff4348401ff292601affd0232005fec690803be64084017fb12a200bfd9121007fec8990037d5454801fea924000bf596430aefca1288037d6508401feaa26200ff98e42007faa6a0002ff6150001ff9944200bf59520005fac719003fd4348401fe31a8400ff50f2002ff88390003fe42cc8017eb2664009f59720007dc849002bfc41484017eb286200bf59330005fac610803fd628c401ff21aa400bf59710005fec0a9002fd6590833ffa826419ffd4532005fcc410803fc6348401ff18a6200ff50d52005fac688013ff5148001feb1c8400ff18d54007faa72106ffe10cc819ffa9c4200ff545400e7f88399003ff3250401ff210621bff90332005fac98805ffe304c801bf292a000bfd8d10005feca90047fc208c401f790c421bff10332005f8c488003f55144001ff2146200ff90a51007ee4388003ff614c801be32a4200ff58f20007faa490843ff424c4013eb2e6213ffd0b31007faa999002fd65c8401fb20a2000bfd8d40007faa998802ff644c037ff1066400bf98643005fec4a8003ee42c80017eb144200bf582510c7fe8099002ff644c8017eb006400ff18d10006faa928803ff3294401fe10a6000ff90b30005fac118803fe52508017eb2e4007ff14530005fec919003fd6394801ff2184200bf59632005facb98802fd62cc019ffaa44217ff881320c7fe8299003ee2148401ef9926203ffd0520005facb98003fe21cc0017e312a200ffd9532007fec898837ff40c84017f3166000bf98831005fac899003fd32500016f3184200ff94e42007fcc720803bd4350033ffa9a6400bfd9151005fcc520802ff65c802ffe3026400bf58f20005f2c019002f5610c839fe2a66400ff59130007fca49903fff540c41dff0806200f74c431005fec098802dd6308401fea0e600eff08031007fe42a0002bd640c839ffa166416ffd0832004faca19002ff624c023ff0846200f74c832007fa64a8803fd62904017fb1a8200bf18954007bc6298802fd640c4017eb106213ff95331067fea51082bff4048401ff216201dffd5332005facaa0803ff614c001fb90a2000ff55330005fac598802ff63c40017fb126200bfd9721005fcc52184bff538c401fe9904200ff50931005fac010802fd650c801fb1084200bf59131005fac721002fc6154c01ff29a8208ff15330005facb99037fe64c8421ffa026200bfd9321007fa6298003fd2150001fea106200be58021007fa8729003fe214c001bf292a400ff90721097fea918843fe544c401ff2126000bf58321
  | 1 => 0x3fd420c801ff10a8000bf98a51007faa598003fd424c007ff2a24003ff9912001ff88690003fd4254401ff21aa000df54d500e7fe8399003fe52cc801ff30a4000fd8c710007f8c298053be4090401fb28e2000bfd964209ffe8198802fe6294c01fe9926000f750f30005facb20803fe53c8001bea8aa000ff90f20007fca690802ff658c431ff2a26400bfd8543007fa8788002fc614c801ff21a4000bfd9510007fa8519002ff654c4017fb2a8600ffcc540037fe869805ffe604c81bff2a64200ff50910007f26090003ff6354401fe3128600ff90f21005fac529803fd614c001ffb1a8400bf58332005fec0a0803f52108401fea9a8400ff58e41005fac788002fe61cc8017e3128000fd50510007fc6499003fd64c80017eb086400ffd9130007fc82908027d650841dff1006200bf59320007fa86980037e52944017f3162000ff4c910007fec4aa01bfc414c001fea9a6400ffd8132007f2a088047fe208c401fe9948200ff48530005fac918802fd6550001fea9a4000ff0c5400d7fe8719002bd64c802dfe2086400ff54f2102ffca990003fe4148001fea8a4000bfd9131007fca2a0003fe4348401ff18a8000bf58b10007f2408802bfe5448401fe31aa218ff1053200ffe8688003ff63440017e312861aff10632027f8a690002fd650842ffe2826400fd8c5100077a8720817fc43c8001fea1c6400bf59530007eca28802bfc4348401fea926007ffd4530005f8c588067fc524c811ffa0e6000ff50950005fec0a98037f6548401bea9aa41eef90142007fa8499003fd534842ffe2026400ff50b21005fec588002fd6494c01fea1a2000fdc862100ff88288003fd42480017fb224000ff4c950007faa790003fe52cc0017fb204200df54951007fa8790803fd4354401ffb126000bf59321007fa6490002ff6055001ff20e4000ffcc8210057ec888003f53148401ff90aa00dffd0f210c7f8c8990027f65484017fb0a4000bfd8d42007faca90002fe610c83bfe28e6406ff191300077a86a1002ff63c842fff2026416ffd0032005fec988002fe620c801ef1926400ff18954007fcc298002ff60484017eb2c4200ff54910007fa659082bfc64484017e30aa800ffd9121006fcca10803fd32c8031ffa1a6400bfd8953007fca6a0003f641c40017fb128600ff98a41007de421080fff43480017fb222000f750d3001ff8829006ffc10cc8017eb0e6400bfd9152005fec2a8003fd4354001ffb0a8600ff98f20005fcc488003fe628c401ffb1a4200ff50b20005fac018803fd4248401fe90aa000fb48421005feca90802ff604c801ffb1aa800bfd8143005f8c2a9003fd434c801fe9924200bf58e41037fe8298002fc6154001ff1928000ff98f21007f84398003fd4348001faa8e2000ff54932005fecb2086ffc20cc833ff3
  | 2 => 0x2107ff8a418802ff6054401feaa24000ff90932007fc6528802ff6050805ffa962000bf98a31007f8c2a1803fc3144001eeb184200ff1854200778c888002ff6488401ff18a2000ff9494005ff8a110802fd6444001deaa28400bfd9710006feca88003fd4294401ff10a4000ff50550005fec918877fc52cc801ff98aa01dffd4732007e8438802ffe4088435ffa146400bf58652005fec2a9003ee32c8001feaa26404ff99520005faca99002fe6108401fea166200ff50b32007fa64a0802fd644c001ffb0a8410ff10531007fa8698807ff42440017fb1c4200ff50520007fe6290002ff6454001f6992401bff1433200ff8c88804bfc528c40fffa926000df19510007f2c010803ed42480017eb244200fd8c621007faca98002fc62540017fb2c4200bfd8940027fea690003ff3248001ffb12a600ff98d20007f86588003fd51cc001feb1a4000ff90f10007fe659005ffe104c801fea926200ff59120007be6519002fd6290401fea966200ffccb2109ff88398802ff6550801feaa64217ff08132007fa8518803bd5450c01ee9926200bf18953007fa6518802fd628c413fe2966000fb4cb20077fc801883bfc500c401fe18a4000bf58653007faa599002fd638c4017fb1e4000ff8c520005fac198803fc2150001ff1962000ff94d1008ff8a118803fc31c84017eb204200ff945200c7fcc899002ff6150831fe2a26400fb50b20007faa99000ffc5448001ff18e4200bf596310c7fe8499003fe31c8001fa98e2006ff95130007fca390003ff32484017eb046400bf18542007fa859805bfe540c833ffaa26400ff54941007fac099003f42144001fe98a800dffd0b2101ffe8490002ff6154c01feaa24200bf59542007f62088003fc614c801fea9a8600ff0c521005fac79080bfc53c4001feb046200ff59132007f86390003fe324c009ffa924004ffd5120007f4c010837fc43c8435ff2a46400ff54530007ba6598802fd6090801ffb128600efd9110007fa8718803fd43944017eb04a600ffc873007ffea01881ffc524c005fe2962000ff8c521007faa698003fe3290401ff21a2000ff94d4205ffc6110802ff65500017eb24a201ff95110005feca98003fe414c035ff3246400bfd9153067fea110803fe4354401faa0e2000bf9863208ffc6118803fd42c4001ff29e4205ffd0b20005fec990067ff524c825ffa846201ff10d10007fe64a0002fc6250401ff29a400affd0921005fec610823fc41cc001fe90e6000bf58d20007fa6588063fc424c801fe192a000f790d30007fe4298003fd538c8017f30ca600ff8c950005fac890803ff6444039ffa066400ef590210effea199002fe610c4013fb2a2006ff99130007fac91902ffe20884017eb24a409ffd4730007ea6288003fd53440017eb2a4200ff59321007fc828800
  | 3 => 0x101800220000c4000200b35c3706c5e0002b03000010000080407001000997a000028a67640300001000030440105c0b0101d450070000336c1e8021e016995ec00008000000721416058830d80907c04000004a48e0084803c053000a00826000000004103a1e1082a00001038d2001140000303c000ac674d80305000074470083e0200e0000001025000db004010000200191020080040515c09000090004601800168000f13a9f003000360094503c0800c6b000005a0010140b00c0002009130000082e00002000000880700000000010d400001df060011800612c00120030001e01c3800034026670240c03c210001908c3e11e452384800004038005340002c0300801018000000202c060000000c00000021bc04024960180303001026860240002c032281e7440f00403004d00b42f2f4000182f4440a008000100600ac071000004030b8003b036000006fc00010180042d0d4440701500000000061700300004288200001a0380f08c000005800c0a02c010684e0f41000000150000313e01c3500404005f8c498802ff6348001fea1c4200ff947300effea599003fd4208401fe3126000bf582520e7fca999002fd62944017fb2a8200ff4ca21007fac290003fd5250001ff3184200bfd89540057ac81085ffc104c801ff9962000ff90e210e7f88599002fd65440017fb2c6400f7cc631097fea518803fd534c4017fb1aa008ffd0b30027f8a290002fe61cc033fe28a6400bfd8d54007f8c4a9802ff614c801beaa2a60fffd4831005feca99003fd6308401ef3184200bf58730007f86520803fe41cc001ffb2a6009ffd533003ff8ca98003fe414c401fea0a6000ffcc950005f8c498002fd638840dfe2126017ff94132007fe6520803fd5350405ffaa62019ff19532007fcc498003fe514c023ff3046200bf58221005f8c2a0003fd4308421fe3226200ff55130005fcc329002fd63484017eb1ca202ffd4f10005fac819003fc32944017e30a4000bfd8d520077c82a0802bd64cc401fe994a200ef50941005fac321002ff614c001feaa06400ff98532007fac2990037e65c8001fa98c4200ff5953203ffea89802ffc3088413ffa966000bfd8910007fc6518802fe62cc401df2128400ff98e5203ffcca98017fe64c8001deb264000df55150007ee4290802fc6150c0fffa9a600cff14e21047f88598002ff6155001df3264000ff4c550007fc6298023fe54cc001f71924006ff15130005fac998803fd548c8017eb0e4000ff90e51007fac498002fd6190c01bf28aa200ffcc95108ffc8118803ff32440017eb122000ff90731006faa728803fd3148001fe9926200ff90950007faa888002f6610c801feb1e4200bf58a43037fe8498002fd64480017eb048600bf59531007fa8510843ff434c43fbf282a400bf986
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0xd74cc550006ff63945400d6fe648cb10005f57390710004ff73595410cf7f535513214efc6354910004ff7359120005fd739052024dfc7350950006fd6458132006fc51d8d20004fd7694b30006fd65cc940005fd7550d320077c4319510005f5710c950006bd6498f20005f7714ca31006fd640ca5119fbe4350e21006f631d8121006fc5458d20007dd63ccb1005efd30d89100bff860581320dfed20d89303b77c53d8953005fc71591321bfef414c920006f66148730004fd73d9320006ef6298930125fe73905100067c641952101dbc74585200077d5354932006ff5458031076fa2058031057bc6450d21007f441d853201dbe74cc520006fd6350f20005fc7150b30007bd4350931006fc4358910005ff76545201f7ef3218532005fd7550b32007bd43c854015fef328cb10176fe760c520007ed4248520005ff7055331006fc64d8132006ba6458021006fe54d8d21006fd7058c21006fe5458f210deff32d8930006ff634cb10004f970d9642005fd7690f200277c5154d20006fe7158e42006fe764c9510d6fc41d8d42005fd7394530006fe3058a31087bf4050d31006fd53d81410057f735515001faf4350920117f84354110007f47150d31074fe768c51018dff7648730087bc6450d3118efe7690d21005f47155131006fe20d8e211defe43d81320077d548c950007f77159132007ed434cb20166fc6390950006be6458f20004f97018552177f97098d200d6fe648ca31006fd6350d10006fd644c530006ff4358f20007de4388530005ff7250f21006fe43587200c6fc4158e4215ff7328c710006ff644c5200277f5255120006ff6354d10246fc31d9130007ed548c920005fd7290f10007ae644cb20157bd6455332187fb534c120005fe7688530006fc43d8121006bd64ccb20006ff65d9132005fd7694520057bf4348540004fd7218553007ee32905201fefc43d85320bef86058132137fb3090530157fb3055130007f4714c910317be40cca41006fc7650f21006ff64d8d10007f54294510006f441d8532006fe3218540004fd70d8943147ec325913215efd63ccb10005ff7250e51005ff7050e32006ff6518930206ff3218530004fe764c9510beff50d8132005fe7608530006fd640c520005fd7090c21075fd700c720004ff7358a51006ff4258f20005ff7354910005fd721854324ffb3059530005ff744c821007dd648c932007dd324c550007dd63cca51006ff5358e210beff1058b30005fd7494932005ff7255110006fd6354d200defa60cc8210967f5359631006dd7458c21006fd7058a31004bd74d9720004ec7258d1008eff40d8d100dff840cc9400befd7058b30006f6768c510165fd7690b30006fd7458332006fc54d8930005fd73909300047d7518b101c7ec514c9200067f65cc910006fd65d8532
  | 1 => 0x8730006ff5358d200bfed404cb20006ff63c8540005fd7294d42006dd6350c21007dd4358930005fd7394520005ff7250550007ed628ca31005ff7355321006ff648ca31005fd760c520006fc7158332006bc7359320005ff7350951125fc7354910177ec434c92025fdc5150f300067d6550c21006ff64589300b77e5455032004ff7259631005df7350932006ff4358d10005fd7290d52046bf42593301defc31d8132005fd7294d20006fd7058e52006fd75d8132006fa4358021037bc6450d30006fc655893000ebe71d9110006fc5058a31006fd6290730006fd5458b300077c4399720007ee714c920006be4058a41006fb7058d20006fe53d8121007f643c8710004fd7318550006fd64c8730006fe7358a41006ff5258831006fc764c910177f7318c520006fc7458f21006fc54583321a5ff7350730005ff7050e21006ff6294540005fb7050d30007bd4348540006b96498021006ff53d89301fdfd73c873017ffb414c120004fd70d8d52005f9700c940005fe76551321b5fe7390a51006ff32d81410c5fc7454d32004fd76085300deff60cc910006fc764c951006f5628c5100c7bc404ca41006fe74d8d212afdc50cc931004fd7698c21004fc764c9510c5fc7498532007f54348421007ed420c520126ff63cc910006fc6418d10006fd6254b3005efd40d89101cfef438c9200c5fe7494932006f84158032006ff53582210057d7598930006fe7558a310ddff70cc9101dfef32d8132005ed72cc520005ff7250d2115dfc7350b100d7df4350e320e7f441cca41007dc7350932006fd6458f20007dd704c931005fd70d9132007f53290710006ff6559130004ff7650e52005fd7394942005fd728c54000774658c51016ffb43c8120005ff7350920006ff658cb10005fd7094e420e77e5455332357bc43d8943004ff7058c21006ff5458831156fc6355110004fc764c910006fc65d89300a6bd30d9110136fc6390510005ff7254d310d7ef4250a32006fe64d8532087bf43509310c7bf4050d32007dd43d8930006fe764cb100ce7e654cb20004fd72d8d54005ff7259130127f6438c510005ff7454b31006dd634ca41005fd728c530007f7714ca31007ed754c920007f73254710005fd7498532007da434c120007dd4318530006ff64ccb10006ff4318910007b4648c510006ff5158b30006ff64d89300077f754ca51006fd71d895426ff7434c521005ff704c921006ff5258031005ff7350a31007de4358530007ed644cb20007f732507100bfed204c9100e6fc64ccb10005ff7354530007ef72591320063e6559021007dd754cb31037be5450930006ff6418530007f66118532006fd7158a43006fd75d8d10005ff744c931006ff650c940176fd63cc920006fc6418930006ff5358f100e7ef4290b320479e5450f30005b
  | 2 => 0xe6fc64cc910006ff6348540006fc65581320057d7518943006f94258032006fd650c94034fde648c932005fb7055120004fd760ca411f6fd76cc82138ebf42d8d54005ff7355121005fc7655132007f5434c52100777658c5101dfec32d813205ffa3088730006fc7558231007dd4394930007ed524c921005fd7318542006fe2058831006ff654c9301aeff3259631006fd64c8530005f973c81201577f53553300bded738c92005eff40d8910005fe7190f20005f471553210c6ff4258a43005ff7054d43006fe7258e41005ff764c520006ff65d8532156fe63550320d7bf4355232006fd624ca51136ff64cc941005ff7250d50006fd42d8131006fd43d895118efc4358d21006fd6250a31136fd63cca41004fd73d895408edf30d8d10005f77354710007f943c8120007bd54509210a6bd20d9110006ff7458f21007e932c8120004ff7358b10007d7324c710006ff41d8d2024eff3259530005ff7255132006fe435802105dfe71085300b6ff4318943004fd72986430dcff764cb200067e6558c21005fd728c5200077f6590d21006ff4258b30157ef325523214f7f5354b30006fd7158b30007ee428c5201bfee744c920216fc6394940005f6768c521007ed438c920006ff764c821005ff7054e32216fc6394942006ff4358632005fe7694930006fe43d85501fdfd76c8730006ff635095108cfd70d8d10006ff75d8d210077c43d9510396ff31d815315ff4328c710007f74118532004fd70185520cf7f544ca510277f515952001fbe5450920006bf648c5102e7de744cb31005fd74d813223fbd430c5400bfed634cb20006ff6354d42127bc4350d10007f9744c12015efd630cb10006fd4318910004fd73d9621356fc31d8943006ff43583210cf7f50d95322ffbe400ca410b7bf4118d42007f63188530005ff7354520006fd6354e420cf7c51551320ce7c5158e52005bd740c950004ff72593313b6ff30d8953137ef328ca41006fd6350a51006fc764ca5136cff7259542006fd7558f21206fc321853006fbc4150f210c6fc644ca51006fd7458831127ef324c910006bf735932020ffb30d8530006fe72d8d54006fc515833218ff57190d21006fd649893021efe4318930007f47159132006f5628c7100bdff704c9501defc43d8f20004ff7058a430c6fc644c950005f57394710005fd76909300befd4058f20004ff764c8210067d6590f20007f93254110006fd6448520005fd74cc8210d5ff7650e3206fbf4350b2108eff20d8f100076d6550b20006fc7358a410047d75d854303e7e65d95300d6fe6459232006fd6458d20006fd4398b10147be6450b32007f7329451003e7f52d9530005fd7294d41006fd52d8142006ff7058c21007f64354510004fc7648530007f54254710005fc7155232006fe54d8121006fd644
  | 3 => 0x56118530004f47159532005ff7650930076ff5058031005ff7359520007f9324c120005ff7550b32006fe764c940005f5710ca41006ff415833205efd30987201d7ee65509200ce7e654c8211b6fd63cca510e6fe64cc821005fe7190930006df6350d21006f5545843206fbf43d8542146ff6318d42006ff715833229fdf434c93106fbf4050f21006ff62485400379c4150d30157bd4355331177fa534c1200067d6550b31006fd4358632006fc5158d20007ed5390920006df764c832005ff7050b31356ff6218d42035be7498930006fd6448530007ed7298532006bf6454d100befd3058f20036bc41d9130006fd6458f21215fd7694b30004bd74d9421006fd644cb211e7ec414cb2023eff630c540137bd4390731005bd740cb10006fd7458231006fd75d894319dff7688730005f970cc520006d56348421135fe7398a41005fd7090a51007bc7359320006fe73d8954006fd32d8151005fc7159520007df744cb310bdff704cb100c7fb404c94019eff30d8931005fd72d9530005fd7090e51005fc7150d32005fe7690d21166fe6390a51007dd6550d30006fc7258e41007df6390d21177bf4390d200beff7058d20006df630c520006fd7058a41135ff76cca41136fe6390720006fd53d81310ceff654c95118ff6614873024fdf32cc5500e6fe64cc920007df648c932004fd76cc52019ffb30885301f6fd6390c21007dd435493019efe43d8931005fd7090831006fc7458f20277f6308c6210077d75d8543004ff7258e41007f95348110355ff7250b320ddfd70cc9101b7de4394730004ff7359542005f47150910176fc43d8d200bfed304cb20005fd748c932005dd7308540007bd4350b21005f671cc9210057d7508540006ff72d8d10006fc6158132005ff7654530005fe7690930007ef744c920156fe6355320145ff7350b32007ec7250e3202fbe6450f20006fc4158032006ef7258d20165fd7390b32004fd7694d200b6fc640cb10006ff64d85320067f6550d21057bc4150d21006fd624cb10215fd7394b32147f73150a31007dd544c9310eefd73d89531bfee544c9200057f7355152006ff7558a430073d5454942006bd6454b31006fe7258031006ff640cb10004fc7655132005f97090730006bf6418d10007ef7258132006ff65cc91009fbf425533114fef3259532006fd53d8910057bf4350921007bd5450831006fe4358251007ed635092008efd2098730006ff75d81320d7bf438ca41007ea324c120006fd3258241006fd655853219ff6434c6211f7ec321853214efc635494222fdf5150d30005ed720c5202afde50cc931004df764c8320c6fc644c930177f8434c120007f4715953208eff30d8f1014efc6354940006fc51d8930006fd3258231005f57308510006fb4058032006ff764cb20177ee534c920
  | 4 => 0xc910004fd70986530d7bf4250e320c5fe76d91320967c658c521005fc7155130006bf64cc9100ef7f5055332005fd72cc550155ff76553320d6fe648c9500c6be644c8210bdfd704c910005fc7150f2023ff5310c540006fd7258e41007f5434c710006fd52d8132006ff7458e522b7dc54cc9310d6fc42d8d42006fe43d8950057bf4050d21006fe75d8132007dd744c832007ed324c520006ff7458a5318efc3058a31005f97094d20176ff6394d20007ee5350b20007f5328c521006ff41d89301fefd6390f21136fd630ca41005ff7250e520cdff755953204f7c515533023efc3159130007ed424cb20006fd644ca510c6bc644c910005f47154d31006bd43d8940004fd72d8f100e7be5450b32007f4714c9313377e508ca510067e6598c2124efc325953024dfe7390950006fd654c920267f743c8521127f4434c510006fe74d813204f7f5494730004f970d9231004fd7690c21004fd7690a3115eff32d8131004fd7318552006fe5458232007fb6058132004ff7058831006ff51d8132005dd7308530004fc76509300e6be64ccb20005ff7354931006f74258432005ff744cb21007ed5250920005fd7090f210057d750853008ff7638c5102a7de754c93119ff671cca21006ff64d8530037bc6450930005fd7690d2018efe76cc921005f970c8530077f51018530005ff7050e31005fc7654530175fc73595200077d538ca51005fd72d9130004fe76c853005ffa20885300057f75485401aeff63cc951006fd638c7200ccfd7694b322d7be4050a31006fe6418930006ff620c540006fc43d852006fbe6450f21006ff764cb100063d6559320176fe5358232005f471595320077d655513208efa2058231007df638c5200077d54cca51007bd4350921004bd74d8f20006fd648c932006fd7558d201ffde43c8730007f24148110006ff6458532006fc6218530006fe4358652005f6710c521005f573c8510007ed328c720107f854481100c6fc644ca31005fd768c520004fc7650d21005f7735051008dfd708c7200c7be6455132004bf74595302b7df40cc9311d7ef5150920005fb7054d30005ff725513108ffa708c530006fc71d8d42006be6458c21157bf43553310257c7548520006fd43583210c6fe644ca51004fe769053009ebf4259331006fe7558d2004f7c5194b3018dff7348730005ff7250f10006fd624ca41006fc4158f20155fd765533203d7c7548530145fd7350b31005ff7550d32005fe7650d21007f63188520006fd7558f20007bd5450e320077d6590f20007dd43d8530005fd75d8132005ff72545400b7f4410ca41005ff7058532006fd648c720007ef754c92023fbd74cc940004fd7098732007bf735932000fbe5450d1017ffa544c120127fb3058530006fd768c5201fdfc7359321006fe6458532006f
  | 5 => 0x7de634ca41005fb7059132006fc7158e42075f6768c510006bd54d89431f7ef324c8210cf7f534c950006ff634c550006ff624c550006fd6498f200057f7559132006df764cb31007f543c852108eff3058231004ff7650831237dc6590d300c7bf42d913203f7f5154930006ff64cca21004fd72d8d401fefe6358f210c6fc644ca2123fef328c940005fd744ca21006ff43587200c7bf43d913219ff531887303beff31d9153007f6618c520006fd4258331006fe6158132006fd6558132006f77458432176fc4358232004bd74189510077d540ca51037bf42551300cf7f544c950007ef714c920037bf4390530005ff704ca41006ff644c931005fd7294730005ff7050a211dfee438cb20004ff7259330177ee720c52003f7f5254d30006ff654c940006fd6418530006ff640c520006fd7058a43005ff7358520037bf4355130005ff7250530006ff5258b10005fe71cc920004fe7694d42004fd7690f211f5fd730873019ff7328c6210c6bf42d9132006fd43d855219ff4308c621005fd7090d210bfef304c920006fd53d8143004fb7059132136fc639052015efd76ccb10004ff73586421c7ef524c920005fd768ca41226fc43d8930005fe7194f20007ed534cb20006ff4158d200047f7559132006fd64d8930005ff744c921006fd64cc520006ff64d8d21005ed7290f20007f9314c12002ebc4359320007bd5450e211cfec418c920006fe6458f2018fde43487301defd76ccb200befd4058b30006fd648ca31004df73589100beff4058f2008ffa708c520147bd435083114dff7354b30006fd64ccb201aefc3259631007dd438c9300e6fc64cc921007fa714c12003f7f5454d300077f4319521006ff624855014fec3259532006fe6358520005fc7688530006ff5358a3103f7f5254530006fd6398a411e7ee644cb20167ef32d91323d67f53185542dfde404cb31006ff65585323b6fe43d8953006ff5458b10006fd65d9130006ff648c930136fe76cca41007dd434c931006ff5258231364fe7694942005fd7290e21005fd7694930006fe425825110ffb5348110007f97448110005ff72545300beef2058b30006fd54d81321c7ef544c9200bfef404cb2005efd30d8b100c6fc64d9132006fe6298530007dd63cca41006fe54d8d20007de43545300c5fc7459532005ff7255330136fd76cca4119fec329853203f7c5154d30006be6498f20006fe3218550005ff7050d51006ff644c921005ff724c550005ec7250d32006fd62887302efdf544cb31005fc7158132007f7638c5210defd10d8930006fc52580310065d6558c21006be6498c21004ff76552321b6ff32d9531246ff31d9130006fd6350b20005de73085401ddfe7390720006ff634c950005fd764ca41005ff76505300167f53d97100dffa50cc9100ce7c654
  | 6 => 0xc7154b30005ff7350550005fd71d8943007dd4388530006fd6458930006fd634cb10006fa7158032007f9614c120006ff71d8943006fc4158b300277e65551200057f7548520006ff7158a43005fd7094d42004fd7218530004fd73d9720007dd634ca51006ff7058831166fe6390b10006fd658cb10006ff5058831004ff7654f20007f463905101dfbc4350f200befa604c821006ff7058a310d6fd72d8d420bff8404c9400e6bf42593321dff6310c72008ffa30582311f6ff64087300077d54cc950006ff6488530006fd6488520006fe4058831006ed6250831076fa4058031006ff6354940187fa754c1200277f5454d20004ff73593210076e6550b201a7fb3050530005ff7055332007f4614c530005fd73d91102afdc40cc931004fd73d89400065d6598c211b6fe63945200f4bd769932019dfd7688730007dd324c5401defd63ccb20006fe6498f211fefd6394f21007dd4308730004ff7655320006fd5458321007dd438ca3119dfc7350a21005fd7390510005ff7054941006ff634c520007f643c86210c6fe644c93008cfe760c5101dfef324cb2008dfe710c520007cd32cc520005fb7050920004f77159132126fc43d8d10007bd438ca411d7ec5350920007f6611853018eff630c521147fb3050930007ed5250b32006ff7358a41005fd73c8550005fd7290730157df32553310073d5454d430bdfd738c950006f631582210077c6550d210c6bf43d9132005f67190d100c77e5455132006ff658ca410067d54d8953006f96398021006ff3218540004ff7655130006fd7058e41004fd70d89540c5fe7454d32054fd72d912118eff6318d21187fb524c1200067f654c91018eff6390d21005fd7290d21006ff6394940007f47150921007ed744cb200067d6550821156fc63551201777f5394d20006fd32d812104d7e7508730006ff64cc950006ff764c950006ff75d8d420057575087100d7bf438c940177ee634c920007ed42cc520004ff7058e52166fc31d91320e6ff42d89430ef7f51cc950005d5730871009fbf42d8543006ef628c930006fc7458b300ddfe730c940006ff644c9510c7ef4290932046bc4159330187fb544c120176fc4358d20006fc7158b301f6fc4318931005fc765513023fbf43cc54015dfe7390b10006fd4398a510967c51d8d51006fe4398910006dd6350821005fc7155120007ee328c52031eff3018543007ef7254d32007f451d85320077f754c950004bd7418953006fd6354f201fefd630c721007ed3258520006fd74d8d102dfde704cb310057f7548530006fd74d8d210b6bf7259032005ff7250d5208efe768c5300ee7c65cc921006ff43d8132217ef32d9532005ff7254d21147be6450b300067d54d8950005fd74ccb210ef7f54cc9500ac7e7619510006ff42d8132147bd6450b32
  | 7 => 0x931007f9708c5300077c6590d10007f5325471007e7f52594310defa2058332006ff6458132004ff765513231efe61cca41007f5438c510006ff644cb100bffa30d8132005fe71d9130006fd654c9400e7f441cc9410077d538c9500d7bf43d8d421477d7518d42004fd73189410c6fc644cb10007dd5350e32006fe7158332006fe5458d20007f53250710005ff7059132005fd7550932007b7648c51008cfe7618d100cf7e65d9532006fd71d8930004fd7018553004fc76551310cf7c6554d320d6ff41d8d42356ff31d89430befd634c920004f97018931006bd4318542005ff7458f21007f5728c510006ef6288530006fe4358910006fc764c941237dc5190d301ffef32d8532007dd634cb1000fbc6490d1002fbc4359320006fe7458d20005ff7054d411deff31d8132007bd5450931005ff73593210047f7558d10006ff65ccb10006ef6250931007fa4354110007e9424c120004ff7258231006f561185321affb3054530007ed621893008ff83098530006fd764ca51006f76198532176fd6394d20006fd6598d20005ef7250d32135fc7358a41006ff4318930005fe718c9300c5fc7650d3217ff8744c120167ec32d9132006fc64d8532007fb754c120004fd72d9710146fc635091003f7c54d9530005f4714c9310ce7e65d95320bedf3058f20006ff62549400e7ef4250b320e6fc42d8943007dd4358530005fd7294d1013ff74354510007bd438c9400befa30d813223fbd43cc540006fe6458132006fa6398021006fd6558520004fd7398a51006fd658ca41007f63294710005fe7194930147f531508310bcfd764c9201fefe43d85320077f6554932005f5710c9400067f65509211aefe76cc951007ed538c9200c6fc4158a430e6fe64ccb10177f5310c520006fc74d8d10005f7715913200fbc43d9110004ff7359621006ff6458530006ff6598930005fc7654930006f9435802118ff63148730005ff7250e32006fc6498930006ff624c930006fd6518930007ed3294520004dd73d94211defe6358f20006ff640c950006fd43d8132297de304c93118fdc6390d21006fe5458332005fe71d9530005ff7350910376ff32d814306eff7650821007f5328c710005fc7154e3208ffa208c530177fa634c120006fe42580310bff8704c930045be7408730006fe54d89300dcff7258d20006fd32185301defc53d8132004ff76547300277f5254d201dfee634cb2001fbf4355120005fd7094d41004f4715954201fbf43905200c7be5450d32007ef7250e32006fd43587200077e3254550006bd644cb200047f7558910005ff7054d420e6fc64cc951307be404ca4101fbf4255120004fc7650931006ff54d8d20017775254710006fd73d8954005ff7348550007bf6450d32006bd6494f20005fd74cc921226fe53d8930005f
  | 8 => 0x67d6550f200063e6559320127bf4390d10004ff7654e420c5fe74d8132007be73d9110004dd73d9021006fd72d8d10006ff5258332004fe7694d10006ff624c530005ff70509510ce7f5258e520cf7f5255132006fe4358b10004fd760c72018ff4638c5210ef7c50cca51006ff6418d10006ff62ccb100077d540c950396ff32d81531bfec744c920007ec714cb20006f7618c530006fd431893023dfe7394540006ff638c940005fd72d8543007f53294510006ff43d8931005ff73552321fdfe7390721006ff62d8543005ff7255121007ed654c920006fe6358a41005ff7055032005ff704ca21006df7458c21006fc5258231005f471591320e7f741cca410e7ec4250b320ae7f30d9510006fd535832103f7f53d9530006ff54582210bdff704c940007f543545101a6fc63505500063d6599320177ee434c920005fd75d913218efd7690d21007f9708c520006ff6558132005fd708ca512cfde308ca3118dfc7690d21007f47150f2109ebc7159331005f67194d10004fd73d8520006ff7058e41006fd64d853008ff7208c710007ed424cb21006fe725823114eff6390d5236ebf43d895404f7c52947300077e6590f20004ff7650f21006fe7458b3015ff571ccb102efdf504cb31146fc43d8d42147ef3250a3218efe634852023eff63cc540155ff73553310beff4058b30004fd73d9121005fb7050d10146fc6350950006ff6298530126fe43582310077f43d95210ae7a5058251006fc7458d20087be5450d3119dfd7388730006ff7058a53004ff7359110005bf7355142007f543c8710006fe4318950007fb704c930005fd70985320bfef504c920007bd5450b31005ff7655132006fe7058a31006fd6254730005fd744ca31004f4715913225fdf5250f30076ff2018530006ff71d893020efc43d8530006fd32d8141297dc504c931006fd6250730004fd72d9131006ff4258331006fd53d8941006ff5458231136ff32d923102fbe5450f2000fbe5450910007f5708c521166fe6358e42004ff7259530005f47154f2119efc638854011ff443c8510005ff7654d20006fe4058e210c7f4414ca41004fd76c8530006fc7158f2000ebf4358241004fc7650951007dd324c53019ff57190e21006fe54d8d10006fe4358a51007f73290510006fe43d8121007fa514c120005ff7655120006fd70d8d51005fd7390a31006fd6559130005ff7050a31007d9434c120006ff634c910007f76198532217ec32d9532006fd54d8931005fd7290d20006ff5458e21005fb704c93008eff5058231007bd5450e31007dd5350d31007ed42885200067d65cc821006de6350821007f56118532005fc7155332007ed714c920004fd769083107e7e650c720037bf4250d30006dd63cc8210beff604c910004fd70d8e21126ff6394d10087bc405
  | 9 => 0xf32cc540076ff3018530006fd43d8550006fd7258031004ff7650c21006ff63549211fefe4398821146ff6394d42166fd6394e42006fd764c94029fdf404c931006f7628c510006fd54d8d21006fd6498520005fc7159130006ff654c91015efc43d8131007f77150d310bdff704c930006fd648c5201adff76547300b7bf4218943004fd7318954006fe65d893000ebc43d911008ff5408c510007d5324c710007f5434c6210deff30d8930004fe7608530006ff5258f100067d54d8d521adfc7350951007f47150b31297de504c931006ff650cb10007fb704c920006ff6318542004fd7318910007bd5450a210c6fc644c91018dfe7390521005fc714c930006fd7058f21006fe7158d200d4ff7359132005bf7458520006ff764cb210c6fe644c821107f84348110006ff64cc91018efd6390d210c4fd73d9132006fe3258251005fd7090d52004ff7058e4203f7f5394530004fd72d911024eff6390d500defd73d893006ebf43593210ddff70cc95008efa20d8d10005ff7250e210d6ff72d8d42007ef624c930004ef7258d1008ff7308c7100e6fe64ccb20146fe6350b20006fd6390721007dd438c530005f471549100deff60cc940006fd5458f21006fc5458b30006fd634ca41004ff7259540006fd654ca310c6ff644c9410c6fd5458e32006ff648c5300069d6458c210077d5454b320d6bf4359232005fd7655132175fc7355120177fa434c1200077f6550d2108eff70d8d10007f76198530006fd7458c21004fd7218554006fd71d8d54175ff760c5200067d6559320007ed424c921005fd7418532006fc43d8910005fb704c920006fd6250b30006fd654c9300cf7c5154d32075ff700c520004fd76cc8210067d5458a510beff7058f200c5fc74d9532005ff7058a311b7de63cca510057f7559130006fd5458b310b6fe640cb1023dfc73545400077f4359720006fd64887300063e6599021175fc7350920006ff63c8550004fc7654d10007ed3248520006ff6418d21006fe764c941004fd73d91101deff6390f20006ff63549411b7ef324ca5101ebc41d9120006fd6298530004f77159542006ff62cc540007f9654c120005fd7290d51006fe301853203f7c6594530004ff7258f10006ff54d8930007ed429472014fde4354b30007f5424c710006fd43580210bfef704cb20247fb30d91300d7bc4150e32007de4318930007bd43885400d7bc42d8d4203d7c7559130147bf4350b31006ff639452001fbe6450d20004fd768c720007f77150c21006fc3218540006f44158432006ec624c930006ff658ca31006fd435825101fbf4250d20004ff7654520005fd7090e52005f4714c921137bf43cca41006fe43d8151146fe63508320e7bf425533205dfd7088730005bd74085302e7dc744cb31006ff5458f10005f97008540
  | 10 => 0xc931006fa5458032004ff7058a51005fd7390720005f9700c540396fc32d81530ddff70ccb10006fe54d8910005fe71d9132004ff72591300bfe8204c9200b6bc41590321b6fd76cca51006ff6390521007f6430851029fdc544c931006d532584320067d54d8d50007dd5350d30094ff735953118dff7450d21004ff73597100077d544ca51006fd6358520004fc7654d21137bd43cca41004fd7318951006fd634c5200e6fc41d894301777539471008ff5308c510006bf6350941006fd53d8142177f8314c120004ff7655032005ff7458132005ff73508211b77d53cca510067d6558f20006fa7358021037be64d9130005ff7550932006fd634ca51007f7648c521006ff7258231005ff75581320c5ff72509320d7bf4050e32006fe53d8910007ed4298520005fc7650d21005ff7650d2024dfc7348550006f97558032006ff71d8d42004ff7058a41006fc64d8930006796558021005fd74d8532007ed428c52009fbc41d85430ddef7258d2009cfe76905310d6fe648c932006f740584320076d654cb200277f5394520005b574087100077d6550f2001fbc6490520176ff6390d20005ff7050b32006fe6558930006fd7058831006fd7458a31007fb40d813203f7c51d9530006ff64cc520177dc630c520155fe73d8954006fd75d8930005ff7458532005ff73509320057d7394a51006d96358021006df63cc92108eff30d8d10145ff7350832007fa42541100067f65cc92104f7f5454b30006ed628ca31177ed720c52023eff3159130006ff52d8930006ff5258d20006fe7558831006ef624c9310047f7558642006fc41d8132004fd76cca41005fd70cca511ffbc4350f21006ff6158132006fb40d81320063c6519110005bf72551430bfed504c92033f7e50cca510077f6590d100073d5454d420fe7d4059720005fc7159530147bd4350b31007dd4354530005bd74cc520007bd4350a32006ff63885400c6fe644c920006fa7458032136fc32d92310beff3058d20006fe7458f20006ff6348550007ef6208530004fd72d9631005ff7250d30006fc645853218ff6438c521004df764c4310deff70d8930006fd6498f21007dd534c9311ffef324cb21146fc3159232004fd760c520006ff4258f21077fa300c520084fd73d9131005f97090930006fe6498f20005fc7154d30006ff74d8930145fe73d8542006fd71d81320f6bf3059320006f54258432006fd70d8954007f231481100e6fe64cc950177ed320c5200967f5259631217de4394b30007dd4394730004ff7359121005fc71550320c5fd7390932006fd648c930006ff7458031176fe43582320e6fe64ccb210cdfd7394932007df6350d21005ff7559132007ed42cca21007f9214c1200967f52d8d51006ff5458d201aefc635454018fef3258532005f9700853023fd
  | 11 => 0x6fd63945200479f4250f3006fbe5450f210beff40d8132006f56348421006ff6350d2124dfc73505500047d75d8c21006ff644c950176ff630c520007f8714c120005ff7250d20037bf4350930007df7350b32006fc7558b301defc4358f20006fd43d89500067f6590d100bfed204cb10006ff65d8930005ff7358a41146fc6350951135fd739073025fdc5250f30006fd52d81210ef7f50cc951004fd7690930006ff7458a31007dd634ca41005ff704c951007bd4350a21005ff7355130004fe76909300063f651911007e7c650c510005fd72d85300bffa504c910005f77150e3123dfe7388540127f6434c510007f4714cb10006fd74d8953005ff704c9411f6fd7690c21004fd73d89501dfec434cb20004fe76cc92108efd70d8d10006ff43989100277f5359520126fc4358d10006fe6598d20005fd730854004f7f52553300bfed704c920006fd72d8d21006fe6058a31006fe7558b30005ff7350931086bf43d91310fe7d3059720006fe30d8e21005fd7298e41006ff7458f20246ff32d91300d6fe648ca51006fd64cc9200ce7f5058e52005fc7154d20005ff724c5400047d75d9320006f94258021007bd438c54019efd6390e211fefd7690f21006bd64947203beff32d9153006fd648cb10007dd704cb31004fd731854203d7e7598930037bc6459130007bf6450932007ed4254520005ff7054931006fe43d8520005fe7694530006ff648c932006fd6350f21006fd42d8132006ec6250931006fc75d89300057f7558532005fe7690d10006ff3218550006fd32d8131006fe6218530006fc6458930176fc3158232006be73d9110006fd624ca310c5fe74595320c6be644cb20146ff3259132007ee5390920007ef72595322b7de54cc931006ff7458831005bf7458530006ff6558930007f53188540006fd6488530007ed754cb20146fe6350a51006ff62885401b7ed320ca51006ff42d8d210047d75d8f20005f97094520006ff62945300e6bc41593320e6fd73d894323efd76cc940056bf42d9121006ff5058e210063d6559021107fa544811019ff66188730006bf6494d1017ffa744c1200e6ff43d89430bcfd76ccb203a6fe43d85531f5ff74cc82118fef324c921047bf4150b30175fe73945201dfef72d8132137bf430ca41006ff62cc550005ff7648530005fc714c9201feff64c8730166ff31d91321a6ff32592310069d6498c21006d56388421005fd7690530004fd7298653005ff704ca31006fe6498930175fc7354520005fd7690f21157bf4355032007ee714cb20006ff634c951007dd43c8730056bf43d9121004ff764c520007fa5348110176fe6358d20006fd6350c21006fe71d89300a4be7619110085fd7390531006fd7058a53007f4714c921006f9745802115ff7324c7100dfef20d8930007dd744
  | 12 => 0xe5450d21145fd7350832007bf6459132005ed720c720007ec7254d3200fbf4355110006ff42d8121145ff7350b300cf7f514c950005fd7090e21006fc54d8132006fe5458032006fc7558031006fd64185320077c7559132006ff638c540006ff43d8532004fd7690720004ff7358a4100fbf4255110007ed42cc920007f7648c510006fd4398910056bf4358a41005fd700ca41006df638c520006ff654c9311c7ef514c920006fc5258f10005fb7050f200ce7c654c921007df754cb3124dfe73c85501b6fe76cca512e7de544cb31006fe4258231004fd7690d200c7be5459132087be5450931005fd70185323277e500ca51226fe43d8930005fd7090a310967f50d8d51005fd7550e32006ff6390950006ff65cc941007f5318853008ff5208c510007ec6288530006fc64d8d211e7ee744cb200c6fe644ca31004fd70d8d4205eff505822115efd6390f10006fd53d89430067f6254550156fe6355120006fd6158132005ff7258530136fe6390520006fd7558332005fc7650d10165fd7690b32004fd768c520006ff7158a53006f6768c521004fd7218543006ff638cb1001faf41509201b77f53cca5134fdc648c932006fd7458b30004fd7694e4222fdf5350d30166fc4358e42006ff62189430c7bc6450d32127f4638c51023fbf43cc940006ff65cc921006fc5158b301dfbf4390f20006ff65cca41005f47150921007de430853022fdc6550d30007f9724c1201c7ee654c9200d7bc408ca41297dc704c931165fd7390b300067f6394551005fd7118943075fd700c540006ff644ca21007ed438cb20006fd43d89310deff50d893021ffb3018930006fc70588310deff50583320047f7558d21007bd5450a31005fd70cc921157bd4355032137bd430ca41004ff7358720006bd64cc821006ff7650b3124fef324c9502a7dc754c931006ff4358f2115efe53d8131004ff73595200beff7058b30006bd4358a4114efe6354920006fd6458530006fd53d8132007f5328c621215fd7394b30006ff43d8d211aefc6354520004fe76949300047d75185201fefc43d8f21005fd72cc5400b6fe640c950007fb724c120006ba6498021005ff764ca41005ff7350b20007dd7318532006fe53d8141007f5428c510005ef7254d32005ff7250d51006fe43582210c6fc644c92118eff6448730006fd54d812102faf4350b20004ff7058e51006fe54d8131006fd644cb200cf7f5055132006da63580213b6ff31d8953037bf4250530006bf644c910005fd7394720007dd32cc550037bc4150d30006fd75d8d212a7df534c9311b77e75cca51004bd7418b10007df744c8321efef438cb200067a6598021004ff76553321a6fc6350520007ed420c720076f51018530007dd43487300c7be5450932007ed5350920005ff7388530005ff7250e31
  | 13 => 0xc920004fe7690d10005fb7055330127f73158231127f7328c510005ff7050c21004fd7398a41007ef744cb20005f97090d20005ed73909200077f4399720005fd7290d10006fd5358242006bd640c72024f7d53cc9500c6fc644c9510047f7558221006fd634852016ff843c8120006ff644c5500067d6558c21005ed7294d200dffa10cc9502efde754cb31136fe6358e41007f9524c1200bff840d8132246fc32d91300e7bf42d8943005ff7050d32006ff628c540187fb514c120136fc63905211b77d530ca510cf7c65595320067c65d8d100a6bf30d911018ff4434c5211d7ef535092039eff3218553005ff7254d40005fd74d8d21006fd648c530004ff7358910077f71018530006fe75582311e7ee544cb20006fd65cca4115fef324cb10006ff5258a31006ff6354540006bc64d8d10005f573c8521006fc7158d200befd1058b30156fc6355121007f87059132007df704c93118eff3058a31006ff7258031006fe6498d20126ff6390d10006fc4318910356ff32d894300fbd73191103aefe4318953005ef7350920004ff7058e21004ff72580310277e65545200057d73949500379e5450d30007e8724c1200077d544c950007f73294710047be5450b30005fd73d8542087bf43d9131177ec438c9202bfdf54cc931007f64354710005fd760ca41006fe5458f200ddfd70cc9502afde40cc931005ff7055132006fe74d8d10085fc7650d3123ffb305913001fbc4150d20006fc6458132006fc64d8530187fa654c1200bef840d81320befd634cb20007ed544c9201f7be4350c211f6fc3018532005ff7388520005ff7348540007ed32905200077f325455014efc6354921007f63290710007f543c8621005ff7258e410077f4319510005fd73d8954006fb3258021006fd764cb1001fbf4350920006ff7258e41006fd4258251176fd6390d20007dd544cb3123dfe73085401b5fd739473019fde43887303befc32d9153006fd65ccb1005eff30d89100077d5454e32005fc7150930006fe64585201defd6394f20297dc404c931005fd73985201deff32d813210ffb54481100ce7c65595320063e659932008eff2098730004fe768c521006fd4358652006fd32185400067c65d8d21004fc76545301f6fe4318931007f75118532006ff4358910005ff724c530007de4398530006ff6248530004fd7018532005fd7494f211dfee534cb20005ff7355120006ff43d8121005f9700c520117fb42541100067d6550b201f6ff32185320067d53d8950376fe53d8143004ff76545300d5fc7454e32006fd64d81321b6fd630ca51127f671cc910007ed524c920005fd72d8d54117fb43541100beef604c920004fd73d9221005fd730853018fbc4350d21006fd6558d20005fd720c540005f47150d310bdfd738c9400beff5058d20057b
  | 14 => 0xbefd5058d200067d6598c21006fe7458332005ff755853217ffa644c1200cf7c54d9532007f53290510006fc4358321177ee538c920006b9645802117ffb424c120006fe64589302c7be4050931007ed624ca31006ff648c52000fbf4250d1017ffb434c1200077f6554d32006fd4358a51007e942481100ddfd70ccb1023fbf430c940006ff74d8132005fd73d9121006fe3258231006fd53d8940005fd708ca41006fc71d8132177ed32cc5200077f43d9510007bf6450d31005ff7050d31006ff621853024f7e75cc950005fc7155132126fc5358231007bd5450b32006fe4398a5108edd30d8d101b7ef328ca51006fc4158f21004fd72d9231005fc71509200057d75d8543216fe6358e520b6ff7650a320057f73545500d5fe7454e3214dff7354b3101fae5450920006dd634c821005fd70d8532006ff43d8f200067d654c8211b77e659473014efc63549410c6fe614ca41004fd72d95300c7f4414c94123fbd43cc940007bd4350a31176fd630c5200077c6550d10004fd7018542006fe2058a31005ff7348530006ff5458a31006dd634ca51006ff51d8d20006ff625454019ff63188730005fd7390721005fd74d9532005f573905100f6bd5059320217ef3294932004fd72d8d51006ff650ca41177ef32581320c7df4350d32005fd73c8540004fc7650d5105eed20d89101a5ff76507300c6ff4158a43004fd72d8d50005fd74cca21004ff7650b3022fdc5150d30006fc7558d20005f57308710004fd73d85400defd50d8930006fd6350821006ff654cb100bcfd7698f20006fd4358910007f64394510005ff7350a51004fd731895000fbc6450d10006fc65d8132117f84254110177f970cc920006fe5458331006fe3258241006fe4058a310b7bc41189431bfee644c920006fc60185320047d7699421005fc7159120006ff4158b30004dd7698c21005fd70cc9510047d7518943007fa7348110005ff7255331007f943541103e67c51d8d54006fc321855019ff56188730006fd71d8d42005ff744ca2134fdf438c932005fd7390a51004fd72d9130004fd7318940005fd73c8530004ff7359521006fe64d8930006fd43d8121007f77150831005ff7650f21237df5290d300dff830d8930007fa414c120007ef6298930007f9544c120005fd7494d21007ef754cb2004e7f54d8153006ff6354d40145ff7650b32004ff7650930004f970d8c21007dc6350d211bfef424c920007f77150f211bfef434c920005ff7350530006fd43d8532006ff53d81320d6fc648c9500defd70d89301adff73547300d6fc648ca510277e6554d20004ff7655331007f9754c1200c6fe644cb10007fa3254110004f970d9421006fd75d8d42077f83018530006fd6598930226fc31d8930006ff65d85301a6fc32592310257c75585201c7ee754
  | 15 => 0xf545833223eff3259130006ff6350f20006fe53d8941006fd6350b210277c659452019efe6388520005fe719893001fbf43591200c6bf4258e4218efc4358632007de4394530006ff43d8d2024f7d530c950007dd4318930006fc41d8d21006ff515833215fed320cb101fdff7690f21177f8534c120006fc50588310cf7f5254d32006ff62509500c5fd749093225fdf5150f3023fbd430c940007ee42945200bfea304c92024eff63cc550006ff62cc940177ec32581320beff3058f201feff6390f21006fd650ca410c7bf4255132156fe6355321005dc7358520006fc75d8132005f573c87100ce7f53d95321f7fb30085300c7f7414ca410f6bf1059320006ff638c521037bf42d9130007df6590d300cf7c504ca5124f7f53cc950006ff7058a411b6ff32d9631177fb314c120006fc61d81320deff10d89301defd760c72019efc30d8e2120efe43d85300bfef304cb2008efd30d8f10005fd720c520005ff7054d32006fd4258031147bf4318d42005fd70d9532007dd438c932006ff40d893114eff3259532007f4329471039efc3218553005fd7390521006ff7258d200b7ef42508321d7ec5150920007dd4394b300c7ec4250932005f5718ca3103f7f53551300067e6558f20005ff744ca310d6ff765083224fed320c950006ff70d8943005fc7150e3206cff76508210077c3254550006fd5458232006fd62185300cf7f5454d32005ff7350520347de744c832216fd6390e520067d6598f20006fe43d81520e6be54d8943006fd4358b10005f67190d21006fd62582310c7ef4250932125fc7355110137ef324ca41277f6208c6210067c64195100d7fb408c9400667f53d9621006fd638c721007cd424c832005ec7258530157ef3255132007ed434c920006ef764cb20006fd435823114fef325493208efa3058231006fd6498532006fd6390b10006ff624cb10005ff705513108efd50d8d100067f65d8d10006bd54d8d42007f643c8510006fd54d8d20147bf4350b320d6fc648c930237de6590d30007fb714c120006ff6350d52006fd650cb1004d7c75487300076e654cb20006fe75d8930006fc5358b1018dfe73d9121006ff6390520005ff7350b21006fd43189500077e6550f20006fd6358a411cfee548c920005fd7690520007ee624ca31006fe71d8132006fd53d89310bff83058930006ff3258251006df7658c2103f7c65595300c5fe7498532006fe625823106fbf4359321155ff735533203f7c655493005eff6088530006ff4058b31177ec534c920006ff4358d21146fe6350b10006fd7258332386fc4318943037bf43d9130155fe7318954004fd7398910004fd7694930125fc7350910126ff630c5100befa2058f20005f9700ca51006ff658c930004fc7650d10004fc7655110075fd700c52003f7f5354930
  | 16 => 0xcb10005fd7608530006ff625493023efe76cc940006fc63185420067c6518d21006ff7650a31006ff655853008efd20d8f10006ff43d85200c5fc7458532006ff7458c21006df634c921145ff73508310bfea104c920176fc53d8d20005fd700ca511577d53553320c6fe6459132006fd7558b30004ff73595100c6fe644c950007de43c85300c7bc6450932005f9709052019eff63cca21005fd75d85320b7bc4218d42006fc6458530356fc32d89430c6fe644cb21006fe6458f21006ff71d8132007f5728c52115efe43d81310167c52d9710006fc7558332005ff73549400ddef764cb20006fe4318951007dd32cc540005fd7598532006fd72d8d51006fc6098532006ff74d8953006ff75d893005eff30987200c7bf43551320277f5355120007fa4348110006ff51d8930006ff7650e2119fef3298532006fd7258231147bd4350b3208dfd708c5401777c5354d20176ff63cc520005fd7294540006fd648ca51006fe5458b301b5fd7694730007ed3288520005fc7150b321aeff6390d51004ff7654d20005f47150f210c6fe644cb20006fd6350d21004fe760c521004fe76cc95106efd4398821007dd4354b30005fd70cca41006fd6559132006ff5058a31006fd6354f21004ff7655120006fe5458321006ff4058f21006fd5458332004ff7258e51006ff74583320067f654c92103f7c519493015ffb3098530005fd7518532006ff6354d41004fd73d9641006ff644c910006ff644ca31005fd7294d21006fe43d8910004dd7318b100067d5358a51006f4614c530005ff7254d41004fd73d94210057f7255153007f6614c52023eff63cc9402bfdf50cc931007f97548110006ec62cc9510479c4150f30005fd7090d510057d7394952006ef62cc910006fc6418d211fdff74ccb210bdfd704cb100c7bf434ca410077f6550d1018dff74cc921005fb7048520006ff6350921005ff7550e320beff604c940007de43989300ef7f52d8953006fd5258332004fd7018543006ff7558f21136fe63907210d6fc648ca31006ff6350d50006fe5358321006ff64189301ffbf4390f21007ec7250d32005ff7254d42005fd7694d20005ff73485201f6fd63cc821005f9708c5300c5fc74185321b6fd6390e51005ff7350921007e9324c12014dff7654b300cf7f53d9532005fc71553200047e7619521005ff7688530007f9434c120005ff74549310c6fc644c9311afde43547300067f65d8d210ddff70cc940006fd43d8151005fe7190b30007de634ca51007dd754c931005f77354510006ff6250550005fd7498f21006fd71d8943146fe63508210bffa204c930006fe65d8132004fc7655130006fd6250831005fd7218d54005ff7254d20006fc51d81320067e5058a51005ff7254d300067d65ccb20004bf7458221006ff638c950006f
  | 17 => 0x5fe7218543006ff4358232005f47150b31005ff7454d320cf7c51d9532007ee5250b32004ff7058a31007f9714c120005ff735493018eff63cc921006fd6558930297de704c931004fc7654d42006fc7458332005ff7154d43006ff62cc950005fe7118930005fe76905300047d75d9231126fe76cc910007de43485301577e6555332004fd7318540007f5618c520006fc74d813204e7f5259730007f5324c710155fd7355332006fd7158332006fd644ca31004ff7259543006fe61d8132005fe7190d20005ff7055232006fd64ccb100077c4319521005ff7454e32006ff75d8d1008dfd708c5300c7bf4250d32006fd54d8930007bd5450c21006ff63d8542006ff62d853004f7f5254730005ff7254730006fe2098732166ff32d91320d7bf4350a32347dc744c8320047d75189310073d5450e51054fd7690721006fd6354920006dd7058c21006ff658c940006ff41d8132005fd7290c21007f9709853035dff7555332005f67194d2123dfc7348540005fb7050b30005ff7050e51006fd639472005eff30d8b10006fe7158f20006fd7558a43007f54308510055fd7490d21157ed3255032005fd7294530005fc76485300ccfd73d9532005ff768c520005ff72551300e77c54553320077d534ca511ffbe4350f21006ff40d8d211fefd63ccb21004ff7058f210067d5458e510d7be6450e321b6fc32d9631147bf435083208ffa2098530005ff7250d10005f57190a31137ed320ca4115fde63ccb100067f63549511a6ff63cc941006ed6218930004f77648421006ff70d8953006ff5158d20004fd70d8953087bf4355131087bf4255131007fa214c120176fd760c520007ed3294720006fd64cc821007ef7254e32006fd7458f2129fde744c931267f443c85210cf7e655513203f7e65d953003f7f5494530006ff6290530006ff7058e52005f9708c52018efe4358a31167ef32909320077d54549320c5fe748c932155ff7355032005ff7350950007bd434ca41006ff6354d21057be5450921006fd65d8930004bd7418931005ff7050932005fd7390950006fc3258251006ff6350d200967e658c720007ef764cb2002fbf4390720006ff4258332007fb7058930005fc715533023eff630c94003f7c5155130006fd435823202fbf435532012ff7434c51018fbf4390d21005ff7054d31007bd6450f210bdff704c91032f7e504ca51004fe7690d51145ff7650b30006df7058c210063c65d911023dfe739494002fae6450b20006fe6558d20004fd73d9021005dd7308730007bd5450d32165fd7390831005ff7359120007f5438c5210e5fe7454b32006fe64d85300057d75087300bfed404c920005ff745953208ef510987300379c6450d30006fc7558831006ff64c855003f7f52d9530006fc7650d210d6fc648c932006dd63c
  | 18 => 0xc744cb2030fbe408ca41007f6768c521037bc41d9130004fc7655121005ff7255120006f654584321577d53550320c6be64d9132006ff7558d2023fef324c940006fd640c720146fe63509200047d75d9021006fd4358221005ef7254520007ed6350b20005fd744c93115eff63ccb10006fd638cb1015efc5358f10356fc43d8943005ff70509311f6fc6308540006f5618c7200167f52597101dfee434cb20004ff7654f21007df754c93103d7e7508530007f7714cb100a6bd50d91100cd7c7558532126fd6390d10005f6710c940006f96358021005fd7494b32005ff7254d43257fb30d9530005ff7350b10226ff31d8930237dc5290d30007bf6450d210c5fd73509321bfec414c9200c4fd7690b320cf7f5054d32006ff4358d20007df7350932006ff4258d20006fe6558132004ff76553300d77e5455232006ff7058f21147bd4350832007f44118532006fe7158b30006ff75d8943007bd439053102fbe6490f20006ff5458b30005fd7390b10145fe73185420067f6550d10084fd7690731007bd5450d310277f5494520006fc64d8d10006ff43189310277c51551201f5fc7350821006fc5358221007df744c931007f94254110387bc4318943005ff7050f21376fc32d8143005fd7290e52004fd73d9642006fe43582520e7bc41d89432dfdc504cb3103e7f53d95300063f65d9110007dd434c930216ff32d95320bffa60d813223dfc7354940006f97458032007f63148540006ff7458231006fe63985200cf7f504c951007f5434c5101defc43d81320e7bc40cca41006fc7258031005fc7150d30006fd7458d20006fd62d8530007ee420c5200d6fe648c930006fd644c9200c7bc6459132006fd7558e42006ff644c930006bd6458c21007fb7058d20006fd54d8d10006ff63905100d6be54d8d42006fc435872004f7f5154b30157bf4355330006fd70d8d42006bf640c51002ebf72593200057d7518d42006fe53d8142006fd639052000774658c521006fd3218550006fd6350e21005fc76509300067e64997203de7f53d89540c5fe74d9532157bf43553321a6fe76cc941057bf43d9121157bd4355332004fd7018554006fd52d8141006fe71d8943005fd7290f20006ff65cca210ef7f525533214f7d5354b32006fd43d8520005ff7250730137bf4390730005f9708c9300057f7548730005f9700c9500befa60d8132047bf4255330005fd744c8210c6bc645913209fbc4050b3119efc5358e21006ff42d893005efd50d891002ebf4359320006fd5458d20006ff7458b300bfed304c920007ef6258930007e5424842129fde544c931006ff6354910006ff43d8930005fe71d89301fefe4398a310e6ff41d8943006fd65d813223efc32591301b77d75cca510e6fe64cca51006ff6448550004bf7458910006fe764ca51
  | 19 => 0xc931007ed3254520005fc7158930005fe7194d20006fe6458d20006ff74d8d10006fd654cb10146fc6350921005fd7388540006fe64d8132007fa614c12024efe76cc950145fe73949422dfde504cb31005fe7194b30006fd644c520176fc5358d20006fd3218532007dd4398530007ed3250520006ff648cb10006fd4318931007f64348421006fd640cb101defe53d813202fbd7399320155fd735503205ff8308853000fbf43d9110007dc638c5200d6fc648cb100067f6518d21005fc7150d20006fe4398b10005ff7055121005757508510166fc32d9132006dd63cca410e6ff73d8943005ff7354941004f87648110175fc7348520006fd71d8953005d5730851019eff3098632006fd764ca41006ff6498530006fd6250b10007f97348110007de43d8930004bd74d8c21004fd768ca41007ed424c9200277f54595200cd7c7559132006fc7158a43005ff7454d31004fd73d97210cf7c754ca51005f9700cb100bcff7058d20007f73290710006ff7158b30035be74085300d7bf41d8d42005ff7055321006fd658c940006fe764c91019eff6488730006fd4258231005ef7250e32005fd7418d21007f63148530006fd7458e52005bd7498930005bf7459530005fb7254110004fe7690d210e5fe7494b32007de4318530075ff700c720007f56118530005fd72945201dffb30989303c6bf43d815408ffa308c520006ef624c930056bc4058a41007ef7258d20007ee5350920007df324c5500ee7e65ccb20006bd644c821006bd6498c21007ed5250921176fd63cc520006fd6350f10005fd748ca31005f671cc910007dd4388730006bc71590320047f7558b10004fd764ca41006ff5258b300077d7518943006fd42d812100fbc4150d10005fc7154930004fd7218550006f56388421006f76198530175fc7359120005ff7050d21006fc74d8d21005bd741895317ff8414c1200065e6558c21006fd43d89300c7bf434c940087bf4250d311aefe63545201ddfc7350b20006fd6250a5123dfe73c8540007ee32945200c7be64d913215efe76ccb10007bd73d9110006ff654ca41006ff7458d20007ed328c520006ff764c940007dd4308530006fd53d8121006fc764cb101577f535533218fbe4350d21004fd7218540006ff654c9211b7fb3094530004fe764c910005ff765493000fbf435091008dfd708c520007e942c81200047f755913000fbe7319110006fd6390a5102fbf4250f20007f6328c710007ed3298520006fc764c940004ff7359320006ff6408530197ef5288520006fd7458a53006ff43d8d101a6fe63505200c6fc4258a43007f77159532007f4714ca21004ff7650d20005fd7290530006ff42d8d101defd6390f20006fe3218530004bd76990210d7be5450e32226fc53d8930005ff7355110006fe74d89301e7e
  | 20 => 0xc6ff4358e4222fdf5250d300967c658c510006fd7158a53006ff65d8132006fd70d8953006ff7558332006fe6018532005fd7388530004fd7690530006ff7558f20005ff725533223fed320c940006fd62cca51004fd70d8d510047d7518941004fd7694f20005f7715083106fbf4355321006fe43d8951006ff6394942157be6455332004ff7648530005fd708ca31004fd729873000fb74390510006ff43d8530087bf434c540137be74cca410bdff7058132007f9514c120175fe7398520006fe4318910006fc41582320067d6590c210ef7f54cca511fefd76ccb21006ff7650f213e67f52d8d54147dc7350b3218ff6434c52108ffa2058231006ff6350550007f5328c5100deef20d89300bfe8704c920006ec62cc9100befd5058f2011ff743c8510006fd654ca41005ff7054f21004fd7694f21006fd62947300c5fe74d85321577e6555330006dd63cca51006ff3258241005f77159532006fc6218543177ee438c9200bffa104c950007f9414c1200bfed504cb201ddfc7359320004fd7098643007746590510006ed629083119fef324ca21005fd7290520006fd65d85300ef7c5155332006fd764c950005fe7198d200b7bc400ca41007bd434c940006ff63509500157e750cb100057d750c9400077c43d9521006ff6288530036be64d91300077d3254550004ff7650b311dfed720c7200cf7f534ca51007f9424c12010ffa7548110005fc7154d32007ed534c920005fd70cca21004fd73d912008df6710c51014f7e6554b30005fd76cc520004ef72595310e6fc64cc95007e7c650c521005fd7694530006fa6358021006fe6458530006bd43185401ddfc735532028fbe4050831005ff7250d3205dfd708854000fb46490510005ed7290d20007f4714ca31006fc41d8d20007f53294710007fb3254110005fd73189540ae7d40d9510006ff32d8121177f9700c520007de4358930007df7359132006fd64d8532006ff644c5301defd630c720006fd74d8930004f771595320af725094510006ef62085300bdf87059132005fe76c85301fffb30c8530006bf64d8d10006fd64189300b6fe640ca51006ff654c941006dd6390c21006ff7058a43356fe53d8943005ec7254d320cf6f5294932007ef7250d32007df630c5200bfef404c920007f54354710007dd434c5300267f5359520005fc7254d43297de404c931006fc71d8943006fe54d81320e4ff725913213ff44354510005df7350b32175fe73905201dfed320c7200077f655953221efc4318930006fd42d81510063d6599021376fc31d81430069e6458c210bded7298d202e7df404cb31006ff64185320bedd3058f200067e6598f20006ec624c931007fa314c1200e6fc64cca5102fbf4359320006ff6354942005fd72985300ddfd70cc940006fd6350d202a7df544
  | 21 => 0xd64ccb21005ff7250f2018ff671cc921007f543c85100077c43597200f6bd3059320005bc71551431afef324c951006fd6408730006ff70d8d21006ff76508310befd7058f20177ee320c52027fee20cca21005ff7355132005f97094930006bd73d911017ff8544c120006ff634c94000ebe76191100bfef204cb10004ef7648421057bf43551210065e6598c21006fe7558332004fd73d85421a7ef324c94108efd40d8d10006ff43d8910006fb4258032005fc7154f2031eff3218543145ff7350b31006ff6354520006ff65591320c5fc74d8132005ff7054d210bfed704cb20006fe764c950006fd70d89430067c6518d100069e6498c21006fe3058e211b77f5394730177f6310c5201b6ff65cc951005ff7655130006fd658c930006bf7259331006ff764ca51007f432907100e7fb40cc940006ff7058e42177bc4350d20004fd73d8b10006ff6350520006fc4158332147ef32509320067d654cb200fc7d7699720146ff32592320c6ff4258e42005ff704c93137fbc43d8543004fd73d93210d7bf4359232006f95458032007f5428c521006ff6350d10005ff7054b31006ff71d8953007ed428c720007d4714c931006bc6418d10237df5190d30006fe53582421a5fc73549410befa20d8132006fd54d8131006fc5058e21006fd62ccb10005fd7094d21006fd6498d200befd4058d20005bd739094238cff73595430067f65d9121005bd7408730004ff7259710006fd658ca31007cd324c520004fd7690730125fe73d9110126ff3258231006fd638ca41007dd54cc931177ef324c920155ff7655330006fd52d81311fefe7690f21007f954481100befc764c9301ddfe73947200fe7a50d81520cdfc7654d3219efc43d8931005fc7158d20004bf7458d10135fd7390731004fd73d9310004ff7650f200067f6590d21007bd545093218ff67190d21005ff7050a51007bd43085400cf7f5459532006bf6454910006fd6458520007ed744c920287ef52cca21004fd73d952024f7d75cc950006f542984321bfec544c9200ae7d30d9510036bc6459130006fd6388520007f9534c120006ff64d813222fde6550d30007de4394930005fd7094f21006bd6458f20256ff32d9530006ef62cc95115eff630cb10007f4618c530007ed424c520396fe43d81530c5fe74185320057d75cc540006fd54d89100d6ff43d8d42005f9700ca41006ff43d8f21007dd744cb310defd40d8930005f573c862118ffb3048530006be4018542175fc735052003f7c5294530005fd7290e51007f63148520006ff62585303ce7f53d8154005ff7250c2100777658c521007ad644cb20005fd76cca41006ff638c520006fd4358252007f543945100077d534c9500d6ff42d8d42005ff7359320004fd7690e52005f970cc9202e7dc544cb31007fa43c8120
  | 22 => 0x49301fefc63c8550187f8754c120006fd634c82103f7c6554d30006fc54d8d20006fd64cca510057f75585301fdfc7350b210beff5058b30007bd645513218ff7328c52106fbf4250f210077e54d95320c5fe74549320067f65509100ee7f5259732007bd6450e3235eff32d9543006fd6350e51005fc7650530006fe53d8940215fd7694b32227fb30d8930005ff7259530006f97358021006fe5458b3109fbe5450b31207fb3018530006ff7650d21006f932580210047f7559121005f97008730004ff7259730005ff7059532006fc41d8930005fe7690932005ff7650f20007ee6350920006fd4258332006fd65cc920005ff7050e52006ff65d9130006fd64585320cf7c754c95000ebf42d91101fefc4358f21007ed644c92019efe53d8931004ff7655321006fd62487300ae7d20d9510006fe70588310177452947100befd3058d20006ff624c9400b6fc640ca5139eff30185530bffa20d8132006fc764ca41006fe764c9210ecfe7694932006ff61d8132006fd638ca51007dd439453024eff63cc950007ed4258520006fe43583212efdc754cb31005fd7650f211c7ec754c920006ff6308540004ff7648730006fd53582320077d548ca51075fe718c5200ee7e65cc821006fb6348110006ff6350f213b6ff32d8953006ff7650c21006fd62585300beff30d8132006ff72d8d21006fd65d9132004fd7608730006fd7158d20007de4354930006fd62cca411b6fc63945400b6fc640c9502dfdc704cb310057f735525102ebc4159320007bd4390721004fd7318554005fd744cb210e4fe7690932006ff52d8132006fe764ca41007de43d8530007f83254110007ed42cc821137f431d91310c7bf4350932037bc54d9130006ff654ca3100ebf43d9110007f6768c51005dfd7088530006fd70d8d54005ff7250d31006ff5358b10004bd74989100cdfd7354932006ff54d8132006d96398021006ff6498532007eb704c920006ff6354d2018ff73158a31004fe7694d21004fd72d93100067965980210beff1058f2008ff2208c5101c7ef534c9201b6fe6394720006fd43d85300077765905101f6ff3018532005fd7218530006ff43d8131177fb324c1200c7bc4150d320073d5450a51007ef628c930005ff7254d10006ff42d8131006ff32d8151107fa7448110006fc7258231005df7358520007bd5450f21006fd43d8152076fd3018530004fd73d9710107fb434811018efe4358632004fd7690b3008ff5308c710007bd434c540006fe6098532006fd6350e520ddfe7618930006bc7159320004ff7058a531d7ef5250920006fd3258251007df6550d30004fd70d8d41007ed5350b20057bf42551210d5ff7350a32146fe6350b21004ff764ca41005fd7290f21006bd72d9110006df6390d21006ff53582311b5fc7350a51006f
  | 23 => 0x7eb724c120005ed7294f20005fc7150932004fd73185203e67f50d8d54004fc7650910006fc7058a31005fe71d953218dfc7350921057bf4250d21006fc7650931006ff6254530005fe71d8132356ff30d8943005fd7098a31006da6398021006ff648c9500c6fe64d91320dffa20d89300057d75cc520004fd7690f200c5ff7650932006ff7558e42004ff725943131efc3218543006fd638c520006fd63985200e6fc64cca21007dd4398930007dd6590d30006fd74580310057f755852014f7d6554b32007ed3290720006ee624ca31007ec714c9200befd5058b30007f76390510005ef7350b20087bc4150d31007ed4294520006fd4398a310b7fb400c94006cfe7690521005ff7050d52006ee6250831006fc764c950005fd739494003f7f5255130077fa2018530006fd655853008ff5208c710006fd5458f20006dd634cb10005ed7390b20006fd63907201dfec438cb20147ef32592320077d5454d32006fc41d8d10167fb3090930006fc74d893019dff74cca21007dd534c93029fdc744c931006ff64cc550005fd7688530006ff64cc921006fd6559120227fb70d8930006fd4358a31007ee6350b20007dd43c8530005ff7350a21006ed624ca31007e93248110006ff64989302a7df504c931147ef32591320067f65d9110006ff64c8530006fe768c520007ed544cb2018efc5358a31006fd43d8131006fd7458f20006ff764ca41005fd76c8530037be5450d30005fd744c9210067d6550832006ff634c5400073d5450d52035bc7459530005ff7050921005ff7454f21006fd640853002fbf4350b20006fd6350b10005ff7355131004fd70d8d212dfdc404cb31006fc6298530006fc3258241007f94348110006fd72d8d54004fd7690520004f970d9021007715154110007bd4350932005ff735532002fbe7399320037bc6490530007ed42ccb2001fbe5450d20005ff7650520004ff7058e410047f75586320ee7f54d89531fdfc73553210b4ff7650a321f6fe6358c21006ff7158d20006ff6350d51076fd201853003f7f5459530007f25148110006fc71d8930006fc4158d200deff405833215ff6434c71002ebf43d81420ee7c65cc9101fefc63c8540006bd648c720006ff74d8d21126fc325823108ff7308c510007bd4390521005ff7258231256fc32d9530007bd5450d210067f6518d10006fd74d813218efc6348550004fd72d8d4123eff6394d40006ff628c5301deff72d8132006fd4318951175fc7388520007f9644c12010ff85348110007fb744c120006fd43d8910006fd7058e42005fe76949320047f755911008efd30d8d10006ff7558b300e6bc64cc9100275f5394d200e6be64cc821006fd644c9300c6fc6459132006fd5458032007ef6288530007dd4354730006fe54d8931005fd70cc94103f7f545
  | 24 => 0xf7350930147ed32508321f7de430873018eff6394d21006fe71d8d42004ff7650a3114ffb3054930005f4714c9102f7be4050b31036bf43d9130007df324c540126ff6318d10376ff31d8143007df704cb31006f7624c710187f8514c120005fd739454003e7c65595300077c6590d21007ec624c930006fd61d81320beff4058d20005ef7258530007ed65509200047d7598910005fd7394930006fe7558031157be6455330137de63cca411e7ef434cb2002fae5450b20137be64907300067a6558021005fe72d8543004fd76c8730157bc3155143137bd74cca41005ff7354540005ff7254d32135fd7690730006fe43d8552006ff654ca21006ff6448530004fd7318b100ddfe730c950006fc63d854218dfc7355121005ff704ca510379f4250d300257e75cc520006ff634c92119efc3058e21004fd72d8d100c5fc7458132006ff64cc95119efd7690e21006fd6350520004ec72595310d7f4418ca41006fd74d8d51035bc7458530005fb704c530006ff6218543005fd7398a41007ea424c120006ff6250530047bf4250730006fd7358a41006fd6354520006ff63509100bffa20589300c5ff7459132004fd72d964124eff630c9500c5ff755513215ff671ccb10007dd4348530006fd644cb10006fd5458331006fe6398a41007f643c8521005fc7159532004fd73988210ecff7259532077fa700c520004fd7398b101f5fd760873019dff7388730147bf4350b30004bf7459510217fb309493008efd20d8d101b6fc639452024efd76cc95006fbf43c85400cf7f52d953235efc32d95431e7ef424cb20007fb70591320077f7559132037bf4150930005fd7390530006f47458432004fe7618d21006fd53d8930006fc7558a31006bd6454f20177fb305893022fdc5250d3024fef328c950006fe201853208ff5708c510145fd7350831036bf42d9130155ff7355330006ff624c9500c77c545513223fbe74cc94023ff7318c54001ebf4359120006fd634cb210deff40d8930005ff7454d21006fd635092002fbc4150f20007f77150e31004fe76cc910006ff634c941004fd70d8d54004ff7359540004fb705954308eff638c51018efc6348540007de634cb10005bd740ca510c5fe7458132006fd768c720006fd5258331006ff624c540006fd6498530175fc7358520006fd644c821005b57408510007f451185320fe7f305972002ebf7659320005ef7254e321577d655533218efc43d8d21007f7618c530005fd7294d40136ff32d9131005fd7290d50006fd70d8d21006fc4398910005f47154b31006ff53d8d20177ed7298d200bfef704c92003d7c75585300ce7f52d95321a6ff6394d4103f7e6555130004ff7358221007bd4350821005ff7050831006ff6250930006ff65cc9400d4ff7650832006fe7458f21005ff7054e42
  | 25 => 0x201604b81d808471f015008c00e0010000024000024004000400e003009000c01800c0e7888c00289700e000800408a00215a82424bc00680a000000a1cd000c01000000001540341c70258030042000000001000620b000822804c00d006801805800863201ac2b600a0ac012400000236a003401e38d00a1a3803a00a00906d4002008000001c0bc27e04606a80300cb0090000000000005800800a02b0130010074000061803c00000a01a000c00a000000800800048c04180080ac00f0d3801000601b00c804c02c030081010c00a0060048340002095006025811403800001540021f233a03080020010618000044088000004417a01700701e001204d00300c0118002032000000600000200680ca09f005001525404600e000c00202201e0004000002001805c06200d023004c000000008800004c00f1840020118b5f000001006a06100500280100080230040004002000800001a00405c001c00200200e000812e0050080020016027000002c04452b00100000121ab044000001a0e0000002c024003000009009e0150008be000000600d002000e4040080020004001001800854cbba010004c58e00e0210000134026003801000a00018200717be03b05580400c600308d01d8080015004800008a1900000330002001000000802001f000800c00005901b009019a00002180c400600b000000000219100000700000d9005003000400d001801c04004d00100000300630110000000005010800403a016000002017802300f019811c2ed00280040e20000020000014036003001400a09800b81c406607303c83d80080113e1005003009c0020018020000001800c1d800100600000065bb000806400e08a00000b15920ca00800cc074000004000001c00100780108a200500c817001e07b000000402c001003816d71600600280740062b400281441f60000032e6001400100080d09da00102d800c176003013801c1b60020038004bdc000005803803800101300f0002017000003800c0030000098122028008000c00404200000f039a016016000c0700790d1015c5a824201b800000200300e800008a0030010060058000001000410e00007401d05e4001008000c00001b00183c8d4600000b8000008014003803000a00d00c001000213d000060000200d01680cc062001000800400082101c000004c0c6001000008206700100780000030021fe001004508b80c807c013001002d3ca000001810401a00100a80740000c600300000000860000084002002008851c00c000001801000000000b81d001c00e013006000008433d805000000701a800800e01200100000060030180c5001a00200680c8002106098800806e0c12a4005801200002080300120390000034040002000843804601b006fe7158a43006ff70d8d42005f
  | 26 => 0x6800c03800305e807c00c00100000040020090078168008000001077c07a0980000404050001000000002800600400ac018006004800400001b0ae802400008200000e400c089001000419a001001000004201900600040a0027046802801401a00081200220000460fc021c00114180e000004900003b800000d00a800405e010003800c00c00300d80201d0000012006000600102a800000800d00800bc02401800480080360660030d9c03c00e07504e81d20011b4800000e099000001403611600580b002e00900081c800000701801f005600000080082d2003000046c00e001000002c0e000001a80280160002d6000400e010010007801000300100301d6021002807000e09700001580660c8001804403609e000800425c00000d8000020000000805c03a08a000838806a00101db3f401402b00b0000078065002800c1480af001801000c00a031803800200000380a800401b00282ec028025002819c000009001001c00e00004100d000a00200106dc020002467003c000018001001400200902702e000000f00280fc00000117d0068000009018801804600406200ac008018059800c03000800680b542800d00101f0048000001804c2f805a017802400005203c005c9700000230008012032003003c10e006078002c02407539c809c004007003801000402300000000000000028000006003004800000001d0230fc5c3c151000002000600400003c0016090002005c02a00503500240346aa033001400e0de0e780a801602d28d000404238b00d000800400a00b800c00000100381080000c30048220012356003009c008016006005003e002001001000001000b000002000e005027000200000201ec03600a0038000000010030000402603100480540080070010000070000005804000604f003011c2881c30a48044008000007800400e00301180a41020890080004000022207000082601a00000100000020008160016015000870807200000480080d40080708010000002003008c036019000800002002100300000b400000009a01e60120cb0160030000000000400e00700f8018008000000004006601700600240180050010000060000000000402e002000000000000e000802c620002000009c09a001004800c01000f0080148002007003000c02a00900000100080000008010002000003003018a00300380c000007d0010018004003007011000a0070020008026000003003400c28700b00004c2011008800800055c1b2804c0020050000008ba800700982a4004063083000006207b00100fc03a00b00280740a203101d002001c0180098784000000023000002e002000000037406f028800c0020000be813c0ca02b0000258000060000800c51404800101f8002000001003806616b001801019600001680500
  | 27 => 0x4d03201440171a50054032027000000000a00007f8bc4080003018000001203e002000015200000000000020045d68218970053002800002a01d000003801800000000400140020048170004000007822c00000005a00000040ab0690000120023000000004c001014043000a01300100000020171068030006092008800400c04602a802c16c03700000c82e600400b801c04000b000000802405700b013001200600000ec032001001008800400a0000000b680000018004044000016001803200202f000414e003009000800200b027818c00401101b804805c03906b8028000ce3009000401c00001c002406cad3009803401400e000803c0e4040001800000c0280040030004049000012023c00700180080886240838214000000016000011001800a80000040e600000581a21cf000143000e0900
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xd7a65dc154cc155cbea8b1e65288023fe1d32582410047f438c8b126000c7d75592624c0019ec6438aca990032f5957498930007e4a9a649824000eae6458d42c80015bb07b2a65108033bdcb624c5500067d3a2e8b006400af980dc7604c8013ef0e99482880033761f638c520004f7c12ed18a4000cfb63dc14344001f9287b9260900a73718f73549100067b40ee4b006200eb464dc5644c80157f08b2ec498062b7219434c9310047ec30e2a9e4000beb8050e32c8001af6ebb82c8990035d5d5430851032fb92826528a2000cdf86dcd6148039c78c8aa664a8003b350c624c9304866fb82c69962000c7f75591214c079f1b0732265900bba710f6350d200053e42ae8b106200cf5861c5654c8014ff0ab20c498003ad18f648c5101de7b18ee0b106200cbf435cb644c0015bb07a16c6880031f18d75085400047ec3c86b0642009dd83dc954cc851d7286a12c019003375cf63945400071eaa287b12a000cf6815d832904019dae5b16c2a18031fdd96550f2017fcc3a28698240008fd80dcd62944011fb0e20ac790803b6d8d708c5200047fc02ed2106200af48650f21440014ff0caa2a599002b7e0d65cc9200075c3a082b006400c7d751d560cc801a7aa9b82a6a10033b5c87258231005f940ca6902202bfc7824c931c4001bb286b8043980029fe15648c93218d6f41e81b1a42008ff805c86154c015df00b14841885efa60e324c12000779434629022000dd4535cc214400197eec39ac990002bbe09644c9300067bb2ee2b22642bafb805c560cc85ff50e8a1260900038f9926590f200047f43887b024200aef8650e32c80ff5ef06b08c2981f7dcd0951541100047f43ca7b024200cdf30dcd60884014fd0ba0ac59806b8f191548c95017fcd2a2869824000ced72188614c0015ed0329ec488002bee094358021144f6c36e4a1c6400e3f54597644c001d3f06b24c7900023fa1b7255131005f9c028790a2047d3d435d432500019eee83a2c2190eeb720d6458f2000477c3ac43126000add839d163480015f70f21ac0108029fe1574583320055f408e6b264000aed82d0560cc8014fb0a324c4980027e6007154d2017ddc422ea9824031cdc63dcd21480575bf0eb1e65880032fe1170d895315e7cb1ae0196202edbb435c243480011fb07bb2a8900032f90076509310063fbacebb12602ede9325c332480013d90e992a2900c7a710d43586320053ec28c8b0a6400d6f205d4635085397ae6b22a5988035cdc95154110006f4412e118a4094d7b545c251480011ff04b86c6aa0033bccb725823114756a1ac4a106200ced7298a614c0011fb0e2a2c1990cebbe097158b300053ec2886b0e4000c7c855c36250c0197b0fb266488006eda0673d9110004fac10e2a1e422ecdc635d8314800157908b2ec4980023f61c43d8520
  | 1 => 0x8e2b0ac0990023fa1b704c93100737996ca992429dcbf7059253c80011f90cb9482980023f61f43d85201776b38ec618a4000cbe405d832904377d704b9a40880023fe1d43582520057cc00a6b044295ced70dd932c80019790eb206390016eb60873593200047f43e87b024200d3e525d331540011fb0f320c498002af21175583320071f282c8a9662009f98790f20480015db0420ec6900bb2f58d74cc5200065f3b4e7b22202ebd88358530480011ff0ea12c0188037690d70c853000574c00c4a126200a7c85591624c079f1d07322659000337213764c8320047ec38a0b146200f1d5450d524c001daf0c9926388003b9ccb628c510004fdc02e728a603bdce734ca51c80013eb0038aa7908bab7a0e6558d200d65e326e6a1220008ff87594624c0014f90ab26c4980a32f50f7650b310076b40ec718a4000cef621c5324c0015f5032a2c019062af21165591320067cb844030a642ed79305d731480017e300194a3880023fa1c43587200065f2a6eca166000add8399663480011ff04b9ec8880033ee0176949301b65fb1ae8194a200ed563dc54308401b7286b8042a014bf1481324c710005f5c02ea9924000cdf7650d214c0495bd06326c6880033b48172d8f1000757a1ec4a126200cfb309da414c0519b8c7b9a84a80023f61d6390720005ddc22ea9824000d7574d9631440015f100b20c299003b958b71508310067b990e2b2a6400cbc41dcd64c80019eeed21a42108027d61f32907100047ec06eca1ca4008fd87105608c8b597ee0b2463900a2bd60d42984320057a40aec99280008fd861c5548c8011ff0ea1cc5288038f15365d91301dd6f41e84b1e4000d6e655ca43c80013f700ba26510816af608735932000577c12c810a6000cf581dc9600c4a5f94609926290003ad190714c9100047ec16ecaa6606eee9329d1600c8011fb0c38aa8980033e993704c9200047ec3a6430aa000a7e85d0560cc8019bb0db9a85990febba1c624c9311471ea1acaa106400af68190f60484019b8eca1a42980b33e4c17690b300c4be43acaaa26400abd84195604c8513bb0db9a85990029fa1b43d9510006ebb9ee2b226400d3d54dc15350c017a902a9a6498802fa602714c920005b6c1686b2e4000bf180144614c88fd7686ba2c0190031fccb755913246e5fb86c8a9a20188fc87591614c8017e30720a40880025f61c43997200074f418c831a2000cbf8759231c805d9b8e6b1ac290002af2195450d210057d434a69022000af880592614c801b7660ba04298002bee1d545803200577c12c7194a2b1d9e54dcd42cc8014fb0d2a6ca990bb1f58d75cc5200055e432a8a1242008fd87d0c624c001af2cbb828790002bb60b63909500047fc3aa7b128000deb721c1644c80197ae83a6c6880eeb7a0c71d81320047fc3a84b0462a7
  | 2 => 0xc7150b310066ebb6c618a4000cf5631c543c84015bb07b20c6908a3750c5744c9310063eaa2e7b12a000afb8654d30480013bf06baa85990031f21570d8953006cfb9a8690a80009df87596434c0018fecab94869086ba7191438c932007e898a64a8220009ed8794e42480019bee6a1ac488003b9a07628853000677ba6c49926268d9c745d1320c8019f086b80c4988023f61e43189510066ebb48610a6000afb8050f604c84d9b8e6b1ac5208031f5d764085300047fc02ed29c8400a7f855d932c4001bb286b8464980023f60876551310075da1e81b026400e9f40d8d43485098fae1b2a64880c2de215744c12023e3eb1aeb98a8063eb943105600c8015f3013a2c6900023fa1f4158d200057cc0484b04622ede5315c8314800199ae7b1042980023fe1d6390520006bd982ea10a60008fd87cc9609040197ee93a2c7900023fe0973d97100047ec00ecaa26418abc84d95644c871ad8ea992429022b6e1937050d103566f31ee4a184237dac744c9614805db9ce699482900023f61f41583320075a320c720a2000aed8210e62440011ff00bb06520802b760c74d8d210047ec3ec7212a000cdd63dc143084011fd0fb22c4980034f5d254d953215f74994e2b0064008fd8758e41c84d59b8c7b9286908033b5c862185430047ec06eca9c8495dcd73d8a624c08bab8eaa1ac29800337d8e71cc9200065e420eca1a2000af48158d61480015bb06320c6880c6bb60b634c9210067db22e0192a000be7815d13248001c7aa7b22a4880027e6037350530176dc982e998a4000be88750930480015f50c192a08802efae09614c1200055ec20a4b1e2000af587d86614c0016f70ab0a6090002bda0443d89100063fbaac6b0a4000aec8258d434400197e86b96c888002afe0973d91100047fc02e630aa400af980d53604c8016f30021eca880027be1d420c7200047f43ec498a60009f48750d210852faf6a7b82a8900d33718f7350520006f4412e018a4039dae54dcd42480015bb07ba6c6908031f5d3654c9100066e982e7b162000be98294d204406d5bf0eb1e6528917571d543485300066fb1ee4a1a4200d9d54dcd42cc8014fb0a3a2c690006ed20573d91100067ab88e3b026400cdd734c86154001bd484b8062900c71fd4d7298653176f918ae018a40008fe87d91214c001d7286a12c010a33974c36590d1000577c12863122000a7d851d3604c87fd3887b1a87908035d551710c95018cf6c14e3b226400cdd7350c62440019f660bb042980029f2156158132236af3ac8731260009f5801c5544c4495eb0fb0c62980029f21574583320067d432e0194a200cbf421d94348401c7886b2ac99018fad50c74584320055f420cab026400edb73d8d20440018faedbaa6528803574c175d85430067bb8ce3b1a8400cbc8759231c80019e
  | 3 => 0x5b024200ecd6350b32084013f301b92a890002bee0132582410057cc04eab1a4000cf5631c553c84017cb0420ec2990029fe0d54d8950004fdc02e710a6063af7831d1610c801d9b05b1a6490803575d6430853000676b2ee4b0a6000cbf84dd943084c7bae6438a86988039755163cca510057b40ec9b0a6000cfb325c3648c4015f301aa2c1108029fe1564d85300066eb9c87b12a000c7c65dc9654c0015f309992c010802be60374d8d1000576c16c6992a044aef825c1620c4018fea6b80c2aa0fba7dd16350c2100677906e4b046200af980147604c8011fb0fa9ec49811f3d58e710c9400066fbb0c718a4031ade8319363484011fb0fb2264908033e58d708c5200057b40886b0e401ccbc64dc9434c8013df04bb062900036e19372541101666f31ae7214a2008ff865ca41cc0015f700aa2c1190029fa1672582310066e43ac6a104221f735394520440011fb0f21cc488003b5e116348421004fa43a8498e2000cf7719c56290c011fb003b286a88023fe0d721854000577c12c93126000cf9865c032904019f6c4b8462980023fa1f644c5200055e422eab1a4000cfb805da424c0631fb0e20ec6908023f60376508310047f43ac6a1042009f980dcd424c0015bf00b1c86108bb7c8c570cc5200047fc3a86312a000cf7631c5324848fb3ce6a1842a00029fa162058a3120f4e21a87b0a6000c7c525cb65c40019eacbb8ac8990b7ead0d42c812000576c16863126200af481597604c8011fb05bb2a3980023f21d43582210047ec3ec998a4000ed97390d60084011fb0fa16c68811f671cd4348540006eab9e6528a2000cf962dc142cc0015bb07a16c099002fa60e424c1202fedc202e0194821c8ff865d332c840167f04aa2a6a1803ab9926350b2000576c1086b064200deb74dc132480011ff0eb1c8528802bbe096390b100067c322e01962000cdf7350d61c80015f301b2465189abaed0f4258032005ea40ae09926200af4815d162cc001ce8cbb8aca990baf520d618c5200057a4328790a423ecdc7358d4208449bb486b8462980033bdcf62885300047fc12ed18a402eade839916348055b9864baa86990029fa0c64195100067dc04ec10a60008fd8794d60908c75eb063a2c2192bf6b9537250d320047f436e6a922000af5811886150c0197ee93a2c199003bad8d4248110004fd43c829824047cde73d8e51500fddca41b1462880723fe1d43189310047ec3a6430a8000af9808c9608c4599bcc7ba264108023f6007654d420047ec16ecaa66200c7f655cf64440b5d6e20b2463900bbf290d324c1203575aa1e84b086400a7f85593604c8635bd0620ec690802bb60b43d81321666e31ee89924200cdf8758f3290401adeea992429000337d8f73485200071a320cb20a2000d5f7550d214c0011f90ea9ec4880027d60
  | 4 => 0xc847bb5ca9b9a859000337dd3634c9210047ec3e863126200cdf76dd1320c94db74c9b82a9980bb5b4c975cc5200d65e326e6a1242008fd80dd9428c401ae8ebb8ac899003b3e09634ca41006eab9c8610a20008fd8794f62500019bae9b1e64908035e551700c95000577c12c91926000cdd7358e61480013f700bb287908032f5d764cc910006bdba8e0b226400ced625c2420c44df1864a1a652080375dd0714c931006db200e2a1242a2e5e65d96434c00197ee5b9ac990002b7e19704cb310c65f3a6c9b026400c767619631484011ff0e990c2a80bba710d43582320066eba2c7990421acbc64dcd424c0011fd0fb2a65880023f61f654ca41004fdc02e72126000af9868c530480019deca392c2980037a909708c5200053f42e82b1a4000add8310763440011fb0e2a2c6900032fdd274d8d101474f31a86a1042008fc8750d61c80015eb053b4628809a3fe1973907210065e424ed21a20008fc87591214c0d7dd2652a2c0190039d18c658c5210053fc2ae2b066400afb844c96008451d38c6a1a8490802b7e0d62cca4100576c14e9b026400a7e85d07624c0015f700a1ac1108026f608715514300677b14e33126000aed82d07624c0019dc87b92c688003bcd85709853045e3eb86caa1a2000e6f7659532c805d5db05382c4188023f61f64c85300055fc22cab126000dd5734ca41c4001abaeaa1cc498002bbe09654c930006d6aa6e4a1a6400e3c6419543484515eb06a12c2190023f6007654d210047fc3ac830a6000cdc631c563480017e700a1a62880027de1d428c5210053e432a8a9a6400adf8358b32c40019dae4990c2a00023fe1d64189300065fa1aed1948200aed829cd62904511fb0db9287190023fe0d701855200775b16e09926000e7463d963148401c7cc932a87900033b5db62885300069eaa6e6a14a2008ff825cc61550015db0420ac5980027e6007150d200071f29ac8a9e4000c7d7459532c80019bac6b84861085f7a5cd32c81200057a4328698a2026cfb635c0329043597cc9b9a84108fb3e4c1760873000677902e5b1e2036de9325c03294401c7ecab9ec8880033b5d9420c520004fcc04e329a4000cf9655c032904019f2c7b82868826f974c16590f2000756a1ec4a126200cdf76dd132cc40157b083aac5980033e991700ca51004fac10e2a9a6247eb9435d1600c8013db01b9286991bb3798f7050c21005eac188230a6400a7e85193604c801ee484a8aa088002be6003218550004bec388632a4200cec63dc9514802d1fd0fb1a849092b3e1db754c1200047f43886b1220009fb805d1324c401d3ec6a1a84908027e61e514c120004f6c16e6aa46400af681d0f604c401f8a6530a62900029f21574580310047ec1eecaa26400cf8635c021500019df0eb1465188029f61741d8d200057b40e8
  | 5 => 0x9ab7e1d63cca41006ceb9a8610a8000af9801c96390401ae8ca38aca990632f991744ca310067db84c0b14626aaef825d162cc12bdd0c1b92c0990025f21d544c9500063f39ecbb224200cfb301d9544c001adeea992c290002ee60273d911012eda322e720a2000add8310563c8493cf2a6baac0190039bccb654c9100074e20ec6a1a4200cf980dd9424c08f9eac6b8864a00bb6b4c974cc5200047f43c80b1c4200eaf3259132084019dee5392c720802be61b40d81320071fa1ecbb22421acbe64dcd42c80015f30e20ac0190033e993705913218e6e31ee690a803bdce734ca41c80fbee084a8aa0880033ddd943484210066fc26e6b122000afb80593614c8237b706b8a60900927e60271d91300057dc02863122000cbd741936348401c7aa8a1ac1288035d5d0658c51031e5f3b28720a6200cfb805da4148039978c8ba66510802bd61841185321ae6e31ee6a8a4000c7c7558d61480639bee9b1a86908c7671cd4350921004fac386520e2000df131dc95044001aeee832c62880c7a7dd36350d210066fb98e2b1a4000cbf425cf64484e7bae6438aa6988032f1077650f200047ec3864b048200add83dd363440011fb0db9aa290002be60075d8132005bb4088632a42008fd87153624c0019bee8b1a64108033ecc170185322ce6f38ec618a4000c7f7559121cc0019de87b92c6880037acc07258530005ecc1cc298240a3d7865dc1534c001c7ea92a6c0990033ddc67158332006bd986eab22602ede9325c031480011fd0db92869880337a1d6350821005f5c1a849824000adf835923148001ada40ba8c6a1002bb60843d8520176e639a64b0a4000dd7535cc21440011fd0db9a8490802fc20573481100056ec1e85b1a4200cfa865c032904014fd0da18ca880033d191710c9500063fb02ea3128600de4321c5644c801d9f04b1a65288027760c71509300047ec36e4aa66000cdd63dc943084013eb0038a8790802f5205744c83223ef898ae018a8000afb805d163c840197ca83b28688002bde1d61185300047fc3ac990e6018cbe74592614c801adae8b2a65900029f61771d89300047f438c8b0a64008fd878c9609045d5f301392c01880337a137358910005b6c108732e4049d3d535d032540395bb07b8ec4a199fdc94332945101766e39ec6a0a4000ed58458d21084015df04b1a652080337dcf63505200065fb2ee8b0a4000af582185314c0a9abcebbaa64988037a50b704c9200053ec28c8b0a6000ed46358631480013f700ba26518802f5600714c9312467c3b6e89824000afb8050d60944011fb003b264a88023fa1c51d89301dd7dc02e4b0062009f5821c5434c4019eee338ac5980023f61c41d8d200056f430c6a1a42008fe87901620c4019f2e1304c2990031d1947159532006eca1ae190a6000af98010d6
  | 6 => 0x8e77192e530c86008ff825da414c001d76e820ac0190031f595744c821004fd43ca29824095cef70dc963480011ff04b84c3218031f21572986530047ec06ecaa642008fe8790d62c40011fb063b284a88031f5537258e510053ec2e82b166000cfa835c061548891ff04bb06290003a758d43508212eeaf3aeea99662009f980dcd52440011ff00b90c2aa0af7690f704c5300057640ac4312608be5d30d9543440d7d6e872a2c21911f371cf63549401463eb9acaa1064a9e5c7558d3294509cda41b2a64880023f60f72595400053fc2ac8b126000cde87d8e3148031d5cc8a1265900a23f61f63949420057a40a863126200c7f7459563c8089cbca7a9ec4980032fd0d72d9131177e218a6498a4000ed97350d600846d9bee4b1a65288fb3b1d8714c9202cf6a886c718a4000cef20dc9600c48babceaa1cc4980035bdd77259132005bcc0064a8aa000dce431c9614c001d3b07b26c6880031fd957290d100053ec2886312209ac7d7059543c8001c7c81b2a84908027d6007154d31115dd42064a822000cfa305da31480015bb0620ec099002bde0161185320053fc2ac9b126000ced74189324c45d9ec62bb662900027e6007155130005bcc008632a2000cfb645c0214c001978c7ba2c290002bbe19534cb2000e5ec3ec918a20009f7865c4329044d9eec6b8865208033ed95700cb1018e6e31ee690aa02ede9325c3314805d5bd07a8ec69005f7a60b704c9201eed7326e6a164000cf97088363884013db01b92a69900337dcf63549400047fc12e1b1a826eebb439d1600c801b9ee6b1a8590003371c3764cb31006af982ea3128600c7d75590214c05db5e86b9486900023fa1c5158b300076d39c86b004200ced72d88614c0011fb0f212c0188bb37dc3630c5202fedd202e01948229cbf7359152cc40197908bb48298002bb60b43d89310076b21ac230a6086cbd70d9332440014fd0c21eca880033d5c471d893000577c32a699240008fe87d91324c4011ff0ea9ac190803abe1162508312e6ce3a2e89966228af983509600c8011fb0fa0ac69011f67612730854000677b94c4b046200cef641c9614c06de9864a9a65288c2de215614c1203575ca1e84b006400adf835893294401c7aa8b1a8528802b760f65cca21006daa18e2a166200cdf7358d42c8001c78c832c8688002be205745803200576c16863122038b6c855c532480017ab0628ec2990af379cd6390b100d576c16e3b1a8418eb4644ca41440011fd0c38a84980bab7a0c54d8d200075ca1e81b0264008ff825cf64c4055dd264aa2c01918ebe60c41580320c55e422ca9926000aef8258d32c40015f5033a2c0190033edc23058e21006ecc02e610e602ef984350d30480011fb0f202c418802fa60a434811000577c1287b12a200afb8055160c84015e902b2ac29
  | 7 => 0xbe541d94244051b9ec5b9a84990033e191700c9500053e42ac8b026400a7f855c56290cc75f70620ac01910b3e4c17694b30004fac10e2aa642249f9809c7624c00179f04b2464990027ee017290d20586d72a6e4a1c64008fd869c653480015f308992c0108023f21d43589101466e31ee6a122000abf86551428c4018faebb10c4a18031fdd564485200063e196eab162000c7e76d954344093a7aa6ba662a800337dcf63545200057b40e87b1a2000cbf749d3604c8015bf00b1a8610802be60043d85200075ba1883b0a64008fd87105600c8015df04a9ec4a08039bcc9654cb20006f4992e118a4000dd4855cc21440679d8ed38a6490002bda06645853244f1f286c8a922000adf865d132cc40197aebb2264880023fe1d61d813218d76c14e2b166020faa5450920440012fb0e218ca880023fa1f42d8d210065f426e0b14822efca438c930480011fb0fa0ec0990029f61741d8132006ed21ae010a6000abf845c36254c015db0420ec0990023fe0172986530065e422e1b12a600a7f8558932c40019deeca1262900032f90f7650c21007b8192a2a822000ed7635863148001c7aa8a1ec0a90032f5d9438ca410065eb24e329e4000fd0738c520440014fb0ba0ac199003375cf32185500071eb22cb21e4000abf84595324c001d6c62b2063900037c185708c530004efc3a8610e6000add83d476348001daf02ba2c610802bee0153d8143004fb434e321a4200aed8718b32544019bce9bb264190039bcc9654c8211fecf39a8720e4200dd9435c2314c00197ae83a2c790003ab50c62509310063fbaec690a8026eb543dd1610c8010fd0f282c528802be205755803244e5fb86c8a922000de9425c25148001c7aa8b1a87288023f61c51d893000677c36e4b0a602ae7953551600c8015bb073a2c7909aabe60f42580320047ec3e87b126000ced724c861540015f30a20ac0190db3e58d700ca511474ec24c6a104200f713254550440519bce7b1ec2a1002dee15744c12000762a1264b086400fc9434c930480011ff06b96cb208037ad89708c9300047fc3ac918a4000cf8635c24148159d38c8b2464990031f1d965551320055ec1c80b148200e3d7359564c8001ba8e038a64988033be09760c5200057ac30a3b0a64008fd87d96329042d1ff0ea1ec4980031fd97705092100677bb0c510a60008fc8754f60508011fb0c38aa9980023f61e301853224fa7992a7192a000af8865cd20440019baeca1842980031f1457694b300057a40ac8b0264008fd801d94254401dcac438a65188bb9794f5358d20005f4c04a6a124000f1d5454d434c05797ec6ba065880032f5d074d89301463eb9acaa1662008fd87d8a414c05dbcc62b9062900bb7a4c1720c52000576c1086b1220009f583dc5420c4015ed03322c2900023f21972945301
  | 8 => 0xf21ac1290033ddc67158d20004fac3c8790c4200aee87189424c401b7660ba4c498003735cd32985201fc7f430e2a126400dad54dc9438c8011ff00b98c2a1002bda0765d85300071fb9ecbb222000c7d655ca43c8001bd701b9a84900029f2195454932006cfb26e6a126400a7f85587604c8019bf0eb1e65880033b5cb62d85302466f39ec810a6000a7f855c36250c017e102baa4088002af2195450d3100577c12c6a1a20009ed80dc9438c831978e8b22c099002bd61a43484210057dc02e8b166000dd5831c5654c8014ff0ab26c2990033d0c476509310065eb2ae998a4000af980d49600c4011fb0e20ec4980023f603764ca41004fcc06e6a8a6000cdd7358e41c800197e85bb287900fb3718d73085400047ec38a2b166000c7c76d9643440015db0420ac6900023fa1c54d81320057c432a8902202af4c32551534c8015db053aac6900033e9d37058d200067db84e0b106200e346519231440011fb0f202c518802bbe097358a4100576c10c83126000d7b855c03294401b9ee731a8590002f5205744cb31176f5182e418a4000de772dc5644c89f9dae1b1442980038fd0d65593200047fc1ae030aa800c7e63dd521480015eb012a2c2190031fdd665581320078eaa2caa1a6000e3e4059542cc401c7acbb9ac990002b76037458c2100576c16c7192a076ced32dc965cc05ff34c8a1a60900033ee1b70591324d72e982caa1e4024af9809c560cc88f9f0ecba260901836e103704ca411767a98aec18a4000add839d163c80014fb0a326c0992976e9937050b3042d77c12c710a40009f4815d5424c8018facab9486109a76719373509321fe6f39ac720e42319f586dc5328c4015bb07324c7908033dc41768c720005edc1ac29824000c74651c53248401ae8cb38c8688002fae01544c92000577c1286312a200e3f745536254c013bd0f21ac298002afe117558d20004fc43aa89824000cfa435c0624c4ed79f04baa6598803575d54308530006f9a02e21928000cbe54dd943c84633db0538eca990072f61f6418d101f6ea180e29926200aed82105608c8593dd0c392869900337dcd63585200047ec3e85b1a4200cdd651cd61480013f700ba264908032fd957498930007e898e64a822000cbc7498d61480019e882bb065208af6d8c5740cb100057a4328698a4228cde63dcd42c807f5bd07a12c7908038fd976450d210047f43c64b046228dce82dcd424c8019daec9946290002bee01648c93200676b9ec510a6000e3d5359251c804df2863b2286988032f0cb745953000676c36e4a1c6400eb46319231440015f106ba2c010802bbe0965989300057cc00e3b0264008fc8750d6294401cdeecb2a85900023f6027690d510066fb9ac6b148200cf4621c5534c4dd5f700ba2c1990abadd0d54584320047ec16ecaa26400c
  | 9 => 0x7388520176f5192e018a4005cbc8759163c8001d38c8a1cc4980023fa1f435891000577c12c71948228cdc635d132484019f6e1a02c7908033e5c07058a3100576c10ebb126000cbe715cf644400197ec8b94a6880027ee017294d200047fc3aa6b04843bade8399163c80018faeab266290003ad190715913200676b946430a8000ced74d89324c401c7eeaaa6c6a11ab7394f7250e321267d182e130e6400ced764ca31c8001f1ee8a1264190eebee0172583320065fba4e8b1e42008fd8710c62440391f90ea1ec49890b3718d739494241e5eb86c899220008fe87d8d21500015eb0339ec4aa002f5205648c932007f0994a29022000e3c73d9764440019bae7b1ec2a10023f6187150d200066fb9ec6a92206eeb9439d1600c801ce8ca38a6490803755cf329071035f5da1ca8b006465e7a504c96094471ad8ea992c290147ae90142580310057dc3287902407fbd783584614c01b97ceca1c8290802bb60b654ca310063f3b0cb21a425db5c855d132cc46d9bce6b1c8528a032f5c164947200047ec3c4130e64008fe8714560cc80157f08b8ac1990038f5536354942004bf43e64a8aa000de732dc5644c80157f0caa287190032fdd274d8930006f3b96e2b2a64008fc865ca43440015db0420ac790002b760c6418d2100773a1284b08642eadc8359163480019bae9b1a649080379cc871595320047fc12e130ca6009ef825d5434c80157908b2cc4980031fd9375485200047f430e2aa26000cf4768c5214c0558faa7bb2a8190033b5907258530176e6c10e6b0a4018cbc74591614c80197ec7ba2c290002bd20532d81210057dc22e6b004200af481591614c001d72e9a06c09911f1fd8d75cc5400063eba8eab166000c7c65dc1654c83597cc8ba465188023fe1973907200067c3a6e0b1a403bdaf435ca43c8001d3e85b1a86908037cdc7705913200576c1687b1a4000bf38050e31440015bb0620ec6908023fe0172986430057bc0acbb026469e9c64dcd644c801daac7b8a6588002bd20565d91320074f41ec831a2000cfb435c0624c4011fb053b482982772f5c16494f200057a40acbb0a6400dd57350c21440018facbb8285988732f1937250d100074ec22c72184200c7f655d36348401adacab948790002afe1954508310066eb9a6430a802ee5c53d8d53480011ff06b90c2aa0023fe1d64cc52000676bb28418e4000af98010d6244141cbccbb2a8698002afe195450e31576e6c1ee4a9a6447c7d635d432500015df04b2442980035b9977350b2010fb83aca29022000d6f65dc9534c8011fb0e2a6c099003375cd43d89500067d996e0b226400bcf835d132480015bb07324c69010bd30cb6554d323fe7ab84ed18a20009fb805d5434c8775dd0e3126498002bde0154584320057a4328718a2000aef82596324c0011fb
  | 10 => 0x32e4000af980d49608c5118fee1b2a84880031f5d56408730004fac18e2a9220008fd87d0f614c0d579f04ba264190029f6174158d200053fc2ae8b1e4200add8399263c80017cb04288c2990033d9c761d81320047ec06eca1842009ed80dc9538c8011f90ea12c018803371d3764c8320055ec20eab106200c7f7559161480011fb0e20ac6900033e60d70185520066fb9c86b1620008fd87d0963c84015db05b1a64880bb798c572cc5200053ec2e83b126000cbd735cb64440015db05b28c4980a3b94c56250831006f4402e418a4000deb72dc16348055d7686aa2c019002bbe09638cb102cfe51846518a4000a7c855c562cc063f2886a1a62908023fe1d650c9400047ec04ed29a4200aef8654e324813997ae0b22a79006aaf211658c93000576c14e8b1a4000cef629c6324c0018f90ab90c2a98032fd0c7650931006eb42ae610a2000cf9645c031480013bb0638aa899002bbe0971583320e65e326e4a1a4200fd3738c520440011fb0e20ec099003b69cd43580210047f436e4a9a2000db4415c46250c0157b08292c018802bb60a7058a31005f8c1ca290220008fd829da43440014fd0c218ca880023fe1d654c9400057bc0ae8b1a4000cfb70881620c40197acaba06588002b7e0d62cca5123e7bb1ce21928000c7f65dcd42484011ff06b96c9880029fa1843d952148e6eb82c79962000af980149600c45dbb30039ac2900031f0c975d923100576c16c831260008fd87d0763480019bb0fb1c86908023fe19729453018e5ea1ae530c8600af586d04614c8011fb05b82c7208023f61f650ca410047f43ec4b0a6000ed543584614c0019f700bb48298092b7a0f42d8d1000677b12e1992a200aef865d532c80015eb0ba02c2190023de1d61185324471f206caa122000cbc40dd942cc4019f700bb04298002fc600329071029ece3a2e89926200cdd731cd62904499bce7b1c82880732f19174cc9210067d986eca12601c8ff8750e628c4014fd0b382c418893371cf63549100057dc0287b02a200afb8050c624c001bd2e9b8264900029fa1464589300047f43e83b1260009f5801c5434c4014fd0c218ca90802bb60b51d89300055fc22eab066400c7f74d97324842fbd10e99260900023fe0976907300078eaa28728e6018abc845d932540019f2c8b8042980032fa117690f200063fb26ea90e606beb543951610c801c7aa9b1a86a90029f617644ca31006ebb98e2b226400eba74d03604c8015f30028ec6900029fa1464d8930004dfc3a8610a802ebd88359130480018fcedb2c86909275d54d710c9500065eb20e2a9e402af9431551434c401d3d06326c6880a33798d744c821214f7430e4a9a6400cdd641cd614805dbd260b9662900023f61f64085300065eba0c9b026464e7a500c960944011fd0e28ac6900027e603
  | 11 => 0x4c801bd661b92c2980037650d70085301def318ae418e40008fe87d49608c401b9ee6992c290003f250e324c1200067db84e0b146200abd84dc7604c8017d700b2264900033e19370591320071eb22caa1e4000deb725c530480015bb07a12c598003375cf6394942007b9192a2a822000d5c75dcd644c801c7ecaa1c829080337e13764c8320043f43ec4a8aa0009f9801c552cc04d9bce6b1cc520803755d0714c9310065fbaec89922000dcf7354942cc8635bb0fb1c86908032fdd26458f210056ec1ec49928000cef769c532c8001b3b08b9842a00732f9937250c2155f5c20082b006400af98010f62440019f6c8b806290002be60271d893000676bb6c410a6031cde43dd921cc0011fb0eb1c82900038f9cc65191100055fc3286a1042008ff805da53c8401c7ea92a6c690002bee0132d81410066fb20e6b0a405bdd7764c931c40019ececb946290802af21171583320067b3a6c330a6400af481589614c0635bd072a6c6908032fdd264585320077599264b004288c7d70d9542440019beecba265988723fe1974cc82117fd5a1a84982401ceae6450b32084019dce5b16c2a1803cb55142945200047f43c86b044200cbd65dd1614c0018faebb266290003f850a31481100e65f322e99904200af4864ca31440011ff04b80c2aa002be60254580320067ab88e2b1660008fd86dcd54c84013ef0eb08c2990ef371cd6350b200057cc0083b1a4000cbf731cd64c80015bb07b126588073ad19332905100071fbaaa9b128685cef70d8b32440019bec8b9842980b3e30cb6450d324c757c12c89964000ecf8258d32c40015df00b126518802b76036390d210063e39acab264000cdf745c163084011fb01b92c728802bda0643589100056ec18e9b1a20188fd86dd132084015f70f2a2c019002f6e01744c832005f240ae899240008ff805c86150c015db05b1a64a88031f5d16598f2000576c10e8b066400cbc431d94344001dd704b9ac010803ad19363905100073b3b0cb20a2026cde635ce41c8001be0c3b82629800373dce5250b3200577c12c6a14a200af881551600c801c78c832a86880023f61f64cc9210047f43ca7b12202aeb543551610c8015ef02ba2c5980027761e43985300047ec3ea4b006218abe86d91644c801bd065b82c899003a760c6418d10136f4992e01948200cf965dc1644c905ee4a121ca2880037650f704c5300067c41ae030aa400cef72d89314c07dbb6c0b9842980033bd97725853023f6a18ec698a8026cdc635ce41440015db0421ac39009bb3dc9634ca41006eb180e299262a6dbb43dc154cc04d1ff0eb1cc5208023fa1e42580310055fc22cb3126000e3c641d5644c8011fb0fb1462a00033bdd8714cb200071eaa2c4a14a200af681d0d63440014fb0a320c4980032fdd264581320053ec1cc9
  | 12 => 0x33b5da328c52000766412c6994a24bd5e7550c21cc0011ff0ea18c488002b7e0d7458f200053ec2ce3b128600c7c855c86150c0197a86b90c2a00033b5da420c5200047f43883b026400c7f65dc1324840197e65ba2ca98003375ce6398a410076a4326498e20009fb805ca51480015e90ca1c62908023f61c4158b300063fbaceab1a4031ecf72d8d32484015f700a1ec298002be60052582311deed21ee09926000af98014562cc00197eeca1a85188032f21170d89540074ec22c6a104200af98090d6094801d5aa8b1284188eeb7a0f42d81320063fbaec490a80008ff835cb65c40015ef02b26c0991275e54d700c9501756f41882b1a402ecde71d8e31480011ff0eb206390003375d1634c821005ea40ae89926233aef825c56290c014ff0ab1665880023fe017690f210067cc06ec90a6000eaf32d9132440011fb0fb1842a00033e50d70189310047ec3ecb99620008fe87d85604c8015f700a1ac1290033b5cf620853018c7ec3ec720a4244ade83107624c1593bf06ba46499003a720d6458f20004f643a84a8a40acecf86509320c8518fee6b2a85988032f9537650b310063ebb4cb21e4000add83d0960cc80179f04baa64988023fe0172d8d54006ebb98e2b2a6400cf5711c56290c019f0c8b806528802bd20543d85324af74386c49926000af980d4d608c4014fd07324cb9011f379cd6408530004fdc3a84982403b8ff805d831480015f30521ac01086ba7191438c9304e65fb82c8a9e4000d7775dc5644c801bd464b846290003dccc95154110147c619286a126400df0415c032904015e902b22c2990029f61463d854243e3fb86cb9922000cf9625c241cc0015bf06b2062900931fd4d7098653006e6a18e4b0a6000c7e32dd562c4001be502b80652891f3dd8d710c9400047ec1eecaa64200c7f64dd56148001dd684a12c0190db3ed8d700ca510071eb2ac8aa26400aed82d8d32500011fb0f21ec29000337dd37058c212b56ec1ce3b128600c7f535c3625505d5bd07a0ec6900035790f75487300057dc0287b024200dd57318e4144001f970099662900023fa1e43587200063e32ee09924200afb80553604c4013eb0f9948288002fc60051d85320c65f326e89904200abf84596324c0019ececb8462908037ae1d32c81200e65e326e4a1a6000cbf749d363484019f301bb2a6900032fd0d76907200057dc0284b0462008ff8750960cc4019dec9b92c2980039d95154584320063fbacc6b0a4000aed8298e629040179f06ba265900033b5ca32185500053a42ac230a6426cbf435d83290401d3f08b1a86108033bdc87158d20006e6b9a6520a402ecdf76d8c3148053d98c6a926490802be602764ca410e7573228599640008ff8759632500716d90aba264902bb5bd537254d320067c18ee0b226400af681d9761
  | 13 => 0x736b2cc6a164000dbb845c03150001d3d09b1a86908031fdd365cc9100075cba286b004200cf4321c5644c8019f2e2baac0190029fe157158d200065fba4e8b1a4000ae980189324c401b9ee699242900029f60e5058a510047ec06eca9e4200f2d545954248001be6e2382c8990023fa1b7250d10005f940c869022000c7d74d9463440d579f04ba26598802bd60762185430047f43ec89922000afb805d163c80012ff0eaa664a820fab483644c9100066fb1ae521a4200af98094d609083573908a9a87190032fdd95450831004fac00e29926200cef72d89514c00197eebb2664881272fd8d740c950004efc1aed10a602efca534c930480015db05b2c6518802bda0764d85320053f42c40b106200cdf765d1320c8011fb0fb1062a01da7ba1c7254d320056ec1e83b1a40008fe86dc95444001d5c80b1284188023f61e20185320063faa2e1b12a600cf5711c560cc8018f8eabb264a8002be60074d81320066eba6e0b184205cbc8759132c8001bd700b90629027f3e5c064189300067bb8ce3b026400beb8350920440011ff0ea1cc48809b6dd0d710ca413b677196e4b2e6000c7c32dd5644c05d79906b2264900031f5d475d89300067d39ae6b004236d3d535d0329440197e863b28498152d7215744c9310047ec06ecaa06400ced645c831c8151dcf0ca1242108032f5d074583320063fbaceab066400dd7845cc2144001f4a86a124210a8f5ed537054d300066eb98c7b0a8400abd84149608c4011fd0db9aa8880037560c71591320055ec20ebb026451cbf7059031c8001e6e87b2c82880c73718d728c5200065fa12e7b222036cdc635ce515012db7687b82a890002db60843d95210067a318e2a124217cf963dc132480015db0429ac5882331fdc36590d100047ec3e6430a8094d7b535c251480d7d72872a2c0190bb5ed4d7094d2035ee6196eaa1a6400dce43dc9614c00157906b96c8880072f61f64d8d1015f4e21a87b026200aed82141620c4016db04218ca908029fe15644c9300053ec2887b0242008fd8758a41cc101c7ca0b24a3900028f61673d91100057cc2e80b006400d79545c032944011fb013b664a889a3f21973905210067cb22e0194a2008fd87d903148001ae8ea38ac899003f820532481100053ec308732e4000e7765147614c8019f6e5b82c6900023f61e425823100676b90e4b006200cf9645c032c40639dc64b94c3298023f61c52582311f66f982ed2184200c7d75d8c21500015f700ba2c690002be6167458032004fdc02e790a606ff9443dc5434c47797e87b82c521802cf61673d9110005f5c02a91924000cbf76dcd64c80fbee086a8aa088003375d17058c210047fc3ac990a6000a7d8319065440016db0421acb900023fa1e4358a510047ec30e2a9660008fd861c5538c85d9ec62bb06290
  | 14 => 0x781597644c8cfcf4a1992c1288aabde0d54584320047ec00ecaa24218cbe74d93614c8013bb0638aa999002be6004158332006af982ebb0a86008fe8715163480495b906b92c118802be6023258251006f4a12e199240008fd870c8615000157b0832ec0990eeb7a0c4158f200057ac3ec330a64008fe8710f62440015bb07b226510803750c871595320055f420eab166000d6d54dc9534c801bc86438aca992bfab19372591320074e326c6a1a42009f5831c542484013f50db92a0880031f1d86550d210047fc02e7b12a800af68198d61480d75ef072a2c219003375cf32185401466f39ec630a8400ed7844c9610c801e5e8732a85900623f61b744cb210056fc1ae8b1a4000cdd65dcd6148093dd264baac0190032f1cf64549100047f438a8b066400cdf7358d42c84015790caa28499203dc94142945100055ec24e4b046200c7f75d91614c85d8fea6bb4a6900033e5917008730004fac3c8790e2000c7d75d8b31500011ff0cb9ca290003b6dc17058c21005edc02e89966200a7c855d162cc001d3906b24c7900023f61c3218550006f4a16e090a4000a7c855c560cc8018f8edb2c869086b2f191748c93229d6ec1ec89926200f2d5450a51c80011fd0fb2a6520803b5a1132584320066fc1aec9948200cdd7398e61480011ff0ea1ec4a80a23f61b735082115e7db1ae01962000af6819d9329054bb7687b8285980032f1d9435093100576c10e9b1260008ff825cf64484011ff0ea1ac0108031fdcf62545500055e422cab0a60008fd83dd951480018feecb2c87900029fa1b43d95210063fa9ae430aa82ecdc73d8d51480011ff0cb948298002f6e0d644c120005afc2ae89906400c7f65dcd42440013ef0ea1462880031f9cf65d91100071faa4a8b166005cbf8759332c80011fd0e20ec4980033da1e31d812100676b16e0a106200beb825c5304800b97f0eb24c7900031fd8175d85432ae6eb9ec530a6028af78350a610c85d9bee5b186290002fae09514c120004be43aa8994a22aeb943551600c801ad865baac8990032fd9373549100055f426e3b026400cdf8758f32944015f700aa2c019002dd215611853200677b94e2b1a4090cdd7058d32c40014fb0a326c299002be60242582510065fbb2a8a166200c7f605d46350801baae6994a388002af61272580310e65f326e4a1e4000af787584614c8011fb0fa92c1188031f55172d8d50005f240ae89964028aed829d162cc00197ae83a2c6900033b61f628853000677994ec992a22ef8c4350e32480011fb0f190c2a00029f61464d853000577c12e2b1a4000cfa63dc15448067da8c718c42900023fa1c4158f20004f7c12eaa1c6400afb8750d60084014fd0da18ca908023f6187150e320063faa6eca9a406eaf783d01610c8011ff0eb206290002bda0643d891000
  | 15 => 0xdb92a898002afe1165585304c6d743cc89964000be9829c530480015db052a6c4988029f21561d81320047f43e87b12209bc7f7059643c80011fd0fa9ac110802af60e40185420047ec04ed21a4200c7f65dc1434847d1ff0cb94879091fe30c9434c9400056fc1aeab1a4000af8865d12044119cbe61b2c868812f571d54348730006f4316e0992600dcbf7650d42084015e902a96c0908c72fd0e7690d210057dc02a7b028200d7b65dc14344043eb6a729a408811f3761a730854040fb92828728a2068f8c74509320c8015f700a1ec0a9002afa1065d81320056ec1e85b126028ead43989420c4315d90ca126490802bb60b74d893000676b22e418a4000cec641c9614c08f8fec6ba864a0002f6e01648c932006eab9a6520a20008fd80dd954cc91bc7aa1b22a6880027d60c7154b3100576c1686b04643be9c43d8d43c8001d72a8a1ac010802bde1f628c5100047e43aca9928000afb805c9608c4015f700a16c098803ae19370591320e4f7c12e630a8400dcf874cb31480015db0538ac6902573bdc3764cb200071f20ecaa1a20008fd83dc16294501d6e20b24a3900027ee0173085300047ec3e84b066200c7d54dcd62944011fb0db9a8290002b76036350d21005f543c84982402aaf583551610c801e3aa8a1aa5980023f61f644cb1000577c32e899640008fd821d954440014fb0a3a2c7908023fe1d43d85200075731cc899640008fe86dcd42440493f30138eca980af7c8c5700cb100056ec1882b166000e3f659cf6444001dd6c6992408823b2fdc36494d100066f982e7b162000abc86551434c801e6aa8a14a288003b158d42484211457bc1a84b086400c7f325d7648c401d5cc6b2265900038fd525458332004fcc06e6aa26000adf8359263c80dd5eb07a02c219003a71906350d210b47f436e4a9a86008ff825cf65904011f90fb1a848800373dcf7259132005ea40aa89926200aef8254f62440019eec638a879080337dcd4358b100063e3acc6b0a4000bd583107614c84d97a86bb065208fbf1dc8714c9310067dc02ed21a40009ee874c95148001c7aa9b1aa6a10029f617648ca310047fc1ae1b12a800cfb65dc1644c8018feebb22c2980023fa1871551320071f2a6cab2264008fd87d9532c40011ff0eb1c83900031f21570d89540053fc1aa8b14a200c7d75197604c8015b90cba2649891f3ed8d700c9400066e426e6b122000cf474d86614c8018fec8ba84398003735cd32907200065f43ec89922000af68190d61c8001cf4a8aa2c019002bda0653d812118e6f39ec720a42009f5821c5544c401af661baac2980029fe195454e32006eac22e610a2000ced721c963904011fd0fa16c6882bb9b19772595320047ec00eca1a42008fe87141620c4011fb0e292c0188031f1db6550d100055fc22ec992a000af
  | 16 => 0x4580320066fb28e6b0a4000af681991614c001bb287b826498002bb60b4358f200047ec3e86b06422ddbb43dc142480019dac9b92c298002bb60b75d89300057b40887b024200ead54d89424c4011fb00b96c688002be6007158b3017fcc20a869824000ead7259031c8057d9ee4b1a65880023fe1d629073047eebbb66498e2000cfb309d8214c0dd9f2e1320c4980031fdd7625853018d6f41ec9b1a42008fd8714563480015f30028ec4980ba7b21d3258520006b6b2ee6a1640008fd8790f6254001daec718c4290003a79536350d210065eba0c831a4228cdf62dcd424c80177708b0a6090002bda0732d81210047ec38a0b106200cf9701c1620c4017d30521e409000337dcf63509100079aa1ecb20a2000cbe84dc16290c014ff0ab24c4980033bd91720c5200047ec3ecb1926000cfb635c0215011397ae1b22a4880033759373585200065e202ed19482008fc865c332484011fb0e28ec6900035bdd2654cb200056ec1ec59962095ecd83d89324c0013f301b92869000379cc871591320057dc02a6b048400add83d0963c80016ed0ba08c2990031f5d762d85430067c182e030a64009f7874ca41c40011ff0eb20c299002bd61841d85320066fb9c86b14a2008fd869c643c807dd9ee4b1a64108031f5d47558d202267a98ee4b006200deb625c0214c0018facbb9a85900033e5c0601853202d5ec16e6b26403fb9c8359143c84011fb07b92cb8805a3f21d4358a3100576c1686b1a4000ced829d932441098fee1b2a6488003f2e01324c5203373d28464b04a200cf7719c7624c001c7c87b2a8690803f1205324c5201466f31ee6a164228cde8798d42084019f700bb64298002bd20565591320047f43883b1a4200deb32dc1644c8e55f700baac19916f761c1704cb310065fba2c6b0a4000a7d851d3624c051dca64a12c2191272fd8d74cc5500065f2a6eca1e4000d5f7550d21cc0019f661bb2a8980031f18f754852018d6f41e85b1a4200bdb835953048001abeeb21ac29800376dcf7059132004eec3c873126000a3d851cd64c80018f8e7b2a8490aafae9004158032136dda1ae019482008fe8790f60484014ff0ab22c0990bb7618d700c5200057dc326298240008ff8759231c80014fd0a3a6c0990fbb390c624c9310047ec30e2aa24000c7c76d9543484018fee8b2e659000337d8d728c52000577c02c51946285aef8258e61480013f700b9062900032fdd95450f210066f320e6b0a4000e3c43d9764440015bf08b82c6108033d991710c9500063eb2ee6a104200e9c6450d614c0019b8c839ac2900033d0c871595420066fc1aed18a4092cdd70d8c31480011ff00bb487290036bd937250d320047f43ea4b1e2000cdf7650d21cc0015bb07a12c690003cd551439451000767c12e0b184200be98094e42480011fb0
  | 17 => 0xaa600fe13290520440011fb0e28ec099243b3481634cb100057dc3286982402ae9e63551430843597cc9b9a85188039b98e654cb201f6ce39a86a104228c7f635d46350801d3d07b26c6880aba718d5450d210057a40aeab1a40aed6f529da524c8013f704b8462980033e595700cb10005afc2ae89966247af9809d160cc8016e706a8aa088002be60271d89434df2f982cb21e403ad6c7550921480015f30020ac1191033e1d8714c120006b7baa8490a40008fe86dc9544c001d5c81b1284988031fd9574cc9210047ec3ec72928000a7d851d162cc0019f700bb4a6900abc70c95454d4300778c0463b024200abd849d5608c4011fb01bb2a899167375c3638c52035676996e4b266000af7815d562cc0011ff0fb1c82908032f59173947200066eb9ac720e4200cbf655d331480013df0eb10c4980033d9937159132005e7c1ac8992406acbf73dc964cc533b74c9b8287900aabee0d54580320066fb1ce331a40008fd87d9232c4001c7c82b2a8790002fca0673481100065f3b2e7b222000a7e851d160cc8011ff04b80c2a986a3f21f6350921006ba32ce321a42008fe86dc9534c4015db05b1a64a08023f61c43583210079ba18cb20a2000e5c65d8e43484019ecc9b8a65188033bdcb6250530004bfc3aa8192a000b7b855c53048001b7108b8065208031f21570185430067b3b6e29962000cbc43dcd64c800197ecbba2c2980033bdc962582310057dc02873122000cf832dc16550c019bee731ac290003c79536550d300056ec1882b066400c7f535cb654c0018fcedb2c86880033e98f7050920006e6a1ee4b0a6000cf5655c4325005d9b906bb062900033b99072585300063fbacebb026400ae8865092044077f1886a1c6590003cb5515250920006da29ae810a2000cbe40dd942cc401b9f05b9ac2901caf6e016590d300053ec28c8b126000a7d86d0e65c80015f30ea1ac010803a75536350d2110fb9aa4a29022000c7f655c243484019db0fb1464980632f9d3648c9320bef4996e09924000a7e85191604c949b74c8b8483980023f61f4158b3002dd6c16e6b264000fca431c9304807d97a86bb486108032f18574189530047ec3e87b0a6400cef329d932440011ff0eb20429800337a1973085400057cc06a8b0062008fd87d9132440011fd0f21ec4880037a90970945200047fc3a86312a200beb805d1324800167f06aa285288038f61473593200047ec18eca1220008fd87d92314c0019bac8b9842980033e58f7050f200047ec00eca126200cbc84dd943c8001a7aa9b9286a9002bb60b638c940136daa1ae21948200c74651c532440011ff04b98c2a81272f58d740c9500057cc04a6b064200cec32dc9658c4015e902b2ac099092b7a0f64d8d100063fbaac4b0a6000af98014563480019bac6b9486109aebee0e5
  | 18 => 0xc88f9bce7b1842a00023f6187154d200047fc1aed20a4000cee72d886150c015f30020ac6900023fa1c5358b10004eec18e2a16602e9ec874c921480d53dd0e39286990033dcc87159132005dcc2064a822049cbd635d331540019f6c8b8043982b7ae10041d813223e6e39ec690a8000cbf605d06254c7f5b906b22c790802b7e0d650c9400057a40acab0a6000d3e505d03294553cbea7b2a64988a31fdcd65508320047ec3882b1e40008fe86dc13248401c7ea92a2c6902535e14970945200069eaa6e4a1ca200b5f85592324c8014fb0a21ac190803b9d893188530004fcc06e4a9a4000dbb30dd1614c0015db05b1a84a8003bae0162189300055fc32a8a1842008fd829da53440011ff00b96c6a08027d61e43c8521174fc43ac29824000add8315363480011fd0e292c1188037618d708c5200055fc32a8a166200c7f75591614c0018faea3aec0990023f61f650cb10005edc02e89926200cef729c9608c4019eaec38a658811f37a1a730854000576c18c59922000cef73189424c40157d03b9ac9900029f6144398910004fdc02ecaa26400bb48155143c840179f04ba264988023fe09731854015ef4992e01962000c7f65dd132484019da413b264880038f5514358a510053f42e83b026400de7721c5644c80197e87b82c520802f5205754cb311766f39ac730a4000cf7719c76250c011f90eb2262900bfead05424c1200057dc02c8b0a6400ee8864c920440019f6e1102c5188032f61f644c910007b921aa2a822000cdf73d8d2150001c7ea92a6c4980035dd95739051000577c02c4a1062008fd861c542cc0015f301396c6aa0abd3cc95454e3200576c38c59922026cf5635c432904939eec6b8864a80a2bee0d42580322cf6d386c718a402aaf983551600c80197882b9ec8900023f61e43189500047ec10eca8a6000ced7650b3208431978c8b9486a80ef1fd4f7058a53006ebb9ee2b2a6400af481592324c85dadea6b94a6900033761f630c5200066fb26e6b0a4000d6c75dc9644c8779ec62bb063900033e5c220987320053ec2ce9b1a2000cbd7559031c80013ef0eb08c2981babe60e74580320057cc0083b126047de9325c032500015df04b1cc5208632f9d364185323565fbb286a1464009fb8755130480019f4c8b8064a800397d976390d210c65e322e89924200a7e859c1628c4014fb06320ca908032fdd27458b300053ec28c9b126000e5c6319643484313bb07396c2a18037c1c770591320066eb9ac728e4000a7f85592324c001dcac5b8a65188023f60876551303777499680b006400cbd741d162cc001e5a8732a8590002be60b40d81320073a328e29922000db5431c542484019bced2184298002bee0154d81320063fb2ee4a1a42008fd8790e62944391fd0c392a6a18031f21570185540065fc22e03
  | 19 => 0x33e0cb70591320057cc00a2b066400bd481553324c4015bf06b226490003375cf6390510004be43a64a8aa000dcc735096148001c7ecaa1a8490802bb60b644ca3100576c16a0b106200cbf431d942440015bf00ba2c6108023fa1f63485500056ec1882b1a4000cef321d93244131d5f0cb2265900032f5d074d8d210047fc02e5b1aa200ddb805cc214c001af4cbb8287900033e8c372582310055ec18e2b264000bcf835953248057bad0f9926388002b760f62cc9400057cc06a8b046200cf731dd9428c401d3b06326c68810a3f21973949420053fc2ae3b1a8400db6401c542cc4011fb0fb1c8290003a76136350d210057dc1a84b004200abc845c563480019d886392c6880033bdd9324c520006b6baa8598a40008fd86dcd5448041f5686a124088002b760c41d89300071ec2ce7b222000cbc76591544c85797ac6ba06588126be60275583320057dc02ec9928000af9859c5600c8019eecab8864a00037a4c970945200067d980eca126000ddb635c031480015bb07b1264a8003a7d906350d210067dc02ec18a403fd9c7350d42c844d9bcc6b9c83908023fa1c5258f100063e31eeab0a4000d6d54dc9538c8631fb0e326c690803b95cb628c510006bc3aee0b226400aed8215160cc8019f6c4b8062a00035790d75087300057a40a85b0242008fe87d0562cc0011fd0fa16c0988c73b4c972987300057cc0486b064200d5d305d46250c4997e873b486880023fe0970185433efb9a1aa2a822000afb84cc9600840197ae9b1662a8003ab95362509311565ea1eecaa6622ede9325c253480018feed32a879000337a13764c8320067dc02ed18a40008fe87d89315400157b09314c2980039d9d8658c5210066eb22e610e60008fd861c5524c1178fee1b2a86880029fa147458d200047f43ea6b1462008fd829da43544018fe65baac898003379c3764cb314365fb86c99922000cfb645c032c4041f60e920a40880038f19375591320073a320cb18a42008fd869c653c80018f90ab90c2aa0035e1977050d10006eab9e6528e20009ed821c543480014fb0a3a2c7900031f1d86550d10006eb190e2b2a6428ee932509600c8015bf0cbaa659896ef6201744cb310047ec00ecaa2623ecdc631c53248001ade65baac8990023fe1d64087300074fb26c6a1a42008fe861c5524c06397a873b486908032f5d07458f210056ec1ceab1a4000a7e8319065484013eb0f21842880031f14676949300063f3b6ea992a000dd7545cc2144001abeebb9ac8990023f21d43d891034ee6c16e6a12643ecde435d821cc001d9c86b10c4980034fdd543485400066ebb0c718a402ebda8398530480019bb09b9ac488002bee1175580324a6bc32ae128a4000af48155163c8401bd2e6a1640900035dd9471595320063fb1eea90a40008fd861c5540
  | 20 => 0x7ec06ecaa66200eeb82d8d20440013f10ea1260900027b6087155132004f6c3c8418a402ec7f635d7314808fa7a86bae62a00023f61f63c85400047ec36e6aa640009f980dce214c0019da403b2648800337dcd4358a51006eab9ec720a2000be582104614c801d9904b1a6588002bbe0943d89100047fc32e528e60008ff8750d60c8401e6a8632c8288002bbe096350b1000677c3ac4312603fcbf435da43c847797e86bb4879006f7ae0970cc92000576c14c9312606eeb743d01610c8014ff0ab8ac5982573b5cf62989300074e322863126000ced87d88214c0014fb0b3b265208023fa1c6558930005f240aea9924000af987551600c801bd264b8482900029fa1771d893035677196e4b2660009f4815d542cc80197908bb48290093e510d434c51000676c3ec531260009fb805d132084018faecb2c87900035bdd542585200ddf5438e49824000a7f855d162cc055e3e60aa2a6a18037ca05700ca41005ddc22e29824033cdc63dce2148001bb6e6382c8990039d18f658c5100047f436e6aa24280cbf7059251c80011fb0fb2464980023fa1f644c9301b66f31ae728e4000aef825d16348077cbca7a9ec099002af60a73d91100074fba2e8b1842008fc8759121cc0d5f1887b9287190cf760c173885300066fc32e610a80008ff865d13208401d9a8631264988037cd85708c5302956ec34c69962000cbd741d3604c80197ee638ac990002b760c4158f200072e31ecb21a425bfc8804cb31480011f90ea9ec0908032f19372591300071f29ec8a9a2036ecf7258d32944018fee8b2e64108ff371cd6350b210056ec26e0b184200e2e6499542c80018fcedb2a8690803a75516350c21296ec382e09926200cbf74d89614c0015df04b1c85288c7679cd43905210055e422ca3126000eaf7659132c8001d5881b1284988abc7cc55454d434ae76b86c49926000cf9655c032500019f0c9b8264980027ee0173949300067db2ae01948200afb8050d608c4011fb01b9ac5208029fe157458d20004f743ca6a124024e9c4358d4344001d70c8382c899003ad50c41d8532005b7c2ae89924000daf744c9614800197d09bb284980bfe6d09434c120004eec18e2a166400ed6861c5324c4011f90ea1ec0908023fe0172d8d101366fb92c69948200cbe87d9332440011fb0e2a2c5980033d8c871595420057dc02e2b1a40008fd8790e62c40019e883bb26520802fae01744cb2035d7ac1ca8b086400cdf73d8d425403157d09b2ec899002db60b43997200056ec1eca9962000cbf74589614c001c7c87b2a86880632f991744c8210047fc3a873162000de9425c031480019bee621ac488002b7e0d644cb210055fc32a8a1e42008fe87d8d42440015bb07b2265880033d61c41d85320047ec3ec918a4000cdd73d8c61508018f8e7b2a84880
  | 21 => 0x87909608c401ee284a8aa0880027b6087150f2000576c18c5992a200abf84594624c0015ef02b2ac8990ab3718f7355120006bbaa0e2b2a6463ee932105600c8019baedb1c62900bb2fd8d74cc5200067c31ee0aa24000b5f855d1324c4014ff0ab0ac0990038f90d6550c2157ed6326e4a1a6400cbc411d94344001cecec32c628811b579d643085301471ea1acaa166200d5d7550c21cc0017cb0428ec2990bb7a4c97090d2000677996e4b2c6200af980dd3604c8019dee7b128498803971976350d210047ec3ecb1962031e9c43d8d434845d7b106b2a60900029f61464581324059e402a8a14a2008ff835cb64440018f8e6b2a8410802f6e016550d300063fb2ee4a1a2000c7f75591614c8011fb0e21cc4880023fa1c4158d200057a40ac9b0264009f9809c643480019d865b92c1189ffbc882768c5100057cc04e4b0462008ff865c332904d5ba863b928698802be61e43580210076a990c298a6000df141dc95044089d9e63b126498003f250c724c1200067ba0eec9948200abd84988614c0014ff0ab22c298002bee0164185320063f3b0cb21a2044cf631dc9600c4015df04aa6c4988038fd936590d10006f5b16e09926000afb8050b604c911cda41b2a84880031f5d365cc9100047ec04ed29a8400c7f7558921cc001b9ae6994a2900029fe1564585320065e21eeca1e4049de9325c032540019bae7b1842a0002b760e74d813218e6fba6c79924200c7c855c06154c53c7aa6b22a5988038f5cc651911015d6f418a4b1e2000ee7621c5324c4015bb07a06c69080376d8d708c5200066fb9ce6b1482009df8750c214c001e3aa8a9a87190db5e54d700ca512ce6fb86c718a4029cdc63dcd5250075adceaa1662900033b61b7254e321475ba1a84b08642ede9305ca5348001abeeaa1ac2980023fe01768ca410067b43882b086400add83d953290401bcee438aca990037a50970cc52023edca1ae018a808be5f30d9543440011ff00bb485188023fe0173185540047ec30e2a1e409ac7f7059543c8001bd701b92c2980029f6184359720006bbba8e2b226400ed7631c53248401d3b07322c7900029f61443d85201367cb1ae0194822eadc8359563480011fd0fa1ac319002bea12715803218f6a31c6290a4000bb5840ca51c40013f700b9c82980bb37a1873585200057cc06ebb026400beb825d130480015df0ca1a64900632f1917290d100065f202ed1948200c7e85dc16294c939f6c6b8064a8003755cf329051024e7ab1ae2192a000cec64dc9614c0018fae9b2ec6882331f5c36590d100063fc2ae1b1286008fe87d8d425408fb6e86b8864a00023f60b73595400063eb2ee0a184200deb72dc530480011fd0fb1262a0003abdda644cb2000766a1ac4312602edcc635c831480011fb0f190c298243b3c81634cb10004
  | 22 => 0xb84a498002afa1075d813235d7cc1ca8b006400c7d655c2430844d3ed0c38a86988029f61443589100065fa1eec99482008ff8758e42c40011fb0fa1cc488002bb6085158b30006ed21ae010e6018e3c6455132540019bceca184298003375cd6390b1000796aa2a6a124000afb855d1600c8019f2e1186c7108023fe19748ca310056fc32e89906400f7143545504402dc78c8aa064a8002be600321854000797a1acaa164028eb54350a610c8779ea63b82c4188033e619700ca510072fb28c6a1a4200cde64dcd61480012ff0abb2a8990a27b60b73509320047fc12e1b1aa200deb825c231480efb9865ba2a6990038f59473593200047ec06eca166200cdc64dcd6148001c7e87b2ec88811fba4c97458032004bf43864a8aa000de9425c23148001b9ae7b1042980bbb50c7634c5200066ec32e610a8000af9800c960944ab5bb0738ec4982a797d51634ca5123fca18a8698a808be3d40d9543440015df0ca1a6590002afe195450b32174fc43ac89824000af48154960cc40157f06b96c8880fe3fe197290c2100736b2a8599042008fc8758d4294401daac721a42108023f61f640cb1028e5eb82c818e4000d74655ce414405db9ce6994c29006277e1d648c9320047f43c80b146200d3d54dc95350801cdacaa1665900025fe1d54cca510beecc1ee09926000af681193614c801978803b284988c73b8c972987300067a318e2a922000af48159161480013f700ba26590893371cf63509101de6f39ac728e4000cdd7358e629047f5bd0620ac7908023f6087650d510067d996e0b2a8600af781595604c8018f8c7baa42a0003b518e618c5200067dc1ae030aa400e9e8399163c80011fd0f182c518802bd2057458d200059fc02a8a9a8600bd583144614c8014f90ab26c0990023fe017690c210071eaa2a7b128600af4815d562cc0b3dae21b1c62900027e60071551200053f42ee3b0264009f68790d514405df96629926090002fce0143945100047fc32e728e4000adf8359532480018fec7baac2900023f21d42d8131006dba9ae810a2000e5f65d8d43484014fb0a3a2c199002bb61a714cb2000796aa2a4a16643fade8399163c8401dcae5b0cc2990033be09764ca410067bb0ae130a6400bd4815d5324c4018faecb2a87900031fdd3654c9100047ec30e2aa66493db8645c24148001c7c86b2a87900037ae017294d20004ef43c86b126000cfb655c032500011fb063b2a88826b97cc16550f200057a40acab0a64008fd8790d60084015db05b1a65880031f19570cc9210063fbaceab166000af9849cd60084011fb01bb287908a33798f73508210065f39ac928e4000c7c7359542c80019f4c8b8065880023fa1c5058e210076a42264b086400af5809da31484013f700baa8719002cf2055454d430066fb18e299240008fe
  | 23 => 0x585300066e3b48690a6000abd840c861540019dee5b1262a00038f55363509500063eb2ee89904254add83d95324c4011fb07bb2a9900032f6117690c2100677326e4b0a60009fb805ca31480015f108baac0190023f61e62185300067b40ee4b046200af9800c960904015f50d39a40880bb7a8c97094d20005bb4088632a2000be4815d532c800197ec9b92a6880036ee11700ca41004efc1aeaa126400d9d54dcd424c8019f6c6b846290002fae01714c920004fa40aecaa26400cf464dc5644c80167f06aa2a4a10031f5977250f20006e7b1ae418a4000e9c6450f614c10797ee1b2264880029f2157158d20295ec402e89926249cf8765d530480015bb07b20c68809badd0f745843200577c12a7b126247db5435c432500015f700b24c2990023f6037258e410047fc02ed9948200eaf3259132c80018facbb9ac9900031f1d562487300057ac1883b0a6400d6d7499532c8001daec718a4290002be60353582210071ea1ecaa122000abc8650d424847d9bec8b984398003b9d8a3188530007f0994629022000deb805ca43480011fd0e3b287908037c8c77048520006bc3a8e0b22646aaef82592324c8018fae8b2e65901bbad50f4058432147ca18a86a126200cdf65dcd61480579bee0b1e65880033be09768c5200057cc24e2b0064a4dbb435c241cc0011fd0e322c2980031f5977250c210067a190e2b2a6400cee63dc951480018fecab8664908038f5ce65993200065fa1ae1b12a800d757590c2144059ba863ba264988032f5d064d853234ecf2a6e6a1264008fc8750d62c40011fb05bb2a89811f6d50e710c9400066fb1ee710a40008fe8715162cc001e3aa8a1ca2980a3379cf6394942006f5b96e0b226400cbf439da414c0011fd0e28ec099003375d94308730006f8388e0b226400aef8258d329447f9f260bb6439811f6ed0d700c940004fcc06e690a6000e6f7699532c80015bf06ba2c7908037ae09700c5200057ac30a230a6400cfb31dc1644c8d55ef07a12c219002dbe15744cb200063eb2ae99904200fca43dc93048001b76c9b92a088002af21165d853021f67218c49926000d3d54dc95350c0195ac8b906390002bda06764ca511666f31ae72162000cbd7559231c80011fd0f21ac4880db2f58d740ca514de3eb82cb21e401acbc64dcd424c841f668720a40880032f59774585203847f43ec89924228abc845c7635080197eeab246390002fae01434cb200053f42ce4b006200a7e851d3624c051d98c6a1264908023f21d6350b100063e196eab2264009ee8794d42c80011fd0e20ac5980023f6187150b320047ec16eca8a6000adf8359263480019f660bb48298003b960762885300057a40a65b0262009dd83dc9544c8011fb0fb1662a02bb5b1977254d32005da40aa8a1a62008fd831d95448401bb486
  | 24 => 0xa4000c7f535cb65c40019eec638a64880fe3fa1f4258f210047ec30e2aa64000e746319631440011fb0f190c2a80023fa1a7650d210065fbb2a8a184200abf84597614c0017e700a184288003b3dd9424c8320047fc1ae030a8400e3e7399664c80019dc86392c68816b2f5c1648c7200057dc0286b004200adf8359263c845d1fb0cb9062900beee211714c1200d74f322871946200af983d03604c8019bae7218c488003a7e0d6458f20004fac18e2a122000eb676d923144001c7aa9b1a86a8002b760f62cc95000577c12eab1a4000adf835536348001d3d07324c7900029fa1741d8d2000775b96e0b1a4000aed82d0f6244001adee8b2a65900bb7a4c17290d200047fc1ae430aa000b7481595544c8011fb0c38aa899002bb60b40d89314d71ea02caa1e4028eb543509610c8011ff0e990c2a00a32fd0f7650b310066fb9cc6b148226db9435c03290401d5e8631284989dabbe097558b300065fc3ac818e402ecbf435da434800197e86bb4829005efa60a73481100057d40e80b006470f8c431c9438c8019f660b80c2a9802bd21943085100047f43e83b0264008fd821d953440495bd0620ec6880023f61c54d8d201fc7f43cc8b1e42008fe87149600c401daec730c6290003f850a51481100056fc1acb1928000c7f75d91214c143b70c9b828698002be60232582410078eaa2a6a1a6200beb8350b20480a5f910099262901abba4cb42580320063ebaec93126000ddb80dcd61480019bee6b1a8410803735cd32947200066eb9ec720a4249f4c3254d3254001ce8ca38aca990032f101760ca410047ec36e0994821a9df835c86150c55ceaa6aa2c2190033b59472585300067a326e2994622edf1315c0314813d5bf06b10c2980027d60071553211f74e21a86312626aabd83dc964cc4015e902a1ec2900023fe1f62905300047f43e82b066400dd6701c5324c4015f30138ac6900fe3fa1c4158f21006bd982eb31260008fd86dc943084011fb0f218c4880023f60b7058e510047ec36e899462008fe8794f6050801bd464b84a2900031fd957418d2131f5ba1882b086428ebb43509600c8018fee8b2a65901bbaed0f40580320074ec1cc931e4000add83d9332884018fecab9ec890802bb60843d81210066fbb48690a6000cfa64dc1324c0011fb013b264a889ba718d43905211fe5ea1aed21e42008ff865ce41480014fb0b3a6c6908023fa1c41583320047e432e529a2000dcd53dc9438c801978e8b12c298002bee017558d200072e328c6a1a4200d7b30dd5214c03197cc8b948610802afe117158d200047ec3e6430aa0188fd87d93614c8019e8c438aa89884776e0d708c5301756ec3ec618a4000e9f6350e414845d5b906aa6c6900a6bb60a7558b3000576c10a9b126000cf676d8e31484011fb0f29ac1908032f1d362
  | 25 => 0x17d30038a64900033ed8f7050f200e65f322e9996422edce734ca5148055f1864aa28699003ba50b32580210047ec3ecb99482008fd86dc954cc41597aeca1c83908039d190658c5100065fbaac818e4036f4f3254e329447d5dd0f31265188027ee1d43481100065fba4c6b0a40008fd87d9332440018feeab1a42900033e0c970d92310071fb26caa1a20009ef8750b31480019de86392c6880027e6037354930004bfc3aa8194a200aef8650e32480015ef02baac6900031fdd76248530004fac3c8790a20009f5861c543c84879df0cb906390127371cf63485500047e43a84b046200af980105600c8018f8eab12c298002be603644ca310066eb98c630a84009fb805ca41480011fb0fa0ec4980029f61771d81320071ea1acaa164000e5f7558d32944c7d6e863a2c2190035bccb75585320057bc3ac318e402bcdf7258d32c40018fecaba264908ebd3d4e53509200055ec2064b04a200ecf624c9314c0017a902a1a6498802b7e0d64cc9200047f438a0b146200c7c75d89614c0018f90ab84c329802b760f4258f210047fc3acb9928000cbc7458d6148001abaeb21cc4980f36b9917290f200057bc3ac518a2000ee671d8b3244001d7486a1ac0108023fa1f63509510053ec2887b122000cdf7390d624400157d0638ac9900cf671cd4350a210047ec1ee0b148200af88350960084011fd0fa9ac58800397551634ca5100766412c69948200adf8359332c84019eae238ec4a180379ccb71595320065e422e1b128600add8314963c4001dab03b1c62902173b5c362cc9100063e3aac690a402eade83d0963480013db0438aa919002fc20574481100071eb2a86a104200af987951600c83197eedb2284990027e61e414c1200067b3b0e29922000adf83596634811d97ae1b24a688002b760f65ccb102256f41e85b12603f8ff8758e41c84019eb03b92c11880357dd64348530004fdc3a429824000a7d85dc76250c018f8ebb1242980027e6007154930175e641aca9924000ee56350921084017d704baa60900bb7690d708c9300057a40aec992a000af781591604c8011fb0e28ac1990fe7de19718ca3100676b96c430a8600add83d9332c40013f10e90a60900023f61f431891024e6e39ec6a12a000ed5844c9610c8011fd0e29ac1108fb37dd163cc82100796aa2a6a164000cdf73d8d21540015ed02326c2980033e6037650d20236ae3ac86b0a6000cbe735cf64440011fd0fa1ac390002bb60b5458831006eab9a6528a2000e3d545096094401a7aeaa1842a00632f9917290f20236ae3ac8690a6000e9d83d9063440015db05b246518803b558c714cb100065fa10eca1a2000e7975551600c8019d6c4b80429800337a1b73585200057dc1ae8b004226cdc635ce41484011fb0fb1e42a80023f6087650d101d6b63aa84b0
  | 26 => 0xe411801c00402c1a40b6c0005806405401400405000002801802430800000015001800020c06400800c00000424809c008de40644600c00c801c01400001801007800000026401c010064178310001240013bb0f2184298002bee015458b300047ec30e2a126000af681d8b614c05dcbca7a9ec690002cf61473593200057cc0484b006200afa8690d20440011fb01bb2a9190037650d70949300057cc3e81b026400add83953634843197cc9ba265908039e545755803246e5eb86c8a9a201c8ff8750c624c0017e700a1aa2880023f61a7190d200047ec16e6b2e2000af98090d60084019eae238ec6a1002af610535822153ebda9ee0aa66000cf5711c563480635db0538ac5218c76d50e7190d210047f438ec9948200e6f7699542c8001b9ee6a12c29018fad50c415843249edda1ae120a406aeb743d09610c85597a87bb2a8190029f2157458d200071eaa6c4a12a000de932dc121480019b90cb9842a0002bd20564d853222577430c49926000cdd7358e4294401e5aa8a9284908023de1d61185300053fc2aec9928000cef74189324c4015e902a12c198802bb60b638cb1023edca1ae01928000afb87105600c8ddd7287a02c0190023fe01764ca410057dc02a7b028400cdd84dd9320c8014fd0a3a2c5980033bdca72580310057b40886b12202edea325c24348139c7aa0b22a7900027e60071509301dd6f41883b0264008fe87d49600c4019eec8b8864a8002f9e05754c9200066fb9e86b122000cbd64dc152cc4016f70a90a6090002dda07431951017fd52a2849824000abc84595624c00157b0829ac588002b760f65cca410053ec3686b2e402bef2319c5600c8011ff06bb48390103b5cc8614c5300047ec3ec598aa000adf8358932904d55eb07a12c21900337d8d720c5200065fbb2869948200aed82901620c47d1f90eb1a8410803f24c9314c1200067ac30e2b226400cbd7499263c84019f4c6b8482900023f61c4158332326bd282e0194a245d5e7550c214c0c757f0638ac8190c2de215714c1200076c39ec6902203bcde7358e41c80c7d768620ac0190033d18c71509100047f438a9b126000cf9805d821cc001e5a86b2a859021f1f5c365cc9100065e21ae7b222000e9d545d16308401b7661ba2ca98002cf61032545500076ab1a869084200deb82dc1644c8013eb0438aa7908037a8c9709052000576c1687b1e4043e9c4350c624c0016df0ab8a64902bf7360f7250d320056fc1ac49962000cdf7390d61c80d55f707a12c0190027b60b735513217ddc422c29824000afb8050d61c80013df0ea10629018eaf60c71590320047f43ec89962001cbd87d903144001c7ce6b2ac9900032fd95740cb100073731aca9964000cec43dc963440011fb0fb2665880732f9937250e3100677990ec992a230b78854853048
  | 27 => 0x980100040140000041ec13c000050018044ec003018405c0146481f81240000a800c09000c00803844406c01402c01974000400000401c04018800862c02400da6400800000807401c28800800003c09b16803c33c00800005815000001c00000c0041c406002802c01401c05402c02800000404825802801841c01d85400822402c19c0600080ac0000085140880483840080000480d01d00001541f004006811801400813c0d000c00000000c13000800004801002000400019c02800000800803400c0100a008005807c01400002c0040d007c00400802007c030004024a60004d6002400400c1200d453806008400c13405009400002405802000000003000c0680280700fc5f803c01c06c07c1f00a011835c1f003813800408000c000000170090148088ab011000000006419409c0100180000202d80280300101b00200040000000000f801c0000000000441240140080080080c802a6ac0dc0000cc0040c83ac04c0a0104004000cfc090ef40b805c02c0000ac0540440000c007c0f406c1aca3809405c03420c0200000c4138000f889a800c0087903dc02400439416c17873c0000e0000c200a800001c86802402400402406400000c04800000000808c04400007802408c06c0cc01800002405006000002800000001018002c01009c0122040a40240640040000cc3f8034f4c0882f808c00001412410000401c0001a002016c010110024010b401941c4c8808c0080300400080100cc3ec3e811c0240041c006c008041b6404400400007802000019800004c0700000c4000000004024020004010004064e5c0a80f03307b44840080540600080000480140ec9080181980080000000480400000600140000e017800001000002444807c19c01472000000000400000005c00098004825406802431400417806c0140201080000f00000600000047d400004000800000007400c0700180640240040500d00040740140000142400000180f048802c03400c03c04c16800001000004c00802c0e80000582400084bc01424800003c24c00000c0080500000480041502cc0000e064801800000001405c800b1400405c0a412003400002017c0000200080680b003c0042f00000345a007800000810400001c0580010380081740081b65c800808003402444012c020004008040cd80000a426c02003c01001c03401c0101c806c29c00801005c0528c853000000067401405c0400a40240640301301601dc0001180000439309740040b00000240900140340800100080000100140dc0500000d038400010c86c00427800803001401800001002ce300600c80f00bc0a40580880540ac0080008300001dc0180140000300000500b00c401802400c2a80000080680540100301c08c800812c0001aeb4000425c0341b80200a88d001c0241
  | 28 => 0x100402403800c0600180080080540000005900200081740041cc0284e816000d81c00000c00807412801c00002001815808c6dc00c0e83fc058034048b8003403c0b001c04800d5a80b08f40dc0640000080480000040b154401c02cf3800802001808009880c00c08400000c0040500249e800c010b7004000045002400c0001a410003c0000d806405235c05c0180040056c80381e80000780002302e407ce0012400000013c2900141e800015c02801806d45803401407418401005c0980d001807c004048b000781300300000100002240000000540240040380d800c06c00000000001c0680340040100140200340080300580bc02400005808c0ac8ac04c07800002c0086280240100a801823c0282742d400008c0201600243d400c05401c0300e40740f404000003000001009468c0bc05c00c0bc0681b0006d342d401800035807804400005c03003002c05405400c00408032cb340028380000040280001800002880100000000041b800407410c0841a405000400002c0200500180080040040000200240007d008001801805c01c0640140040680000045cab1802001000400000400800c0080f40000000140e00142b800806421041032402400001c0006111f807000000020000c04c00013004004819801c1c4018b480e4064e5400400c0280080280f800800002c01c0180280800043c405000697c00039c3981f000c00413808000000c1900140340144e80181c802800803000403c03002c06000c09c00c0000500d401807247001000c24000c00833417400802802c0701bc0283200140500200040200300c80000ac00406c02004800c00004000412806c00023c07401004803c5bc0880000e40140100040600003381341840000001c402800400802c0480001a809c03006c01408c00802821c00402002806004852804800c14004c68805c14808c064014020000058016dcc0000301480c80640b800006801003800c0280bc0b802c00002c06d6b80cc01c0140dc29402d6b000000c4740000084b02ac00c014f8c0d40000001240200580540340ac00400401c06801404860c01400000c03448001400c3640080d401c0087d800c03007c02004427042403008800400400800405c03c00006
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x40147b905d3654c910006f060d3290520440015e1900c871591320051d64432dd5644c8014f1910cb70591320042fa60431d9434400197383dc951541100068b55182d8d42540014f2910cb705913200517e5584dd9320c80187b75e016458532006b2e0f6350920440014e6960c871595320065ce137254550440012e898d8d42481100048fe63659cf6444001e84845093258432005c52455454d434c401c4d65dce6350b200060f5d584197604c8010be98d0d76905200042fe61741d3624c06349d97d8d439052100595654844c9610c801c8c74dd9424c832007071cd6550d420840127696a04431952100587a4f64d9543440018d7732056358520006a510c8650d3144001c1d54dcf6350950005b26408258d32904014e9900cb72596310058b65440d89424c4016349650f65905100050f650525cb65c4001aab4360062509310041f66276dd532540014e49159472585300070d190655ce41440016d39061132584320051e656645c032c400137298cc951541100042fe61741d3604c801731940c951541100068e54184149600c4014e992191700c9500051e65432dc1644c80187986e15700ca5100536e4d655c032501017289055142945200043de61711c562cc00187965e01744c8210058e64373d97644400163594194715953200707dcf659cf644400162d96d0d6550b200060f617731cd64c80014b99021d640c7200058724d6459543c8001c1c7350d6550b200053c64432dc16550c014ad9210f7650f200043b6637618a214c0014d49159073585200053a24963dc1434400147597190658c510006b290d80189324c401c34641967190d100063a1d9801c532480010fa980cb70591323edcca503254550440018db76e01744c83200536e417458d3208401c39645977050f200058be595454942cc80107f985d475583320058d65065dc5654c801479900cb75591320051e640515da52cc00183f7461464585300052be5165dc9614c00107d980cb7558b100043d660631c542484014d691a1b73585200070da1c651923144001479900c975d92310048f259859cf64440010f7985c471d89300042fa5c84595614c00185d85dcc43589100052d64432dd1654c0010fb9761132580210051e654435c0624c401c946350c71509210061d1d881595544c801c1e73d9543905210070e99265dc143c800149e94a1b73585200058b259545494248401a736560051d85320050f65687d933244001c1d545cd43d895000539648311d9424c401672960c951541101f6b1218814c9314800149d9310076509310050f65065dc1654c80183d7561075d81320053a648435c0624c4014e9900cb72582310050f6578759231c80017c190205324c520004f164881551324c4018d776205744c83200536e4184dd9320c8010f7985c471d8943
  | 1 => 0x50f65443dcd64c80014bb905d07458d20007071cd43d9542440014b69719371591320074355153dc9438c80143d940cb7558b100061ed97805d132484019d030600714c9310062e10187105600c8010bf985d07458b300052ea5c64dc1644c8010bf985d07458f210043de61711c56290c01c38641977050d10005872595454d434c4016349650c659051000437e61731cd629040146f95590725853000574643545cc214400183d855d07458b300058725954595434c0014f1900c871595320042fe61741d363440010be989cd64947200058ee417319464440014f39159770591320043be61721c9600c4010be98d0d70d8954005a36486450c624c001a988350d42580210070e1d4641c1644c80123e9819375591320043de61761c532c40012d698d8d618c520006aad0c86509204400143d9418f75585200070e191545c0325400147995cc7705913200574241741c5324c4018b876e11754c1200052764c405da32904010fb9061f4258f210043be61768ca314800162f965515350b200041fe61751d7604c8018d58318c71509100062e61c74105600c8016359519071591320051e64032dd562c40014b69118f74585200052d650321c5654c801a3a5061032582510042fe61741d160cc80143d9510d73d91100060f615741d3604c801569900cb755913200719197721c5654c8010bd97211659893000595e55844c9610c8011e898509708c5200050f65440dd942cc4018d58318c71549100053c24565dc1644c80197175e0143085100042fe61741d3634840161d9519143989300052ea5c641c1644c801c994310d7018931005876546450c624c0010f5981887154d3100636203765d132cc40146d9519372585300052e640431d943440014d593a0772580310063a5d180189324c40163b905cd65593200053525d844c9610c8014d491613764c8320041fa63535c061550bf59993211700ca410043de61711c7604c801a9584211325843200785a0c651923144001c3a505937054b310042fe61741d163c80014b6919507650d1000535245651cd614800161d9519143d85300063cd85801c5524c00143d9510f7650f2000587a4e4159543c80010bf985d07458d200060fdd5849d5608c40107e98d4d70d895400672e0d7350b204800107f985d475d8930007a165163509210840145d95a1b73585200043de5d86104614c80149d93101760ca41005a564c6418e414400143d959cd73d91100056c643535d021440013729890d5154110145b164a844c9610c8018d58318c715092100617ddb855d1320c8010f697205655913200475660321c5654c80147594194715953200574643535cc21440014ac9459772585300042f66073d91524400117298dc951541100052da5c641c5644c8010f7985c47158332007075537350d6294
  | 2 => 0xc47d49c9758d43508210052b64841dd943c8001c1c73d9543509210052e650835c06154801c2d645957290f20007298c5645c831c80012e99321942481100070d9c764d964344001a2d526107558831005b26408258d32c400183d756107558b30004dc26142545504400161d95a136350d210054d650651c5654c80162f9655142947200052da44431d943440010ef985c87258e41596b1e0863586314800183d85dd274d8d100053664e645c03294401e1583194648c510005872595454d434c00161e939076550d1000533e49645cc214c0014af9459472585300043de61711c763508014359419471595320051e65464dc1644c8018e97060864189300043ea6032dc16550c018da63e01744c8210072c190711c1644c8011ea980cb70591320041fa63535c861550014ad92dd5640c72000535259845cc21440010ef985c872582310058d24565591544c801d0d54dcd5250b320050f6548759031c800145d951d3764c8320058be594359542c81676c593a076288530006aa10182107604c80183d7561075588310052b648615d06254c014b9940c170185320050f65063dd52148001ac943600624c9310052765286dcd6148001aaa5421942481100051d64432dd5644c001a2d54e096350a510069618f85585304800197181e15700ca510053525d8458d2108401a395061052582310060f615741d163c84392af9850c62509310061e5c185190624c001d3064dc951541100052ee51835c061548014d793595710c9404ff265c06450c624c00189c8761163508210074c442505d032944014d993991700cb100053a64b435c0624c401c1d73594735932000565650855cc21440014e592191710c950006aa1d08650920440014ba940cb7059132005a364c40d89424c4014f1900c87159132007a1e11424c9610c801bc1834ca51481100050f650755d9325400143d95a1f644c9100052da47421d943440010f59818871551310053564c645c4325400143e9719375591320051765684dcd62440019c880e1d32cc52000565650535cc214400183d855d064d813200535a58321c5654c8d56c79261132584320055ca5b72545504402d49e97d8d43509210048fa6354597644c03143c975956455132004b5a606358631480014e6960c8715913200437e4d861c5544800143d9518f74585200051da5c65dc5654c8010f990a1b7250d310041fe61751d563480016349655142945100063521d6350d21084014e992991700ca5100517654641cd6148001638945d554580320051b654431c9634400163b905ce65993200063adcd80189424c4014f1900c871595420051da5c651c5654c801c3b64d977050d10004dca60325455044001a2d825977359320006352197350c21440019d173e0143085100058e65464dc1644c8014e491590725853
  | 3 => 0x2e21054ee1001878160000018780e0a8103e0c0b00000702c81042211c854000a06d8858070000c6c030419c1a1f000203400008fc000b0080016090a0340eaa098e4040c0c8142e8d14800280c04070c87d03018004500006ea233c81c4015006780024048002c000a0e96506000187c011d19034030500c6a0001020ac050846570002b250080501a2404000f8187c5302800040200010002b058180014028440c0000a94c006360480143e971907559132006c655380595434c0018d870e19704cb31006271d3865d1320c80186e875966350b2000587e595454d438c8010f7985c47158d200043ee61701c1628c4014eb9260d70185520051ee417459532c8001d295450970945200060f61574193614c80146f9559372585300051d644325d7648c40183d7461464989300062e993805d1320840161d9519143585300051d65464dc5644c80187876e15744c1200048f661651cd64c80014d993191700c95000574e41845cc214400149d939da73d911000539e49711c56348001699939d340d8132006a310c8258d43440014e99290d70189310051b654641c9614c00146e960cb75591320056c640535d021440018b970211651893000723191431c9614c0016c990209634ca510049e656849c5600c80183d855d07458f200052b251651c9614c0018eb74600624c931007250c47650d424c40183d7461464189300051b65443dc96344001c3587194648c5100058e654641c1644c80189c73e194350821004b96488150c624c4015d19014d73085100043ee61701c1620c557699931d041580320053a64a645c032c40015e1900c871595320047ce6131dc95044001c3464551710c9500058d2595450e5144001f215450a51481100052764f761cd64c800123f966147359320004dc261325455044001e856350d4248421006aa50d80189424c4015d19021573085100051765484dd9320c8014e99220d70185520048f660641d5644c8014ba94cc77059132006361cc865cd204400145d951937358520006c6cc3805515350c0149d931037650b310042fa6043dd943c8001d3364dc951541100053ae49645c0214c0014ad929537650f20007251917318e41440018b464e1d3290510004376637618e31480014ea960cb70591320043e660325c3648c4016359519371591320071c5c5515d5600c8014f1910c970d92310051e640519da524c00143d9510c7650d100041fe61751d562cc0014b5969007150b3100574642855cc214400162f9650e6550b2000674600701c5324
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xe00000100c0901c000000000041019609140d0140000542b4a2190ca1a6288002c25a4197721c5654c801514d28e8432849022000b0c694641c4705913200626531b26e4a8aa088002435a9a1c65192314400190acab0842264b086400aa268c4060841d8132006832e0ca8c8a18c498002e05a5211424c9610c80124a5332829ae610a2000a0769474e19744c8320054314caa700b2a8698003489706486450c624c001606d28e9bb2849906400c2664d871d0415803200691286c9086b80c498802991a40c1801c5324c40160cd18c8aa2e0192a000c4ca6064dc95154110005c414caa28528a40880032c086640814c93148001614d10c8aa2e0192a000a83694432096350d100068332aa1886b80c498802c85a20c47650d424c40124a5332842ae610a2000aa468043219434c51000584b44322a8b8864a8002439a91d4641c1644c801606d28c8a18e4b0a6000b0568c64551710c950
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x94d
  | 2 => 0x138e
  | 3 => 0x98d
  | 4 => 0x98e
  | 5 => 0x150d
  | 6 => 0x9cd
  | 7 => 0x9ce
  | 8 => 0x168d
  | 9 => 0x168e
  | 10 => 0xb0d
  | 11 => 0x1409
  | 12 => 0x140e
  | 13 => 0x154d
  | 14 => 0x249
  | 15 => 0x24e
  | 16 => 0xb4d
  | 17 => 0x1449
  | 18 => 0x144e
  | 19 => 0x16cd
  | 20 => 0x1489
  | 21 => 0x14c9
  | 22 => 0x3cd
  | 23 => 0xcc9
  | 24 => 0xccd
  | 25 => 0xcce
  | 26 => 0x15cd
  | 27 => 0x1709
  | 28 => 0x170d
  | 29 => 0x170e
  | 30 => 0xd09
  | 31 => 0xd49
  | 32 => 0x98955
  | 33 => 0x98956
  | 34 => 0xa4955
  | 35 => 0x154955
  | 36 => 0x94c
  | 37 => 0xb4955
  | 38 => 0x148c
  | 39 => 0xbc955
  | 40 => 0xd0c
  | 41 => 0xd4c
  | 42 => 0x104c
  | 43 => 0x138c
  | 44 => 0x160c
  | 45 => 0x150995
  | 46 => 0x98c
  | 47 => 0x9c995
  | 48 => 0x9c996
  | 49 => 0xb0c
  | 50 => 0x140996
  | 51 => 0x140c
  | 52 => 0xb8c
  | 53 => 0xbcc
  | 54 => 0x14cc
  | 55 => 0xcc995
  | 56 => 0xcc996
  | 57 => 0x15c995
  | 58 => 0xd0996
  | 59 => 0x150c
  | 60 => 0xcd515
  | 61 => 0x15d515
  | 62 => 0x20c
  | 63 => 0x154c
  | 64 => 0x4c
  | 65 => 0x124c
  | 66 => 0x164c
  | 67 => 0x8c
  | 68 => 0x128c
  | 69 => 0xe89d6
  | 70 => 0x1789d6
  | 71 => 0xa0c
  | 72 => 0x130c
  | 73 => 0xa4c
  | 74 => 0x134c
  | 75 => 0xe9696
  | 76 => 0x154b15
  | 77 => 0xb4b15
  | 78 => 0x145411
  | 79 => 0x171411
  | 80 => 0x171416
  | 81 => 0xd0251
  | 82 => 0xccb51
  | 83 => 0xccb55
  | 84 => 0xccb56
  | 85 => 0x170b51
  | 86 => 0x170b55
  | 87 => 0x170b56
  | 88 => 0xd0b51
  | 89 => 0x15d451
  | 90 => 0xd1451
  | 91 => 0xcd6d1
  | 92 => 0xcd6d5
  | 93 => 0xcd6d6
  | 94 => 0xd16d1
  | 95 => 0x3d491
  | 96 => 0xcd491
  | 97 => 0x15d491
  | 98 => 0x171491
  | 99 => 0x28c
  | 100 => 0x3d4d1
  | 101 => 0xcd4d1
  | 102 => 0x15d4d1
  | 103 => 0x1714d1
  | 104 => 0xcc3d5
  | 105 => 0x15ccd5
  | 106 => 0x188c
  | 107 => 0x194c
  | 108 => 0x44d
  | 109 => 0x1a0d
  | 110 => 0x180c
  | 111 => 0x184c
  | 112 => 0x40c
  | 113 => 0x1a4d
  | 114 => 0x198c
  | 115 => 0x2cc
  | 116 => 0x19cc
  | 117 => 0x44c
  | 118 => 0x1a0c
  | 119 => 0x1a8c
  | 120 => 0x198d
  | 121 => 0x180e
  | 122 => 0x28e
  | 123 => 0x188e
  | 124 => 0x18ce
  | 125 => 0xbca495d
  | 126 => 0x141451
  | 127 => 0x25451
  | 128 => 0xd14d1
  | 129 => 0xe94d1
  | 130 => 0x1794d1
  | 131 => 0x148cd1
  | 132 => 0x14ccd1
  | 133 => 0x141711
  | 134 => 0x149711
  | 135 => 0x14d711
  | 136 => 0x14cd11
  | 137 => 0x148d51
  | 138 => 0x168955
  | 139 => 0x14ce91
  | 140 => 0x14d791
  | 141 => 0x148ed1
  | 142 => 0x1497d1
  | 143 => 0x1716d1
  | 144 => 0xb4cd1
  | 145 => 0xb5711
  | 146 => 0x15c251
  | 147 => 0x94995
  | 148 => 0x94996
  | 149 => 0x170cd1
  | 150 => 0x198995
  | 151 => 0x180996
  | 152 => 0x150cd5
  | 153 => 0x169515
  | 154 => 0xd4e91
  | 155 => 0xd5791
  | 156 => 0xd0ed1
  | 157 => 0xd17d1
  | 158 => 0x255d1
  | 159 => 0x10c
  | 160 => 0x9ce96
  | 161 => 0x1689d5
  | 162 => 0x9d796
  | 163 => 0x1689d6
  | 164 => 0x95695
  | 165 => 0x151695
  | 166 => 0x199695
  | 167 => 0x181696
  | 168 => 0xb1555
  | 169 => 0xb4cd6
  | 170 => 0xb5716
  | 171 => 0x283d1
  | 172 => 0xcd5d5
  | 173 => 0x28cd1
  | 174 => 0x170cd6
  | 175 => 0x170cd5
  | 176 => 0x1715d5
  | 177 => 0x15d715
  | 178 => 0x3d45419
  | 179 => 0x17140b59
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 10 => 1
  | 9 => 33
  | 8 => 800
  | 7 => 4269
  | 6 => 3738
  | 5 => 437
  | 4 => 32
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
  | 9 => 2*((h/18+packedAt gbK9 (858+(h % 18)*6) 6) % 33)
  | 8 => 2*((h/315+packedAt gbK8 (29600+(h % 315)*10) 10) % 800)
  | 7 => 2*((h/1444+packedAt gbK7 (204912+(h % 1444)*13) 13) % 4269)
  | 6 => 2*((h/1281+packedAt gbK6 (220542+(h % 1281)*12) 12) % 3738)
  | 5 => 2*((h/152+packedAt gbK5 (30590+(h % 152)*9) 9) % 437)
  | 4 => 2*((h/38+packedAt gbK4 (2592+(h % 38)*5) 5) % 32)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xe0f870787f87ffff1c07fff00163239c13f4fc
  | 1 => 0xff07807f87f87807e00780fff2bc3ce0ecc8cf
  | 2 => 0xffffff8007ff8007fff800fffcc0c0ff0f0f0f
  | 3 => 0x7fffff8000007ffffff000f00ff03f00ff0
  | 4 => 0x7fffffffffff8000000000fff0003fff000
  | 5 => 0xfff8000000000000000000000ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0xe84810080980ca330414a6906021218c01545c
  | 1 => 0x294180388288505520250aa5a02c2ca064c8c5
  | 2 => 0x52923480055500a24950044a44c040550b050a
  | 3 => 0x4c9555000010492a258008b009602b00aa0
  | 4 => 0x10876e66666625c000c010030fd60003dea000
  | 5 => 0x9ce00c04404446000304608c0ffbfbf8000000
  | _ => 0
def gbRaw : List Sig := (rawDecor 63 gbPos gbNeg).map Prod.fst
def gbPools : List BoundPool := [(0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555, 8, 0, gbRaw),(0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333, 6, 0, gbRaw),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 6, 0, gbRaw),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 6, 0, gbRaw),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 7, 0, gbRaw),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff, 8, 0, gbRaw),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 6, 0, gbRaw),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff, 8, 0, gbRaw),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 6, 0, gbRaw),(0x44444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444, 5, 0, gbRaw),(0x5050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505, 5, 0, gbRaw),(0x5555000055550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555, 5, 0, gbRaw),(0x55550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555000055550000, 5, 0, gbRaw),(0x555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555, 5, 0, gbRaw),(0x55555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000, 5, 0, gbRaw),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 5, 0, gbRaw),(0x3333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333, 5, 0, gbRaw),(0x333333330000000033333333000000003333333300000000333333330000000033333333000000003333333300000000333333330000000033333333, 4, 0, gbRaw),(0x33333333000000003333333300000000333333330000000033333333000000003333333300000000333333330000000033333333000000003333333300000000, 5, 0, gbRaw),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 5, 0, gbRaw),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f, 5, 0, gbRaw),(0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff, 4, 0, gbRaw),(0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff00000000, 5, 0, gbRaw),(0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000, 5, 0, gbRaw)]
def gbAtlas : Atlas := ⟨10,rawDecor 63 gbPos gbNeg, 0xfeeefee0feeafac0feeefee0feeafac0feeefee0feeafac0feeefee0feeafac0feeefee0feeafac0feeefee0feeafac0feeefee0feeafac0feeefee0feeafac0, gbN, gbR, gbH, gbI, gbPools⟩
end PEqualNP.Outside.L_meta_36278
namespace PEqualNP.Outside.L_meta_36278
open PEqualNP.Outside.L_meta_36278.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 10 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_96 : Interval s0Atlas 3 96 16 := block_range (n:=16) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 112 := (concat bs0_3_0 bs0_3_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_96 : Interval s0Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_192 : Interval s0Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_288 : Interval s0Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_384 : Interval s0Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_480 : Interval s0Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_576 : Interval s0Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_672 : Interval s0Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_768 : Interval s0Atlas 4 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_864 : Interval s0Atlas 4 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_960 : Interval s0Atlas 4 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1056 : Interval s0Atlas 4 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1152 : Interval s0Atlas 4 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1248 : Interval s0Atlas 4 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1344 : Interval s0Atlas 4 1344 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 1345 := (concat (concat (concat bs0_4_0 (concat bs0_4_96 bs0_4_192)) (concat (concat bs0_4_288 bs0_4_384) (concat bs0_4_480 bs0_4_576))) (concat (concat (concat bs0_4_672 bs0_4_768) (concat bs0_4_864 bs0_4_960)) (concat (concat bs0_4_1056 bs0_4_1152) (concat bs0_4_1248 bs0_4_1344))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_96 : Interval s0Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_192 : Interval s0Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_288 : Interval s0Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_384 : Interval s0Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_480 : Interval s0Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_576 : Interval s0Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_672 : Interval s0Atlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_768 : Interval s0Atlas 5 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_864 : Interval s0Atlas 5 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_960 : Interval s0Atlas 5 960 57 := block_range (n:=57) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 1017 := (concat (concat (concat bs0_5_0 bs0_5_96) (concat bs0_5_192 (concat bs0_5_288 bs0_5_384))) (concat (concat bs0_5_480 (concat bs0_5_576 bs0_5_672)) (concat bs0_5_768 (concat bs0_5_864 bs0_5_960))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 48 := block_range (n:=48) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 48 := bs0_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_7_0 : Interval s0Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_7 : Interval s0Atlas 7 0 1 := bs0_7_0
theorem alls0 : ∀ k ≤ 7, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
  · exact alls0_6 i (by omega) hi
  · exact alls0_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 4 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 12 := bs1_4_0
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
theorem bs2_3_0 : Interval s2Atlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 2 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 6 := bs2_4_0
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
theorem bs3_4_0 : Interval s3Atlas 4 0 64 := block_range (n:=64) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 64 := bs3_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 40 := block_range (n:=40) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 40 := bs3_5_0
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
  · exact alls3_6 i (by omega) hi
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
theorem bs5_2_0 : Interval s5Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 3 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 29 := block_range (n:=29) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 29 := bs5_3_0
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
theorem bs5_4_384 : Interval s5Atlas 4 384 89 := block_range (n:=89) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 473 := (concat (concat bs5_4_0 bs5_4_96) (concat bs5_4_192 (concat bs5_4_288 bs5_4_384)))
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
theorem bs5_5_576 : Interval s5Atlas 5 576 56 := block_range (n:=56) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 632 := (concat (concat bs5_5_0 (concat bs5_5_96 bs5_5_192)) (concat (concat bs5_5_288 bs5_5_384) (concat bs5_5_480 bs5_5_576)))
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
theorem bq2_2_0 : Interval q2Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq2_2 : Interval q2Atlas 2 0 3 := bq2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_3_0 : Interval q2Atlas 3 0 14 := block_range (n:=14) (by decide +kernel)
theorem allq2_3 : Interval q2Atlas 3 0 14 := bq2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_0 : Interval q2Atlas 4 0 13 := block_range (n:=13) (by decide +kernel)
theorem allq2_4 : Interval q2Atlas 4 0 13 := bq2_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_0 : Interval q2Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq2_5 : Interval q2Atlas 5 0 1 := bq2_5_0
theorem allq2 : ∀ k ≤ 5, ∀ i < count q2Atlas k, checkRow q2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq2_2 i (by omega) hi
  · exact allq2_3 i (by omega) hi
  · exact allq2_4 i (by omega) hi
  · exact allq2_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq6_3_0 : Interval q6Atlas 3 0 9 := block_range (n:=9) (by decide +kernel)
theorem allq6_3 : Interval q6Atlas 3 0 9 := bq6_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq6_4_0 : Interval q6Atlas 4 0 14 := block_range (n:=14) (by decide +kernel)
theorem allq6_4 : Interval q6Atlas 4 0 14 := bq6_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq6_5_0 : Interval q6Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq6_5 : Interval q6Atlas 5 0 1 := bq6_5_0
theorem allq6 : ∀ k ≤ 5, ∀ i < count q6Atlas k, checkRow q6Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq6_3 i (by omega) hi
  · exact allq6_4 i (by omega) hi
  · exact allq6_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq8_2_0 : Interval q8Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq8_2 : Interval q8Atlas 2 0 4 := bq8_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq8_3_0 : Interval q8Atlas 3 0 9 := block_range (n:=9) (by decide +kernel)
theorem allq8_3 : Interval q8Atlas 3 0 9 := bq8_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq8_4_0 : Interval q8Atlas 4 0 9 := block_range (n:=9) (by decide +kernel)
theorem allq8_4 : Interval q8Atlas 4 0 9 := bq8_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq8_5_0 : Interval q8Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq8_5 : Interval q8Atlas 5 0 1 := bq8_5_0
theorem allq8 : ∀ k ≤ 5, ∀ i < count q8Atlas k, checkRow q8Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq8_2 i (by omega) hi
  · exact allq8_3 i (by omega) hi
  · exact allq8_4 i (by omega) hi
  · exact allq8_5 i (by omega) hi
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
theorem bq10_2_0 : Interval q10Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq10_2 : Interval q10Atlas 2 0 3 := bq10_2_0
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
theorem bq17_3_0 : Interval q17Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq17_3 : Interval q17Atlas 3 0 1 := bq17_3_0
theorem allq17 : ∀ k ≤ 3, ∀ i < count q17Atlas k, checkRow q17Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq17_3 i (by omega) hi
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
theorem bq20_2_0 : Interval q20Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq20_2 : Interval q20Atlas 2 0 4 := bq20_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq20_3_0 : Interval q20Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq20_3 : Interval q20Atlas 3 0 6 := bq20_3_0
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
theorem bq23_2_0 : Interval q23Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq23_2 : Interval q23Atlas 2 0 3 := bq23_2_0
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
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 32 := bgb_4_0
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
theorem bgb_5_384 : Interval gbAtlas 5 384 53 := block_range (n:=53) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 437 := (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 (concat bgb_5_288 bgb_5_384)))
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
theorem bgb_6_3648 : Interval gbAtlas 6 3648 90 := block_range (n:=90) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3738 := (concat (concat (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 bgb_6_288)) (concat (concat bgb_6_384 bgb_6_480) (concat bgb_6_576 (concat bgb_6_672 bgb_6_768)))) (concat (concat (concat bgb_6_864 bgb_6_960) (concat bgb_6_1056 (concat bgb_6_1152 bgb_6_1248))) (concat (concat bgb_6_1344 bgb_6_1440) (concat bgb_6_1536 (concat bgb_6_1632 bgb_6_1728))))) (concat (concat (concat (concat bgb_6_1824 bgb_6_1920) (concat bgb_6_2016 (concat bgb_6_2112 bgb_6_2208))) (concat (concat bgb_6_2304 bgb_6_2400) (concat bgb_6_2496 (concat bgb_6_2592 bgb_6_2688)))) (concat (concat (concat bgb_6_2784 bgb_6_2880) (concat bgb_6_2976 (concat bgb_6_3072 bgb_6_3168))) (concat (concat bgb_6_3264 bgb_6_3360) (concat bgb_6_3456 (concat bgb_6_3552 bgb_6_3648))))))
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
theorem bgb_7_4224 : Interval gbAtlas 7 4224 45 := block_range (n:=45) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 4269 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_96) (concat bgb_7_192 (concat bgb_7_288 bgb_7_384))) (concat (concat bgb_7_480 (concat bgb_7_576 bgb_7_672)) (concat bgb_7_768 (concat bgb_7_864 bgb_7_960)))) (concat (concat (concat bgb_7_1056 bgb_7_1152) (concat bgb_7_1248 (concat bgb_7_1344 bgb_7_1440))) (concat (concat bgb_7_1536 (concat bgb_7_1632 bgb_7_1728)) (concat bgb_7_1824 (concat bgb_7_1920 bgb_7_2016))))) (concat (concat (concat (concat bgb_7_2112 bgb_7_2208) (concat bgb_7_2304 (concat bgb_7_2400 bgb_7_2496))) (concat (concat bgb_7_2592 (concat bgb_7_2688 bgb_7_2784)) (concat bgb_7_2880 (concat bgb_7_2976 bgb_7_3072)))) (concat (concat (concat bgb_7_3168 (concat bgb_7_3264 bgb_7_3360)) (concat bgb_7_3456 (concat bgb_7_3552 bgb_7_3648))) (concat (concat bgb_7_3744 (concat bgb_7_3840 bgb_7_3936)) (concat bgb_7_4032 (concat bgb_7_4128 bgb_7_4224))))))
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
theorem bgb_8_768 : Interval gbAtlas 8 768 32 := block_range (n:=32) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 800 := (concat (concat (concat bgb_8_0 bgb_8_96) (concat bgb_8_192 bgb_8_288)) (concat (concat bgb_8_384 bgb_8_480) (concat bgb_8_576 (concat bgb_8_672 bgb_8_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_9_0 : Interval gbAtlas 9 0 33 := block_range (n:=33) (by decide +kernel)
theorem allgb_9 : Interval gbAtlas 9 0 33 := bgb_9_0
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 8 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 24, 26),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq2 (cert : Complete q2Atlas) : Lower true (roots q2Atlas) (target q2Atlas) 6 := by
  have ready : Ready q2Atlas (asRow q2Pos) (asRow q2Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 0, 4),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq6 (cert : Complete q6Atlas) : Lower true (roots q6Atlas) (target q6Atlas) 6 := by
  have ready : Ready q6Atlas (asRow q6Pos) (asRow q6Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq8 (cert : Complete q8Atlas) : Lower true (roots q8Atlas) (target q8Atlas) 6 := by
  have ready : Ready q8Atlas (asRow q8Pos) (asRow q8Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq9 (cert : Complete q9Atlas) : Lower true (roots q9Atlas) (target q9Atlas) 5 := by
  have ready : Ready q9Atlas (asRow q9Pos) (asRow q9Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 2 zero, 0, 4),(inputs.getD 3 zero, 16, 24),(inputs.getD 4 zero, 8, 24),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq10 (cert : Complete q10Atlas) : Lower true (roots q10Atlas) (target q10Atlas) 5 := by
  have ready : Ready q10Atlas (asRow q10Pos) (asRow q10Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 24, 26),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq11 (cert : Complete q11Atlas) : Lower true (roots q11Atlas) (target q11Atlas) 5 := by
  have ready : Ready q11Atlas (asRow q11Pos) (asRow q11Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq12 (cert : Complete q12Atlas) : Lower true (roots q12Atlas) (target q12Atlas) 5 := by
  have ready : Ready q12Atlas (asRow q12Pos) (asRow q12Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq13 (cert : Complete q13Atlas) : Lower true (roots q13Atlas) (target q13Atlas) 5 := by
  have ready : Ready q13Atlas (asRow q13Pos) (asRow q13Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 10, 26)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq14 (cert : Complete q14Atlas) : Lower true (roots q14Atlas) (target q14Atlas) 5 := by
  have ready : Ready q14Atlas (asRow q14Pos) (asRow q14Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq15 (cert : Complete q15Atlas) : Lower true (roots q15Atlas) (target q15Atlas) 5 := by
  have ready : Ready q15Atlas (asRow q15Pos) (asRow q15Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq16 (cert : Complete q16Atlas) : Lower true (roots q16Atlas) (target q16Atlas) 5 := by
  have ready : Ready q16Atlas (asRow q16Pos) (asRow q16Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq17 (cert : Complete q17Atlas) : Lower true (roots q17Atlas) (target q17Atlas) 4 := by
  have ready : Ready q17Atlas (asRow q17Pos) (asRow q17Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq18 (cert : Complete q18Atlas) : Lower true (roots q18Atlas) (target q18Atlas) 5 := by
  have ready : Ready q18Atlas (asRow q18Pos) (asRow q18Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq19 (cert : Complete q19Atlas) : Lower true (roots q19Atlas) (target q19Atlas) 5 := by
  have ready : Ready q19Atlas (asRow q19Pos) (asRow q19Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 0, 4),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq20 (cert : Complete q20Atlas) : Lower true (roots q20Atlas) (target q20Atlas) 5 := by
  have ready : Ready q20Atlas (asRow q20Pos) (asRow q20Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 24, 26),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq21 (cert : Complete q21Atlas) : Lower true (roots q21Atlas) (target q21Atlas) 4 := by
  have ready : Ready q21Atlas (asRow q21Pos) (asRow q21Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq22 (cert : Complete q22Atlas) : Lower true (roots q22Atlas) (target q22Atlas) 5 := by
  have ready : Ready q22Atlas (asRow q22Pos) (asRow q22Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq23 (cert : Complete q23Atlas) : Lower true (roots q23Atlas) (target q23Atlas) 5 := by
  have ready : Ready q23Atlas (asRow q23Pos) (asRow q23Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) (pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p) : Lower true (roots gbAtlas) (target gbAtlas) 11 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact pv
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefee0feeafac0feeefee0feeafac0feeefee0feeafac0feeefee0feeafac0feeefee0feeafac0feeefee0feeafac0feeefee0feeafac0feeefee0feeafac0
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certq2 : Complete q2Atlas) (certq6 : Complete q6Atlas) (certq8 : Complete q8Atlas) (certq9 : Complete q9Atlas) (certq10 : Complete q10Atlas) (certq11 : Complete q11Atlas) (certq12 : Complete q12Atlas) (certq13 : Complete q13Atlas) (certq14 : Complete q14Atlas) (certq15 : Complete q15Atlas) (certq16 : Complete q16Atlas) (certq17 : Complete q17Atlas) (certq18 : Complete q18Atlas) (certq19 : Complete q19Atlas) (certq20 : Complete q20Atlas) (certq21 : Complete q21Atlas) (certq22 : Complete q22Atlas) (certq23 : Complete q23Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 11 := by
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
  have q0 : Slice true (roots gbAtlas) (target gbAtlas) (0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555 : Sig) 8 :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have q1 : Slice true (roots gbAtlas) (target gbAtlas) (0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333 : Sig) 6 :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have q2 : Slice true (roots gbAtlas) (target gbAtlas) (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc : Sig) 6 :=
    slice_correct (ms:=fixRows 0 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq2 certq2)
  have q3 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f : Sig) 6 :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have q4 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff : Sig) 7 :=
    slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
  have q5 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff : Sig) 8 :=
    slice_correct (ms:=fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds4 certs4)
  have q6 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000 : Sig) 6 :=
    slice_correct (ms:=fixRows 0 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq6 certq6)
  have q7 : Slice true (roots gbAtlas) (target gbAtlas) (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff : Sig) 8 :=
    slice_correct (ms:=fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds5 certs5)
  have q8 : Slice true (roots gbAtlas) (target gbAtlas) (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000 : Sig) 6 :=
    slice_correct (ms:=fixRows 0 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq8 certq8)
  have q9 : Slice true (roots gbAtlas) (target gbAtlas) (0x44444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444 : Sig) 5 :=
    slice_correct (ms:=fixRows 1 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq9 certq9)
  have q10 : Slice true (roots gbAtlas) (target gbAtlas) (0x5050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505 : Sig) 5 :=
    slice_correct (ms:=fixRows 5 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq10 certq10)
  have q11 : Slice true (roots gbAtlas) (target gbAtlas) (0x5555000055550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555 : Sig) 5 :=
    slice_correct (ms:=fixRows 17 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq11 certq11)
  have q12 : Slice true (roots gbAtlas) (target gbAtlas) (0x55550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555000055550000 : Sig) 5 :=
    slice_correct (ms:=fixRows 1 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq12 certq12)
  have q13 : Slice true (roots gbAtlas) (target gbAtlas) (0x555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555 : Sig) 5 :=
    slice_correct (ms:=fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq13 certq13)
  have q14 : Slice true (roots gbAtlas) (target gbAtlas) (0x55555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000 : Sig) 5 :=
    slice_correct (ms:=fixRows 1 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq14 certq14)
  have q15 : Slice true (roots gbAtlas) (target gbAtlas) (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c : Sig) 5 :=
    slice_correct (ms:=fixRows 4 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq15 certq15)
  have q16 : Slice true (roots gbAtlas) (target gbAtlas) (0x3333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333 : Sig) 5 :=
    slice_correct (ms:=fixRows 18 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq16 certq16)
  have q17 : Slice true (roots gbAtlas) (target gbAtlas) (0x333333330000000033333333000000003333333300000000333333330000000033333333000000003333333300000000333333330000000033333333 : Sig) 4 :=
    slice_correct (ms:=fixRows 34 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq17 certq17)
  have q18 : Slice true (roots gbAtlas) (target gbAtlas) (0x33333333000000003333333300000000333333330000000033333333000000003333333300000000333333330000000033333333000000003333333300000000 : Sig) 5 :=
    slice_correct (ms:=fixRows 2 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq18 certq18)
  have q19 : Slice true (roots gbAtlas) (target gbAtlas) (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc : Sig) 5 :=
    slice_correct (ms:=fixRows 32 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq19 certq19)
  have q20 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f : Sig) 5 :=
    slice_correct (ms:=fixRows 36 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq20 certq20)
  have q21 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff : Sig) 4 :=
    slice_correct (ms:=fixRows 48 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq21 certq21)
  have q22 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff00000000 : Sig) 5 :=
    slice_correct (ms:=fixRows 16 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq22 certq22)
  have q23 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000 : Sig) 5 :=
    slice_correct (ms:=fixRows 32 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq23 certq23)
  have pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p :=
    List.forall_iff_forall_mem.1 (show List.Forall (fun p => ValidPool true (roots gbAtlas) (target gbAtlas) p) gbPools from ⟨build_valid q0 [] rfl, build_valid q1 [] rfl, build_valid q2 [] rfl, build_valid q3 [] rfl, build_valid q4 [] rfl, build_valid q5 [] rfl, build_valid q6 [] rfl, build_valid q7 [] rfl, build_valid q8 [] rfl, build_valid q9 [] rfl, build_valid q10 [] rfl, build_valid q11 [] rfl, build_valid q12 [] rfl, build_valid q13 [] rfl, build_valid q14 [] rfl, build_valid q15 [] rfl, build_valid q16 [] rfl, build_valid q17 [] rfl, build_valid q18 [] rfl, build_valid q19 [] rfl, build_valid q20 [] rfl, build_valid q21 [] rfl, build_valid q22 [] rfl, build_valid q23 [] rfl⟩)
  have low := boundgb certgb allCuts pv
  have lift := lift_ok (u:=true) (ms:=fixRows 0 0) (raw:=fullRoots) (T:=fullWord) (xs:=[]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 0 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075680 * 2 ^ 32 + 4276812480) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36278.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,1]⟩,⟨.and,[5,6]⟩,⟨.or,[3,7]⟩,⟨.or,[1,8]⟩,⟨.or,[4,7]⟩,⟨.and,[8,10]⟩,⟨.or,[0,11]⟩,⟨.and,[2,9]⟩,⟨.or,[3,4]⟩,⟨.and,[12,14]⟩,⟨.and,[6,15]⟩,⟨.or,[13,16]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,17⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 11) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075680 * 2 ^ 32 + 4276812480) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075680 * 2 ^ 32 + 4276812480) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36278

open PEqualNP.Outside.L_meta_36278 in
theorem PEqualNP.Outside.L_meta_36278 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075680 * 2 ^ 32 + 4276812480) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075680 * 2 ^ 32 + 4276812480) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allq2 allq6 allq8 allq9 allq10 allq11 allq12 allq13 allq14 allq15 allq16 allq17 allq18 allq19 allq20 allq21 allq22 allq23 allgb)
