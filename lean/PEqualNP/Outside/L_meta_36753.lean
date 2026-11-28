import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, children closed at the parent by
-- restriction pools (closeChild of the model), and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36753.Model
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


end PEqualNP.Outside.L_meta_36753.Model

namespace PEqualNP.Outside.L_meta_36753
open PEqualNP.Outside.L_meta_36753.Model
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

def SBf (j : Nat) : Nat := [6, 4, 7, 7, 7, 9].getD j 0

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

end PEqualNP.Outside.L_meta_36753

namespace PEqualNP.Outside.L_meta_36753
open PEqualNP.Outside.L_meta_36753.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x50001052020f610bf43ec20bd42be40de30bc41bd43bf42be41bc40ee20f410dc30
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0xa48023aa7a178080108ea9883d0300425aa420cb54b43
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 14
  | 3 => 6
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
  | 4 => 2*((h/11+packedAt s0K4 (224+(h % 11)*4) 4) % 14)
  | 3 => 2*((h/9+packedAt s0K3 (162+(h % 9)*3) 3) % 6)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xfe03fffffffe01fffff80fffffff01fff1fe3f
  | 3 => 0xfffc03fc03fffe01fffff01fc07ffe07fe63c7
  | 4 => 0xfffffc0003fffffe01ffffe0007ffff81f83f8
  | 5 => 0xfffffffffc00000001ffffffff8000001ffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x9604848428a224242450b162d48b628a26acdb
  | 2 => 0x2ba1292a51451d4948ac0ab56955115551562d
  | 3 => 0x4caba2329a69491d913d58198c66b4479a6346
  | 4 => 0x713233a3639191911dce6cd03078d9e11d83b0
  | 5 => 0x81c3c3c383e1e1e1e1f78f1e3e40e1861ff800
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xccc0c0c0ccc0c000ccc0c0c0ccc0c000ccc0c0c0ccc0c000ccc0c0c0ccc0c000ccc0c0c0ccc0c000ccc0c0c0ccc0c000ccc0c0c0ccc0c000ccc0c0c0ccc0c000, s0N, s0R, (fun _ _ => 0), s0I, []⟩
end PEqualNP.Outside.L_meta_36753
namespace PEqualNP.Outside.L_meta_36753
open PEqualNP.Outside.L_meta_36753.Model
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
  | 2 => 0xfc0fc0fe07e07e07fe1e0f07c3c1f0f87d5293
  | 3 => 0xfff000fff8007ff81fe00ff803fe00ff86631c
  | 4 => 0xffffff80001ffff00003ffff000783e0
  | 5 => 0xffffff00000000001ffffffffc00000007fc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x4000002000000000000100840021008000425
  | 2 => 0xaaa99965354ad4ae8f168b468ad1a2d1755292
  | 3 => 0x326aaaa954d369a2b7710dd2137484e7166318
  | 4 => 0xa34d34d1a69a4d34dbbba88423b9ce422783c0
  | 5 => 0xc38e38e1c71c71c71dddcee73a21088447f800
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xaaaaaaaaaaaaaaa0aaaaaaaaaaaaaaa0aaaaaaaaaaaaaaa0aaaaaaaaaaaaaaa0aaaaaaaaaaaaaaa0aaaaaaaaaaaaaaa0aaaaaaaaaaaaaaa0aaaaaaaaaaaaaaa0, s1N, s1R, (fun _ _ => 0), s1I, []⟩
end PEqualNP.Outside.L_meta_36753
namespace PEqualNP.Outside.L_meta_36753
open PEqualNP.Outside.L_meta_36753.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x100102d040283449000014207304002080ff30fe43fc31fc41fc20fc32fe21fd21fc42ff20ff32ff31fe32fe10fc30fc40bc40fd41fc21fd43fd30bf41bd41fd42fe20ff41bd43bd42fe31ff10fe30ff40fd10bf42fc43be40ff42fe41fe40ff43fd31ff21fd32bf43fc10fd40fe42fd20
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x1c45ccc1c00fc100400680004342c3c00280000000858002d1c3960007c542c241c6c1124082418194800100400218c087c0800040420848808a00810100614980008040010f40020c4057c00240010000c00040c1400a424267ea9105d544409f284813551d0a7aa3a14f54e40af29e835c534427ca890cf14143b7296833d540c35a85904f55021b6a90816d52d073aa7a16b94b43aea98415e53c87ca4210e794f41ba28a619f5350edca5a1c754c409eaa463b751506eca2204fd4d419fa92837651d0b74a0204f553109ea9e853d54cc27aa7a0ebd4942af298213e54cc25aa5a1db948109f2a0873d51902eca3a1dbd4910af29c439d53d067ca0204fd5230aea9e835d5304278a8986d947429e2a2213e50d076a83885b14910baa8e853d54ccb5aa5a0db14930cea1e613d52d0e7ea9084f14141bb28e653d540427ca1a15d54430ea9886377514835aa4204f55031bb288415e531033a8718eb94b419f2a6653d548876aa3a16750d30b6a9463ad42cca7ca8185754c40aea9c433e540867aa921cfd45429faa26176510c27aa998cf54c4096a90813e540836ca2204f943439faa221b5511027aa3a1cf95331cea1c65cd320cb6a8210cf54a40b7290813f5250e6aa3a1cf95032daa0a215d53c86bca6104f952329f2a4435c534827ca820cf54840d6a96873551102daa598eb50821baa8c653e5410b5ca4205794f429eaa0413e54c863aa7a14fd4543baa8841b5410c67aa9195bd49309e2a44174514835a8510cf141429eaa0659d430c6bea6884f950109ea88813d549067ca8994f15210b6a96879e53d0a7aa890cf55242b6a90613e544c73aa6204f95031baa8e873d52d076aa3a1ed947439eaa64176518caeea2986794c40b7296633d54c867aa898db948309f2a6413c544835a84904fd5120cea18653f5350adca518cf953109e2a4615f534836a8398db548108ea9e833d544cabaa7a16d5072196a96837551ccb5a84194f95231
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x502008870c000000004000020400000141040000080042c18c3c08a83029c0000024ca90018082001409114000070a600ae0028a800000800140000000340820400f868758e54c828e62d4d43c954951d0e2d62953108d584548822d62951218dd85529021d63152208b19542483254214520c394d428862f6254640c594d41c861d63152108d195414428d644c8328b58850506356114142c994951d0e1d63951318b588548432652507318d5845050f0e53548408b588548c30d5394840a998b515070d5354b418758e54086a564484218d5875250f165354440a398f5250a1d6395132a99875250b255294743c354e52d07255254440c91494144235619512187195434c22d62d4543c954a511021d6395121a59875350e2d62141438dd85539031553947428d584548c23561d4d428b58a544c6356195032c594d51d0a3561953208b58a54cc30d53548408758c5050b254294732c350e528c62d6295031c554d511030c53509208758e54c431553944408b58a544ca1f6354a40c514d414422d62d4d41a598f515071553547428758c50506356195131a5591310c62f6254e4087d8d51903265254440c394d52d061d63d45428d58654cc30d4314930c550c514c31543946328758f52506356195132
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 186
  | 3 => 84
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (i*5) 5
  | 5 => packedAt s2K5 (i*16) 16
  | 4 => packedAt s2K4 (i*27) 27
  | 3 => packedAt s2K3 (i*38) 38
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/23+packedAt s2K5 (768+(h % 23)*6) 6) % 48)
  | 4 => 2*((h/90+packedAt s2K4 (5022+(h % 90)*8) 8) % 186)
  | 3 => 2*((h/77+packedAt s2K3 (3192+(h % 77)*7) 7) % 84)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffff87fffffffc0fffffffe07fffff8ff1ff
  | 1 => 0xc1f03ff83e0f83fff1c1c1f0ff878787f54e93
  | 3 => 0xfe003fffc00ffc1ffe01fe00fff807f8798f1c
  | 4 => 0x3ffffff0001ffffe0000fffff8007e0fe0
  | 5 => 0xffffc0000000001fffffffff000000007ff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x40000080000000000002021000088080001025
  | 1 => 0x946659119495270cb0d0d1a26c851517354692
  | 3 => 0xcaaaa228d2a613556217484b5502671598b18
  | 4 => 0x294d344529834a5a6b742108da6670226e0dc0
  | 5 => 0x318e387631cc739f8db9b9ce1c4444447fe000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaaaaaeeaaaa88eeaaaaaaeeaaaa88eeaaaaaaeeaaaa88eeaaaaaaeeaaaa88eeaaaaaaeeaaaa88eeaaaaaaeeaaaa88eeaaaaaaeeaaaa88eeaaaaaaeeaaaa88, s2N, s2R, (fun _ _ => 0), s2I, []⟩
end PEqualNP.Outside.L_meta_36753
namespace PEqualNP.Outside.L_meta_36753
open PEqualNP.Outside.L_meta_36753.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x22970070010d500fa8258548c0870021c0089fc43fc41bd43fe10fc42fe21ff21fe20ff20bf43fd219d43fc40fe43fc31fd30fc32fd32dd43ff42fd10ff40fd40fd41fc10fd20ff32ff41fe40fe42ff31fd43fd42fe41ff10de43fe31fd31ff43fc21fe32fc20fe30ff30fc30
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x28480000037010400060280831c8080020b801c8282848001800004000084000a118e800080238182808000a6828000018001010300060181018c070c0388806750c429eaa0219d5150f3a87105dd4520af29e837551102bea6904f55330cf282875d53d0678a8886750f42cea1e419d430c6bca6215754f21cea1a859d434ca7aa990db54b319eaa0653e54042bca621e750d31aea98216f52442dca598dd54742ce28a877551082dca4204f55030aea98859d43c873a87a0e750c30cfaa2879d43c4278a8904755243cea18659d435073a8798e750d21cea1a616e520427ca9994f95221cea82879d438c7ca4210dd54430cea1c617551cca7aa921e750c219eaa0415d53102daa5a0e750e32aea9e859d438433a8720e750d20ae29a419d43d033a86885794f40b6a90615d53d033a8710d794f219faa2419d435027ca998d794c209eaa6653e540833a87205754c20ce292879d431073a86104fd51109eaa6639f5150e7ca8185794f42cfa82873e54c873a87994f95043ae29a215e531033a86086794943cea1e619e5150f3ea4a1d794c41aea988376510c2bca710e714143bb28e655d538873a8621cf55031afa9a215d5490edca5a0cf95032cea18817651d0abca6085b948309eaa4437651102eca2105d14520b6a90213e540c73a872167549439f2a6616c524433ea6a1db54840
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0xc1000a0c01506a070004083ae001c180043c0000c00000100430500140070c00029000c080000c0335a00000000000000240000000300a398a5150e1d6550e21a358a5150f0d4354840c350d52cc61c6550d20c550e51103154394420c550e51d0b154354420879954344315435474287d9543c871543d452087595430430d4394830c350d520421d6494e2187592530821d6414d108758e540421d6395221c350e52d069661d4943a55865250e8d62d454387d9543042966114143c55445150e1d6550c2087592530421d6315110a55875250e8f6254143a31895050f0d4394b31c550d510c2956114143c550d51cca1e6550d20c350d52d071543944308758e54c861c6550d10a39885050e9461541438759253c861d6355030a5d855050f0d439484087590534830d43d49108758c54483154354440c550c514821d6395020c550e51cca8e62d454387d95430830d4354830e150d210870d4394810a35885050f0d4314910c35485250e96619494387d95438861d6550f21
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 45
  | 4 => 129
  | 3 => 68
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (i*5) 5
  | 5 => packedAt s3K5 (i*16) 16
  | 4 => packedAt s3K4 (i*27) 27
  | 3 => packedAt s3K3 (i*38) 38
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/29+packedAt s3K5 (720+(h % 29)*6) 6) % 45)
  | 4 => 2*((h/64+packedAt s3K4 (3483+(h % 64)*8) 8) % 129)
  | 3 => 2*((h/64+packedAt s3K3 (2584+(h % 64)*7) 7) % 68)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x87ffffc3fffffff03fff07fff07fffff38f1ff
  | 1 => 0xf83e0ffc1f07c3ffc707f8787f87870fd74e93
  | 2 => 0xffc00fffe007fc3ff807ff807ff807f0e78f1c
  | 4 => 0xffffff8003ffff800007ffff800f80fe0
  | 5 => 0xfffff0000000003fffffffff80000000fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x80000040000000000008008800088100001025
  | 1 => 0x128c9488ca4a8612c34348513485122e534692
  | 2 => 0x219529114695206558859502595024e2a58b18
  | 4 => 0x7529ce2294c1aab9add0c4446e667044f80dc0
  | 5 => 0x46318c3b18e6333e36e6e6670c444088fee000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeaeaeaeaeaeaa8a8eaeaeaeaeaeaa8a8eaeaeaeaeaeaa8a8eaeaeaeaeaeaa8a8eaeaeaeaeaeaa8a8eaeaeaeaeaeaa8a8eaeaeaeaeaeaa8a8eaeaeaeaeaeaa8a8, s3N, s3R, (fun _ _ => 0), s3I, []⟩
end PEqualNP.Outside.L_meta_36753
namespace PEqualNP.Outside.L_meta_36753
open PEqualNP.Outside.L_meta_36753.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x1e7400000000800000000804400c400000505d2c06802c0093844fe41fe30de43fc42fe10ff43bf43ff30ff41fc30fc32bd43fe21fc40fe43fc319d43fd42fd20fc41fc43fe31fd43fd21ff32dd43fd40fc21fd41fd10fc10fd32ff20fc20ff31fd30ff21ff42fe42ff10fd31fe40fe20ff40fe32
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x3585838f828f80018001809a80061c80100014880b801a0000a781808e828001820000000002868200aa82028f00018180060204001200800000000081801f834f55321cea1e415e53c873a86a16794943ae29a419d43c42eaa2105bd49109eaa0413e54042baa7a16750c43cea1e839d438c73a86186750c21b7290819d43c867ca8194f151209eaa6619d4350738a2a1cf952219eaa0639d434c2dca40879484219faa2213d540c2bca620e714943bb288615c53442daa5a0db54830cea1e615e53886eaa2205794c109eaa4879d5050e7ca818e750d20af29e837551ccabea6886750c32cea1c219d434873a87a06750d109f2a0613f544833a8710d794c43cea1a813e54082eca3995794c20cea1e653e54cc73a8698e750e40cea1c835d530833a8620e750c20b6a96635d5490ebaa6084f95043cea1e636e52cc67ca990db94830aea9e4375510c2baa7a0db54840cfaa2873e54cc2baa620dd94742cea18215e53d0b3ca2a1e754943cfa8a879e5050eeaa3a15b94b41cea18819f5050e7ca9995794f409eaa6653d54886bca6205d94420bb288816d52042baa710e750e42ba28a419d438cb3a86215b14910afa9a419d434ca7aa8085754f40cea1c411d5490eeea29067545439e2a2215d531033a87186750c31ce282879f5250ebca62167d4d439eaa0659d43d0a7aa998d754c42
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0xb8000002a66c00004000cf04000c00506180005000000000401d0000000200000100b80013c1000000000000a580003c00080005001500014810c000000200200020000d87595438871543145208759253c861c6550d10c550e511031543d4520c350c524421d6494e218758e548861d639532187d9543c870d4394840c550d511030d43548308758c54483154394742c350e520c385434842187590534821d6494c10a59875250e1e6550d20c550e510830d435481087d95430430d52149438759543c868d621414387995434431543944308758c54443154354742a59845050e8e621414387d95430830d4394810a55845050e1d6550c2087195434830d4354b41875905344296619494387595430428d62d4543c550d510821d6494c20a55865250e1f6550e21a398b5150f154354732a358a5150e9561d4943c55445150e1d6395010a3d895050e976154143c350e52cc70d4354b31a31895050e8e62945438758d540c29461541438758e54083154354430c550e51ccb0d4394b41c350f524430d4354840
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 45
  | 4 => 129
  | 3 => 68
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
  | 5 => 2*((h/36+packedAt s4K5 (720+(h % 36)*6) 6) % 45)
  | 4 => 2*((h/64+packedAt s4K4 (3483+(h % 64)*8) 8) % 129)
  | 3 => 2*((h/78+packedAt s4K3 (2584+(h % 78)*7) 7) % 68)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x87ffffc3fffffff03fff07fff07fffff38f1ff
  | 1 => 0xf83e0ffc1f07c3ffc707f8787f87870fd74e93
  | 2 => 0xffc00fffe007fc3ff807ff807ff807f0e78f1c
  | 3 => 0xffffff8003ffff800007ffff800f80fe0
  | 5 => 0xfffff0000000003fffffffff80000000fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x80000040000000000008008800088100001025
  | 1 => 0x128c9488ca4a8612c34348513485122e534692
  | 2 => 0x219529114695206558859502595024e2a58b18
  | 3 => 0x7529ce2294c1aab9add0c4446e667044f80dc0
  | 5 => 0x46318c3b18e6333e36e6e6670c444088fee000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeaeaeaeaeaa8eaa8eaeaeaeaeaa8eaa8eaeaeaeaeaa8eaa8eaeaeaeaeaa8eaa8eaeaeaeaeaa8eaa8eaeaeaeaeaa8eaa8eaeaeaeaeaa8eaa8eaeaeaeaeaa8eaa8, s4N, s4R, (fun _ _ => 0), s4I, []⟩
end PEqualNP.Outside.L_meta_36753
namespace PEqualNP.Outside.L_meta_36753
open PEqualNP.Outside.L_meta_36753.Model
def s5K8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K7 : Nat → Nat
  | 0 => 0x3031000400404c000b1ce09e0040801c0543200fc42fe10fc41fc20fd31fd32ff30ff21ff10fc40fc32ff31fe20fc43fc31fc21fe30ff42fd30fe31fc30fd43fe43ff43fe42ff32fd40fe21fd42ff40ff20ff41fd21fe40fe32fe41fc10fd10fd41fd20
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x883fe318c3f621087f4cb10ff99443fc42c87ea83887f54221ffaa463fd32107fc6218f714d10ff286637d5090bfe64887f08640dfa1a81fc42c43fa41087f8c832ff98621ff5210ff86420ff8c720fe19681f541443faa2907f90942f7194437d53843fc65985f54032ff28465de53d06fea990ff10e40fea1281fe5090bda6410ef50040f790041ff53c86fea0997f90f31fe99221fe31842fca3a07f14732fe21221ef21887fc87087fd0330dfa0e81ff31043fea1197f94341fe98c43fc32c43daa4087f50620fea9061fc518cbfe8498ff94c20ffa1821fc40482f8a9087f90c31deaa643dd53c87fa83207f4c430fe2a443fc40043fc85a07f50b32ff21465fc43883f883985bd4910ef99261bf41106f8a2a1ffd0140ffa1c87fe32503f8a8197b50a32fe18821fc32443faa5087f10630fea9c41fc21083f882205fd4e21be2a641fe544c2fca3a17f50420faa8861fe31102faa710ff94f41fe284837e53482faa610ffcc110ff90021fe30043ee6298ff8c831eea1887f721487faa8197f54341fe290637d50d0f7a87a07f54143fe2a0637d5190bfa6290df54b43fea8c81ff31887baa6087f90841ff080217c5050ffc87907f90e30ffa82653d54043fa64987fd0641fe20a817f540c3fca8107f48420ff29c41ee42087fe65a05f94f42ffaa043fe54c43fc85886f50c41ff996437c51483fea7217d48710ffa1441fc424c3fc84887f50310ef18261ff5290ff8a918ff15130fe98a417e52843f86310ff50110fa90a21ff520c7fca610dfd4810ff98261dd32cc3dca421df55031fea8065fc53d03fc63107fcc841ff18a637d54443fca6207f55230ff10e41fe218c3f8a7a17fccb10fe29483ff42082faa6207ed0240bfa9821ff5250ff864985f94a31ffa1a85fe43103f8a890ff14f41bea8483de53043fc43087f50831bf2a0617f51503fa8598ff0c020ff2a043ff41087ba64195f14e20bfaa265fd21883fca6a17f54843fe28465f551103fa87a0df54043fea9e857d53c82faa22177cc530fea96817c53843fca7a07f48640dea0e81f631c43fea1a0ff55221bf29e41fd43907fa62085fd4131fb18a217e544c2fca3107f94930fea84857e53903fc40907f14343fea9481fd42c82f8a6907fd4841fea1461ff438caf8a8187f90421bf286437f54443fea3217f88440ff21261fd508cbfc63207f54f21ff20241ed32482faa9105f94720fea8a87fd404c3fa85087fd4b30f7a1485ff43c87fea2907f94243de2a221ff50907fe87a07f54630bf2a4617e500cbfa84207fd4141ffa1e213e54cc7dca598ffd4432dfa1681fe434c6fea8107f94d41ffa1883fe32c83faa018df54840bea9c657e54cc3f8a6884f55020bfaa243fc31d02fca5217f90010fa88021ff324c3fc65186fd0841fb88021fd53487f86390ff10731
  | 1 => 0xc30882f8a8905fd5221fea1c61fd21cc2fea690df14132fe99463ed52cc7f864907754c20bf29887fc52103fe8610ff55132b6a9087f6510c2faa810ff90020fe21463fd43c83fca2105f14141f6292217d5310bfe82207f8c930fe28a65fe20083fe60907fcc830ffa1a83ff53d0adca598ff8cb31ffaa6437e54487fa8610ffc8530bfa9a41ff53503fa87087f50731fea18817c5350bfe80987f90921bea8063ff5010f5a84217e84010bf28843df318c7bc87997f0ca31fe90a81fc31087fc86217f14221fea8263de324cafaa6107f54620ff29a43ee52d07fea6087f08720bf28685bf40902faa9985f15031beaa461fe31cc2fca4087f10530feaa663fc218c3fa86105f95232fea9683ed42483fa61887f90920ff98a43f5310c7ec8220ff10810fe990217c53887fa8218ffd4630fea0241f621087fe6490ff4c110fe29681fc50487f8a3a17f08610ffa9c21ff52903fea9107f10c31be29021fc5090e7ca8197bd4910ff21a65fc504cbbc63187fd4d41ff28a65fc32042fca1197f90531fe21c617c53087f8a518fbc8520ffa0a63fe428c7faa3907f94143fe21e41ff430c3faa9987f50720ff99241fb304c3fc62a07f54c42ff21865fd418c3f887087fd4332fe28881bc41902faa2107b8c920bfa8287fd41842fea5885f54a41fe2a043ff30043dca4087f08440fe29e437f54483ec83885f54630ffa1e85fd32887fe62187fd0b31ff29483ff41902eca2107d905109f2a643fd32c87f886207f55131ff28083fc42887fe6518ff55232ffa1a43de53083eca2207f90f30bea8083fd31087fca021ffcc740ffa10637e52c43fea018f7d0e43ff280637e520cbf8a3205f14131ff28243fc310c3f885195f14a10fea1a63de430c7fc83105f94643fe29841fe42043fca918ffd0b20bf2a4217c52c43fc8590df95040fe19443fd41103fa80085f14d21fe18641fe300c2fca410ffc8540ff28c81fd54083bc6298ff90e42ffa0c41fe41903f886105f54e30fe29683ff42843faa8887f50e20ff21a81fe21cc3fea31977cca32fe18421ff54443fca710ef50441fea1065ff42103f84310774c930aea9881fd4210bfc82105f94831ff90e61fd218c2faa890fe48020bf2a021fc31487faa1a17fcc810ff188417e51042f8a6086f95032bea8c217c540cafea9195f54430ffa9e81fe50c87fe86907f8c310ff28263ff540c7fa43087f90f32ff98a41fc510cbfc8510df54a43fe90e417d548c7f8a8107794c40fea1661bd42906d8a4887f88540fe28063fc400c3fe82107f50e40fea9083fe324cbda8510ff10d31fe18a417c52506dca4185f15230bea8c87fe51d03fa42205f14532ffa8a87fd32d02fca5a0df55032ffa1c637e50886faa4087fcc631f7904417e5110ffaa090ff50531fe29263ff20483fc60907f10b40faa0
  | 2 => 0xefca8107f10410ff20461fe30883fa86997f54e21ffaa6619d4310ffa86217f90f40f6a9081fe40c83da65905f94e41beaa483fe43c86fca010df15110bfa9283fe5190f7e86a17f4c821ff988417e53106faa3907fd0c20ff204216e52103fa60907f14c109f2a061fd10043fc41087f95010ff88021fd52cc3faa521ff90c41fe20041fc51503fc62987f95232fea9c83fc31083fc85a0ff94c41ff19443fd430cb7e8620ff90d10ff10e81fc41887f8a021ffd0540fea1643fd54843fc60107f90f10fe21043dd53d07fca420ff54332ff29a81fd43cc37a8720ff54043ffaa261ff32907fa63207f10841ff90041fd5190efca8215f94241efa1a87fc40882fca018ff94d20ff20081fd52042daa4187f95030ffa9c81fe52cc6f8a7887f08210ff99683ff41cc6bca6205f54a10fe2a2413f54443fea4187f54331ff28a81fc53107f886997750c31fea1681fd53087fc43885fd4910fea1465fc32087fa64a0ff50e42ffa8861bf43d03ba6518fd4c710ff10a21fc4310bfea610fb48520fea1a81fc42506baa6217b94830fe10e61fc548cb7a86a17f94141fa98a21ff508c7dc85907e8c030fea9463fd43ccbfe8720fb50821fe28a41fc540c2fea6a05f14931fe21e83fc51cc3fa60087f95321be29e43fe50886faa5205f55242fe19643fe54cc7fe6390df54a21bf29c41ff528c7f886197f54443ffa1265ff54cc6fca521ff10f31fea1083fc43cc3f864a0fd54420aea9841fd5390bfa63105f94442bfaa063fe434c3fa84887f90821bf28861ff43886f8a9885f54a20fea1621fe32d03fa83986f90541fe10a81f521087baa6215f94c40ffa1481fb40503fe84217f94843df2a643fe32c877aa8087f4c830fea8c85ff52c43f8a190ff14d20fea8083ff41c83fe43a07f10830f719043fb20483fc6420ff14642dfa0081fd50087fe80887f8c910fea8a85fe528c7fe83087f88530ef21a65fc4390bfe87a0df94331ff20e637d53883fe6410ffd0832ff196217e510c7f886a07bc8421fea9461fe42507fca5887f54f41fe19061fc41d037a8621ffd0310fe2a663fe418c3fa82a07f90431fe20e43fd54ccaf8a0a17f95220ffa1661bf42907fea9195f55132b6a9683ff410c7fa62107fcc030bfaa261fc42487fea4085f54231fe99243bc41103f8a5887fc8710bf290617d5090fde84a17f90610ff90a21fc43ccbbe6518ff54931ef21e61ff418c3fc83907f94442ff20441ff32507fe86a1ff94e10ff284637e54483f883887f4c920ffa9c43fc41443fe85217f94742ff98843fe50d0ffa84987f50c31bf28421fc32487b862187fd0940fea1e63ff540c37aa8187b94840fe21241fe41103f8a1a15d54440fe29a43fe420c3f8a118ffd0a30ffa0461ff10443fea720ff90030f710a43ff53d07fa80186f90d43dea1e85f
  | 3 => 0x83a07fcc630beaa261ff52843f843887e90040ff98c21fe31043fa83887fd0f20ffa9a43fe424c7fa84187b4c832ff29683ff31c83fea6907f50721bfa9281fd510cbfa62a05f94c21f710c417f54c83f8a1a0ff14b43ffa1465fc318c2fea9107f94f21fea9663fc43106faa421ffd0e10bf28683fc31c83f865207f14f10af298417d5010bf884107fd5020fe21e21fc52443f886887f10430ff10a41f741907f8a421ff90330df20c81ff51903fe6498df55120ff98441fd434c37aa8107f8c320bfaa0657f514cbfc64187f14032be298413e54043f842985fd4121fea0a217e54cc77a84217f15110fea9063fd52507faa2997f50921fea8487fe30843fe62207fc8210fe19041fc5050bfe86205fd5331ffa1643ff51d0ffe65207f8c621ff2a063fc54883fe42187f90a40fe29c817d54083fca9997f90a20bea8643fc52506faa921ff90c10ff20281fc31103ba86997fcc020fea0441ff42107dc42107f54530f721265fd42482f8a8104f55032f7210857e54106fca3207f54430fe20461fc510c2faa1997fcca20ff98c81fd5010af8a2a05f94043ff19243ff42c43f881905794f21ff28a41fc40842fea9985f94e10ffa1221ff52d03f861885f54742be29a837d540c2f8a998ff0c110ffaa241fd504cafea8085fd4141fea1463fd21d037ea8885f94441fe29261dd43cc3faa120ffd5230fe21a61fe32483de64997fd4910ff28685ff21486faa9997f90820fea0a61fc54ccb7c84a17f88410ffaa2437c5250efaa5187f14740fea0041fd5350bfca4086f50940ff28a87fd32d06faa221ff10521ff90a41ff514cbfe80905f94242fe98c617d52cc3f8a7907fd0d31ff21c437e54087fe6298ff0ca41bea8c81ff54887fca5187fd4041fe28085fc41483da4210ff95320beaa643fd21c43fea3107fd5032fd88221fe328c7fe64107f48510ff21a857e50d0ff8a6217f4c431ffa0e61bf41907fca4207fd0b32fe21483fe51ccbf8a4087f15310ff18e81fe52d0ffaa7207f4ca41fe98881fd31c82fca6107f50810fba0a83fe31c877e8721ffd4e20fe90621ff51d0bfe84987fd5320fe216837e53c43fe63107fd4242fe90221ff328cadaa598fd84110fe98061fc418c6fca598ffd4940ff29281fa20083faa6a05fd5310fe98c21fc31882fca8887f94e41ffa8e41fd51102faa3106f55032eea1e65fc5390bf863207790d30fe29c437e51886faa7217fd0e20ff28a85fe31c42faa6887fd4b43ffa1c817c540437ca8107f8c510fb88421fc5350bfc64087f94630fea1443fc5050efca1185fd4e10fea9281ff40043fca890df94f21fe196837c524c3fc87197f90730ffa8443fd548c7fca898df14910fe90a617f54087fca7a15f55331ffa9841fd50507fa84997fc8220bf28e65ff21043be60185f94641fea8e877e539
  | 4 => 0xff50c10fe10221fd320c7f8a2985f54341af29e837e50902fca2197f54c40ffa0c43fd53d03f88718ff4c931fe21063fe548c3f88790efd0842ff21843fd42087fca3a1ff4c220fe2a661fd418c6fca5185fd5230fe99641ff42486eaa2105794c10ffa1865fe50ccbde65197fd4740b729683fd210c3fa65187f0ca30bea8e81fc428c3fc80987f0cb31ff29c85fc42c83fea6217f94430feaa243fd32843fe87986fd0e41ffa9a21ff5110afca4207f94042fe10821fc53103fe63987f50441fe2a021bd41503ba63987fd0920ffa8e617e52d03fca4a0ff14d40fe21421fc31cc2faa2207f0cb20fe18241ff308c2fca9905f15231fea94837d510cafaa4185f14f20fe2a2637e5090efea4987f0ca10feaa043fd30082bea6887fcc210ffa0e43fc5250ffaa9907fcc320fea1a85fe42cc7b863187fd0e42ff21461fd41043f886087fd0a31fea9081fd32103fe62a07f14743ffa1a81fd408c3f8a2217f8c430bfa9a857d528c6fca520df54e31bea9a41ff52cc7fc8418ff8ca41ff21887fc5110ffe83a07f94830ffa0e21fd51cc37e85217f0c540ff19683fc50507fca7207b54843ef21c63fe21087fea9086fd0940fe90a41fc324c7faa3997f90740bea9621dd434c3fe87995fd4542ffa9e4175510c3da85907f15132ff21641fd438cbfe6598ff0c840ff20e437d53043fea0a1df94020fea1e43fd40c83fe65185f95220bf2a665ff320c6fea2a1df94630bf29221f9300c2fca7215fd4520f710241fe42843f881986f90440fea1e817c514c2fca910ff10e21ffa1021ff41107fa81087fd4342fe29461fc52503ee6318ff55130f790e41fc53087fc87a17f14e20fe180217c54ccbf88498df94040fea0c43ff32c837e8621ff90710fe28c41ff41443fe64207f8c520ffa8263fd524c3fc82887f90c30f7196416d52103faa990df94420be2a643f6310c7f8a010ff14a40ff21081fe51102faa7887f94a43f690041ff32843fe87187fd4840bf28c65fd40103f641107fd0c43ffa80657d50cc7fca498db94843beaa421ff54ccafca8995f55010fe21a85fc32883fe80185f94f41bea8e87fe51883fc8520ff48410ffa0a617e53043f863085f54b41fea1883fc5150ef8a890ff90540ffa9263fe32087fa64107f50941bea9e857f5050bfe8510df55131deaa663fe43487f8a5985f94220dfa1e85fd43c43faa6887f88430bb28881ff544c6faa7a07f50d10fc88021fc21d03fca8887fd4a30ff29287ff21087fa63987fd0942feaa4417f53443fea010ffd0b40ff19283ff43cc7fe6218df54d21fe900217d518cbfc8718ff08510ff29e21fe54483f887a07f10e32fe28c87fd32883faa118ffc8621fe20843fe414c3f8a020ffd4b41ffaa621fd32903fe8618ff94a40ee98061fc42883fc86907f88521ee98863fc42903fa
  | 5 => 0x843bfa9843ff10843fea7887f95210fb10a21fd54043faa3a177cc832ff21c81ff21103faa4885f94b43ffa8243ff42d06fca5985f94e21ff2a4437e54c43fc65207f94241eea1c635d53d07f8849977ccb30fea1a83fe53043fa8498df54e41bea9083fe4350ffe82187f90430be2a441fc548c3f840087f14332fe29083fc40c43faa6907f95132be2a265fc43087fe86987f50c30ffa8a85fe510cbfe62987f94b40fea0843fd42d07ba62987b4ca21bb288617e52107faa8187f10110feaa241ff41482fca990ff88640ff21841fd320cbf885985f94c32ff10c41fe54cc3fea6a17f0c530fe908437c50487f884195794c42fe216637d50887f88298ff50a40ff28065fd32cc3fe43207fd4142f6a1265ff41487fa82187fd4c41ff28e61fe304c3fa87a17f4c320ff99065fe324c7faa7907f8ca20bea8043ff53103fc8290f7cc431fe29c83fd53083fc8318f7cc730ff280437e50ccbbaa6207f14b31ff28c85fd31d03bca6217f54b43fe28485fd30843f865985f95043ee99063fd31c86f8a898ff88110ff28a61fe21083f280207f54e10fe21a83fe424cbda84217f54321fea14417e548c7fc82906f50b40bf29863ff42087fa64a07f90842fea1a437f514c3be61187f54343ef29e433e54082fca7a05f55232fe21281df53442faa7207f15210be2a4433c54443fe8318ff08430bea9681fd31c43f8a198df15330ff18a43fc404c3fe64997fd5010df2a0217f53883faa818ffd4321ff21065fd31442fea6107fd0240ff29661fd518cbfea4a0ff10b32bfa9421fc32502fca8197b90a21f690e41fc5290e7aa998ff90b30fe20c41fd52c43fc86a0ff50820fea8841ff42507daa5a0ff94910fea06617d51ccbf887a17f14131ff90c41fd43483fe81107fd4440dfa0a817c53443f8a210778c430fe218617d53c86f8a6a05b54810bea98837d508cbf8a990ff54142bf284637f5250ffea321f34c832fe20c81ff5090ffe65985f15021fe28c617e53443fea4985f54f41fb28841de4310efaa9885754c10ff19041be540c2fca318ffd0410fea8e81fe52843fa8718fb8c832bf290417f53507d843107f88310ff212817e500c2f8a9197f08520ff20821fe43d07fca0997f54f10ffa8841fd314c3fc81887f15320ffa86877f548c7fc8720ff10840ff202217d50d0bfaa4a1f7cc831ff908417e5010bfe80106f50d40bea9663fe31087f88690df94010be29281fe42ccaf8a2a17fd0830f6a9061fd41487fca0a17f94632bea8e61fe51c83fe64a05f54831bea92217f54ccbfca221ef50841ffa8e65fe41106fea7887fd4a41df2a663fd42906fca6217f10420fe29c21ff434cbd842105f55221fe19063fe53c83dc85195f95031fe21a41fd43887fea198ff50520bf2a263fd32cc7fe86217f94c42ff2a065fc20c43fc8310
  | 6 => 0xd072248010890040b41481b03200051002004004790020000000180001a000000000000d06f85d0000003b819006858200120060180380406c0e00200d02e01c0100004a00806a160020ac0183100e0080c00000a00008814002560031280840100003002405406808000194021290000044400000001c09b300b20a80402c01c0400680511e000cd80301204007058000004010110260000600b11e7b80681f30c009218080021bc19005000004010000841f17b00e0180009d2430246a0002480000680c80a00002c0200100ab9c0180004e3fc0c8060020000582b0000000e8031800246180b000008028060080240080f00e00056802000000000230020001000005002c0903204e174008061520340204d0081cc1f09c008000031d102401c0301002e0680d8460008dc0400807c000030140000141400000e0009f87d01e0180a0010000000280702e0040f0320cc06c2ba4b068274fe0ad03e0c4018030500180301f0000000c8022da00404806036020000020000041d845088100000150d679c0080036a028088000600106880a0060104181d00c15c338034ce164000080020700680003200000815002130120000000442781044e1040507f00001cc18000720040080401c3bc070020520940400902400002816286080010050100200600a0920000100000200001b260080002b03b00864c3d90b00a000a200400e6681500801000c058080000002500303a000050ce000004310010466700f003028000028182bc00490801000400768031740304f9080180280181a0421a4000a60000941902009a010011be01cc8d0681900006c6280f0320900b80401e020470040980bc0801111201419803014020000000500780180e008028010000460000686d0bc0a80702801e04ccc0022520001e0240080140e80c0020080181c01e0006280302e0380000000200005802006004008080120389500b25404c0100b016000ea81000202c0107100a01c008000e402c03b04002004da0000de0140500b1d40a8028010030ec048010260000504008601c080310260082280002a0ac00800001fe43883fa8621ff54c41ffa0421ff21c83fea0217fd0320fea8885fb308c3fc65087f14830fe90041ff314437c80a07fc8630fe29421fc51c83fe63885f94642ffa1a21fc410c7f883907dc8621fe21c83fe53443fca418dfd4f21fe29a83ff40102fca690ffd0541bf29465fd54c43faa6087f90541ffaa2657e5210afea898ff0c710ff90c21fc31442fca3a1ffd4540ff10021fc5150afaa9205b94810bf29861ff514c2f8a8987d88710beaa641fc41843fea221ff8c840bfa9263ff20c42fca5205f94440ff182217e50106b8a6885754f21bfaa421ff20443dc84904f553219eaa0617f53c82fca3987f54d41fea8a81fe10443fe8520df94
  | 7 => 0x1f058aa400065430000098010020040382f20805c051fc000178058021d0000019a60021183880a0023543302e0060dc9f8001c809d3200b0600100280004204d900fd0100f0010024ea0140f801090068000000180a81200003e0006d00b0168d8058060020200780001c0003d0000680100b00b03800c0f9f000c08c0d31f01a07ca70010100009db8d0181d0088
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x7401035d538c421cf58e54c873d5350b40b798c428c27d6494b10db58b538836d52d0430bdd85428427e6094a419f9885150f3d54d0c329fd8153106dd6314221f918910042bd63d0740cf95131c867e63d4142d954a510c3ae62d0540dd54531902ee620c010bd58742886fa6010c40b758e548867d6590c20ddd4651d0e7d6195230bb58b415027d63d49409fd9443c42dd63c8530d79815310a7f6354342d9949510c36e62d4f20af58b41d035e43d49309f98f525026d658c821bbd89310826e62951319798c54083f231c4110dbd95521027d60d53319f59641482df624c431bd58341906be60d0e41db948321035d544c832af590538435f5350910d794c400827c6354841dd54d51102ee6215230cf15343442f5610cb31dd146415023d64d4c20bb195424ca7e6094841cf55031043b54110731d754d401036f5294943dbd9552cc76d62d5331f9d4521c827f6550c32bd58432c86fa6008540db548520c2ee62d06209f5935244376510c730db18e52102ed62d4440db948421073e5490210bb988510c27f658c840d794e308827e65905209fd95218c2be64c8621bdd85524c35e53d0f42bb588530435d54d4d10db58d521036d53c8020db94b511033e5450e32be58043cc3756354420bd98443c427e63d45409f1895010777518c530d794e329067f62551219f98754043756294430af993310c27e6194830b718d42cc67e65d0b10cb552320caed6214c40afd8d41502dd6394b109f196215035f6550f32db54932d033d6494b10ded42508875e53484408f596540c36f548cb20d714e315027e65d07309f594438427d62d4530b758f414c39d4310f219f997415027e650ca40bb58b414839d4310e41cb55152042f561d4c20eb9514210b3f43540419f9805150bad4210a10db94d520427f6054d20cd58454442ed62144439f98c524427e62150209f58253487af4350a32ddd85534427c65104219f997318827e63d4542db54b219027e65d0c10db54b200436c654c920d7547308c36e51487209f19543c827e6510d30d794d42d06ed6294d10f3985320cb6d5390920af593510c2be6408110cb551200827d658c720cf95051082ee6214f41b718143cc2ed63c8520cf951421033d5410f21d798853443eb5088120bd586544cb754294420bb59321086ee62cc5409f594420c67e650c120d394e52d067c65d0e219f987548c3e86050920f5984318c33f54d0d319f595321035e5450f30bd587434436c6254640cfd51430c67d6508010dbd4b414435d6314121cf981540cb6d6494810dbd4b208435c5450c31d794e52103765110030dd58653443ce538c821ded4250c873c5450531d7952434c36c5210910cf191518827e6094f429fd9621d02ed6190821ddd85534875c53d0d20db54942cc76e4254021eb950210836c6494830
  | 1 => 0x433d6510640fa58242c827d62d5110f694e401036e52d4430d758e544c36f544c920cf55042c833c54485109f580530867d6510520bb98b31cc33e5490020b798f418c2ed62d0631cf95342cc76d520ca419fd9543482ee628c4219f99421482de630c930af983425035e5310f42d794e320427e6395020d7d52530435d53480209f19742843766114c20bb58840c427e61d5220f514e314433f5450920be58021c425c6550d30d79825310bcd5350842d754f328435c534c1109f995424c33d548c820b758c41cc35f53cc710bd586420873f5410310ddd465110b5d5310020cf550548427e6590930cb549401027d6015131f94ca210867e650c020db58e521033d61950329f997414c33e5490531b798e424c2bc6444010ee951300c27d6115020db149424427f6255210bd58442c867d6294630b798e52c42bd6414031e714d43107755188640db59621082ef6348520af59331c42f7624c710b358f218876d6454830cfd50418427e65ccb40fc181414427d60d5321d7d4f30843cd320c910b758c418c6ee6210c30bd58a104423e6414e109798c548839e5490f309f18d511027e6510620db18d521027c6590c21db5974290b6e6215210db550524435e534cb409fd81521075d63d5221bb189438827f6454a31cf951310435e6315010afd814350a6d6215330cf153428caee62cc631afd8543d02ec6250e32d798e54442f561d0c41d754e510827e658c941d754c50c867e65cc930bd18543043e562cc6319f58c54c43f25150040cf15143cca7e6550a10af994544437561d5321cf152424437565c4010db54a5110e5e6395110bb58831c835f6354f209f1855210e7c6354b41f58c6304433e6255010b758c519035c530c310d794d42c876c4394830e754f43d035e53cca20bed8141503b9544c0309f597424427e650c510cf15152442f561d0841d794d430435d5314810cf59053c867e62152109fd9541487d56190c31af993318427d6550130bdd855050fb54390510de597409027d6590d10b758c424c67f6154a30d754e308427f6154342bb988438c67e650c840cf58654083756114910af59050c867e6194f409f195325035e504c0309f58b540433e54104209fd89544ca7e6015231de58352c42bd640cb10be58031882766114132bd587404427f6550b30d7d9553d06ef64881209f98254cc6bf6454131db58a544ca7f6055231b798c40c42ee62cc120db949210c3e52108520cf55143c833f6455310b7d8d505067e65151109f18d521027f650c0109f58f520435c5310d20cf993530833e53d0c419f99643482df6150d30be98242902ed6210f41cf550544c67d62d5030f3551320cbaf6450a329f58454483e95244010bd986321073d5454331d794d52d075d5344010cf551430837751c85309f98a510c35e538c621ed94
  | 2 => 0x54548109f595420436d5454b31b718543ccadc6354142cfd8254c867c6510c10af99050cc6ef64c8621d754f211033f5495231bd9845050abe64887409f994424831d5310440be583418433f5490110cf950414867e6494031cf58a54043773294420dd59741907ea52500409f597410833d5414810bb98b434833f5450d21b758c540833e61550329f59443c833f6355020b798f54886dd64cc930bb58b41c875d53cca209f59431d027f65d0f10d7d4e304427d61951329f59432d02ad62d04419fd89508c6bf6454121dd54f108437b5094343be580411033d63d5110f390d320876c5454830dd98454082f56110030f9d4621487b45488510cf151434c6ed62d0730cfd50414427d6094b41f3909328c67d6414c109f58c52042f96090d40db54b32cc67f6354420de54050c875e6314e219f99251883775194530db94930042bf65508429f580540c75d6315232ded81534827f6510a30f350d424cbe7528c510af99351c82dd608c630d754f311039e5454f21f60c6300c35e53ccb41eb50b5110a7e6194b40dd94630082de6310831af990540c27d63940429fd81539073d53508429fd9541cc2bd64cc7409f189531035f54cc831db50e52d079c6250c43bb189414873d5444010bd986544cadd6310330be58242083b54390441eb94b40102f9608c7109f587530836e6294c21bb58b41cc75d5390010d754d328867e658c4209f191508caed6215330b718d514827d658c910f958b41906f661cc1108f590520427f6550932db94920c436f524c110dd54441d033d54d0c21af990315035f31540319f58454ccaf56488710fc907104433f5495321cf551438833d5490f32b7593314c27e63d52209f99743502bc64484409f98a540c76f5294841d794e20043af4350842d754c32d067e65d0d21db50d520427e61d5120ee98343d027c6550f10cf986540cb3e5490e219f58354ccabd64c8710d754e308827f6155332cf152414c35d53104108f990524c33c3055030dd485500873d54880209f99721482bf6250441dd58454882ed62105209f59654043d5314c310fc545300c2df63504309b98b540c36d52d0a31ed50441c873e5488410d750d528c7b664c8521bed91401027d6414131d794c210827e65d0921d714b324c2bd6510640d7d8d519033f6454910b7d8d51903d65344010db54b32cc2de63887309f195434cb766114c10bb988438435d53143419f59350486f56110f31cd552510836f5288540db98b53c86bd64cc420db98a530c6fa600c620db14a425067f6510d20cf153424cb6551c8020cf55243cc7b4544c510cf150434427e650c9409fd96410c27f658c820cf18a54cc73d6494f109f98f544435d538c4409f58e501067d6590440db94842d06ed62cc630ebd814210add6310a21f3149320c67e6414f10f5cca314
  | 3 => 0x6209f994524426e6294d109f19743486f660905109f59352043ae62d0641bb58b41907cd32885309f988535073f6550c43d754d30c427c6510d10bb988530427f6254f40db58152cc75e5348020bb580210835c6054c10db182520c376510c4209f195314827e64943219f590514cb3d5410410cf552430cb6e5250b41d759643cc2f5610c210b798f410c6de63100209f595420c6f661d0e31af59742906be64d4c20dd987530833c6055010de94e300c2f66190f219f98b53042ed64c8520ee106401036e52082109f18151cca7c65d0520b358f210867c6054b41ed545401039f6350f42cf55132cc76c528c110d794c42043e65188420bb588434c27e62d52319f58c54c86f764487109f99352043774254440bd5875290f6d544ca21bd587434c7ad42108109f18d54c435f534c9209f588548c2f56110210cf550420833c62553319fd8d529067c6548630d714c324435d530cb219f592534833e54d4830bd584540c2de6390832b758f428c76d524c030d794e51083ac4350842bb58b434cb3f60950329f5845050f5d6315132bb98830c43ad42109219f9865010f5e52cc831af99032507766054420f514e414427d6294740fa54a300c2ed6214630ee58342d027e6494732bb58b310c67e6550c20b798a43cca7e6414131bd98643cc76d52880109f189540c7da534c030d754d400833d5450a21cfd0f525035f5350d42dbd8252cc67d6114e20cf951310837661d53109f59642cc6f960cc920d7d4f324435e5450e319fd96418833f6455232f350a324cade63c86309f98a51d0f3d5415221bd587521038e544c832ded425050f5d5390f20af990500c75d54cc8319f59632c42ef624c1209798c548427f6154b30bdd9221443746394430af590530873e54d0f31be980324436e52908209f59543487bb42d01409f587540836f5294a40f9549100433d54d08309f99430442ef6250e32cf553520c35e6514d10f358f21886bd640c210cfd4e415075c6054c40d7d8953042fa6090640db94942907776154d20db182520436e5290731db147214833d61d51108f590504867d658c440e7551530827d6094d10ebd51424cb7564544209f58c51482bc6050d40bb982428867b654c030d7cc9508c7e952900409f98354cca7d6550a10f3d8d424cadd63d40429f594321035c51cc530b7d93324c27661150309f98652d0ef56114830dd58453c86ee6210f429f994414c2f7614ca319f597420c33e5450e209f98253d07cd320ca40cfd91544867c6054841f390932cc37651504409f5845250e7e63943429f58c525027d6114d20cf552420875f6554f21af59332d033f54d02209f98353c876d528c810bb586424827d60949109f98f54886f6610c1209f98e518827c6255030d715143cc3da608c6309f99052c437452944409f992538876f
  | 4 => 0xbd9552d067e6394b41af59321082de6314b41db596428cb6f5354840cf99054cc27c65d0c20af98342906ee6214c409fd97434867e65d0930ee951200827d6494f20db548420427d65c8430bb988504c75d3254032bb58a430cade63d01309f994410867e6494d20d754e31083766194b109f986544cb6e6214f219f587548c27e6394810d794c31c87795014041cfd51424867d6494b31cf151430c6f56390710db9885050e5c6354910cb54a41103d563d0541cf550548c37960153209fd91530839e64cc6319d584504cbae5490b20d794f4010376534c7109f191508c6f661d0f219f58654ccbad4214442b7d89320cb6e6194810e750c430c33d64d4e21b758c50087365454430cf551438c67f60550109f59442842ef6254640dbd4a52d036f4394843cf95043cc67c65d0d20be58054087e731484219f582548cadd6390431db5485010eee62cc721bd9864390775510c020cf15342c43746254430b758c42086f96008420dd98e510836e5248420db988504c67e65c8510dd945400c27d6494c109f582528c79e5494c10d754d31042f56190f109fd94400c36e4354840bb588400832e5494810af993314867c6590e21fc98231c42ef6254630d714d31487ad42d0320dd984548c67e61943439fd91500867f65907309f99630482dd648c1309f5825190b6e520c8109f18d54c827f6154b43af99032c827e65d0430eb552520c35f5394c40db949411033e5350e41cfd954210abd640cb40d754d31902bf6454620cf153104433e54d0830af5824250b6f520c910be58243cc3b960104409f596211027f6550520bdd85424873e54084109f98854cc78d4394843b7d81300c2fb6048520fcd8510042dd6190c31d798c534867d65908409f99632d02be64cc410d7192530427d63d50109fd95204439d438c740f354b320c7774254430ddd95511027e63d53109b588548433d5454321d718d518826d6214131f9d4a41443774254420de597308c27e64948109f98e52907355454430b798c424436c5314910d7d4c31443796015310dbd48215036e538cb20b758a304c27d650cb10dd54d51082f66110320d75815310b5e524ca31e750d32503cd320c7209fd9442c42f561ccb419fd81548876e62150209f19742443ae5448020dd14a21c433e5488420cf55341cc77752544309f58f54c876f64548309fd9541107766115021cf153434cb1d4354843fa50b204827e6315130f918a510827c6014910bbd81428cb5e53ccb21bd185504cb3e5490b319f996430835d53904409759653083796014c219f988520433e6515110dd0c1510c2f56108210bb58853842be644c8419f993514c2f76150810b7984310c36f53d4910cf552400435e534c841eb50a215027f6155110e7d9143cc2bd640c8209f59421902ef6250e20db55132c827f650c
  | 5 => 0x30082f56348510f34c832886bd61d0b40bb98b418c2f6618c931bd987320c6f66114a40be580414827e6294e41ddd0d510c31d53508429f99251cc3766114810cfd53438873e6255321dd59631c427d6254c20dd147314827f6590030cf552420c2ed63d0942b7983328c67f6354640b758e214c27f6550b10cf95340c82f66190b31be580430c33f544c510eb50842c42be64c8421e7553320cabe6414830cf551418427d65cc941ddd47314835d6254f41db149324c27661d5332cf18a540c3cd43cc932ed50a414427d64d4e21cf550500cb754394440b798c429027c6510530eb951520427d63943219f593504c79d5494c20db94932843746354420bed81434c35c5490d329fd85548c27f6254f41af582411027c6154d20f9944210836e54508219b588540c3af5250940d759253c867c65d0f10bb588544c2dd6315220d754f210833d5350040cfd52214432f4354843bd98443d067d6294343d758f54c867c63547429fd8d540876d520c830d794d420427d65c86309f181544867d63950219f99732502ee6214843b798c42106f66108110db98b548c75f5394f42ddd0d511027e650c440bdd85438c75e534c840cf551420827d65880109f99632d065d63d5221dbd5021082dc6354540cf551438ca7e654c940cfd51434cb5e6294f41c750e5110efa60cca20be98041883ce434c920e7d894310e7e63940419f58b54cc39c5450d30d794e31c833d54508319f596530433d6414131bb988434875c53cc220cf953430c2be6494b109f5865310b3e5410010bb982420873d544c832b798f414436f5388620dd981511027d6550f109798e524435d53cc4209f189548427e6394d21f358f21087cd3254032cb151428cb5f54cca31dd182510c3b74290710cf95050cc71d548c430b7986324caed62cc510b758c544835e5350020dbd8d52d075c53cc821cf982540cadd6314841cf94f43d0b7a6014a10d754e210433c60950209f997434c2ee6210320db14831443cd320c9319f595420c27e6494720bb988430435c538c620d794d43902ee62d4331b758f42cc2766114c109f195424cb6e5254440bd98454882ef6254d10bed8142882fb60506109fd9741c83bb43d0140be98043cc33d5450330cf55350c86dd6310840cf59053842ef64c84219798c540436d6194b31e750c43842bd64d47329f195324827e63951219f191518cb7561d5232e750d42ccadf6250f30e799331cc33d54d0c30af993510835f6354f219f58a54483e652484219f594329067e62d5210bb1894350b6e5450920cf145415039d43d0330e750c43d0a7e6414c10db98152d07d6510c430db98b54c82bf65508419f98650d0aec6048720bb98b51cc27d6510e21af1854350af661c8310cf55054086f66110b10bd98450d0f6d52d4341cf55243c867f658c720d
  | 6 => 0x27e6095232bd584300427e6294031bb98b310c25e63d4542db54b411039d434ca41eb1854210a7c650c940b7580310c33d5450a20e79514310ebd6414a10b798f520427f6550430db185521027d61943439f982520c73d53106408f990538835f6550f309fd95418836e52d0030cf54d42906be640c210db952428cafa6088520dd909510836d52943319f596310836d5294341ed546411033d51d0240af593314c2bf6550441af59032d067e6515120dd545211036d3254021bd984500ca7c65cc941cf951510cb6d5210731afd91518c2de63c85109f98b544437651c8430db54942042f960ccb30d7188534436d6454b319fd9443086de63d0640d7d4c30c427d6194342db98252cc67d6590b309f18553c833c6315110b7582324cade63d5010dbd4f20082f860505409f984540c6f96010e10cf990504c75e538c420cf98254cc6ec6254540be98042443795014241cf951210c37642544309f997321033e5410210bb189518c35e4394730cf553418c2f56110010dd8ca511037b5094141b7d91314c3ba5484010bd587430873c54d0b209fd9541043cd320c841dd947310c3b654944209f18552102de60ccb309f587544cb5d5390420f394b300c2de63d04419fd8d548435e5390d20dd182511027f650c910cf952401027d6195220db54e52d07e65254430cf990540cb3d5410c309718d544433d5494321cf15343c435d5350721c7553300c3774354420cf993538867f65c8630d5547300c35f62d4d10bd185328c76d3294720af18141d027e64d49109fd9731102be640c0109fd95401027f61550209f99732843d7634c431cb95252cc76e6054843db14b324427e6510521cfd52540827e6395321cf950210836d524c840cf186540435d4354043bd98632086ed6290720dd909511027c6508530f5cca310c6bd640c010f3d4a324cb6e43948309fd855404374538c5109f997219033f5495330af18143906dc604c831bdd9231c42ee620c020dd947300c27d6550e20cf189540833d42944429fd8151d0a7e60d5030bdd89210873e5490830cb151424cbad42085409f98254c87db604c530d754c53d067d6494810de983540827d6094e41af59321d02bd64141329f594410876e52908329f993514cb3f6455230f394a310c2bd64d4032af590504c67a6014c21f34c8214c27c6550530be580510ca7c654cb41bb98a314836f6254640cf150418c33d544c410b799453442f66190b219f18954cc6766114e20dd185544827d6294e41e750d420c75c6154c40d5546310c3765354420cfd095010b6d6590a219f590534436f6548421ebd914210b5e53d0440b758f415076d6215332d794f30c827d6494031eb952520c2de60cc5309f58e544c36e52cca419f596414c3e55294430af990215025d6314a10d7982531027d63944409f194
  | 7 => 0x28c840b798c414c27f6054d10cf95053042cd63c8520ddd4651c827f65107209f992530827d658c6209f98653d0a7e65cc910b758f529079d4310c10dd584538436d5250831db151424833f54085109f98e54c433f5410930bb98843c435e63d4810bb189318827d6510d10f9886204433e5450e319f994438836e524c8309f98a50cc6f661cc910d798c540c2bf6454d209f19743042f661d4c209798c530827e6114c209f992518ca7f6550841bb98b318435553c4010b7d95310c72f54d4910d994a510c2be6494e21bdd9531c42f561d5232b798e410c75e53cc420ddd8e510835f54cc9309e980540c67c658c941d7553328cb7b6544010cf153404436f5488420bb98b410c75d5314e40bb189410827f6454f10eb95252cc67f6590d10d794f210835e538c010d714d324835d5494f21bd9845010b755114532f98ca214427c6154f42e798f419067e6494c21d7d4e404427e6510b309f996424827f654c640e750c4390af4614ca41dd946410c27e6510d20b758c50c867d6014943cf552300827d6494d21b7d91320c67d6315021dd945419036c534c8219f18d52843d5310c721b79874350e7e6194c42cf55341c875e534c620cf50c515027e658c720dd10d510836e6394840d758c548c73e63553319f993538867c62543419758c54482be640ca20cfd50418c33f5450a31dbd4c21883cc644c832d758553083ae548c832b758c400c35d5308410be58042103796015031d354e520427e63d5320cf550428c67e6494332db94b42d027e6214d10bd98642907e65188620b7d9543ccbea608cb20eb50d424cb5f5310510cf95040082be64cc710af990504c6dc604c530f558f218873e54d44309fd95430c35d53cc020dd19521443b74390710b718d420c35c53505109f586534876c528c9319f995434433c5494910cf98154c874e43548439fd8d54c42f76350510eb50a32d027e64d4131db58c524436d5388521dbd95520c3744354430af58f425039d4350130db94b32d073f54952209b189544439d43d0a31db9514210af7634c4319f588544c3d5310c730b7d89438c73e5410c30b758f21c83b64250441bb987200827e6115330af993214835d54cca31bb58b31902f561949439f597329033e64150109fd96434835d6154f41b798c42ccb755148430f590e31c427d64d4e20bd584200427d61d5332db50e521036c6054830f594d310c6de63d4321d7d4d304833f6215110cf951418c2bc6454132db440524433c5490d10bed81314c33c5408110eb50a418867f6254d21dd94441082f46154930cf953500cb744354440bd984408833d54d4430d71815310b3c54d4910dd946400833e548c832bb58e320cb3d5488410c7d50534435e53cc020fcd42104435e5354042bbd894350a7e6550e20d798f548867f65d08109f1973204
  | 8 => 0x30bd987404433f54d0531db94b20043ad4210820bed8d300c27e6294e10bb58b314c73f6454d10db549219027d6394010d754f421027e6494d109f996414c27e63150329f5865090f5c538c610fa98221882f561d4c40cf981540836f52c8110cf55032cc67f658c910bd984324427c6154830f618d100433e5450b32af993215027f654c841cf95150cc67d6494820f354d520435f6194f41db54a30042de63d05319fd9742c43d5328c710dd10a51102756115220d758e548c6ef62541319fd895110f3f4154041d394d520435c54d4d10eb552210827c6454f10e7d4d43d0ade63d0932d7d95438c6ef6250120cfd9154482bd640c310db98854cc73d5390440dd94631882ef64508429f98a509075d650c630f54c7304427d6550d20d718653082f46154d409f99632482be6414e10afd89435035d62d4d109f99632103765254440cf15143cc36c53548409f18951d03776548421be98331cc36c5290110cf990544ca7c6550430eb551320ca7d6015321bbd89418833c544c9109f19521cc36d6294d219fd9431103775344010cf95120043b754505108fd91534835d5354341cf153434c35e5350e109f592510867d6094f21be58221482f76384110b798c428875d32947308f590524c35d5310010dd945318c3746054420e754d401036e52d04309f58a548c76f528c941dd945410433f5410520d7584534427e6094b43db54a429027e6394020dd584540836e62151308f99053c835f54cca32bb988408827c6055031dbd5152cc67d6314142cf550428ca7e62d51308fd91534435f5394e42f394d4210b3d5450e109f196414c35e5390420bb98b540c36c6494b319f98054c86dd6310920af990520c73f62d5110db14841442f960c8720cf181540c27d6295132db54b42d07766094420db185520435d6454c10d718653102bf6150441d794f320427e6015232bb582424cafa608ca30db986520c3e761d4910af990508867d6510c21e750c434876c61548309f997404833d5490730b758c40842bd65d0240d754d30c83d7634c510af983415027f6354041cf553320827e65d0a30db94a420c27d6394640bb58b510c2ed6295110b758e314c27e6590110db949410427d6394b40b798f21903756254430f34c832086de6348530cf551210c2f5648c7109f996438436d6214e109f586500cb6e6214c209f588544435f63551109f98052506df654c831bb58b418427c6510030cf151424c76f5250510dd54431cc36d52d0030d714f204435f654c030d7996434c36d62d5010d754f5010b5d6254c10d798953d06dd63d0720f514e10443b443504419f19541c82dc614c030d754d318435d53940429f195430835e5310721af993510c2df64cc5309f59643c833e5450a20cfd51424cb765454420bd5845010e7c65d0d10db94b42cc76e5
  | 9 => 0xd8653c86ec6150a32af58b431067e6515121bd587304427f6590d21d754d43c866e62d4543b758c42502f56190b219fd9732102fa60d0c40c715143cca7d6314540bb58b40c827e6590720db191520c36f4394b319f990530867d65cc821d718d544833d63550109b596210833e548c721afd9543d027f65d0420db94842103756588710bb98b51d0e7f6590a30cf95142cc2bd6590440d7d86531036f5294931bd58420c42f960d0c40cf55054ccb6d6194840cf18d540833e5450e309f986529027f6454630cfd50404436c5490a218f59053086ed6215010e7d91438c7755114740db15052442f5628c7109f994410c67e6590510dbd51200836d6294e41bed81328825d63d48109fd8d520427d658c830d754f431077765440109fd95310827d6494b30d7d4d31443ea5244010af58743d027e6394440d758c50507d953840109fd95420875f6294c409f59053887cd63c85209fd9420042f9608c530d750c514cb5d538cb41d354d521027f6254e10bb982424827e63952109f58a51042f5610c3109f987530836f6255121db54b5110eed62cc6219f59251ccb6e6294e41be181439027f65508429f597418835d5394440be582430c3d55354440d754c53507eb62440109fd91520c27e6215131ebd8942106ed6348421b758f51c835f5394c42db54720882de63d0621db54b32043cd320c840bd59131c42be64c84409fd8154486ed6210130b758c540867e654c520bdd85328433e5410832db54b401035d510c430fc181214436d62951319f587540c27d6014542bd58440cc3746354440be181438c2dd608c5319f59742042ef64c8520bed95300c33e6155030bb58a43c835e6314d10be580214c3b551d0740b798c50d0a746155130cf152424c36e62d4c21bb98b41442ed6210d41a758f41d026d6214141af59021d02f66115030eb50a410867d6590a10b7591310c6f56110310db988528427d650c8209f986528c33c54d0510cd55310043e76148520db549410c27d6295331dbd4a528c35d534c6208f592524435c53cc2109f58e51082bd65d0e419f191518c3e752841109f99251042be6494d10dd946218c27e63d5321db14932507ad4210b409f98e5090a3e64948219fd85548cb9d5494c10b7594318c27d6294f41e7153534423d6494f10db5485110e7d658c640d794c31043cc534c821dd94531083355150040bd987321067e650c720cf151404827e65c8630bb58b410c36d52c86309f98b54042f6610c510af99030c437a60d4e109f596431079f5450f32dd58454c873f5450f30cf597429073d540c420cf952410876d52887309f99431d027f6055130db58652d067d6054c10d354f20082f86048620cfd51434c27c6510931cf550210436e5394810bbd81200832d54948109f99250082de6310130de540504c6bd640c9
  | 10 => 0x4042ed6294f10b798f218873c62950109f188534823e6415010cfd8c544437661d5020ddd4d51082b561d0841dd54631902bd6408110be58032cc3795014342db54a42d06ec6254d10d714e32442bc64549309f19531d039d53d0842db50e520427d62951309f5825390a7d650c520bd984414427e650ca10d754c530433e5490220af59350c867f6254043d798f54c86de6390a32cfd52540cb3e63550209fd9521102ee62cc4109fd9432102fa60106309f99643443f26090710f5946318c27f6510010be980430c33f62553319f99443c833e5410710db50f52442bd6414221db949320827d6015121cf992520876d5214843bd5845050a7e6395010bb98b41902ee6210c209f99453442f561d0b31d7d95320cb5d53d0c40db149314427e6590e20db149424c73d6215110cf0c9540cbcd424c831d794c321035e53548409f98853086bd6414f20db54b320c75e5310e21eb55152042ee60c8720cf951200835d5314d40bd586429076d5214b419f59654082df6354142e750c43c427e65cc110dbd4b21c436e4394843fc546401033d53d0a42db548310435c5390f109f98f514836c52909409fd95318833c54d0a31ab593218867e6494430fc945300c2ee62d0441ed551510c35d530c020cfd0d50d0b3f5450a32d7992530439d6050c43f9d0921086bd64d4e219f996414c66d62d5331bb988540c75e53d4440cf55050c86ee6294543fc945200833e54cc721b798c505073e5410a31b758f218837763544209fd9643c827e64d4930cf55041c83ad4250120db549510c2de6315210fa582218836f4354b41dd586544c67c65481109f98a500427d65886309f191530833f6455220d754c32c836e63548409f59531d035f5388510cf99353c866d62d5231d794d31c87cd324c1209f99532c427f6055132cf99052842be64cc740dd50a511027c6355210de983530439d63d05409f59250ccb5f6354d20cf153408836c54948309b988540c3ad4210932cf18a54082f46150941dd185534827d6508740af99321cc27f62540319fd8950d067e6508430bb9874250af56190b31d7151530435c5350d10fc945100435c5490d309f19151c83cd5354b41d794d30c433e5450010dd18a510833d5410010bb594218827e6494832cf55041887f121c4110db94f524433e5490f319f59643c86bd63d0a41de582534427e65109109f586539033f54502109f9835350b5e5350e42cf953420c7ce604c832bb58843c82be64cc420f9945200827d65c86409f594410c67d6590c31eb15052442df6350a30ed50441c427c6354a40af990425027e65d09409f582521073c62550309f59643886dd63d06209f98e50d067f64543319f98c515035d538cb219f58e50082ed620c320dd14d31c433f42947409f18550ccbda6090f30cf952510827f65d0c20d7
  | 11 => 0x9f5390d43bb58e428876e4214532de980548836d4354830b7d8d42ccb6e6094b41cf14f435035e6094f21af992321075d53d0f42db145214833d54d03109f9875350a7e6094a439fd8d54c836f52509419f58e521035e4354b30db50b504cafa6090940d754c42c86f76150e10ddd5310043e76244010d718a531036e5214331db98b540833d5415010dd553108427d6395010cf55032c879e548c430e750f321067d6215031f34ca500ca5d6395221bb58854842be640c020b798f424c36c52c8710b798c421027d654ca10d7d8d544c2fa60144429f997311036d6294d20db94a320437b5094142dd984548c2f5610cb109fd855310a7e65908109f58052506fa60d05109f583534873d5414432bb58b414876d52d0841db949421027e6294630dd54541882ee6210f40dbd955210e7e65d0531bbd8e204835d5310c40dd946418836c5450821d754d20043ce538c8329f597319027d6395310b758c42cc3cd52ccb30cf952310439d43d0932dbc85508876f5494810dd5445110bce62cc730be181324c27c6548540dbd4a324433f53d09409fd9531c827e6014d219f986544c35d5348440e754e411035d544c030be98042102de6314a409b58a544c6ee62d4c40d7d5332cc33e6295321f614f104433f4294441d7d4d434875e5350c32d7d4d43886dd6314940cf552430c23e6414f2197195434cb5f5390d419f18d50c86bd640c0209f181540865e63d52219f58254cc67c6454d21af99052cc33e6195010d714e20442be6190d439fd81528c75d5310b41dbd8052442ed62d52319f99732902f9600c640e750e414c36e4214520d7d51300c2f76550710e7552310c35d5314d21db54832103d45348510b798e408c2dd6310010cf95132cc67c6254443db14a21442f76150e41bd984510c27d6095321db94a210867c6550920db54821cc35e5314810bb58b410425d6314940f5986430c7cf654c832e754f431065e6394a41b758c428c76d524ca31be98021042bf6250e419f19541cc35c5350d419fd9731c826c6254640cf550510827e61150219fd9642c427e650c521d754f420827d650c4409f59643043b86050d40ee55210043ad4210b41cf18e54c873d6494d21ddd95411072c5450b20db949300c27e6394821db54b511027d6588410fa94a300c36c4394b319b988544c27e65d09329758c52042fa6010e10f518d10043b564cc531db948320c67e65d0d31f950a214435d5310c419fd91518caee6290c32ddd4651ccb5d5390840af98341906dd6308210ddd4541502fa60c87209fd9151ccb3d4354043b7592430c6796015021d714f32c827f6510c329f98e52d02ee62cc521db548524c33e54d4c10d794d10043ad5408420bd18540c435e538c8329f996424c67e6295231cf951420ca7d654cb40ed951510c35c534c120dd9875
  | 12 => 0x4c8309f9825390add6314a409fd94420c6be640ca30af997415027d60d5232be592401039d4310431db54a320c27c654ca40b758c528427c62544409fd95400435e6315031cf551428434c524c930de54050ccb746294430b798c208436d5250a419fd9521d035f5494f21cf590530433654944309758f54042ed6210e329b98a54442fb62480209fd91518827f6454810bb98b414c6f56110b109f98a548c27f65c8640d798c5050a7e62d4143bb98843d067e62d50328f99054083764354420dd5445190ebe6414c20ab593210867c6355120b798f411027f6550840dd98951082be64d48309f594210c2de63d0421d714c424433f5490610db54a32d02bd64c8530f694d40103da43cc130d314c524427f6055021dbd4b424c25d63d5321ded42504867d6394841d758153c867f6354440ed906404435d6254c40bd98442d067d6510530cd552510c27e6214c209f99732106f7614c921cf94b421067e6315110cf550530435f53085109f997329076c6054840b7996434c33d6255030db988505079f6350f40f5547300c3d663c85219f597318827e6194c40f350d328877551d0040cf990538427d6015332afd81401027d6590810cf548411033d54548309f19432442ee62d0f429f596329076f548c821d7982530437420544209f584525027d650c020d794e40043e75248510d3d4f524433e54c8410bd98430842bc644cb41cf95341cc6cd62cc431db54852042bd64148109f994404427c6454e21cf95331043355190440bd58632442f7614c8109f196315033d62953319f996329077752944309f594400833e54d0030cf55240082ed62d4e41afd91219033e52d0a41af993538876c6354b41d3549300c33d4214540bd984408c39d54cc030ddd4d51103d5518c430ddd0a510c2f56114232dd90d510c27d6214c10d7d4e538839d5350e41bd584300833c5410610cf18d54cc73f4394740bd584530835f654c730d794c410436e52880109f59621502f661d4830cf550410c73c5490520e794f40102bd6490d42cf182540c2be6410d40cf55041082f4614ca10ed50740442f661cca219f582548c6fa600c640fad4b104435e6194c409f986539027d654c120c7d954310eed62cc421db988530867d64946309f59250082f764504419f181529073c5450e21cf951400836f5288110eb593218876d5244010dd94421082ed6215030d794c300827d6294e10af99052cc73d5415130f3585320ca7c650c421bb988434cb9e54cc030cf15130443b4548c510d714d32c42ee6210621bdd8530c433f5448110cf553400c27d6114d40d554d511035e53cca40cf952430c3775494420db50d5210f9e5490c31dd90d511036c4354b41cf55253c876e6354b41d790e51ccbe65244010cf95330042f960d0740d754e43086f56110020d7d4e5350b
  | 13 => 0x1dd94431102ed62d0710e750c43d027d650cb419f18552902de63d4a419f996420c27e6494c329f99253c43775194443ed98441902de6190f329f59740082be6414630d7d8d538831d53500409fd8151ccb5d5390820be98241502be64485409759653043cd320c940af191518837b5094042e7d914310f6e54509329f996210c2f56110f10cf552408833e54cc020cf99053883753254430b758c54c86ed6390821ed152414436f5390a21b798c5110a7d6510430f9986320873d6414132f34c8324836d5290010bb988408c27c6354241db58a54486ad62d05409f597310435d53d0c209b58a54c42df6355110bd58632107b661d0c41cfd51404433d5450731bb586328873d54d0430db14d32c827d6550932cf19153482df6354910ebd0d428875d5350b21bb58d21482ef6148421bb988531073e5414830d794e430c33f5495332d754c43d0b7661d4c21cf95231083745490510bd5845050e7e65104209f984544c33d6095032cf9974350b5f5310110db94842042dd6290e319f19643082f661140439f98854442ee62cc710db14821443766115031b798c52d035e5490c31db991520c25e6395121be583421034d5394b41cf153534427e658c110af59050486dd6395110dd98453c435e5450d30b798e529071c5450c31dbd4d42c827d658c430db54d4210af56448710eb50a414837532544409fd815190a7d65d0630cf953320cb6f52109109d584548c36d5210410cf950430c67c6154232cf58554cc73e5490410bb58843883cc53d4910cf550520c3ad4210930cf59053c83cf624c831fa549401033e544c830d714e43503b541107409fd954310f765450441dd984538839d63d0641cfd0e511073e60950209f594428c67d6494730e750c43082ed620c220bed8121843755254430ded42508c67f6255110dd547400827e6588110eb149421075d5350b419f99732c435e6315330d7989531033e5414f21bd986328c776534c431f990a21c427c6155020cf981540c35d535001097d8d519035e43944319fd96320875f654c431eb54b42107ce62cc6319f588514c3cd62cc431cf951520c2bd64cc720dd547400c36e5294443cf551200427f6254740d718253083d75350510eb94d4210ade63c8421db952428867d6590830db948320c35f6354620d7d4d308833f54d0b209fd9543c826d6294d10db54b218427f650cb40f994a511027f61551219f586548cb765110020d794f42082f4614c110d7d8553c87766115221d758c54083cf634ca219f994544cabf6250540d554d510831e5350e41cf14f4350a7d60145329f58c548435f534c941db94a42cc2ed62d53319f594428c27d62d5130d750f524c35d5394840f9d4921c433d54d0b309f58c50506dd6310a41bb58b311033d53d0841d7d9553083ad52d00409f590530833d54
  | 14 => 0x95315027f6590e21dd987548c67f6510a31e750f424c2bd6090d439f99621902bd64d4420b798c424826f654c832dd546218c33c54d09219f597324433e6414f219f582540c67c6590f10f34ca510cb5d6494c209f59732502dd61ccb309f980544c67e64d4e109f99441502f76284110dd14521482f76150c10f350d3208776538c710e750c434cb3d5415331dbd52324827f6510c31cf55350cc76d53c8220be583320c3795014132eed91401036d5214840d794d310433d54500109f99631483e65294430e798f41d036c52c82109f593504cb3e6415120ed953100436f528c931d7d53320caef6448720d7550534433f6155321cf18154cc77551d0420bb5884310b54538c510f9984218836f5294940f5d0d310c75e6294c109f597328436d52108309f586508ca7d6294c409fd85531027c6510e21dd94441d027d65cca419f585540435e53d40429f983544c73d64141219f99432d037452544309f997324c67d61d4d20d754b300c27e6494c308f59053882be64cc530b758a43cc36e5214043d714d424436c5210110d754e310435c5390d42d798f540ca7d6094c21cf99054882be65d0d40cf990530827f6355020db54b20c42fa6008710d798e54cc3ae54948109fd95200437451105309f1855010b5e5394042b7587328c6ec6254131d7d8153d06bf6150841af992524427e64949109f194410c7d932cc1309f98f54082ed62d4331db5495110f765288421d754c43083b551906409f597430ca7f6255231db18d52043af6450a21dd54451d0e7f6590e10f914921c427e6115120d74ca510caee6290621eb18b4350b5d5390e42ddd4651883745354420d754d52d073e54c8420eb593210867c6510020bed81328c2bd640c941d594d51082ee6210421dd5445150b3f5454d109f586540c33e5450a30d754d210827d62940319f592510c67c60552328f994544427f6354b10d718d524427f6454430dd547411027e6314542af990320c75d528c4309fd95320c6be60d0f40dd14a214433f54d0b10bdd855050be76248710af181421075e5390c21afd95401038d544c832bb18930c83774394430dd54451483776154910bb58b51cc2f96090b209b988504c75d5314d20cf55353c86bd64d4532bb58b43c826f6255130bd5845010a3d6494b10bd98632c867d64d4931cf95331083756114c20ddcca511027d6314941dd98d51102f96010a10d798e529067f654c431eed07405035d6294c40cf150324427e65d0941d794c52102ed6290020b758c200427d6510821d7d8d530433d64d4c20ddd8e511036e6590932d7982530827e6194c20dd545318c2f561d0e31be983310c31d544c832bbd89535033f6115110ed90d411075e6054c108f99741503e632884219d987548cadd63d5321ebd954210a7f6055031b758c40c435c5490e3
  | 15 => 0x442de6308010bb58a4350aec6254d40f34c832cc67d6194c20bb58632086f56114342d794e420835f5390f10cf551310835d538c740e7d814310e3d6414c109f997324867d60d5132cfd50524425d6315021cfd5321443af43508219f98e519039d43944439f592508c6f76150d21bd98743c42fa60d0840ded8152442ed6210320eb50a5110b6d5214a43db54951102dd63c8630cf153404c38d4350932cf990540c2f9600c830f34c8328c6f561c81109fd8152d067e63d4141ee551200836d6154b319f996410827f65908329f98e544835e53cca109f58c54c835e538c210dd592510827c654c510b798243cc36d62150319f584530836d524c410db59252cc67e6508510ded95200833d5415032cf953410c2f66110110de983548427d6015221b758f418c27e6214c109f185548836e61548109fd8950cc73d54d4c109f98e540867d654c7209fd895190ebf644ca40cf953430867e6115232e79814310e7c6454c10d714e438876d52cca41cfd53314436d62952319f595430827e63d50319f595414c6ee620c7209fd95210c2f96010f40d314d320877531540319b98854cc3cd320cb309f18151d0f3f65550329f58f528436e52c8630af993321067c6154343db54842d02ee6290f20db949420435e5350440b758f40cc39d4310f41cf98854442ee6210d30cf98c544435f5394f41db55320083e56114910d754f21042ed62cc120db94b428c73d54150309f98c530435f54cc2309fd9431902f4614c921db549218c37650440108f596411027d61151329f195414427f6550910eb508420ca7e62d4e10ded81544827f6054810d7951530827c6254241f3d8d32086de6090e31db94b321027d65cc720cfd52544c36f6194b41db5495010f3f54cc1109fd9431d023d6414131db98a544435d6315120af993210c33e5490420d7d8553d076d5250440bed81429036f52509109f984548c27d6194840af99131d02be64d46329f191520c36e52543319fd8954cc27e6515130bb982328869d64cc530ddd4521483776494420db94831102ef624c620bd986208436d6154843d794e21042f6610c010b758c50906ee6290421db55352442f46155120d71895310ade6315010d754f31042f4614c810eb551200827e6294041ad587431073d5450f31b798f51d033d5488420dd4c9510836f6548020bd98643c435c53cc521b798f21102dc6354121d794d320c35e5354440cfd9543d0a7f654c520b798c40c82ee62d0621ed593218873e6414c10f654e401027d6414910dd549100427d6315221d754f300435d53cc6409f997314c38d5350842cf15341c427d63151219f197438435f548c630d718953102be644c940ed95141106bd644c841d794f430827e650c921cfd5231442bc6250f42dd992510837551d0430db54a428c2dd63485309f1
  | 16 => 0xf624c730db14a324c2ad64c8520d798f540827f6154a40e7951438c67f6548421cf952414867c65908109fd94430826e6215230afd8d41d027c654c6409fd8154ccb3d63950209f59532d076d54c8220d7952530823e64d45329f58654c82be61d0d42bb98b411036e62952329f5805350bd4434c431db90d52d067e64d4c10cf15343486ee62cc4209f19743c865d6314142b758c214c2ad62d0641d7d4d20442f56110130bdd8520c426e6214d40db949410c27f658cb41cf55331042f46154940be58241902f76484110bb588548c33f54951109f18154cc6dd6308310d714e30442dd6310830bd58743c863e64141319f197314827e6294343cfd52414427e6510c219f592520c27f6355010d754e431033e544c030b758c400827e65d0a109f994428c6f661d0831dd145314c36e524cb409fd8954c437651cc7309f9875050a7f654c110d758e544cb6e62d5010db54e210835e43540319f5865210ef9600ca10ebd9142086f86050610b7597308c2ee6215330eb1814210bba548c030bb58b410835d5350f209f584540c3e86048520d798c54ccafa60cc610db195424ca7e64d4931dd586544427f6154f209fd95428c6bc644c640db549420c2de6310940cf95342c873e540cb31be181318431e5450e31ded425090b5f534c8219f99721cc36d548cb20dbd4a529073d54cc010db54e428876d5288410cb949429076e6454b319f191500873e6095010b7d95320cabd64cc620af592321067c6548740e750d5210ede63d4341cf952420875d53ccb21be58342482fa6008420cf94942d036e658c920bb988540c39e5350e41dd151510c27e65d0d20cfd50414c35d3294431cf95241c873d544c030ee552300c36e4254042d754e410433d548c410dd90a510c36f60948439798e54c427d6094843b798c540827c65cca109f58c544435e5310c20f9149414427f6354720af59321c83cd6390a32cf989540ca3d6595010cf953434827d6494832eb99321c82f56114e20db90e52cc76d548ca219fd96219037651480209f18d51c82f5618c931af592411067d65d0720dd95141c436f5288610dbd95320871c5450f30d794d210827d65c8740cfd5143cca3e6494e21bb98853502ee6214440b718d424caee62d0421cfd4a415067d6194b40cf55043cc33d548cb31af99053086be64c86109f59432842be640c910b758f511033f54d0f10f5587320c67f6055232cb55152cc67e6588510cf59743907cd320cb21be586100427d65cc840af593530833c6255010dd14d51102be6414f21db548521063c64546309f58f540827c65909309fd9532506ed6214043f948421c427e65d07209f986540caf960087209f59643487af43548439f99543c82de63d0520bb58b314827f6154232bb58b438cb5d53ccb41db18152d067d60953329f19521
  | 17 => 0xa31bd984504cb7950143419f18d52c427f6510f209fd95414c3ad6350842bd986200436e3254021af590510835e6194c10ab1894350adc6350630cf553500cb6e5254430dbd89528433e6415310cf55042cc73d5490410cf585540cb3d548c832db988540433d54106319f586520c2ed62d0c429f58a5010ef6610c3109f590524c77651500209f19532103ae62d0740f518e510c36e528ca109f995438433d5415220ee90640102df63486309f997430826c6255130dd94921c436e62d53319fd94438836c5248110cf952100435c3194030db98a54c836c6454b31db50d521027d6494e109f58650ccbd553c4010db94932cc75d53d0842bb988214836f5390920bbd8542c82f56190d419fd8d524435f534c210cf58254cc6bf6448440cf551510cb3d5450e30bd98432086f96014831d754c53c82bc6454530bb988430cb3d65904409f986544827e6394740d754d32107ce4354843d74c9500c6ee6214243c754e411033d54084209f19543086ed6390920bb58b31503e54288421cf151414427c654c910d7d8d54482ed620c6219fd94430c375514c0309f58a50cc67f6588630ed55251082de63c8520d794c21043ad5454b319f59743c867d65d0410b798f41502ee620c320b7d85430c6dd6310a10dbd4a5210f3e5454810bd984539033f64550209798f54c86f86048510bb98232086be640c8419f5805150f5e6254c20f354e520435f6354e10dd98a510c37661153109f98a540426f65480209fd95300834e5394810b758b314c2746155120f390e424cabe6414232d754e32c827d6494221e794f4210be551c8020dbd4a30442dd6090f329f994434427661d5020dd545300835f6354c20bb18132c835f534cb109f98e521027e65cc7409f58d540c33f6395321d714f324433d5410531ed15141c427f6454c21e715143cc35d53d0040be98342482ed6214f40e750c5010ef46148310ebd854210a3d64d48109f98254087b651d07409fd9541082ee62146309f58e52907775194430d790c514c3744394430dbd8e52042f66190b10d754c31c879d64cc5309f582548867e60950329f98f52507765148430d794d328875c6294c10dd94640102ec6050b209f59443042ed62d0740bb582428cb3d5450c329f596420c67d650c841dd584540c33e62950329798c540caf46150d41bd586408435e6154c109f58254443ad4350b20f34c8329073d5450630fc546300c33c54502309f594410433e5410220d758c548c39c5350f42d7d4a314c6dd63d0431cf950300423e64d4810bbd8950506ec6148020bb988404433f6455221cfd51414c6df6350931d794d431027e62d4d41cf553210433d4154041bb98b31d033c54d0920db95242c836f544c832af59032c827e6215032cf54441102ed6490932f594e310c77751d0530dd94441102d
  | 18 => 0xcf55232c873f6195032b718d544835d53d0440ee98241903e62108310cf950300836d5390b209fd815310b3e5490b219fd97420c27c6154c42db592520c2bd64d4830f5d45314c33c5190140af99041502fa6088410ed993314c7ac5450920b7d8d404c2de63d0631db148424c2bd6390140db54c21083da538c030dbd4831443755254440dbd4a524c37b50942439f58f54483da60cc730b798c42c873d6055032bb58851902de6310220eb5085010b3e5490842de945100427d65909319f99353443ce5354810b798f5110b6d5208410d74c8514c3743254440ed95241c436d32145209fd96430c2dc6250d329f58c54882dd64cc831b758c5010bcd434c920cfd0f5050b5c5450d32cf59353c86ee6190932dbd4a52d0e7c6454a30db94a40103b55494430d754f318427e6510d21eb593214836d528c840db54a300c27e6548540eb50932106dd63d0510db54a510c3b64110110bd58a21442be60d0b40b798c20c42ed6210e309f58f548827e64d4d219f5835350aed6290f329f98052442ef634c832cf99054c875c6154c10dd587548427e6414810d714f32507756115210e7d5143cc37a6014e109f98b50506f661d0910d798153102ee62d4f41bb9884148376518c630d794c400427f6454a309f58c5150aed6008620cf550400827c654c521b7593310c73d6315110af59032882dc63546209f195414867f6510e21d7d4f324867d65d0b30f394b320c75c530c510bb59132c82766114810dbd49424c76e52d07319f194428436f5208610bd586100433d6115110b718d404c2dd60d0d43bd58443d07665294440cf18254cc76e5210440bb58853903d5310c710f68c6300c35f5350110be9805110f2d52d0040db14f524427e61d4e20cf15320443b45484110cf952430c67d63947209f58e54883ad548c832cf95143c835d534c840f3549300c27d6094743d794b32cc3766454420d794d31902be6190942b798c42cc2ef644cb20db94a208433d540c83097596430c77751946309fd85534436f6254d10dbd4b324436e528c010d9546210836d5214a30db54932d067f65ccb109b58a534875e6494f21cf990540873e54d0f219fd9432082f96010410dd945218827d6395121cf14942503776155110ddd92510c27d650c941e750c434c23e6414c10b798e420c73d5450f21db94b320437551145439f988534835e53cc620d794e321027d60946439bd8953442ef63c87209f58e544427f63547429f197424c67f6355110cf9534310bb561d0841af991329076e6295231dd584528427c6054e219f99442486f56114a309f19531103af5450a32fa94a200835f5394f209f582544ca7f6054e429f99440042f6658c5109f592500437661d4c10d758f540833e5350f409f18550d0a7b65480209fd8d544ca7d6294231cf95342042de631
  | 19 => 0x408827d6095021b758f411066e6294910cf55142cca7e6510830ed984411033e54d08209f986548c2df654cb30be980521067e61141329fd8550ccaf76150941cf99253c433d5410832bb98b41482dd6390030db14e32087765394440bd987421076e52c8640ebd89425039f6450d32af590518c2ed62cc721d750e51cc26d62d4c10cf95343042dd63d0932db19052443ad4210b20cf590538833f6355321d754f318836f5394b41cf552408436e4254221d754c530873f5450d319f185500cb6c5290b10bd181214436d62d5332b7586438c6ed620c421b798f41c873d4354041af597419067d6194e20d794c421027f6254343db94d320cabe640c931af99020842ed648cb20af593528c73e5454c20af593218837b5094241d758c548833d5415320dbd92520435d5454f21b798c429067e64d4121cfd8e54043cf634c9209f195414c7ad52d0b40f34ca31c83da5384010db548400427d6548440cf152534427f65d08318fd95401035e5350d209fd9441cc36e3294720d754f4310a7d6194c40b7d93320c65e6394821dbd4a42c427d65505219f597300427d6510420cf550544ca7f65d0430b758f520433d6494d10d7553320cb3e5410f219f58754883d4514c730db58a530c67e6550b10cfd8354442ed62d4043c750d5010e7f6510d21dd947300836d6194830de540500c67e6414532d7081530835d5390c20b7586304c27e62942319f994418c36e4294421ddd49100435f6454f21b798f41cc67d658c840bdd8d21c427d65ccb40dd945311027e65c84409f98b548c35c6454f21d755132cc3766115220b798c214c3b554c4010af593510cb3f5450120be98032cc33e5410730f598f419077454907109f1855090eed6210f32db90a518cb5d6194c40db149404433c6454630fc18131443743254420b7181434c33e6255331bb58b31cc27d64947209f1855010eee6290520cf950320c3d5518c630cfd09509067e6588630cfd51408c2de630c530e71854310e7e6588530b758e424c26f6254640bd586320875e63950319f996414876d63548109fd81520c76d52cc830dbd4921c433e6414810cf55143482de63d07309f19642843ad5494810d954b100439d5450e319fd96329067e6590d32af99321043755454420cf953428436e6154830d7d4e5308376518c4209f594325035d530c8219f98f540c3743254430d7d87534425e6514d10bd584500ca7e6015121b758f214427c65c8540b798f215035f6454c109fd8154442de63d5321ee191100427f6550930d7d8d53443ad42109419fd8d54c867c6155230dd98752042ed6210220de5405010e7f6590720d798c520427d60d4e21ed952510c27c6454c21d758a530436e520c410cfd9540102ed62cc631bbd954210b3e54106319f189544c63d64d4e219f58853842be640c740
  | 20 => 0x42f96010710af99054043da60ccb30dbd95420876e5214443d7550318c35d5310c42cf552510839e53d0f42bbd93324cb765190420af58b435027d65c85309f99642c42bf644c840bd58642c427d6395120dd54451cc2f86050a20b758e420cb5e6394910d7d4e31443764394430d758c54c827d6214f10e750d32d027d63d4141db547200835f5314910cfd8254cc7746254440cf94d43107e95284010d798c530435d53840109fd9152cc76e52440109fd85540cb3c6295321fc54540102ee620c220d7d4c32503af6450920db50e520c35d5314c40bed81438c27f6254c40be582210433c54d08219f594418c23d6494d21bd98743d076c528c5109f994324437b50943328f993538866f62546309f195404c27d65cc421bb99452442be640ca21dd987540867d6590a309f596410827d65cc810b758f21903cd320c830db54a41cc6de63c8730cf985540835d63d4810db949311035d520c6309f583548c6dd63108109fd9543842de63d0641d794f50d073e61550109fd94430436c52487109f98c528435f53c8510bd984300827c6550520e750f5210eed628c020bb98720883796014f10db98d52cc75e53ccb40bb58b51d0fb45150740eb14d4210a7d6510d219f99051483e532887109f59431502f960cc5109f984525036e63548439f99742482bd6490842cfd91544c7745108530db18e520c3d6518c430b758e41cc34d4354843bb588508c73f540c1109fd8d54482dd6390631db58a541073c5490630c755253c873d5494b31e750c430cb6d658cb20cf58554c867d6590730d754c41c873e64153319f99053486be640ca40d75855310b6f5290940f34c831887b551d0040af990500ca7f6508640bbd9232c82de6310b31eb50d428cb74538c710f948520c433c5450d10d9544210833e6415121ddd8d511027e6195020d7d4f314437651cc4209ed95100427e64d4a10d754c31c435e538c721f550e31c427d61d4940bd58742486f56190010db58f52442ed60885219fd8951cc35d53d00209f18d54486f86050d40be583214427e650c640bdd8e21c433e5450731db54a5010fac5450821d7152530433e5454032cfd0d50906bc644c440f3549328c67d61d51209758e54c42f76250510bd984508cb5f6454c20db152428cb5e5390f20bb593324cb765188440cf550548cb3f6155032b758f41902ed618c9209f983548c7ba60d07409f992500873c5410d20db54c524436f65487209f59442442ed6210c31cf94741d02dd6190f30cf18e54cc7755114720d7440534427d6294f10ebd0d424835f53cc110cf95142887cd32cc320d754c30042fa608c4109f58053886dc6348430dd947210836d62d4c10db548310c27c6215120d7cc5508c73e6494e21af18143d033d5494830bb98e424ca7d6494430de983520436e5148421cf55
  | 21 => 0x6394420d718953c867d6255020bb583324cb3e5490441af99321c427d65cc020db98a53c42ee6210821cf55143086ed6214341dd185544c35e5394b41dd551100437652544309f19732502ed620c110cf550414867e6510832d718653042bd60d0d429f592538827c6354642db949428427c6548440ddd4431503ad4350842bb98843c827d62d4543b758c404c33654544209718d544833e63550109b58854cc6bd6494f10be58343d033d54d033097d954310f3e54d0c20db551320cbcf424c832bd584504ca7f65104219fd8d52106be62d0d42e750d42cc33e5450310af593318c3ad62d0441ee153104433d540c010d314d32c83d651cc0309f595329027f6590b31bb9885010f7751d0520db14a325067d6550110db549218433f61553319f99631d033e5490230cf551420cb6d4254021d754f410837950142219f9865090efa6088710d719253c873f6455032dd54a510c35e5348010be980411033c5488110ded42500c73d6414930ed151214427e6494030db14b21442f66114143cf551200835d6315321cf95253083795014343cfd52418c27e6494a319f9865090abe64cc7209f59250cc66e62150109fd97310835e63d5030d7953534427d65908209f987540c76e5450a32bb98b41503cd320ca10ed50540c42ee62cc5309fd95329067d6215010db549321076d6154840d7d4e41443bb60509409fd815110f5c53901109758c548437a6014c109f9865010b3f54d0910bb58b414c27f60553219f98354cc65d658c430af993528c73d5450320db152424cb5d53cca219fd9532502dd63d4420af99321486fa600c520cf59052843b46444010cfd52548439d4350a31db151520435d5314c209f995414c36d6294e21db14b31442f661d4840b798c53082dd63949109f1815190b3d5390640bb996424caf96014c419758c50506fa6008530bd9875290f6d5290a10afd8d4310f5e530c7409f19431482dd63140419f596424435d5390842d714c414427f61540329fd9743482dd6310530fc54620082f56114332db94e521035e6394821f9d05210867f6154d21cfd5210442f56290510be181328836f65508429b988538433d5490f30cf950430427661141429f18554ccabd64149309f99640483ad4288740b758c520435e530c821d758f5150a7e6494a30db98852043b564cc6319fd95320866d6295110af592215035d53d0810cf15232443ce5394b41cf18a540cb2c5450920d7587534435d534c820bb988435076e2114121d75825310a7d654c440cf95042c833f4394742d758153d06fa6010f40cf951210427f6590f21d794f31c876e4254232d754d520436c52cc110cf95343842dc6354940cf55042c873e6415221d798b534436f63d4910cf952520c2f9600c5209fd8d5110a7d65d0831b798c50d067e6215231cf952420
  | 22 => 0xd109f58a54487745248710cb15052443cd320c421d7d8d544c67c6355220cf18b544427d6215330cf990544c6dd63d0621bb98b418c73e5450f31be983214427d6590430eb50821d035d53d0c10af990320867f60544329f98e500439e53d0f409f98453c836f5388420d794d320835e6454c10dd58a511027e6550d209f594324435e6314940bbd8d42c833e6414930db549200433d43d49409798f54082be6408010f314932cc2be6408740af99232502ee608c920dd151510833f5495021d795153042f661d0a21dd987540c37651d04309f996329035f6354e21dbd89518c27f65d0b309fd8553d02dd63d4840af59030c833f6550f40dd14a510c27f6054632cfd87544427c63550109f587524c39c5350d42be580315027d658cb408fd954210b4d5350842be98231c427d6510820ded4250106f96010820b798c52106dd6310921cfd52414827d6510720d7d4f32483796015021d7150534427e6095231db59632887776155120cf951424c3ad4210a329dd9510043d9600c430e75894310e7e6295131cf55342042dd644ca31dd195414427d658c821b7d9132cc33c6195020dbd49208435d53d4442dd984540c25f654c431bb58a418867f6510a10db50a51c835c6494c40db50a5110b776454430cf952420827d62d5031d7593534427e64d4c21db548421033d53d0842db988540caee62d0d32dd947400c35e5350840bd58450d0e7c6254e41d794f40082df654c730f5d46314c73d5454810db950524436c5290510dbd49324c2de60cc431dd946418c33d54ccb31cf55142cc6ee6214331bd58e21c42fa600c8309fd9442443753294430d79524310f5e5390c209f99443c42dd63d0531cf55210043775294440dd14951102fa60d0440bd18141c42dc604ca31cf951410c36e6214d40b758f5190a7d6414f20dd544510cb6f5294840db195424827f6454420f3909324c36e5290010db54852cc7cd538cb20cf98d54c867e6510831cf95350cc73e54d48109f994435035f60d4d10d754c318867c6454732dd545219037551087209f597430c27d6508730db948410436e5354b41bb58a210867f6454831b7d91328c76f52901109f19151882f66114840bb189418837451d0520db948420c27d64946209f18951d0e7e64d4f109f980520427e62952109f58454c835d5314442cf548419033d61950309b596420873d5450a30af59352cc75d658c430cf54f401036e52884408f992534436d524ca30b718132cc35e6314c21b798e214c27f6548730af590510c27d6590930f5984310c2f661ccb31bb58a31c836f52105109f1895190f9d5494f21d7d95430c6ed6210d10bb98a4350b6e62d5032d794e41c876e5250831c7153534436c53548109f984540c2f561d0b10bed81318c35e534c6109f98652cc33d5450430db1815210f74
  | 23 => 0xb55132482ed620c520db189534435c1054c10d798e548867f6354b40d7d8a53042f4604c710db54832d076d43948439f98053443b75150540cfd5152442df6354520d754c5350af661144409f994434c76e52d4043bb98b41c873f64553329798c530433e65d0d40d7597318c73f5495031cf15141c42f660887109b189534432e5454b319f997315036e5290a30e750c435073c63d51109f98c504867d65d0e10cf981540435e53943418f596540837661d5031bdd85404437551c8020b7181310c6de63906319f99353c835c5350f10b798c410c73e548cb31dd945319027f6255230d754d31c86bd63d0b409fd8153d07d6310c110d754e42042be64d4331af98341d027e60d4943bd9875390ade6390730f954a51102bd640ca30d7cc9500cb3f4354a419fd85544c67e64944329f58652cc27e6295030eb153524427f658c810af99351cc3755114630ed58743106de6310230de980540c27d6114132b758f218879d4314443af593518caf9600c730d754c32103e521c8110af59242106f5610c320d714d31443cf434c832db18252103cd534ca21e750c315037561d4e10db58a54443eb604c920db54d424836e5208440d754c308435d53d0f40de582544827d6394821f6980310c35f5394f40cf549401027c6254243db153524427d6294743cf953100425e65cc5309f58851502dd6310b10db94a200833c5450d329f593514c35f530c520bdd8553502ed6210e40cf951510c33d60d5110db58b540c36e6094840af990528c27f6454f209f59421042ec6048421bdd9131c42de6310830f998b419075c5450d30cf98e540cbd7414c4319f597400c37a6015010dbd4a525079f6550c43bb98b41cc27e61d50219fd94410c27e65d0520cf95150c876d5214341b798e544867f65d0e20cf5095010b755150420db548525077651084409f18153906bd64cc431cfd5343442f96088710d798c530827d6115032cf551400825d6315320cf151408427d6550b10b7597318c6f561103209f99531502be640c320eb5095110aed6210c41be980428435e5350010dd58654487eb21c8120b758f424c39d43cc940e7d91434c2f6610cb21bd587320c6f96010b40db1865210ebe64149309f58b54c42fa600ca10cf951210827e6590d31cf950430827d63951319f98c520427e658c9218f99053087ad4210a209fd85540c33d54544309f98b53c426c6254630db5865210faf5450821b7597328cb3f6550c41cf55142c867e64141219f99252842dd63d5010db94a320835e53cc841af59031502f6610cb31db54d200835e530c2209f98e548827e6114930db14832503d653944408fd91518c27f6454a109f593530427f6354021be980315035e52cca31b7d91310c76e520cb319f181520c73c5410910db5825210e7f6154910dd545410c39c5414
  | 24 => 0x54042bc61500409f997404c36f5308420d754f520427e6095031cf94d43d0b5e53cc0109fd8d529033f5410d10cf992528c76c62546309758f540835f534c521dd152510c3765188640cf550544432c5450821d754d521037960d4f20cf592524427d650c620b7582310c27d6114f20f310d320cb7663544309f983544867d64d45209f582540cb3c5450910afd8943d03b65110440d754c43d033e54d4321d794e310433e54907109f5964310bb943d0140e79894310e7e63d5032bd986308437b654c030d954520082bd64c8630af58f411075e65cc530be983324827f6550931bb98a43ccabc6050940f34c8324875d548c531d7189530827f6508730db949218c3776550710cfd5341c42ed6590a32ee980411033d548c420d714d308833d5450c30f34c8320427c6155330cf55153c87b7544c5109f9825310b76514c410d754c31c827d6588740cf55042086be64c84209fd91538427e61d5332db94b50d075f32946329f99443843795014232e79854310ebd62d04419fd855390af96008630d754c30882ee62d0641e7993314c33f4314542bb18943c867f6254c20cf95243c86ee62148409fd8d548873d5490720bed81424827e6550e21cfd5121442f66110c31be98241042be64d47329f983525075c6054f21d758253d076d62141439f189530435e53d04209f196438427e6294c419fd96210c3ba60d0b409f9835150b6d5250010bd584529027c6454f20db54a328c6ed64487209f98e508873d54d0c109f99432c42be6414430dd5445190be552887109f98e534436e524c410be58041d027e6094c21d798e52c435f5394d21fc58241c433f6555010ddd4651d02ed62102309f9805350abf6444010f354f200827f654c030cf58954cc67d6588730d754d300835e53cc840dbd4820c43ce5394840be582318c2df6250d30d794f4210b5e6454c42b798f410c33d54cc832dbd89544436d524ca40d754c430433d42540419f5865090b755190640dbd49314427c6550b30f3909320cb7551cc730db54a400c36f60d4910b798c54c837a5288020e750f5110f5e6314e20cf553424c35c5388510cf55241886be64cc620d794c314866e62141419fd95428435e43d41329f59431903745150540d798c505075f5390d409f58454cc2f561d5332d754d21043ad61508429f18d548877660944408f990504cb5c530c940dd94e310c6be640c840dd19251102ee62d0731b798c42843b76450710af191325067761551309b98a54c435f5394c10db548410c27e61952209fd97438427d65c8440db18e52cc6df64cc431cfd5242442be65d0940dd546318c3766114e219fd855010a7e6114c109f59431086f56194d429f98c514827e64d4f21db949420c37a54900409f98b540c39d43d01309f59743c42ed6215331b758e300c3b941d0140d
  | 25 => 0x27c6154a309f19151082dd6310820bd984528c27e6514d219f194420427e63944209f58a5090e7e6588440dbd86521027d6510f109f58f54087d943cc130cf952320c35d518c430cb50d5210eee62109209f19543043755190630b7d8d515035d538c821d750e51ccbe662cc531db14e32c83e562d0541dbd51320879d43cca41b798f210c3ce524c030ddd46510cb6d520c440d758e52c43f141c4110cd547401036c5490b20af590320c73d5410c109fd96430ca7d6394910cf550408427f650ca10bb58a410867e62141439fd95310867f6054a43be580530867c6550830db54a310433c54d01209f597314827e6294d10dd945300c35c6454c209f19731503754354420afd85425027e6394021bb588434c67f658c440bd58743c425d6394a419f592530c75f5454f21dd984504cabf6454132cf551210439e544c8329f98c5448755514c030db981521033e5410b319f594430c73d54cc020db546218835d5314e20cf553210833f6255010b759132cc36c6454810bdd9541107774294420db94832cc2f46150931bb58a43886ee62d4440dd8c5500c67d62141319fd9151c83e43248421af99020c42ed62cc430cf552320c27f6154343cfd51424c67d6295230cf98d540cbdb604c930d7597328c7cc6250d32edd52214427e6194e42cf18e540c36d6394b41cf152434835e53c8410b758e310c67f6590830be980540867c6114d10db549310c34f544c832db548428c73d54ccb21cf04154042de60cc930bed81439036f5354810db14942506ed60884209f98c540876d6215030dd54e510833c54d0521bd984208435d5314f42db54b42cc6fb604c510fc946300c37561d5332af990500867f6548410f558f214879d6150c43bb58b31842f9600c820d754d43086bf6150c41db186520435e6315210dd946210436f6194b31d7991530836f6154b41b798c500867d64d4930eb551428867c658ca10af58b439067e6015030be597409036d6508620be98031cc3754354440bb596210835d51cc0309fd9543c42f6618cb10be982439036d60d4910bb984210836e524ca319fd96400827f6254e41d354e210827d658c820d799253082de63d06109f984538835e53cc410d7d4c304436c5208310cf552420439d4314843af99321d027d63d4b10eb95152cc6bd64cc5109f588548c75e530c440b758f410877553440109f992510866e6215031bd58a210879d53d0040db98d52042dd644c730cfd91518c33d54cc420ded4250d0b5d4354b30d754f510833e54d0840bb988438826d6594810ebd89429076e5288410bd587324435f6194c42d794d30c827d6315010ddd85544879d4310f20c7551300c36d52cc8409f592530cadc6350531bd98231c433f5495120cf951430c2fa6010520dd944300827d658c841dbd4a214427e6294730dd984
  | 26 => 0x5cc920b798c404427d6095130dd8c9511035e53d4420d754c521027e61d4f20cf953431039d63d0740af993520433c548c110bbd8943c876d3254221af59252c427d6494a10be181328c36c52841109f98752502f5618cb21edd5141c427e61d4810db98a540867e65887409f992534876d5208210cf95341c875e5494f21f3d81320cbb54390710dbd89544c2be640c920cf953400436e52507319f595219027d6094d20cd152414427e6590831cf98e540833f5410620b7d8d544835e53d44429f99253042bc6454910db98b530833d5410731d7951430c6f7624c5109f995424c73f6295030d794f42c87cd320c520d754f100436e52cc830db55132086de6314620cf950418867f65d0e21ebd8d4210b2d5350842dd146314c33f4354a439f990538867f658c420e750e410c6f561d0310db14932c427e65d09319f596540cb5e53d0c429fd95310c35d544c930d794c31c435d5314c41b758c510836d52c8410af59332106ed6215031cf55250cc67e60d5321cf953530823f6550c43f958632087bb6050d40b798f218439d43d4043b758f211033d52904409f993530827d65d0c209f997320427d6550b31dd8c951083ad5490821d718a53d067d65d0d209f987544c376325443097d8d54442df6450c43bd58732107cd424cb30af993325036d5288430cf553520423d6414c20bd984434427d6394410cf9524310f6d52cc0109f595428c6de61cc230cf54f42d02ee62d0320d798c540835c5308510bd583314c6ed62953109f197414c2ed62885209f19532c425d6395110d754f51102be640c2209f191524436e5214440cfd5340842f66110120d7d4f424427f65cc620b798f51d0a7e6294410ded42504cb3c5490610bb58843886f46150a21dd544518cb4c53d4910db54b310427f654c4109f980548867f658cb40d754c320836f524cb10cf952500cb6d6215210d794e41042ed62d46438fd91518827f6590810d7952434caee6214343cf95243043cd32d44329f195424875f5384110b758f411033d540c721db94a300c3ce53c8020cf950200433d5490420d794d300835d5390c42eb948411027c6510c21f594731cc3765490510b758f21087d9535004097d8d524427c6550f219f996324427e6114d42cf952520436e5294430f3509328c67f658c740e750e5210f3e63953219f996424cb3d5490431db148304436f53508219f588548436e52544439f18d54082ef614cb20dd544514c3d5310c530bed81425036d62d5221d7d4d435067f6354221cfd9154c833e544cb21be583434c36d3254032f398f21c83b761505409f58c52c42f5618ca319f595438873e5494321db54a21d02de6310821dbd4a5290e7f658c421af590530435d5454c20cf98d540c2bd644c940bb98b5010ebd640c220d798e54486f560d0541d798f5404
  | 27 => 0x10d7181530827d6590832d7550310c27d64940219f19443c42cd62cc6319fd95404c2f66110c419f9805250e7c6550b10af593319036f64948309f583530876d51086209f9875050ebe6494931d794e42d07d4324c431db94b42106ed62d07209f58253d0a7d6494a309b58853502ee62cc720dd10951102ed60d0a42d798f54cc2f6618c010cf989540836e5294341f54c530443e45148720d7552530833f54d0920e750c43882bd6490540db588544ca7f6254c41cf15143c43cf6250d329fd9732107af4394843d714d4350aee6210120d714c404433e5454c109f19152c43d653c4010bd58321886dd6310b40b358b31cc35c5450e31fa580210827d6215030af59232503776548710cf95142cc73e5410830bb58a430867d63d45209f19532906ee62d44309fd9642cc2ed62101109f584548827e6294f41cf58b544427d6194f20be98021c827e6314141d7cca51cc27e6414a10dbd93524427d6590c30b758c511027e6394442cf98f544437664544309f592520c66e62d53319f1815210e7f60549109f595321077451c85309d98454083d7328c710edd4541d027e654c910b7596310c27c6508010d794c52d076e520c4309f19153c873f5495310b758c424cb5e5310c42b798c54086f960905409f594420c27e6094642bb18121482ec6250320d794d43086ed62d4c40d7551530433e5410230db19252103ce5394810db54a41043774394420eb14942d02de63d0b32de983548827d6314910cfd0d5210f6e6414910bb988519036d53908219f590504cb6d5290b30dd0ca510c33c5414d10b798c42487756254440d7d4d32c823e64949109f994214c27f6254d20d714c314827d65107309f592500c2ee6188420cf550420c39d4310e329f5825290f4d5308420cfd5342087755114443af593520436e5208410f6181434c27e6014c21b798f5190a766115220db14d52d077543544309f99250cc73f5450130d794d430c36f4354b319f586500436f5208510d754d411035d5350e42cfd0d52d027d6510b31dd94e51083795014032dbd8152cc6ed62140319f19150c875f6154c40be98241c42ee6210c42be59710843ad42d01209f983548cb6d3294421db949420827f6590c20b798c42043cd320cb109758c548835f5350d40b7d8d518836d6354b41bd9845090b3c5450a328f99253c42ed62d0541db9495010ef56110220fa98242c836c52d09109f58f524433f54c4110d794c32c837552c4210dd992510c37b5094341cfd86540c35c53cc920be58242902ed6214d40f58c630c433e5450330af59231502bf6050f429f997414876c6394810bd584308827f65c8730f514d414427f6454032bd58742d075e53908429fd9521083755188020af59032442f9608c820db15252cc75c6094f219f98a53d027e6550c21d758c528427e6
  | 28 => 0x195438875c538c940dbd85521027e6094d21bb98b54cc7b664cc631bb58a414833d54152319f583524c6f76488710dd10e510833f43944439f59742cc6df6354940bb58e320875d6395131dbd51520c35d6394a41f954b100427f6550440db14d32482de63d4042bb98b51d035e53cc6409f994314839f5450d32dd109510c35d63951109f98053c86bc6050a41d3548310c27d6550120afd91524c35e5310f419f59253887cf63909329f59630043b442504419f58a50906f9600c430cf953400839f5350c419f19643c82ee60c84219f980544433e51507409f597414c27e658c440db588535036e52d4331bed81324827e60d4c21eb151424cb3f6295010bb9884350a7d64946329f59253c867c6510930cb55320083cd62cc6319b98a53c42f56190c31dd945210835f53549109d987540c33f41542419f59542cc2bd64cc531cf990540c73d54d4b319f594400433f5450e21dbd48404435e53d0f41cfd095090b5e53d0f21bd58e10443d7614c730bb58a408827d6195020dbd90524427e61d53209f58f54442766115010be980510cb775194543bb98b410c2f66108010dd584504cb6e5248640dd546218835c5350e219f184544427d63944219f195219036561149109fd97324427e62d4131be580414c27e6548530db588538876e6354830d794e40102bf6150a41f658243cc3d7614ca319f582520c7ae5490842eb54942906ed62cc521cf151434c27e6494e109f595324433c540c510db54821d036d524ca10bb588430875c534c210dd10951082ed63c8720e750c41cc33e54d04109f59631482be640c940b758c548427c6454d20bb58b5150f6d5208430b798f41487ad4210a30cf545401027c6550120db58853482f7614c941eb50841c836c63948439f990534835653944409fd9152c435d5314e10f6181314c27d60d4543db948400427d61d41329f19531082dd6310320db94a42902de63d08319f992520827d6590f10dd94a214433e5494b31d794c41102fa6090820af59032107ce644c832d794e32086f56488510bb58b31043764294420cf593520427c6508540f9d4941443746494420f654e200835e530c820dd58454cc6be6414c10dbd8152d073e5490c20cfd9154cc6be6415020f558453442dd6310b41be181214827c6155130b798f410431e5454c20f318d424cb796015330be98332cc36d528ca409f595410c2f66190d41b758e428ca7c6155030b758e529073d54c4010db54b5010eee6214e109fd9543103d55354420dd945218c2bd64c8510cf951320435f540c430d7d4f434433c5450932de540500876d5290b319fd9153c867f6154840dd94540102f661cc310b7d8d42cc76d52149319f196434867c6154e429f592520867d6194b43dd545318835f538c940d754d511033c54cc9109f58a50d073e64d48
  | 29 => 0x14ca7d6548630bb98b30c839f6350d42cf550300833d5490631f390d320cb7542544409f5875350a7f65cc640cfd52524427c64543319f98252d06de63c85219f994430435d53d0010af59243503cd320c820d7151530837661d5221afd8941d033d61550209f994434cafa600c430b798c42c427c6548530af587421075c62d4d10e750d5010f6d62153309f98e52c42ed62d4c109d587548cbcd53908429fd8554cc33f5490d109f191538836d4354b419f994534827d6114930dbd8952c427d6494d10d798c53c86ef6255110bb588531074e5394840db98152cc7d65354420bb983218867d6194a40d7597328cadd63c8520af990328c67d64d4b10db14a424436e528cb409f595438433e544c8209758e544866d62951219f586544873f5408110f3d89328c73d6255010cfd85540c27d65d09319f195404435c6354640db988540c35f6094f419f58b53442de63c8410db54950d06be64cc6309f58a5190e7f6454e21cf953418436d5214910dd18251083ae6050842bd59710842f46155130bb58b43886f66090710af993329067f6254c10cf951420c2bd64c8640dd58754082f764485109f18d520433e5410720f554e31c435f5310d10cfd5352442756114142d758553c86ed6210c40dbd52320cbd7534c510db949420ca7d64d4e10af591315027c6354021bb99721483ae52d0841fa94a100427e62d5310de98053086de6310d329f185544cbaf43d09429b58b540c27e6394241bb98a30082be64c8530f390e5210f5d5390c109fd91534876d5454830eb50842ccaee620c110e750c4310b5d43540319f18d50d0b6d4394b31bd185434873d5410721d7d8a53d076d5210030b758f414833e5494432af593318867e658c841cf953428827c650c540b718d519027e6515131d7d4c318827d6590720db94940102f561cca21db94b42d07765494420d7986530837661d4f109fd91508c76e5454830d7d4d2144376518c440d754c20043b942d0140db54850cc7756115230d754e520427e6590921bd996414435d6315010db18152cc7766354420cf552408c35c5390d21f3d8932cc25f6355120afd91514c3b75190541cf551420c2f8604c530db54a40103af54509209f9865210f5d5390e409f59643087cd62cc7309f997414436c62551309fd89540c36f5348020be580219035f5390910cfd91540867e6015332bb58b53d076f5390821bd58452102ee62d0610dd94a510c27e60150219f98a519035f5394d40db10d52cc67e65105209fd95420c67e60150319798c52842f76154d20dbd0c52442be64d4321db548411035e4354843af591329075f5350f10d715253c867c62551108f990540cb655294440b7d8d10043756354440b798e54c427d60944429f58e50d076f6254d20db94d32483d46150e31cf553428867d65487309f
  | 30 => 0x7e6494b10d758f548c27c6550a319f98a531027e6294c10cf553420826e6215210cf952410c71d53d0842cf186540c27f64540319f18d51d036f54885219f994404c27f6588410ded81544427e6214530cf55243042f66110910d75974390f5f6014d10cf553420c6bd6408210db98a5390b5f6554c42bd987204435d538c840b758c424c3ce62cc530f350d5210f5d53c8020cf550200427c654c1209f595319027d6154c10d754d320435e5384010cf552520427c6454031d714d324873f6195321db949328c35e4394443cf98254c86be6414231bdd85435067f6454910cfd8154c86de65cc9309f58e52c42bf6350940db14e520433d5454c20b7d8532cc25d6315321eb508420c6de6314321bb988500c67c6154f40b798f52d06ee62cc620d714d204427d64d4f209f994310827f658c620bd58e41443cd4390932cf544419036e528c440db54a21c427d65d0520d394d52d075d534ca40d7d9253c876d5214b10db14a21842be640cb21d794d311031e5454f21db54a32d06be64d4032af590329033c5450b10d794e42c875e5354810ddd9151082ee6210e30bd58453902be6448740d758c540879d43d0b329f994428c33d5454032bb18931c867f654c521f34c832d027d65d08329f597434871d53d0040cfd53424873f5490530d750c514c37a60d50309f58b5050f6c6394b41af592329067e6395221bbd8d21c827d60d51319fd9642442bc6150f429fd97210c2ee62d4341f914931442f66190941cf992534873e54d04209f59443c86f5618c210d7cc9508cb3e54907309f58c540835c538c310cf106501033f6555331ab58b41d033f5410d209f99432d067e6494b31b7d85328c6be640cb309f181510cabe640cb319f181548867e61d49309fd96430c67e60d4810cf997425036c43149109f18552d034d544c832bdd85544836c5288530bd586434433f54d01109f98c54c86be648c540db981520c2fb65440109fd8554c82de6395221be982314c33e5150441dd509510836f544ca21dd54721c836c5248510bd98632d073e64d4c10eb98d4210b9d43544439f98b530866d62d50109f58e5090b3d1015110ddd44215033d65d0a429f98c540c73e54ccb31b758c42c877651c84409f18d529067d650c010dd509510c3af5290942d718153d066e6215020af590508cb3d544cb21cf55141c87e52108720d794c30042dd63d4542bdd9521c433d4354342d7d9253042f66110330cf95053082bd6494d109f59532c43da5388020db54852d0f6c5494810d794c43c873e54143218f993530427f654cb10f5d4e214436f54c8220b7d95430c73e5410721bb189100431e5494c209f98c548867e65d0e21d7195434c2dd6314b41fc946100435e53d0e219f992544437651cc4409f994430827e6214f10d754d410835c5350d40cf5935
  | 31 => 0x543329fd855290e5d6394821de58052c427e6590c21ed19251102de63d4720d715253082f7654c4319f98c525035f53cc941af99132d02bf644c640c7151434caed6190b20e750c4350b3f54d0510d7d4e534827e60d5031cfd53430c6f56110230bd98430c82f9608c930db98a53443e921c8120bb5924210aee6210c319f586544c76d5250a40cf952510c27c6454a31af990329067e65c8110cf58254c86be64cc431be98341842ee620c621f5545300c3b542907109fd94434423e6414810db58252d06bd640c9319f9825210e7d6115130db94a5010f6d5214430cf55242c83ae64c8621bbd8941c87ad62d05409f98b54cc39f54d4d109f181534869d64cc431cf152404436f52481109f98c5050a5e63148109f98b5150e6e65c8520f3d4d32483ad4210910d7d4f104427d65884209f992510c6ee6290e219f98a5190f3d544c721bb58b430876d5488420b5587320c6ee62d0f209f18553902fa600c8209fd94210436e6314910af593310867e61149109758e544c73e5494f219fd97418c35f6354d21ddd4e510836c5188120dd54741d0376658c510bb988540433c5410510d750e510c6ee6214143db98854c86ed6288020db94b211035e6294c40bd58d21c427d65950219f5865010f6d62d4e219f197214c27a60150219f194434875d53d04109f59051482ee6214f40b758f215034d5348020db981520436e52480109fd815190e7f65087409f98c540c27d60d5121cf55340042e56190821d7d4e538427d62d4141bd58743d073e54d0e209f18d518839d43d0831ee952401027e61d4c21cf54f429073e540cb21db8c851482de6315220d7d53534435d530c521cf552510c3ea42c8120d754d32d02dd6310220dbd0e52d06bd640ca21d754d510836d520c010cf50e51d03cf524c8319fd95420835d6454c20db948410c2ed62107209f994215036e5290a41bd984548c3755114540db94b20c439e544c030cf14d43502fb65500409f5835150adf6350630cf552300c36e52cc440afd91524433d54905319f58c50487d4614ca31d798f5150abf6550740cfd51324427e60d4c10d794e211033e6494b109fd8151d0e776154d20edd0a41442ee6210f32cf54641103cd5394b41cf997415027c6154c20cf98a540c2bd6010640db54e218827f6590431dd945410c27d62141419f59631d037950141429f58e52083d4534c710bd98420c435e53d08109f99441c82ee6215130b798f41c437a6015230f590e310c6f4614c941bb58b418833e544c010db986521027c6550b31dbd8c524427d6590431f914a21443756590710db94842d033d54d0f20bb986428cadd63d0540d714f32c42ed62cc7109f58e54c879d544c030bb98840cc2f86050a409f98f528427c6550d10af592534876e5290030cf150424c2f661cc921e755243cc2
  | 32 => 0xf98ca21c433f63d5110d754e438427e6394410dbd4940443d6438c5109fd95420c33e63950109f590534831d54cc832eb509329067d6550910cf553430827960150319fd94420cb5e53d0c109b588548c2f763507109f597321067f6550c41bbd95200835d6194c209758c540427d60951319798e534431d5454f219f586544425f654c030de5405010a7e6550c10b7d85438c7ad42540429f98c52c427f6254440d7952530436d5208710cf18254042dd6310832cfd53428c67c6054a31db952420876f61948309f58753c82bf6550b40db98853c82dd6395310db988548c33d540c430dd54e51103d563d0641bd98754083af54149109f58b504c7d5328c431dd584534436d52543319f9825110eec6250e42e750c418c67d62940419fd8153d0b3e6255030d754e31c867c6054f219f5845350aed64cca329f99642442ed6295131bb59321c835e53c8020db14b10442fa60d0f40d798253d06ed6210d209f58f54c427e6508630bdd95100433d5494c209f992530c75d5310840d794f31842de6310820dd54630082bd64cc440b798c5090a7e6495131db18252d075d6590f32b798c424c6f9600c410dbd49324c6ee6390a32bb58830482bd6414432f3d4d32c836d5214b409f98253c876c5208530db10e52d07b74290441f6d42304c27d60d50319dd8554482df63508309f596540c67f65100209f98c544827d60150219fd8954482ed62d01209f59353c42df6550f309f58a54cc2f96015031d790d520c76d5214a10cf551320436e52904409fd9632903773254440af5974290bb96090640cf551530436e52cc831f34c8500cadd638c8319f58f52506bd64c8621bb98b414873d54d0a20cf953438ca7e6550520af590520c33e62d5110b7591320c76f5414910b7d85320c67d6115230cf580544435d5314e429f18d519039d53d0f42cf953320c3b46150a41db988540867d6295010d794e438833f54d0d219fd95400835c5350110dd58653486de63c87109f580548c65e6314121bdd9231442dd63d06319f58b54cc67c6510b109f58b548c6df6550c43d794f52103776554430cd551510836e538c832e714d43d02af65508429f195424c76d52d0810b758b4390e7d60d4d41db549311027d64d4f219e58053087ad424c940bbd8930c82f76154940af591215035d6194c42bb98b410433d5410e21be58a200827d65d0b10bb58b5110f6f654cb20bd9844210775518c0309fd8553d0afa6010820f34c832d06de6314042ddd85544c76e5210b31db98853842de630c8319f596431036d6154b41db59632086dc6354141bd984320c6df6050d32d7192530833f6454d20cfd0a5110aed61881209f988540c27d6414e10bb58a434835e5350420db54a211033e6415231db94d521036d6590821cf553320c33e548c030db54a100427f64
  | 33 => 0x93214867f658c640d754e438836e524c430d794d50c873d6395010de980540c73f6195020dd544310836e5454810d714f304425e6315021e7593310c6dd64cc631db54a321075f530c610bb58f4290ade6314c10bd984510835c6094f41d7182531027e6394d20bbd8542886ee6290c21db19252043765150620be58042c835d524c030f5d8d31c43555394420dbd95320cb3c5450521cf95351082bd6408010be98042d027e65c8740d3949328c6dd63d4742e750c43ccb3c544c510de980530836e5288430dd946319037543944309f594424c33c54d0230db997214826e6514910db98b530427e6510020eb50d42886fb6548020b798e400c2ee6210d10d794d32882be64d45329f184524426e6214810cf950310c2dd62cc4319f18153d0a7c6590d209fd94320433e54d4f21db90d52cc67e65d0830cf953510cb5e5390810f554731cc2ee6290020af590320875d6394821db54f52443cc524c930be980310436d62d52319f994324c67c6550630d7d855310b3c54d09319f194438827e65d0b319fd9543087755148630d554d100435c538c5109f596418835d43548319f99442842de63d04209f5875050b5d6590c31dbd9252cc6ef64cca32cfd53424cade6390a31d7585531027e6394642cf55242082ec6254141dbd48325035d6214d10d754e32083773254430bb18132887795014143f6582318c2ef6550821af18141106dd6314840d794c211027d6194f42f988620c42bd61d0c419b98b530435e5350f20cf951300835f6254c40d754c53c427c6154b43d794e300c2f5618c010db54c218835d5350c209fd855010ef46150d31bd98732c427f6550c20db588548837561d5331af993314433c5450b209f195428436d5210b419f58353c873d5410421af59253886be64d4432bb588509067e60d45329f58a544c66e62d5231de58354c435e514c7309f19532507db32cc130de58354cc27e6115132cfd525488775510c440db98f524435d53cc721cf15343cca7e6414530db15142886df6150f30eb508429027d62940109fd9732d027f65d0f20bb18142886dd6290d309f996320427c60553219f195321067e61d4943be983320c35e5354420b798c42d03e65254440dd149214436e52500109f988544c27c64542219f189539029d63d0441b758f41c867f6354341d754e5110a7f65106209f597438867c6154b309f195424c2dd63c8730edd0e414435d530c421e750c438c35e3194030b758f41cc6ef64484219f995320427e6495132ddcc9510833e5490a32db952424827e65cc120eb953200833d54d0410cf952418c6ed638c920b758f41cc27c6454032d754c534435e6454f41cf95032042de6310d30de59710843ad4210841cfd5141c433d4394441db552218836c5208610cf590530879f6150c43bb983214827c625464
  | 34 => 0xcc67c6254f40db94a42cc6ee628c720d794f520426c654c920af99030442f661d5030b7d93328c6bd640c8409f996430427f6154c20cf597419067e6415030dd949210873e54d0b30db508514835c5490f32dbd4b31442bc644ca409fd9442cc36d6215130d754e439073f6555020b798c531035c6094c10db58b5150f5c530c5409b195424cb6d52908109fd9542cc67f65cca41b758c42cc67d65ccb41d7cca510c6ee62d07109f98a54442f661100309fd96420873c6055321b7d92304c23e6494a319f180544436e52cc010f34c8324c35e5450c43b798c42d067e65d0e10e7552430c6ee61cc9329f994314c35e6254f21bb591328876f6254d21b758f404c2ef6255130dbd4a52d06f661d0b31eb993210866e62153319f19443c835c524c9309758e5244376518c410edd5231443af5250b40af58a405027d65d04309f596418c36f52cc110cfd5130442dc6350a30f910921087763294430d7d4e524427d6550c10f3548310c37a5450040cf153434c6bd640c110db549400c33e5410731be58331cc35f5308110bd58642506f661d0310e750c430c67f650ca40be58342d035e5350c209f59742842dd638c9309f584548cb3f6455321bb583328caed62cc4209f596430cb3d5410c31b759332cc33d53d0240d754d421033e54d0b32cf55054cc2f960d05109fd95304837651d0020edd0e411075c53c8510cf152214435c5314910eb58b41907d5328c510d754d328437464544209f98e529035f53cc821d34c9500caed62cc740af592425035d5390721e755153c875f5390d10f390d32c836e528c410bb98b438ca7d6294440af993319033d54d0e20dbd4a31442dd6590e31f3949328c7ae62d0f42db99152d067c6055332cf95250cc76f6550a219f983540830d43548439f595320427d61d4943ddd4f10042bf6550c41b758c50d0af56490510d7597308c36d548c832bd98432c435d53d4341d7d4f524427561d4c209f596540c35e538cb20b759331cc27d63d5320d798c53c82ee620c421de980538835e5310c10db54821102756115020bbd8f218867e6550910dbd85520c2ed6210d40db550210837621540219f596310436d6295310db149425027d6494410d714f314433d5410c20b798e42cc27e65901309f59543442dd64cca31d754d30043d531cc310d794f320c35e5348410db54e521033d5448420eb5814210a7f65d0a10d790d508c67e65100309f98454ccadd6314242e7d51434c2de6310932bbd91328873c5410620bb98b548c6dd61cc930ed504410c7e55188420dbd0d520437753c42109f986500ca7f6510630cbd954210b6e5250b31dd544310c2dd63d0641cfd8e540836f5394810bd18543886bf6350a419f982544caf5648c510cf990548435d5388020dd90e510836c6494b41fa88620082f66114342ed5
  | 35 => 0xd62d0d20ddd0a51102bd64d4720eb50d5210e7f65d0910fa181324833f54d0a32ed50441443ad4210a21be98342d033d4294740b7580318c2ed62d5030b7181430c6ed6210f30db949329027c654c810af19153442bd6414a30d7551320c73d5410430db948210c27e6588540af99321c82fa6090d409f58a53903eb60509209d58754082ed648ca21db54b300c31c5414d10d594e510827d6510b10ed945401027d65d0821f954421082bd63d05409f98f544867c65d0e209f59743087d55394440af59321102bd64cc520cf551300435f6354910dd14e51082ee62142319b58a53906de63c8740cf55041c433f6455330d798e54106f5610c831bb98b53906f5644c510bb181320877b50943319f983540432d42944429f984534833f5495121cf98e54cc67e62d4c209f98e54c827f658c020cf597409033d65d0e439fd9441042fa60d0d309f58a510c35f538c310bd584204423e6414121bd592411075d3254231bd185428c75e530c421d754e31c436d5354b41db988524427e6115320cf50d521067c6454d109f59642106f5628c510dd4ca51082ed6210e319f98a5090e7c6354b40afd8d421067f658c841be58332882ef6250d219f58a54c435e5390f21bd58730c43b46150e41cf95143482ee62144439f99743c437651906409fd8152d0e7e6414c20db54a310c36e6154843af992528c76d4214532cf585540c35c6294c20eb50d420873c6155030bb181420876c4354810cfd5243483795014242bd58430442dc6150d32f998b318c75e538c820e795243cca3d6414f20eb508424c73e5450721d754c42083766114b108f19151883f1608c710bd996214436c5208110db90c52442dc6350731db94b21043ad428c841bb98854cc7b54290441cf98e540c35d5394b41d7950534436d52484109fd89510c36c4054840d714e41442df64ccb30d799053442ed628c220b758e420c75d534ca209f983535073c6095321dd59710842ec6250d21db550218836f528c930d7d4c315033d5490521cf990534833e5450c219f58a530435e53d4321dbd4b214427f654cb41be58031c43ce5354840bd584404435f654cb30db99452442be640c830bb98843902df614c4319f996434c27f65d0d108fd9541107cc63909329f1855290e7c65d0930dd905501076f654ca21b798f41d036d62d5220d798153d0774510c540f954721c82ee6214041d7d8153c86de63c8420cd551100427d65d0010d798f54cc73f54d02309fd8954cc7d6324c431bb98843106f6610c220cb551320ca7f6155132cb55252cc76e52cc410bb99642483cc534c920af99053c836c1054810b718d42ccb5f544c831b7982434c33d54102309fd8d5090baf52508419f194434835f53d01109f58a534433e540c820db18252cc6ef6250e429f58053486bd64c8421db95152
  | 36 => 0x720dd546400c2ed628c6219f59541c836d5494b31afd954310fd8604c930db98b54c87ba5488020d798c534827e6590730e754d4210b6e52100309f195438826d6215130bb189544c36e52ccb31b7d89314c35d54ccb30bb98840843af53508429f592528c7755110430d754f321067f654c832cfd5032443b451505409f59421102f560cc6319b98a539076e5494830d794e31d02be6414e209fd95315033d54d4c20dbd48424c2dd6395121d798e54c43e54288710bd185404437a60d4a10bdd8542886ee62953109fd95430c6f56190c219fd89544c35d54cc230cf150214427f6255031cf153430c7d7534c710cf951410427b6550040dd18151103b86050940db54b41cc6776550441eed81415027f6550e209f987530436c5490920db14b32502de63146409d986544ca7e6494420f9546218835f53d0510bb59132087ad5490b20bb58a535067e65c8540dd587540c33d54d0e31d7d4f32c433d64d4c10af98641103765190410bbd9521c83755190040ed951510827c6510010b7d8d504875f3254031bb58843cc75e534cb21c7151434c33e54d0440d7d4f314872c54d49109fd96410867d61d5130b758c408c35e53c4010af58e4250b9d4310d10af59020c427d6215131db94942cc33c5450a31db552324835d52cc230cfd89540c2fb6050510ebd8942d027e6510f21cfd4d425036e5450a21bb58843c867d6590030dd10a510c36d52cc430db552520c33e54900309f982528c7755110440bed85100436c6054810d758053443ce5390842af993314c6f66114e20edd52414435e63d5332dd50550106ed62d06309f98b540c77564944309f58253106f661102109f59721cc39f6350c41cf151434867e6510810ebd8b4350b3f5450f109f185544833e5410430dd591510c2bd64945329f98754082f9600cb209f59721042756114e20db95352442de6314a10b758e320caef644c821bb98b4310afa600c710dbd52520c27f650cb109f98f544827d650ca40afd8543503755150640bed81218835d6194f21db1825210ebe640ca10bed81435035f534c910db14b40442756114143cfd53534435e53cca21bb988400c35d528c630af58b41502fa6008630c354d4210b5d5390d20d79865310b6d3294432eed42405036e5290410eb94b42d02dd6490c439f58e50887f360485109f58b53506ef61508219798c50507cd3288730af592524c67c6054c428f593530427d62d4d40d754c320436f6254810cf95352cc75d510c630dd54451082ee658c920cf552400c37651d0420fa086200835f6094c429d984530835d5314f21ded95401027e61d53309f58a531076f5290510f594e31c435e524c831cfd53404827f65c8440db54a420c67d6094b31bb98b318c35e5388020b798a434cb1e5454c109f988504c6f46154d20d754f30c42e
  | 37 => 0x9f19543486f46154143d794e43907cd328c621cf99053c82ed65c8621cf951418427f654cb409f597430c6fb6050640cf950420867d654c521e750c43902f7614c1109f581520427e654c941db98b540867f6254640dd54631882de60cc631af992215033e5450f21cfd5140883e46150a21be582425027d6508540cf55152cc67d6414a10d754c5310aee6215210af59221d035f5394d41d7552318c3665254440ded42508ca7e6094e21cf150404433d5490a32d7d51328c67e6115032bd592104427f65d0c21f34c8510cb6e528ca31d7cc8514c2dd63d04309fd9732902bd640c920f994a21087756115110cf9514310b5d538c621af992514cabe65d0d429f18953c43775444010db54b10042de6310120e750d424cb3d540c8109f996418c2f860486109f58253887b541d03109fd895090edc6250f32f6d8d300c27c6354042db58a548875f64d4d10af58b43d033f54909309fd94420836e524c8419f59632043774394440eb15142c836d5290430af59052cc36c534ca21db14b41442f5610c910bd185429073d5290640afd91311027f654c740db90e52d075e5314440be98243cc3e652c40109f189500c6ee62cc431de983530833e5494c10bb98b41083765108720db548511039e53104409f592510833e5410f32bd584430c67e6015020cf50a5110777654c431cfd08515027f6550531d794c308433e54c80109fd81529073c5490310db94a511027e6014c20b758c42c833d6195331b798c424c3cf5314910d7d4e538876f5350a21cf949421075d43d4132bbd91214827c62552309fd9521903ad5210440d714d31c42bd64cc540af19151482dd6310431d755253042ed63881209f996318839e63d0441af580411037762944409f58a540c6ec6350932d714d320875e6254c42d794f41c86de6395110bbd8940c83b65190640cf951420c7b45450510bd98442086ee6210d318f99353c876d528ca30d794c420827e61148109f18953107776155130eb949401027e6215330d754f321033d5490a319fd95420427d6014f21d754d420836e534c8219f18954cc3cd5394840bb18930482dd65d0e43d794c318867d6394642d754e50d077751946329f58753502756195132cf552438873d5494032d754c5010a7c61542429f9944350a7f6590420db54842107755190020cfd53434c2cd63c87209f99421cc2d56190c319f99351482de63d0330db9865210f6c524c910dd151414435c518c130af993318867e64d4e20bbd95320ca7c650c010dd18a511027d6194a439f987535027e6510b10bb58b51d0377654c710dd544410836d52ccb41db54920c436c5248210bbd9232887ea5248020bbd8f21086fa60104109f987544cb6d52c84309f597320835e53943219f59053c876d5188420d718953d067f654c810af582415067f655
  | 38 => 0xe52102f66194d42cf94f43906df654c0309d18553483744394440eb949429076d6214c109fd8d5010a5e6395221d7d4e314837563944209f594418827d64d4c20ed946411033e6415320bb58a548c67d6015032af992329073d6494a31cf18e540839f6450f32f3d91320ca5d6315020b7d9131cc2f7614ca41bb98a535067d61d5330cf552210c27e6590f20dbd4a20c43765148440db58e52042dd63d0b329f996428c3d761d4d10db14a424c776514c0209fd9742cc67c6054f41b758f418427e65d0910af593214833e5490832cf50f5050afa6088620d754f42d07e651c8020af58b419066e62d5010dd545311027e62d4540bbd92320873f6015110cf951410837662544309f988548c36c64948439f19531882f56115220af593318c65e6315321f3909320c6f4614c310dbd815210e7d6550f20b758c425067c6550620d799153c86ed62d4341bb58a5150e7f64542219f59632506bf644c9419f191528427c6454b30cf55054486dd6394542f3d4d320876f54c8020de94610042f66110010cf951310c3cf524cb30cf54d421073e548cb21bb58850507cc604c832af592431076d5454810bbd89514c3e932c8120bb58b314c36e3254032bb988314837561141439f986540c27e6214d409f597420827e63d4121bb98242c836c6194840d79855310a7d6194e429f597428c36f528cb10f34c821cc36e6394b419f58a540c36d5250a30d7d52314c6dd63c8430cf949429067d6588530bb58843906ec6250c20f358f21c833e6415020db94d32886f965cc230b798331cc2ed6210120d798553102de63d0530cf95340c433d54d0a109fd9543c873e6415130de983538827c6255130ed99321886dd63949419f99441cc37b50941319f997420435f6214d10dd181510c2f9608cb20b798c54482f661ccb41d795243cc3754294430bbd8931c87764294440eb993214827e6394841d719353442ef6550a32d7152430c7766294440ddd47315035f6354f10e750c431077b6054d109f98a5010eed6294e41b798f540834c534c920bbd9321c827f6355121cf551310c27d65cc740b7d8d414c7ce534ca21bb9874290bb64190310ee951100437751c8540af590508c66d62952319fd9443842bd64cc940be58241043ad4210821bd58442442dd63887309798e52c427f650c410bdd85424c67e65109319f18d54086ed62d0431be58041883cd328c421d758a53d06dd63d4321d795243cca7d658c831e7551320cbb56115110db551200833e54d0c32db58854886be60d0c41cf95043cc2ed648c821bb98a43482ee6294e41de983548c3e76148720db94b42102f5618cb10cf55340c83e66190821bb988438873f5495331bb596328863d6494c319f18951cc35f6194c209f992544c2f96010d109f18950d0f5d530c440f3581320ca7e6494f21
  | 39 => 0xc35d53cc820dd546210835f5394c41af191504c776534c5109f19532d03e55148020bb189434ca7e6314941db54832cc2fa608c8209f58053506de63c8530db90b504cbd931cc1309f98854c436e62950419f194424427f6254d10dbd4a425076e520c0109f582544835e53d00108f596540cb5d5350410af1894350b3d54d0020db58a544839d43503309f98f524427e6014532e7d4d43502be6494f10d7551328c67e63d48109fd96420c67e6414e109f582518cb6e6094843d714e10442dd63d0831cf953418835e53944429d58754ccadd63d5020fa980210836f520c110d790d528c6fa6010710d794e31486ed62d0510b798c52502ed6214f419f980540cb775194532af59031d036c5288310dd546210c27d6494432b798c508867f6054c21d7592530427d61d53209f596428c65d6314121bb58a310873f64552109f191510c3ad42108409f58154043e76248510dd54641883ae5490821b718131cc3cd644c8328f19152443766588510e7d91430c76e5210a31cf953438c67e60d4543bb58850106de6310730bb18142483e960c8720be583310c375514c420af59331c875e53080109f59631087ae61508429fd85520c3755114640d7d4f30482ee62d4543cf953200833e6295010db552320875c6494c42d7951434cb5f654c831bd5875390b6f544cb20cf592530c7765354440cf590534827e60d49319f19432c427d6294d20b7d93318c6f561ccb31d794e430433f4314540cfd5142c836e52ccb308f99353082de63108329f596530876e3254221b758c51882ed6488120e750f32d033e5410c32af99232d03d7538c510d78c4504c67d6550620d798c53c42f565d0641af191534836f6154843af99331086f56110d10e750e31502ee62cc510d758253c867d6588640dd54621102bf6150e41d754e300835d5314e21eb50940c82dd6314341db95142c833c2055020b7586434c2ec624c521b758c52d027c658c810bd591214435f534c110f34c930c835f3294432ddd44414c35c6550d32d794d401027f654ca10db591520427e6590e21af590325033d5490c20d794e520431d5454c20ebd0d424cbe732484219f191510ca7d6014931db14a32c436c63d4910db544210825d6394b10eb151428caed6590a21d718d544427c63542219f597410867f6548020d758e544867d60d4532f990a214427d6414930db8ca510875d53d0b21de58053c82fa6090b20af990534833d5490c319fd89539033e5410531d794d420839c5350d409f994404833e5414432f394e32c835e53d4b41ddd46415036e54908429f99731082bd64cc7309fd8d544c6be640c8109f19153842dd63c8610bd986430c774654c510d714c30442ef6350a21d794f42d06f56110b419f58a53d02be64d4f21af58f419073d5450b30db94a32d075e534cb41dbd0
  | 40 => 0x6494821af59032cc3743294420edd5210443776294430cfd53204436f6114910db0c1520c35d6454f21f318a434cb6d5214940cf15120443765184010cfd5343cc27f6590c219f98251ccb3e5488010bd597218866e6295231cf151424876d528ca10db94b420427d6590b10be58241c436e52943319f596400825c6354640eb952428cb6f52d0910bb98b319023e6414a109fd95438875e534c810ebd91424cbcd5388420cfd52418827e6510e21ddd44314826c65509209fd9621cc3795014231d754c310827d65904109f59743442f56110c41b7d89430c75c6154c42cf952418867c6590f219f18954042f66190d10e7993310c6ef63c8520bb988430867e6494e209798c5050a7d6214d10cf551320833e5450c109fd81534877762544409f189538427c6454810afd8d41106bd64cca419f58e509077661d5232d794c50c867d64148109f982548867e6315320db94a10042be640c921b758c42882ed6088620be98341d033e5450e10d7d95530436e5210731c7551530435e538c440bb181324835d60d4d10db55221486bd640ca31ddd4b10842f66110f31d754f43d06bd64c8540d754f200427f6354620fc545200827d65d0c10be582218825e63151209f98b54082f8604c920cf95140c836f5284110ed951100435d53cc320d758e54c439d430c740bb98830482ef644c920cf95042c876e21940209f990524c33d43542419f98b514c27e65109329f984530867c6055032de94d300c33d5490731bd584421076d5208010d394d521033d54944329f59743883775254440f34c832506be64c86209f19542443e4528c510d3d95320cb5e530cb41ddd465150b5d5314e41d7d815310b5c6454c109798c52502f960cc610d794d310c2f960085409f19151cc35d5354442dd192510c36c4394840dd552510827e65904309f99430043e7614ca21cf952428c67c60546329fd9442042dc6350430de540505073f5450b10be181424827d654c110cfd51414427f65cc810bbd8542483eb6248020b798c54c876c524c110eb94a411027f658c010cf95232042df6348430d754e31c83765294440d758c5050a796584010cf553438436e5248440ed98742106ed62d50109fd815110b6c6255110be583218427e63d5010cf150414c27e6014d41cfd5254042df64cc7309f19152cc73c61950329718d518833c6055032f90c5210875e5314341db549401036d6590b20c714d435033c54d0f30db5095010b6e52144308f992534873f5495132af99353043e9524c030db94932d079d4310d31b758c404427d6294d219f58f5150b5d6194f419f9845050bd6514c030bd98640842de6348730dbd87524433e5454420d714f42442ee6210010cf153408437a6014810ddd4651083ad4350920cf953428c27f65d0620de540504875e6294c42cf952210
  | 41 => 0xc10dd544210c23d6494e21d754c43d067d6195120db54b311035e5454f21db54b420c27c62542319f98b53442bf6454520de980540833f64550309f98a524435e6154c20bb58850d0f3c6355032eb50a5010a7e60d4d21cfd91518835c4254c42dbd95428caef654cb20f9484214436f53149109fd94218c27d6294640b7983320c776510c430b7597328c76f6394840db086500833f54950309f98c530875e53cc820be181425035e530cb21af990520423c6454d20b758f414867e6395110b7d91324c3775194540db54d520427f61548109f58254486bd6414c20d754e42c867e650c540ddd4651902ed620c2109f595430873c6095032f3951320caf561d4f42af99032c427d6194d10cf55231c875f5390d42cf953420caf661d5332ddd45314c27d6588430db949400c39e5494f219f19631482f661d0921eed9110042dd63d04109f997434cb5d53d0f21bd98743442ed62103309f597410c75d530ca41af58640502de63148109f58e500876d5350a219fd94410c76e52c8610d798a53c875e530c7209fd8953c437651d0740d794f21102bd61d0940db580524427f63551309f19632503755108440dbc85500873e50500409f58b530427d60d5221d715153c873f64551309f98a51d02ee62d0740be181434c33f54d0521d754c52d076d5390842db94e32482ee620c821d794f41042ef63508219f98a54cc33f6155020f9586420879d4350930af59032c86be64d4b319f590504867f65440109fd8552d027f6154c109f580548ca7e6014e21d7d51324c33e5408430cf58154cc73d54d0420af59032cc63e6414d20cf951430836c538c920dbd4e42c833f65507409b588540c6bc6050b40cf59052043755114732bb98a53c436d5288210eb98b411073d5450410bd58720c42ef62505219f58e52903765490441d754e401027e6194840bd98440c435d5390b41d715243cc33d43947429f98a5110edc6350931db54a311035f530c9109f185538827e6114d10dd144314827e658c521f654d10042de6310631ddcca510c3cd320cb20d7952438c6dd6390530d754c41103e65288710d794f31102ee6210c409f99431086dc604c930bb58b41902f661908319fd8153042ee6214241b758c428cb1d540c430dd946300c27e6415031dbd95520435e538c020c755253082be64cc440db90d520436d5290a419f992520c6ed644c920f5d4e414431e5494f21db54b40043ce4350932dd54b100436f5350920cf550210c2de6310330db58a53442be64141329798c540c3556114d109fd9150c873d5414c20af181415035c530c620bbd95210871c5350d42eb95142886ed6210c309f594430c27e65d0e20d7991531027f654c830bb58b41106ef6250c20be980219036f53c8220e750c438863d6414132be583438c33d52d0040af191321023d
  | 42 => 0xfd9532903365494420bb98b5190f5c6294f21b758c54042fa600cb209f195410827d62951109f98f54086ee62951319f590514c27d6590e20e750c43086ef648c920cfd0d5010e7f650c420db14942c436f6194843d354e521036e534cb209fd95321033d5415310b718d10043d663d05419f99643c42fa6014831db50a510875c538c5209f99731c83b95444010d74c5500c7b76150a419f1815190fcd5308420bbd895050f5e5314042cf553418835d5350e40f958b314c7b960d0740cf950410c75e6395332db50a518ca7c6550d20b798e414c36f4394810be980434436f548ca21f6d81434c35f6414d10dd15141c43cd6290f32de58354c833c6395010bdd85204435f534c710bb58d21c82be61d02409f58f544867d63953209f98654ccbf221c4110cf952200836f5294831b7592434ca6f62551109f99432506fa6090c30db952520427f65501109fd9732842ee6210310ddd53108436d52d0410db58a53c43b761507409f189548c6dd6308110dbd0f52443d76150e319f988540876d60548439f990534435c5390910dd101511033e5490f32dbd4a52cc7755454430cf59252086be6414332d758e548867f65504219f59532907cd32cc120d794f30c427d6394742cf550400c3ad42907209f98a544c2de6314121cb54841103b54110421bd9865250f5c5354910d754d43042bd6414e20cf151404432e5454830dd54451d0abe64143219f98b544c75d5310f21e750e41cc2ee6294d10db54d42c82ee62d0530d714d434867e6550f21dbd5252cc76e51c87209f982531067f6590a109f98650ccb7661d4e21edd87544439f5350f40af98743d0abe60d0841bd98450ccadd63d4740be5805110b5e6294c209f99731483ce5388420eb50842482bf62508429fd89518c3d65354440db148324426e6214c20ddd51510c35e5390440cf952320836e6214c10cf95142c86ed648c9209f98e51d0b3d54cc7219d587540c3ea60c87209f58753882dd63c8521bbd85328867f6510f21cfd5253442dd644c930f914521482ee6214e40db952424cb6d6214e20be58341103ce63c86219f594430cb3d5414b31bd587520c35e514c431ee951401027d60d4943bbd89434ca7e65cc510f3948310c3cd328c520cb551520c3ad42d4042eb50a325027f6550d219f18d5110b3d5494c10bd984520c37754544209fd9153883755108420cf950420427e65906209f98e50c86dd63c8410cf55320042f46150a10d554e51102bd6490c43f914a414435d63d5010af59321cc36d524c8109f196214c27f6154e40cfd8154cc6bf6150b40d5544310c33e52d0b409f594400c2ef6254540d794e31c42f661d4c40bb588438433f6555030fc4c7104433e54d0e30bb58843d0bd7614c530db54b42d035c53d0d10af5974390e7f6550a30f3151320ca6d6214
  | 43 => 0x42502dd63d43419f98654c836e52484109fd815210f5d5310420f34cb500cbd45388510e750c431027f6590e20d794731cc33f54d0130f350e5210f9e53508429f595428c3645288510de980540875c6494f41bb98b314c73e5450440db94b210c2bf644cb41cf590530827e65d0831dd989511033c6155010dbd49214436f5250940bd98753d0b3c548c510d7d8453443775194643af58742906de6310b209f98f548435d5388010bb988520436c6314910af18143106de6394910d7553300c37960d4f109f195434c73e54100309f99642cc27d6294730b7997314c3e44148421dd144215037651506309f98e5010b5d43944439f587540cb3f42946429f195304433f548c910db548529035e5390e40bd984304435e63141219f195328427c6154c40af59053482ef6244010cf15040c43cd3254432d7949320ca7c650c810db94a328c27f6454b30b798f428c6ee628c220db14a215037561d4a109f593534435f54cc0309f983544ca7c6054742db94b310c33e5490720dd147414c2f661d5232af99331482ee62cc621f554d100427f650c841d758c548435c534cb20f390f324caf5618cb41e7951530827e6590f219f197420436e52908109f59531082f96010630fcd8141442bd648c7409f59731503755110020ed952411067d61d4143bd584531036c5490821cfd0e5190f5d548c430ddd89510c3f25188020d714f304836d52c8440c3551320ca7f650c421bb98b530427e6510930db99252cc75e63d5031d714c434427e65d0d10cfd8d540436e52cc030b798e52507ea5290040de94920082ef6550b209f58854cc73c62151109fd9631043f25190040bd58752d0e7d6394b41db54520082f46150e31be582439035d538c8109f98e510876f5290910bb58b414c67e62d50219f18d50107cd434c832dd945219027e6215010bb58a314835f5454c10dd58453882f96014443ddd4651cc27f6354241dd98754ccb3f5450d10cf50d529067d6195130b7d8d424ca7661d4c209f59052c435f548c4309f58e54082bd640ca41cf151534433f6550441cf15142483d4534c5109f195428c33c54d05319f99352c436d4254221dd951510c2dc6354910bd185204435e6314e10be98041d02de618c4309f58e548436f5250b10d754c53d035c5348510f9185328867e60944329f994219035d63d52319f5865010abe64ccb40bdd95210876e5394b419fd85544c27c6155320db58152d063e6495110be983218433e5490f30cfd8654cc6f66190010b798c42507e75148520af59132d02f66190910d754c51082f66115020db54a411036e5288740cf992524427f6550d10d794c31083e552544409f984544433c52d0940d7996434cafa6010b20db991520437551100309f988538436e528c430d9549510c23d6494d109f9974350af661d0c419
  | 44 => 0xade63d44209f98e52842bd64d47309f19732c435f538c6209fd96418c33c54c8510bd18542042bd64cc610cf9494210b5f5350510d7d4e53c867d650c810db151428cb3e5490c32d794c51082ed6448421db98b5150eed6214243ab5924210a7e6590a319f592530c2fa608c930bb588430433d548c8109f59431042bd648cb409f59643843655244010db585520c36d53548409fd95430432d5488420f988420442bd644c740bed81214427e6414e20cf950510c35c530c610af990510caed620c010cfd91540c67e6014c109f594420caf56190f21dbd4a520433f6455010cf553510827d6550730d794c329067e65d0620e350d5210f6e5290430cf150524427d6194a30db94821d027e65cc521f3d8d320ca7661141439f189518c27c6510e109f593534833d5190640db94832d067d62d4e109f18152d0f7965c8220bd58432086dd63c87109f98654cc2f56110821dd95241c427e65d0630f9d4a214431f54d4d109f982518cadc6355110db95252cc73d51d0040b758f41c436d5250a10dd996414435f5394f10bb5884390bce53084209f99632c436d5290830af58743502de6590d32bdd85324c67e6094442bb58f218876e6295310cf95340cc27f6548530cf189540caf76155130f398f210873e4114141d754d31102f56190f31cfd8a54cc67e6194d20b798c204435e4354043d794d329027e6315220ed55241c43ad4210621cf15331442ef614c821f9189510827f6054f21ddd44214c33d5414430dd945410835e63150329f99642cc7775394440dd14441482be64c8630de54050cc75f6494c20cf982540c3cd320ca20bb98843482ed62cc320cf98654082fa6015031db15152cc75d5390020dbd0d5210faf5450b20bb189310835e534c010ddd4651d0a7d6214143eed53104436f6254910dd544511027d6508530f550e310c74d52cc030f658331cc2dd644c530bb597328cabd64cc4309f195434c37561949109f982544879d434c841edd51214433e54508108f99252c436f43548309fd855210f3e54108209fd91510cb5e6315331dd15251083b641103109fd9432087765148410cf50950907d5310c510cf153304435c514c530b798f42cc3b55110440cfd5220442f56188210db98854cc27f6590820db54941cc6dd63d4b41cf18954c876d65c8220be181318c33d4314542a758f415037a60d5010e7953320cb6e5214341db509508ca7e650c620d354d52d067f6254041bd98742c435d53884409fd89509067e65d0c21cf55143042be6410d42eb553200836c4394810cf551300834d528c430d34ca510ca7d65908219f580544ca3f6454910db10f524433e5454f21cf153438867c65d0c21ee58343d03b76444010ded4250087764394440fad8121482f66110020bb58b41886f76044010ddd4441483e7524c510eb508
  | 45 => 0x5d0f20d754d438439d43906319f99254486bd64d4331cfd52544c6f56190831cf94d4310eed62141319f992518c3e9608cb20db14821503ad4210a319fd95418c33d53104409f181544c67d63951329f992508c6be6414121eb50842cc67e62953109f594438836c524c931d794d4310af76250710ab59321c83e64288421cf95031c867c65484308f992530c6ec6250721bb988424caee62cc421d794c41082de61d0e43ee181415027d65900109f98753483cc424c832f3509324c36d6414910bbd95320867d6294443cf95152cc7d753841109f195420c75e5350721dbd4e52102f56110120db54b510c2ec6255110bdd85328875e6054f21ded42500caf96010910db151424ca7c65cc9109f983530827d6508630ddd95510827c65d0b10d794d43882be640c120cf55241c875e65cc9309f99732507ad4210b30d7d4f20442f560c8521db991521035d514c030bdd8e214427e6115220cf55041cc33e64151109f98e51c833e62950209f18953442f56190e41be580431035d54cc930cfd5042442ee620c920ed19151102f561142429fd89544c72f5414910e7952530827c6254f41e7d50534433f5495320cf15241442ef6250420d714f104423d64d4f219fd81538867f654c820b3d95320cb6d64d4910f5105310c75e63150219fd8d548827e6295331fc98221c436f5294a31bdd8d214433e54d0a219f59743c827f6550120cf552200427d658c9409f994320425f654c832b758f5110aee62d4443b758b4350eee62100209f98252cc7ad5490a329f596434829f6550c43de582544c33d54d0b329bd954210af9638c030d754f52103d4514c5309f99421d027d6510b30db90e52102f460487109f58e5110b6e520ca419f9865290f7551144309fd96410437651c8720d7d5132cc2f66110b219b988530427e65d0d418f590538427f6154243db549300427f6454c10af59030482ef6050932d7d95531027c6510520bd987434c6ef63509209fd8d52d076d6214131cf906501037651d0040d7d50534427d658c540d798c54882ed62cc720dd946400c27e64948309f98251d0f5d6314940db10d5210efa608c630dd947200827f6154e20bb1895050e7d6394810d754c42042ed6210d21ed551100439e5490c43cf951428436c4354830bd185424875f53cc220bed8131842ed62d0f42e7d51430c7ad428ca41cf15140883d663c8621af993315035d43548439f59442042bf6550f42bd185439073d6494e21bb59242086ee6295231d754f52d067c6155032b798f41c82bd6408540d794f43d036d5248430dd984530873c6155032cf55053c877651104309f98c54082be640cb40ddd4b10042ec6254530cf95332c86be640c8209f994435067e6415021b798e5150a7d6494232dd9845050a7e6550d21b798c501075f5394e409f58251d0
  | 46 => 0x40bbd89314875d5390f41b798f5150b5f5394d10b758f41082cd62cc530b798c5050b5e5354442f354d200837561141429f1895010e7e6215031d754d4210bae4350842db949428c38e5350842ddd4621483e662d0541ed505404436e524c8409f59652043ad53508429fd9743c875d5388420d794c5110b3d54500309f58e52842f9608ca30d394d32886de6314840cb5095010b6e6494830af990518833d5410810b798c408427d658cb41bb58f21086bd640ca10d794e438439d5490f32bb58e42c835d43543329fd9153482f56290710cfd0d5090fad42104219f996319035e5354341bb588400c35e5350f41d758f548ca7d650c7209f987548cb3d54503109dd95310c6f561909109f98a50d067c6155232cf990548cabe640cb41cf553438cb3e54cc810cf151420867d63d52109f99053c833e5410a32de980548436f5294b109f18d50d067e64942329b988540ca7e6194232db14b204436d5214a31b798c428ca7d6194d20f914a10443ac6350842db94b210836f5388521cfd53434ca7f6454d109bd9521086be648c740b318d424cb7661d4b109fd9620043ac5250940bb185424cb3e5450c40eb1894350b5d5308440b7d92324cb5c6154c20f9d8921086bd6414831dbd4b325027e60d4e21cf990530876f5290931dd58e51103ce428c932e715143ccb5e63153209f99543c427d64d4532dd4ca511035f5394e419f58854c42dd6310b329fd96430427d6550420cf95041086be64cc6319f984540827e64d41329fd95311035e5310f40dbd52218827d6094f41db94b10042de6190d32d7d4f32c833e544c8329f99442503ae544c8329f990504ca7e61d5032f6d8d100427d61950329f990540ca7e61149439fd97428c37551480209f98c54843e532885109f59250c877661141439f19150cca7c6014d109f996434873e5414032b7592324cb3e5450c32bb588430ca7f65504319f18954c427c6510832ebd5352442de63c87209f98251d0abd6290d43dbd4b10442cd638c832dbd4a528433d54d44329f98a539027e6494221eb50842c867c6054442bd584304827e65109419f19543843ad424cb40b798f41507d5438c510bd98752d0eed62d04219fd8154cc73d54d0b31dd947411035d534c420db54b50cc76e5288730cf58a540c33e6195030bd587420c67e61d4132db54832cc6ed6214440d794c32043cf6290d32bdd85428c6bd64d4c109f19432843775194520f948520442fa60cc510db14b424c35d5354321cf951420839e5454c10db149414427f6354a10dbd8d520423d6414d209f99621cc35f6094f21b798c400c33d540c8209f5825310b3e548c010af590320c35d53d0e21db941200827d62d4f10b7592434c35e53900209f592500cadd6310a309f988505071e5494c10dbd5352442f86050510bb988435027e6
  | 47 => 0x195414433c51d0540bd185328867f650ca41cf50d5210f7551500209f19532487b95488020d7596438c67f6590a31cf990504ca7c62544309f590530875c53cc710af593218437632944209f58054cc75e538cb41d594d51102be64cc7309fd8154483766094430bd587424435c6414d10bdd85429075e4314532be597208826d6214143db982520c3cd53548409fd9442cc69d64cc7309f19443c87746454430ed55151082ed620c3109f9845050e7c6054a439f994324c2bd64949109f59721503ad5250040d7d4d43442be6414a109f99253c827d6114142af191219033d5490b31db54b421036d528cb319f98e52082be64c8510dd945310c27d65d0930dd545400c2dd63141419f18d524436d62153319f98851503cf544c832e7950310c374534c510db94b411036e528ca40db5485250f6e62d5030bb98843cc27d64949109f59352843cd424c832cf551424c33d54d0a30d754f50c867e6095332db54852cc37554c4010e750c414c3cd434cb20bd597318c67e6114d409fd81544c67e6414910af592401027e6510b31be980414c2f8604c510db1855210fd95348020bb58840843ea524c030b758f41d035e53d0c41db50d52cc67d61949109fd9643c42ed6210f109f997210c2fa6014c41cf95031042bd63d0841af58743906ee6210720b798f521035e5394440f398b310c67e61d50309f58a548433f54509109f58b544c6f66190c21dd54521882bd6414021eb59321c827d6494f10d750d508c67c650c9419f992520872c5250940db98852c427e6115010d754c438876d6215010dd14621483ad4394843db94a21c42be60d0441d754e43c86bd60d0f429d984548c27d62145439fd9430082dd63c8420e7d8d435036d6114910fa18910043755150040e7550310c2f86050640d710153102be64cc7219fd89540827f6550c42f3d85320cb6d5494810dd58753082f561880109f58b51502f4614c9319f59053486dd6310831dbd49325076d520c810cfd9154442ed6210621d7d51320cadd6314442cf18154083d46354430db94b5110ff16088710bb987328cabe6414420bb59720882ed62d0440a758f419075f53d0d20cf552410873e5450030b758d21cc3ad4210a41e750c434827d6094443e750f42cc39d4394043dd949214437b5094043af593210c32e5454810eb58b43d0b6e52d00409f1815390aed6290e42d794f421029d64cc631cfd5240c427c63542429f597428c67d6594c209f58e518827f6154242de596100433e6414121db5885350b9e5350040afd8d42d033e6494c31af59051882de6310a20dd50e510835d5350e20cf14d4350b3d54d0832cb550210835d5350810cf50d52d02bd64143319f58251cca7e6014543cf55343cc6de6314420bb591214836e6590920afd91534427c6055231bdd85434c6ee62cc4
  | 48 => 0x3ccaee62d01208f592528c67e6314c20cf55050cc6ed65d0a429fd97430439d5310440f5d4d21442dd63902308f59053c875e5390c32d7d8953d067f65508329f58e50d0af56115230d7d4e204435d534cb21d754e329063c6454d109fd9621102756115030f5d8d100435c53d01109fd8d50c873c6454d109f59632902f661101309f196424435e6254c10eb551520c33d6055321bbd8d210867e658c940bb98b41c833d54cc430d754e50c867d6494c20ebd894350b9d64cc730cf55341842bd6448740bb98b43886ed64c8621bb98b540427d6094b43f394d200836d62152308f990530827e60d5021cf55043cc7795014243d794e210833c6155020cf95043886f661142439f995328433d5410f32de5825244375518c440e750c43502e5618c821f398f214827d63d41219f18d51082ee6290720cf552310c36f5294b30cf95332082bf6250c419798f52042ef614c920db50c524427f6508440eb951520c27d61d52329f597310825d63d4542cf58654c87746394440d794d31082ee6210f31db9915210ff3604c510d7d4c434833e54d0930cf553300c33d54508109fd8d51d027c658cb109fd9432d066d6214e109f595318825f6354620af98740102746548510bb98850d073e548c430be583210827f6590010db988548ca7c6054443b798c5310b5c5394910d7d4e32443655254440af590500cabd6414332cfd0d521075d534cb41cf990548c27d63d5221bb988520c2f960d0a20dd54451882be62d0f42dd981510c39d64cc631bd5845090fcf624c930db58854482f661d0c21d794e4390bd5510c430dbd5021883cc534cb20db58252cc75e534ca10f3d8d32c836d520c831dd946200835e6315120d714e434437565cc6319fd9741cc39e63d05409f58653d02cc6250d329d195314427d6394740db548529076e52087309d584530827f6508430cf95241cc6ed6214430bd58e21442dd63d5221dbd4a214c2f460505109f99631502f561d5030be58032442dd63c8740d714c204427e6394910cf18d540c3cd62cc530bd58732486bd64cc521db14e52d06ee6210f219f596328433f6555321f394d52d075e64d4d10f9d85428873e548c020d794d43c87b54110540db597218875c5450f329f59630082ee62902209f98c540427e6015010eb58b41d033d54d0b219fd8951d0e5e63d50109f58654cc2ed62cc620cf15241882f76154132d754e314875c53d4910dd586544cb5e6315321db8ca510ca7e65ccb41bb586428863e6415030dd946210c27e65d0a319f594434827d65ccb109f58354086bd64cc4109f19531c836d5294440bb98b415067f654c910b798f418835d5350e41bb5885050f3f54d0f32bdd85438875c6094c429fd95300426e62141439f592530876e53149109fd95215037453944409f98054cc67e64951209d
  | 49 => 0x6e5290a10b758c54c82df614c930edd91414427e650c8419fd9731d0376538c510dd547210c34d5390842f914921442ec6350a32dbd9542c833f6550b409f98854482dd63141429fd94410836e6294f20af59032043796095110cf94f43d039f5350d42b798c40043355110440db14a20442bc6454121cf550544836e52d0010bb58850cc77551cc420dd58753c867e6294440dd10a510835d53cc810bd181314433e5414b31f3185320cb3f6055032cfd95421073d5490710cfd09501075c534c9109f181530876c6194830db98b548cadf6350731cf551410827d6548110cb552520c35f5390e219f994329075d5308420cf54b409036f5294830cb951428867d6414f10d714f32487cd320ca30bd98221442f561150209b58a53c43af6450b20dd951414435c6254c109f19642c427e6414931dd98e511035d53cca409fd97428c75d5350d20dd547310c2bd6494a319f99742cc27e6315310d794e421036f52d0110b798f218833c5410520db94821c436f6094b41dd54730082f46150e10cf552420cb5d53d07219f98b54cc6dd62cc730db19352442dd6290c31dd547211033e54c8430af59353c867f65108219dd95210875f5390d21cfd52304427f6550030db54842cc75e5310b41db587524427f61552209f196434435c5390d41cf99054ccadd6308730ddd465190b3c6355010db14a324433c6454910be983428833e540c4209f196424c77b6055130dbd48204436e52d0830db94e320873d5415020cf553438c33d5415031f5d4531cc3e552544309f59731103af4350b20f694d200837551cc030cf95141882ed64909209fd9721d02de63d4440d7d4e318435e5310c41db14e521033e64d4532e794f431067f658ca10dd98653c423d64d45329f181544cb3e5444010db985521027d6510c20dd547311035f5454c20f58c430c43b76150e41cf150304427e62d4d40af990324c27e65d0110dd546310827e6590a10d758e54106f76150310d754c51103755150630dbd4a524427d65c80109f983540caee620c210b798c430c73d54c84309f99053c87d55394420bb988439076d62141419f195420427f6355030db99252043db53c41109fd9151cc2dd62cc6319f59741cc3ae5488420bd98453102be64c8640cf98154cc76f64548109fd8d5190b9c5450d329f19641483e521c83109f196430427d63952219f59543c873e54cc4309f58c528427f6054b319f99632842dd6310910db948200427c6355110f354e320867e63d4b10d754e30042dc6348630af983435027c6355321cfd51414867e6415010bd98742d06f5638c431d794e32c87ad43d0942dd546310c35f6354c21dd98654c42f7644c510bb58632c836e43d49109798c54c827e6194e20d794f431027d62d5230f394b32cc36c5450b20cf50e5110f6e6215320f398a4
  | 50 => 0xcc430d7d52530827d64d4c218f590528436d5250410db10d521035e538c421eb50841482f6608c510bb588410876d5248440db94e328873e5490b20be580521076e62150319f98653c827f6454232d794c42c86df6050f32b75834390f5c6194c429f18c544c2fb604c930dd991511036f62551209f99441442ed6210f409f986548cb3e5490010db54942cc37551904409f594310827d6094a41db54d420877552944409f588535067d6414e20dd0ca51103755190430dd946218827d6214d40e7d8d439073f5495230af990431076f6154b31db597328cadd6390a31e758f411076e6394810eb508420c27d64d4d21bd1855050b3d5490b21e7551530433d54c8020be983438c37553c4010cf58d540827d62d5210af99042106ed6210010d7d4e31503d5310c421d790d50cca7e6094e41ddd52510c36e528c8419f58c54482ee608cb20e750c43cc76e524c810cf950410427c6510c20bd58732c433d548c0109f18950cc73e6494d10c755253042dd6090d32dd94a21c427e6510531d754c31042f66190821b798c509075e538c431ddd4651102f9608c410db94950d076e6094810be58021043db31cc130d714f41442ee6210130af984411036e4294720dbd49324435e53c8010dbd48214c33d54153219f995420436e4294442bd58e314434f5314910e750c43cc2dd61cc831db54e520435c6294c42b758c42107ce434ca219f994324835f6550c43f354b300c36d52908409f19743c827e6294f10d794932cc33e54cc030dd986544ca7d61548109f583540cb3c6355321af59053c87ce534c832db94a420c6ee62141419f582510cadc6350330cfd53424c67e6510430dbd9152cc76d2154021d794c431027e658c510cf953418c35d520c430d758c544c33c5450130d354d52042be6494d21cf153424427f6255010d754f32d033e5490430d7d4c424435e5350842db90d5210fd661cc831f398e428ca7f658cb109f181531076c538ca219f596410873f54cc9109fd94420c27e65d0420bb58843083e852c41109f99250043e651c8720bb98b314833d5410c32dbd4d52d075d53540429f994204435f6154c20d7590534436e6295131cf95343c827d6548430dd944210c35e6314a10db90d520c2ed620c020cfd52548ca7e64d4d209f99252cc33e5414810dbd89544caf965840109f58f51502bd6414b319fd81540cabd640c921dd5472108376514c620e794e41103cd528c430d758e524429d6490c43cf152104436e4394810b758c504876f6394b41b7987300c27d60d4941af991315033d54d0f219f196438839d4310e31db949218427d6550630cf552410c27f6154d20bb189404827e6095131d794d410435d6314810bb98a4390b2e5494830cfd50534436f43548409f594424c67e6014931bb98b430876d5214831e7151430c7
  | 51 => 0x3074451c0fb000a000c000000000f0004004003801f000003c000001e001000487100000064c5c00ac0ec001c00700040030000087000400a04600020004014000000300040000000000001c025009802a0000000002001962385a300000080024000001c007000c0ad005003a035800500000574aac11500040e7001c000000c00700b807801ac0000020002006800300340137120024000c04404b80050000002001006c00000070044009000000e00000010050000000c00b001000a00e40000720136005007b0008001081c000000003b00300010000000002a16f071800f00b4000000000a0044003001800200080010018004008400000241700010000005800f024000a00200e9001000100b000c084c0080ce00c00060008068800700000340080079007000c01dc01a04540b6000400d01c407000200500008061006400600000020098016000004900480880134407001000502b000a004021b0208026026800a051c03502944af0030000011802c010400101080005b3400f002001301fc009013001d00000180034cb00004001001002b000800d003400b0138004002802d00000035778034012008f0000017000000200080000034064000009100b14820000003005c0320004028000001000000080010004000dddb0024013000000b0098003000019b00240000004000001c02900002f900a8009002401600000000094011018c0000000024018481b002000a00280940060000104401801d803600d0011001400000080951c2000703f801d0010001000000104440100178002001800100036e5250a40bb98a54443ad5494b319f9825190eed60d0942b7982430c67f6155120cf18e540caf66114c20cf55343483b76450441fa8cb204827e65cc6409fd9732d067c6454831d7546318c37451cc540cf553320436f4394830af593214876e52d0410b798c21cc37451c8540d7d4e530867d6548740af58241903e66108420db99352442de63144409f980544cadc6050e31be98321082f561d5020af990540cbda5344010e71814310f3f64552319f98354886ec6254640cfd5142087cc53149109b58b5150ebc6454630be98053086df63503309f994200427c6054b31be98232c82f66108510f34c8320c77565c8621cf58d54c873e6295331d7d8d544cb5f534c921cf551418827e65d0f21f3d49324c27f6354840d754c31d03755494430b758e42cc27e6494032dbd8d521035e5350e41bd986324433f540c510bb98a31887d65394420dd952510c35c534c941b758c429027d63d41429b58854042dd63101209f594320873d54544209fd9431c835e6054c20de58253483ad5290440d7d50318c3d960ccb309f997214c2bd64c8410d795143cca7e6415020dd546410833f64551329f99421103cf53d49109f196324435e53
  | 52 => 0x3003802400000cf015811101340750010014001433d007c00f00000150778063012405d053400000007ef001c0460134007002002900b80090074003002000900000070000095000803400cc15c0000011001c00001c800100000030000015000000000023c4001806e05700050a9802c0008057001c002001c15b001800d000802100140014ae8020002800c01dc025438801a002801d009000000080080188036004c0fa0014014004c00b001402202d4023000c44b000805c0858009363800000000350088000014c00100003960000020000000282e00b943b800f000400302e810f0004016001a95a07ac000000800c000c00a00280000188000004c0000000024000000d003000b001c06100c8020001c00701f40080058025006000901ac001001404c00000a00018000020c094002802500fc011002400400280000314020005800b0519b4d23a000201f00060014009014c0030068026001c002001000a001800000540070150062525c066001c042004c06906e000b003c09e002c001007c0010000000000c0ac00100180004dc7000402000083b9000400300ec0610010016152800000081bb019800f0414033016801d000003200765fd014000604e800301a400a0084554050c20b059c007002c0830000054000c06903ec1e1003c09e011c02d0cb407602ec0030004016002808d00c072a013400d0ac4000000c00a0bb000e0014490001001202e4f3013100c7004001f003002300040350000003005400700e00030a3400f00c000001b008c045001800800000008047010000303c000001b800000600000008000008000100140000080110555000100180590010000031400e000002402d003600ec008049401f001000b2e3402b000400c0008002003c0020000007000000b00340d40048120000000e016c1b9000400407600160040002000801f00000df000401a000000000e8060015400d0000003002802f02940000ef0cdf000404801b40190c6400303ac00000002cb09ac01200000100008002000c06a011800c001800b001400e0100000000802400b8002001c030002400301bc004004002804e007405f400400000ac0014000001004600ec00c0ed40110410eac04f00050024000001800b0010002004404100fc01e0044000000400000000160058001003c061007801900103e9056da540228004001000900000060054001000000000040200dac00b000001700000aa0010034005800100dc0000034012001800400780dd000000c0020008002800100f0001009400013800850000007002c04700000860000006001c000000400a06b0004002800201180390398061001c06c0050005000809b008000000880180000001015c03c002802e00500030005ac0000011200ec00500ac0e9000c0de001405600ec001000
  | 53 => 0x4066000024e0000000008c014006c015001002306a4018009411a00b4023006800200380140098068018000200b40060010005001c006000001300240020068018040400b002000903940130000037007800000280160008007008804300d509000701a6004800b0018008003403c009402b0acc07c032c0ca00040000004002070c0010054005004400f0018125005c48302680032260032001c01422fc0c30054004004c0cb001034e017802700c0000002c08304600000004000000c009003405200cc000023400101740694fc400d134035604d0fc8000c001007c011000c002000000401c000a00100070000000044c00000a400200d400e00800000004009000c00000d0048000c02300043b20128055002c1cd35e802c002c069000002e03b80810024000002c00b002c04c07d0004000001b002d08c00bc00700000010008050029003103ec001045c03f04cc03000240030004001000c001000401500000fc01740010020028000c0020024003000405808ec00100380d4011800d000001301f40090004052000400413b000a0600000010000000400163e8800e0010063000c0090000002001c002006c0080000097076400200c80180020065002404c00180000004000000007300000010000000001c00c000c0040088000000001d000800a041c03900ec001000002000084fe001401600040030428000000001e0004000023c000000876200980000038006000178102a5aec00180ad04780030014035261403704c002b002000f001403a000401c0008000007c00600d4003001001e0d381ab00009cf00d400e002400b000005100e403a00600000010000000000f0000001001400f006400000500d600140090089589000401001c407400a802501900010020000027000c000400b0010018003c010000000f0000022020800c225c00f012c065014000d0004025a14c006006c00000140010004000000000000040000048000004400400040cc10a0003306400b00d400b00000000004002012000500180cd02b0001000000a01c8000010400500dc00b000c805000800605b80bc00340051afc00b11b001f001402e00280111130012002c0160408c08007c0060010001001800000900070304075000c79e000000101180090198001000000e00040b30000000000400001819b9000000000040000444091003910c034c00400740ba090000000a801205e40150004000010401b001024903040020000009017401c000c00400ac1370080001001004f02b400109cc002010c014000000001580a7001c0030014000011c00c000400000a4008000000200080000024008008801d00440040070007000c01e006407f047c02a0358000011c00903340020000005000000100000030054007001c00500000590018003007c00a004c00
  | 54 => 0x1000c0010004018003c039010805800800d3000801d0018007015c00a002809f003c00a027800000100170000000002800304662b3009c00800000cb005c0110008055002400000080000008030000800b0028002000c00000702410664002008c05300280050010000003000a048800069182b90478256001000100340010024009015c208000c01f000800a000400600000090004000019407b05d0000009008a0eb4006000053a00240010000ba300840010050000008403d0094009105806b004400000003740020262000c000000000f0020005003c0220054054000400a00a000b00018050024090100800e00000010050015000c0b90018005019000d001c006068801c00001070024068006800021fc0000000000000400400e000000541160188016001000f003400d053812e0010000000003307bc02d018c007004851b01a8003002800001ac48202c01ab000801601000ed0a1c03b000000700e40061f000000048046007c0000010000059c079000400d000000b0000012003800402500060020009000812c0010012002400300080010000000000000f0038051019c00500380c600000130040901000525500100110004007002c05e02d400f00b0006000800c000401c007c0010010080000c0330000000004c00f07380020054000000000b017800019a403801b800501200000020053000400b03b604b00cc3bd001802300040083b700000518000003c01601a0000000000b005c0b7014400a051c2d100080ba00ec01f0014000013c03400000350068002000000400e4001000000e000403b004801b00640000088002005c014000401300a40020000005039800504c801303a8021002805700c404701140c100080000004036036c00000086a20004000004000000d403e003000a001c00000b000d002c0e401e015c01040000014005002400000080720004011003400008c000b1718003000802e00100000040003000008a01a400000b000102a40400000000000dfe47abc006014401400b801e001400080ac02302a41b50000002011004400040010004043012800000b80a700059860000036000000b0008f0b03a80070010069000018f00000650000009000000b0050016003801f023800b0160000000017e022c0d9000403100000e801e8013000554602bc026007c02b006805a0014014000000700040090088009000000a000001e01480770014000004c00c2c2400702dc000003802f00b00050018040009001b002400a0894000004800600180030610007000034201ac037010c003024c01b00ac011000000700ac001001800800c400d003c054005c009000c082015807a129002a001400405f00240004003030c017000000a00080100b5000f021c0aa0014002001401b03ac0040015bdc000001a007800400
  | 55 => 0x5c0070068004000000101b8002001c00f003c009002400400000050008145000400f0010015a2cc003000000f049808a00e10d6003c2da00140bc00480520000031001805a0244004000822d0074021009000e005000c002c013000000000b0032008404900e8000000c0055718020005005001841fa00fc054031c0030100022000452700b81060050000003c005010818100b4016000800002382a3000000000700050c6800d0254005004400200841c20280278010403d00e808d0028006007000a000400a003007b000401a00b800200640090000000000000402340570acc185006400000ec076001800400b41710004000000001200400020748020007c0130078016005649600700670aac01500ac0040020007039c061057406f005400302f40010050007006c0010000001001400e012400900d403500d82d0034c00800800000184000002c030001400311380660000127023003013ac001004c05d0000026000000a004c00a000c006034c00a00001ea00080131d78008003803000a01440090007000002d005802b005c00701040c5000000304b402801640070194088002414c001001602ac23100000440004031001804202f404d002800004e000c000000701258f28a3c01c004000c000400e11e800d000c0ab0000ab0006000400000140010000013005200b802b08d807d00380000008061030803902a00070274001251400101280015348000001801a001c012016c02900600070020024038805e008400000301b8001401c001006500f4019018c01b0010034000800100000010124001012c007018c75001280080008004008000100000000050000003803b005800600000020084006000400801400000000112004c00d00002c3011c004000a62c0150002001000d01a001b008002b00100cf00780390c200070228019003403500240410004008008002300944b3000800288715f000f00dd00243f500840130020008003c0025444000007c005000400100240020080001001c024016c00f03c40060000000000cf4100881890000008000001b003400c0018000005c00505140050390037000014c001c01b000000c06e400e00040bd00000000000023000000000000020024006000002a0018092013800654a400076e8003003002b005c009000c0030058025001400404f4045006001c0000000002408b00340040004004658405e01207ae00400000000000000c04e0014000004801300242a006c000001e8009000000000040050238005547800000980004a1c001001c12c0018016008802a043c000002c002000db5d0028002014c00503a803d06c8006012400c0c9c046022c39d034000c0008001002c012001003a73b400a0000000000c03f004c00e00180020018047004c01c00080121338001003000000300
  | 56 => 0x2002c00400d000000dc000001803d0000002025000901891f9001000604680010000000000c09400040020008007000800e02d000f0000024086c13e0354008014c006000805205080250008019010803c0800040002c02f001409d0018027000c000000198e00040c400003b200ec0000004040008800000640000000018002800200000ca006c001000402c00300020038002000c0001cc0096014403e02b401503840d50418006002c00b0008000009809200680540fbc07600dc09b0014044000000303d400100540030108019007c0020000007001c03202ec00e01ec00000000010010001006401906f8000000003a00fc036046401900c0055012c0050474007008801700a21f000000090100007000c001003400b0034003008c04d00fc0490588004029c002008c005000800c00080020010001007000500081c5085c02500080b901b8005004c0530030000000001a0388003005c0040104003000c01f001403c000400a004804e007801a00fc00a00b0007008000500000100000000004802b0000005000800e0040001015c0050004002002c011001c005017804f014000000e000000040060648007015c01b000000305a4014001c040002c000000004c00a003a00009fd0014006000000106c007911880040058006000800300100000014009049c00101d004a000c03d406003e0068004018c01a006c002000001f00140300004009029414f001000000001780050001000000501101260040000000092303c400300040460040c0c0000056009c0060004001001001900380040008c6b0134000000c0220014001000000c015401c046407400bc03400f1538002c00800000750000039004400001180000004002001000e022409000080030020000001800b00442cb00000000150010002400700240010034006001c015669400e00d00080374011001800700cc000133c058000c0060004001004400b0008003000400d00080050004124001400f00cc00700100ae0028000020013f000000700180420009ca900080ae00000040070004005000000c40090750055000c00000080ad000806e007400b019c03e002c000000000100000000168000000004f0108001015c0000064000000002307a81d1024c0cf00e8030002000e19d0004000000b7c0801301e801f008801b040006c089c00802318cc008408f0008053000822c0014000000000800140290048038008401e0014008001000200580060000000001400c008000402cc0005f5400f0b18008001000000000030010074003802e0080018014c012000800b019800301bc00027c80030040018125153602cc02e003802e002400007ac00700ec0002f2800000b800e0008002002801300a40a6003c001004000a001800003180230044097000403000000050b2400e0
  | 57 => 0x7c0000074003009c1d800f0011002422500100aa003e23f00000010050009001809e000802000100030000000003c022002419501f000600d403900000ee1348016164c008072c02900740db01e803c003000219f401d0000028009401f000801300080940068080000400f000c00b02300000008000002833a0030005002c00e0028c36003c002000000103180090004197009c72c000554e003066d0068015000c01500000450024084051009f003c0390004035002800e00001e6033405900180000100000003003000066bc00a002500f4016001808900fc00900740000000004008400000200243fe400c0138003004c02800ac3ea002c003002c07100100c005000c00000044005800100000140004a2d01ec019001800a0318172004c002012800e01580100008007007800002b006100280120040036004c12100000020038000000000101140070050000000c00100fc000002802900003d0000808a00540190035f0000d800101640000004610210c04200cc0010001c060114000000000a0098016000c18b0090014000007d000400000082874d58001017808d09140280000001014c00a0000011009177600a117200fc008013c00903cc023004036200000090074022000007815bc00200006a4003c00400000b0017c00000040000070062001002a016006703c000000300bc029429900bc0000aa4044013c03d007409b001804a091c00400000740048002042c01500049ce001000a00300100034007001003415dc52800000140328040029404a008823e025401b0010057002c02e006400e03c800000700000030010000c0030000004000c00179340760050000005000c000c017001400200080010040007000000700000bf03e401800340040000014000842802b40030068006000c042001c0004b140fe00400080800007000000100a801a0000054001407f003c02f000800d000c0000a6c045000c0c902400040024010011000101f8000000011f000403b0038001005401200080000020001009c0a8000400000fc005003800d0d880100054
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x8846e72194430861fbaac810021179d764cc530e1ca6a948220655635845050b16b22c429c414b5c853d0d40c5aa93108610555731495110326b1aa4296819998b51cc540c5ac9310a60846d72191500c71ab08a3202819599453885108bae6300a4887165350441c8726b1ac52a243599c4539484087ae931ea090e56635445108332a92c210421179ce6508010a38eaa1a809864e53988400422ebb4a621643539c86094f418deeab10800870e5454a310c334294c019221179cf6590421c6ac8a88a21046e72d954344386ba0a699043c39ca5350e41e1ae42a2869955673182511023bbaac22006117dd95414d10d5284b00859061d5458e400c386a1aa4290870f9d0654c620a6ae8192a22061d6494f3184326a9ac421e831d5c66550f20a9eea9906520e4d5358b31c86c73a0a899065c95506294420c5ac8a9643084ce76d51320cb1b324a3988619358e6295131e48a8292828854d70d95320cb2629ac421a2187d516310910ca8a7308808852d7494f52442973a0c129061559c45494c20a3aeaa188710c6d72d953044266b96c998863555c7544c030e4a84214a22070e544c832cc746b2264190639598d51c8420ca8a630a808861d5358041102a7390c0a982117dd95314e41c9aa63126390e8d635084288332296c2982211b5c96510c20e1aeca9a842145c7654d1004296b98a4a12814b1d161d4910c38a931ca48870d54151320ca2fbb2a7a0e4395d8d5148430a9ae7b0ca420666525842084236b94cb988814b9cb6155020a3ce7b08a88852d72153404c2a7baa86a90878b95162cc430cd4c4b00a610f29525804110296ba4a4906210fdd954c84308bce7328422043f76550438870e320a6a922187992530cb41a5ae52a48298d1e7114d4350a96b90c72a061179ce62d5110caea6b08608854c7254d32d0237bb2a4200612d5c763508418baedaa66518f0d4310e52d0637bb2a428861335c06250d32a3ceaa18869052e72d91540423abb6a988021a659160cc73087ae832c640862e5458b410c34aa1cc221863475cc54906208beeab1e421051f74546318c2373b0a6a90214b5c85450f30c6aa8b08a91862d6494b310430f324a7a9021b89856008420b2ce3a9a87a149d7498d214c21fbb4a9908610fdd161d4d20a9eea990642067365545300c296ba6a6a90218b5506148020b8ce230264196a9425804284333294c3216638b9926294c31a5ae42a083084e572d9531c4317322c42a021535cb3154231c5aa8b10a818c3d76d50418c316326c4a8c61939d8534c821a9ae7290642051d731524148317aa2c598a21175cf6590910a5ae5b0aa998f465354621082a6392a6994812b9d854508218ece3b2e859868d43588430c30fb2a8621c411b9d8534c821d8a65308648846e7694910042a7390c9298810f1d16548110
  | 1 => 0x4284326a9ac4298218715163d05108dae4328860854d72d84534432cb1aa0280831bdd562d0430a98e4b22a790e5453984434428eb9ec8aa643c954a5110440aaae7312a2206365498632c8746b1ac5a0e81599c460948308deeca90a498d2d7414b424c22eb9eca21043c9151210851087ce832c650843d74d96310861eba4cb108611b5cb650c010acae3aa4421061e6498c53082863aa86a12658b9516210f30c5ac9296432072554549510c31b322c22a041479d06054c20c9aa6b10a7a052e72d5254cc6a7398c0a9021555c46094c42a6ae8192a21868d6398b4110787382a6a1085d154d5244010cb6e7b2a200855673992510822fbaac6200419598e6115020c6ca8b0e8790e3564947310c3162a2c5a1a659958a6114c10e18a829ea48862d5418940c829ab8ca820a6317dd9530c210cacc6a88801861c7650e5110f1632a8519281275d26388730e1ce929a6510d1d74cc5500c72729ac59886199d886155120a5ae5b0ca998e2e651505244317324a4196631d5c765d0d20a9ae4304a62051c73585540c386a9a84280858b99542905208eaea30a84087495394920082a639aa4990834b5c05450821acce3aa2a41853671d5143cca1eba0c0a9e430f9d0650c020a6ae8302a21846d72994311021f3a0c0a8c650f9da5450d20c3ca8b18841861d6494c2004326b1cc52a4631b1d95350920aaae3322a62161d6454f3104237bb2a5a0e6393d4d62cc710a3cec2a2869864e639885404346b2264190610fdd854cc510e1aa8a9c421064e6354850d0716b20c8292211b9c865d0c20a5ae829c649045f7614c424428f398c42a2211b5d662d0c21c9ac7290841861d6414f31c4386a9aa420881875926314810cc8a430a608870f6550d424cab338ea5290614b9d06054843c9cc7310a998d6472546218c237bb2a429421875954310c32c5aa8b108008596740c9310c70fb2a86218219958a6115030c3ecaa1e6520c3f76550414c69bb8ac0aa0654b9ca6055321c3ac8a98a190e2d6454b310c29b388c0aa065871906354910c9ca6312200843d7695052cc786aa264a8065c3dc94354843c9aca99064a064d5358853d0697388a8a1241a650d600c540c38a8b1e80985657199152cc716a12c1288851bdd95214841ce2c2a80a021f2554545200826ab88c099661879925314810a9ae72a48510d4d7298c5344326a9ac598c41595c63214520d1cc8b1e429070d53508420832b29cc220041a958a4110110a9ae7b0aa420596731094110717322c5a9821a358d421093287ce9b28658861e6550c434868eb98a921a419358d62d5010b48e2b02842161d5458c544830eb24a619081a950a6114042a5ae431ca998c3d74d96320871b2a4c3a90610fdd951d0040a9ae5298642043d74197214c32729cc4290818715163949109aae630243
  | 2 => 0xc9a9a219399662cc5308daea3026510e5963540500862f3b0a698a434b9d25450932c9ac7296431868d435884390346b226419481171cd61d4940acae331aa5a0e4d6358a54107173b0a8a14658799663d054087eecaa0810854e72d4d3250732392c3a98418799563d0540c9eca99065a04cd73d93218872729ac4286839358d521084087ae832c650851e7615143cc3a2a9aa3900414d9d26354440ca8e6b0ea99946d76d48218428eba0a618c211d5c465d0c20acce421aa220655639875488637baac4200619654e60084208ece332c841864d6594a310c316aa4c4180211b9db544c832c5ac8a96620846e76d4d52d0636bb6a7210439998a51d04308dceca92200862e64588544c30fb22a690881699c75450821d1ac6a10859046d76d522108332b14c32a26593195320c94187ce9b286410d2d72151404c327a9cc421a211b5db52d0510caac7288801061c5458f41c430eb24c629a41c594d5150040a6ae3a12a020d1d74d8653c870eb24a619483ca9515250040a6ae9a94a21858d74149320c6a6b90a921a61999962188110c6ee9b2a200843c765511004236bb4a5108431b9d8435484087aedaa0849846e72194438429d38682a8483539d46390932c9ac6290849865a63580540c6b338c86292211d9c665d0830ccacab168320d597014f32086a6392a8992619398e52d4341e1a87292a021e4d5398b41042a739ea5290814b5ca641523187ce832a621045c7694d100428e3a2c4a9881c55515354420a3ce7aa4a910c9d7318142906ab39cc9288611bdd562cc440ad2e0324a5a0e1d5498e420cb872a26428865aa59160c8720acae5aa2a21854d7215243cc22f398caa084153dd6424ca31c5ac8a90a598e355418542042b2b90c0a8861879516310821caecaa8a601868d4358843442b3390c128861475d26314d108eaeb30e8610f0d5350d42c832bb18c2aa2418b59152c8440a5ce9a9ca40864d639885408738a8ac1a08811b5da5314910c3ec831aa31051d7395340c430eaa2c62a42117dd563908328bae7b288408554735463190237396caa1e21175ce6588740caea630a608862d54588408c30eb2ca9188610f5d3654c110caca6b08800852d7218d540c236bacc5a0861c31d54350932a3ce6304a81061e5458c52042b338ea6a90818d5926114c208bae7324a2104cd7298e414c21fbb2a82a065539cb6154c40acae331aa421cae751894350b2729ac421841479d36354f21a58e4b0aa81045e739964108386b98a8a1465635cb5450f328bce632e85084e571d91320868f38ecaa18878bd536254d10aace6294a22062d62189540430eaa2c790821179cc6510d20c5cc8b10a818e4d5398a31086a6392a899063179cc6055321a9ce5b1aa60851e73181540821fbb0a990a219514d61d0910ccec4a8a621068d63508
  | 3 => 0x8d52d073187ae9b2840087175414e314430e2a4c610221c3d96544c8328d8e4b2a608864d63548400c32631ec4aa2418b5516215210cb4c6b00a610f0f7054d4210b2aa98c2a1821599c65450932c9ac7296a22052c74549428c2ab39ea4a88818b55162144308ecec2a2828862e64988538432a39ac2282658d9516108010caac730ea8104b574d8e21c421fbb2a82a6639554e6114420a6cecaa220085397015342086963a2a6a1043535cf5488420cccc4a8c801053674182510c236b90cb21821559cc609442087ae8302a598f154310e5110335b2ca4a0081c39c85450f308bae7314a20862d54988430cb34a92c0290631d1d56348510c5aa8b16831054c7254c5344364992c010a611d5c46550c20e1ca8994a2197475314a214422f398ca210219394e6210c4087ce9b2864085c672d05310c6a6392a9a9a2163dd1604c83287ce9314a39852d72d5254042b2b88c8292219514d6190910a3ce22a2879962f6454932102aab8ca618e818759263d48108bae7b28400861d6498c528434aa1cc221a21a950a618c84187ce832c640845f7654c50c8717324a4190819398d5210840a3ae9b0aa61064e6354b2110346b2264192218b1954210421b18e6b02842172652544411028f3a6c6a98211b5db5210110ae4e0192a21847b765405010a2fbb2a6298854b9c86315110d5284b0085a061f5498f214422e39acaa02414b5d0538cb20acae421ca21063465d914144316b20c9290614b9d95350842a98e4a9a642061f5498c4244297396c32a06117dda531082087eedaa0608847671d9642cc30f2a2c7a0c219658e6015021c68a930e648865453d8520442a6baa641908187592530c810c5ca8b16822043d76950530821f3a4c3a82658e1526010d10e1ce8292649846d72d94434868e3a22029a211d9c4650c8108eae3328861043c745865004296ba4c429221175cf65904218baeca98800863554584540832d29cc02888533dd932d4432a9ce6304a421c75711964308236392c3aa4619398e52144408bae6302a810d1d7418a5304326b1ea42122117dd95314b4187ce8302a610e1d64147314c2a6392a699021475ce5250a41c3ca931e420861e5498c4204333312c22a0410f5db54cc510a6ce3312a8196365498742cc62fbb2a629e81635ce615084287ae932c63906c463189100432632c86a1265555c66254c42a58e8b02a421d3671182540c272b90c098a21c354d435082199cec29a6410c6e72d96434423ab8cc7a8285665c35350f408b8eab1e428865563984540422eb9cc928821695d25288421878eab26428843f76550544c62eb9ecb20e41479d85350d428bce6302a910f4553189510830e2a2c7a0a63559ce6454420c5ec6a12a0214ce76149320c656ba0c0908430f1d16548630c5ac528e83a061d6458e52086a6b94
  | 4 => 0x5aa9316821849d7418132cc21f3a6ca9922187993530c91096ae23028520d2e71151428ca1ebb4a9908618d5506150e31c9cc7290841866562544518c327b1ec4aa2214d1d54390510a9ae4298630866652984400426ab98c0a0e218d99151cc440a3ce7320a88861e6550c438872ab1ac22a4211b9ca6394440c6ee8b08a0a1d1d72d954310ea6b9ca4196839558d51c84208beeab226418f0d72151434c22eb98c42a2418bd516295110c5aa9b128790cd571d93324c32a31ec2a92214b9d35354810a98ea994629070d4394a5110e1fbb2a82a6211e9c065d0c21c9ac729643086595358041042a7b9aa39044193595320c810cc8e4b0ea91943c74595328432b31ac3aa6651ddd95114640c3cc9a9e628862f5458b4148636bb087296838b5926294c31878e8b2e64886655298732cc68f398c0aa0659394d620c220ccaa530e65a0d717010d5110332b2cc598c638b553624401099ee4b0c6098656635445110387b8a86a90870f9d2650c020cc8a5b0a808854c7254c53502ab38ea729c858d98551d0240c5cc8a14a39046e72993504c726b1cc5aa02193d8d5250430c3ac928e639851d72151434c2a639aa8292211b5da52d0731a3ce7aa28710d2e74d49424430eaa4c7a86439314d62cc510c3ca9318841843f7559032cc732294c321221a999262cc5318dae431aa90862f64d89524421eba4c5a98431bdd95214a318beeab18400843f765505404317b2a8421663275cc605054087ce8312a198d1d70d954310f0e2a0c6a922193995320cb10a9ae129a6510e1e5498c520423ab8ecb216611b5cb6154c10d1a87310a221f0d72151430c637394c728e811b9c8655043087ce9b0aa61054d7394a210870fb26c6aa22159dc965c42108ece3316a0a1d547154d4348332b12a2200418dd516108110c5ac929642186366498653c430fb22a6988811b5cb6510d20c6ac230ca81951d70151430c6b3394c9288619394e6214341c5ca8b108710e4c5358b4144273baac3190438d9964110110c9cc7314a820e2e6494b311030eb24c629c21635c85350c41cacc7308a6104ad74181214821f3a6ca192211b5c86510010a9ae7b0aa5a0e2e6414b314423ab8ccaa18418b99152887408dceda9a401045f7654c5348636b96c2aa0218b990520c910c3ac9a9ca48866752185204429b3a0a7288414b9cb64553318eaea30a860854c75509320c733bb2a3900419598d61d5030cacc7308a81864d63948400423abacc220041475ce5450310c38caa1a849946f765485290f5930ac0208818b59152d44308bce7b0aa890c9d7318141d028fbaa8621c430f5d26294430c5ac9310a098e8d6358b4150386aa26419663879db6550c43c5ae4322a69058e73d854210b86a1886a90871edd95014332c9cca9906490e5653584300432bb2ca688021935
  | 5 => 0xe1d5458f41c8636bb6a418221711c5424ca318bae732a858845f7614c20442a6b94c7aa661471d54310530c5ca8b10879961e6498c54c8734b12a0280630fdd5640c810e8aa6312200866562584548432731aa5a86839694d6010c40a3ae8304a790e1d5458f418c333312a2180419554e611001087ae931ca3906c5638842044352b08c2a10858d59261d4e21878e8b28629068d635084250787398a8a10431b5d84394b318bce6322a010e8d6350842d028eb98a4a12819594d6114840c3cc8a9e422053970151430c63b3b6a688021535cb6194f41e18caa1a849953671d91540c2573b6a6a1085475d053cc120c5aa831286106555398752102e238a8699443c398d43548438daed296620862d6454b21902ab388c12984117dd95314e20a1ae62a28410d1d7315142c829a38aa82a24127dd1618c1308bce7326a58862e5498b510c29aba6a3288611b9c865d0c10d1a86b1087a0e2d64d4b214430e32a8620a61175d663c84208bce6302a5a0e6552984400c32ab1ca22006193d8e63d4910c3ecaa1a6520d6671181521022f3b0a698e21951cd61d5030c9ae7316a918e2c655082150297ba2a3904418759153cc610c6cc8b08a91061e6494c50c870fb20a6a92218b1974350932cacc6b0ea990e2e6458854cc3922a6a520a214b5d25210b3187aec2a6428851e73d53438861fbb2a82a2439358d52c861087ceb32642884ae7614d4210ab2b96a6a88818759053cc5218ece332c6420476711963204237390c8a9c218718d4354041c9ca6b16821051d7318954c863abacc3218438b9916294d21e48a8b08a48853474546418c30eb24a7a88411e5c065d0c218bee6b2c848861d6458e52c430eaa2c7a86430f5da5414c108deeca96622067365545401032731ac428283175cc645481087ee8b2a408868e6458b318c71baa2c32a2654b5cc5450920a92e029a6410e677654421082b2b8ea6108414d5c46095032c9ac729040084ad729912150256ba6c299241479cf6195321c5cc8a90a41843d7599032c86c6ba0a499261c3550434c832b1ae529a8720d4e73d4a520428eb9ea92a0219394d62cc420a3aeb2a2641962d6419252043162a2c5a02419354d62d0c42ac8e2a1aa4084757198b5050fa2298a490a21539c7544c832b8ce32126418e366454430082aab9ea8a8841c3552528c430c3acaa1887104d573d9221c43162a2c421a41875516314321c9aa6b106010656635845050a3bb8aca21a41555ce6494420c6cc8b08a50854e72d8553d061f3a4cb18841479d35394c20a5ae4302a998e1d6458c50486d338cc6a1085179ce65d0810b1aeb29a84217245414a3144346a1ac4218210f5d26394421acce421aa218536740c9511021f3a0c0a9a430f5d0654c620a5ae5a0aa020e4f654c832d070eaa2c7a08211d9c465cc810c
  | 6 => 0x30430eb24c629e438799153c8420c6ca8b0881185367414a510c296392c0aa065535ce520ca419ceeab0c8410f0d54d09320ca96baca89906553dd5644c832c9cc7a90848853674989510831b328a918a21c3191544c832b1ae9b0a641964d6218a53d0716b20a598a219554d61d48408dcec21aa5a0e1d6419153c878a2a0a698a2187592530cb41c3a8630aa421d2e72d525404386aa28699641595c74314910e8aa6a92a2204cd7398a41886a6b9ca599483175ce62d4141c5ecaa1085986555398430082b8b8086a8861395c7648ca2187aedaa06088669625405010727b2a641904153dc95314d10a6ce8192a21862d54588544c28f39ec8aa0211d9c66550c20a3ce7302a998e645298632443172a2c421e434d5c462d5110c9cc6994a39056671d4a52d0e8f398c0aa6639558e6194b10b1ae7aa2851953574d4651082c6ba0a699241535cc64948108beeca98a6a0e3664547310c3932a2a3108411bdc9654c110ec2a4a8a802062d6419252cc61eba4c5a82630f9d85450c31c9ac6a90800843d7498a51cc30fb20c6a9221c3551424c832c6ca8b08a41846e7615152cc6aab9ea32884153dd6434ca21c9aa7b126390e595358232082b3b8ac0a96638755263d07319aae2302879846f7558b41cc717322c42826393d95534802093ae9b0a6518cad74d8532086b2b8ea690041d254d5284010aace7312a21051d74cc5508c68e39ac3aa22147dcd5190640e1ca8992a01945d7398a519021fba2c3280654b5c854d0d30a9ae72948520f0e54549300c30f32a8621a219558d5190030acae421ca21851e7318a540c32aa9cc3a1e43335cb6150e31c6cc928e422054d72d4e5310237394caa1843a3591320c810cb6cb29a80206c5628c430c42a63aa86a12658755063440108ece331ea0a145e7399741082a73b0a6996419998961d50208bae730ea0a146d75d9232086b2b8ea6a90811ddd95114740a9ae6302a40863965552100423ab88c0a9e859354d6214e40aace3a9ca61047575d85420432731ac429c21539cb534cb10c3cc929ea190d4c7550d32c824f3b0a6a1e8117dd951cc03087ce9b2c6410d1d73153424832729cc421821539cc6454830a68e2aa68690654531852044346b24c5988638d1526108110c3cc8b18a810c6f76548525030f324a619081479d36354e21a6ce8302a2187177150e5110f4ca1ac021c210f9d66448540c6ac8a88a21868d4358b5110f1a2a2c399221c594d51104408eeeca88a21068d43588434c726a9ac421821179d85450d30c3ca931e421861c6550c438861ebb4a8180214d1d15190620ccca5308a021e2d5458843cc334a92c0208214d5c6635532187aed2a6420846e7299543c422eb9ec2a90811bddb5210110c74c8b00a818e4e634ca5108735294c02888795dd561cc831ab4e0314a79
  | 7 => 0x6992418dd906154d20c9ca6b1087a0e2e545884004296baca81084117dcd61d51208dce5b2e8788477755862004326b1aa4214638e5526008410c6ccbaa4828862d65508424c317b2aa4a0081175cc6055121b8ce62124210c6e76151428cb172a2c4218418d55360440108bae6302a990d2e7418252d068eba4a618c439954a6114830b52e990e409045e7614d320871ab22a398881d114f528c510e1ea6a1464a061d5458c400c26ab88c099063355da310c310c38c9b1aa48863654984400828eb84a8a1c639358d5208010d1a86b16a021c5d7319442c428f3a6c2a9881651c56050c43c3ca8b188010556711815310316b10c4aa0618b5516008420a9ce7b12a40861d64d4f314430eb24c6298219998a51cc440cacc728e822043d74d9731c8386a1886a96838759353cc521aaae6214a21062d6494b311030f3b0a8a1e61565c05490c31cccc428e62a061d65993318c68eba0a6990434b5c85410530c6eeab0e8420c5f7359521902a639ac8a9061995895190020b8ce72924210c3f74587538821eba6cb90e61535ca530c521a5ae831ca41870d7154d4210b33a92c2102219558d61d50208eeeca88a221e5753986324428eb90a8a1e6193d4d6294f10d1ac899065a0e2c64949100432ab1ac22a0418b1894254041c5ac9290a198f0d535854210b86a9cc0a10851b9cb65d0430a5ae9a98421045d75d8d210c364992c0194214b5d54210810d1ac8322641945d731942004286b90a6a1a81a358d42d444295eeca10a22154d7294f30c432b30aa3984619358d6215010c3ec8a9a65a0c777159543482b338ea529487179d85450f30c3ac8a98a69055571d9253c86a63aa84996618759053c8510d1a86b108690e4e63d4b214428e3a2c0a98858b592520cb30c58a8b1060885357118f54442363b4a488021539cc6494830d1ac6a10842043f7655054cca8eb9ec2aa6431bdd95214b10c3ac631aa990e1d6414c325032aa9ac3180218d1526110510c5aa9316821054d7218153102aa39ac8a88611ddd95114442caac7a8ca2a17145414e414429ab88c12a06193595320cb4187ae9b0aa40855573989510829aba0a6a8841359c7648c932c3cc8b18a91070d43549420c71b324c22a0411b5cb65d0f10e1ce6aa2641951f755854310f1aa8ac1208811b5d852d0510ccaa5308800854f75581320ca3b388cba18410f5d9540c8209acec29a638868d63508428cb0eaa4c6286434d9d353944208dae532c86086656294741082a6392c3a9a218b5954210831a3ce22a2869964e5358b51102b3b9286a8841c35513214032c9ac7296a1a0d2e7218254cc71caa2c120821551cd5114520e1ce4a9a842161d5498c2004326a9cc598881471d15350c20e1ce2a1aa421d1e73d5143c42e338ec7212658d5c664d4532cccc4b08a610476711974
  | 8 => 0xa6115010c38c8a9a200847970196430872ab2cc790c43961cf6544010a9ae629484a062d54588430c333312a3a0881479d02054c2087eed2a0400843c74596324421eba6c2a9061699c762d0d42a38eaa1886884e676cc52108726b1aa4210611b1d56210d10cccc4b08a90862d64148325031baa2c2206210f9d6644c540c9ca6b16630855571d8d53082a6b90c0a9e831b9d843948108deeca90a52051d74d4e530421e3b2a8a1a418b58862953318bce6310a89043e7615142c829b3a4c5288818b99252d4430d1cc8990a01943d74194214c2ccb80a8a18638b5965290440c9ea7316828870d5494c2108364b12c198e611bdd95214830c5ea8b168298e1d54984310c29cb80c42a2211d5da510c020c3ea8b1e428862e5498843cc637396ca21c21a3591320c921e1a87296a021e1d435825110f17b26c4aa2210fdd5640c8208dae532a87887465354a511023ab88cba1c41c350e60548438bae732c422045e7399621d02b2b8c64a80439358d6214141c5acb3264310d1e74d4d43886b2b8ea929061599c86054430a9ce4302a62066552586300430eb24a6184419554d6114c408bae63288210ccd73181420872bb9eca88021179cf6154810d1ac931e43905657598421082673b0a6996411b5db5308620d2a86b08a021e1d54d8d410c316b2cc5a0c834b5d35348020c3ca8b1e420845d7694f210830f324a6190211edd9501404399ae43028718cb57118143d028f3a0c429a21471cd54d0d20c9ac7316a81046d729944004346b1a8428885d294d524c030c9aa6b1087a162d52185401021fbb2a8218631b5da52d0440acae5a8ca21861d6318e540431aaa4c2200619358d5214940c9ac7296432052d74d8652cc70f324a7988214d5d35344010b1ce629a842153a7018e54cc78729a84216430f9d0650c910c9aa7314639052c7550d42482e4b86a6996410fdd5644c841c9aa6b04421062e6550842c42a7390c929e834b1c953508418dced2a28510e665258632d0637b92c128887335cf6150a218bee6b00a2a146e72181539076331cc5a0c831b5ca63d531087cebb0a86a051e741815310ac639286a16654b9c86395321a38e6aa0a89064d5398b310822f39ecba0c418b9926294d10c9aa6b14601070c5450e424ca9ab8ea92a0611b5d6621003087aecaa0601062d549872008317aa2c420221595c46054830e8a64194a22054c735493290296ba0c129021535cc6094810d1ac6a1084a070e73151424822eb9ccba0841d1d8d52440108ece232c840856471591520431ab2ac990c43b24c9600cb20a1ae72a28510d3571950414868eba4a621e434b9d06394810a9ce7aa26510c3e74197214c332b14a39884153dcd54d4910c3ac929e421062d64d4820c42a739ea499283555c46054f41ad0e090aa010f0e7154d4210aa63ac8
  | 9 => 0xae9314a21843d7418950cc64eb9cc910e818b9926214f21e28a8988628870d5494d200823ab88c0aa065331c96090d32a5ce22a2849945f7654c31487173b4a4a14838e15260d0510a5ae9294438852d74d8552cc6acb80c529e431bddb520c1108bae7b2e432064d5358853103a8a9aa3100411bdda521001087eecaa0a60845f76d4c404430e320c6a8c4117dd563c8440c5ea8b14a918d5471591530422fbaac321863875915314e10c3ca8b1e421858e72d854310ea6b90a8a9821559d95344010c6ac8b08a61076252545200821f3b0a8a0461539cb6114d108bce6328400843d74194200421f3b0a8a1463acd9060505108bce7316a810e2d6218a540422eb98ca908819998a61953108bce7324a210ccd73181424831db28c8880210fdd564cc420c3ca8b18a190c5e73189548421f3a0c0a966359dd951084208dce5b28600852d7298f544421eba4c7288411d9c66590c208dae5324a21863564584538838732286a9087475cc5490610e18e0a1aa421d577158153d0716b24a5a8663ca55260084208dcedaa2401058d74985320ca37bb2a428683279d85450c31aace2304a6216565398443d070eaa4c7208634b5ca5350e41c3cc8a98a190e4d63948420431b322c2282658759253cc440c3cc8b18a990d1e74d865310a96392a9a12610f9d06254c1087ae9328421854d7314832502a7396a729e83479d36194f2193ae63028220c5e76d4d5244326b1cc42a2618bd52620c110c3ac8a986410f145414e2144316aa2c5a9821175cf6510910d3286b0087a045e7399542c432aa9cc3a1e83171cd6548640d1ac8b166318f0d54585320ca37394c9a9a219c9456008420aaae7a94a22045f73595404428fbaa86218214b5c854d0f30ca8e6b08a0a1e1e6454e31d022f398caa1021c354e52d0040c3ac9318a79065563547410832b29ac3a16839adcb6544010ca8a6b08408843c76951100438638aa899065535cc5490b208e8e2b28849862e54588400c32aa9ec2990211b5cb65501108deeab0c6410c747559131442a639aa499081a358d62d04418bce732e422065561146304c3172a4c41802193d95320ca40c6ae2322a31063554984200432cb1cc029021175cf6588740a9ae598aa018c75715942004364b1ac190e414b5d65448020a3cec2a287996a9425802150236392ca98c819358e6215232a3ae62a0868861d5458c4084394b80a8a1043475ce5410710a38e8b0aa6206656298453882373b0a6992419598d6114a1087aeb320601070d7214d4350326a9cc4288811b5ca64d4f10c9cc6b16a80863454984304428f39ec8aa643275d26348730ccaa4b08a021f2542109510830eaa2c62a0211b5c86510530a9ae7316a99055571d53300c2373aec4a1a43559c75494c20c3ac8a98601065453984314430f32a8621e219998
  | 10 => 0x61c54d8d524438d380a8a1863999496190b31aace62a2a2107197015143cc38a29a8220a2117dd95314e109cae5b24638847571181548cb16aa2c42a661555cc42944308dce531ca2086656298754ccb33294c2288814b5d66350842e1aa6a12a02152c7454e4248362994c228065d1949518c430c3cc931ea40847576944400c386aa265280651b5d66210f418eee2b2a868851e7318254cc63bbb2a22888187d516394910a9eea99065a0e1d5458c40082abb8aa818c6117dd953c8440cd4a4b0042087155354740102a639aa499021475d36354c20a72e02a28410f0d43508514cb862a264192219358c52101108daeda9041886355498440082a6b98a8a10438b95162d0721e8aa528c621846d7298e510430f3228728e654d5d26254430e62a8a8a401055571188534429b38ea92a665cc95151500408baeb3188590e8d43185424ca96b94a9a06219958a61d4c108e8eab08648854e721915308333312a3a08618b5526214810a6ae32a0839052d7215241842ab388c1298814d5d35254430cc8c5b0aa88847571d96434831b2a4c2298410f5d065cca10cacc7a8e829061c5498f4144317b2a8421061a399162cc5308eaebb0a860843d74194324422eb9cca20021475d06214d10aaae3322a790e4c6318954443172a4c429061d194e5254440ccaa5b0a640861c64d8d53482abb8ac0a9e438b95162cc721aace6102a21045d7319442442373acc5a0a218b15262cc510a6ce3aa6879945e73d9442842973b0a8a164193595528c430e2ca8a8c621864c63549410c31aaa4c22a0418b551620c010c3aa8b18859045e73d9442082acb80c829a219958a51cc430caac7308a40872464549511022fbb2a629e83539da534ca21a6ae3b10a88861e6550e414c22ebb4a62104187d526394910c9aa7310a42068d6350842cca1eba0c0a98431b9ca658c740cb2a6b00a22168e644cb510cb0eb2462282631d9db5254430d1cc8b1e4310ccd7318121c82373b6a8996418d59251c8420c5cc8b14a68845f7694f4104354a12c020a411d9c46550810c6aa9b0a840864c63549420c266b96c2a1a61a398d42d4042caea6b0ca6a143e74994210c326b1ca5908619358e5210a31c74a8b008410665525845290327a9cc529a214d5c454d0230a3ce6304a81964e5358843d032729cc5a88819354d62d04108baed29885a0c77765445150a1f3a0c4a9c21745c3534c710a9ae52a0a68864c5358b31c4387b22a8990651b5d843d4910a5eeab02842172554546210821ebb0a818221479cc60950108dae4322a60846d7218153d0732b14a3a08618d550614c810c9ca7316822062c645491004316aa2c5a88618755163d4810a3ae8298868864e6358854cc636b96c2a9881595cb54c40108beeca98a78864d5358b3104332b12a228861a358d4210a31a6
  | 11 => 0x832ca9ac010821719c76290d32a9ce5a9ca60845e73d97410828eba0a618a418d99161d4c20c9ac6a96822045e73d972110326b18a4102211b5da538c83287eecaa0838851e73985540ca37bb2a428887535c85350d40c9ac7310a40852e7218d54cc70eb18a3a0a811b5c86355010c3cc8a98a21064e6354b41cc70f32a8621a83871935354910ccee4b08a0a154c72553324c346b1a8421461539cf61948308bce6328858851d740415304296392a8a1021c350c4354b31d2ac9188618845e7319150c870eb20c8a98415a5c0538c821a3ce9a9a878864d53d81200838638a86a9087475cc5410d20c5ca8b16621043d74181520c72b31ac2298419654d60d0c40c5ac829042a064e6358a544421fbb2a8214639998b51d0530e8ca6a92200846e72d974344326a9ac5a86831e1d56010d10a6ae2318a88864e6358a541072731ac4298211b5ca6494410a38e6aa2861052e74d855210f86aa4a498061c3d5053d4910c9cc6b16a99962d5498843cc716b24a590821275d3614c93087ae931ca31064d63548420430f2a2c7a0821339d46250d32a38e6b12a81861e5458c42c86a6b94a721c838d5915114620a5ae4302a80870d539494010237b92cb21a219598e51c84208dcebb1e429070d5354a4110334a92c1a10819354e62100208ece2302a7a162e65d50524431cb24c0290218b95162d04208bae7328840863776547401021eba6ca992219998a61150208beec29e82885567310a510830eb2ca720881175d953c841087cec2a2a68864e76149324c32aa9ac3200219518f6155120b4ae9294438852d72152418c22f3b6a899065991486150110c9ac528e639852f7550e5210e1fbb2a819663875915314c21c9aa7b128790d6471551324830eb2ac998c63879954390730c3ac929e620854c76551320ca36bacc4218819914a6110110e28c8a9ca22061d6494c51082963a2a429221c31d95350842c9aa6b10a70851e73189540c23a3aac3a1a21939db654c832c5ced2a28510e2e54d891004387aa28699443335ca6390730dc242b004388559708c4504c786a1aa4a1661c350e52144438deeca968208656658c6304428f3b0a6a1a81175cc6454021cd2a5300621870e73149425030fb2aa6a10850fdd954102308dced29241887165454e510821eba6ca19041699c46050842e1aa6a14a02162d6550842cc697394c82a2219958a61d5030a98ea992609064c63d8951902a6b98a510a810f5d060546328bae7b0aa81051d7015143ccb17b20c4a9a211b9ca61d4143a3ce7aa2868851c7454d43c8272b88c0a10434b5ca5410521c3ac8324a61064e6354b511038aa9cc220881179d66310910c6ac8a8e6218557714c8514c21f3a6cb192211b1c96510d10e4aa9288421045d739925108786a1ac0a90878d5506150a21c3ca8b1ea210
  | 12 => 0x2126387d9264d4d10c9ac6a96432068d6318d4210a3ab88ca21841c350d5254043c3ca831a200846d72d9731d031b324c229c414b5d2524ca31a58e4aa2850843d7695032082a639aa899241c3551528c430c3ac8a98642064e6394b210428eba4a621c43c350d524cb40c5aa8b10811063654987530823ab88ca990810f5da5490040c3ac8a9e420851f7550c430822eb9ccaa10218795163d0430c38c8a9a422045d73d96420870e32a86990839398e62d501087ce832a64084b5769044044297396c8aa4630fdd95415110c76caaa22008639659521004317324c42a663555c75494c20c98c4992a018e4e63548420c2a6b94c7aa063655c46050c43c6aa9308600864e6354b210c2373b0a490e21715c4604c832e4aa928a4010639545803104394b80a8a1641595c84354440c6ac9308a40854d7294c329072b31cc2290214d5d26394420e2a8621aa21066552586400431aaa4c321e63c6552534c030a58e4a9a85a070f6554d4210a1fbaac8180418b1d94254042d1ac6a108420d4d73951428861f3a0c6a94211b5da52cc4308daeb310860847b765405050a973a8c5a1a850f5d06354321b1ae929a6510c3e741943284346b2487992658799153d4321c9ea6b14a68861f6550c434821f3a0c6a86438b5926214c20c5cc9a90608852c7255142cc72ab2ca3188611d9c46510e209cce5b0a8710e6662147414c2373acc421a214b5d0605483099ce231a849968d43d81424ca3a3aac321a21c35d94354843aace7a8ca3a146f7654852442aab8ec829a211d9c66510c20a3ce9b08a68854d75109320cb27a9ac421a21879d85350d40c5aa530e802051d7418a5308326b1cc52a6219354c6250420b1ae530a8621e4e5398b410432a31ec2aa221555cc40544408daedaa0431053571151408c346b1cc5a0c839558d5114620a5ee4b0ea88852d74948420c21f3a6ca180211ddd95114620caea7308808870d5350b5110ae338cc89906517dd56390030c5aa8b16821862d64948320c716aa2c421841395c46050920a68e8992a22046f72594315021eba6ca98a43179da534c610e92a6b00421043f765505408392aa4a588021535cc64548108dce432e62a064d63d4b21443a5b8264a80651b9ca651001087cea32264a0c5c7359442442b3394c6a8861175d85310910a58eaa168090725529464110326b1aa429481555cf54c4010e1aa6a1265a062e64988540c3a2298a508221879916394b1087eec2a0608843e7498e51087a4b80a699641879516310820acee2b02a5a0d657214e51103273b0a6996419358d62152108deecaa4649047475586424428f388a8a1e61531c96454c20c9ac72908598d5673181511022eb9eca21421479d76450d32c5cc9310a098c6f72587535030faa2c7a0a212b5d363c8720a3ae8102a61047676d4d51
  | 13 => 0x320c840c3cec2a2869945e7399641c822ebacc6200211b5d6620c010c5aa8b16621854d74d95320cb2729ac4200419a1cb6544010d1a86b10870864c535884348316a92c020881a650d6014443c5ec8a92422047776544510c326a9ac598c210f5d664080108baeb31e4220665611865210e36b94c728c81175ce6294440e1aa8990640861f5498c2044236b96c2a9e818d5526190b31c3aa931e82085667298e510832731ea5292211d9d8534c710c9ca6b1086204ad74d8532887162a4c42022153dc95414d10cd4a4b00842068d6458f21c830f32cc998a61555c4538c620c5ac8a906520e4d6314820c430fb26c6a8c41c354d43509208bae7328801062d54588430cb862a6a7a92210f9d36508010d1ac8990651062d64884504861fbb2a82a421535ca530c710a3ce9a9ca710e1d6414c3150237b92caa0221355c764ccb30c6ac230aa81963554984530829b38ea9a1465c39d15350842a3ce9a9ca60846f755912108656b80c4a1a85539c86054c42c5aa8b16830870d5350842c870f322c7292218b55262cc4108eae3328841866662587540c21eba6cb98c418d5916114e1087eecaa0a01961e5498c2004392a10a220a4199949610801087ae831aa010e8e6358b415032aa9ac220041479cc629501087ced2a2200865563544400c22f3b0a6a1c438d15261d0910caca7308a22054e721825310b16b22a5908610f5db5410d20c6ca8b08811047671997430830f324c6294214d5d03294440a9ee4a8e611856672d4d511022fbb2a6216438b151621052087ce9b2a658843e7498f5048746a1ac421c419598d6114e20e2aa8a9e200851c7454d43c86373aec2a1241355cf6548710c3aa8b188518c3e74d973244316b22c4298218d5526114830c5cc8b10a91864d6394b410c327b14c5a9a214b5c25450a21a38e8b0ea68850d739494290726b1aa590881a9590414842187eecaa0811061f64d8d5244296ba6c2a90611edd95014021c98a6b10808864f644c9500cb2b31cc32a621959945390510a5ae52a2818851e73d52540422fbaac8988631e9c065108108dae431aa020c6e7614d5210296ba4a629221c3551424c831c3cc931ca48845d7694c50d06973a0c729683559ce6294440e1ae0aa2641954d73148324432b318a3a0a411d9c46510c20d5285300a22162d645885348236b90c02a2214b5d01054810c6ac928e421851e73d85540c22f39ec2a96811b5da5214043c5aa9314839045d7654f4104316320c4a9a21c350f60548438dce531ca32045d73189501072731ca4210218b9516210621d18caa1a849951d731514248237bb2a3900419594e6114840c6aa930ea41865553986300421fba2c3280210fdd95414f21c3aa8b18841843d7419731482d338ea8a1465a550c614ca418dce4322a018d2d72990544c66a38ac6
  | 14 => 0xe7aa4a40852e7218e540428eb9cc82a2218b552621501087ee8b2a431866462185544c32731aa42908187992530c020e1aa8a1a641953671182540cb16aa2c5a08410fdd8540c910caaa6b08400870d4354a5110f0eaa2c7a88419998961d5321ccaa530e8598e4d6354b50d070fb2ca6a1085d154d5108420ccaa4b08a41852e72d5142443273b4a699443c3551320cb21c58caa10829043f7655321082b2b94c9288614b5d36114910da6c6302628862e64948510c30f324c7290431bdd56210f31cacc6b0ea998e6765545200830faa4c72a2218795163144208dce432c870861e5498c42c871a3b2a2a00819a54a600c410e4aa8a96200846f7694b310422ebb6a621a41c5552518c430d1ac6a108410f4553947200831caa2c1218618718d4354342caaa6b08601063671596411030eaa4c7a0e430fdd95415231a9ae7b08a48843d741895304286b90a8a1a611edd9501423293ae732243a052f7558d4210b2629cc418221395c4604cb20a9ae7296418862d5498854cc696ba0a59042127dd943144439aae7b2a838870e535095010ab8b8064a88419a5496014841ccaa530e85a0e3454586324428fba2a398461a350d6210f20c5cc8a96a198c6e72180534432731cc4290219a14a6010910e4a8428842a051d75951300c2a6b96a9188619598e51c8430ca8cbb1a62885657298d510c21f3a0ca19621c31c1544c832e1ea7a1a849045e73d855408236bb2a5a08210f1d5640c9108beeca98a6a15557314a5110326b1aa4290212b5d2628c720c3acaaa4621861e6414c304432aa9ac310021399d85248710b2ee2b028621da5729524110696392a82a261725cf21c8120c68a8b0e8490e1d54d89320ca2ebacc6210410f9d06254031c9aa7b12821051e73189540830eaa0c6a0861179cc6055121ccaa530c600861f5418d524430e31a86a9681595c84354430caca6b08611065476545300c21f3a0ca9942135dd561cc831ad2e02a48410c6e7299631102963aa84a0241c55515394420e2a862888298747714ca510ca963a220292218b99352949108dced292430854d7294e329072ab2ac790c430fdd95410b20e4ae22a6a48862d6454b218c316b22a590821c35d9544c83287aeb320641852e7498152d070ebaecaa18874b5d2534ca21cb2c6b00a810f0e72951438c717b26c4a9a211bdd95214a30a58e8a90a49866562544300823bbb2a220041175cf6154810c5ac9310a40865a535805110b33a92c329287a359162cc530e4aa930842105547550e314422f398c8a942187591530c820c3aa831a841845f7654f410426ab98c090a21875935394d10c98a6b166290c5f735974244316a10c2a8085359d8514c7308dee4b0ca121e4d6594e21082a6b96a8a982155dc56054c42c9cc6b10a99865563984540822fbaac321e6193595
  | 15 => 0x4d531852008316326c4a9a218b5906454830ae2e0212a22063561d80544424eba0c098a61c394d4294442c6aa930ea61054d7298c53c428f3a6c2a9885435cc5250940c3cc929ea21064d621895304334b12c02a0638795263c8420c9cc6b10a818e2d64988530872db2aa6900411bdda52d04308dae5b2e868861e5458f4110237bb2a410e21951cf65440108bae7b2a408861e5498c420822ebb4a621081479cf6195030c9cc72908598d2c72551424c332292c3212214b9d06054810d1ac6a108490665525862004236b94cba086187592530c821a58e8b1aa42064d631484244333b92c228265435cc5450b20b1ae8302641954e72d4e531031b2a4c210021c354d42d40428deeca96821851d7550c4304333312c3a9e434b1d5421093087ce8300a68843f765503208286baca8990651d9c46055132a38eaa18869064c5358831483862a0a6292211b9c860551318daebb12861066562584538422eb9cc9a96214b5d32154221a3ee8880a68861e6458c540422fbb2a628085875516310820c3ea8b1ca890c6d72181544c6ab3988528861535c86454c10a9ae629641084e671d93324cb98aa4a288021275ce64485408eceda92a22052e74d8552cc726a9cc421881179d85450f32e1aa730a8421477755864004236bb4a4286831e9c06550831a3ce6304a990e4f631895344327b2a6419083a55846150c4396ae23028620d4d7219253042aab8cc4a9e838e552600c430cc8e4b08a0994b57118143502a6392c0a9885175cf65505218bce7326a090ccc73582424caaab98c0a88818d59261d4c20aaae3aa0621874453149414422f39eca90221475d06094c10c9cc6a90840846f72587548c32731aa590821a358d42109308bce7b28800847571d97434868f3a0c4a98219358e5210840a5cec29284a065553984531038ab88a829a219654e6010440a58e4aa28418d1d7494c314869bb8ac0aa643875915314810e1ea9212649868d6490a324cb46b2264194218d99151c84208dae5b2e839870c6354d4210b26b1ea5a0a218b592520cb41e1aa630a842146d72992518c32bb1aa2a08611bdd852101108baeda98630872b705095010a9b3a0a4a88618d1516110110a3aeb30a8621c6d7298f544872ab2ac7a0c838b59262d4c10c3ccaa1c62a0637755874310636bb0a420221c9d516114910aa8eca9a200862e6494832d07872a2a59806195d8c61551308eee2b2a6488726525464110296ba4c7a9221175da5414d10a6ae8302a21051d7318a54c862eb98ca214215c9c04254440c9ac7310a90870e739514288786b90a8a1e6517dd95314d408f4e032864084e57688420c4326b1ca4286838b55162cc420c5ca93168398ccd72181434c326b1ea5292218b5526214c10cccc4b0ea61046f7654851102a6b94a6190211b9ca6590430a9a
  | 16 => 0xc30f328a829a210f5d954c84108eae3b2c8690c5c735964244386a1aa4a88878b951620c010a3ae829e6410d6571d51520c28eba0a621a414ddd95110440e88a690842885667299151083172a4c5a8663539cb6194c428beeca98400861d431855010e8eb84a6a1c83875926314c20c5ac8322a40845d7694f411032ab1ca3908418b5526210010c9cca298a48854d70949328c63bbaac2180418e5516008420a9ee6a88431064f63549420c2aab9ea9288418b5935294a31c3ccab26629864e6354852042aab9884a88811d9c66550f20e8a64192a21070d74149324c333314c329e2199d4a61cc910c6ca930e8790e8d6350842c870f3228728e61695c6635084287ae931ea48864d539884308237bb6a598a21c354e5210440cccc4a8e621045e73d9442c432729ac5a8683c354d4210b41c6ca8b08810861d6550c438431a3a2c2282858ed506050510a5aeb21a842167261580540868e39ac0aa0654b5c86315110e1a8621aa42062c5458b4148786a9a84a8885551cd518c62087eeab206590e3554984500cb16b22a4290211b9c865d0530a9aeb322641943d74997310831bb28c888021559c754cca3287ae9b28648862e6550a21d022f398ca212210f1d161d4d20c6aa930c800853674d46510829b3a040a8841c3d965350842a5ae829264984b574d8e2144237b92c3280218795163d4810c9ea6b166290d2e74d86520c22eb9ccba102117dd95314c418ecebb0a8690d1c7550e414c2c6b98a4a108393d4d62d0510ccac530ca7884757695241107932a4a5288611bdd562d04408bae632c85084b57199132d03273b4a4994638755163d0620a9ae7310a58861e5458c42c821e3a2ca10a61635cc5450b20a5ee8a90a48861c5498c40443273b6a8990659358851cc530b1ae5a9a87a147571195438822fbb2a621683c35ce5450a21e8ca4a8a601870e7414d324830eb1ca3a0e8193d4d62cc510c3ac8a98659074552945300c297b92a3a04819394d6210c108bce732c422070d5454e5204237390ca218416a5c35250b40ccee5b2a200862f64d89518c28eb80a6a1a85d154a610c430acce5a8ca21854d73152424829aba4c6a886199589518c020acae3a9c421058f7050d424ca2eb9cc5aa043d454d519004087ce9328621070e7414d32c822eb9cca108819958a51100208eeeab088010665529845010e2eb98c8a86430f9d3654811087ae9b286410d2e74d49424c61f3a4c728c419594e6110010c9aa4b04621866762185544c21eba0ca18041599c84394440c5ca8b16a60846e72994410c332a92c2100219c5855014032b92e029a6410e69529805110f1baa4c2102218e1d36544010cc8a4b0c8588745535452008272b96caa0e21879905394910ccacb28c42104b5719913250326b1aa428881175da5310020a9aea21a64196
  | 17 => 0x1887635cf6150842d52c4b0683a04cf735862048296ba6a710841171cd61d512095ae83126190477765445148316392c8292614b5ca5410710cc8e4b0ea81071553544411030eaa2c628841c3551434c821ccca530c65a0e3654584530830eaa2c62106599589511444087ce8302a418f265250441cc61fbb6a998a21479cc6295020b2ce72a28220e6562547411023bbb2a228e851bdc965d0d10c5aa9314601043d74181534872631ec4a9221c3dd55350842e48a8292628849e7615143cca2fbb2a62004133dd93214032acae2302a421c3e741943004332b12a3988818b55262d4430a3ae7a0aa020e3565993318c666b94c7208638bd91524c440a9ce5aa2a60846c72587535023c382caa1a434b5cb6195030c5cc8a96a21871553545401030f3b0a8a1e659318c6254640a9ae4324a62045e731815210637bb2a4292879554d6114840878e8b0ca19943d74d97324421eba0ca994210f9d365c87308bae632e42a047671994420c2a7390c129e439358f5210930e92a5300621854e731815210f1b322c3a9e438bd954210832a9ae6302a5a0d1d7494e31c423d380cb21843435c85450f30a9ce6304a598e2f65508420c697396a92a061555d6610c4308deeca9c849055673d4a5110346b1a8421663535d6614c832c9cc6a94801846e72191530429ab88a820c618bd925244010a3ce7b0ca81947b7654050d0b8b2a4a6a8841a3591320cb20c9cc7a904088666629443008297ba2a210c414d5c46055030c9ca6b10a220474715954348286ba0a699043179cc6590a10a5ee0a9a842164e5358b41102a6b9ea8a90214b1d15250b31a6ce3aa4a81056472544515030faa2c7a0a43599d95244010a9ae4304a608656635474108335312c02a043171cd6550620c5ac8a9065a0c3d74195218c23db82caa1a431bddb52d0510a5ce930aa421c5e7694d434828eb94a6a1c838d1936154d20d1a86b1087a064f654c8321031ab22a218041c51516114d10c5aa8312200861f64d4d52443873a4a4994631ddd951147308eceda9aa2206565358643c8746a1ac421a831b9c8605503196eeab0e8420d3476551100428eb9ca820c438b550624c420cc8eca8a401061d5498c420c317aa2c4182210f9d3650ca1087ee8b28648862e549885204332a8ac110841531cd524ca10a6ee2a10a2a046d7298f54442a73b0a699043339d46350932e2ca6a8c822046d7610e520431a2a2c21822187952631442093ae7b0a85a0665625845050f1b2a4c2216432bdd942140428bae7b0aa80849d74181320c68f3aec6a1a814b5d25210a318dce5b2e831862d6498b530831b324a218041c5951514c030c3cec29a86a161d5498f210c2963a2a4a10638b59562d0641e8aa6314a21051e741825310b35314c02a0638d191514c440c3ac631aa81047676151510
  | 18 => 0x20c220a3ae7aa4a990d3574d4d510823cb80caa1063b4985600c430aaae6212a2186375498430443162a4c421a219354d62d4440c3aa931e421043f76950300822ebb2a6210410fdd95415021c38caa1e64a070d53d814210b172a2c42186517dd9530cb20ccac5308a91045e7318052442d238a86a1443a359132d4032caeeab0c8618e736594540102aab88a8a9841a950a61108418dcebb26429061d641915304236bb087290818b9516210f31878eab26628854e7395352443a2a92a318861179cf65108108bce7328800861c6494d10042ab388c0a9841595cb53944408eaed2944210e2d549842108316aa0c4a0e438bd906255130a9ae52a48718e4d535884004386aa2a6a902127dd943d4443c6ca93086008567714c8514822f398c0a94831b9db5354840c6aa8b08a41865953582310422eb9ecaa12219958a61d5010a5ae5b22a998e3664947311029b3a6a3288618d59564cc631a9ae1aa2641951d7550c43c8657ba2c3102411edd950142418dceda9aa40852d7218254cc65b3b084a088387d91534401096ae9b2a438845d73d94420829b3a06528881479d06254c40c5ac8a906598e8d644c832d029b38cc6aa065275ce6488540c5cc9290600845f7654c53102963ae86a1043555cf5194440a6ce3b22a810534745895110327b1ec4a9a21175cf65d0910b1ae8292659847571181544ca1ebb4a829e43175cf6155121ca8a730e648862e65508428c72c29cc021a21595c64214520c9aca9906420c3e7418d520430f322c62902196d955350040c5aa93168398e37745845050a1f3b4a8a12611bdd95210010d1ac6a16a0215b170d4541d028f39ec2aa065c3551524c0308daeb316822046e75d92324828f3a020a98211b9c86510f10a5ae4aa0841070e5350b5010b86aa084990659358d6215230c98caa1a84995957494e31c4332316c2a9a211b9ca6510c108bee6b2a809052e72d5142c4237390ca21821b14c961140328b8e6b0ca00870f5490d3248316b20a590a211b9c86510d10c6aa8b088008656639845404332b12a398861a398d62d0441e1a8621ca41862d6494b21082a7390c829a219358e52c84108bae732c840864d6218a530438caa4c0188618b9d46250d42e1aa930a64197453214431482acb80c929e834b5d0534c9208ece232a642052d72152414c2973a0c0a9683875536344010e48a8294828863454d8530442b338ea729081355cc6050510d2ac7208818864d6354b210c28e3a2a721a41635c85350d408f4ed28a200875253545300c333312c2282871edd9501434387ae8302a710d1e74951434ca1eba0ca1962163dcd6050842e18a6a10848861e6454c321026ab9ec910a210f5d0650c520c9ca6b16622045e73d9420042973a0c1290218799153cc440ccac4a8e821849d73991315022ebb4a92
  | 19 => 0x8b1881184ae7615142c838638aa6a1085c350c43d4910e2ca8a9e200864e5358b310421fba2ca10a618d55261880108bce7b2c8410d1c7454d430868e39ac4aa6634b5d05210930c5cc9316a60862f64549100426ab8ec99906353dd5320c810c5ccab1682a064d6358a548c6aa3aa62982219998951100208bce6328801045d75982430c72bb18c2a9a418b195424c940c3cc8b1ca410e8d644c8325061fbb2a8210430f9d76150940a9ae5aa2601845f735875250386aa6c0990651b9cb6510c10aa8e6a12a21854d72152530432ab1ca3a0841175da538c832a5ce8082a40862e6598b415028f3a0c4a98419314d62cc120c9ca6b16820843d7498a5104387bb286a90870f5d7644c840aaae2304a7a0e2d5498b50cc70f322a6180214d5c75495020a3ae72a4838868d6358b41906a7b92a218c614b9cb619503287aeb3266390c9d73d85425032b38acb18861539db544c832b1ae62a28410f0d5494b300c346a1cc4280878b5925208210c9cc6296428855970188534432aa98c2a10218b9925214331b52e1aa2859061e6550c434c72632a6410a61595cb5194440a5ce5b0ca998f195454d100430eaa6c6a1061535d6544c832c76cbb22200866962980540422f39ecba0e411e1d5600c910caca73086590c5c735875488296ba6a52966399d4a61081108dce432c861052c725875444296b80a8a1265171cd6508540c9ac6b14a8885b170d5141c42c7baa872908717dd95314e42c3aa9318800843d74181510ca1f3acc819221b158a310c110d1cc8b16639868d435884350386aa4a7108410fdd1654ca10a58eaa10829043f7655052cc63dbb2a0282638759353c8510aa8e6a88a2a052e7418c52442973a060a90614d9d35194732c9ac5188a098d1e73d86540821fbb4a990821c9553624401087aed2a064084ad7418132c822e39aca9022193d4d620c310d1a86b10862043e74d97318831db2ca8880214b1d15250b30a5ce431aa80862d6494b211028f3a0c529821535c85450d3099ae63028510e4e6394b211031ab22a390881475d36154f21c5cc8a96422056472544514c386a1aa5a1463531d5434c821c3cc8a98641046d721964384296b94a7a1c838d5516110230e1ca6a10841047671195329030f322a7988418b591521483187ae9316a6884cd72d8543cc326b2ac598c631b9c86054743a3ae9298860864e639484210297390c72a6631b9c8655063087ce932e621070e5454f200822eb9ccb908811b5c86054443a98ea9966090566711825210332b14a2200610fdd9541533087ce9b2a6290c7471595329030eaa4c621041875526390030c9cca99442985357414e51082b2b88c1290878d150614c110a9ae7326a48870e7650d5210e9d380c52a6431bdd95214930aaae229a611051d7498c538878a2a6a720a219354d6
  | 20 => 0xe6550a41c8237b92c3286878b991520c010d2cc931e4310d29701514208746b226419081635cc5250b40a3ae7b0aa81046d721953190296b94a920a438b553624c420aace7a8ca21053575951100428f3a4c2a98859598e61d5020c3ac8a9e6220475711815390a1e3a2ca98241ca55152440108bce730ea0a161d5458c4208697394c2aa0658bd5262951109aaed188608843d74994200432ab1cc3aa021d194d51c8020d1ac6a10858845d739964108338b0aa028085c3d51320c910c5cc8b10a998e4d539884310a8eba4a499463b158c314842187ae9314a31870f6354d4210b26b1aa590c614d5c46055321a6ee2a98832066472d9510042ab38cc4a98850f5d36154c20a9ce229a6590536711815408346b2264192810f5d06154032c3cc9318a40843d76950300834731a84288854b9cb6155032c3ea8b1ca910e1f5498f414423ab88ca21c419398d52d0440c9ac6a9642085a671d0d420869bba264a88811b5d66210010c5ca8b10801070e544c8320434a320c6880218b99252c8430a6ce3aa2851945e7694d318832b31aa3908810f9d854508218dae532a860845d73d9721d028f398c4aa021479da5450e31a3ae72a08290e2e5458850cc61f3b6a8a92214b5d0534cb20d1ac931e4210d4e76949328c657b92c320281a358f43d0942a3ae7b0ca990e6452584204423ab8ccba184187591530ca41a9ae429c62a07155494d510822ebb6a6186218b591520cb308dce531ea0a0c5d739935244297390c12a0654b9c86055331c5ea9316628866652984510c24eba6c29966195dd951cc030a5eeaa10840870e72551320cb16b22a4104214b5c85490930c5aa9b128390d2c72551428c31ab22a228c6153dcd541491087eecaa0a89946f7558843d071b322a2288418b5516210c31d18c7a1a849952c7458d52d070ea9ac120881c91505288510e88a6b08a48851d74189530422f3b4a698621175da5314840c5ac8a90a41853571d91540c237394cb20e618d9526110f3187ae9b28650846e72d85531021fbb2a8190211ddd95114432c9cc629084886376555110042b238aa721241871516310530c3ca931e82085d0704c5304422f398ca208431b5c86154043d4ac910841887445314a314423cb80ca990834b1d54350b20e1aa8a1a649062e5498b310434731a8428085875526314420c5ac8296438854d7315142c821ebb2a998841559c75394c40c9aa7310600851e75d8d4350b87398a8a16418d95161d0b31aace32a286994cd72181314c32a31aa2a08614d5d020544208bae632e840861d63904505078aaa4a2980619558e51c8430c6aa8b08600863654984510c333baac3190439398e6215321ac8ea90e408846e721815110f8aaa4c2188610f9d263d4b10b2ae33128621d2e741825210e2f39ecaa02211edd95014242c3ca
  | 21 => 0x236bb6a598a2187d516310310aace7aa2a21054d7414d3208717322a4288618755163c8430e1ecaa1aa421e4d5398b411022f398cb210211b5c86550430c9aa7316a22062d5458b50cc65ab8cc8990839698e6015021acce4302a22066561d80524430eb24c629843a350d6210e31a6ae2310a88846f755864208716aa2c421e63c350d524c841c5cec2a28410d1d7498c534868eba4a7188632b5cb6150f408beeca98a22143d7695050cc72b29cc228841c3552434ca21acae3a9ca4204e571d8d420862fbb2a619043595c46314910e48e2a14a22172554946210830eaa4c6298219c5456014432c5ca9316621868e6358b41d02b338e8629221c3951320c830c3ac929e631045d739942004272b88c0a1443535c8530c91095ae532463a061d6454f3190346b24c790a410f9da54506308dee4b2a870846d75988430c30eb24a6196430fdd95410521e48a4a0882884af7650b5010a36b96cba08611b5c86054e4187aeb320640846d72996311021ebacc9988412d5c6640c841ccaa430a840861e6350e51d0a37394ca18881175cc65908109aae3b128618c76711815290e37396cb988810fdd16094432c3aa9b1a8398d1d73550430c332316c2aa2610fdd9540c010ec2a4a8c60186d13158031c431b2a4c2280658d59051cc540c5cc9310a808565729915110236b96c2aa661535d6604c832a5eeaa1aa421e1e5498f50c868f3a4a8a1a614b5d06314910a9ae6320a48862e5498853042aab88c129e438d59251cc440c5ac92906520c6d721815190f0faa2c7a0a630f9d06054e21a38e6aa2879054c7354932d062f398caa1421991895150420c6cc9a8e629043d7419432842a739ea529683655ce54907108bae632a432051d73d84544422fb9aca20a419354e62cc721e1aa9b0a6419655611865310a3b38ccb99081c3951520c430cd4a4b00641862d54588400c237390c6aa0411b5ca64d4d21a5cec2a2849058d7214d43d030eaa2c1188611b5ca650c010acce5322a218655639845050b26b1ca5a0821871936354620e4ca8a96200855471551324c28eb9ea92a0418e99160150218eaeda96200854e72993534430632a86a1265c350d5214443c5acb2a4421062d65508428c21f3a6cb908619358d6215120c38caa1a849854d73c85508868fba2a218c61535ca54d4d10ca8a6b0e648870d4354b5010f2a29cc210221995896115220c3ea9b1aa48861e5458f21083a3298c4a8841175cc6510010e4a84214a21054d72152430c78ca9cc0208818b195424cb40ce2a2b00a22164d53189430838aaa0c68802135dd56190c31c3ac929e422052c72550544431aaa2c22984195d4d6108110c9ac6a96821855673109511031ab22a390861535cb6154f41a9ce5a9ca720d677155021882a7398c9290819c5866015020a9ae629284a062
  | 22 => 0x6593995328c720e1aa8996a01954e73d52520428eb98c4aa0210f5d854cc510acae3a1ca5a0c6d72d9543486b2b88c0a96838795163d072187eeab26421861e6458c54842a6b94a6196831ddd95114540c9ae431aa89045d7318950d06973b4a4a14839394d6210e21b4ce92924210f0d4354b3290726a9ac4218834b5cb5495331a5ce9b0ca598e8d63508420821fbb2a998841595cb53c4010aace62a4a21046f7654852cc7872a2a729021475d0538c620c5cc8b14a618d6571d9052442a739ec3290814b5ca5450e31a5eeaa108518d3970153430c696b90a8a18638759253c8410c6ac930ca5884d571181430c61eba4cb10e61a358d4210931c5cc8a906598c5f7654f41082a6392a8996619554d6114042c68e9b2a20084ad7218141d032ba9cc3a1a21c5551518c430ccec4a8a821058d731494250334a92c199061715c6644c832c6cc8b08a81843d769505204326a9ac429a814b5ca5410a31c5aa9310a4187145414d214432631ca4880218b952620c020d9265300a21956571d5320082b238aa4292611b9db5454810c3ac9318a71062e64d4b2144296b96c22a2214b9d35294830c3ca8b1ea190e67529843044386b90a8a1e61335c86050f30c5cc8a9065a0f1671151430c62f39eca212219a59652840108bced29a200846d72d9543c4316aa2c4204218b59051c852095ae532462a056672d465110333b16c2aa261559cc4254430acae2304a41853870505501061eba0cb99021535c86094f41c3ced2a28718e8d6458b31cc3172a2c5a0e63561c1315403195cec29285a0564715815210f273b0a6992419598d5110020a9ce6304a40853574d4b1004326a9ac598c819358d5214341acae2304a42064c5358830443a2a9ca4a8881b24c9600c520e1a86a90a021ccd7318121086963a2a6a12414d5d03254420ad4e031ca598cd57198c420c636b90c029a211bdd95214840b8ee2b02641965663547210c316b22a419063591c55214940e8aa6a94a22043d7695331c8733312c32a2634d5c76395321c5acaa10841861d6419253c863ab8ecba1661939d46350932a5cec2a28410f0d5454f200832731ca5a08614b9d05394810c9cc6b10a80862e54588430c69ab8ec8aa0410f9d262d4f10a3ce8302a790d8d72151430c70eb22a629e43471cd5450f21aaae7322a21045c7558c4244237bb2a410421179d663485308deeca90600846e75d853248316aa4c598e439354f62440108eae3b2e65a046d7299251cc332294c221221535c85450f308ece3b2e87906366458653486b2b88a6a90818759153cc420c9ac6b10a91043f76550540c387390a8a18634d5d05294430c5aa9310860852e74d865210eb3390a928861475d2534c310c98ca990658851c73550544428eba4a6994431b9c86354041c9aa6b108710e2c64189518c
  | 23 => 0x94c10a5ce831ca41846f725805150f26a9cc3900419358f5208310d1ac8996a21967365545200821f3a0c6a80431edd95014143c5aa8b10801064e63d4b4144256ba6c7908438d99051cc520a32e02a28618f0d435855210f2ab2cc7a0c830f5da5490c43aa8ea994628863565946411029aba0c128841999945290510e1ce0aa2641943d76d5040c4317326a4102218b9916215210cacc6a8c801843f76550548c21eba6cb996218b9506244010d1ecaa9a842143d7498f52c431b324c229821c695153500408daeb3048410d6571d9252cc63dbb2a028283535d653084208e8e2b2a8710665611462048236bb4a5100419354d6008420c6aa8b08a019476711974204296ba0c1296631b1c96550d10d1ac8990a01964d6354b4104316aa2c42a663595c464d4910e1ae0a1aa421e1d64d4c30c4317aa4c42022117dd95314c108f0eab0084886596554e100434ab2082988630f5db54c8510e1aa929a641943d74d9432c4266b9ec990e410f9da5450610c9cc6b16a81854c754c83244237390ca18a8117dd95314c2187ae9b0aa690cad72d854350272b96c918a218b99564c852087cec2a2810843d76550200428ebacc4a18878b5955488420e1aa6a10840858e729854310eabbb2a218861a3d95544c832aaae2326a6886a9425805110b16b10c52a061999896114e10a98e6b0aa4184cd73181214821eba4ca188411b9cb658c7408baebb1a821852f725444190346a1ac421c618b9914294421c9ac631aa40861d5458c54c8387baa8729087c3dd54354843c5ca9310800846e7615142c8236bb2a42002187951631022099ae5b266318d2e7218d54c869ab88c0aa065c51915344010a9ce6324a40853671d91548cb8aaa4a788021879915314c10acce2302a421f147150e5110f87aa6a7a92218750f6254043aa8e2a98a6a045f735865090b173b0a8a1265555cc54544208bee6b2842a068d435884310b87b9a86a9087555cf52c40108dcec21aa598e2d6498853c869738ecaa10859398e5208010c3acaa9c822070c7254d4210b863b286a9087c354f4350842e1aa6a14a22162f765095010a3b38ecb21e41c354f6150842c3ea8b1ca88868d644c8328c716aa4c421e438b5516214331c5aa9314801063554d85430421fbb6a81922193d4d6294d418dce432a870846e72d9643c4236b94cb20e61435cc5450920d1ac6a108520c3e7418151ccb172a4c42886117dda53c8440c9aa7316821043c74587524c32ab1ca3a08614b9d06054830c38c8a1aa018e8d4358843cca8eb9ca820a63595cb5444010acae22a4a41854e72191530430f3b4a6a1c83939d46250d32c9ca6b10601061d54d81300c335b2ec4880211b5da5214440c3ca8b188598e1d5498c420ca7238ac421a434b5ca5410b31a9aeba1a641961d6454c3088387ba2a899
  | 24 => 0x29e421043f75593210831a2a2c3a1a2193d96524c030cd2caa94200843d76550320430f32ea829a21b1584614c832c3aa8b1e821862e64588540c28f39ec2aa041c354d60508428deeca90a198d1e74d8553c8637bb0a5a0a219554e6114840c3eeca1aa021e345458743c4392a94c22088196d946344010c6ecaa8a8020695648c430442973a0a6a9021875935394d21c6aa8b08a91051c7454d4304332294c3902218d9516110010cb2a6b00822043d75993210832b29cc21804193d96534802087aec2a06488672515804110386a9c86a1085475ca5450e31a9ce730aa421d2c74549428430eaa2c62a0439594d6108010c5ca9310801871654547300c2aab98c128841a3591320ca30a3ce7aa28690dc970d4932cc326b1ca590841179ce62946408bce632a432052c7654d4210a97394c7aa2219354e62d434187ee8b0ca19945e731974204392322a488021999896115030a5ae5a0aa120e2d64d4830442973a6c2292211e5da5184010c6acb3264310e4e6598f214832731ac52a6212b5c86050f40a5ce9a9c8510f246454a511022ebaec6a1061175d663d0440a9ae7aa64010639649805304386aa68699065935886254c40c68a930c64886566358754082a73b2a8990652b5c86050540d1a86b108620c6d76948400430fb2ca898061175cf65d0620e18ecaa264197155394740102373b087a9221c550c4394420a98e6a90a4a05c673d05210872729ac418c435c9c0325442087ae9b2c639061d6458f520424eba0c098e618b9954210921d8a653086410e5a53580320822f398cba0a4193d8f6254910a6ae22a6811064d6394b21102aab8ea729881569c33154231e94e029a6410c3d769524210a36392ca18a818799053c85108f6eca80a1a0e4e5398843c87932a4a4a8861479d85450c3193ae7b0a8420e4d6318d52d06a6b98c1290818b55262904218deeca90a418e6461545200828eb9ca821e438b95162d0630a3ce8314a790e4d6394b41cc696ba0c129061c95084294430aaae3b14a7a0e2c655094048346b1a8421661531cd61d4910c3ca8b1e821062d54988540c28eba0a499261c3d50531491087ce9b2e658861d5458f21082b2b94c728881179db5454c10c3ecaa18879070d7294d439062ebb6a7a0a21535cc6054840a3ae7b22a8107265454a510c21f3a6c2a90218bd965250040a5ce92a2849043e759933144326990c2a8065d194e52944408d8eab108690e5453984304421fbb2a8286634bdd110149108beeda9884885557194c314861f3b0a8a0a439358e6215321a3ae8314a790d367498e511030f2a4c6286438b553634c832e8aa4a8a60186355498643c862ebb6a6212211d5db53c4010a5ee8a9ea48853671d52548ca3b388c0a96871b9ca65d0c10bc0e090a408846c7258650d0eab39cc4a8881535cb54
  | 25 => 0x6458f210872731ca5a88818b5d765508428d8e4b2a831854e72950534421ebacc818021475cc54d02208daed296820852d7414e320871db2ca89806117dcd65109108bee6b2a408858d72d854310f0eaa2c621663175da531001087ce8300a48846d7694850cc72d31ac02a04369dc560508428e8eab0c648866562d465150f86ba4a4994639358f5294941c5ac9314a6884e6760c9210868eb98c52a0411ddd95114743aaae3992a018c3e74197314834aa1cc22188387551639083295ae532263a065563547211028eba0a718c218b15262d0510ccac4b0ea81864e635482004392a92a3a008117dd9530c220d1ac6a10841949e7615143cc386aa4a4188610fdd1654c110a5ce9a92858846f7558d210868fba2a629a21179d663c85108daeca96821847575d8532042b538642a844353dc1544c8328deeab14601061e5498f510821eba0c4a80639354c625072187aed2a0a41862c645492110347322c5988639398d62d5221a9ce7aa2a40861f5458e54c4338b0cc0298414e9c341540418d8eab22649064d6398b54c8716b22c52986393d955350842c9aa6b10862064d6358a544c787aa2849946353dc954d4d108d8e4b2e868861e6414c204423bbb2a228c85179cf6155010c98a7316628847776544518ca66b96c2a18634b9cb611511099ae431a809874553546210832b29cc321e43179cf65d0910b32e998e60985557118253103a4a9cc0108418b595421083299ce2312869966562984548c22f39cc928c414b9c454508218bce7b2c848854d754c83290636b96cb98c810f5d0650c810c9ea6b14a720c3d74d8553c8387b22a6a10851b9cb6154c10ec2a4a8a601846f72595319031a30aa2a0081c394d52d00409aae3b226418e1c6454d3210316aa2c5a0e639554e6114440e1ca8a9aa408659539802104346b1a84214438d15161d0d31a5cebb1284a061d6494c52042a63aa6418a41535cc5494810e4aa9292200846e76d513208656ba6c790a419554f6044010aaee6a12a2184b571d894310696ba6a529021179cc6510520ea2a6a8a40104747558742442b339086a8841539c86094c10c3acaa18879064d6394842d028f3a0c129e8387195430c540a3ae6304a990e65629875388717b2aa8990658d5526190b21aaae7aa2200874652547300c297baa84216630f9d2654cb1096ae8302438852e7418d52043a2a94a3980611d9c46550e20c5cc8290608870c72551320cb6898ac018e611bdd95214b409cae4302838864f53588404432631aa488021c395132d40328eee2b2a652062f64993524428eb98a9a0241875526315010c6ea8b08808851d7395043082a6baca6900411ddc56550e20a9ae72928520c5e7319421502aab8ca618e419358c52c8510c5aa9310601045d7399641c830f2a6c6880214b9c86395030c3cc9
  | 26 => 0xeb22a6196434b9d36194840a3ae7320a890c6e721954308332b12a220061c3dd9544c8328baed298840847b76540504862eb9eca200414b9d35294b3187eecaa0a91964d6394842d06973a4c4292218dd51610c1108b8eca9a869061e6494c32c874aa1cc3a1063479d06094c20a9ae5b1aa60864d53d8941c8636392cb21a21475c85450c31c5ccaa1084a0c5e76951438c72a29ac321a214d5d26254420acae2302a42061d4358a5110f0f2a4c6216630f1d161940328dce4328800862c5498a5344237bb4a5a08211b9c8650c010c9ac7a94a58855571190534422fbb2a6210219354d6210c2087ce9b28601062d6454832103a2a9ca210841171cd601454295ae430286a049d74d85320c63bbb2a218041475d0534c92093eeca18a021e6765945200830f324a798e431d9c46550a30c3ac8a9ea40855571d4e5308296b86caa10859594e6190b2187aedaa0408843f745973244272b88c099043591c96454420acae3212a010d2d74148218432aa9cc2100211d1d56110d10a9ae7290438843e7418153c861fbb2a818041555c46054c42c6ca8b08600870d4310d520c333292c2200618b5916294f108daeb3148610e6552d811004256ba4c518843c55515344010e18a9a98a48845e76d51320c72aa9cc2200419358d62151308eee2b2a84887255254540102a6b98a410c210f9d26294410c9ac7310a91864f5398830442ab388c0a98858b9926214c10caca6b08a02161d5458c548831bb2ec8880218bd5162d0710a9ce7310a48846e72181531072b31ac32a243879526314c20c9ac6296438843d741805344346b226419083595c84054440caec7b0aa89051d7550c43082a63ac86996419514d61ccb10a6ae22a2811065551582310c2733b6829084387590530c1108beec29e428866b65949300c316b2a8421041175cc65085408beeca98a68843e76951418821eba4ca996210fdd954080108dae5b2e622051e7318a54c86a73b0a6992410fdd564cc72196cec28a83a070d5494e5204332b14a218041699c843504418dae5b2c868861f5498c4044237390c0aa46387d954350a31e4ae22a0a488637659511004335292c028887535c9530c8208e8e2b2a851843e741973204296b94a9a1c638755163d06108bce6322a40851e7694d4390716aa2c42a461595c84394440a9ae7a94a40847671195430434ca1ac020a618d59261d4c10a5ce929ea48861d6494f50c871b2a2c2200611b1d95244010c5aa9b12861063664584538430eb26a729c4387993530c110caeeca8862187246494951102ab388a8a984187d9653500408baeca9e422046e72d954044236b94cb18e81175d8530811087ae9b2e431856672d52510c236bb4a428887879526310010a3ce7aa4a990dd170d4531cc386a1887290218d59261141328d8e4b28829868d
  | 27 => 0x839354a61cc0308dce4328829846e72d9641cc21fba2cb192214b9cb64550308eae232a851866552984200421f3b6a8a9a214d9d03054430a6ae22a4831851e7498c534422fbb2a621041535c0534c8218dae530ea0a1f45539452008237bb2a4290879358c52d05109caed108408862f6550842082aab88a7984418b95162d06208f2e03288610c3d749943008326a9ac418021535cc54548109cae2302649064d6394b411032731ca420061535c8538c610c9aca990641047b76540500caa7398c9296630f9d3654c110d1a86b10869054d7394920c4316b24a419061c95515244010c5ac4312a998e5553584538832a29cc2192214d1c554d093087ae932c640861e64d4e524431632a84212211ddd95114630d6282b0083a054d739535244296b96a92a0615a5c05450821a5ae9b12a40865553d8542042a6b98a490421539cb5494c108dae432a622055771548318c22ebacc6210819358d52148408dce4322a610474715943250256ba4c518a41a3d9653508428eee2b28849865563547210c21f3a6ca190410f5d9540c010c3ac6318a88864c5358830c42a7baa86994430f9d2654c810cacc7308a0a162d5418943c8637394c928821c995151c8020a38e8a98a68861d5458f41083932a0c4a88411ddc5650c940a9ee6a8c431065553185320438729aa4a0081a950a6110821c6ac9308a71050d7294d439072b31ac22a421c550c4394430a6ce8192a2105547154e434830eaa0c6a0e639654d6014c418daeb316621843c74595304421ebb6a820c21539cc6414910a98eb21a6410d697018e52cc63b388c0a90879598f51c8540a58eaa1a849970d7150d5210f2732ac598a61879926315020e1ca6a1085a0c7576944400832731aa429683179d663d0510c5aa8b10a60873154546300c272b8ec919641a350d6210d3087ae831aa40862c64509508ca9b3a6a328c651b5c86055331c9ac631ca5a0e1e6454c5308386b90a6a1a85a359163c8520e2ae22a6a68862d64d4820442a739880a90814b1d153d4910ccea530e848852c74549420428fb9ac3aa221539c4534c920c3ac9298601059671d5143cca8eb98a8a0241595c86094430e1aa8a96601851e76151434ca973a0c1296630f9d3658c7208bcedaa2659845d7399251c8335a90c090a21a350d6214443a68eaa14828843d76553310421fbb2a998821875ce64d4e21c5ac9314a78867161980540c296b90a821221875506350b31d9264b00a2196656558b318c6b3396a728881335ce629072087eeab0e87a058e74181320cb16b22c429c21a950a6110b10c38caa1e849863654587520c23b3b0a8a0e2117dd95314341c9ec6312a88870d731494250326a92c018861c5d516114d108dce432a622043f76150204432729ac418421175da53d0721c5aa8b14801054d7398852443
  | 28 => 0xd20c68a9308808866552d854204327b2a6419021c555251cc030a3ae829a65906575358430c42c6b98c0a1085475ce5410c10e92e029a6410d2d72153430c62f39ecb90c818d1936154910c3ac8320a68862d6550842042573b0a8a14654b9d76450920c98a7310808870d5494d52042a7390c0a9e83871cd6494e21a9ce229a6410f0d4310e52cc726b18a390a41335c8604c730c5ea9310868843e74197328438aa9ca2a00811b5d46250c20ccaa430a640864e6354a21cc237390c02a22199d496110110acce229aa4204767614921c432aa9ac21844117dd953c8420a5ae9316a610cb574d9531c421fbb2a821e658b9954210931a5ae92908408554754c7304422eba8c09946387d954310f21c9ca6b10800861d6414c204432731ac52a2434b5ca5490710ccca53086008636649472108236b90c8a9c21535d5320cb4199ae43028618f45320ca5108236bb4a8292218b99252c8410d1ac8b166218d4d73d89520428eba6a7298418b9526210c108bce6302a810c5f7558f41c862ebb4a628885179ce655081087ce83286408566711825210f2ab1cc32a621a3d96544c832d1ac899064986565358732d078aa9aa320881535cb54cc030c98ca9906210c3d74180524422eb98c2a80850f9d262d4d10e4aa9294a21854f72587534438639aa8990650f5d06354a108d8eab10869045d7694e300c317322a5908619598e51d04208f6eca80a09955571cc8514c38aaa2a2980619998a51cc4208bae6302a5a0f4463949510c21e3a2c3a9c41c350c435481095ae5b0a8620e2d5498b410423bbb2a220061175db530c62087aed2a0641861d5498f510832732ea6292219a549600c430c6ca9308a21061e5498c5304237390c2a8087a650d6010f30a3ce8314a6105667214d5110334a94c020881475d0534c2208daec21ca41858c74581320ca97396c2aa6639594e61ccb41a38eaa1e8499666629474110386b98a8a1641539cb544ca31b1ae42a2869855970151430c61f3b0a8a1e61175cf655011087ce9328400851e7418153d069b3a4c4a88818b5506250e32a9cec292649861c5458c404430f2a2c620c63531cd524cb40e1aa9302641946d7298f505061f3a6cb90c61559cc6054420a5cec2a2849963954980510cb32a94c228861539cf61548408b8e6b2a850862d6458a5344334b14c029821599c66454843c9cca9906520d4d73151424828f39ea8a18638b55262d4c10d1ac89906410c3f76953310824eb98c0a16811ddc56550a30a5ae8292410843d749953204326a9cc429021475cc5450220a5ee8a8c431061e6498c504861eba4ca19021c59506354430c9cc7314a8885a972d0740502cab9ca9208832b5ca644c540caac730ea91962e5498850cc6b2b8ea52906117dd953c8410c6cc8a8e621051e74182530430eb2ac7a0c
  | 29 => 0x906590e1d6454f510828eba4a5994638b59352c8710e4ee2a14a22154e73d855210f2731ca5a08214e5c06295321e1aa629a842162e54988430c32aa9cc2280854b1d54290520c9cc6290408846d72994430430eb24a798e43c51505384110e1a87b0aa421c6d72d9631d032732ac790a418b5915214331c6ea930c868845e7615153c870f324a6288419398d52d0430c3ca8b18810845d7694f41082a6392c2a9841175d853d0510ccac528e822070f53508424430f322a790821659c46050c43e18e0a9a84214797694e300c22fbb2a629081c31c9435484387eecaa0a89061c5458f41486a7390c929841475ce5490621ccac4b08a91863664984540c386a9a851948387d8e63d5110c3aa93188598cd571181328c7b0a92a3200818b593520c9108dee4b2a869046e7298f544428eb9cc5aa221359db414c431c6aa8b08811046c72587544c236b90caa1c21335cc6250320a5ae9316a79064d52185300c3a2a9ca588021471cd5450e10c3cc9298600862e54588300830eb24a61964163dd54354843c9aa6b16622064d639885404256b90c0a08831d9db54440108baedaa4621864d5398843c872aa9cc218021175d663d0420acae231ea48868d4358843cc61fbaac8180212d5c46050e41caaa7308a61045e731895010637394c9a9e2159dc56054843a5cebb22849961e6458c54c8316b24c429e419394e62100208d8e4b0ca00873154545300c29ab88c12a6638799143944318ecedaa2a21065b53181314432ab18a390a61591c94354420a98e6b22a598d2e7218d540c236b96cba1a43475ce5490e21c38a8b18408861d73191534823b3aec910a218d9926194b108deeab0c659043c74580514cb86a1ea5a126193d965350842d1ac93166318c3e74d855348637bb2a4290219398e62150308ecec292a2204757118152d0ea639ac0a9087875526314c20a3aeb2a0621845f7694f410830e2a2c6206219354d6214440a3eeab128621e4d6318d521031b328a910a218b9894294740ce4c2b00a610c3d76952411068eb98c4aa041175ce64d4121a98e6880a48861f6494d1004326a9ac5a08811b9d46250d2196ae8302638854c75909324c2ab39cc4a8861ca55252480208baed298a0214cd73d8542c838b2a4a728841471cd5450c218dae5b2c878862c545884344237bb2a5a0881335cb64cc5308bee6b0ca02162c5458a534431ab24a218041535cc6494840b1ae43028621c3d7695032cc69a3aa83a02211b5d66210c20ca8a730e848864e654c8324422ebb2a620041179d85450c31c6cc2a8e802043e741942004326baeca99065175cf65d0720c3acaa18861068d644c8324823b388cba1c415a5c0534c8218d8e4b2a870864e6358b54cc72ab1aa3a08819ad965244010a9ce7b08a48868d4358843c8734294c190a2187595431
  | 30 => 0x3588548830eb18c72a6438b5526214331acce42a2a21864e5398b41c8726b1ac42a265c5951510c430a9ce6304a5a0f0d53509321068f398c4aa663a399163c872099eec996a01945e739944008332a94c218021539ce6054b31caee6b08a09943e7695140c431ab0ac02a2218dd915148440cb0a7306628846e72992518c2a739ca8292210f9d365cc720acce531ca22062d6498b53c861eba8c0a1c83c5951310c72187eecaa0a190e3564d46514cab2b88a8a9061475d2538c621a6ae9a9ca21063664984530821ebb4a8288619354d62cc420a3ce9b0aa61047a70194438870f324c62a021535cc6494b4187cec2a28710dc671d49320c72a318c2aa241479d06094f21c3a87b02a421e1d6494c308422ebb6a818c6117dd9530c710c9cc729085a0cb57118142d032a29ac399243a3591320cb3193ae83026218e2d64948300430e322a6988819558d51d04308baed29e42207457114f524422eb9eca216218b59251c8720ad2e0318a48862c6454932d0726a98c498841171cd65d0910c72c9300a610e5563987548c696ba4a5906210f9d2658c810c5eeca14a22145f7654c53482a6b9820a90210f5da540cb218bcebb0a649846e76d4d420870eb18c6aa0210fdd954153218daec21aa40852d740c1520c21eba4cb990210f5d954c8430aa8e2aa6649854d7318252d06aab88c0a9841599ca6494420c9cc7310a81068d63508429030f2a2c621065c955151c8020c9ec6a928398d4d7294e3148726b1aa4216814d5d05254430a5ae8302a4085647254621902b938086a8881479d36354c208eae3328642064d5358b410829ab88c0aa663c654d6010440b1ce43028621e3454587424431ab22a3988418e5516015031a98e6a90a4885557310a511021e3a2ca192219394d62cc62087ce932c43986c53298432c4333a92c218221875526315020e8a642884298634549844344326b18c6292211b9ca649473095ae9b0a4210f0e73949429072a29ac2202219c945600c430e4ea8294428851f745875344317322c429c41635d0534c821e4a84212a22046e7218153d061f3a0ca18a418bd96544c83293ae630284a053571989540cb16aa4c5a0e43695ca5490710cb6caa9a200845f7654c5110266b80c6a126593595320ca10e1aa7294822063554185430421f3a0c0a8865175ce6494620caaa6b08a72063664947210c317b20c4aa2211d5c56510010acce22a4a41845f7654c5108332b14c22a021871954350130d1cc6b168320d377150c51502b339060a88619398f5210110c5cc92904008745539842108333b2ec4880214e5c06395331c9ca7310600866562947311023aba8c299021539cc6054840a5ce5aa68518c5d7694f2104326992c12886517dcd6194010c3ac8a9865a0d8c7150d424ca36b90cba1c214d5c66355032d1ac89
  | 31 => 0xebacc0a1887179cc6510a108bae7b0aa5a045d76d4c204423ab8aca180218d5526110010ccea4b0841886a942580424430f3b0a8a18631b5d9520c010e4aa8312200861d54987300c2e4b80a4990631b5ca6394740c5ac8322a598c5e7398b505072631aa490861555c46094c20c3ec831aa88845d7318151d0a4eba4c618a6195996310c1108bcec2a2869946f7558b310c3872a26419643539d7634c920c3ac8a98600852e7218d5408326a9ac4184211bdd95214b41c9ac6290429863954980210833330aa39044117dd953148108ecebb1c428861c6450d520c716aa2c421e652b5d0604c82196cec21a8220e1e6550e31d0352320c4880218b1954210931cccc5288801066662984540c296bacc0a10859ad955250040a6ae931aa21052c75d0d42c82363aac521a419ad955244010a3ae829a6108745320ca510c2373b0a8a90618b95262cc721a3ce9a9c8710e3454d85204430eb22a7a86432b5d262085208dae432862a06a56290440c432bb28c6880218795263d0721e30e0a1aa021c7a7019543086e338c86990432d5c6644ca41a3ce6302a80863664544510c22f398c02a2218b593520c9408dae5b2a86886385498042442aab8ec429a218b9d85450b208eaed28c200863554984510838aa9ca220881c350e6154843d1ac6a108418e6662547410822f39cc5aa6214b9c86055321b4ae2302842152d74148214c2d4b80a4a108387590530c310c9ec7b12a32062e6454832102aab8c86a80630f9d3658cb1087ae9b28640853571150418829a3aa82a02219594d6110020c3ac8298648865663947410c32732a6518a414b5ca5410631e4aa4a88822074652544310c38729a84210818bd516295131c9ac6a96a22046f7694b311023b388c0aa0652b5d0624c120c5cc8a9662205357118254c8792aa0c4a884187551600c43087ce931ca21047475587324430eaa2c620021535c86414d10cccc528e621845f735825110a8eb9ca920a431b9c86355010c9cc6a90a22051f735474090236b90ca21a21d154a510c4308daed290600843d74188534828eba4a798621a558e4110110a5ae62a28410f195454e1004326b1aa429683a358d4210830c3ac929e63206345458742c428eba4a7994431b5db5390a21d1ac931e4310e1e6454c2004286ba4a499463171cd655091096eeab0e8620e1d64d4e53c4296b94a8210610f5d262d4f1087ee8b28629066552584521030e32a8621e21535c86494f41e1ca8a98421062f659512008334a92c018821599c66354843a6ce2304a81061c6350d521069a3a2a228a41531d5320c940a6ce8304a21063754986424431d324c029843b24c9600cb30c5cc8a96420864d5398b3104387390a8a1a61475cc6095010a3ae9316a68845d73d974108257394c3a1a85179ce64944108bce7314a22064e6
  | 32 => 0x3c350c6154843a5ae52a08298e2d6494820043a2298a498a218e5516090820a9ce5aa66518d3571182540822f3aec2a1a618bd95424ca41caea730840886595358021083a2a92a3980618b15162cc510cccca29462884797694a2008297390c12a643599c74394b41c9cc72968398c3f7655054c8317324a419061179cf65d0b10e28a829a828847a7019443087a329aa2108419358e62d52328dcec29a659053471589540423dbb2a028663995496114a30a5ae9310a58846d75d89410830f322c7a90218b95262cc420e2aa9b1a200853674d4a510c296b90c12a0618d15261d0110a9ce4304a62061d5498f5204346a1ac421e211b1d562d0510c3ac8b18a5085a672951411062ebacc6200411b5d8520c110cccc5308a60862e6494b310c316aa2c418041399d84248421caca6b08601061d6550c430c237396c2aa6618b15162d0510d32c6b0683a052e7418d5210386b94a8a1c639354e6210f418baed298a5a0e1d54d8d42cc71a320c2a9a41179d46350931b1ae72a28510c3e76551100426739cc321265179db544c030a3ae62a0829045d731815110b2ab1cc22a4410f5d36154b30c98c7b12a88861f6550c430cb8729aa420881591d53288510a5aeaa108598f44714ca510ca37baac4218818e551600c4308bce7314a20852e74d4a5204394aa2a508021c39515350842e4a84212a21861d5458c200432ab18a3a0a61175da538c4318bce6312a808654539873044237394cb98881a350e62d40438eae332c861070e5454d200828f388a8a1863179cf65c8740c5cc8a90a598e1d5498c54c86963aa86a1043175cf6155320c9cc6a96820855673991511032a29ac321e210fdd95414830c3eeca1ca221d56719915310aa7390a8a982193dd93294432e8aa6a96200851d731534208726a9cc4298210fdd9541481087ce932c421845d73194400822f398c0a8885591c55350920b18e4b028621e2e645482004386aa484994638759153c8440a6ee2b02a998dc67294d310c62fbb6a7a0a219394f6244010a3ae929e8710e4e654ca21cc21ebacc1a10839998551c8020a6ce931aa21058d7490d424caa739ea529483559cc5254440e1ae829a649047475591214421f3a0ca908615c9c04354430a3ae7320a9885647548421443162a0c4a9a214b1c95450830e1a8621ca42070d73151424830f322a6196438b5516210c10c5acaa1085984ad7218143106373b086a90619514d610c110a58e2a9a8421475711815290f932a2a4a88618e9516010c30cc8a5308408846e7610d52043a3a9ac229221a358d4214042a9ce7a92648862d64948510c286ba4a6994434b5d32154021c6ca9308601052d72182540430eb24a61904193195324c120c6cc9308a40862d6454b50cc6ab38ec6a9841c65c05450c31c6cc8b08a91865563984548c28
  | 33 => 0x4428dce4328869068d644c832c422fbb4a79082117dd95310e21c3ec8a9a642065665d4e3144326a98c4a1e43595c64394b31acae2304a5a0c6f75588430c2caba4a7188638b99142946328dce432e870843e741943108636bb4a5a08618b9516214c1087aed2a0a21947b7654050c8696b90c0aa0619ad95524c030aace7aa4a21046d7218151d0f86aa264190619958a61141438dce5b2887884777558630042a7baa8729087b198e62d0541a9ce5b0ca7a0c5d7694c5110316a92c1208814d9d26254430d1ac6a10848852d7395142886ab39cc8a88619958560149108beeab18800863654584500ca1eba6cb192210fdd954144208dcec218a4884b571181425023b38ecb196811b5d852cc510cccc5308a91846d72d85540c32db2ca690041175d46050e31caca7308a02147671995430872cb2ca708021175cc6454a10c9aa7314601047571997321038729a84210218755263d043087ae83286210c7671195420c30f322c62824387550614c0308f4e0328860870d4354b5110f922a0a490a218b9926214810a9ce7b0aa5a0c6d72181540c726b2a6419481c550c4354440c3ecaaa2641943f76550540c696ba0c0a9663179cf6590b10c5aa9316621854f75585320cab2b88c0a966327dcd61901408dce5b0aa81846e7298f54c4272b90c098e21b8d886048510c5ca8b16a198d1e74d4d434878db8286a8087179cf6550910a9ce6302a598d1d74189530830eb22a790841475d052cc930c3ac8b1ca48862e54588408c22eb98ca20a411b5c86510f108ecec292428863564147215023b3b0a4a88618b15162d0710e1aa8a90621863a54980510cb16aa4c5218659558d5114440acce531aa2105667298d511021f3a4c728e412b5d0604c9208dce5b2e839854e75d89324c352b244210221659c75450c31a5ae52a0840861e6498c5304386a188629221599cb5454430cb0a7300648845d73d97211030e2a2c6212210f9d2650c810c9ca7316a1a0e355458630042a6b94a6a1c83a3d9143cc932c5aa8b108790d4d7214d308438bb22a6880214b5c05450a32a5ce5b0ca81045e7614d5244333294c2216838d95161d4c20c38caa1a8418d647548520443a2298a520a210f9d36588730a3ae8302a60868d435884308726b1c42282434b5c85350d40a3ce6302a990c5e73d85521022e39aca20a4163dc96050c43a68e2aa0a89855473589510c30eb24c729221935cc6255130a3ae62a0831070d73151424cb2631a64a80431d5d66110030e2aa929ca21062d6454830042f0b86a290e41c39d95350842c9ecaa926018748704c9500cb872a264190418795263d0420a6ae3b14a998cac725834350a1fbb2a8196438d59251c8440a38e8b12a7a0c6e76151520438b2a2a6880210fdd564cc430ea2a728a200854e731915204332b14c3aa46
  | 34 => 0x8822043d751814290733312c3aa6635a9c06494b41b4ce998a4210d54754c43144326b18c729081535cf6194b41b32e029a8620d5671d5153082e4b9663982610f5d8419404099cec292659843e74d8553c828eba6a729e43475cc6055010a6ae32a0839861c5458c424c22fbaac6216838b55262144308bee6b0ca1a156572152510c24eb9ec2a14838b5926214e10c9aa6312200862d64548528c2b338ea5290810f9d85450f32c6aa9308a21850d74149324c317326a419221475d0538c520a9ce7aa46510f0f71551320ca2eb98c4aa0212b5d363c8621a68e2aa2849845d7398b5444346a1ac4218411b9c86590c10acae3aa0421062f6555120083a4a92c018861535cb540c430a9ce4324a790c3e74d96310868e3a2a6a1c219394e6210c20c6ec8a8a6220655635845488394a94c0208818b99352cc510c3cc8a98a40863954580510cb1732a8421221659c75350c41c98a731086887446354a510c316b22c529c431bdd952cc430c5ca9316a60846d7219150cc733314a220061a999262cc631a9ce5b0ca62063564987520422fb9acaa14211b5cb65d0630e4ec8a92200858d73949429072731ac42a421595c46094b31a3ae72a68510e8d6498b314c236b94c9a9a212b5d06048720e1aa8a98421062f5458a54c4256ba6c299641555cc6054420ccca4b08800864d6354842cc636bb043280410fdd954144328baed298400852f75508420c32729ac4218851d5c765d0f208beed298840843d76d50324432ab08c2a98858d552610c020d2cc931e4290e4d539842108286b94a8a1c6317dcd61d5220c9ec7292200865765945300c28eba0c0a9841335c86350330a98eaa12649870e5494e520432729ac421e43275d0604ca31b52e02a28410f2654549100423b388ca218218799153cc7218daedaa46410e6552584400c2cbb8a8720c638b59152cc440aaae2302a62064d6354842d07b0a94a288021475cc6095020c3aa8b18a990e4d539884004296ba0c6a90218b9916294f10cacc7288801046e76151424831a2a0c2902219598e51c8440c5ca8b16830865563544400828eb80a8a1a654d9c46055030a9ae5a9ca7a0e1c7650d5010eb2b90c1288819598c51c8540c5ac9a94a488535740ca510829bba2cb884214d9d26394420c3ac931ca58845d73181521061fbaac3a1681479d06254f21c3aa8b188118746535452008327a9ac421a4193d4d620c110c58a8b168298c6f7558a430ca2eb98caa14211b9ca6550c10a3ae72a48298e1d6454c2004327b1aa4908614bdc95190640a9ce7326a48843c74586508ca8e3a2a629a41555c64314530e1aa8992a21946d72195430421eba4c7288219554e6190010c3cc8a9ea40843f74595318822f398ca90881a350d62140438ece232c861053571d0c515034aa1cc221e21c354d4214
  | 35 => 0x4c8324c7a2a9ca528881875915314420a98e6aa6a48864e535884310726a9cc5a0e43c3d5353149108ece232a640854f7358752443a22926218a21175cc62552108deeca90a4a0d6572d4d1004237b92c328087599c65490932e50e0a12a02143c74582510cb2631aa4a1663a95096114042a5ce9a9a8510e5753984304430e32286a8665c5552510c4308deeca96620861d5418d210c316aa4c598841595c86054440c3ac829ca48863554584540c339b2ca290041535c8530c940c6ca8b0c6590c5e73d9440082b2b8ea8900410f5da54080108f2e03288710dc671d4d320874aa18c2a14638b99252d4331c6ac8b0ea61062d5458b4104316b24a4190211b5da52cc440c9cc7290800863776544411038caa2c0188614d1c56355010c5ac92966218655535844004317320a590a21551c56254c108dee4b28829843d74d95204422f39cc9a9221569c33154031cd6ca312200854e73d865210e66b9ec990843c550c4354430c3ecaa18861067365945300c30eb22a6184210f5d0650c010a5ae431aa998d4e73d4932c430fb2a8621c210fdda540c010a6ce829aa21052d72153408c32ab1cc3a90219598e6194b10b18e4a1e849954e7298153c8786aa265a88654b5d063948109acec21a6218d1c73551430432bb9ac2282879958851cc520acae421aa21062d5458a3008316b22a4190619914a6108510c9cc6a90801870d5310d4210a1eba6cb10e611b1c961940438baed29e820853574d4910042b2b94c8a8861c519253544408ecedaa2a2187445314a2144296392a8a16618b9516214430aaae6102a21070d5454d2008316b22a4100219398e6214141c6aa9b0a640852e75508424c23ab88c0a9087555cc549442087ae930ea0994d571181438c6373b0a8a1043535d2524ca31a5ce9b12a40862f5458840c422eb98c0a8c859358e5208210c5cc9314a78856970190524424eb98c0a10838759153cc721c74c8b00a610d1d73153408422f398caa0c418b9d85250940c5ec5316a88861c6450d52cc332b10a3a0a418bd5262d0510ccaa530c800845d7598c42d074732265a8065531c95414d10c6cc930ea6106656258453882a7390c9298218b1c96494a31a3ae829e649062c64d895348236392caa02210f5da5414321aaae2298631054d7214e4350316b2ac990c434b1d54210910a9ce6302a5a0e2c54d8953443163b2852888587991530cb418ece3326a09947776544514c24f3b0a6a18830fdd1654c910a5ae8290848861e76151434c22f398c0a8e85531cd544cb20c3acaa188610e6452984304430f322c62a2414b9c86055030d1a86b108720e2e5498b410422e39ac3286858e5916014c218bae6302a520c3d769533108266b90c0988639514e6190d10ccca53086598e66629845050e37bb2a4296874b9c86095010a6aeb30
  | 36 => 0xba4ca180218b5886215110ac8e2b1aa408636645845308326b1ca390e411edd950142438b8e6b2a8088596719894310e37b92caa1a219594e61d48408ece2302a91962d5418931c86b2b8ea5290818b5526210030c5aa8b168390d2d709494290716aa2c110841535cb5394c10c38caa1a859856571d8c524430f320a6192219c54560c8420a6ce3aa4a81862f5458843482c73a6c299065599c843944208daebb12621062d54588540c266b9ec990a41555c45494c20acae3a9e401062e645485204296ba6c32906199589611503087ce830aa01952e72d51428c636bb2a5988818dd936154d208beeab18841063664984504cb8aaa4a688021479cf6155321e8aa7b12200864d53d89310828e3aa86a1265c3dd14354843cd4c4b00a818c79769524010266b9ec2908438bd526294d10c5aa8b16831862e641482044326b1ca428881955856014d10a5ee8a98a48862d6554a4110333312c3aa46527dd943d4043ab2e029a6410c6e7694d328863ab88c0aa665539cb6154c42a9ae929a6510e5653984200421fbb2a82a4431b5da52100308dee4b28868864c6354941cc636b94c9a8263b84856008720a9ae7a94a5a0c3e74d8553043263b264a80659398c52d051087ceb32264a046c725825110f0e32a8699281179ce6294740c3cc9318a790e365498732cc696b90a9a0421a358d4210810cb6cbb1a200864e6394b411030eb24a7a9021a359163c8621e4aa9292a21864d63d4b21c42d338ea4a1083479c45350d40c3ecaaa2601843d74195310822f398ca200214d9c76455332c3cc829e628865653584308423dbb2a028063555cf5244010a9ae790aa010c3e741885348326b2cc790c430f9d85450a32d1ac89906520f0d7494d3288697ba2c3a9221539ca6154c42c3ecaa18861852e7218e540830eaa2c6210210f9d26294430ccca4b086008659639805404317b2a84214218759353cc710e4aa8a94a21853475504414422eb9eca200218b95262d04308dce432a860865563584548c2d33a064908438d55161d4c208ece232c871054e7218153c8637baac520041a3591320c82093ae931c429855573182511028eba0a7a1a41d118d5254430c6cc8a8e4220667659491004236392c028a879a5496014443d1a86b10879870d54185320cb2a29cc3212219594e61d0b418eae3b2c879056970884504872aa9cc319643935886294c4087eecaa66390c5f7694c400822fbaac7a0881435d0534c920a5eeab0a842145d7614f2144316aa2c598821335ca63485308bae7314a3a062d54588540430eb22a798c41b158e2108310c9aa6b10a1a0d65720c1510c3872a4a6a9021535cb6154c40c3cc9a9e428861d5498f4108326b1aa4104211d1d56110910e1a86302a421c5d73d9642c421eba6cb19621871954310d21e1ce429a86a068d64
  | 37 => 0x4b9d85450a32e1aa921a641946e7614d52d06ab39ea328c859a5496010440e1eeaaa26419699435804344237b92c3aa2614b9d263d4910c5ecaa10840861e6494c3208347b2285192659554e618cb41a5ae52a48318e1f6554d4010386b9ca4a1483171d563d0510c3ca8b18800854c7254d32d06373b6a8a9663599c45454830a3ee6aa0a88873154546200833930ac02a0638b59352cc510a38e6aa2871045d731974148266b9cc410a41a550e6114043e1cecaa2641970d531814210b92a94a3a00818ed95544c030c74a8b00a21952d7299054442b3390c128881555c462d4d10acae531aa22068d43588430caa7394a9a9a214b9c45250940e1a86a16a099745320c9511031a3a2c2282870f5da54cc41099ae5b2663985567310a5110296b90a8a0461c5150538c51087cec2a28298dc471581320ca3dbb2a028463595c64314910c38a931e428861d5458c42c872b31aa3a08818d1516108110a6ae3312a998d4d73d4a521030eb22a629c419598551cc030a9ae629664a054d7214e32502b938084a884187d936354d10c5cc8b16a710e1d6494c50c862f3b6a8a9e434b9c45450b2087cec2a2811064e63988548428f388a8a1a61475d053ccb20c9cc7290a1a0d4d7394a21c421ebb4a828065279d85350f42c6ec830aa8906555358430042a6b90c0a98215c5c04254420e8aa728c421064f5398b31442d838282a0221c35cc5450821ae2e0192a21868d439885210f46b2264196611d9c460553328dae532c821846d721815310637396c2a9e81c55506394430cccc4a8e62204b4715903250732b14c32a621599cb5194743e1ca6a10a22152d75508420c32b31ca2200618799253c8440c6aa8b0c800861e64d4c204430eb24a798861d454d5150040a3ae7a0aa120e3a545804104272b88c099443435c85450c318beeda98408845f76d4f2144346a1ac421c85599c75494830c5ae5326a710c6d72d94400423b3b0a8a884187dd94354843c98ca990629071554547300c296ba0a510c218b590520c110c6ac8b08a09968d43588438872a29ec2a0221595c4539484087eecaa064186565358642c8786a9aa5a0081931d932944328dae432e62a061d5418d42cca1fbb4a8190414b9d36154840c38caa1a65a062e76d954210ab3b8a8428a419554c614ca21a9ae62944308535740ca510c236b90caa0c61179d8534c210b1ae62a2849047571997420c22f398c2a80852b5d2628c6218beed298400868d6350842d0657388c4a1a85475d2530c710a9ae7aa0421068c6350d428ca8f3a0c4a9e8395d9553440108baec298808864f635491004296ba6a5290618799253cc420c3ac8a98640861e5458f41cc68eba0a7984418795163d0630c38a931884886655258440043a3388a6990430f9d06548630a9ee6a90a48856471552324821e
  | 38 => 0x42c3ca8b18851954d72951438c63b3aec918a211d5c46590e20a72e0318a88862d64548528421ebacc9908618b9916214c10ccac4a8e621054d74149324c28eb98c42a2210f9d2658c72087ce9b0aa4185c57294e31c431baa4c2202211bdd8520c1108bcec29a611062e761514248296b9ca4a1483c39c14354843caae231aa31063664d47214c32ca9cc020821395c66210c21a58e4b1aa990c5c735865090b26b1aa429421939893294730cccc4a88a22064e5398b3110332a94c228881c3dc1544c832c38caa188218e2d6350a5110b2729ac41802199549610c0108f6eca80a020cb5711814210716322a499081595c76394b41cc8a5308648870f7654d4210b1baa0c2a0221175ce62d5310a5ae9a9e40104d571181324c32aa9cc3100218e552600c4108deec296628853674d4d510824fbb286290879954a6188010c5ca8b10860861e5498c4008386aa484990654b5c85450210c5ecaa10851862c6550842c4387a9a86a14434b9cb5450821a3ce7316a88854c7550e424ca1fbb2a82a261a3591320ca21c9ac7310a0a0d567398a510c316b2a8421421179d953440108beeab18840862d6494832cc63abacc218041c3551320c820c9ac7316a918d1c7454d434821ebaec8988810fdd95410f308deeca90a59868d6350842486963a2a6292218dd965150040a3ce6314a998d2c74585521030f31a8728e81359cf6150a31a6ae9a9e200865653587521028fb9aa220c8193d8c6254640a6ee2a90832052e7550842442a63aa86992419598d6115020c6aa8b08801854d754c8320421f3a4c5a984399d955244010e1ae0a9a8421746535495110326b94c7aa443595cb5494430aaae3aa4621850d7414d32c82363b2a8992419358e6214a10caac3b00a68866552984521028eb9ec32a041479cf5495020cccc4b08a91845d7598c420432729ac598e43d254d5244010a9ae7aa240105557594d1004316b22a419021179d85454c1096ae8302428864e6354842cc71b2a2c220041175db53c8510c6ae2322a31864d6398a544428f3a6a6a1a211d5c46550830c6ac8b08a50870d4354a5010e2fbb0a6202210f5d6640c820a9ae6202a42061d531854010317b20c4a8c61475d2538c52187eecaa6420847a70195321072731aa4200214b9d06394840c5aa8b166390e4e53988520430e39ac829a411bdda520c010c3aa9b1a421870d71551320cb17b22a4996838b5935294931ac8e4b1aa2104767614d51102963a2a6a16411b5db548ca21c3ea8b18808861d5458c428ca5b3a6c299483531c9534c841a5ae431ca80861d64d4c304432731aa421683395c86050510c3ea8b18849864e5358b41c871bb20c2aa26187d96544c832d1ac731683a052e76951428861fbb6a990a218755163d0731c6cc8a8e421855571d51530831caa2c010821
  | 39 => 0x86887295458021083172a4c421e431e5c06550c2199ae6302859058e731814210ab339087288618d5926194f108beeca988008667755864208792a94a2a00819354d6210f21e1aa6a92802068d43588438cb32b2cc5a0c838b59162d4c10c9acb3166318e4e654c8325061ebacc8196631b9ca650c010c6ca8b0e6598c76711815310a1eba6cb98841479d54310d10c5ac8a90a21845f7558732cc30f322a7a88411b5c86510e10c72a8b00a810c777654451c831b320a390a614b5cb645503087ce8328869043f74580514ca1eba6c2a98211d5c46054c42a3ae72968520e1f6418d54482c6ba0a6996419694d600c410e4ca4a8e802064f764c9500cba231aa488021531c9534ca10a3ae9318a78851d73151408429ab8e86a8083635d6544c8328eceda92200861e6494f21042a7398c8a96638758c6395020c5ac9296a21852e74d4a528c69ab8ec62a2219c5456014443c3ac8a98a7905557398a51102733b0a290e4193995320c93193ae8302649854c71551320cab2baca48802117dd563d0420c6aa930c600865461545300c30f322c62a0419354e6210c10c9ac7290801845d731974284316b20a4102211b9c8654c640ccac4a88a32061e64d4e53442373acc598a21475cc6055020a5ae92946518e345498442443a299064a88610f9d263d49108dce431aa1a0c3f745953048317322c429c21785c35248710c58caa1a84995677154c2188297396a8a12638715163d0932c6aa8b0881085347458d511030eb20a798a2193595538842087ae832a421861d5498c400c23b38cca190819558e51c8440ce2a2b06621861c64d8d5344316aa6c0900419354d62100208beecaa66498726545442108237396cb98c8187d954310c21e1aa8b02641964f63189544c272b8ec9190434d9d03294420a5ce8302a598cad72d85439061ebacc998861535ce5414910cc8c4a8a621052c7258d54082a738eca990651b9d85248210b1ae92926518e366494731082b3394c8a888187d516308110ccac4a8e821045e73d9621d02a6b9ca4190219398d6295221aaae6212a21046d72d9641cc334b14c02a0638d951610c020c3ca931ea40866662547310c23ab8ccb210618d9916114e20c5aa9310801054c73552324831a2a4c3a1a21555cf52544408dae4328600864d5398850d0726b1cc42a6418795163100308eae3b2c65a051d731514208726b10c429a21d1549510c430c76e9b2a200846d7610c524431aaa2c3a9061171cd6194042c9aca99065a052e7494c5244237baac421821335ce6290421a3ce7b22a910c5d7694c5204296bacc2a1085879516308010c9ac8994a21945d760c6500c30eaa2c6290218bd516294d10caac6b08a50864d6398a541070faa2c7a0e21535cb6194c40c3aa931c839846d72181548c637390c8a86631b5da54908
  | 40 => 0x1511021f3a0ca10a618b992520c8109cce3b26651943f76d50204430f324a610021475d06094c209acec1926218c77765445190f2729cc5988211b5cb6510f10a5ce4304a81865553d85430422fbb2a629e4317dd56310b21c9cc6b10a99952f7550d4288636b96cb21a434d9d35254430a68e2b02a81964d6218953d062f39ecb20e418795163d062087ce932e421854d7214c315023b388cb218218d55161080108eaed29c6218d9973d07405030e3b286a9087c3550604c832e1aa8990a21951e7418a53102aa38ac0a9885475d36194c20a5aeaa108518d2d7494a210862ebb6a6202219354e620c020a6ae3320a89961f6550f428c697390c0aa065591d95244010a3ae429a86a061d64d4c20443932a2a2900411ddd95114532c9ca6b16632065663547410c32ca9ac0298431b9db5454830a5ae8294429843d749963108327a9cc420221355c46050d30c5cc9296620851d73950438871aaa2c220041a350e62d4443c5cc8a96621845e7318950d063bbb2a228a879354d6214c41cccc4a88a21854d7414d324831b2a4c2200619358d6295221a5ae929c6510e2e64548320c22fbb2a629e859a54a6010410a3ce9302a7a0c3d769532108316b148228283475cc62950108daea3028510d2d73d954210b16aa0c4a0841395c7648c9208ece3b2c869051d74d8d53c86a739820a9021a35886250c43cc8a4b0c648843f76550530828eba4a621841339d8544c8328eeeca88a3997245414a10442a7398a9290219398e6295310a3eeaa188790d1d73990548862f3b0a699641539cb534c8218deecaa0a48846e72d855404364992c0192219314e62d051087ae9b2a658866652984400c237bb2a4294834d5c742145408ecec29a62886a5421853290732b14c3aa443a358e62d05408dce5b28800872671151420870f322a6180414b1d152508308dce5b2e63a05657214d511030eb24a79884153dd5424ca31aaae7322a22047671d97434831aaa2c3100219354e629002087aec2a0408843e7615141c4326b1aa520061475d0534c120c76cb2a2401046d72197414c2a73a8a899065715ce5288710c38caa18868846f755883004316b24c429421479d262d4d1087ee8b0ea49870d43d4b3250296b96c8aa0214d1c55450d208bcedaa2a61070d5494f20082b538642a804355dcd65c421099ae531c8318c3d74d94300832db2ca6880218b9516210c30a5ae52a48518c747159443482363aac598a210f5da54cc430e2aa831aa21851e74d4e53c870eaa4c6210218755263c8410d4a853088488665611855210f86a9e86a1443539cb534c910a9cea99064a051d7414f308421fba2c328465b14ca610c831c9ac6b14a98852d7414e5204316aa2c5218651b5cb6510d10c5ac92964318535740c1510c31632a84990839358f5294a41c5ea8b10
  | 41 => 0x22a619021639ce6150842c5ea8312a68854e7298c534431cb22a0280639518d5148430e4aa4a8c822065563544510828f3a6c3298411b9c86355210e1aa8994a21954d7294d30c42c73a4c2990651bdc96550630c6ac8a8e421046e72997410c333312a3180418b1936254910c5cc8b14a710e2d649483210393292a2a00819354f6250c20ccccb108408861e5458c428c70f322a798821999c565884208bce6302a3215667214e5110326b1ca421083535d7424c832c6aa9308a81854d7398b5408636bb2a5988211d5c4654ca40a5ae5b0aa81845f7359541883872a2a7108412bdd942d44428beeca9884206556354451902e2b94a7188631b9cb654c110a3ae72a28510e1d6494c300431ab24c229821535cc520854087eecaa0a91047571996321023dbb2a0284430fdda540c810a5ce5b0aa8184cf764c8510cb162a2c420221ca9c0545082187ae9b2e421864d6558f2188656ba0c0994438b9954288540c5ac8b10a098e1d64d4c3250316b24a590c218b55362504208bce7b0aa99062d545884388786aa6c699065475cc6055321caac730ca8995367498d510c236bb6a7108419358f5210110a9ce6304a4206396454050086573b0a4a10830f5d265c8430878e8b2a648852e7418e52cc62f398cb90a810fdd5640c83087ae8302a39966952582210438738aa8990651b5d66210f31c9aa6b1087a045e7399251c8326a98c498641595c66454843c9cc6b10a81852e72181540432729cc421e83875926394821e28c8a9aa22064d5398853d06e339086988631b1c96194243c5ca8b16a2184ce72986434ca37390c0a8c87a3591321443296cec2a2838845d75983320c71732cc990a411b5d662cc440d3287300a221d8d7215143cc296b90a8a1a61479d06294f418eae3326a09943e74994300422eb9cca208411d9c46054e42a3ce7b22a810655535843084237baac899043875526314810c9ec6a928598c3d75d9121103172a2c4204419598d6115030a3ce8302a60862e549884308317324c429841599c46054830c3ac8a98a60846c7558b434822f39ecaa16211b9cb6510d108beeca98a61043f76550428cb16b20a4106219554d6114c20c9ca7316821064d53988531030eb2cc7a0c83a398d42d4442a5ae62a2859065663984548832731ac42a2414b5d35394810cc8a4b08808862e64588534823b3b0a6a8841875526310b21c6ccb20c808845f735954244387b8286a9087879926394b10a5ae5320a98864f654c8328423b388caa1841335ce629052087ce9b2e621051e74d86531022f39cca20841175da5314321a9ce729a649055a7019253d062f3b0a8a98411b9d854509328dce5324a21852d7418e52cc6a7b9a20292211b5d66210c21a5eeba1a8510ccd73d8542086a6b94a718e21475d06054f21aace7a8ca220566721
  | 42 => 0x35cc6250120d1cc8b1e4210e8d4358843d0a37bb2a428087539cc5454810a9ae829a659062d6454852cc236b94cba182127dd943d4843cc8a4b08608854e73d85520c32632a64192214b5c85410630c9ac6a90a420c5f7654c538866ab8ec999463171cd609444287aeb3068620e4d63988540822ebb2a610021879516310810aaae2302a790e59539805110a2fbb2a7a08818b191524c440cc8cbb12428861d5418d40cc2b2b8ca410e814b5d0528c93087aedaa0831045d73195418829cb848228283c31524350932b8ae72944210f45539491004326a9ac5200418bd5162d0510a58eba1a849045d731815488726b1ea410221875926314121e2ca8a9aa21063654984520c29aba0c1288610f5d0654c810c5ac428e82a054e72d86530830eaa2c62a0414b5d25208710c5ac9a94a58846f7654c524430eaa2c620441991c96114142c68c8a8a422066665d4a21442ab38ea729e85175cc6550420a5ae829aa40851c73551434822f39ecaa0a438b15162103108bae7b2e858851c7454d438822ebb2a621021539cf6194b41c58c8a12a010d8d72951438c733b28c4880211b5cb6510e10a5ee4aa0a88845f7558c421022eb98ca21021179cf651082187ae8312a70861d6458c5204272b88c0a1641475cc54d0b20d1cc8990a219536740ca510c22ebb2a7a0841c955251c8020a3ae62a0830846d76948510c346a1ac421863539cc6494b418beeca98a79065563947411030eb22a6298419598d6115220b18e4a1a849964d6318e52043a329aa58802155dc54314530ccca4b08a021c9d74d85310c70e322a699683c594d51d0040c9ca7310a2204ad72181439061fbb2a998861539c85494c10a3ae629684a064e63148404422ebacc610021479cc6255321d2a8730e6420e1c5458f21442a6b90a7984218d551610c020a3ae9b1aa60861d64192530421f3a4cb990211b5cb6510c10c5ac8290648854e72d85530832731cc4298218b95162d0410cccc530ea81843d76950510829b3a4c5288611b5c865d0c1087ce9316a098f0d54509324c25aba0c098a21c554e51904408daeb3046410f0f65551320cb1ab24a398841c550c510c540a38eaa1e80985667190e52cc6a6b98a9210438754e61d004087ce9b0aa598535711524188266b9ec2a1241665c35450f308bce7324a21066752984404421f3a0c0a946359dc54354810c5ac8a90a49864d635484210717322a428663875954310c10a5ae92968518d4e7219153c8732292c3196218d1936154d10a3eeab028621e1e6454c53c869ab88c0aa0414b9d06354b41c5ac8b14a690c6d7298e51102b2b90a8a8861175cf6550b108dce532c860846e7218154cc72ba9ac220221535c85450c318dceda9a859061d6550c43c863b38ecb996818b5526210c3087ce931ca20862f6550a329070f3
  | 43 => 0x31001814c09800000800980c810800000040e8061000124c01600927a800006a00500e8224028000005002c01c003006000c00e036000000c0c00b6001801840a00e25f80140181e201bb5580000300028000000003000806002a00100100082bc00300080001c80ac006890496c00200101b803802c00080200000000000074c3600201e801000e00403580440160110708004056064014005c064048072000000001400200580540020028e2c05400a018844400c01600582e001a00100380940de003000000c000025063009002090703a8008000008000003000a36e00b80841400040050004000036000005c29001900d00ac03200001001e01d200800d80d800044c00580281220f900080140041f300401d800800a002bc5400c07f03d80d802e0170818004000002002001c0020850000008000003024008003c000016800400c00e012004801a017000017c00c005000804805007104a80180023420028038090080199804807000300f00000420000c823fc098000003016c026002000000001000200001e00be007029000401200001481b0008002044041c04c0a701b000004c102000001000c00302881300660070018018042001001810c6b2007012000c35a0060241b6000205e000013c00a0b300c001001601600f006c0380d6010001000000100000e23e4010000800000001d000001018c0060130000000004032000c00e006012001801403b047803400001d0080004080000004812c0120943f8801819800502380481f6027000800804604b011801c05202f04b000296b90c6aa021a359262cc7308dae53288218536741815108297396a92a46317dda5310010e1aa6a10842043c74595318832bb2ec6880218b152620c1108bae632a84085547154c5348236b90c6a8683595c65208730aace6202a22070f7154d4210a8eba6c229a210f5d06054a318bcebb26649843e761515244386ba0a6996418b9516210210c76caaa2401070e7414d3208726a9ac5a0e438b991520c8108ece2328840851d7418953c87a2b88a62922153dc9518c630cccc5308a61051d7414c3188333314a3a08410fdd954144308beeca98a72062d54d8931c861eba6ca18021539d46290d32e4aa8a88421056672d465190e2f39cca21021175d663d072196aed208818851e75d91434c317322a598821175cc6015110a3ae7b22a80843f7695331042ab38ca921a6587593530c910c5ca8b16620854c7355132086a7388a499261539d5320c910a5ae42a0849853474544514c386aa28499661879916314a10d6282b00838846d7598b41cc70eaa4c620041179ce6590810ac8eaa14428871554544310c2ab39884a8841175da531442087ce9314a31846f7558642c8333312a2200614b9d36154830ccec430aa69052d7414d32086cb3a4a6988633
  | 44 => 0x13c0cc000001005c26e0b8000014400c0b1007038800000f010800c0b000900f8084000001000800534000600c8000000006002012c15600e00a803c01200004680080b400001800080000080018008006001012000029e00007808d49ba026000044c01c0321770118004000038009403604304d8150000008005833401800c004000c0080000060000dde027000802c00c00e000800403045c004801400a0150000004000009001800c000028000005403000f0bb0150668128012802c03a02e01180b006201302c0001102021021800801000200b01d0006e7f000806c00ca1a00d84b4b00025007078800a0dd01f802c02001300081d800002500d006401600100001c800000900780c80060330010004026005020013801402d000844009000304a0030000001013000800600000600e400200000c006c00202a072004403e04a005814009602e00d837000a0ff38415a9254009095802445603b00180399000010388004000019009000402e011029809400200a0048010014007004000000804f00326e005405601303a005e00001303ac01a00200f8000006016004000011a00a01d012c0000020030004ca8081000005000600b23701f40020010000008020018002800800400a0050000000027000a05002e00001580dc0044fc0000f3c0120021ed381c1d000000c805001200000680000000b2039149401a001000800000800900c841c00c002029800c00a0af00c000401400103f005400001503c082400c00501200040a800e4190000004037000000000c0a100000000040050000028004a52000000004406e0d6003004a00f68180000040060000001bf2001000013c01200e00a197000e02a0090024180056001800807204902080f002c032033800c008001012003844e002000803805200404b000000a00b03b03b8000008018800029402f0248000006000006803800000100105d000e97e007800000809b0088014022000002000803400000605d022c0c40350dbc00a00300c837002400100000141089250000000054016007004cbfe004000800000200000200380000a100d015c01000001b8014124096004803c04c2f6000000400000000581d800e1b5014000004402c00088a0048001013802001201302f8004076000005802c000018012006c21e00000f80080007ee00000040000000000008064026014000000c09600183f800000301f00d003000000501c8000006004004434c2910018054000006007002459a00700c000001404800001a8044015000000000800f009000c00204c00700580240110018084004006043801002e04c06a800000a00024e011800a00001f800401601f004015000c0160320a6c02601e007000400400000700440000000078174004017037802400c00304382346dc44d21bb92801c0
  | 45 => 0x1d0000008084000005000c33a0940179b80010007018000800006f00b019c01200000006900e200e064018cdae004000800045e01200b0000004002006800408e124018800000c018001001400003c0b70bc40181f602800080000ec00162800000142f212dc00803400280240be003011003402800000e000455801b001800c0420000038190e9200b01000400d800207100b84cc01407001c000852b00009f804a009000001c00000e008829001019400380b40c0006001800800000908b82f419200a00d89ac034003011803801604e000017401c02000a80340a4000000809c01403d000000800e000026800c07400001580dc00004a0018004008b1a005800400000f00a81d00300020c70088022025000000001400108800441e0004001803809601b00000186a803000300200120a110286b01f600000200000560a600d0004040069009004c116011004010c008027022001400002f029a37801a0010068054000047015000000201b00080c805c075009801000003e000000401a00000e8008030008003009c0b200b004800403e00900100100a008400082fc2ae006000025800400000180002a201800780002ae03900210480de007000800005200007d8024030000002003c07e000000000001402502300ae0360080001e5c034007000004800c012003804803c00000004480003d400980040520ae01d000400a004005816414c01c0000068022001000000400e00200e002410601401a00000080000000000006487008000400035f000000022201100a803c0860210608cd065205300002c000600700000081a0a69002000c00000800d001001820002600000bc04501587842a200a533000000000b008800c08201801201a8188011003002000000000000f00d6000c2d800000400b0008694086040000002c000026031805027a001005000000001b000001c048769000000c006000065804c0120000618038004010054000c00008f000000401201900080b004606c003003406a081000001800000c001808400401c087008800800b0028000014092000000800000000b80dc0e8001053000000001a00600bc4b800c00100140141640b9022800000418301b47bc01f02d000003e00b00a801400c000004800001404000000ac0000080438014012005011015810c0270ae804c08600001e80242c201f01180c004c00300000640040070080804002000129000000c000035800400c00f0000018000000001801400805b00500d03ac02e094001404804b012000000401800000a401800000002b849005500180286ca00701d01b0034152000007007000e000035005e00001b019008c4b706f002405a097002001001801900e011800000900100e400000c000871c1ac00206d80c4008011004000806e00300200100002e200a8
  | 46 => 0x4032008003002000200100080ec00c01e00001100120050038008006004006003c00a049906800c07400300f8108000004002800001801100700080100f100601c801e02103d0048062034002809004e0860038154012000009008000406b014000411a1820000024006109000800803600c00100103900d801b80000340282ee003000019b0038000184001010803402c0007fc82fc054003007000018600007b00180424ab09c00000100020018124000009000802c03a00c0e182e001a000000007c50201300800000e015500102fc00600f0578000002b6b006807011e06f00f9f4401a00000280b1a0e00000c803401a36e00081e00180030000000002000009000400403400000c840e26200000284aa05900502c00006fb00700040000ed000805c01204a0088ae4000011001206023e00d00a007448e0e329b033802808b00001e800202d035000041a005092800c04000302b801403402103a185800e00001c0190000007003000400200000a00840c8024007004001a031000025000c000005013800000100000700d204000100000cc663003802406200e01e003400000400481d4082002252001404218b000013805600000d815c06600306802380064e703f801003c0e109d9b4809e01502380000b40390e480a4070000003805001400301d801802400723b0118012007002801415200000e8018022002001800400218102f820c0c8000051800800c022000001404a00100d8010010011003809800000502d806c00ab6702c826c016011001031818000000b804c04e0260d0003001602102c00f00000ff020001c0000410450004014000000030c00000500f007406a004031800003800b1c101a006802e0020230002007000801000005d001008803c01b01180fc0000110e20044fd2000380805c0ec02e002800001800016a016402c00f0181b5802400f074021c0023a200102dc002090013842800800c000801004419a073806400000a00e8004000005004015819a27b93ea0f00e80ba00d002000203c000001c020000065808800a0000018054034019004032001a00101f000401c00c00300180d60010028005f2803a000045c000001027906801a01106280080000e203b82ec0222a70220000000063187000001000a00000780b2000031801000a0b400000f002a02f004800c00000700080080029b3020800400001100a062400009503a01f8012002015801c02e0aa0010000016000009800c054041001002400000635a81dc0000010080078036037006808c462003041095024004200280c0000023004808406a007000801c080008006001800e00300100041744ba0008014048181055800026008900280008a60050a3000802e00301e0028000070011002c01a054003806807a19100180140000090068094002
  | 47 => 0xaa0108000072008803c03c0d400e06e008a002000001400800046980200020021138050034000000000000800702f80440b800000880240020200028028004002034800c04600e004000000a00e00000080100000188014078061001007002000a004001c07a00f0219f185cc03b02606b80501ab03900080060410010174000065001800c07c060005803400c04c00f8038e96000000094c00c00d006005c0200180050be193c0040050004004002000833c05802e00600802060000988004006000007000000200e000801005203d0560000000001004819401601a001038400005305b8018058004005800000201f025806804c03e04a83c804c0020080958026007004802c01000a003002422e00a000110805c000000001002801000280680000090040114042046015811803a004000
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x5450c31d05735084294440c49625c06214d10a0d841d93254032c19635c06315110a0d8494d6210c10c0d75591320ca41a0f8654d4214042e046418d5244010a0d821914354031e0a535096014442c0d75591320c810c0d735886295010b0681dd95350842c49635c06314910b068198d4354843a0e869c55350842a0d8694d4210810a0d8550d6210e2190d831d1525081090d829cf5450d10a0d82195430c540e05544ca6114032c0c75591320c910949801d5424c831d05435c84354420e05535096114042a0e861c1544c83290d831c95450810a0c86551434c92090d839d35250b10d05735084254420a0e86dc5544c832a0d831914254021d05545c4604c832c0f7558d4210b31a0d8694d4210b2190d829d35350d2190d831c95450a10c0f645ce64d4910c0f75591320cb4190c87551604c832d05711c5544c832e09544ca6014432a0d8550d6210f21c0d7650c4394840a0d821cd6414d20a0d8614d4210910e0554584614c832a0d8418d3254021a0d8298d4394740e11539856010440a0c8550d6210d20a0d8654d421082090f87553614c832a0c8558d4210910a19801954350831a0d821516310910b06819914354843d05711c54354843c0d645ce520ca41c0d7558d4210a31b06819d15350842a0e86dc54354843d42715c0534c821b07815c15350842c0d735ca64d4e21c16769c45450c3190d841c9534ca10a8481591320c941b05819cd544c83290f8754e6150842c0d7458c5210910949801d5434c821a0d869513214432c0d73d8a62d511090d849c7654c832d09739c05450821a0d839516210f2190c8754d4350920d22715c05450821c0d7558d4210830b0481551434c920a0f8550d6210e21a0d831c96414930c0e75591320c940a0d829516310810a8681d9143cc932d05549c4604c832b04815c14354843a0d8654d421081090d859cc605084281c875954310d2090d829c76550c43c0d744c86154032a0d86951320c82090d841cd524c810c0d7454c624c320e095350a6014442a1980195434c841a0d831954208540a0e86dc5535084281e879954310e21a14815954310d20c0f735096094442a0d8694d4210820e05535846150842a0d839516210c10b04815c15350842926819d95350842949831c12154021c0d645cc6454810a0f8650d5214043d09745c0534c821a0e869c54354843d09735c05450821d05541c5604c832c0d735886255010c0d435c86154043a0d83d954210810a0f8558d4210820a0d8694d4214442c0d745886294c1090f8750e6154843a0d8414d620c520a61859856008420a0d831d94254042a0f865c14354843a0d84195320c520c0d545ce629072090c8754d6050842e055350a6114042a0d821516310930c0c7550d6210d21c0e7558d421093082c875954210930a0d839516210c20
  | 1 => 0xc0d645c8530c940c0f7550d6210f31a0d84dd93294432c0c7550d6210d10a0c865c15350842c0d635c86395010a5185985600c430a0d82151631053090d829cf5450f10929801d74350821c19645c06414d10a0d8315162d0120a0d831c96494a31c0d545c8635033090d849cb534c91090d821d15350c1090d859d3614c832a2980195424c841c0d7458e5210830c0d645ca530cb41c0f75591320c81090d839cb5450910a0d8550d6210c20a24815954210930a0d83991429442182e879954210a31a0d8218d4354041d05744c83254430929801d54350821c0d645cc520854090d849cb534cb1090d829d35350d10c25641c55214930c0e7558d421091090f845c3654c832c0f7558d4210810a0f85591320cb21c0d7650c4394b41c0d635c86315110a0d86951320cb21a0d829516310a31c0f7550d6210c30b06819cd544c832e055418c6244010c2a765c05450821c14761915344010c0d545cc6250320a0d821954310530b05811c15350842d0553dc56050842b05819d15350842c0d7558d4210b31d05744c8329444090d859cf6150842c0d745886214d10991841c1314c11090d839c76550842c28755096010910a0d83d954210820a0d84d95320c82090f87552614c832a0f86d51320c910a0e8550d6210d20c0f635ca63d5110b0581991435484390f825c36550c43c187550d6010d10a0f8558d4210b21a0c865c14354843c0d645ca530c810c4a765c0534c821c0e75591320c910a0d831894254041a0d831516210d20a0f8558d421081090d849cb534c82190d859cb6150c43c0d75591320c840a0d841953208530c0d645ce520cb41c0f7558d4210830a0d84195320c421a0d8215163d0130a0f8550d6210c10e09435496014443b05819d95350842c0d7458c6314910d05744c8325442090e87551604c832a0d83d954210a10a0d86151320c910c0f7650d5214043b05819d94354843b06811c15350842a0d84d95320ca10a0d86951320c830c0d7458c6354810e046454c6244010c24761915244010d05435c84354430a0f8650d52d4443a0f8550d6210f21c0f75591320c840a0d839516210621a148550e6110d1090d849cf524c910d05431c56054843b05819c95350842c0d7650e5214443c0d545ca6390431e05435496114043c0f765513214032d05735084254430b0681dd9544c832c0f7550d6210c40a0d86551320c810c0f7654d42d4442b0581dd95350842a0d829516310b31c0f7550d6210c10a0e861c14354843a0d82d954310c10a0d841893254031c0d7650c4394810d05531c56050842c0d735c86454d20c0d7458e5210b3190c8750d6054843c0d645ca530ca41a0d831954210b10c0d545ca639073090f8754f6150842c0f7550d6210f41c0d645ce520c810d05435c84394440a8681d91428c932c1a765c
  | 2 => 0xc14154041a0d825516310820a0c865c1544c832d05435c84394430a0f85591320cb31a0d839954288740a0d8414d6210d20c0d7650c4394b31c0f744c96094432e0a544c96014432a0d84995328c720a24815516215130d05735084294430a0d82995438c740d05744c83294420929841c12154021c447618d5244010b21811c14254042c0d7650c439483090e8754d6050842c0d75591320cb41c0d761d9544c832a0f865513214032e21529856010440e0543584615484390f8754c6050842a0d8494d6210e21a0d839516210e21b0481551424c930b06819c9544c832c0d74d8e63d491090d859d0604c832a0f86d4d4210910c0d7458e5210810c0d645c86414d10e094354a6014443a1681dd94354843c0d7458c5208530a0c8654d4350920c0d645c86494c10e41539856008420a0c85591320c910a0d839894294740c29625c06215110d0543dc56054843a0d84195320c910c0d7458e5210a3184c87595320c940b04815c1544c832a19801954310e21c29645c06414910b05811c1544c832a448154d6214d40a0e869c5544c832a0f8558d4210840a0d821d94354043b0681dd94354843b06819d9544c832a0f8558d4210b41c0c7558d4210910a848158d421093184e87995320ca419a1841c12148110a0d83991429472090f8750c6054843a44854ca610c91090f835c36550842a0d8494d6210c2090d841c9534c810a4481595320c940d05435c84354440d05735084254440a0d849893294730a0d829516310830d0a735c05450821c0d645c8530c910d0554dc5604c832c0d645ce520c840c0d645c86454c10a248655062440109a1821c14150110c0d7650c4354810c0d7558d421081090c87551434c920e09544c96014432a0d831516210d1090d829d35350f10b05811c14354843e05544c96114032b05819d9544c832a0d8414d62cc120a0d821954310d10c0d645cc520c910a0d84195320cb10a448654c6244010949801d6434c821a0d8494d6210f21d05735084294420d05435c8439442090d821cd5450e10c0f645ca64d4d10b06819c9535084290d839cb5450821949821c13154031c48754c9600c910a0d84d95320c810a31859856010440a0d8498d3294421b048154d4350920946819d9544c832c0f7654d4214042c0d7454e628c421c0d645c8530c540a0d839954290720a0d831954210910e21549856008420929821c14154041a0e861c1535084290d839d35250910b0581dd9544c832b06819d95350842e4152985600c430d09749c0534c82190d831d15250a10d05535c46050842c0d645cc520c940a0d8498d5288730b05819c9544c832d09725c05450c31b11811c14354043b07815c1544c832e1154985600c430c85431c56210d21a0d82d954310d20d0a745c0534c821d09729c05450c31a0d86551320c82
  | 3 => 0x6804020102828000009008040c00014340d0a0185624078600c0001800ac020080004310d8580200000002e001c8040000010082e80008040000010001414408140c030500c0000030000200050180001390642000030105a14030101e090083408010700004080680002013504400070683c02010480042010b014020f000141e01030180209010000000118b81400062b40804000400c030701008040a8002002311147e050003400100080000071000008041d01c08230099800030d0841a07000000226048200000010001a6f0002c0e00008000200003180a47002602e0d0003048070080044000980c368e00800001c040000400020009c080000820140682400030000c0200028000002002440004028041a01007380a012b000380aa0d82d954310e10a0e8550d6210d10a0d829516310631b058198d4354843c0d645c9530c820c0d645cc6494810a0d83dd94294442c0d635c86355010e054354a6114043a0d82995439073090d8754e6150842a0d8494d620c621c45631c5521494090d839cb5450b1090d841cd524ca10919841c13154031d05744c83294430a0d86951320cb31a0d82dd94394443a0d849953288730b07815c14354843a0f85591320c830a0d8550d6210c10a0d8694d4210840a0d831516210520a0d8498d3294720c0d745886254c1090d829cf5450d21e09535096014442a0d8414d6210d10a14865506344010d05435c46054843c0d7454e628c720d05711c5535084290d821d15350e109c1831c12148110c0d545ce6290421c0d7458c6394810b0681d954350932a0d8319542104219c1821c1314c110a0d839915288740c0e765c85450f32c0d74d8a62d4d10c0d735886215110a0c8550d6210d1090d849cf524cb10991831c14150110a0f85591320c810a0d8694d4210b41b41811c1325403290f8750f6154843d05539c46050842a0d821cd6494e2190d87552614c832c15641c55314d20a0d831954210520c0d645cc6414910b0581dd94354843c0f7655132d4432c0d645ca530c840a0d86951320c810c0e7650c43d4910c0d43dc9609444390d821cd5450c10c0d7458c5210930c0d7650c4314910d05439c46054843a0f8550d6210c20a0f85591320c82090d859c86050c43b06819d94354843a0d869c54354843b06811c14354843e09439496014443d05744c8325444090f87550604c832a0d821954310f10b06811c1544c832a0d829914394730d0a725c05450c31c0d735086154042a14815516315120a0d825954310c20a248550a6110910a0d82991538c740d12715c05450c31919831
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 40
  | 6 => 1895
  | 5 => 11087
  | 4 => 7262
  | 3 => 497
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 8 => packedAt s5K8 (i*5) 5
  | 7 => packedAt s5K7 (i*16) 16
  | 6 => packedAt s5K6 (i*27) 27
  | 5 => packedAt s5K5 (i*38) 38
  | 4 => packedAt s5K4 (i*49) 49
  | 3 => packedAt s5K3 (i*60) 60
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 8 => 2*((h/1+packedAt s5K8 (5+(h % 1)*1) 1) % 1)
  | 7 => 2*((h/27+packedAt s5K7 (640+(h % 27)*6) 6) % 40)
  | 6 => 2*((h/666+packedAt s5K6 (51165+(h % 666)*11) 11) % 1895)
  | 5 => 2*((h/3695+packedAt s5K5 (421306+(h % 3695)*14) 14) % 11087)
  | 4 => 2*((h/2434+packedAt s5K4 (355838+(h % 2434)*13) 13) % 7262)
  | 3 => 2*((h/256+packedAt s5K3 (29820+(h % 256)*9) 9) % 497)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfc3ffff87ffffff03f0fe1fff87ffffe88f1ff
  | 1 => 0x7fc1f0ff83e1f0ffc7f0fe1c3f870e1f774e93
  | 2 => 0x7ffe00fffc01ff1ff800ffe03ff80fe1878f1c
  | 3 => 0x800000fffffe001fffff00003ffff001f80fe0
  | 4 => 0xffffff000000001fffffffffc0000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x4000008000000000001002400090200001025
  | 1 => 0x89461111942a102c31062089882245c334692
  | 2 => 0x510caaa228d548355888b5412d5049c5858b18
  | 3 => 0x43a94cc452906a59adaa11023664e089d80dc0
  | 4 => 0x6231888763198c9e36ccd99384408111eee000
  | _ => 0
def s5Atlas : Atlas := ⟨8,rawDecor 31 s5Pos s5Neg, 0xeeeaeaa8eeeaeaa8eeeaeaa8eeeaeaa8eeeaeaa8eeeaeaa8eeeaeaa8eeeaeaa8eeeaeaa8eeeaeaa8eeeaeaa8eeeaeaa8eeeaeaa8eeeaeaa8eeeaeaa8eeeaeaa8, s5N, s5R, (fun _ _ => 0), s5I, []⟩
end PEqualNP.Outside.L_meta_36753
namespace PEqualNP.Outside.L_meta_36753
open PEqualNP.Outside.L_meta_36753.Model
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
  | 0 => 0x1fffe03f80ff03fffe07ffffff44e71e88f1ff
  | 1 => 0xe0f83fc3ff07fc1e0ff83c1c1fbb5ae9774e93
  | 2 => 0xff003ffc0007ffe00fffc01fe0c39cf1878f1c
  | 3 => 0x3ffffff800000fffffe000fc1f01f80fe0
  | 4 => 0x3ffffffffffff000000000ffe001fff000
  | 5 => 0xffffc000000000000000000000fffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x1080000000800220000440400000002001025
  | 1 => 0x20d082c1b1034414268828485e194a68334692
  | 2 => 0x5a01356c0845ab404b568093c2c294b1858b18
  | 3 => 0x84239b6dad021008de733c084ec1f01d80dc0
  | 4 => 0x10843e3b6ce6f399e042010108f7e001eee000
  | 5 => 0x9ce790207080c2110184220210ffffdc000000
  | _ => 0
def gbRaw : List Sig := (rawDecor 63 gbPos gbNeg).map Prod.fst
def gbPools : List BoundPool := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 7, 0, gbRaw),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 7, 0, gbRaw),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff, 7, 0, gbRaw),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff, 9, 0, gbRaw)]
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeaeaeeeaeaa8eeeaeaeaeeeaeaa8eeeaeaeaeeeaeaa8eeeaeaeaeeeaeaa8eeeaeaeaeeeaeaa8eeeaeaeaeeeaeaa8eeeaeaeaeeeaeaa8eeeaeaeaeeeaeaa8, gbN, gbR, gbH, gbI, gbPools⟩
end PEqualNP.Outside.L_meta_36753
namespace PEqualNP.Outside.L_meta_36753
open PEqualNP.Outside.L_meta_36753.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 6 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 14 := bs0_4_0
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
theorem bs2_3_0 : Interval s2Atlas 3 0 84 := block_range (n:=84) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 84 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_96 : Interval s2Atlas 4 96 90 := block_range (n:=90) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 186 := (concat bs2_4_0 bs2_4_96)
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 68 := block_range (n:=68) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 68 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_96 : Interval s3Atlas 4 96 33 := block_range (n:=33) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 129 := (concat bs3_4_0 bs3_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 45 := block_range (n:=45) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 45 := bs3_5_0
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
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
  · exact alls3_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 68 := block_range (n:=68) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 68 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_96 : Interval s4Atlas 4 96 33 := block_range (n:=33) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 129 := (concat bs4_4_0 bs4_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 45 := block_range (n:=45) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 45 := bs4_5_0
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
theorem bs5_3_384 : Interval s5Atlas 3 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_480 : Interval s5Atlas 3 480 17 := block_range (n:=17) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 497 := (concat (concat bs5_3_0 (concat bs5_3_96 bs5_3_192)) (concat bs5_3_288 (concat bs5_3_384 bs5_3_480)))
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
theorem bs5_4_6720 : Interval s5Atlas 4 6720 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_6816 : Interval s5Atlas 4 6816 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_6912 : Interval s5Atlas 4 6912 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_7008 : Interval s5Atlas 4 7008 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_7104 : Interval s5Atlas 4 7104 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_7200 : Interval s5Atlas 4 7200 62 := block_range (n:=62) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 7262 := (concat (concat (concat (concat (concat (concat bs5_4_0 bs5_4_96) (concat bs5_4_192 bs5_4_288)) (concat (concat bs5_4_384 bs5_4_480) (concat bs5_4_576 (concat bs5_4_672 bs5_4_768)))) (concat (concat (concat bs5_4_864 bs5_4_960) (concat bs5_4_1056 (concat bs5_4_1152 bs5_4_1248))) (concat (concat bs5_4_1344 bs5_4_1440) (concat bs5_4_1536 (concat bs5_4_1632 bs5_4_1728))))) (concat (concat (concat (concat bs5_4_1824 bs5_4_1920) (concat bs5_4_2016 bs5_4_2112)) (concat (concat bs5_4_2208 bs5_4_2304) (concat bs5_4_2400 (concat bs5_4_2496 bs5_4_2592)))) (concat (concat (concat bs5_4_2688 bs5_4_2784) (concat bs5_4_2880 (concat bs5_4_2976 bs5_4_3072))) (concat (concat bs5_4_3168 bs5_4_3264) (concat bs5_4_3360 (concat bs5_4_3456 bs5_4_3552)))))) (concat (concat (concat (concat (concat bs5_4_3648 bs5_4_3744) (concat bs5_4_3840 bs5_4_3936)) (concat (concat bs5_4_4032 bs5_4_4128) (concat bs5_4_4224 (concat bs5_4_4320 bs5_4_4416)))) (concat (concat (concat bs5_4_4512 bs5_4_4608) (concat bs5_4_4704 (concat bs5_4_4800 bs5_4_4896))) (concat (concat bs5_4_4992 bs5_4_5088) (concat bs5_4_5184 (concat bs5_4_5280 bs5_4_5376))))) (concat (concat (concat (concat bs5_4_5472 bs5_4_5568) (concat bs5_4_5664 bs5_4_5760)) (concat (concat bs5_4_5856 bs5_4_5952) (concat bs5_4_6048 (concat bs5_4_6144 bs5_4_6240)))) (concat (concat (concat bs5_4_6336 bs5_4_6432) (concat bs5_4_6528 (concat bs5_4_6624 bs5_4_6720))) (concat (concat bs5_4_6816 bs5_4_6912) (concat bs5_4_7008 (concat bs5_4_7104 bs5_4_7200)))))))
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
theorem bs5_5_11040 : Interval s5Atlas 5 11040 47 := block_range (n:=47) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 11087 := (concat (concat (concat (concat (concat (concat bs5_5_0 (concat bs5_5_96 bs5_5_192)) (concat (concat bs5_5_288 bs5_5_384) (concat bs5_5_480 bs5_5_576))) (concat (concat bs5_5_672 (concat bs5_5_768 bs5_5_864)) (concat (concat bs5_5_960 bs5_5_1056) (concat bs5_5_1152 bs5_5_1248)))) (concat (concat (concat bs5_5_1344 (concat bs5_5_1440 bs5_5_1536)) (concat (concat bs5_5_1632 bs5_5_1728) (concat bs5_5_1824 bs5_5_1920))) (concat (concat (concat bs5_5_2016 bs5_5_2112) (concat bs5_5_2208 bs5_5_2304)) (concat (concat bs5_5_2400 bs5_5_2496) (concat bs5_5_2592 bs5_5_2688))))) (concat (concat (concat (concat bs5_5_2784 (concat bs5_5_2880 bs5_5_2976)) (concat (concat bs5_5_3072 bs5_5_3168) (concat bs5_5_3264 bs5_5_3360))) (concat (concat bs5_5_3456 (concat bs5_5_3552 bs5_5_3648)) (concat (concat bs5_5_3744 bs5_5_3840) (concat bs5_5_3936 bs5_5_4032)))) (concat (concat (concat bs5_5_4128 (concat bs5_5_4224 bs5_5_4320)) (concat (concat bs5_5_4416 bs5_5_4512) (concat bs5_5_4608 bs5_5_4704))) (concat (concat (concat bs5_5_4800 bs5_5_4896) (concat bs5_5_4992 bs5_5_5088)) (concat (concat bs5_5_5184 bs5_5_5280) (concat bs5_5_5376 bs5_5_5472)))))) (concat (concat (concat (concat (concat bs5_5_5568 (concat bs5_5_5664 bs5_5_5760)) (concat (concat bs5_5_5856 bs5_5_5952) (concat bs5_5_6048 bs5_5_6144))) (concat (concat bs5_5_6240 (concat bs5_5_6336 bs5_5_6432)) (concat (concat bs5_5_6528 bs5_5_6624) (concat bs5_5_6720 bs5_5_6816)))) (concat (concat (concat bs5_5_6912 (concat bs5_5_7008 bs5_5_7104)) (concat (concat bs5_5_7200 bs5_5_7296) (concat bs5_5_7392 bs5_5_7488))) (concat (concat (concat bs5_5_7584 bs5_5_7680) (concat bs5_5_7776 bs5_5_7872)) (concat (concat bs5_5_7968 bs5_5_8064) (concat bs5_5_8160 bs5_5_8256))))) (concat (concat (concat (concat bs5_5_8352 (concat bs5_5_8448 bs5_5_8544)) (concat (concat bs5_5_8640 bs5_5_8736) (concat bs5_5_8832 bs5_5_8928))) (concat (concat bs5_5_9024 (concat bs5_5_9120 bs5_5_9216)) (concat (concat bs5_5_9312 bs5_5_9408) (concat bs5_5_9504 bs5_5_9600)))) (concat (concat (concat bs5_5_9696 (concat bs5_5_9792 bs5_5_9888)) (concat (concat bs5_5_9984 bs5_5_10080) (concat bs5_5_10176 bs5_5_10272))) (concat (concat (concat bs5_5_10368 bs5_5_10464) (concat bs5_5_10560 bs5_5_10656)) (concat (concat bs5_5_10752 bs5_5_10848) (concat bs5_5_10944 bs5_5_11040)))))))
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
theorem bs5_6_1824 : Interval s5Atlas 6 1824 71 := block_range (n:=71) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 1895 := (concat (concat (concat (concat bs5_6_0 bs5_6_96) (concat bs5_6_192 (concat bs5_6_288 bs5_6_384))) (concat (concat bs5_6_480 bs5_6_576) (concat bs5_6_672 (concat bs5_6_768 bs5_6_864)))) (concat (concat (concat bs5_6_960 bs5_6_1056) (concat bs5_6_1152 (concat bs5_6_1248 bs5_6_1344))) (concat (concat bs5_6_1440 bs5_6_1536) (concat bs5_6_1632 (concat bs5_6_1728 bs5_6_1824)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_7_0 : Interval s5Atlas 7 0 40 := block_range (n:=40) (by decide +kernel)
theorem alls5_7 : Interval s5Atlas 7 0 40 := bs5_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_8_0 : Interval s5Atlas 8 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_8 : Interval s5Atlas 8 0 1 := bs5_8_0
theorem alls5 : ∀ k ≤ 8, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 6 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 9 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeaeaeeeaeaa8eeeaeaeaeeeaeaa8eeeaeaeaeeeaeaa8eeeaeaeaeeeaeaa8eeeaeaeaeeeaeaa8eeeaeaeaeeeaeaa8eeeaeaeaeeeaeaa8eeeaeaeaeeeaeaa8
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
  have q0 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f : Sig) 7 :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have q1 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff : Sig) 7 :=
    slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
  have q2 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff : Sig) 7 :=
    slice_correct (ms:=fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds4 certs4)
  have q3 : Slice true (roots gbAtlas) (target gbAtlas) (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff : Sig) 9 :=
    slice_correct (ms:=fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds5 certs5)
  have pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p :=
    List.forall_iff_forall_mem.1 (show List.Forall (fun p => ValidPool true (roots gbAtlas) (target gbAtlas) p) gbPools from ⟨build_valid q0 [] rfl, build_valid q1 [] rfl, build_valid q2 [] rfl, build_valid q3 [] rfl⟩)
  have low := boundgb certgb allCuts pv
  have lift := lift_ok (u:=true) (ms:=fixRows 0 0) (raw:=fullRoots) (T:=fullWord) (xs:=[]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 0 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372970 * 2 ^ 32 + 4008372904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36753.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,4]⟩,⟨.or,[3,5]⟩,⟨.or,[4,7]⟩,⟨.or,[2,3]⟩,⟨.and,[1,6]⟩,⟨.and,[8,9]⟩,⟨.or,[2,8]⟩,⟨.or,[1,12]⟩,⟨.and,[0,13]⟩,⟨.and,[10,11]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372970 * 2 ^ 32 + 4008372904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372970 * 2 ^ 32 + 4008372904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36753

open PEqualNP.Outside.L_meta_36753 in
theorem PEqualNP.Outside.L_meta_36753 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372970 * 2 ^ 32 + 4008372904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372970 * 2 ^ 32 + 4008372904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
