import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, children closed at the parent by
-- restriction pools (closeChild of the model), and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37247.Model
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
noncomputable def anyEq2 (m c d : Sig) (l : List Sig) : Bool :=
  @List.rec Sig (fun _ => Bool) false (fun v _ ih => eqF (masked d v) m || (eqF (masked d v) c || ih)) l
theorem anyEq2_eq (m c d : Sig) (l : List Sig) : anyEq2 m c d l = (anyEq m d l || anyEq c d l) := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change (eqF (masked d v) m || (eqF (masked d v) c || anyEq2 m c d vs)) =
      ((eqF (masked d v) m || anyEq m d vs) || (eqF (masked d v) c || anyEq c d vs))
    rw [ih]
    cases eqF (masked d v) m <;> cases eqF (masked d v) c <;> cases anyEq m d vs <;> cases anyEq c d vs <;> rfl
noncomputable def availF (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) : Bool :=
  eqF (masked d a) zero || eqF (masked d a) d ||
    cond u (anyEq2 (masked d a) (masked d (neg a)) d pool) (anyEq (masked d a) d pool)
theorem availF_eq (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :
    availF u d pool a = availableB u d pool a := by
  cases u
  · simp only [availF,cond_false,availableB,eqF_eq,anyEq_eq,Bool.false_and,Bool.or_false]
  · simp only [availF,cond_true,anyEq2_eq,availableB,eqF_eq,anyEq_eq,Bool.true_and,Bool.or_assoc]
noncomputable def memF (x : Sig) (l : List Sig) : Bool :=
  @List.rec Sig (fun _ => Bool) false (fun v _ ih => eqF x v || ih) l
theorem memF_eq (x : Sig) (l : List Sig) : memF x l = l.contains x := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change (eqF x v || memF x vs) = _
    rw [ih,eqF_eq,List.contains_cons]
noncomputable def subF (a b : List Sig) : Bool :=
  @List.rec Sig (fun _ => Bool) true (fun v _ ih => memF v b && ih) a
theorem subF_eq (a b : List Sig) : subF a b = a.all (fun x => b.contains x) := by
  induction a with
  | nil => rfl
  | cons v vs ih =>
    change (memF v b && subF vs b) = _
    rw [ih,memF_eq,List.all_cons]
noncomputable def sameWordsF (a b : List Sig) : Bool := subF a b && subF b a
theorem sameWordsF_eq (a b : List Sig) : sameWordsF a b = sameWords a b := by
  simp only [sameWordsF,sameWords,subF_eq]
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
    (links (keySet (choiceVal op::rest))).any (sameWordsF (choiceVal op::rest))

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,anyP_eq,sameWordsF_eq,Bool.or_eq_true,List.any_eq_true] at h
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
def M152 : Nat := 2^152-1
theorem not152 (x : Bits) : (~~~x).toNat = x.toNat ^^^ M152 := by
  rw [BitVec.not_def,BitVec.toNat_xor,BitVec.toNat_allOnes,Nat.xor_comm]
  rfl
def natBv (d x y : Nat) : Nat :=
  cond (Nat.beq d 0) (x &&& y) (cond (Nat.beq d 1) (x ||| y)
    (cond (Nat.beq d 2) (x &&& (y ^^^ M152)) ((x ^^^ M152) &&& y)))
theorem natBv_eq (d : Nat) (a b : Bits) : (bv d a b).toNat = natBv d a.toNat b.toNat := by
  match d with
  | 0 => simp [bv,natBv]
  | 1 => simp [bv,natBv]
  | 2 =>
    rw [show bv 2 a b = a &&& ~~~b from rfl,BitVec.toNat_and,not152]
    rfl
  | n+3 =>
    have e : bv (n+3) a b = ~~~a &&& b := by
      unfold bv
      rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]
    rw [e,BitVec.toNat_and,not152]
    rfl
def natCol (d : Bool) (x y : Nat) : Nat := cond d (x &&& (y ^^^ M152)) (x ^^^ y)
theorem natCol_eq (d : Bool) (s : Bits × Bits) : (column d s).toNat = natCol d s.1.toNat s.2.toNat := by
  cases d
  · rw [show column false s = s.1 ^^^ s.2 from rfl,BitVec.toNat_xor]
    rfl
  · rw [show column true s = s.1 &&& ~~~s.2 from rfl,BitVec.toNat_and,not152]
    rfl
def covFail (d : Bool) (t : Bits) (op : Nat) (a b : Decor) : Bool :=
  !(Nat.beq (t.toNat ||| natCol d (natBv op a.2.1.toNat b.2.1.toNat) (natBv op a.2.2.toNat b.2.2.toNat)) M152)
theorem covFail_eq (d : Bool) (t : Bits) (op : Nat) (a b : Decor) :
    covFail d t op a b = ((t ||| column d (dbin op a b).2) != BitVec.allOnes 152) := by
  have e : (t ||| column d (dbin op a b).2).toNat =
      t.toNat ||| natCol d (natBv op a.2.1.toNat b.2.1.toNat) (natBv op a.2.2.toNat b.2.2.toNat) := by
    rw [BitVec.toNat_or,natCol_eq]
    simp only [dbin,natBv_eq]
  unfold covFail
  rw [←e]
  generalize (t ||| column d (dbin op a b).2) = X
  by_cases h : X = BitVec.allOnes 152
  · subst h
    decide
  · have h3 : X.toNat ≠ M152 := fun q => h (BitVec.eq_of_toNat_eq (by rw [q,BitVec.toNat_allOnes]; rfl))
    have h4 : Nat.beq X.toNat M152 = false := by
      cases hb : Nat.beq X.toNat M152
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) h3
    rw [bne_iff_ne.mpr h,h4]
    rfl
noncomputable def allD (f : Decor → Bool) (l : List Decor) : Bool :=
  @List.rec Decor (fun _ => Bool) true (fun v _ ih => f v && ih) l
theorem allD_eq (f : Decor → Bool) (l : List Decor) : allD f l = l.all f := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change (f v && allD f vs) = _
    rw [ih,List.all_cons]
def opsAll (u : Bool) (f : Nat → Bool) : Bool := f 0 && (f 1 && cond u (f 2 && f 3) true)
theorem opsAll_eq (u : Bool) (f : Nat → Bool) : opsAll u f = (opsOf u).all f := by
  cases u <;> simp [opsAll,opsOf]
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
def quickPairN (c : NodeContext) (a b : Decor) (op : Nat) : Bool :=
  if Nat.blt c.1 c.2.1 then
    covFail (!c.2.2.2.1.2) (takeTwo c.2.2.2.1.1 (column (!c.2.2.2.1.2) a.2) (column (!c.2.2.2.1.2) b.2)) op a b
  else Nat.blt c.1 (c.2.1+1) &&
    (covFail (!c.2.2.2.1.2) (takeOne c.2.2.2.1.1 (column (!c.2.2.2.1.2) b.2)) op a b &&
     covFail (!c.2.2.2.1.2) (takeOne c.2.2.2.1.1 (column (!c.2.2.2.1.2) a.2)) op a b)
theorem quickPairN_eq (c : NodeContext) (a b : Decor) (op : Nat) :
    quickPairN c a b op = quickPair c a b op := by
  simp only [quickPairN,quickPair,covFail_eq]
noncomputable def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    allD (fun b => opsAll ctx.2.2.2.1.2 (fun op => quickPairN ctx a b op || testPair ctx a b op)) bs
noncomputable def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,allD_eq,opsAll_eq,quickPairN_eq,List.all_eq_true] at h
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


end PEqualNP.Outside.L_meta_37247.Model

namespace PEqualNP.Outside.L_meta_37247
open PEqualNP.Outside.L_meta_37247.Model
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

def SBf (j : Nat) : Nat := [7, 7, 5, 7, 6, 8].getD j 0

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

end PEqualNP.Outside.L_meta_37247

namespace PEqualNP.Outside.L_meta_37247
open PEqualNP.Outside.L_meta_37247.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x400010020c075d0004c20ca000117701041680140087ff32fe41fc43fd31ff43fc10be43bf42ff31ff42ff41fd40bc40fe20ff20fc32fd21be40fd42fe32bf41fe30fe42fe10fd41fd43fe43fc31fe21fe40ff10bc43fc40fc42fe31fd30fc41ff30ff21ff40fd20bd42fd10fd32fc21fc20fc30bd41
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x10ec1801040804504c0c442818000014180858002455dc0014085c0c080c040800a4080cb4680400047ce4285c4c14101c0120d00000b018181e7ca7a14794e409faa6633e509027aa521cfd52109faa2213f54cca78a9084f950329ea96833d5408278a9996754e40afa9a413c544827ca9885794c209faa2635c534827aa321e714d419eaa4653f54883ca4210cf95320ba28a413e53902d8a4985754e40ce21c639c430ca7ca9985754e21b7a92619c430c67ea8904f54443dba8a833c5350aeaa3195dd45209f2a6433d5210e78a0a16714d42af29e433e548867aa9984f141419f2988175510833887196794e40af29c813d5210278a8995d145309f29e833d548c67aa32057d4d109f29c871c5350a7aa890cf547429e2a4413d54c42daa518cf544409e2a2613d5408678a898cf15331ae29a859f5350aeea2984f950109faa2653f544c27ca021cf952319f2a0855e53042b8a6885754c20b7294633e548c27ea2a16794c43bb28c653d54c82d8a4885d944209e2a2215c535073887984f952328e29a839f535067ea4a0cf550329f2a0435d530427aa990cf54a40af29c43ba501027aa9184f943419e2a0613e540827aa8086710d30b7290216d520427ca890cf14d41afa9a833d54906bea6a14f943429eaa4436f524427ca0205754f219f2a0633d5490a7ea8184f55031d7a92853e541067ca121cf94c43
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x150004400400000008940008000182c200001280008718d54c821c63553108798f540c21e63d52208d58454cca2d62150308b58854cc61c63547428d584540c21e6394342c510e518ca1c6354b41c510c514c30c4394a318798f548421e63943418718d544861c6354840a5584430c70c43149308718d5408638605512187594430c68d6210c3287594430ca1c6354440
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 134
  | 3 => 26
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (i*5) 5
  | 5 => packedAt s0K5 (i*16) 16
  | 4 => packedAt s0K4 (i*27) 27
  | 3 => packedAt s0K3 (i*38) 38
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt s0K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/30+packedAt s0K5 (768+(h % 30)*6) 6) % 48)
  | 4 => 2*((h/58+packedAt s0K4 (3618+(h % 58)*8) 8) % 134)
  | 3 => 2*((h/36+packedAt s0K3 (988+(h % 36)*5) 5) % 26)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xfffff83fffffffc0ffffffff81fffffe3ff1ff
  | 2 => 0xc0ffffc0fff83fff07c1e0fffe1fe07fd13e73
  | 3 => 0xff03ffff03ffc1fff801ff07ffe1ff81e1cf9c
  | 4 => 0x3fffffc0001fffffe0007fffe0001fe0fe0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x44100888209000002942410900222a280650a5
  | 2 => 0x92299106492270cb0290a8d2b2154154d12652
  | 3 => 0xa4aa2121a46135550213a44d5419505618b18
  | 4 => 0x2cb344a49074a5a69cf4108769980619ba0de0
  | 5 => 0x30c38738e38739f8e739dce071111861fdf000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcccccc0fcc0ccc0fcccccc0fcc0ccc0fcccccc0fcc0ccc0fcccccc0fcc0ccc0fcccccc0fcc0ccc0fcccccc0fcc0ccc0fcccccc0fcc0ccc0fcccccc0fcc0ccc0, s0N, s0R, (fun _ _ => 0), s0I, []⟩
end PEqualNP.Outside.L_meta_37247
namespace PEqualNP.Outside.L_meta_37247
open PEqualNP.Outside.L_meta_37247.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x604000100f74c1441c08c300c3c4780fd30fd40fe20fe43fd42fc30fd41bc40fd43fe21ff41dc31fc43fe31ff40fd21de31ff21ee21fc40ff43fd32fe32fd10fc20fd31fd20ff30fc42fc21ff32fe30fc10fe10fc41fc32fc31ec21be40fe42ff42ff20fe40fe41ff31ff10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x1b137018094057b93ad84aa040c1020084500541c00a0410f000c0ab8f0e0038b1978002222220b047008006140dbd4910ea188435f53486b8a690db94b41cf29881cd320cb5c43205ed4141ceaa0636d52d0fcca210ed94440aea9e4377514caf0a0a0cfd5110af298417551d0adea4a0db54a10dc20621d4310427ea898710c421f210821ad540873aa6206b08640b6a96837451483ac8218db14930e7188437551d0fc86210f30c421e718c435d531033c63205794e10ba28a615e531035ca810db94a10af29e439e31102dca4186b08440d710881b8400427ea8905754f429e2a2413d54cc2bca7a0dd944409f2a0636e51086dca310cf94040d729081e5410873ca818f30c6219e2a2619c3190278a8885bd4930af29e853d54c42d8a498d754c20b6a90617651d0edca5a1f9086109f2a6415f53506dca4204f95021ce188813d540c76aa2205714d41ba28a656e52cc7ce6210d794631d6a90813e54cc374a02057d4d10eaa08637551102bea6904f55021b6292213e54c42daa4204f94240bb28e853d54c82baa7085714d20b6a96635d53d07a863085dd4520bba8a61e641086d8a4a0d794431eb288635c53443a86390dbd4931
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xcc0008006a10119000c95495110385540c421951855308385640c421c554d5110315540c421b118d41086e06050421e10c421103843108640e19503108786640c42199185520c2d060504318759431103903110010d194c21842c6618c421a9590310862d6508440b1189410c746520c610b1185320cba02110010
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0xc0aca1884220485769503108682ba86210881415d6640c421
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 117
  | 3 => 24
  | 2 => 4
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
  | 5 => 2*((h/22+packedAt s1K5 (736+(h % 22)*6) 6) % 46)
  | 4 => 2*((h/53+packedAt s1K4 (3159+(h % 53)*7) 7) % 117)
  | 3 => 2*((h/15+packedAt s1K3 (912+(h % 15)*5) 5) % 24)
  | 2 => 2*((h/8+packedAt s1K2 (196+(h % 8)*2) 2) % 4)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfffffffff01fffe07ffffffffffc07fe3ffe3f
  | 2 => 0x7f01fc07ffffffff83e07c0f80ffffffc933ff
  | 3 => 0x7ffe0007ffe07ffffc007ff000fff83ff1c3c7
  | 4 => 0x80000007ffff81ffffff800000ffffc1fe03f8
  | 5 => 0xfffffff8000001ffffffffffff000001fffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x914284011c104200c628c508e2c425212561b
  | 2 => 0x224c518b224a28c581a8350d12558ca4c930ed
  | 3 => 0x4c289ad54487516ab4125b64249ad23971c346
  | 4 => 0x68b1636689141db35adb024848e36711be03b0
  | 5 => 0x70c183870e1861dc631c638e70038421eda800
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaaf0a0a000faaaaaaaf0a0a000faaaaaaaf0a0a000faaaaaaaf0a0a000faaaaaaaf0a0a000faaaaaaaf0a0a000faaaaaaaf0a0a000faaaaaaaf0a0a000, s1N, s1R, (fun _ _ => 0), s1I, []⟩
end PEqualNP.Outside.L_meta_37247
namespace PEqualNP.Outside.L_meta_37247
open PEqualNP.Outside.L_meta_37247.Model
def s2K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (i*5) 5
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt s2K4 (5+(h % 1)*1) 1) % 1)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xe07fffff01f81c1ff83ff0fffff81f00e33fcc
  | 1 => 0xff81f81fffffffe0ffc0ff0780ffffff3cccff
  | 3 => 0xfffe001fffffffff0000fff800ffffffc0f0ff
  | 4 => 0x1ffe001fffffff000000ffe001ff00f0
  | 5 => 0xffffffe000001fffffffffffff000001ffff00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x230c33011c11ac03190d302a8e3b190c6115cc
  | 1 => 0x4524412224a084a06944510312492a542c4c55
  | 3 => 0x8a1096544945194d0428aab0249654a9c0b0aa
  | 4 => 0x1c5967989075de76b5ae08a248e79831f700f0
  | 5 => 0x10618410e1861398c630ccc4700400c19aea00
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaacc00cc00eeeeeeaacc00cc00eeeeeeaacc00cc00eeeeeeaacc00cc00eeeeeeaacc00cc00eeeeeeaacc00cc00eeeeeeaacc00cc00eeeeeeaacc00cc00, s2N, s2R, (fun _ _ => 0), s2I, []⟩
end PEqualNP.Outside.L_meta_37247
namespace PEqualNP.Outside.L_meta_37247
open PEqualNP.Outside.L_meta_37247.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x14000801491c01c0240080000055000780444141fe41fe10fc21fd41fc20fe30ff10fc30ff21fc31fe20fe40fc32fd43fe43ff43fc43ff31fe42fd31fd40ff32ff41fc41fe32ff42fd30fd21fe31fc10ff30fd20fd32ff40ff20fd10fc42fd42fe21fc40
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x800ef0801431854020100001413020020000040190000d80010402c2800140af29c417a500c6eaa2204fd5130b6292633d54c82daa421ded4142aea98855c53442baa720d714d42af29c8374514cabaa7a0dd94440b7296833e54086dca4205b54840af298215f53486b8a690de54241baa8c417651882baa610cfd5110aea98815f53442e8a2a15e94241baa88617b5050eeca2184f95320bba8a856f52442baa6085754e20bca80435e53102dca421d794f41bca80633e540ca7aa8195dd45329e2a221785050ebea6a05e94021af298853c544c2f0a0a15bd4931b6292216d52d06bca610d794f20ae29a815d53c82bea6a14f55021
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
  | 4 => 2*((h/42+packedAt s3K4 (1728+(h % 42)*6) 6) % 64)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x7ffffe03ff8307fe0ff87ffff83fe018cfe7c
  | 1 => 0xf81f83ffc1ffff83ff07f8780ffc1ffef3338f
  | 2 => 0xffe003fffffffffc0007ff800fffffff03c3ff
  | 4 => 0x3fffe003ffffff800000fffe003fc03f0
  | 5 => 0xfffffc0000003ffffffffffff0000003fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x30c320238411500c642980a8e3a1321884563c
  | 1 => 0x524424448ca11281a522883124a514a8b13285
  | 2 => 0xa1094a891144253410855502494a495302c15a
  | 4 => 0xc59673122875b9dad6b044248e739063dc03e0
  | 5 => 0x618421c31862e6318c66647004201836ba800
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeae0e0c0c0eeeeeaeae0e0c0c0eeeeeaeae0e0c0c0eeeeeaeae0e0c0c0eeeeeaeae0e0c0c0eeeeeaeae0e0c0c0eeeeeaeae0e0c0c0eeeeeaeae0e0c0c0, s3N, s3R, (fun _ _ => 0), s3I, []⟩
end PEqualNP.Outside.L_meta_37247
namespace PEqualNP.Outside.L_meta_37247
open PEqualNP.Outside.L_meta_37247.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xbe40bc40
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 2
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (i*5) 5
  | 4 => packedAt s4K4 (i*16) 16
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s4K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/21+packedAt s4K4 (32+(h % 21)*1) 1) % 2)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x1ffffe03fe1f087fc3fc3ffff0fe070133f7cc
  | 1 => 0xe07c3ffc3fffff83fc3fc380ff0ffffeccc8ff
  | 2 => 0xff803fffc01ffffc003ffc00fff007ff0f0f0f
  | 3 => 0x3fffffe00fffffc00000fffff803f00ff0
  | 5 => 0xffffc00000000fffffffffff00000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xc31802388422100cc04c048e701231181153cc
  | 1 => 0x4900444890080101441441121104924844c055
  | 2 => 0x842aa8910d548ab4222aa824aaa044b30b0d0a
  | 3 => 0x165331222906acdaaa822048ccc96023b00ea0
  | 5 => 0x186221c33198cf6333333270088180c3eea000
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xeeeaeeeaecc0ecc0eeeaeeeaecc0ecc0eeeaeeeaecc0ecc0eeeaeeeaecc0ecc0eeeaeeeaecc0ecc0eeeaeeeaecc0ecc0eeeaeeeaecc0ecc0eeeaeeeaecc0ecc0, s4N, s4R, (fun _ _ => 0), s4I, []⟩
end PEqualNP.Outside.L_meta_37247
namespace PEqualNP.Outside.L_meta_37247
open PEqualNP.Outside.L_meta_37247.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x69c800000000028610004000001008028030201a041ff32ff21fd42ff40fd30ff20fe40ff10fc41fe20fe42bd41fd20fb20fe43ff41fd31fd21fc10fd43fc31fe32fc32ff43fe10fc30fd32fc20fc21ff30fa10ff42f820fd10fc42be42fc40ff31f910fc43bc42fe31bf41fe41fd41fe30fd40fe21
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x85bf41c86fca9107ed0510fca1641be420837c84195f54a21df2a441f950106faa7196f50520bea80837c548c77aa5a0df95040be2a0637e5090f7282105f54032dfa08417e520c77a8220df94c41be2a643fb43843788420fe50020bfa928177514cb7887205f14121be292817f548c2f8a890ef94941be29a417c53842fca621df15221fd90c21fa548437aa3215f94843dea9c857f54887baa610fe4c720fc18641fb40cc2fea2905f14d42bea9e837e52d06faa6087e0ca10dea0c61bd4310ff6a0997e4c320f790441fa53c82fca5987e08210bea9c857d5110af8a2996e10910fda14217d53d02f8a099770ca31fc10841fa31c83f4a6886e90b20ee996637e54486faa9904f55221df21683bc505077ca2215fd4b10bf2a087bb41c83f082105fd4f21df21021bd43507788510dfd4941fd99041f8400837e82086fd4f41bf290437e54842f2a018fe88110dca0a217f53c83f240107e94e10bca84437d52d077aa8086f90910dfaa2437f54c42faa3907e90720df21c857d54086fca5195f15220bf2a0437e508837e86a05f54430bea8841be420c6fca2195f94b319eaa063be43d07dca418efd0510fd986417e5410b7a86217ed0240bf2a061f9404437e8218de94342ba28a65fa100437e80207e94041ee988637e54106faa121df54642bfa82837e53042fca3205fd4d40de21461bd410c2f4a010df94041bea9841bf5390bf683087ed5110bf28841de324cbde65195f54242fd21c21fa42843f6a190fed4510dfaa2657f52442fca318df94a31fb98e437c5250efaa720fd4c431fc18c21fb31c827ca818fa94820ef99663be42902fca7086f50842bc294217e54483f042885e94820bc29221fa21082faa7a15fd4d20de286837f53082fea0a1df94210bf2a2637e508c7ec6218fe10110fd992217e500cb78a8996fd5321df21281bd54087f2a4885fd5232df2a043fb54082fca420df94f10bf28443fb50487f480107e48110dfa0c41ef4290afaa3085f55131bfaa063bd414c7f6a9905f94842dea0a61be42882f8a898df94810bea8643f841442f8a8987d88421de21061fa32c83788498ef10930f9a8a21fb400c37a83985e54041fd180413d54ccbf260105f15332fc2a421bd418c67ca8086f94f41beaa4637d54c87f6a5085f54b30fba0c837d53886faa5205f94430bd286657d548cafca5a05f55010dfa04817f548c6fca918fe0c020df20a837950086f8a0a16f90821fca1841bf415037e8220df14542fca10417e52c42faa3195f54e40fc21e41fa20843f081085f94732ef98863f950906f8a9087e94221fba8a657c54083f0a6885f54c409f2a665be428437ca1217e94910bfaa061f9408437283085e94031f690843bd41cc77484106fccb41fd10a21bf418437085087e95320de2148379508c6fea8905f94d10
  | 1 => 0xc51482fca120fec4110beaa265f7314c6f4a0086fd0941bfaa2637d509077c84a0df14e20fda00417e540c7ea200877cc631df21885f7318c778a890ef55231bf280877e50c877c8420df54443dfa82837d548c2faa598ef10a31fca8463bf42d06faa690cfd5120f719243bd50d06faa9997e90130df28683f721487f641105f54c42f719643b940102f8a9886f15321bf29461bc32d07f460186fd4941dca0e41ed32487f686105f54d20df216413d54c437c85197e50320eea18877e50d0af2a021ef8cb41fd28063bf41c82fca5205f55121bf298637e5190b7085905794c21fd90841bc43d07ba6498df94d21dea08217a52842fca3987e4c910bea8063be435067aa9106f94842de210217d50887f0a5087e48510fc19041bd535077887215f55020bf28085bf51506fea2a15f94e41fd21841fa32843f2a2107e94021fda1041bd410c77a82885f95010bfaa641bf43d03f641085f940219eaa463fb5050a78a8995f15021de212217e52d0ef6a0995fd4d42ef19463bc420c6faa8887ed0110de21683bc5390af0a0a1df95320fc10e41bc53d07f661187e54c20bf29c41fb43442f4a4886f90b10bf286837d50cc7f4a2107e10320fc21c21bf50d07f640907e4c030bc282437d54cc3be64196fd0710fd996417d50d077aa910fb8c832fca0c217c53083de40107bc8421fca84437e53083f6609877d4d21fc214217c524437ea8986f55030de214817c5150ef8a5087ed4c20dea0c817e52083f083905f14c21beaa241f820042f8a8196f14042df212653f54486fca9995f54a43be28263be42d03f642887ec4210dba8a83fb42442fca5217e0c420bea8c817e54cc77aa9997e90320bf2a6217d53c82f8a5885f94a439f2a443f832442f8a6a0dfd5331beaa483bd41843f484107e54043fc10221f950086fca721cfd5321bf28465bf41486fea6a0fed4720fda0841be424877a83105f15320de21241f853c837885107d84110bf28c65fa50ccbee4310df94620be2a6637c52042faa010cfd5132de996837b5050afaa420dfd5032dfa9885fb405037aa9886f50941bf2a2216d520c7b8a690efd0a42fd10e417e50ccbf0a8104f15120bf288217c540c37a82a07d0c421fda92217f514caf8a7885f54a41bea8687bc42ccb7884a05f14d40fc994217e540827aa8186fd0740fdaa421bf4390b7a8310fe48610bf2a4657d518837a8210df54042bf28c617c525077aa7a0df54b43be28a817e5310bf220085f54f10fd21221bf325077084105f94f42bea84633f544c3f461905e54332be28a61bc42842f6a090df94031dea0881ed32c877e8721fe14e10dfa9683bf43d06faa2207ed0210fc18a21be54ccaf8a9985fd4530df216437e548c37886207e90d10bca8685bc420877884205f94720bfaa421fa20082fea098fe50f20f721
  | 2 => 0xb7e83187794c21bf284817e530ca78a4a0ef8c941bea9681f830443f262887dd0541fd28463de4310efaa021fed4e10fc90e417c54042fca2207e94043dfa0c43ed20083ba64195f94643de21641be43902fea890df95221fb880217d54cc6faa5086f50720dd212217a50882faa4885754c21bea94637c53c86faa4187ecc420d7290857951082fca3a1ef95030dda0a217e51906fca9987e88610de21465bd4010378a6215f94242be2a241f954082fea8995f95321fda06417d510cbec8220de94041df21a877d52042fea690cf15121bea9461fa32083f2a9907e50230bfa9c43de304c3ee6210fe90210bfa8a877d540cbde4310efd0430dfa0c83fa414437a87215f94030de28485fb304437ea6a0fed0f20de218857f504ca7ca5a0ef90931bfa9c21bc425077a85a0ef50f41be29e417e52842f2a3086f50710fd18421bf5010afca2217e94342bf292217d51ccbf480205fd5332df2a6217c544cbf6a7907d50441fd90e41f850c87f4a4107e0c720bea8c617e510877885887e50a10fc218417a50886f8a0a0fe50130bd284637f544c2f8a6886f94d41fd29841f853083f287087e0cb20de29a837f53443f6a2106f90830bfa9261bc5190b78a8986f54042fca8e41be424c2fca0207ecc510dfa0a63df328cb78a4a0df94343df29885fb42c82faa418efd0530fc98421be5390b7c8518df94d209ea8885785050afca790fe4c8209eaa0437e53887f282105fd4e20fca80633e540877e83985f15230bea8665bf418c77485085f14d21fcaa421f830843be61186f901409f2a061bd32507f4a8105f55030bfaa041be42906fca4186f94141bda8287f931843de84a1774c030fc288417d5490f7aa818fe10820dea0a43fa318427aa3216f10932fcaa2217d54843f487905f54f21df2a463bc42487bc6298fe08310be2a2215f53486fca7a077d0e43dda0c217d534437c85987e10030bea8e87bd43503f640087e54e10dea0e437d5210f78a8906f90b31dfa88857f540437e8398fdc4210be29c437e50cc77a83a06fd0d41f710241bc42d02faa1196f95031fa18e43f921083f0a0997e8c910bf28461fa42c83f4a120fe54332fd902217d538c7f0a4886f95221fc282877f54086faa420770c831bf29e417f53087f683905f54e30ef98061ed520c7be86a1fe90230beaa4437f54883f483085fd4121fd98421bf4310efca218cf94842bf298437e51106dca418df14143dfa18857d5490afea0a16f95010df28c857d538427ca820ef10832de192833c544c3f086886f54242fc28243f9414437c84a16f94042be292615c53486faa818efd0842fc212217e52906f4a120ef10b21dfa8485f840cc37884104f95231bf2a065bd410827aa8085f94832fa908437e530c3da64197e95110bf29c85bd5110b7ca5a0ef14b41fd98c217
  | 3 => 0x69700a05e04800060a8148400100022002010060001805812000a0004980180a0507607800498001700017c200180434000040022b0280000a1410e010000000566000290280800004006000000380009066000be004e813008000020100003820000040020f2f818000000200c0880000002038000005a010500a004218520500e03808000441e05c00272ea958000000a00002006018480000a0001e010062c82a00832008160182e04822008001d80c0400c0000c00815560022400800818078020007e000170d0042d80414800990000000e14814080421c0000081005000c00263a800078000380401016010200007e04800008001780c010000000604016008002e0061001000008000b000052008360020c038008a83200066008160d01000000021ee050d4290160280429a8e02216010161b88c02000038060182ca080005008050261b00a0080802812348080904600010000001a008221e008008000040f0b649000040be062700008413020028040b800020020503c1a1340a034000000d81001a1002824020040100405858010ca0d8000007c048060d8080000a0300e0082801f5a0000027000020088a044249220806c0700e0a8041505a00074208082580001844098023800a0e8014f80085668000081c000000c4058000000413802618200007c00043a9002040040880a0000200a840080a24000235f95130bfa9421bc42cc3f2a7907e90110fc28e41bd43d037e8210de94043fda9a21ef324cbf283906f90840fc98841be431037c85995f55310bf28e85bf41103f284885fd4c10bea8c87fa30443f085907e8c420fc2a641f940102fea4a1ef90920bf280417951c82fea2a06f54c42fc10c217e53d077ea3216f54941bca8483bb410837e82905f55220fca86853e54c42faa3a14f55241bea9883bd54882f8a498fec8310ef992637e5110f788598cf94a42bf2a2653e54882fea4085f54a20bf28c437d54902faa610df15232bf29081f854443f286885fd5330bf298817d50d0bf241087ecc020fd994217e51d02faa7106f90a21de21a83ed4210bf4a3905f54b10fca9421f4514cafea990fe10610bfaa221bf41903f260887e90420bf29c81ee21486fea7885f54740bf28021de320c6f0a0995f54730dea8283fa31442f8a6087e54d10fc99641be428c3f6a0a1dfd49319e2a6437d544c3f4a5086fd5120fc28285bc511
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x54ccab864c85108f59732d073a5210910ae590210823f6550430ae59051c82ba640c6108f59251c833a5408310aed91210827961141429798c54082b96090541ae59221c827b6054843ad58453d067960944428fd91520c33852109108fd85540c26f654c8328f59442c43685210910ce10b50486e86254d109ed8153486ae62d05218fd91530823d6414530ba98a43082eb6254d10c7952530873a42940219e58652442d963147208f994424c2ba640c3209d987538827a6510e108fd91538423e6414131ced05508c7aa6210a109e5865010fb361504209e19542842ac62507218f990530823f6454d20cb98b54c867b6550a10ce95150087546154c218f996424c27960947438f992518c2ba6488110ae990414433a54540318f587544c23e64d4b109758f54086b964d4f209e19521442f16194d1097d95320ca7a6014c10cb94b410c7595314c208f99051482b86050d40ced53504cabb604cb41ce14b41442ba64cc820d3549310c6796014d41cb94842106b9648c610ae98241506bb644c9108f99250c86b86448720aed8153d06bb6054c428f99353c42ba64d49108f98854482ba64087209798c548423d6494f20cd951411073b5094242da98a52082b860509419ed81540ca3e6494632d314e32486d963144208f596421073854d4321ce55054442ba60d0941a758f5090a3f6510a319e9825110ada6314420ae59220843395494021b618d218433842540419758c54083385414121ae19153442f0614c910b658c21842b6610c9418f195414823e6414c21cbd91520c7725044010cd58754c86b161109108f59251086ba64944208f593524c2ea6215020ce553400c27b61543329d984548c2796510e108f99253c867a6015031ae19130842b86350040cb94842d063d651083097d95300c2b56110a31add85525072c5290941aed81525077351d4132d3548320c6b86448020ae59352842796510420bcd8532442d96315210dc580514cb2e5454831ae59031842bb6050c42ec94541082db6348420ce94b414423d65950218f990538863e64944109e9835250eba640c720ae58642442ba62d0510ae983525073a4294332ec506214423f6550431ae992318423e65151219e180524423e64d4f208f596431033a42942218f596420c6b9648c720ce10850486f16115020da948200427a6590510dc147504cb3754d45329e997428427a60d49319e980548873151504209e58253c863c6454f21cdd93514cab56194d41d654c534433954c8220ae191320827860548419e9805150ab86050c42ae59332443726014532da181520c72f5210931ce9085050aba64884209dd85544cb4d6214d21ae980435063d64145329798f54c833b41d41218f19150c863e65909209e99641c827a6214143ce551300c26f6548020ce55020042b56110931
  | 1 => 0xeb86050b419bd8954442796510c208f19152cc7b36150720ae9804310a796590720ab189418833a42547208f590504c6b9640c510bc584530823e64d4e219ed94200426c6255110ba588310823e6515130ae990534423f6454b10ae98342d067b654c030ce95150ccb2d549483197d95310c6b960d0842b698f54c823d6115130ae18941843a86250420cd545418c27860551328fd94420c2f261d0d10aed8152d06796015032bad89410835a5394021ae580435073a42544209e189509067a6094432ce109509063e6494d20ce90a500c6ba64ccb209e1815310ab96110a109e59430082b66114042ce94842842ba648c510da149214427a60d5021ce54d401031c5310921ae982425033a5454231ad9845310a7a65cca10c754c42086bb64c8420ec504314427a658c420ae191538433842542219e983548cabb64480208fd95410863c6255031ae19130443aa5290820ae59221842ba64887209e98253c873954943329e19520442bb60509419ed95320831d53d0421b518d210863f654cb419e9825390b3941940219d584540cb3854141329e983548867561152308fd9152cc6ea620c5109798c530863f6454810ec90b51442da63150209dd85534823d6414e109e98a509073854c81208f99352842ba640c210cb94a42906b9640c1109dd95310c73a54080108f995414c2bb6454c20ae18941c82ba6010f41ae98053506db63487208fd96420c27b6548020ae990218423d64d4c10a758c5110abb61500408fd9442c427b60551319e982544cb2c52109319e99431c82ba6414c20d614f504867960946328f590514827960951219e1815290f1f53505219e982548ca3f6454b309e58352506b960d0b41cb94842d02b960144429e583540c63e6414530c7d4e42487385450110aed91524427960953218f58554042756114c20ae191218435b5314121ae988420826c654c921d514f214867b6054810ce94b4184278654c110cd990514ca6e62d5031b5185320ca7a60d5332ae19132c83356115321ae19152843b141cc5109e98254486db6354910ce10a501072d5210b30ba98b53c831c53d0521cd193514cad963d5320ae98a424423d6494410ce10b504cb3954c80108f992518833b41542219ed95434433941942218f18954c432e52108319e594200431f54d4d219e983530869e63d4242a798c5110a3e64150108fd96420875553cc421b618d54442776548421d654d500863d6195030ae5804390a3d6494432ce109508c63c6550530ae58442c82d96315020ae5825190a7a60150219e98054cc67961d4132ced06508c63d64d4e208fd9541106796014e218f990538829d63143418f994544833860550308fd91534427960d5221ce90b5050ab960d4e42ae98332506ae62d4e429e994430823c64548318f59250c873854502309e98
  | 2 => 0x6494831e3109320ca3c6454d208f19152cc2b561140429ed8152443395014141ae99021442b96110910cb191520c6ba62d04209e58054cc6b96190820aed8142d0678654c910ce10a50cca3d65d0430c754c5310a7965d0910ae593524426c6254d10ced53204827960947429ed8154cc63d6414c10cd590514caba60d4e42ae98053d067965cc820ae18132d06bb64c8720c7d4f41487285210910ecd85418426f6550842b618d524426d6214f108f99052c433b5495320ae9805190a7865501109e59443442ba64c4210ae59021842786054f418fd8554042bb64486109e18152cc6b964900408f992500823d6494f21ae990314433b4154241ce10a508873943540438f194424c33b4194041ce909501073b41540419e980544c73a54c80108f59352043395150720ae590534423e65151329e18152906786055121bc984324431e5390821dc183514ca7b6055130ab9885390a6f6254d108f590520433954942318f997425067a65d0910ce153504869d63d4b41ce10a509073b54103208f993524423e65d0d409758f528433a4254332ced0d5010f3854500209798f528427965100308fd9642c427965d0a108f59741087395150420ce506500c7395410210cb952520c67a6294041ae993328423c6454d10aed9130082b964cc8208f596420867b6054a43ad584325073a4254021dcd83514cb695294031c794d4390b68520c910ea94941082ba60ccb419e980530867b6550c208f59353c423c654c9419ed8152106b96014d41ce550400c33b4194241bcd85534423d6414e21ecd45414433a52908209e5835250ef161d4e10ce909500c6b96494f20cb54a420c73454d45329e980540cab86454910d654c53842b860508429e99621442776154d21ae583411036852cc9109ed8152d0f6a5248610ba98853082bb6448720ae59231443ab52109109798e544871d5494c21cd150514cad4614cb319e99732442786054f21ae189401027765504419e59441c82b96010840ce90850486786254031dc546310827965c8010ea988424434d528c8318f59741042786550d10b5185324c6b56110b21ae59251c825e6314b10bcd8554442b86448210cb94842cc2796590420b698c21082b964904209bd89544c7b161109108fd91528c27b6550f208f584544827b6054f218f993530423d6494730d354b310c6d86348510ad58442087395454231ae99221842d96308510ae59021c83395454021ce95320c42786054b419e58253482ba64d4f20bcd8552442b964881109e181534873950140429e181528c6db63486109e982534865f63551108f191500ca7965d0030ced06508867a650c420ce552100437265d4510ce952508c7395410110dc54531082b8644ca10ce55020c42a86250420ced50504863f6454a10ce10a508c63e6494730ce90c505
  | 3 => 0x42097d8d544877151c8420ced06500c67a6015231ae18143d023e64d49319e98a50042796510f209e58251ccada63147209e98251d0a79658c4209758c54086e4614cb21aed91208433854502109e9805150f1c5414d21ce153304c2b964ccb20ae98a420823e64d4930ce506500433954543328fd91500ca7a6094642ae593108423c64548108f587544cb59530c2109e9825110ee9620c6109e58650cca796114143ce55150886b864c84208f990520423e64d4c219e99631c83385250610dc58452842db6348510ab98b41c873960151308f19152c436852c8110aed814390a7661951329ed8152cc63d65108109e98251cca3e62952318f992510c6796015021ce153504cbb351d0510aed9540102796014532aed9130c827a62940438f191528c23c6454830bc58452842746155132ced53504863f65d0430ea14842442b8644c9109ed855010e7960d53329e58650043395444010ab189505067965884208f99253c82ba6488510bc185320827965cc9109e98054042f161d4a108f593538867a65cc1108f197414c23d6494d218fd9442042b96010c429ed8153483b261109109ed81528c6bb64c8610ae1814390a7860548439ed8153d07c532cc721ced5040cc27960152319d18553483395014341ae592510827b6054b418f592510c23e64942328fd95325066c6255131ced5050c86b561109108f992544c23e6494430ae189414427a6094632cd90b514cab96010f418f59353086ba64880208fd96428c66d6214c10ae181325067a6014532ce550400823d65908108fd91524427a6510720c7951530863e6414e10ae990410835a5354021bc584538427862542318f993538833a54840109e5825190eda63087208f191528c63e6590921bc584548427b6548420aed91538425f6354910ae5833250795414c431c7d4c424863c64543318f997414c27a62949109e58650d0b385450130ead8941082bb644c820ae59221442e9620c7208f188544826d62d53308f594420c67561d4e20c7d4e5390ab960d49418f59251cca79650c420ce550540827a60d5031d58c8514caba6094e42a758c5190b1d5310c42da948208423d6494632ae590510827b6548510ae990304423d6590a319718d544432d5250431ae191300c3394154031ce949410832f64948319d594310873941540218f98a54c432e52108409e18152d0f6952540319d98453082da63152109e5805150f3a4294010bad8931082bb6054d419e994414434d5348421cd54541082ba60d08428f592530cb394114121ae191214423f65506208fd954210a3e65d05219798f54087a842884209ed815310a3d6550620bcd85320823f6454331ce908504cb5b53d4121ce14a428433b41940219e5825390b3954c83109e583530863f65108219ed81520c63d64944208f592534832c
  | 4 => 0xe5875050b6a52c83108f191528431d5314f419e18154cc63d64d4931ce95150886f1610c910cb94a42902f3614ca10ae592310827b6055121ae98b418423e6494732ce952508863e65505208f195414871d5454c219e98254c86d863484209e58354086b561d4f419718d524427965100209e58054cca3f6550040c794f410863d6494232ce152404c279650c720ae9805110a7b6054a41ae58642842f26115020a798c5010a796590020bc185328436a5294031ae58352d063d6414d10ced5350c86ac6250420da14b21442ba60946428f59053082ba6210910b658c21082b8644c0208f990540c69e6314341dad81520c73b54141328f990514cb395150040ba98b54082b561d4b418f98b544c33a4294041cb94a420c67960d4e21ae58332d063c6255030ce90b504cb2c52cc9418f988544c2e8624c420aed9152842ba60d4b418f994424831d5310f41ce909508c67a6294031cb54b410c67a60d4941ae59031082796094432aed9121443384254720bc58442442ba6414720ced05500c73b41540219e98353887a8424c820a7d8d50506e5620c721ce505501073a52d04208f19532d06786055131bc18532c823e65ccb419e19543c823f6454d21d9185520c6bb644c210aed81435067a65881109e597420823f61552209ed95100433852909109b98853c423e65cc941cb14a425032f5210910cd908514cb384254420ae990510825c6355121d654e500873b6550040aed814210aea620c420da14b42442b96408510aed9132c823d6115132dcd44504caba64c4110ae593328427a62d41439e59631c823d64d4b10ce10a500867a6015030dc144504ca3c6454910ecd85414427a65d0110ae98b41c83715108720ae99231083aa5210820a758c5010a7965cca109e9825190ef26114c20dc54541082756195132ae590300823d64944318f99251c832e6294842ce94a424427862540439e19543082b86050d419ed9542082796095120ea94b410826e6214c21ae99332442b96010c40cd54741d023f6454f21ae9825110bb042d4510ce550548427a6294231ae19120443715108420ae181525067b6550910add85325067a6510f208fd91520c63d64d4a109e583524c6b56114b418f59250082766115020ec5454108339548c030abd89505065e6394d21a798c5190ab4614c941bcd8532c82b96094e4297596530865e63150219d984540ca7a65c8110d6d4e53c833951d0720ae181415037151c87209e996404c2da6308610ae58642c827860548318fd91528c6ba64d4a10f18c831c867b6154342ce90b504863d65950319e983530423e6494d21ae590538433a5450320cd547411027961d41439e996410823c62550109e5805150a3f6550410ab189414863e6414d108fd8554cca5d6315210ba58a43082796015031abd89535073951d0
  | 5 => 0x544433a5494031ba98853c83385414321aed8143d067a6014810add8553506f26110910cdd50514ca6d6215031ae593104423c6454d21ce10a500427960d52319e19532842ba6414e108f99254482b961108208f586548827b6055120ba98b530833a52506108f596420c35853141219ed95324433941942318f597410c67a6014d41ae99030082796584010cd9454108358534c110ce95250cca3e62950318f592518c26e62d5330ae59031c827561150209799453487395454031cb551520c72e62153218f992544cab56190821ce148428427b654ca109e18154c863f6454321ae58053d063d6414f109ed9543842da63085109e99421442b86050f41cb148424423e6295010ec50521442786550e10ae19153082796014c21da98852442b56190b21c714d43506b7614cb418f99741482ba6408420ad18532d063e65109218f592518823e649442197d954310e3e6295030ae19121082f16194910cb949410c63d6414e208f596540427b60553219758f54c82ea6215320d354f21086b86050c438f594428c63f65908109758e544867a60d5231bc587434423e65909329e98053886b864c8610c7d505348759530c020ba588314423d6510821cd54541902ba648c720ae9804390ba842084209e18950106b96490510dad82520c73941940419bd95210871e5310821ab189535069e63d4b418f992510caae62d4c42ba98831c836a52540319e994410831c54d4d21ce505508c71c5390921aed81325067961141329e98251d0e796095232ae1815310ab86054d418f59053087395494221da94b218423d65d0620ae99253c827a658c510ced04504865e65cc931ad5845310ab960d0a42ae59030c8279658c020ce552500c63c6454e10ce108504cb3842940318f59052c431e53504218f196424c27a650c5108f994424cab96414c20c754e420867865509108f59642c433b41940108f596540c32c520c941ae99220842b96094442ae19130c82d963d4a10f44c4314433a5494021ae990310823f65908318fd97418823e649512197596320c73842543328f990540c33a4254221aed91204433852d06109e181540ca3e6414c108f59353c827a60d5010ae19321c82796094d21ce109500c6b96010e409b98853043aa6210820c754c535069c63541419e5825190b3a5250040aed9132842bb64c8510ce149414437151904208f58654ccb3a4294231ce94842082da63d4a10ae5805310af16195110da98852842796015131ae592200823c65d0520ce109500872d52108318fd94420c77161949109b988540c73a52505108f593524423d61d5120ce94a428423c6454c209ed81544cab86054b41ce909509063e64150218f597325065d6314b109e582544cabb6454d10ce95110043a8428c820a718d525067a60d4810ce953208827765440109
  | 6 => 0x30003fe00c0080002062978800020060c0806000020000370080740401b0140282a0012d803c06800016078138000d235800018008074000160040017f8136f80040680102a000070570000a82380500000c0185301e2200300f0080cc028000e21300600304a1300083d00c0a04201606a01c0609a13a0041f80101004c040000040001387c03c010170000902fc1c80100a1440003300c27800c540041580481700002426054000018040020060580f89800405c3e8e400e0481280903a004020000220043d8000000341d832032304870e101600c0a0000120a012802022014228450080080880002a0000080201600c00c5d00c01c0780f0000204c0160140800a0041123000293c008010038000020800682513e00c490050000200307f00c0001708e01a000040040020000003e0f804c1885300008c0583d0020a00300700e01c2e8000022fc00091004058008040b0000008000123380040003403c000080560600000d0a217c0d0000040a81a00001c000010050200187782a00c03c570010040680080004a1080f01b00e0000480f0001840f8b001a0d42e0120ce0784e0050102681f8180680040080800c030060c310000490000022000058000544b00105c00403c3b00c0125141500f03c000000080300b81880600001c010e70000c80a8020140180003e02609417806008058070050020d43a876016004040000000340280905c0000382700001400800024121c81b9000004018004f20140d00d0001c43380506c6100512e07e000010a70580000500000001c08826000018010c000801806811014028190000900751100202a0c0001030000289080203a0000080300a6788b8590021841985e00019c0e81500205c0780f0060842804c000004010000140000f975008026db6355110bc587548423e6494c32cdd4541502eb62551108f993520423f6550c43ad58442c42b960d0941ab9885310ab9640c210cd10b514cb3941d41219e583548ca7b6550040ba98831842b86250420ea98842c836860948318f189548c65e6314810ae99251c83344214532a7d8d52506b964884209e58054886e862504209758c520423d6550430aed91304433a4294241ae18153d06ba6014c42f24c832082b960146429e5825110f5a534c3209e195404c27a6510d10cd945418c31c5350521ba98b54c826d62d50318f99251082ba60d0a42c754d41086d863487208f99053c42b56194941b658c21c83394154221ba189
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x37e0010520240041a082010201208001002b0404481041800000000000034000000c306060409b3e043aa023400304000001004000c218080000400000000002e000000000284840800d0000b040004101c2aa6b088410d487254c5344310292c221221891496110910e40a4a0a4288720525844244254bb08410841a8d496110910cc0c4a8a8210528725505444295396a820661469cf5410320a54e529084886196354050d0750312a2a08412c1d94148510962e3300a6a0f2042544210828c3a2a629a21981496110910c66c8a8e4210632525844244318312a2a08418a1905248510a50e4a80a0a0ea06294541082d0b8884108418a19052c8510a32e62a28010720529844244328b1aa2108418554d6114c42c62a8b08a8106a1625043144254392c918841a1108614c832c60a4b088488619635405010b90312a2a0841469d35394f20c50c4292828862862545410831832a8290a21865915314e10c32a6b00a7a0cb1719935244350210c2990414c5c44254420954e5b22a610651535845308258b8cc1a9283a81496110910858e4b2a8218518735504044286392a629a838a1885250610c32a6b0087a0c71711954308258b8cc829a218314c6250521c32c8a9860105c0714c832082943928228243c8d895150420a50e4aa0418863361545401030caa2c62a421315da320c721c50a4b0884886186414d3044318b22a31884186192534c320c34a6302872143876551300c28d39ea1284858654d6010c42c50a530664a0caa72d815310a8d386a729c858654d6014c42c62c2a80a02162862109509068c382a629a834c5c45450020a30e6aa0a8885a0725052144258b8cc199283461cd5014141e0aa4a0a6218e9063505214430c298c0a1a838a1884254231c54c82966488531711095008714314a4a008186591530c210a62e2212a118e195458c5408258b8cc999221881895150420a50e4aa08088468725944344360b126218a219218c5248510a62e22a2811843571194424c312312a2a0841465cc5450210d12c6210421051a73d5254c830cb22a6298418c5915108420
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x23000020e00631494148510c20625c44254231e01631095108420c20651c94148510c81635c44208420a2082591518c420c80631c94148510a218199052cc910c20525c660cc941c20761494148510
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 48
  | 5 => 1017
  | 4 => 1345
  | 3 => 112
  | 2 => 10
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
  | 5 => 2*((h/409+packedAt s5K5 (27459+(h % 409)*10) 10) % 1017)
  | 4 => 2*((h/476+packedAt s5K4 (51110+(h % 476)*11) 11) % 1345)
  | 3 => 2*((h/93+packedAt s5K3 (5488+(h % 93)*7) 7) % 112)
  | 2 => 2*((h/17+packedAt s5K2 (600+(h % 17)*4) 4) % 10)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xe07ff80ffe0fc30fc3e0f87fc7fc0f023277cc
  | 1 => 0xff81fff07ffffff003ffff83f87ffffc3f88ff
  | 2 => 0xffffffff800ffffffc00ffffff800fffc3ff0f
  | 3 => 0x1fffffff003ffffff0003fffff003fc0ff0
  | 4 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x2b0d88e31592a702e0f83c65c4e4691a3233cc
  | 1 => 0x412491212084212001294ca048292a48168055
  | 2 => 0x861022440c2900554400910a910084b0c15d0a
  | 3 => 0x1459448849018a99aa5200432652c023680ea0
  | 4 => 0x1861870e71ce33ee339ce670046308c3bfe000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfce0ecc0fce0ecc0fce0ecc0fce0ecc0fce0ecc0fce0ecc0fce0ecc0fce0ecc0fce0ecc0fce0ecc0fce0ecc0fce0ecc0fce0ecc0fce0ecc0fce0ecc0fce0ecc0, s5N, s5R, (fun _ _ => 0), s5I, []⟩
end PEqualNP.Outside.L_meta_37247
namespace PEqualNP.Outside.L_meta_37247
open PEqualNP.Outside.L_meta_37247.Model
def q1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def q1K4 : Nat → Nat
  | 0 => 0x401240080df30dc31ed42ee42df32f641f940dd30f541fa40dd32de43de31dd43
  | _ => 0
def q1K3 : Nat → Nat
  | 0 => 0x2806c50540d4a12811d540c69aa5985654031d2a12834d520c6b2a1996550d41
  | _ => 0
def q1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 14
  | 3 => 9
  | _ => 0
def q1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt q1K5 (i*5) 5
  | 4 => packedAt q1K4 (i*16) 16
  | 3 => packedAt q1K3 (i*27) 27
  | _ => 0
def q1I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt q1K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/11+packedAt q1K4 (224+(h % 11)*4) 4) % 14)
  | 3 => 2*((h/3+packedAt q1K3 (243+(h % 3)*4) 4) % 9)
  | _ => 0
def q1Pos : Nat → Bits
  | 1 => 0xcd9bb8e718e718e79ce7b260cd863f1cfa270f
  | 2 => 0xf1edff07e0f81f07eff9c3830e07c7ff1849f3
  | 3 => 0xfe0edff800ffe007f0fe7c03f007f81fe48e3c
  | 4 => 0xf1fffff000007ff007ffc0007ffe0070fc0
  | 5 => 0xfff01ffffffffff800007ffffff8000007f000
  | _ => 0
def q1Neg : Nat → Bits
  | 1 => 0x9224483141223108c1481228450a0944522305
  | 2 => 0x4020102024040210002008108104208004052
  | 3 => 0xd13240949402520a80e412a0249092848c28
  | 4 => 0xab70fc94d016949c48d57b58214724c2d70f80
  | 5 => 0x0
  | _ => 0
def q1Atlas : Atlas := ⟨5,rawDecor 62 q1Pos q1Neg, 0xfffffffffcf0fcc0fffffffffcf0fcc0fffffffffcf0fcc0fffffffffcf0fcc0fffffffffcf0fcc0fffffffffcf0fcc0fffffffffcf0fcc0fffffffffcf0fcc0, q1N, q1R, (fun _ _ => 0), q1I, []⟩
end PEqualNP.Outside.L_meta_37247
namespace PEqualNP.Outside.L_meta_37247
open PEqualNP.Outside.L_meta_37247.Model
def q4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def q4K4 : Nat → Nat
  | 0 => 0x10000000203001606ef21bd43bd42be40bf43bf42bd41dd31ed21df31f910fa10bf41bc40
  | _ => 0
def q4K3 : Nat → Nat
  | 0 => 0x4000000390004d5444096a9081b1414438a6290f44c51096a96871d53d0bc242884754c40
  | _ => 0
def q4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 14
  | 3 => 9
  | _ => 0
def q4R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt q4K5 (i*5) 5
  | 4 => packedAt q4K4 (i*16) 16
  | 3 => packedAt q4K3 (i*27) 27
  | _ => 0
def q4I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt q4K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/18+packedAt q4K4 (224+(h % 18)*4) 4) % 14)
  | 3 => 2*((h/17+packedAt q4K3 (243+(h % 17)*4) 4) % 9)
  | _ => 0
def q4Pos : Nat → Bits
  | 0 => 0xfceef8f73e7c7c731e3e189e7c738cf380ac6e
  | 1 => 0x7f777f07cf9f9f83e7cfe0e38f8c0f3cf95093
  | 3 => 0x9f879ff80fe01ffc07f07f03f00ff03f06631c
  | 4 => 0x1ff81ffff0001ffff8007ffc000fffc00783e0
  | 5 => 0xe0001fffffffe00000007ffffff0000007fc00
  | _ => 0
def q4Neg : Nat → Bits
  | 0 => 0x1000011020084042040000414008410080426
  | 1 => 0x0
  | 3 => 0x28382920a40929204c02a902a125202a126118
  | 4 => 0xd003d24201525242009552a8024a4a802582c0
  | 5 => 0x1addfc84a958036a9529fcd34b60628a47f800
  | _ => 0
def q4Atlas : Atlas := ⟨5,rawDecor 59 q4Pos q4Neg, 0xffeeeeeeffeeeeccffeeeeeeffeeeeccffeeeeeeffeeeeccffeeeeeeffeeeeccffeeeeeeffeeeeccffeeeeeeffeeeeccffeeeeeeffeeeeccffeeeeeeffeeeecc, q4N, q4R, (fun _ _ => 0), q4I, []⟩
end PEqualNP.Outside.L_meta_37247
namespace PEqualNP.Outside.L_meta_37247
open PEqualNP.Outside.L_meta_37247.Model
def q6K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def q6N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def q6R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q6K4 (i*5) 5
  | _ => 0
def q6I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q6K4 (5+(h % 1)*1) 1) % 1)
  | _ => 0
def q6Pos : Nat → Bits
  | 0 => 0x9f8f38f9fc7c398e3e0e33cf8f9c319f01ae4e
  | 1 => 0xeff03f3e3f9fc1ffcff03c71f0e03fe3f25073
  | 2 => 0xf3ffc03fc01ffe0ff03fc07e00ffc1fc0c639c
  | 4 => 0x3ffffc0001ffff0003fff8000fffe000f83e0
  | 5 => 0x3ffffffffe00000003fffffff0000000ffc00
  | _ => 0
def q6Neg : Nat → Bits
  | 0 => 0x20818a0888848214404210828284948a108646
  | 1 => 0x0
  | 2 => 0x5120490112910280294405424290150246098
  | 4 => 0xfaa49205aa52a104956ab5004ad2ac0a4b8360
  | 5 => 0x5f4824a53003354929bd2a696c0308508f7800
  | _ => 0
def q6Atlas : Atlas := ⟨4,rawDecor 55 q6Pos q6Neg, 0xfefeeeeefcfcececfefeeeeefcfcececfefeeeeefcfcececfefeeeeefcfcececfefeeeeefcfcececfefeeeeefcfcececfefeeeeefcfcececfefeeeeefcfcecec, q6N, q6R, (fun _ _ => 0), q6I, []⟩
end PEqualNP.Outside.L_meta_37247
namespace PEqualNP.Outside.L_meta_37247
open PEqualNP.Outside.L_meta_37247.Model
def q8K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def q8K4 : Nat → Nat
  | 0 => 0x440f910bd42fa10bf42
  | _ => 0
def q8N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 4
  | _ => 0
def q8R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt q8K5 (i*5) 5
  | 4 => packedAt q8K4 (i*16) 16
  | _ => 0
def q8I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt q8K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/8+packedAt q8K4 (64+(h % 8)*2) 2) % 4)
  | _ => 0
def q8Pos : Nat → Bits
  | 0 => 0xf0fe3fc7f078c71ce38f8fc3f8e1c38f1b3993
  | 1 => 0xff1fc3f8ff80ffe303f1f1fc1f01fff025c1fc
  | 2 => 0x1ffc00ffff07fffc01fe001ffe03ffc60e1f
  | 3 => 0xffe00000fffff803fffe00001ffffc00f80fe0
  | 5 => 0xffffffff00000003ffffffffe0000000fff000
  | _ => 0
def q8Neg : Nat → Bits
  | 0 => 0x1642988813110a2021828248d82458a6091991
  | 1 => 0x224488012112000400909088490089220140b4
  | 2 => 0x888011244201401440124110248024846020a
  | 3 => 0x440132a48a40824aab24002294953004b80d40
  | 5 => 0x889123000c64a493d249493300182048f6a000
  | _ => 0
def q8Atlas : Atlas := ⟨5,rawDecor 47 q8Pos q8Neg, 0xfeeefeeefce0fce0feeefeeefce0fce0feeefeeefce0fce0feeefeeefce0fce0feeefeeefce0fce0feeefeeefce0fce0feeefeeefce0fce0feeefeeefce0fce0, q8N, q8R, (fun _ _ => 0), q8I, []⟩
end PEqualNP.Outside.L_meta_37247
namespace PEqualNP.Outside.L_meta_37247
open PEqualNP.Outside.L_meta_37247.Model
def q10K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q10K3 : Nat → Nat
  | 0 => 0x21b02e995c30be637ccae98de30
  | _ => 0
def q10K2 : Nat → Nat
  | 0 => 0x4009541cca5504308d420c2350b31
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
  | 1 => 0xffffffffffffffffffffffdff7fcfc7ff8f3cf
  | 2 => 0xffffffffffffffffffffffedf99f3f8e3f3d33
  | 3 => 0x76fe1fcff03fce3c
  | 5 => 0x78ffe00fffc00fc0
  | _ => 0
def q10Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffa010010012080045
  | 2 => 0x1224284484922512
  | 3 => 0x941501921248a28
  | 5 => 0x7851aae4986af80
  | _ => 0
def q10Atlas : Atlas := ⟨4,rawDecor 46 q10Pos q10Neg, 0xfcccfcccfcc0fcc0fcccfcccfcc0fcc0fcccfcccfcc0fcc0fcccfcccfcc0fcc0fcccfcccfcc0fcc0fcccfcccfcc0fcc0fcccfcccfcc0fcc0fcccfcccfcc0fcc0, q10N, q10R, (fun _ _ => 0), q10I, []⟩
end PEqualNP.Outside.L_meta_37247
namespace PEqualNP.Outside.L_meta_37247
open PEqualNP.Outside.L_meta_37247.Model
def q11K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q11K3 : Nat → Nat
  | 0 => 0x636997631dc65e8c3c987531
  | _ => 0
def q11K2 : Nat → Nat
  | 0 => 0x324c930d1314c314c931
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
  | 3 => 2*((h/2+packedAt q11K3 (90+(h % 2)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q11K2 (78+(h % 8)*2) 2) % 3)
  | _ => 0
def q11Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffbe93b368ec8f
  | 2 => 0xffffffffffffffffffffffffffdf1cdc70f533
  | 3 => 0xefe0ef80fa3c
  | 5 => 0xffff0fff03c0
  | _ => 0
def q11Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffff422441212085
  | 2 => 0x244124424112
  | 3 => 0x180a1a048228
  | 5 => 0x0
  | _ => 0
def q11Atlas : Atlas := ⟨4,rawDecor 46 q11Pos q11Neg, 0xfffffffffcc0fcc0fffffffffcc0fcc0fffffffffcc0fcc0fffffffffcc0fcc0fffffffffcc0fcc0fffffffffcc0fcc0fffffffffcc0fcc0fffffffffcc0fcc0, q11N, q11R, (fun _ _ => 0), q11I, []⟩
end PEqualNP.Outside.L_meta_37247
namespace PEqualNP.Outside.L_meta_37247
open PEqualNP.Outside.L_meta_37247.Model
def q12K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q12K3 : Nat → Nat
  | 0 => 0x20000b82e18df30ba6178c6f195c32
  | _ => 0
def q12K2 : Nat → Nat
  | 0 => 0x8e428c65906328c424c2510530
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
  | 3 => 2*((h/16+packedAt q12K3 (90+(h % 16)*3) 3) % 6)
  | 2 => 2*((h/1+packedAt q12K2 (104+(h % 1)*2) 2) % 4)
  | _ => 0
def q12Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffdff3ffff1ffff1ff
  | 2 => 0xffffffffffffffffffffffedfc7f3fe3f0fe73
  | 3 => 0x76ff8fcffc7f0f9c
  | 4 => 0x78fff00fff800fe0
  | _ => 0
def q12Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffa0180202049440a5
  | 2 => 0x122324452122a652
  | 3 => 0x9416819484a2b18
  | 4 => 0x78a4eae920ccde0
  | _ => 0
def q12Atlas : Atlas := ⟨4,rawDecor 30 q12Pos q12Neg, 0xfcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0, q12N, q12R, (fun _ _ => 0), q12I, []⟩
end PEqualNP.Outside.L_meta_37247
namespace PEqualNP.Outside.L_meta_37247
open PEqualNP.Outside.L_meta_37247.Model
def q13K5 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q13K4 : Nat → Nat
  | 0 => 0x9000006e000001c021f843f8c3e107c30fc63f4c7f087f32f863f4c3f987f21fe41f8cbe197d21fa41f887e087d10fc41fc43e997f31
  | _ => 0
def q13K3 : Nat → Nat
  | 0 => 0x11c008048008a5000002ca00460002d90430b5410c2d90420ae42042710d109e43c86b508309d43886790c10ac42442d504209e43082d10520e521086d50732ae42cc6dd0520af424c354c431af42442790e21b4414c2d50632b6418ca7d0d20ae420c334c832ad42cc6dd0530b641ccab50a319d43c867d0d10ad42042750c209d43042b90a31ac424c2710d20
  | _ => 0
def q13N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 24
  | 3 => 39
  | _ => 0
def q13R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt q13K5 (i*4) 4
  | 4 => packedAt q13K4 (i*15) 15
  | 3 => packedAt q13K3 (i*26) 26
  | _ => 0
def q13I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt q13K5 (4+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/15+packedAt q13K4 (360+(h % 15)*5) 5) % 24)
  | 3 => 2*((h/20+packedAt q13K3 (1014+(h % 20)*6) 6) % 39)
  | _ => 0
def q13Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffbff7fffe3ffff1ff
  | 2 => 0xffffffffffffffffffffffd5f8e73fc71c7e93
  | 3 => 0xe6ff07cff81f8f1c
  | 4 => 0xf8fff80fffe00fe0
  | _ => 0
def q13Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffff4010000009040025
  | 2 => 0x2a264a4642496692
  | 3 => 0x1942d41a90932b18
  | 4 => 0x78486ad24c24dc0
  | _ => 0
def q13Atlas : Atlas := ⟨5,rawDecor 30 q13Pos q13Neg, 0xfcccccc0fcccccc0fcccccc0fcccccc0fcccccc0fcccccc0fcccccc0fcccccc0fcccccc0fcccccc0fcccccc0fcccccc0fcccccc0fcccccc0fcccccc0fcccccc0, q13N, q13R, (fun _ _ => 0), q13I, []⟩
end PEqualNP.Outside.L_meta_37247
namespace PEqualNP.Outside.L_meta_37247
open PEqualNP.Outside.L_meta_37247.Model
def q14K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q14K3 : Nat → Nat
  | 0 => 0x840042f995c31ba6178c6f985d32
  | _ => 0
def q14K2 : Nat → Nat
  | 0 => 0x8d42cc265033299400c6350831
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
  | 2 => 2*((h/1+packedAt q14K2 (104+(h % 1)*2) 2) % 4)
  | _ => 0
def q14Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffddf39cfc7e39f70f
  | 2 => 0xffffffffffffffffffffffeffdff3f8ffe39f3
  | 3 => 0x76fe1fcff03fce3c
  | 4 => 0x78ffe00fffc00fc0
  | _ => 0
def q14Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffa21829041288a305
  | 2 => 0x1020004084100052
  | 3 => 0x941501921250c28
  | 4 => 0x7891aae4985af80
  | _ => 0
def q14Atlas : Atlas := ⟨4,rawDecor 30 q14Pos q14Neg, 0xfcf0fcc0fcf0fcc0fcf0fcc0fcf0fcc0fcf0fcc0fcf0fcc0fcf0fcc0fcf0fcc0fcf0fcc0fcf0fcc0fcf0fcc0fcf0fcc0fcf0fcc0fcf0fcc0fcf0fcc0fcf0fcc0, q14N, q14R, (fun _ _ => 0), q14I, []⟩
end PEqualNP.Outside.L_meta_37247
namespace PEqualNP.Outside.L_meta_37247
open PEqualNP.Outside.L_meta_37247.Model
def q15K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q15K3 : Nat → Nat
  | 0 => 0x80008ae995d31b86178c2f98df32
  | _ => 0
def q15K2 : Nat → Nat
  | 0 => 0x408d42cc65504308d420c2550732
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
  | 2 => 2*((h/8+packedAt q15K2 (104+(h % 8)*2) 2) % 4)
  | _ => 0
def q15Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff7fcfc7ff8f3cf
  | 3 => 0xffffffffffffffffffffffedf99f3f8e3f3d33
  | 4 => 0x76fe1fcff03fce3c
  | 5 => 0x78ffe00fffc00fc0
  | _ => 0
def q15Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa010010012080045
  | 3 => 0x1224284484922512
  | 4 => 0x941501921248a28
  | 5 => 0x7851aae4986af80
  | _ => 0
def q15Atlas : Atlas := ⟨4,rawDecor 57 q15Pos q15Neg, 0xffaaaaaaffaaaa00ffaaaaaaffaaaa00ffaaaaaaffaaaa00ffaaaaaaffaaaa00ffaaaaaaffaaaa00ffaaaaaaffaaaa00ffaaaaaaffaaaa00ffaaaaaaffaaaa00, q15N, q15R, (fun _ _ => 0), q15I, []⟩
end PEqualNP.Outside.L_meta_37247
namespace PEqualNP.Outside.L_meta_37247
open PEqualNP.Outside.L_meta_37247.Model
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
end PEqualNP.Outside.L_meta_37247
namespace PEqualNP.Outside.L_meta_37247
open PEqualNP.Outside.L_meta_37247.Model
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
  | 2 => 0xffffffffffffffffffffffdff39fff1c3ffc9f
  | 3 => 0xebfc1f3fe03f8f1c
  | 5 => 0xf3ffe03fffc00fe0
  | _ => 0
def q17Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff4061010824892131
  | 2 => 0x2088281109124486
  | 3 => 0x1523506a42a52b18
  | 5 => 0xe0a1ab493064ec0
  | _ => 0
def q17Atlas : Atlas := ⟨3,rawDecor 45 q17Pos q17Neg, 0xfaaafaaaf0a0f0a0faaafaaaf0a0f0a0faaafaaaf0a0f0a0faaafaaaf0a0f0a0faaafaaaf0a0f0a0faaafaaaf0a0f0a0faaafaaaf0a0f0a0faaafaaaf0a0f0a0, q17N, q17R, (fun _ _ => 0), q17I, []⟩
end PEqualNP.Outside.L_meta_37247
namespace PEqualNP.Outside.L_meta_37247
open PEqualNP.Outside.L_meta_37247.Model
def q18K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q18K3 : Nat → Nat
  | 0 => 0xc200403610dc31f02178c7d886e21
  | _ => 0
def q18K2 : Nat → Nat
  | 0 => 0x3808410d03104310c421
  | _ => 0
def q18N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
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
  | 2 => 2*((h/1+packedAt q18K2 (78+(h % 1)*2) 2) % 3)
  | _ => 0
def q18Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffbf0fffc3fe3f
  | 2 => 0xffffffffffffffffffffffffffffffffffffff
  | 3 => 0xffffffffffffffffffffffffffdff0fffc3fc7
  | 4 => 0xefff0fffc3f8
  | _ => 0
def q18Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffff41e222e2661b
  | 2 => 0xffffffffffffffffffffffffff0224454488ed
  | 3 => 0x244e89aa3346
  | 4 => 0x1888ee3323b0
  | _ => 0
def q18Atlas : Atlas := ⟨4,rawDecor 29 q18Pos q18Neg, 0xf0a0a000f0a0a000f0a0a000f0a0a000f0a0a000f0a0a000f0a0a000f0a0a000f0a0a000f0a0a000f0a0a000f0a0a000f0a0a000f0a0a000f0a0a000f0a0a000, q18N, q18R, (fun _ _ => 0), q18I, []⟩
end PEqualNP.Outside.L_meta_37247
namespace PEqualNP.Outside.L_meta_37247
open PEqualNP.Outside.L_meta_37247.Model
def q19K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q19N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q19R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q19K3 (i*4) 4
  | _ => 0
def q19I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q19K3 (4+(h % 1)*1) 1) % 1)
  | _ => 0
def q19Pos : Nat → Bits
  | 0 => 0xb7c7cf38fc7f073c
  | 1 => 0xffffffffffffffffffffffdff9f3ff1f87f9cf
  | 3 => 0xffffffffffffffffffffffe7fe03ffe007fe0f
  | 5 => 0xfbfffc3ffff80ff0
  | _ => 0
def q19Neg : Nat → Bits
  | 0 => 0x487490582531631c
  | 1 => 0xffffffffffffffffffffff2094040909122145
  | 3 => 0x1921aa324264ce0a
  | 5 => 0x60102a492408ca0
  | _ => 0
def q19Atlas : Atlas := ⟨3,rawDecor 43 q19Pos q19Neg, 0xeeeeeeeecc00cc00eeeeeeeecc00cc00eeeeeeeecc00cc00eeeeeeeecc00cc00eeeeeeeecc00cc00eeeeeeeecc00cc00eeeeeeeecc00cc00eeeeeeeecc00cc00, q19N, q19R, (fun _ _ => 0), q19I, []⟩
end PEqualNP.Outside.L_meta_37247
namespace PEqualNP.Outside.L_meta_37247
open PEqualNP.Outside.L_meta_37247.Model
def q20K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q20K3 : Nat → Nat
  | 0 => 0x10010bd085d31be63bc87690f910
  | _ => 0
def q20K2 : Nat → Nat
  | 0 => 0x314c521e12144344c510
  | _ => 0
def q20N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
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
  | 2 => 2*((h/1+packedAt q20K2 (78+(h % 1)*2) 2) % 3)
  | _ => 0
def q20Pos : Nat → Bits
  | 0 => 0xbea673b7606e
  | 1 => 0xffffffffffffffffffffffffffff3bbc3bbc93
  | 3 => 0xdfc3cfc3c31c
  | 4 => 0xeffc0ffc03e0
  | _ => 0
def q20Neg : Nat → Bits
  | 0 => 0x424880910426
  | 1 => 0x0
  | 3 => 0x241415020918
  | 4 => 0x18016a2012c0
  | _ => 0
def q20Atlas : Atlas := ⟨4,rawDecor 27 q20Pos q20Neg, 0xffeeeeccffeeeeccffeeeeccffeeeeccffeeeeccffeeeeccffeeeeccffeeeeccffeeeeccffeeeeccffeeeeccffeeeeccffeeeeccffeeeeccffeeeeccffeeeecc, q20N, q20R, (fun _ _ => 0), q20I, []⟩
end PEqualNP.Outside.L_meta_37247
namespace PEqualNP.Outside.L_meta_37247
open PEqualNP.Outside.L_meta_37247.Model
def q21K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q21K3 : Nat → Nat
  | 0 => 0x4020803c187a10f041ecc3d907910
  | _ => 0
def q21K2 : Nat → Nat
  | 0 => 0x809843442a10910aa42cc2690f20
  | _ => 0
def q21N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
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
  | 2 => 2*((h/15+packedAt q21K2 (104+(h % 15)*2) 2) % 4)
  | _ => 0
def q21Pos : Nat → Bits
  | 0 => 0x5af0f9cf1f8707cc
  | 1 => 0xffffffffffffffffffffffefff3fffe3fff8ff
  | 2 => 0xfffffffffffffffffffffff3ffc1fffc07ff0f
  | 3 => 0x7cfffe0ffff80ff0
  | _ => 0
def q21Neg : Nat → Bits
  | 0 => 0x251e929704b163cc
  | 1 => 0xffffffffffffffffffffff9022800121122055
  | 2 => 0xc44350a4844cd0a
  | 3 => 0x38821ac92608ea0
  | _ => 0
def q21Atlas : Atlas := ⟨4,rawDecor 15 q21Pos q21Neg, 0xecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0, q21N, q21R, (fun _ _ => 0), q21I, []⟩
end PEqualNP.Outside.L_meta_37247
namespace PEqualNP.Outside.L_meta_37247
open PEqualNP.Outside.L_meta_37247.Model
def q22K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q22K3 : Nat → Nat
  | 0 => 0x4100003d187a10f041e4c3d907910
  | _ => 0
def q22K2 : Nat → Nat
  | 0 => 0x4100b141082c506309943842650c20
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
  | 3 => 2*((h/9+packedAt q22K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q22K2 (104+(h % 8)*2) 2) % 4)
  | _ => 0
def q22Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffd6f1933c738e7993
  | 1 => 0x67fe1fcf83ff81fc
  | 2 => 0xfffffffffffffffffffffffbffe3fffc0ffe1f
  | 3 => 0x7cfffc0ffff00fe0
  | _ => 0
def q22Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa91d264c18e36991
  | 1 => 0x18254014812520b4
  | 2 => 0x44008012008020a
  | 3 => 0x38802aa4a404d40
  | _ => 0
def q22Atlas : Atlas := ⟨4,rawDecor 15 q22Pos q22Neg, 0xfce0fce0fce0fce0fce0fce0fce0fce0fce0fce0fce0fce0fce0fce0fce0fce0fce0fce0fce0fce0fce0fce0fce0fce0fce0fce0fce0fce0fce0fce0fce0fce0, q22N, q22R, (fun _ _ => 0), q22I, []⟩
end PEqualNP.Outside.L_meta_37247
namespace PEqualNP.Outside.L_meta_37247
open PEqualNP.Outside.L_meta_37247.Model
def gbK10 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK9 : Nat → Nat
  | 0 => 0x30064493070000010d120020e109000812007f54c01ff43007fd0801fe10007f88401fc20007f8c001fd42007f10401ff20007f4c001fe42007f48401ff10007f94c01fc40007f0c401ff40007f08401ff21007f44001fc10007f54801fd31007f88001fe40007f94801ff41007f55001fd43007f94001fd20007f0c801fe43007f94401fe41007f54401fd50007f0c001fd41007f10c01fd32007f8c801fd40007f95001fc42007fcc001fe31007fcc801ff31
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x14a000ff50d20007fc6518803fd51504017fb1a4200ff8c740007fc4220003fc43c84017d3008200ff58f42005bec690803ff3188001ff29c8400f74c931006f8caa0003ff438c801fe9926200bfd8132007fe8419002fc64544017f3226000ff8ca41007fa86a8803ff648c801ff21aa000ff90951007fc8498803ff64484017fb128000bf5884003f78a9a0803ff604c401fea106400fe48020005fec0a1003fd43884017f3206000ff94a41005f2c020803fc42cc401fea1e4200bf59030007fc8390003fc4290401ff2a44200bfd91200077a82a0013fc544c4015fb22a400ff50721007fc8620803fd21cc001dea1a8000ffd0e42007fc6518003fe4308401ff192a200ff4c720007fe8290803ff2110001fe9884000efd0740007fa6498003ff32540017f3148400ffd0820007f88508003fc32904017eb008200ff10d41007fe8610003f741904017eb044200ff95321007fe8418002fd6290c017eb0c8400ff8c931007f64090003fe42884017fb1aa200ff90930005fcc890803fe42480017eb264200ff4c951007fe6528002fe6210001ff2926200ff50a32007fa63a0003ff32500017fb126005ffd4331005fac408002ff64c80017eb066400ffd0d52007faa498803fd3188001fea164000bf99231005f8c919003ff4394801fe2146200fe50110005fac198827ff538c801ffa1c4003ff143210077e8421003ff428c801ff2164200ff58c42005fec4a1802fd648c801feb2c6400bf191520077a8721003fc21900017f3208400bf99232007ee4290817ff51cc401ff1926000bf58e10007fc6490003fc32480017eb24a200ff90b41007fa42a0002de6308407fe2a64200bf58443007fca720803fc424c411ffa906400ff98f20005fac721002fd6090401fe31a8200efd0d41007fc4210002fd610c001fe192a200ffd823202ffea998803fc428c001ff2988400bf18954007fc4390003fd54cc801fe9928200bf98a53005fac220003be4250001ff31c8400ff0c550007fa42a8003fc3288413ffa946400ff8ca210077c8420803fd5348401ffb0a8600ff88740007f864a0803fe5310409ffa8a6200bf58732007fe43a0003ff2108001dfa148400ffcca10007f884a8802fd62c4001ff1086000ff10e42005fac32a003ff6150001fea1a6404ffd4131007fa4328002ff6344001ff2a26400ffc87200057cc810803fe43d08017f324a600bf59331007faa7a0802fe6204001ff3126200bf98a40007fc6590803fc31940017c302a400ff0cb21007f862a0002fe62cc0017fb028600ff94b2104ff8cb19003fc43080017fb264200ffd8d40007fa8421027fc528c811fe2906400ff58f41007fa6420003fc21cc001ffa0ca000ffc8430007fe6290803df324c4017e3224200bf58e20007f886a9002fe620c401ff98c8000df99442
  | 1 => 0x3ff534c401ffa1a8400ff58f20007f8c898803bc42d0001fe21c2000ffd0d32007fca710803fd32540017f314a200ffd894102ff8a598803fd534c801ff30c8400ff99131007fa6298003fd31480017fb12a600ff99232007faa719003fc32c4001fe3226400ff55132005fcc5a1803ff644c401ff1962000ff98c42005fac5a0802fd6008401fe214a200ffd8931007de8521002fc64440017eb248200ff4c940007fcc319002fd644c401ff29e4200ff4ca50005f8c4a9803fd514c401ff212a000bf58e41007fc8420802ff63548017f3148200ffd0d51007fa849800fff53c8401ff10a6000ff90821007f88490813ff524c401fe2084000bf58d10005fac810002fe64480017eb248600dfd9540005fac790802fe64cc001ffa1c4200ffc8630007f88418802fd6294c017fb0a8600bf58830005fcc928003de328c4017eb046400ff50951007fe84a8802fd6284001ff192a000ff10810007fc6420803fb4050001fe192a000ffcc440007fe6520003fe43440017eb108600fd48421005fac719003fc3294017dfaa48400ff4c721005fac710803fe31100017eb1e8400ff084200077e86a0002fd6290409fe2926200ff10e41007fe8790802fe64084017eb226400ff08720007fa8718803fe54cc4017f3108400ff8c940007fc6528002fe62d0001fe1928000fe90110007fc6410802ff6454001fe1904200bf98a50007fca410802fd60c84017eb0e8000ff90d21005fac990003fe548c401ff9922000bfd8d50007f843a0003ed32c8401ffb0c6400bf9933202ff8a198803fe5350401fe1086000bfd8131007fa6508003fc410c001ff2908200bf98832007dc6590803ff214c001ffa148400bf58420007fec688002ff64544017f3244000ff98743005dcc418803fd43d0801ff21ca200bf58c40007be8721803fd414c4017eb0e4000ff10d42007fc87a0802fe620c001feaa0640aefd504201ff8cb90803ff654c401fe90c80009fd9540007faa3908027d650c4017eb182000bf99040005fcc598803bd43d0401ee9966200bf58841007fa6220003ff4350401fe30a8600bf58442007fe84a0802fd63940015eb204200ff55232007f8c090803fd644c401fea1a6200f7d0d43004faca21002fe62080017eb0ca400ff90b31005fcc508003ff32d0401fea988400ff8ca10007fec488003ff4350c0bfe2a66200ff98b430057cc928803ed4210801ff2146200ff0ca100057ac808003fc4354401fe18c8000bf58632007fc8788003ff3108001ff2946200bf58a54007fa8298013fc504c401fe21c4200ff94b31007f88528003ff31c8001fea0a4000f70ca31007f88410803fe3108001ff3026200ff50d30007fa428800ffc52c8401fe9946000ff19121007fc6390003ff31d0001fea966200bf19130005fac728803ff62500017eb
  | 2 => 0x50007fa84a8003ef42508013eb286400af99010047fea819027ff548c8017f3148600ff50d10007fe8610807f85044001fe30a6000bf582430057ac818802fd6244001fe3246400ffd0a50007fa85988037d65c8001fe21ca200bf58c20005fec919002be640c4017eb106200ff90f20005fac918802fe648c001ff10aa000ff95031007fa8290803fd2110001fe3128200ff08530007f8c498003fc63c8401ff2a24200ff0c440007f88608002fd6010801fe3046400bf99331007fca7a1003fe42cc8017fb22a600ef50740007fa8690802fd638c401fea9c4200ff50730007ee4310803fc6250001ff21ca400afd9121005fac1a1003fd62d0401fe1908200ffd0541007f8c098803fe4354801dea1e8000ffd8d41007fe6410003ff42cc401fea1e8200bfd8950005fac121002dc6348401ffa142000ffccb20007fc8418803fd4394401feb126200ff90921007fa6488003fc64c8401fe98c2000fed0240007f86528803fe2150001ff9968000bf58e30005fac890803f930840017eb204200ff8c630007f24108003fd53c8401beb288400bf99043027fcca98803ff43840017f3104200ff54e42005fac808002fe640c8017eb0e600aef15042005fac888003fe520c401ff2122000bf18940005fac610802fe64948017f324a200ff8c910007f8c4a1802fd62cc4017eb224000ff0ca40007f44088002dd63084017eb144000ffd0e4105f78a921002ff64440017e3226200bf98b10005fcc898803fd604c4015e322a400ffd0e31005fec2a9803fd43c4001df2168000ff18d42007fa65a0803fc31d0001ffb1a4000ff50d50007fec790803fc43940015eb244000ff95131007fc6490802fd61900017fb028200bfd9130007f86488002fd63950017eb24a000ff90c42005f2c018803fe6110801feaa44200bf59310005fec8a9003fc63440017f3204000ff10c21007fac5a1803f94010001dea188400ffcc520007fcc390002fe64c8401fea9a8200ff48420007fc8528803fd21c8001ffb0a6000ff8c530005f8c488002fd6010c017fb126200ff90b30007fa6318002fd6494801fea9a8600bfd8f20007f86210003fc31c8001ff20a6000ff0c9210077e87a0802ff61540017fb226200ff54731004faca10803fc42cc8015eb266400ff55321005fac018802ff6155001dfa168200ffd0420005fac518803fd21d0001ff194a200f750c4302ffea598803ff434c401fe9086000ff94d42007f8422001bbf5450401ffa146000ffc861000ff6a088003fe32d0401fea184200ef50b41007fcc7a0803fc32d0401ff1902000ffd8d21007fe8310002fc6454c01fea188200ffd0430007f86408003fe54084017cb004200ff90b10007fa8498802ff60484017eb242000f7d8d21007faa5a0803fe52d0401ffa126200bf58231007fc431801
  | 3 => 0xe2806400ff08540007fecb19003fc618c801fea984203ffd4721007f84328002fc6250c01fea988200bf59221006f8ca88003fc32c8001fe9904000bb588310057ac818003be42904017eb188200ff94d210077e8721003fd32c80017eb0e8600bf58a40005fac788003fd31440017fb226400bfd8520007f24088002fe64c8001ff90aa000ff8c932007f88328003fd61c8001fc9822000ff10941005fec4a8803de324c8017eb244000f74c832005fcc899003fd218c001ff992a200ff4cb40005fec6a1003fe428c801fe31a4200ff90f21007fc8590002fd6194c01ff1944000ff4c521005fac1a1802be640c001fea188400ef90942005fac321803f541104017d3004208ff15032007fa8488003fe420c8017eb246009ff15232007fca7a0803fb2088001fca042000ffd0630007faa521003fe32080017e3126200bf19321005f8c4a8803fe5290801ff20e6000ffd0d21007f86410002fd63d0401ff10c8000ff94a32005fac720003fe3290011ffa886400ff8cb20007fe8298802bd64944017eb006400ff4ca40005fac999013fc654c4017fb12a800ff55021005fac929803bf43d0001ff90c8000be98031007f865a0002fc624c001ff1968000ff58743007fe8728802fe6488401fe3026400fb4c921005fac310003ff4304001ff98aa000bf58742005fac920003fd520c801ff2906400ff48530005fcc988002fc644c801fe3122000ff54a32007f86510003fe4210801ff18aa000be58251007fa85a0803fd538c401ff3046400ff88650007fec990803fd42cc0017eb1a4200ef50d41007fe62a0002ff63c84017fb0a8400ff59531007f88499002fc64c8001ff98ca000ff54521005fac1a0803ff41c8405fda864000bf98a31007fe4288003fe3194001fea9e8400ffd8943007be6519003fc428c801ff18a8009ffd4232007fa8398803fc60c8401fe2144000ef10a41005fcc420803fd51d0401feb0c6400fb8c921005fac5a1803ff32504017fb128200bf58b40005fac998003fe21cc001fea9e8600ff58442007fe6420002fa6094411ffa806400ffd8121007faa998803fe5308401feb0c8400ffd8132005fec6aa003fe4154001fe98aa000ff10820007fe42a0002fe640c413ffa8c6400ffd83210077e86210027f65440017f3146000ff54d31007faa720803fc43484017fb1a4000bf59032004facb98003fc624c401fea0a2000bf58a51007fca999003ff6350801fe2106400ff08630007faa6a1003ff65c8401dea108400bfd8530007fac721003fc420c001fe20c6000bf98b41007fca421003ff31c8401feaa46200efd0540007fec899003fd544c401ff90e6000ff54842007fe8728003fd3150001feb246400bf18950007fe6308002fd62cc0015e3224200ff98f42007fe8718002fd631080dde2a28200bf191
  | 4 => 0x104c03014000280202c172cc1800c5800006040080a8220000e00c6f0080f028415c00c01ca4708990ac0200802030000001b00c0901808018220584d0234e0481d06c0b00803118020001001c2b058320045900a110040200cb500c2001400004020b82e0380d00c0400c2e0040300800010000140a158b121c0100c4100019024000700902c0100492000151780f5fc64034000380800400028f21e80000d6c02c0704002008000611900c1c0380f0100034c02000010000701c36010830000200801038490b8e20d40202403138042981d160a10080201000000008f8040002155804088000000100c5207994048060140500002014eb018010002352422081580005d2d00e06117000500440600409024000780a0a8040c4010a40002c010080a0a8380d806014070040b0e0041280600c000004d00002098000cc06000011741102c110000f014010146a00db50001202c19008260d80000c0300c040c00004c0100c0604c0955c00048000000c0cc03114210103a00c01014110300200800018f900c060240000001004231a597000070140189c0002802058070000e0000d00043178580a4004382a00016108030441b0000000c00004b1004050280705c0b0384a07c010000039c320082d00c0c018140057cc999002ff6154811fe2886409ff14632007f88729003fe319000fdfaa68200bf58610007dc8421003fc4388013ff32c6400bf990100057cc910002fd6348001ff21c4200bf58432017f0a190013ff544c4017fb122000bf59242005fac8188037e65c8001bfb2a2000ff18540005fac510803fc3210007fe29e4200ff50e32007fec498002fe6444001feaa24200efd0941007fa8390003ff31440017f3122000ff18d20007f88510802ff6150001fba0a8200bf59130005fcc908003fe32504017fb1a8000ff5503101ffea990803fd21840017e3128200ff50f20005fec890803fe3210001dea128200ff95232005fec299003bc6448401fd1822000bf98843005fac518002fe6410401fe31a8000ff94941007bc6418803fd5250401de2108200bf58e52007b8c690802fd63d00017db02a400bf58650004facb90003bc4250001fe2164200ff58232007fa8729003ff4184001ff21a4000ff9093201ffea190802fd618c001ff2a06400bf19120007fa86a9002fe62950017fb1a8200ff98b410077ec890803fd3194001ff90ca000ff50550007fe8398827fc508c801ff21aa200ff4c640007f842a8002fd63c8011f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0xd7308740007ed4210931005fe76109310067f650c540005fd728c5300b5fe70d0d31006bd64d0e1010dfe7010821006fc6258131007e632c8521006fd644ca3021fee320c840004ff7359020005ff7150f42006ff7654c42095fc704c521004fe72d8d51006bf64cc521006dd6354c21005f97008630005bd7110b4001e7c65c8510007ee708cb21005fe7290530006fd65d0e30086fc6110d42005fd71d0e200b7ef204c4200eeff64cca10007ed548c921006fd65d0531086fc6110d52006fb4318152006be6490e51257f73155131007bf434c540006be6450c21007be428c740256fe6355021007bf64d0f21006fd5458432007f5514c510006bd71d9152004fd7610831006fd65ccb41004fe7690d100077e5054d43006f5618c630005ff7055032004fd76d06300067f65885400077e548ca50117bf4088640226ff3159230216fc21d8131004fd760c820004ff7359251007be52d0d401977e6508730006bf4358642195fe7395021006fe624c740007be540c940004fd76d08321cefe62cc420087bc4118d41006fd7518931007fb214c2100067d6590c42006ee628c841005fe7298131005bd7490c42005fe748c931076fe608c841006fd650872009efe7258632005fe76cc9101a5ff7510e21006ff50d8f21004fc764c940007dd7394931005fd751863219fec3218132225fe73185400befc62cc610006bc6450510007ec328842011efd7608430127bf400c640006fc7648540006fe62d8131005fd7010a32006fe6258743005fd70d0d31007fb31d02400a5fe70d8f21266fd6310d51007bf4390a51006fd32d8550007f932d0240005fb73481100b7f6614c420217dd7308730006ff61c8530005fd7190f20005bf7448530267bd4310d51006bc5498b41004fe72d85540277f51d95310067e6598f202b6fe6354b41004ff7158f20005fd71d0d42066fc600c941004fe76d0d42005fd71cca402c7dc540ca31265fc7350951006fd6548630005fc724c53022efc32d8143006fc63d8940005f5710c910004fd7399120006fe7258442006ff4358a310d7bf404ca40006fe42d8530005ff704c721006fd43d8950004fd7690f20005fd7190d52005f5710c941006ff64d8121006bd64d0e201477c51cc650007bb4350210005df7348720227ef324c9400067c65d8d40004ff7358b40006dd630c44010fdd3008430006fe7198a30004fd71193200077c658c910006fd6550931006fd6448630005fd718ca100a5fe7010b21006fd7258743006bd64cc620085fd7610e2102f7c5054b31006ec62085301477c21d9510006fc7650d210067f654c940006bc6490d5210dff7608430106ff31d9132005fd718c950004ff7358654006fe549883123dfe738855009fee6248730005fe728c550117f6618843013fdf318c7400afee538cb21
  | 1 => 0xc9100feff6318d4209efe6348650006df6354d21006bc7359021006fe6448720006fe62ccb400277f545493113efd618c740007bd544cb40006fe7058432006fd658863012dfd768c420005fd75d0931006bd73d9152006fe7258642006fd75d8d42007ee3254721005ff7150d51007dd748ca310077c654c540005fc724c550007f74150531007bf64551311cdfe7390b20006bd6390a41006fd654c640005ee7294d21006fe6210430005fc724c610006fe62d06500efef20cc820067ef200ca2009efc6348510005fd73d09510067d65507201cdfe7388720006fd5358742007f551cc910186ff3299232006f850587200077d5310a5015efc43d8543007ef20948410b7fa404c610004fd76cca10007de7418d21007df3054c4209fec434c9210077e7510b3118ff5710cb100a5fd76c8430006fc7058442067bf400c84013f7d750c7400067d6598f200077e7510831007bf744854011ff97008430225fe7308540076fc648ca1001e7e65c872007dfd7310830006fe53587400d6fc604c9310aefc63c85400aefe63c8510006fd52d8d10006fd4358652226ff32583430057d7510a31006ee628ca31005fd7210430005de7308550007bd4354741006fe648cb10006fc640c910006fb4398021006ff7358720005fd738865008ff8328c110005fd75cc941007ec648c9210077e5090e512befd630ca5129fdc65cc931006fd6590f10007bd515074011efd6110430006ff4318941007bd54cc740005fe74cc721006be640ca20007dc6350d21007bc7448730007bd72d0d412efbf5410b31007bf4354941077f5108c81022dfe73c8740005ff7159232004ff7158c400277c754c650257f53155031004fc7258031005fd7590931005f97010630006fe70d8f21007fb724c210005ff7050b3125dff7395332005f5710cb21004fd711893009fdf7418d21005f57110d212b6fe6354a42006fe72d8d40006fd654ca30006fe768c951005fc72507310b77f504c650004ff7159232006fd6390a210b7bd404c440006bc649091009dff74cc521237ed320ca4023efe760c950005fd70d9131006fc54d8f21007ee324854015dfd73d0430005fe7690d5222fbf430cb40005fe7290f10006df75d8d210beff6118131006ff64cc550007bf7454c42004fd7198b43005f57110931004ff764cb41006ff62d8530007bd744c740005fd7394941006fe53d85420073d6550c42005fd72d8d40004fc7258d10066fe600c8410b5fc7054d31005ff754cb41006fc4398a501deff630c9200077d5350d52006fe619823215efc3299131005be740c9410fdff7350b300067e7518943006fc62cc550005ff764cb20006fc4358a1004e7e658c821006be6490f20006fe640c91001f7f5254f2112f7e508c550007bf744c640005f87054b31006ff65cc52013fd
  | 2 => 0x6fe6448610007bf7448430007be54487400afec438cb210effa40cca10006ff76487400467e650c821007f732d0541007bd540c740006ff74d8530115fd7688430006df6418d21006ff644c52104cff765483222eff329923022fbe5350f40006fd6348740006fd31191311a6fe638842009fee320c921006fd65cca402b77d5390d52004fc7259331006fd6548610005fd720c440005fd71d0e520077f6548540006ff65d813109efc5358632005ff754c931227f7314c540004bf7458d21004fd768c440007de328c440006be7299251006ff7654f410a5ff76c8430006dd638cb20004fd7690c21007bd73d9121096ff6548630005fd7550521005fd7090a32006fe644cb20096fc764864001d7e7518f21006fd658c821004fd71189400c6fc6350550005fd74d8131096ff6448430006fc72d8540006bf435874007efe531894325efe6395021005dd7308650004fd71d9132006fe5458432006fd654c540007fb31d0140007bc74c8740005fd7110d42006fc43586420067e7598a30087ee2110d21006df7558c21007fb3250040007bf43189411cfef328cb20006bf6499232006fc648c9320067d6590b20006ff6510d21007ed32c8650006fe725842009fee324843008ff5710c910005fd7190d10007f921d0140005bf74485500077e540ca50005fb7054b31004ff768c841004ff7359131006bf715922021efd630c840005df7350731196fc6308540004fd768c420115ff7688440005fd710c940215ff7308730007f9315004009fbf4390d21006bf7359010076fe7098832006fe644c630216ff6108730006fd4358a51005f57110e210efbd40cc840007bd5488740005fd708ca310aefc43d8532006fc7258c100067d65907301f7f8504c720004bc7458a31006fe64cc720004fd760ca10004fe76cc940077f8508ca10005df7348510006fd65d9232006fd658c440005fe7290550007bd54487402677e750c95104f7e758ca50227f5310c540086fe7610c21006df6350521005f5710c821006fd6558632005ff7050721007bf4354a42007ef6294931005ff7550e31007bd439844213efc21d8141007ee548c921006fc6418132006fd6550f20005fe7290d1009efe634872001e7f53d8552007bd5190b400077c65cc940005fd7010832005bd7418632007ed20d0e52005fd7348540007ee52cc520007bd72d0e4209efe6348420006ff658cb41006fc7258c41007bc7448740006fd54587320a6fc64c8430287bf5410831004fe7299251006be6490832005fc7250e31006fc4398810025ff7554931006f56118632005fd71909510077c650c910005fd7110d51006bf7159030005f5718c931004fd7690a5113efd768c740006fd54d8d20006ff62d813104e7c658c94009ff67110d21005fd7018931005fd70d8632007dc638
  | 3 => 0xc7454b31004fd7199332006ff4398821006ff65cc5100067f65d85400067d6598c421a6fe6388650005dd7390a32006bf4398b41005dc7348740004fe72d8d4005e3c6590940087dc31191310b5fe7099131006fa5358021006fd5158740006fe72d8d10006fe644ca100067d6508720005fd7010f21076fe6058232006ec628c931006fa4358041005fd7308440007df7348440004fd71191201cefe5358f20137ef2108440006ff65d0521007bf6495131006fc4358810004ff7159020005fb7350210006ff5158432007dd3094c41004fe76d0d41006bd64d0630007dd324c740007df63d0d21004fe721915314fee320ca100aefc63c8550006fd650c420005be74086300afee7294f21327bc544cb410c6ff3258743004fd7198a53257ed3255032006fc7458c10004ff7650720007ed5290d20006fe6398720004ff768c810076fc30d8d20006fc6498232005fe76cc941006fd65cc94023fee320c95008eff6318d10005fd7190f21075fc7050a32006fd654ca10005fd71cc940006fc43d85421a6fe63887200257c7558131007be5390841006fc7458432006fc4358a41006fd64485301cefd6390f200077e51d0a50006fa4358021066fc640ca10087de6310c2109dfd734843002f7f5495331006ee6248730006fe624c650006fd7598b31006be6450d10006fc6598931004fc7258743005fd75d0d21266fd63cc951006bf545864206f7d750c810006ec6294941004fc7258e51106fe63908310077d5254e31005fd71d0a50006bd6419232006be731912107efc63109212477f53cc650006fd7258630007dc644c9310057d7518632006fe32d8121007dd534853019dfe7310820005fc7258f41006fe64cc61010dfc7050c21006fc7458e10004fc7650f21106fc6390950006fd654c941006fd65d0e10006fe5498b31004fd7610e10006fd7118941005fd7494931067f5100c810005fd7110e20006ff63909510aefe63c8610297dc504c93124fbd4310e52006ff75d8540005ec7254d3225ff53195031007df638c951006fe6488720004bf7650842006ff65485100b5fe70d9531007be635084200d787550110006ec62cc941006fe644c440005fd7218d400067d65c8720006fe5398b41004fc7654f21096fe72587200077f65cc540006fd65cc610007de708c831006fd65d0c2013dff7308740265fe73d0951007df324c44018dfe7390b10006fc7058c4210efc6408430005fc7250530097ee6248610007f932d014015dfc7350b4106efd630c810005ec724c420005fd7395121005fc76d0d21005fd7510931006fe5258f10004fd7690832005fd750cb41006fd65cc420005f77150b31006df63909210adfe73d9321006fe640c720007bd438c740005fd7550731005ff7054c21004fd7694f41006f97018910005be7494941
  | 4 => 0xca50004fd73189510adfc74cc721006bd63d074025fed32950321cdff76cc720096ff65486400beff65cc640007bf748cb40007dd32cc6500c6ff630c9410b5fc7054931007fb6010d520a6ff65c8610005fd7190931007ee4210921006ff650c720005bd76d0e42005dd73908320a5fd76c8630006ff6390910005fd7110e52006ff7258440007f541cc510245fe7388650005fd718cb200077f654c9402b7ec3259632006fe768c92108fef328c91013fdd310c740007de328c550005fd7010c211d6ff3219131006fc7650521005fd7494d2112dfe7090a310363c6550540005ff7158c42007f5518cb10006fe52d8d40006fe5258642006ec624c94013fbf4108740005bf7454a3201e7e65c8730007bc428c740006ff7458720196fc6308550215fc7150b30007bc6450531107de7390b310c7ef328c941006fd6550730227ed320c940005fe7218530007f54148510006fd644c620005fd7090832007be5488740006dd630cb20196fc5318931007df64cc931006bd435804210efc3018910005f77154e31106fe6390a21006fd5358720004ff7654e210a6fe3098b1014efd760ca10005fc72505500a5fe720844009dff7648730006ff5198b31005fd74d89311d6fd6394c41004fe72d8131004ff7359132006fe4358652006f87258031007be70d9121005ff7150e522cfdf548ca31006fc764c550006fd650cb41266fd760c951005ed720c740075fd768ca100a7ee62c84300067d65d0832005ff704c931006ee628ca410777f508ca5004f7c548ca50006fd52d8540004fe768c921005dd739493107efc3219132007ee32d0721005ff7154d21007bd414c74011fbe7408430006fc6298131007f93150210106fd6394e42006fd768ca20006fd65d0e31006ff6348720006ff764c720097fa3048610005fd72cc740007dc735053104dfe720c951006ff6350510066fe6298232004fd7198b30006fc764c720005fd75d0d32006df71d8d21006f561cc620007be5250740004ff765083213efe219921022efe64cc840076fd6018232006fc4358620006ef620c941067f8500ca1008fdc630c91022fdf32cc740105fc7354a420467c650c940007dc7348630007df63cc510245fe73d0650005ff73484401d6fd6390c41075fe70d0e320067d75189310b6fd6018131006dc74d8d2113efc3199210006fd51d8d400adfe73d0721007be540c740007bf41c87400077e5090d52005fc764c940006ff65cc720006ff654c9100067d6550842006fe769092108fbd7418d10006fe6448530095fe7019121076fe608ca51006fc648c53004d7e7510a32005df73486500d6ff654ca40006fd650c821006fd5358442007dc328c440006fe5458732005fc7250d51007fa708c910004fe7694d4108dfe7390910004fe760c920007bd53d0e42005f
  | 5 => 0xb77e504c550006be6450f10007df4350d21006fd6310a21005ef7258131006fd644c910007bc6490931095fe70d052109dff7590d210af7d65c8730005fd7418131004ff7648420006df6350d21007be424c740004ff735802118ff431d813123efd630c950007df324c550004ff7158042006fe73584201d6fd7694c411477e51d0650006fc644c951004ff7358321005fd7490d21004fd7690b100afee32c8730004fd764c42024efe6394841004ff76c8440137f6310c440007bd4394b41006bd64d0c21006fd63d0a42005ff7054f21006ff64cc951006fd644c610005bf7350941006fc648c5500069c64d8d21005ff7158e42007ee4210932005ff7510831006bd6310a4115f7e750cb41005ff73c8440006fd62d8131007e5718cb21006fd768c950005fe7208530006de7258c21006ff5058432006fd64cc510006fd6590b30075fc7054e3215eff32d8543247ef328ca5011fde3118131004fd768ca410b5fd738c420006fb6098232007bf438c940007bf4350721006ff63c8510097be40485400b7bd7418131005dc7348420006ff4258650007f5518c910095fe7090d21005fd70d9531066fc3018930255fd7355332004ff7654b41126ff6118d1029fdf54cc931065fc7050832006fd614873021fbd74cc840006fe4258442005ed72d0e32226ff63cc9400c77e5354d41006fc764c540006fd5398a31004ff7158c20006bc64cc521006fc74d8553006fe7258730006fd6150720006ff654c521005fd73d81210a7df30c8630005fd71d8930007bf3250740005fc76509310f7f850cc91010dfe7188440007fb3250210107ef3290a32004fe7610931006ff65d0f21095ff7648420265fe728c951005fd72185302b77d5310d520067d6550f20006f5614c630006fc32d812109fbf4310d21006fe43d89500b5fd764c42008ff9700c910006bd6419131007be54cc740006ff65cc7212b5ff7654832007ed5250720005fc7454d31004ff7358a51005fd70d0e32135fe71cc840004fe760c940006fe635872020efe63907200077d6554f21007ee4210b31005fc7250f41005fe764c540005fd7095121007df3258131006fe639844218ff731d8131006dd63908210a7fa30c84300677f500ca50006fd63c8610006dd6350c21005fe7494d21007df630c951007df734853021ff7318c440006fd74d8d52006bd6494831006fd6448510007bd7019121005fe7498632004ff7159130006bc6450f200077d528c650006fc72d8530006ed628ca310adfe7390b210beff65cc550006fd7518910007be5290b40356fe43d8953235fe73c8640007bd5150f40076fc1098b300067d658c821006ec6288540005ff7510b31006ff63d8910004fd71d8f20006ff75d8530005fa768c1102677f530c951005fd75d0e21005fd70d0721246fd630
  | 6 => 0xe5318940006be6490a320afed62c8730005ff7348610005fc7250d311a6fc6488730066fe760ca501dff7314c520216fd6188730005fd718c910007f9708ca10005ff724c440006f5618c4200077d75c8650007bd6495232005dc7348640007ef724c4202b77e6554b31005fd7095132006bc6450d32005ed720c420007dd73109310077d5255031256fe6355321005bd70d0e420b6fe604c440005ff735872013fee2148740006fd614c74015eff30d8543006bf5498b41006ff62d8540006fc7654d21005ff7054931007ed2010d52005ff7550d31077bd408c8400067e7518941006fd650873021fef324c840005fd718c94109fdc6390d211a6fd760ca21004fd7690a311977d6508730006fe5258740006bd6448430006fc5498b31005dd76cca3208dfc73c8510006fd658ca4007efe6310a100d6fe604cb41005fd71d0c20005fd7095221005fc7458931004fe7219130106fd6310e420af7e5354f210067f6548510007f5510cb10005bf7454f43085ff7110c2115efe640c841007bf43d0521004fe72191100057d750cb41115fe7090e2113dfe718cb40006fc7258e42006fe640cb10005fd7390951277ec508cb21077fa408ca10005bf7448720006fe705874309fed3248730007ec428ca20006be6494c21005f9708ca1022efe76ccb400057d7510931005fe7494e210077d5354b41006bf6390942007ee32c8740006fd614864004f6f5294a32085ff7610c21005fd7590a32005fd709503110fdf30086300d7be404c940217ee214873025dff7695032006ff7648440006fc4358650004ff7358910246fd760ca50006ff4358420006ff43d8931005fd7308550004fc72592500067d6550832095fe7095121005bf7454832006fd63c851012ff5618c420005fc7694931007ed324874009efe7694d21006fd5158f200aeff30d85320bfed20cc420004fc7650910007bd52d0540005be748c9411defe760c920004fe7610d42087f67110e21007dd758ca3109fec638c921006fd61cc420006ff7648430005fc7254e31005fd7110a50216fd76087300bdfe70d0731006fd53d8540007f510d0e51006dd6310821005ff7155131006fd64cca10005fe721065035eff321915321efd76cc840006be73d9152005bd70d0d41005fd7118940004fd7694e21087fa6010c21006fe7398840007be42ccb40006fc7258f10007de748c831005fe7418d21004ff768ca5125ff73195131005de73087200077d5454b3113efe7608740006fe4258720005ec7259131006ff5098b31006fc73d8540006fd768ca50006be6490c21004fc7258440195fe73908210b5fc704c931006fc5458432086ff6510e21007bf4390b21007ed5290b200057f755813109dfc7690d21227bf43cc940066fe600ca51007f731c85100bfbe40cc540005fd7095331
  | 7 => 0x8520005ee7290d21005fd7598632006fc644c520004fd7399221006ff6350550007be5350b41356fc43d8953107de5390b30006fe7258743006bd6488430006fc7258c40007bd434c740005fd72cc640004ff7650c4209efc6448730005bd711094023ff7318c5500eefe60cc840237df32cc64022fbe74cc7402b7ee3254832006ff3258740006fe64c8430004fd76d0820006fd6590a32006fe648c810007bd54cc540005fd7290730004fd71d9152005fd7390b410d5ff764ca10004fd73d9152007be5250f401477e31d9510005fd7310921004bc7458b10007bd4390921007f5510c9100077d7510b31006fd5318931225fe73c8540006fc648c9311fffb508c7201467c31d9510006bc6450f21005fd718ca500d6fe2058f20005ff755813100778658c110006fd6350b20004ff7158342006fd63c8420006fe768cb40005ff7559131007be544cb401ddfc7350520007bd63d0a42006df634c510006fd61d06500373f5454941005be7418632006fe72d8d41236fd63cca40005ff7150b30095ff7648440227bf430c940004fe768c941006ff658c740005bd7408530245fc73c8650065fd760c840116fe7688440007bd744c5402677d750c951005bd74d8232006ff654c931006fd7598b4313fde7308740006fd3258640005bd74982320057d7510b32006fe5398b10125fe70950310067f654c910006ec7498831006bd6410810004ff7358a10006fe4258632006ff65c8540006fc4358652006fe6498632006ec745883115fde630cb41006fd5398841005bc7250740005fe720c440006bd7119121004fc7654d41006fd4358b100d6fc764c8401477e514c650006dd634c6100563c6510940005fd758c9410bdfd76cc4400077d7510921006fd654c440004fd7318941005fd73d0521007de708c932006fd6590f200ef7e50cc950006ee6294831004ff7358a54005be76d0d41006fd6510810007bd43505210d5fe7095132005ff7348550007fb214c110004fd7318910005fe728c650006ff65d0d31007bf64109510a5fd76c84400067d650c821005ff7155332006df7458c2107efe6310831004ff7650b31006de7458c210b6fc2058f100c7de53507300a77c50c8550004bd74d8f20006fc6218131007f973c822022f7e750cb40005fd708c93101dfe7208550006fe7098b31006fd65d0e21006fe6408430006fd65c8740004fc72591100fdff7350832005ff7059232135fc714c840006fa535804109efe7610d21006fd70584322beff61d9531004ff7358420006fd658cb410077d5210e50005ff754c521006fe648ca30006bc649053025dff7395032004fd7199131006fd61cc640005fd7194d21005fd7190c420067f65cc510005ff714cb40217de7308730004fd76104200aefd6390f2122fbd74cc740004fe72d8540006f
  | 8 => 0x6dd768c831004fc7258f10004fc7258e41004fd7610931004ff7359130005f97010a30006fc644c5302477d5310e50005fd7194b41006de639082107fbc4318943005ff7050d21007ed5250f20007f8724c210006fd5398a41005be74cc9510a5fe70d9721006fd4358720006ff764c4200bff661cc440006fe76d0d21004fc7650930006fd6550d21005fd71d0a30006fc61582322c7df540ca311e77d750ca20076fe608ca2109dfe73d9121076fe768c8400067d6590b30006ff6258131006fe3258231004ff764c720004fe7694d42007bd4390932007de320c740005fd7518f210d6ff654c840006bd6410820006fe64c8650007cf638c92125efe639532115f7d750cb410077d5390951005bc74486100077e75189310077d7510a21005fe7498131006fd6310a10025fd7595131006dd5418d21005ff7059131006ff43189511c7fb50cc42012dfe7010a31007bc64109310eeff63cc84011fdd73084300b5fe7090931005df7348630006bc6450531006ff6390950005bf7448510137f97008440006fd650ca40006fc62d8530004be76d0941006fd6519131005ff7590931004fc7258e40004fc7648530005fc724c510007bd544c940096ff6548440006fe6210650004fd7610a30005fd7190b30006ff6508540005fd70d8931067fa400ca10007de324cb4014efe53d853002f7f525533107dfe7390842004fd7198830006fd65c8730007fb704c6100077d751083107efe6310a21007f9319011007eff30189430067f65d8d10007bc74485400077d5354541004dd768c83127fdc508c831007bd53d0540006fd4358442006fc628c5400afde53c8730007df3298131216fd619073007dfc73548420077e51cca50006fd65cc840004ff7158f420077d5354931007ec6248510005fe76d0d21005fd758cb21006fd61c84400b5fe701913113ffa700c7401467e21d9510005ff75507310067d6550730005fe72d05310b5fe70d9131006ff764c940007df735053115efe63d0620004fd76d0e20004fe76885300077d52d0650005ff7550521227dc63cc940006ff61c85400beff65cc440007bd5448540226fc32583431deff3258232005bd7498f2034efc4318953107bd4390b3113efe760c740004ff7648730006fd658c7200077d7510932005ff73c86100077d53d0a50005fd7590832097ed6248430006ee624ca300067c6518910006bf4318940005ed720c640067fa700ca10005ff724c530006fd768c951006fd65c85100a5fc7055321007df3054f420aefd6394f21005bd7494f41006fe648c840006fd6508740007ec624c9400273f5495131004ff7654e410067c6518940106fc3098b43005ff73c8550067bd400c84014efe43d8530005dd7308630006ef628c940007df328c840006fd7610a21005fd7510a32006fd54d
  | 9 => 0xc6354521004fd7399320006ff6150550007ef2054842006fe4358a51007bc7250f41007bf43487400aefd6310f21005fd70d9721006fc63d8121006fc644c52124efd6390e52006ff64d8931006bc6490931004fd76884400457e7510832007be5310940005fd75d923213efe31d8141006fe6158232117f66188440004fc7259010004ff7654c21005fd7510832006f84298251004fe76cc520005fe76d0d52006fd63948410077e5110e5009dfc7350521005ff7055331006ff64cc720006be6450e3209fdc6310d21007bf4310b21005fd7198e42007bc7448430095fe7010d210077e65cc720006ee628c821005bc7454931004fc7650931006fe6448510006fe640c810006fd6394a420077d5250d51007be54cc540005dc7348540127f6610c440007dd324c640257df3255331006bd71993321d6fc32191310067f65d8940004fd7610830007ee3248440006df634c940004fd71d93200a6ff63c8610007bf64d0d21006fd5258f40004fd76cc8400077e5054d42006fd658ca41006ff6558131075fc7054a32004fc7258f41006fa52580410edfe7090b32006dd634c420006fd614c650006fd75d8f21005fc724c650006fe64086500477c540ca50006fd7558642095fc7050521007bf7454f41006ff6548530005fd738c540095ff76486301467e41d951009dff740c921007fb3290110006fd51189400d6fc604c941007dd5350b302477d75cc650005f77154d310077d538c6500c6fc3258743007ed748c9210b5ff764c610006ff65d91310a7f610c8510006ef620c910006ff43d8943006bf64d8d21004fd7118950197de5308730007be5448540007dd64cc931005fc7254f41005de73086501a6fd6390e211affb500c420006fd5198b30006fe7690932006fa5258021007dc328c550006fc7058f420067d65c873010dfc7055021007bc7448640006ff6448720006bc6490d10005fd7098632005fd768c720006fb7358021136fd6108440005fd758c821005ff7458131007be325074022eff31d8143004fd73989100b5fd764c440116ff6588440065ff760c840007fa325021007fef3210a32266fd630c951006fd65d8232005fe76cc940004fd7399132007bf4390821006fd7198a53005fe7294f410b7dd634c42007eff3219232006fd7558720007bc424c740004ff71591312b6fd6390d52006fd7118940006fe5258f20006be6450c41007dd544c93122fbd43ccb40006fb764c210005fd7110c20006fe75189310e7f8508c91009efe6348740005ee720c740097f6614844017ffb50cca10006fe745843224efe6394a4122efc3299230006fa5258031005bd7408550006ff63c8550006f8325825109efe63484400d6ff60181320bdfc7050731096fe604843009ff7314c521006bc6418121096fc6348420126ff650c440
  | 10 => 0x8540005fe740c921005fd730872013ffa7008740076ff63181320bfef20cc6200afee534cb21005fd7398442006fd65d0f21006dd6394c212dfbc5490a310a7bf40c8640005fd70109210d7de634c84008fee320c910006bf63909400aefc53d8f210bfbf40cc440006de5418d21004fe76d0521227df32cc540025ff7555131005ff7454d31004ec7259131006fd63108200777e508c9500067c6518d4013efc3199110006ff6588530004ff7358a41005ed720c540005ec7250c21005fd70d0931006be648ca51005bc7454a32006fd6550e32007bf434cb4022fdc320c740005ff7055221006be64cc620006ff655052009dff75cc52111dff7308430007bd414c540006fc644c550006fc3258021135fc7308440006df638c951005ff70550310077d6548720006fe42d8550007ed708cb210067d6590f20006fc64cc51008efc3258231007bf4310821216fe5158730004fd76d0e21004fd764c720005fb7350110006fe644c910007be5488540006ec705883111efd7688430005fd7348440006ff3258650076fe2098b30006dd6390c21004fc7258653005fc76c85300277c5095131225fe730c940006fd7198b301cfde63cc720006fe7058632105fd7390b32097de3048530005f97488110006fc4358a51105fd7390b30006fc62d85432477e75cc650007bf41c854021eff32191300277f5254d31127de630c440115fe70952210077e650c720006ff7654e42006fd65d8632007be540c540006df70d8d21004fd7688420005fe7210d21006fd650ca41006ff7648530004fd76ccb41005bd73d0941007dd320cb40005fd7194931097bf40484401a6fe63887400afee434cb21004ff7650730006ff654c930006df630c540004ff7159332006ff7558e21004fc7258e10087bd6410c21004ef7258d10116fc6388420007f65190910007bf7448440005bf735084221dfe730844022fbf43cc740006fd5458f10005f970d0a10005ff7050e211cefd63ccb20327bf544cb41006fc64485102b7bf4390d520ffbe4358b43005ff7055132007f9218c11021fdf320c840004fd719925222efc31d814322efe640c840004fe76d0f210a6fc30d8520006ff6318121006ff644cb20006fc4398a51006fe64cc5100077d53d0650006fd6358442006bf6350540007bd5310a4107f7e5354c42096fe3058b100067d6508730007bc42ccb40004ff764c840007be544c940006fd6548430006dc6418d21217fa7008730005fe744c52122fbe74ccb4021ff7314c440006fc7458e21005fd710c840006fd6348440007ec724c521006ef628c93018efd630cb101a6fe6388440115fd7688420005ff7050d32007dd324c540005fc7454e32006ed5458831007be428cb4019dfe7310420005fd7190a320077d524c650005fd750c841004fc764c540266f
  | 11 => 0x6fc64cc9500077e54cc650006fd6148430005f7714c91007fbd4310b31007ed3248640076fe608ca31255ff735533235efc3219153136fe2119110007be744c74007fdf3094c42007f72148630006fd65c86300077d5354721005f97018632366ff32d9153007be420cb40005be740c65010fbf4008640006fe3258740006be64948210077d758ca500067f6508540006ee5458831006fe62cc440004ff7358810096fc6348610006fb5058720006fe5358742004fc7258640006df6354d41005fd7010932004fe7694d210077d650c720006fc64cc720005fd75d9131115fe7010e2115fbd430cb41005ff7054a32127bf400c4401cefc32d8132117bf4088440006fd7598a43006fc7058e2125fdf3295331006f5614c420005fd7190832006fc7558432127dd630c440006be64908310bdfe7095331005bc7454e42006fc6248530007bc428c540006fd6510a32007bd4310921005ff7550e320afee62c87300077d654cb20005ff7350520005ee720c4200077c654c910005fd7310a10006fd61c8630007ef4290b31005fe72106300067d658c720006fc63d8910195ff7510c21006ff650cb41006fe32d8132005fd73d9721006df6394d21005fd7010b31005ff7348720006fd42d8530006be7319152065fc7054832007be424c540097df3048430006bd7319121005fd71cc840006fe6248440137be740844010dfd7608440097bd64484300c7bc63d0d4120ff731d913121ff5310c44015efc32d8543005fd76cc72012dfc7050e31006fd43d89511477c51c8650006fc6448720005fe7295031005fd7019132006ff7058c21005fc725051001f5f5394f21247ee320ca50005ff7550b31136fc31191100d7dd634c840005fd75cc521006fd65884300057d7510a32004fd76cc620005fd7398b41004fd7399121007bf7448530066fe600ca21266ff6390d51004ff735834209ffb3048530005fe760c910006fc4258632076fe608c821006fd5318941006fc62cc510005bd73d0a42007df4390d21007bf43887400b7f5614c420007de544c9310077e5448650226ff630c9400d7bf404c8400077d65cc7200077c65cc510006fd72d8d10005ff7250d3013efe219911015efc63d0521005fd72cc540007df3218131007bc3250740005fd73d0610007bf744c440005fd7110a30005ee72d0721007f93150110007f83250210005fc7254d31005fe720c5500cff8500c910006ff61c85500073d6550842006fe628c630006fc644c9100067f65c8540006ff6419121006df6390d21006fe75d8f211d77e750c841005ff7155232005ff7054e31005bc7454d41005ef724c420006fa325825122fbf430c740005fe72cc440005ff714ca40006f96150040004ff7654f42004fd7319321006fd51d85300077c654851013fbe7488740005fe764
  | 12 => 0xc64cc4202477d53cca5004f3f5495232006fc644cb20005ff75d0521007bd54c8740177fb508ca1019efc3118930005fd710ca10005fd710c950106fc6390910007ee3248550007bd4310a211f7fb504c720004fd7198a4023dfe7308550005fd7019131117df3088430005fe7650d21004fd764c620006fd635864224efd6310e52007bd438cb40007ee3218121005f970d0e3004f7e758c951005bc7458131117bd6488430006ff4398a1014ff7314c610007dd708c831004fd760cb10006fe6288440005ee720c640007be42cc940006df74d8d21006ec62cc910004fd7319152005ff7354a42006fc648c920006de6310821006fc648872007fbd431083115dfe7398b41006fd4358a31007ed3248540006bd6410a51005fd719513123ff7314c55021fed320c840005fd700c9210eefc60cc9510677e500c9500077f654c510006fe62cc6100c6fe6350720005fd7319121007ef20d0e52006fd6510e20006bf7650c4207dfe7398442005f57190b210befc64cc610006ff6318910005fb7054941006bd7319152006fc640c720005fe76d0931005ff7055121006df630c951006fe74d8d21005fe728c6300077e54886500b6fc3058f10007de328c6500077d5310951007dd708c932006fc624c930005ff7558931096fc6448610096fc6448420006ff5458432004bc7458910006fd54d8532004df7650c43004ff7158f401cff7318c720006fe648c420095fd7648630007ee3248610006fc624c540005fb704c61013fbf418c740005f77150f21007de74d8d21007bd43109320a5fc704c721007de320c6400077e540c650004ff7359250006fc764c940006ff65905300077e518ca50006fd70d8d41006bc6418d21007bd51109401a6fd6310e210067e7518931004fc7650520006bf6454d21006ff654c941006fd7098832006ff645893109dfe7310d21006df638c910006fe624c840006df631092109fed7210d210befe20d8530005fd7010a2108fdc63cc510006dc63d05210adff7510f21095fe70cc521006ff6499131066fe600c8210c6fc6350510005fc7255131006fd31d8121216fe7688730106fd7694e42006fd658cb10006fe5458c210077d658872020ff431d9131006ff654c740006dd638ca10005fe740ca2122f7d750cb400057d7518f21006fe6248430006fc7258c2119eff3118930007fb3250110004fc7258c10004f77159132005fe7210e21006bc6450d31007ee5250520006ef628c931004fd7610e200aefe7610f210077e544ca50005fc7250c41005ff7354941005f970cc6100277f524c650006ff6298131096fe3058720004fd7318954004fd768ca5115dfe7394b410c6fc3058743005bd74cc950006bc5458442006fd658c840007bf32505400077d534c650005fd7010831004fd760c7202b6fd6310d52
  | 13 => 0xc840005dd7390b31005bf7650c42006fc648c930005bd7408720006fe7098b410b5fe70989311defc3258232087ef2110e21005fd7590d2108efe53d8d10005bd73d07400077d5254c410d5ff764c820006fe71189300d5fe708c932005fd7195332005f97010420006f76198632217dc31d8131006fd6548530007dd5350530006fc5058f21006fd6348650116fc6488420004fd7398820005fd700ca21005fe7494831076fe10d8d20004fd73d8954006ff65505100aefe63c8720007bc428cb400d7f8504ca10005bc7250540005fd7090b31006fd6390821004fc7258f400adfd73c8730006dd63cc720116ff6188440007bd5408740005ff73485100a6ff65c8630007bc6450d52005fd75d81310077f65cc91009fdc734873009dfc740c921005fd72d0d43007de73109310beff65cc42012dfd768c44007eff3119132007dd32d8131266fe760c95124fde7394b31006fe624c510007f9708c910006fd73584400b5fe7010931006fc3258740005fe72cc610007df324c650126fc640c420006ff654cb41005fe7610d52004fd7690821006fe4358442237be74cca40006fc7458e51006fc7058c41005fc764c54009dfc7355121137be740c440007de5348530006fd43d8550005f77150c21006fc63d8941086ff6510c21007dd7018d21006ed628c841004fc7650d21006bc7159030006fe7690931005fe72cc550006fe6288430006fd7458432126ff610c440006fc62cc940085fd7610e51087ed2110c21006fd7558730075fe7090a32005fd75d8f21005fd70909210aefd7694f2123ff5310c550006dd6310c21006fd650863001f7c5054f21005fd7190f420057d750c8410aefc63c8510106fe6390b20004ff764c4200d6fc644c820006ec7098831236fd630ca40005fb7054a42004ff7159230005ff714c9400a5fc7050f21006bd64d0e32004bf74589100d6fc2058f200c7be53d0d41006fd5258730007fa329011013efe768c740005fd70cc721005f9700842001efd5398821006fe6218131006fe7118943007ee520c7200aefe63c8420007f72188630096ff64486300057d7510832005fd75d05211a6fd6394e210067d6598442006ff65ccb40006fd7558443227bd74cc540005f9700c420006fe620c440137df318c440006fd7610b32005bc7454832005ee7294f21007f65150d1008eff6390d1011efd6188430004ff7358042006fd64d8931007f521086300d6fc644ca10005ec7258131006bf6410921005fe76181310077d5354a3212dfe710c4401defc4358a301cefc4398a30116ff6188430006fd654c720095fe708c921186fe63d0a10006ff6518931007ee52cc720006fe4358b10006be640ca510b5ff764c420006fd65d0c2102e7c65cc540007df634c940006fc6288530005fe72d8d10006fd6310a200bef
  | 14 => 0x6ff6218131005ff7050531006fd644cb20006bf7359220005bd73d084213fbd74087400a6ff65c855002f7c54cc6500fefc6350950006fc7654d42006fd63d0a10006fe7458630266fe6354741006ff65c8510005ee72d0e52005ff7154e42004fd71d8d42005fc724c630005ff73c8510006ff764c6500bdfd76cc4200077d528ca5008ffa700c910006fb6098131007de53885300473f5495032006ff635095110efe10189100b7de634c420007f67110931006bd6410c10007bf4390a3122dfc7348740167fb500ca102d7bc5410a310aefc30d8532006fd644c8200bf7f50cc65012dfe7094a31006fd65d0620006bd73992510bffa40cc440196fe6308720095fd7648440004fd73d8910005fd7090a21006bd6410a20007be54c8740007fb704c510005fd7118930006fe5358720007dd53909300bdfc7050b31007be7319121006fc640c920005fd7094d210067d6590831095fe70d0d210a7ee62c8610006fc4258630007f51010a51005ff7348650005fd73c8740007b8425021009dfe7310921006fd7598b30006fc648c921006ed5498831006fe64c8610006fe54d8532006fa32580410edfe7010b32006fc76487400eefe76cca40006fd6510c10005fd7390550106ff3198b43005ff7054832006ff7058e21126ff650c420196fe6308650006fd65c8610004fe7690930006fd64cc720006fc4358a5004e7c6559632006fe52d8530006fe5398841005ff7350521007dc328c650006dd638c820005fd7395321006ff6590910005bc7454d4309efd7690d21006ff6350521006ff31d812125f7e65950320267c654c510004ff715834301f7f53c8650006dd630ca10006ff6418d21097fa4048440006ff6390921227be74cc540006fc7058f41005fd7090932005fe7219131005bd7310b40266ff6310d51237dc320c640005fd72d04300077865881100077e510ca50006ff43d8552217bd7408730006dd7058c21006fd65c8420006fe62d0630006fd64cc420006bc7259021196fe6308420006ff6550d20005fd7190d51007dc7348740005fd71cc950004fd7398a50007dd548c831006fd6448420006df630c910006fd725843023dfc7350550006fe4358720007bd748c840005fe7210e10005ff71550320afec434cb21006fd65d8131005ff7154d41006bd43586420afee32c8430007bc541932118eff32d813109fed32484300067d6550b200aefe63c8650006fd6448720007ed5290f2009dfe7390d21006df63d8121006fd6590d210afbf4390f21006fa3258021006df6310d21004ff764c820185fd73d0830006df6354521006fd654cb41007bd4358442005fd7394b41096ff6348420007ee548cb21107be53d0e42004ff7358642005fd73086500067d7518941006ff7558c21006fd63c8740005fe7290d51006fd650
  | 15 => 0xd7094e21006fe7258630005fe72d0d21007fa3250110197f43118931006fd6590a31007bf70d9121007f710d0d51004fe7610d21004fe72d9153007bf4354541004fd7694c41005ff73c8650006dc7458c21005f5719082122efe760cb40006fd51d8d10006ff764ca40007bc7319121006fe628c64021efc32191301a5fc740ca21005ff75d0d2109fbe4350d21005fd709083109efe7690d21006bd6410832006ff32d8141005ee7290d52007bc420cb40006fd658c7402afbc5490931007be72d0d41005be74cc82003e3c65d05400f7fb50cc910006fd72d8d41007bd74d8930007ed758c92114efd6310e1015dfc7358b41004fd7690e21137dd7308440006fd43d8910006fc7258c2012dff768c440006fd768cb41004fd7690b31006fe64c8530265fe7390951004fd7118954004fd7399251007dd7394b31004fe72d8d41006bf64d0d52006fe7018931006be64507300beff64cc6100d5fe7019132007ee5250d20196fd7694c21066fe1018930247f7318c650004ff71582320057d75189431d77d750c841005fe7294c41006fc7358442005fe7210e5109efe4358632006fd6354842006fd654c620006fd76d0d21005fd728c630115fe708ca21007bd434c5401e7ef3298232066ff630c840005fe7494b31007be540874011fee21484300077d5290d51006fc648c95013efc21992100aefe5398a31087f96010e51005bf7454b31277ef518cb21006fc7358720006fe644c6200057d7518941065fe70908320a5fe70cc721006bc6450521277ee758cb21006ee62c8730005ee720c540006fd6508420107f73190a31004fd76cc420006fd7198a10086fe6110c21006bd6410a10005fe72d0e21006ff6318940004fd7199130006bf631094011fde730843024eff6310e52005f8705484215efe63d0610006fd7118931005ff7154f21007bc424c540004fc764c941006ec624c931006fd6510a30227bd43cc940006bf64d0d31005ff7459531096ff6448610006ff73d8540004fd73d9121004fd768cb41186fe63d0a4223fed320c95004f7f5254e320877e5110d51005fd75ccb41006df63d05210267e654c72014fed320ca10006bf4358442007f832901100d7fa404c840197f73118931006fd6510831004ff7158e50005fd7310420006ec620c94114ffb324c2100077d5210650297dc544c931006f8735802118efd760cb10006fd6354b410a7fa30c86101a5fc7355221006fd650cb10004fd7198a30007de320c54002d7e7510b31004fc7258341005fd75d0f2122fbd430cb40005fe72d0d32004fd7318940005fe7655131006fe3258650005ec724c521006be73d9121006bd6454c21005fd75d9321007dd53c8530005fe7290f4114eff32d8530004fe76d0d32006be6448430007af648c921004fe72d8530006ff63d0951
  | 16 => 0xc44019dfc734842007efd7694c420d5fc7054d32006fe624cb40006fe6358442006df634c5210a5fe7090f210afbf4310f21005fd7388740005fe729533104f7f528ca50004ff7654c41004fd76d0a302b7f73154931007f510d0d51004ff71590300bdfe70d0b31004fd761082007efe7610b3115dfe7390b41005fc7254c41007ed4210b31005fd7095321005fe749823222dfe734874015dfc7354b41005ff75d07310077d520ca50007b94150110006fe511893004f7c5095232007bd4310a51007be63d0a42006fe7198b43005fe7494f21006fe43d8951005fd70d0d32006f943d81520edfd76cca10006fe4258730097bd40484400077d538ca50005f97010e10005fd75d0731005fc7255231086fe6110e4212dfc7055231005fc7454e3123eff6390d50005ff735484213fed720c740006fd7690931007be76d0d410bfef20cc420006ff65591310077e5455131005fd72d0e30007f77154f210a7f661c8630004fd7694f42007f551cc510096ff6548430006fd65d0931005fd70d0d21066fe760ca10076fc608c951005f970cca100067f6518d10005f9708c630007de548c831096fc7648630267ef328c951006fd5458f200077c65cc540007bd7390841006dc70d8d211377d750c440005bd70d0941005fd7110951007bf4390951005bd74ccb20006fe62cc740277ef508cb21006ff6350910006f83258041006fc640c9210067f65d89100067d654c720007bc64d0d21005fd7094a31006fd7598843006ee5498831186ff31992321877e5354f42006fd7690b3207efe6310820006f84298021007bd76d0e42297df504c931006fe5358442004fd71d8d20097ef2048420004fd7199330006bc6454d21006be6488430006dd630c820006f95458021004ff7158e20006be6490b30005bc7448650007bf4348540007bd7310a41007de53905300067d65d0c21007bc42cc940005fc7650d5215fbe740cb41004ff768ca101a5fd7388730226ff3158343006f95458031007f55148510105fd7390832227be74cc9401e5fe73d0620006ec6208540216fe31d8131006bc64d8d21004ff7358b10125fc7055031006dd6394821005fd7590e21006fe624c630006fc3258650004ff7358840006fe7198843004fd71189530077c6548540006ff658c54021dfe73c8440257dc3255031005fe748c9210d6ff644ca10006fd75d8d10006ba4258041006fe6248740317bc54cc941125fe7094831095fc7054d21005fd75d0c21004fd76d0e51004fd7690e51006bc6490921006fd659083113fbd748c740006fd6150730006fc64cc721115fe70d0e21006fe72586530b5fc7050d31005ff7054d3109efe53586321cefd630cb20006bf6410951006fe648ca31006f83258021006fe6418931005be74084201a5fe7310a21005ff7158232005f
  | 17 => 0x127bd400c4400067f6590910005df7348730005fd7590831006fe32d8131007f83250110007ed32c874006ff73118131226ff6318d40006ff6590931075fc7059232207f850cc72010dfe7090c21007f93250040006fd6550e31005fe720c650007dc7348640007ec62549310077d5210d510ff7e5354d42006fc43d8941135ff7308440005fe72d0e10006bf6494d21217ef2188730005fc764c91011dfe7110830277ec548cb21006fd6510a10004fe7690f21004fc7258331005fe7299131005fd75d0b31196fe53189310077f658c91002f7f5454b31005fd709502122eff3199230005fd710cb20005fe748ca21217ed21087300a5fe70d0721005fe7494c21006fd6310821006fd65108200877e6510c210067c65d85400a5ff76c8440006ff7650d21006fd65cc640007dc74d8d21127ef200c420005fd7194d41004fc768c941255ff7355032005fc7459632005fe72d04300077e5455332006fc640c950005dd7308730005fd71952320bffa40cc61015fef328cb41065ff760ca1027fde758c831006fe7558632004fd7398b410d7bd404c840005ef7259131004ec7258d10004fd7608430117ef2088420297dc654c93124efe6394b41005fd70d0e21007bc64d0f21005fd75d8232007ba42501102b6fc6354941005fd7099131006ec628c930006fe62887400067d65ccb20006fd6198232005ef7250e32004bc7458d10007f850d83211cdfe7308720227bf430c540007bd7494b41005fd7198232007fb31500400077d5310650006bf43d8540006fe74584300477c5095032006fe6448630006bd4398b41006be648c821006bd64d0e50007dd634c720006ff644c510006fd768cb401d6fd630c841005ff73505501cff7314c720007f92150040006fe53d8540007f74150521007bf414c740006fe644c420005ec7250521006fd65486400aefc64c8730007f443c852124efe6394831005fd758ca31006ff658cb400bfbd40cc440005fd7590b310afed32c8730006ff6550d10005fe7298743006ff63d8941116fe7688430004fd73d8940005ff7458931005fd7090d21005fd7190e52006fe620c740006bc6450d20005bd70d0a42006f85018910006ff6550531005fb704ca30097fa4048610006fe648c650007f5514c910006fd63d08200077c654c94012efe20d8d10004fd7690730186fc3199232005fe768c910227bf43cc540007ee3248720006fd5158720006fd7458653006fd61c8730007bf434c9400067f655051007efe6310a500077f754c6500d7ef204c820006bd64d0420065fd760ca10006bc649095002e7f52d8553006fd63d0610086fe6110c20007ef2010d52007bc64d0531006fe648c841006fd6510d21226fc3158343227dc320c540007df6350d21006fd6550b30006bc6450550007bc7448440136fd618
  | 18 => 0xf76487300fefe4358b4323dfe73c85500477f520ca5010dfe7095021006fd63908422e7dc504cb31006be7299021005fd70d9121007f741cc721006fd6218131005ff7154c42006fd654c940004fd71191500077d53d0951005f571d0e31006bc6450d21004fe7219131005fd73d065015f7e5354f41006fd6510a31075fe70d8632006fe6488630006fe43d8550007bc6490d52005fd7518232005bd7418530006be7399021006ff65d0d3210dff7608440007f44348421006fd51d854027fdf508c831006fd768c91009fbd4310d210067e6558442004ff735844013dfc7388740006fe5398a41007fb6388110006ff64cc521006ff764cb400b5fd738c440005fd7194e42005fd73c8640005bf7350b41006fc628c550006be640c821006fe6448440004ff7654c42005df7348740007f443c8621006fe52d8d10005fd7194f21005fd70d05311eff8500c72006ff431181312477d530ca50006fd65886400feff325923204d7e75d8232005be7418131005fd7090e21006fd72584400d6fc3058f20004fd76d0c20187ef3299232006ec620c910005f97008430005fd754c521005dd7308740215fe7190b30004fe760c540006ff7458c21004ff7158c4209efc4358632005fd7318940005bd74cc910006fd65cc540006dd6354f42006f561cc440116fe30d8910007dd324c440086ff6310e21006df64d8d21005fd74d8132066fc600c951006ff64cc910005fd74d812122efc3199230007dd3054c4210ffa70084300b6ff654c610006fd650c640006fe64cc820007f65190d100befc20d8530005dc7348440266fc63547210067d6510831075fe7010a32007bf4310a31005fc744c521004ff7158d10004fd71d8d54004f77650441005ff754c721006ff60cc951005fe7218d1013fed2108740006fd43d8930006bd64c8430004be74d8f200067f65c8510007bf43d0721007dd7418d21006fd7058642235fc7348640216fd6108730006bc5418941004fd7690841006fe644ca3014dfe7310a10007ef2054b41007be744c540007be53d05401cdfc7350720187df3094f42007f532d0541005fd7018d21266ff63cc951005fe7210d52005fd7310941005f970d0610006ff6310921005fd71d0d21006bc6450d300d7fa404ca10196fc640873013efd760c7400adfd76c8730007bc7448530006fd654ca401cff5310c720006fd6548540006bf735925125fdc3295031005fe7298f41117bd4088440115fc7054e2115efc3299231006fe3258221007bf744cb400adff76c873012ff8508c420116ff6588430005ff7150d20006f56148440006bf73590210aefc4398a3109efe6348430006bf545844213efd7608740004ff7159250005fd748c93109efe4358a3119efd6310c20005fc7695131006fd658cb200a5fe7095321004fe76d0931
  | 19 => 0xc720006f56188440006ff6348540004ff7158e40006bd6410e51006fc764cb40007bd41487400277c545513130fbc548c941006fd650cb20007f74150731007f5414c521006fd5458f211cfed320cb20007bc70d9121005ee72d0e32005ff76952320a7ed62c84302a7bc54109311e6fd6310e20007f92150210007ee428c921195fd7608730005fd7550d2108eff63cc910006fa329804113fdf310c74012fbf408c640004fe7299031004fe7610f21004bd74d8930006fe648ca20097be6448430007be72d0e420067f658c54013efe640c440004fb7648020007dd638cb412b77d5354832006fc7648530096ff6018121006fd7398b41006fe7610932007ec62c851014efd63cca102677d5310d5122fbe740cb40006fe624c640086fe2119131007df7348630005fd718cb41005fd7510831005fc768c910005ff7158f2009ff93048430004fe76cc9100a7f561c8630005ee7290f210b5fe7094931005fd710c941005fd710c9100e7fb508c9102bdfe7310a51007f860d0d520a6ff65c844015efc63d07210ffde5350b30006ff6590d20087f62110c21006fd5218930226fd76cc94008ff7314c510007be748cb41005ff7550721005fe7619131006ff3258341007df3054f41005f9708ca3025f7d6595032006fe644c8400eeff65cca10007dd32cc740005fd7398720005fd7195032086fc3119131004fe7610d410c7f7315053127fdc548c83115fbd43ccb41007bf4390931005fd711093109fee7210d21005ff758cb410077f650c910006fd7610b31006ff4398a5020dfe7310a41007de638cb41005fd751893131fbf540cb41004fc7650530007df65cc931006fe6254741007bd4354842006bd6408430004ff7159032007ee32505211ceff3298a30007bf438854020efd630ca41006fe52584421d5fd7310430216fe6388430007bf4394941006fe768cb41006fd63d0420005fd7310b211467c21d9510005fd7388420006fe62cc650137dd310c440004fe7690910005ed720c440005fa7018632006fd61c864004e7c658c910005ff7350950005fe72d0e51004fd760c440007f53148510006fd74d8d10007ee3248510005de76cc931006fc6218530006ff6598931006fc644c931005fd7494b31006be76d0d41006ff43d894122efe64cc440005fd7510b31006fd7518941004fc7258c400c5fc7354941006ff658c941005fd749893107ff73110a31005fd7310a50006fe64181311d6ff3119131006ff7258730006ff650cb4001d7e7519321076fe608ca41004fd7398a54006bf64d0f21005f97010430006f5610c440006ff644c530005fd73d0721007df3054c41005fd72cc440004fd76d042013fbd740c7400edfe730c840006bd639084121fdf32cc440007bf32d07401d5fe7394841005fd7390720006dd638c440006f
  | 20 => 0x6ff6419132007be54c8540006ff65d893108efd63cc910007ee5290d20107f53190831006fd70d8d420077d5354741225fc7348540006fd63d0620006ff4358642005fd710ca50006ff7558c41006fc7258440006fd7018941005fd7519321005fd73c85401cdfc7358720006ff6550530005dc73486100c7bf43cc9412b6ff6390d52006fd659923214ff8324c210006ff4398810006f843982512677d5390d51006fc4398a41006fe72584430877d6510c21004fe764c5200b7f8704c610025fd738c550006fc7458c200aff7314c721007bd3250740006fe62cca40006fd7258730006ff644c951005fd7190b31006fe32d8141007bd51d0540005dc7348550006fd654c740006ff6590930004fd760cb41006ff6550d31006fd6550e210aefe63c8740007f93250210007dc7348540006be645073114efc32d8530005fd73d9321007bf6450531135fe718c84003f3f5454b41006fc63189100067f6550d10006fd6448610005be72d0f40235fe73486400aefe7694f210bdfc7054b31006fe53189410267c6559531005fd7118d40005dd7394b31005fd7388640005fd740c92110eff6508440006fe6458632006fd658c630245fe7308650005ff73509510dff8504c910006ff6310951005dd7308420004fd71d9153005fd7510d21007dd7390931005fd7110d21005ff7050f21087f71010e51107bf4390b3222dfe7388740004ff7650b30006fc7458420006ff6350520247f7314c650007bd71d0e42006fd531891018efc32d813109fed7290d21004ff768cb41006fd64cc620006fd65d9131005ff7059632006bd64108210077e7510a310067d6550b30106fe6390821005fc7250d20004fd76d08300a5fc70507210c7dc7350731006be6450e310aefe63c8440005fe72cc5100077d5350951006fd43d8931005bd73d05401ceff31d8132007b94350110006fe4258432006bf6454521006bf6410d21004fc72592510075d7518d21006fc62545310a6fe60c8430007bd41cc740004fd71993200b7de634c610006ff6350950196fc431893108dfc7350510007fb315021008ff8638c110007de64cc931007be5310a41005ff7150d21006bd6310841006fd7118953107f73190931006fc3258221006fe7398a10005f97010820004fc725804113fef2188740007bc7150c42006bd7690841005ff7054e3215fdf3094f41006fe620c650007ee32486500b5fc7059131006be739925113efe6488440005fd718c951236ff32d9130007df644c931006fc6318941007fb628c110256fc6355121007bd43d0521005bf73507400a5fe70d9321006fd614c720006ff7458e5104e7e658cb20006ff7258e10005fd758cb41006fe5258720107ec32d9132006ff4358a10005be74d8232005ff7454931006fc43d8951006b84258041007ed524
  | 21 => 0xf7650e21005bd7494b410467e650cb200adfc7350721005fe7210e50005ff7055021006fe6258b43007be5408540004fe7608530006df638c921006bd6410e202ffbc540c941007fb218c110005fd71cca50006fc64c85100c7ed320c941005fd7019321007bc70191211a5fd7688730005dd7308640005ff7350720005fd70d932120efd7694e4108ffb324c11008efc4358630006bd6410830004fe7299131006fe5458f2119dfe73d04200b5fc7055131005fc7648530005fe7290c41005fd758c931005ff714c840005fd71d0e10005bc74486300b5fe70d8931005fe764c94035efc3119153006ff6510931005fe74d8131005fd7510e2121f7e750c840007ac648c921005f9700c820006fd644c650006fd654c510005ff7155121006ff614c540004fd7198b40004de7618d21006fd7598b41006fd4358841005fd70949310edfd76cc840005fd75d89310b6fc604c521005fe744c721007dd630cb41137ee2148440006fe5258632007ed32c8640006fd65c8430005fd701912113fbd4188740006fe52d8540006fe7258440005bd7310940005ff7055321006bc7259030007bf43c8740006ff65d0d21006fd63c8440005fe72cc6500cffb500c910006fe62106300a5fe7010f21007bf6490931006fd6390a51004ff76c8730004fd73d9151006bc725901022efe5358f40007fb60d0d52005fc7454d32007bd5350c42006bf64d05212177e750873013f7e7508740006fd644ca10005fd7398642007be424cb40006fc62d05310bdfe730c420006fe76d0f21006fc32d8141006ff65c85300977e5048550007be51d0d40007df70d8d21006be6490b31006fd7318940006fe64c8510006fd531893004efe549883211ff81018d10006fd6550731007f51010e51006fe5198b4008dfe7318910006ff65cc521117be6488430005be7408430006fd658c8410067d658cb20005fc7454d21007ee32c8440196fe63084402d7bf5410a31006ff6354941007be4248740247f5310c650007f72148730004fd7610832004df764c832006dd638c8210077e5210d52007cc424c832007f57110a3113fee720c740005bf7454c42006ff7458432006ee768c9211e7ec3298232006fc4258420006ff64191310c6ff6550731005f77150e31006fd54d8530006fe7398b41006fc7458e20007dd324c550006dc63181210467c650c910006ff764c4400b77c504c550006fc6418d21004fe72d8d50007ed3248440005dd73d0531006bf64d812120eff32d91311a6fd7610e2109efc4358a310eefe30d8930006ff654c540006bd64d0e30006ff6390920066fe600ca41006fd64cc61022fef328cb4012eff631813135eff3119153006ff4258630075fc7050e32005df73484200bdff76cc420006fe43d891013fbd410c7400057d75d8232007be42cc740
  | 22 => 0xc510006ff43189430affb30c853013efe76887400067e6558f20006ff644c72122dfc73c874009eff6394d2112efc20d8d10105fe7398642006ff3258440007f52108740005fe7695131006fd658c420006ff7654f2113ff9700c740247ed320ca50087de3119131004fd7610c2007eff31189430077e54c8650007bf43586420aeff3098a31004fb76500401477e5148650006fd65ccb40136fc2119110006dd74d8d21005fd75cc721186fe63d0820006fd6448730006fe648ca21005ff7155132005fc7250d210befe60cc4400057d7518931006fe7118953115fd7688440004fe76cc94123efd760c9500077d758c951005ff724c630006fd64cca50006ff32d8540005fd708c921006fd61cc740006ff4358810004fe7690921007dd7310b31004fd71d8d40085fd7110e21006fd65cc9100af7f5394f21004fd7610430196fd6390c21006bc7359251215ff7608730004ff7359120006fd6548440006ff43d854211fbd740843019dfe7388420005fd7418d211a6fd630ca21006fc5058632005fe728c740005fd7190930007be420c74001f7f5154f21007f72188730006fd6508430006fe7558432005ff7054b3109eff6390d21006ff6590d10005ff7050c21004ff7654f41005fd7010b21007bd7319121006ff6318941006ff4358a41006f84318152006ff644c5502b6fe6354842007bf4308740006fd65d0a30006fe640ca20006bd648c810005fc769093123dfc7350950004fe7690530006fd5458e21215ff7388730005ff7250730006fd6148740004fd731895010dfd760843023fdf32cc550006fd6590b3113fbd74887400077c65c8510005bc7454b31196fd6394c2125efc6395121006fd7358442196fe630874008efd760c9100bf7e50cc550096fe604844013efc2199110004fd7399110106fe7690b310057d7510b31006ec6254931137de7308440004ff768c840006f832980412afbf5490931005df7348640005fd74d8d21006fd658c810085fd7610c21005ff7550d21006bd43189400d77e504c9500a6fc3098b1008fed320c91010dfe7010c21106ff6590b31136fd7688440005dd7310931005fe72d9531004fd76cc820005fe7694931007be32d0740007f52108730005ed720c550006fe648c720005ff7155331007be4288740267ee320c9510a7de30c85300b6fc764c440005fc7454e21007df6390d210d5ff764c840005fd75989310b7dd634c61009fdc73484300a7bf40c8440006fe644c650005fd7318321006fd63486400adfd73c8430004ff7648630004fd7694e42007bd548c74009efc63487200edfd76cc820006ff6508530005fd7194c42004ef7259131004fc7654941007f72148740006ff65cc940006fd614c440005f97018543006ff764c840006fe6358642095fe700c92119efd63cc820004f
  | 23 => 0x6fc64cc520004fd7119153266ff630c951004fd768c840006fd658844013fbe748c740006fd5298b4002f3f5495331005ff7350b20007f921901101df7d750c920007de53505300afed7210f2113dff7388740006fc7654f21005bd740cb41005ff7550e212bff731d9531005ee720c440225fe73485402677d53cc951006fe64d8931007ed2010e52007bf6450d2123eff63cc9500057d750c921004be74d8930005ff7150d50007ef624c940006bd64d0610005fd73885401defc3158232006fc7258f201d5fe7390841007df74d8d21007dc634c940005f571d0d31075fe70d9632005bd73d0b412b6ff6310d52007bd4348740006fc7258730006fd650c440006df630c921007ec424c8200077e51d0e50096fc6448630007de320c440007ec428c921005f87054b41006fd65d063011dfe71d0830006ff7458e21007bf414c54015efe760cb410077e514ca50006bf63d054007efc311894309fdf7018d2113efd6188740115fe700ca21006ff7058e42005fd7198c420057d75108310aefe539882113fde314c740006fd70189310b6ff644c420006fe640ca21004ec72591101e7ee320ca20006ff64cc950005fd70d9132006fd75d8d410b6fc1058730007be52d0540006ff6550d301e6fe43d8930217f6210873019fef328c820005fd7110820006fd6590821007dd748c83110fbf4008440007bf4310931005fd7390920006fd654c840004ff7650842007f72188740006f84398021005fd7010821007ed544cb21006fd61c8430076ff658ca10005be7410d41006ff72d85400a6fc63c8610006fe64cca5013efd610c740005fd7118943006fd31189310057d75109320befc30d8530004fd7608730006fe3258341006ff7458f1015fee320cb41004fe7618d100073e7510a41085fd7110e41006df63cc5100067d650cb20186fe63d0a50006fd6458232006dd6354e4213f7e750c7400057d7510a21005fc7250d32007de324c840004fd7119152006dd630c821006fd650c8410069f6418d210a7df30c84301a6fc6388720006bf644c521007be548c74013efe31992101deff3158232005fd718cb40006ff7558730006bd64d06201477e51cc650005fd7598131006bd7119152006dd63cc6101cdfe7398720005fd750ca41007dd32cc640006fd7558632006fc62545410d6fe604c840006bd6410b32006fd3258740006ff4358620006fc4318941007be7310a41006fe7198a430a7bd64c8430005fc748c921006fe7058442006fe7610921007bc73d91211277e500c550004fd76d0430006fa43d8152127fa700c440006fd755874315efd760cb41136fd76084401a7f731d8931006ef7598831006fd61d0630007bb41502100b6fc764c420006fd65cc440004fd760c810346fe43d85530b7f8504c420075fe720c8400b7f6104
  | 24 => 0xe63550310fefe6350b20007ed528cb20006fe3258720006fd75d8d20004ff7650f10007bc744c640006fd7610a31115ff7688430006fc64189310eeff64cc820006fd70d8f21005bf7448730006f9601823210eff610843015efe63d0420006fd6510c200d5fe7090932005f7714cb410057d7510a41006fa3298251006fd6148650006bd640c810005ff744c931005fd75d07210277c5054931007bc42cc74010eff610844021eff31191302177d7508730007ec62cc941006fd7118910007ee32c8550007f93290110196fd6310c21005fc7459531007dd3054f42006ff614c550065fe728c840006dd63cc840007f931d0240006fd6348720237ef328ca40004de76cc931007bd4388740006fd735872021fbe74cc840005fc7250d30007bf32d0540006bc6494d2122fbd43cc740006ff658c7200d5fe70d9132006ff6599131004ff71592520077d6554931007bc42487402bff431d9531006fe5458e21004ff7359210007de5390930107be4398b43267bf4390d51006bf54189410057d7518d211a5fd7388430006fc6218540005fd7290530005ff7358b41005ff714c950005fd7210630004fc72592310067d6558f20005bd71d0f40004fc7650521004fd7198910006fd650c8100fefc635091013dfe710cb40006ff764c62010efe7608430007de708ca31007ed32c8540005fe741893114f7e750ca100a6fc64c8610004fe7299130006fd6598632005dd730854023f7e750c950006fc64485300eeff63cca10005bd740c550005ff7590b31006fc4258432007bf744c940006f960181310067f654c5400067d6558442005fd7519131005ff75d0721006ff7558720005fc7650d21006bf4318941006fc501893111efd6108430095fe7090921005fd7110e1007fbf4310b32007fb3190110006ff600c951006fc62d054116ffb504ca10005ff7150930005fd7110a32006ff7458f20007bf4390a32004ff7159220006bd6410b31006fd768c840006bf4398842006fd651893101e7c65c8540006fc7258e100077d53d0d52007bd434cb40006ff6218930007bd52d0d40007ec4288420004fe7299310006df7058c210aeff6394f21196ff301893113ff62108740007bd53d0941004ff7158e42007bc32d0740006bc6490d21006fd7198843006fd65d0a101177e5088550005fd708c932005fd70d8f21005bd7418d10096fc205872007efe6310821006ff644c520004fc725864310fdf3008430006dd54d8d212b77d5354b31086fe6110e50007ee32c8610005fd700cb21007df7350731005fd708ca21005fe72d0731006ff7458653006fd6550f21006ff5318931004ff735822110fbd6408430005ff7350510004ff7650c4107ff731109310eff610cc910235fe7388640005fd73d0a10006fd7258653006fd5158f40006f87258041
  | 25 => 0xc92109f7d750c921006fd63c8650005fd7090821005fc724c740006fd54d8d100b5fe7098131006fd5398b40004fe76cc52127fdf548c831005fe7610d21004dd73d9320346fc43d8553007bf7448630007dd32cc540005fd7095231005fd718c820004fc7258630006fc64981310077d52cc650006be6450e21006fc631894015efe63d0650006fd6258743004fc768c940006de5458c210b5fc7059531006fe7258432004fc7259253006fd65c85300067f65cc940006ff32d8550007bc4288740006fd6419131005fd71d0d52007bc420c740006fc6488530005ff7150950007be5190b4011fed2108430006ff6354521256fe635522106efd760c810004fe72d85430aefc4398821006ff619823221fdc320c440005bd76d0a4207eff6510b31006fc7258430007be739084110dfe708c821006fd3258650004fd7694c21004fd73d8951006fd7198840005fd7518131005f97088630004ff764c440076fe608c810005fb704c6300afed32c8430085fd7110e5104dfe720c950006ff4358650006fe768c92008eff630c910007ed20d0d52005fd728c740006ff654c52010ffa7008440006fc64cc52109eff65487300067f6518910006ff7458730006fc644c930076ff6098232225fe730c54021efc3119130005fd70d9632005fe72d0e50006bc6490d50005fd75d0e310a77f50c8650005fe76c853014efd630ca10004fd73992520eefe76cc840006be6494831006dd63cc420006fd654c6300efbf40cca4013f7d7508740005f87054931006ff63d8540006fe6448730115fe7090a21006ff63d81210b6fc624c610005fd7590f21005dc734872009eff6310d21007dd544cb31006bd64d0e21006fc5258632006de7058c21006fd6310a51006fe624c420006ff7558f420a5fe708cb210057d7519321006fd61cc650004fd7688730297df544c9310c6ff3259131006f84298031007ee544cb21007bc424cb40006dc64d8d21125fe7090831007ed758cb2114dfe73d0a10007de53c8530007fa73c8220005fc7250e21005fd7288540006fd644c630006ec62549410077e75109310057d750ca21007df6310d21066ff650ca10007bf6410931005fd7688720007dd320c8401a6fe43d8931004fe768c920006fd5398b43006fd6510830077de638ca10007ed2094b41006fe7458420005de7308740005ff7350721005df7348540005ff7154f420a5ff76c86300b7bf404c6400c5fe731094122fbd430c7400bdfe7090b31006de6394821087ef2110c2113fbe5150740005ff7354b41006fc7458c21006bd6494c21107ed3290832005fd7090b210bfdd63cc420106ff32d9232106fc6390951005fd7390921006fd6510e10095fe70d8d21007ec6210931006de70d8d21006bd644c620005fe7290730006ff5058f21007dc638c951256f
  | 26 => 0x6bc6450930077dd638ca1011fdc3118131007be424854007efd6390c4221f7d750c840005de7308420005bc7458931005bd7190b40006fd6310810005fd75d8632006fd6448430004fd7198a43005fd758c841004fd760ca51005fd718ca40267dc630c951006ff6558931006fc3258720007de544cb310277e6554931007f86388110006dd638cb41006fc425843008dfc760c910107be7494e42005bf7350540006fc64cc5500afec538cb21005ff7050931007ee524c520006fe5258f400277f5259531004df735912122fee320cb40005ed720c720006ff6354721007ed520cb20005fd7198f20106fc6390920005bf7150f4008efd630c910004fd7690c410057d7510921007f55150510006fe32584400277c5054d310077d520c650366ff31d9153005ee720c550006fd761083104f7c5059632007f55190b10005fc7259531005f7714c9310077d5254e41007f92150110005fc7610931245fe73c8650006bd71d91210057d750ca410adfe7310b21006fe7318941106fe6358e42006fe32d854002f7c5095331006ff63d0521006fd658c9102b7bd4310d52006be64c8430225fe7388540006dd5458c210067b7558041005ff70589310aeff6310f21005fd700c821004ff7358650006dd6354c41005ff7154d42004fc7654d21257ef32552320077e5408650005ff7550d32005fd71d08300c7bf430c941005fd71909500edfc7055332006fd7198a3024efe6394a42005ff7355121075fc70552320c5fe7318941004fd7319320006fe6518931007dd3218131226ff3259230006ff43586520077d525523125efe6395031006de54d8d210bdff76cc440006fd42d85502bf7e750ca51195fc735502101d7e7510b21006fc624c550006fd65d0420005fd7590c21095fd7288430005ff7454d21005dd7310a32007de320c550005dd730843001f7c54c8650005ee72cc521005df7348430125ff760c440005bd7418131005fd7094f21005fd71108320a5fe70d0f21006fd6550c21005fd7194b31005ec724c721007bd544c740005fd71d8d40005fd73d912109dfe7318121007bd4148540107bf4390832005fd738c940006fd65d0610006fd7518930007dd535093011fef2188430004fe7690d21007f5711093108eff32586300777c508c95009eff3058a310c7be7494d41007fb32d0240006fc6448550005fc7250d50006ff72d8553006fc72d85532a7bf5410931007be73d9121004fe768c540006fd658cb40006ff658c940007bc6455131005fc7250531245fe7310a500067f6590d10005ff7350910006ee628c81015fbd740cb411477c514c65009ffb30486300c6fc6350520004ff71592530077d52d0e50006ff6550910005f77150d31007bd53d0d40006fd6590e21006fd53d8520004fd73d8950007de5308530076fc608
  | 27 => 0xd73988400d6fc604c951005fc7654931006fd6519232006fc7258443066fc600c92102f7f52cc650006fd654c610007bf43c8540004fd76d09310077f654c5400277f534c6500077f65545312477d53cc65009fdc7418d210077d53d0e50006fd52d8d40007f551c8510006dd630cb41077f6108c910007bd5250740006ed628ca41095fe70d91210eeff63cca5007fed3210832095fe7094d21007bc6495131004be7619121006fd654c420096fc3058b10006f561c8720006ff764c740006ff64d8132006ff705843234efc3118953006bd4358341007bd4354b41006ff63d0721006fd6558232236fd76cca40006ff650c940007dd3054f410a5fc7054f21006fd6310a41006fe6248730006fd515873019efd630c820006bd648ca51006df6394d41007f8704c510115fe71084300077d7510a31005fd749813123dfe728c95007efc6310941006fb5018910005fd70d0f21006fc3258341006fd6510b31006bd6410c21005fd7550531006fd6394821005fc7250e51006fd650cb40007bd63d0e4225efe6395221005dc7348510005ff7510a3108ff8324c110006fd745863210efe30189101dfef3258232066fe600c810007f93250110007dc70d8d21085fe7390c210677c500c9501cdfc7350b20007f931d0140007de748ca3113efe5158740005fe7690931006dc63505211e6fd760ca20004bf7458b10005fe72d0610006be6408430005ff7454d32005ff75d0f21006fc64885500067f65d8d40007bd6350c422cfdc508ca31007f5519091007efd6394c42007d5718ca31005fc7454931007ec420ca21227ef328c94024fbf4390e52005ff7558232004fc76c8540005ee7210d210277f5354931006fd6510821007dd758c8310d5fd764c84009efe634864022efd76ccb40005fb7054931007dd5348730006ef7498831007be42cc5401a77d750ca21005fd7094c2107ff53110831007bd41cc5400adfc73553210adff75cc721006fd5458720005f57110b21007bd54ccb40006fc5458f21005df7350531006f83298251006fc640c550004ff768ca41006ee72d8f21006bc6454521007ec724c721006fd608ca51006ec6248510005fd70d0b3112dfe709523110dfe70d0c21006fd7018943005fc7254f43006fd7458730004fd7694c42006fc6318540115fe7094e21006fe6488730006ff7558443005ff7254f43007bf7319121005fd75192320067d6590821005be72d0d40005ff7154f4104efd759883215efd6394f41006fd615823204f7c508ca51195fe7310821007bd3250540004ff7358442317bf54cc941006ff6510f21067de630ca10006fe644c7201d7df3094c41005fc7250730006fc644c9501467e31d9510006fe648ca50004ff715911034eff31189531a6ff6588730006fe4358841077f7108ca10007fb3150110
  | 28 => 0x8730006fe64c863018eff31d8131004fc7258443006ec624c930007dd3094c420477c500ca51005ec7250e32006fd65cc720006ff6458232005fd7110d52067dd630ca10067f7100ca10195fd7308730007dd324c650004ff7650e51004fe76d0941006df638c5400077f65cc510005fd7318941005fc7255031006fd6510e2109efd6390d211bffb508c420007bf4308540006fe640ca50006fd7518943005fd7318910005fd720c740005fd7190b20005fd7110830007be5150f40006ff654cb40077be749823207efc6310951004ff7358740006ee6248610006ff650c740005fd7090f21005f97388110007e6718cb2110dfc7054c21007dd5388730006f56108720006fd65cc9411a6fe6388640005fd70cc5210077d5388650005fe7418132004ff764c620007dc64cc931005fd7390950095fd7648430006ee6248430007bf4310932006bd4358442005fe748c93209fee538c921005fd75d0d31006fc3258440005fe7210931005fe7218131006fc32d8540207fb50cc720005ff704c52109f7e6548730006fd6550531007dc63d0d21005fd7195331006ff6310941006fd5458632005fd7318121006ff7650731005fc74582320d6fe1058f200b6ff654c55025fef3295232007be32d0540075fc7059632005fd70d0c21006ff65d072109efc3258632005fd7590b21005dc7348650005ff7150f20007fb32d0140066fe3018930004fc72592102477d530c650004ff7359252065fc705503225dfd7695032004bf7458a31005fe7210c100b6ff654c640007bd5290b40006ff7258c40005fd7194f42006bf7650f41007de7018d21004fd7610e21006fd650c910006ff654c510006fd4258730006de7618d210a7bd40c8440005fd7095032007be544c74025dff7555032106fe6390a51004fe72191510077d534ca50006ff764c550005ff7559232006fc62cc5400277f5495131006fd43d8552004fd760c821006fd7318941005de7308640006fe3258241007dd65cc931065fe7010832005fd7195121005dd7310832046fd731895307dfc7358442007be7019121006fe644c610007df3298232006dc6390921097dd3048430006fc435842023fdc320c550006be648c810004fd7690831086ff6310e510a6ff65c84300077f654851012efc30d8d10007bf4310a32005fc725533109efc7648730006fe64ccb20007fb50d832112efe768c44012eff658c440007bf74c8740004fd7319121004ff7358041006bf648c9211a6fc43d8931006ff65d0931007de328c740005ff7158b43006ff608c951007be424c940004ff73587200077d5348650006ff65cc740006fc624854009fee438c921006fd6358720006fe7258430006ff74d8553006fc641813122efd63ccb40006ff6548740005ff7150d52006bd64d0830006ed628c810006f
  | 29 => 0x1a77e6588730005fd7599131006fe5498a31005fd718c940066ff630ca10005ff754c941006ff658c5300d5fe7010932005ed720c650006bc7259031346ff32d8553006fe6408630005fd7310951007f55150f10005ff7510931006fd6508640006fe735844007efe6310a51005fd74cc521226ff3259130087f96010c21004ff7359221007dc328c740007f72148430006fd6390b10006ec621093113fef2108740005fd7194d4204f7c518ca501477e21d9510066fc1018930137bd7408440004fd760ca41005be740c420004ff7358841005fd7090c2114f7d750ca10005ff76487200effa30cca10006fe7318910006ff64d8d21007f9214c210005fc7655131006bd648ca20006fc6418121006ff7648640067f6100c910006bf6410931007df7348740216fc31d8131006fd75d8d40006fe62cc510005fd75908210067d6550c21006fd650c720005ff70552310077e658c7202e7df504cb310aefe63c8430005fd71d0f21007bd5350740006bd640ca5125dfd739533212fde638c440006ff658874021dfc7348440247df32cc650006fd6354741005fd754c721005bf7458131006fd75586431cfbd7498f200eeff65cca402b6fe62596321defe53d8d2007fde7310b312677d530c951117dd3088430005fd7308740006dc7058c21006ff6550931006ed62908312befd6390e51006fe32d855022fbd740cb401e6fd630ca200b6fe20587300adfe73183210067f6550910007de7390931006ec62885300bdfe7010b31096fc305872033e7b5318152006ff65cc910006fd32d8131006fe7058443006fd6590f21006ff614853023eff630c950005ff764c72010fbd40084401deff6390d20007bc649095108dfc7350910006fc6288540004ff7358640005f5711082109dff734873009dfe73951212c7dc500ca31004fd7199253007f8628c11029fdc50cc931006fc624c940006fd61d042010eff6508430007f6518c9100edff76cc840006fd600ca51077bf408ca40006fc764c5201477c31d9510005fe721043015dff750cb41007cd320c8200067f658c940004fe7299110005fd73c8440005fd728c640005fd71d0e420a7fa40c8610007be54ccb400a7f8501832124ff73194a31004fd760c8411effb500c7202befd760ca51006fd6590931005fd70d8d21005f5718cb21006dd75d8d21006dd70d8d21006ff654c720005bd740c720006fe64cca10006fd65cca10007df7348730006fd7398a10337bc54ccb4111f7e7508430217ef2108730007bf6490d21006fd6310a50005ec7250721004df7359110095fe7010921004fd7399021006fd65c8640005bc7250f400077f654c910005fd719513223dfe7390550006dd6394f42007dc7348440006fd7358642006fa42582510077f65cc940007df634c510006fc620c540006fe628
  | 30 => 0xe74cca10005ff7654a32005bd71d0d40006bf64d0d32006fc7650531007f72188430007ef620c9100d5fe70d0d32007ee3254521005b974881100077d5454931005fd73d06200067d6510821006fe64cc620005fd7190910007ee32c8510005ff7059531004fe76d0d52004ff7358a40005fe72d0e30005fe74d8121004ff7358b41006fc6498931007ee32d812126ff751cc721004fe769093211dff7388430007bc424854012fdd638c440005fd750c941005ff7350842007ed5290832005ff7054d21076fc608c9311dfec3258232006ff4398a51006fd7358420004ff7654b31005bd74cc9510b7be404c540006ff4358a51007f71010951007dd4310d21007bd434c9400bfde63cc420006fc50d8f21004fe7299330006fe54586320adff73c8730005ff7150d102e7dc544cb31007bc32d0540006fd768ca1012fbf408c4400077e5054e41004fc7259031006fe7358442006fd7518940136fe3119110005fd7095131004fd76d0c21044ff7654a32004fd768ca1009efe6348510005fd7190d200073d7510a41004fe7694f21006fd6510630007f521084300067e6558c42216fe6308430004fd768c7201ceff63ccb20006ff63d8940005f87054a32006fe5258730006fd6350842007dc7348530005ff7050731005fe7295231004fd7610821006fe53189100bff561cc440006f7618c530006fc7654d4102e7c65cc510005fe74cc521006fe64c844009efc63485400afbd4310f21187f731d0931005fd7194f41007be6495232006fe7198b300057d751923229fde65cc931007bc6450d21006f571d8f21005be72d0740004fe760c910006fc4318951004fd76d0620115fe7010a2118f7e750cb10006fd7558432006fd43d8520225fe731894020efd6394e41004ff7650931007f55150d10006fd644c51025efc6395321006bd6494821005ff7050e31005fd7510b21006be640c81007fbd7494c42007bd5390b40006fd658ca30004ff7654e42007dd539073022eff32991300aefc3098a31004fd7690720227bd43cc540005fc7259131005f5718c821004fc7648540005ff7348740007bf438c740007df324c740125fe70108310077d75d8132004fc725823113efd7688740006ff654c721004fd7690931006bf640c921005ff7050521007ee708c921006fc3258241006ff65d0531007bd4348540005fd71d0e50106fe63908420069c6418d21007bc748cb40006bc644c521006fd5258740005fe7290d20005bf7650842216fe21d81311a5fe7395221005be76d0941097f56148440004fe72d855007fbf4310832007bf73d9121006fd5358642007ee421093101d7e750cb21006dd5498c210b6fc764c640005fd764c720006fe74d8d52007be548c540006bd64d043013efe319911023f7d750c950005bf7454f41005fc744c721
  | 31 => 0x8f41006bd6410a50006fe65586320477c510ca50006fc628c530006fd7118930196fd7610c21266fc6354541005f9708c820005fd73c8550004fe7690931005fd750cb21006fe6248630005fd728c540006ff7558c42025ff755953111ff621084300067c65d8d10007bc420c5401ceff3198a30006fc7058443006fe648ca511a6fc6388540107bd6490b31007ee32c8650007bc7454d41216ff61887300fff73150931004fd7610a10006fe628c440005fd7388440267f73154531307bc544c941004fe768c9400efbe40cc9400067f654c510005ff7150f210b5fe7095131006fd53d8542006bd640ca200057d75d8132005fd7110e42004fe72d8d10095fc7050d21004fd7119130006ff7654f42006fd65d0e20006fd7558442005fe74d893109f7d7518d21006fc764c74004f7c5054e321d6fe6310420006fc648c720006ff5158632005ff7054d320eefe6298f20005ff7159632006ff7558f10005bd7390b40007de328c64021dfe734844019efe5318930007bc424c940007bd43d0721006ff5458f21007fb2150210007ed5210a32006fd614c640007bc744cb4008efc3258630006fd6590c21004fd768cb10006ff70d854308ff6710c910006fd65cc6200077e548c650007ec62d0931006fc64cc95113efe21d8141007bd41c874009dfe7319121076fe1098b30005fd7095332006fd65908320aff930c84301d6fd760c841006be7619121006fc32d8550004fd76d0c10004bc7458d210a7be64c8430006fd6590720005bd7408730006ff6550521005f9748c1100a5fe7019321004ff73590100067f650c940006ff7558e420c6ff6318d411077e5354e42005ee72d0d320257e7518931006fd65d0830005fd760c7200adfe73d8321007bd548cb40136fd760c440007bf4394a42005bf7454842005ff7358442005fd710c95107fbe5350c42006fd64cc910007bf6410d21004fd7199232005fd7019232006fd7058643117f5618844002e7e65cc720005ee720c720007f51010951005fd7010a3113efc31d814113efe6408440125fd760c440005fd7310a20007bd5250f4008f7e750c910005de7308540006fc6218543006bd6410a3207efe6310810127f5610c44009fec438c921067bf400ca40096fc6448430007bc42cc540005ff73c8740006fe72586432bf7d750ca51005fd7510821004fd7610c100dffb504c91013dfe71ccb40005fc7454a32075ff768ca10186fc43d894309efc3058632007f6510c910006fd745872007efe6358c42006ff7058e410077d658c72022ff7318c740006ff64d81310afee7210f21007ee4210b3209eff3058632006fd614c420086fc2119131006fa3298021006fd32d8141006fd6518632004fd768c8410b5fe70d05310b7ed204c420005ff7050a32006bd43d8540006ff6558232005b
  | 32 => 0x6fd5118910007be548cb40005fc7250d10006fd65104200077e5455132006fe43d8552006f8329802113dfc714cb40006fe70988430067d654cb2032fbc548cb41007ef6210931007bd4390931107be6490b31136fd768c44009fdc7018d21095fe7018d21006fe6288630007bc63d0941006ed6218931006fd658ca10006fc7258e51137ed2108440007bf4148740006df63cc521006fe644842028fbc549083109efc63485500067f65cc910004fe7618d21006fe5198b3012efc648c4200edfe7095332006fd6354a4204f7f538ca50006ff7558e41006be6450720006ff7558f20005fc7454f21106fe6390841005fd7110e50004fd76886300067d7518943007bc7448630006fd658c820004fd76cc72008efe760c91015fbf43ccb41005fe7210d51006fe5418931006bd64d0731006bf6499131005fd7218540006be6490a51006fd7198b43005fd7190d21137ed720c4400077e545533109efd7610d21196fc30189310067d6548720006ff325864023dfc7348550006fd5258f20006fc62d85401cefc3198a30005bc7454a42007bd544c540006bd73d91210057d7510941087be6410c21006fd74d8d20126fe760c44006dfe731081022fef324cb40004fd731915012eff618c440006fb7358041005fd710cb41006fc64d8931006fc63181211e7f7314c620005ff7348420005fd7110f21116fc64884300077d7510931006f561c8630006ff6550930006fd6394b410077e5455121005ec7254e3213fbd4108740004fc765493109efd6310d21006dd63d0c21005bf7650b4109efe634861015ff731d0531005fd720c64010fbe6408430004fd73d8121005fe720c9100afed7294f21007bc7454e42005fe72d9131006fe7610931007df654c931005ff714ca500067d65cc720006ff6550d32006fd6510f2109fee7294d21007ee528c7200d5fc7050d32006fe624ca30007be42c874020dfe7394a41186ff65d0b31005fd73d0a5014dfc734861013ff6310c740006fd65d0b31005fd730842009dfc7610d21006ff63c8540004fd7610b311ddfe73909201d6fe6310650007ee768c921004fd7399321004fd7694e41005ef7254e32005f87054832006f94358251005fe7290d212477e750ca50006ef745883104e7e65d9632005fb7054a32007bc4288540006ff7358420006fd5318943006df638c941006ff4398a30006fd5358740004fd73d8941005ff7054e210adfe73d9721004fc7258e50005fc7250f10005fe72d0c100277c50d9531004fd7610a51006fe6254731007ee32d05210eefe60ccb41006ff72d8543006dc63109211e7f830d8930007dd708ca31005ee768c921005fd73d8321006fd51d8d20006fd65d893122fbd74ccb40004fe7299253005fe7290931006ff4358a30007bd4310a31006de5498c21006ff755
  | 33 => 0xd32c8440006bd64d0c10007bd5390841005fd7510f21006fd61c874006efd6310c10096ff6548610005ff7550f21005fe7290e2113fbf410c740006fe640c420007cc638c921004fc7259230005fd748c932006fd7058632004ff7358652006fd658ca3107dfd7310b320bdfe730c4400b5fc7050531007df328cb40217f97008730137bd740c44015efd63ccb41004fc7258e54087fa6010e51006dd6394c41007df638c910005fd7018632007bd431095115efd7694f41106fe5398b43006fc5458632005bc74549412b77d6554832007bf41cc740216fe76087300067e6558720005bd74ccb41006df63d0d21007bd32d0740006fd6550b31006ec628c940004fc764c520006fe5118940006ff644c910006fd63c864007dfc7350842005fe7494a3122efd630cb40006fd74d8d21006ff72d8530004ff764ca100feff3159232005ff7348640006fe644c8200277f5255131006fd5398b41267ed320c95112dfe708ca31005fc7648540135fc7388440066ff630ca500a5fe700cb21007bf64d0531005bd7190940007dd7318931005fe720c7400057d7510b21217de31d813112eff658c420006ff4358a500077d7510b322b5ff7354832006be6490b20007ee748c9211deff6318d20006fd6510931004fd73191510067e7598a10007dc328c640007ec724c620097ee6248430006fd65d04300feff6550b31005fd76ccb20245fe7310650095fd7288440006ff64cc510007dd548ca31005fd7298743006ef7058831006ff5118931006fd65d0c101b7fb504c420005df7348440215ff7688730186fc63d094109dfd7648730006f561086300067d6598720006dd6394e42004fd7690b30005bd74d8930005ff724c740005ff7155321006ed621083107fec3219132005fd7390b2019ff7318c420006fe62d073109efc3058a31006ff658c910007df7348640005fd75d0e320067d6588720006ff6519131005fd7319321076ff658c9500c7bd43cc941006fe648ca10137ef2188440007dd63cc720007dd74d8d21005fc7454c21005f5710ca41006fe7318940005ff75505312befd6310e510c6ff6394d410a77e50c8550005ff7050832006ff6448510006fe64cc420006ff4258430005bf7150d400067d650c7200bdfd76cc61009dfe73d05210067d6590842007bd5350f40006f561484300a6fe30d852015efc63d0541005fd750c821007df324c640007f86050d52005fd748c921005fd7308640006ff764863011f7d7508430004ff7358341006bf7259030006ff5058632115fc7050e21005dd7308440005fc7458131005fd7018f21005fd73185401cdfe7390720004fd7690f10085fd7110c21005fd7510c21006fe640ca510b6ff654c440005fe7410d21005ee7290e52004fd71d8132007bd540cb40005fc745483209fde4310d21
  | 34 => 0x8931006bc648c92124efc6394941007bf4390921004ff768cb10006be6450530006fd325834131fbc540cb41006bd64d0c20006ef629893113efd6108740006fe640ca10006fe644c51012dfe70d0e3109fee3248730006ff764c640007be540cb400067d6590832006ff63d09410067d65907200d6ff654ca100eefc60cc941005fd7010d21006fd7610931005fe7295131004fc7258343006fc62d8131005ff7550c21005fd728853015fed320cb4107efc4318943004fc7654d420aefc5358f21115fe710844007eff3218943006df63cc940006ed628ca5124ff531948310a6fc64c8630004fc7259131005fd75d832125dfd7395032006ff75d8543006fd650ca10005df7348530006bd7610a41006ee628ca510b6fc2058730107bd4390b32006ff764c5402477f530ca500057d7510821006fc72d8543006ff654c530006ff73584401a6fc6388550007f55190f10005fd7418132006bf6418d21004ff7158043006fe325804113ff97008740006fd6348610006fe6398642237f7318c640005fb7348210137df310c440006fc4398a10004fc7258043125fe718c440006fd650c820004be7499121006ff6448530225fc76cc5400077e654c720005ff705513110dfe700c821004ff7158e52007be544c540006fd6510c21007dd32cc440196fd630c821005ff7050d31006ff644c720006fd65c8440004fc7259130097df3048630005fd73885500c6fe7694d41004fd760c4201477e51c8650005fd70d07310563e7519152005fe72d0d52005fe7210e20005fe72d0e31007bf64d0d52086fe7610e21006f56188430006f9535802110f7e5008550004fe7610932007bf43505211a6ff30d89312b77d6554b31004ff7359021006fd65d0731005fb70548320beff65cc610005ee720c650005fd708cb210d5fd738c84009ff57110d21007de328c54008dfe728c910007ec62cc910006ff63485100a5fe7018f2115eff65d07312f7bc5490b310077d5354941007ef2010e52097fa3048430004fe7690d52005fc7250d52007bf6410d52006ff65cc941006ee628cb1013fbf4188740005fd70d923207fbe6350c42005bc7448420007f86010d520fefc3058b43075ff768c8400057d750c941006fe648842009dfe7390921007be53d0941006fe5258432007bd54cc940186fd7694f420b5fe701893124efe6394821006ff755843225fee3295032005dd7308530004bf7458d10006dd7458c21006fc7458430006fd6590b1024ff73194931006fd5118930006ee6290831006ff604c951007be4208740006df630c9410eeff65cc840006fe32580210af7c5354f21005fd70d0521004fc72586500077e5090a51007de320c65010efe760844009dfc74cc521125fd760c420245fe73d0a50186fd6394f42004ff768c821006fd6394842007e
  | 35 => 0x67d6550c4220efc6390550006fd7258643006fe64cc910007bf744874008dfe73d8910006be6490930005fd710cb40077ed208c820006ec62d09310077c654c510007be51109400efde63cc840006fe3258420006fa425802104f7f5159632006fc43d8552006fe5398b40005f57110a31075fd768c840004ff7650c210077d654c720007ed52cc720076fe768ca50006fd64d813122ff7314c740004ff7648430006fc7458653117df308863002f7c5455331006ff644c9311d7f73119131006fd5218940005bc7250d40004fd76cc440007df630c910004fd76d0b31346fc32d8553005fd7308540006ff6354541006bd6410831007bf7448730005ff70553320c6ff6310d4109f7d65487302efbc5410b3118f7d750cb10006fe62d06100b7ef204c6200a5fe7090b21007ef2094b41007dd540ca3109f7e5354d21236ff31d9130006fd6394a41004ff7158332004fc7258740004fe760c921004df7358910007fb2190110005fd73909101a7f57110e21007ee3248740006fc5418931006bc6450d52005fd7418931005dd7308550006fe62cc640006fe7118940006fe62d0430006ff64ccb20006fe43d85200ffef32592320b7bf404c440004ef7259110007f55190d10337bf54ccb41004fd73d8554004fd7198840006fe7198a53006fd5298b30006bd6410a30007be54cc940007dd3094f421a5fe7390a21006fd54d8d21067fa300ca10004fe7610d52007ed32c8550006ff6158232066ff650c9500077d5254f21006fc63d8540007bc744c440006be6450e51006fc644c510006fd6348510005fd7190842186ff30d8943005f97010a100feff6394d42006fd6508440006ff644c930007de634c720007df324c540004fe7688540005f77154b31006fd61d0430006be644c620005fd7110b310067f6518940007bf4398642005fe74d813220eff31d9131107bf4390b31085ff7110e21006bd4318941007de548ca31006fe6248640006bd648c82109eff630c921004fc7258430004fd76d0e10066fe2018930004fd7198843006fe6448430005fd708c82104d7e7518632005fd7095232005fd7198b43007bc6490d21006fd6350720007bf434c740007ec6294931005ff7150c4201d7e75d8321007ef648c9211cefe6358f20006f7614c53001f3f5495321006ff650c91020efd6310e41186fc63d0951006f95358041005fe72d0650005ff744c5210067d6590c21106fc3198b43007dd54cc931006fe7098b43006fc648c951006fd63d0a50007fb6050d5222eff32d8143005fd7090a31006fd5458c210b6fc764c6500b6ff6098131006ff6550d21006fe6298743006bd7399021237bd74cca400077d5354a4221dfe73884400067d65587200c6fe4358743005fd720c5400073e6550c42006fe7458632006fd6548730006ff501
  | 36 => 0xe73d0610005dd73d073110dfe70908210077c65cc91022fbf43ccb40107bf4390831005f9700ca10006fd6550f10006ff65cc540006fc624c530005be7494e42006cd628c831006ff4398a31006dd71d8d21004fc764c910005fd7310820005fd7310650106fe6390b10006fd65cc740006bf71593320efbf40cc840007f7214844020dfd7390730007dd3094f41006bc640c921004fe72d9131004fd7398b40006fc7258f410077e5050e51004fd731912012dfc7054e311cdfc7348720005fc764c941006fe62886400077d52d0d51006fc64d8d210efdd63cc840006fc7258653004fe76cc540006fe74586532cfde758ca31007bd43109310077d5254c2122efd760cb40006fc6458931005fd73d0420237ef324ca40265fe7310951006fc64cc910227be53d0d400077e5054a422e7df544cb3122ff5310c74007fbe6410b3123dfe730c550006fe6488430006bc6490951006fa4258041006fc64c85300067f658c910005be72d0540005fe72cc740085ff7610e21006ff6548540005fd7390b21007bd748cb410067f6518540006fe768c910246fd6310e5013dfc7308740217be74087300fefc6350951107be63d0e4212fef208c420006df6318121007bd70d9121005fe748ca31007bf438c54008f7d750c91021fef328c840007f743c8521004fd7198a540077e544c650006fd61c8650005fd7518321007de54cc931006bc7259251006fe3258640004fc7259030007de535093008ffb328c110006fd6348420257f73155231006fc3258041006fd63c872022fdf320cb4009dfd7348730005fd7190d50004ff7654931086fe6110e520adfe7319321005f97010e20007ef4290931004fd7610810005fd7218543005fd7194941006fe70d8d210057d750cb21005ff7454b31006fd6588730006fc5258432005fd73d8910004fd760863007fbd6410b31007f9214c1100057d750c8211d7f43119131005fe72d0d51005fd7010931004fd71d8d50004fe7690920004fe768c910004ff73593211377e7508440005bd748cb41007bf4390a21007bf63d0941005df7348610006fd65487400bdfe7094b31005fd70d0e31287bc5410831005ff75509311d5ff750c841007df734854021efd63cc840007dc328c540116fc30d8910004fd760c8400077e5054941075fe7098632005fe7290d50005df7348550006fa4258031076fe608cb41187bc43d8943006fd61cc72015eff32991310bfde63cc6101a77d6588730004ff7648440076fe768ca10247dc320c650087bd6410e51006fc5098b31006be4258041006fc624c510006fd6390b2009fed6248730007de70d8d21007bd4308740005be7494d41006fe768c950006fe624ca40006fe53d852022dfe7308740005fe74d9531007ef20d0d5222efc3299130006fd6510832137ee720c440
  | 37 => 0x884010dfe7094c21097f56148430005ff75d0531135ff7388440006fd61cc440006fd654c910005f5718ca31005ee72cc72109efe760c921004fc76c8530307bf544c941006fd65592322cfdf508ca31005fe7494931076ff658c840004fd764c440005be74cc941007f743c8621004fe7219150006ff64581310267c654c540007be748c840066fe600cb4123dfe7390950006fc32584200067d6558c42004fd7119232005bf7650f41006fd5458730006fd65907301fff8508c720225fc76cc940006fc64c855009eff644873000678755804107fbd4310b32067ed200c8200feff6310d42006fd658c64021dfc73c8440005fe72d0e200b6fc644c420006fd7690b31006bc545864209dff7348430006ff7258430137f9700c440006fe624c61001f7c5095321006bf4398b40007bc54d9321006fe648c6300b5ff764c44001efe5498821216fd7688730006fd5318940007f52108440004ff76c8430006fd64cc650006ff61cc540005f77154c21005bf7458931006fe6498232006fc64ccb20006fe628c740005fd7348740006ff650c540005ff724c640005fd7098931006fe6448650006fd64586320b6ff6018131006fd65cc510006fd6588740006fe54d8d21006fe620c6400bf7c50cc5500affb30c8630006fd72d8d40006fd7098b31006ff7258f41005fd7010e212477d750ca500bdfc7055331006ef7098831004fd7610e51006bf6410d52006bd76d0e42004fe7299331006ff63d05410b6fc644c610096fc76484300077e54cca500077d52c8650004fd7399310006ef6210931004fc7650d32006ed628ca30006fc640c951005fe728c440006fd52d853009fde5348730006fe624c440004fc7650d200067e6598c42006ff62d85430fefe635084211fef2108430227f7318c540004fe72d8d54005dd7310b31005fd71ccb40007df7348430006ff654c940004fd7399131005fe7290e51006ee628ca30004fd73d9320005fc7258131007bf4390932005fd72d0630075fe7019232006ff6148540006fd73189100aefd7610f21006bd6410430004fd7319110007ee524c720006fe64c8730007de540ca31005fd7094b31005fe7690d211a6fd7694e2113fbe7408740006bd6310b40007f74348421006fd654cb400077d65ccb20004ff7359220006fd6448650006fd63d0650005fd74181211557875502100aeff65c8730005fd7590a31006fd6548510006bd640c821006be6454c21095fc7055121195fd7308430004fe72d9151006fc5058432005fd7010b32006fd65d0d21006fc644c720006fa4358251007dc634c510075fe709523212fbd408c440006ee6294841005f77154f21007bf7250f410a5fe7094f21007dd32cc5500d6fc764ca40087dd6310c21006fc6408530006ff658c931005ff7348540007bc420874014df
  | 38 => 0x2cfdc548ca31007ec7250521137f62108440006ff65ccb41007dd53c87300c6fc6350521005ff7350b4108dfc73485100077d52086500077e5054e42007f521085300077d5354842005ff7050e320adff73c8430007bd43c8740006ff644c950006fe6488650006be6490821006ff72586531dfee320c920006bd64d0e51005fd7510a31004fc7258c41006ec62c8510006fe640c650006fc7258e41007bc42c87400bff850cc420004fc7650d10007dd7390b31006fc6408550006f561c8420007bf4310921004fc768c9100eefc30d8930004fd73d8540006fe54d8f210b7be7418131005fd7110a10076fc608c9411a7de538873006f7e750c810004bd76908410067d6510832007dd5390b30136fd6188440096ff634861009fee7290d210eefc64cc820006f9435802115fbd7494f410d5fc7055132006fd65d0e32004fc7258654006ff6394941007f71010d51006ff43d8951086fe3119131004fd73d9321005fe728c530007bf7019121136fd610c44023fef328c950006fe644ca50006ff6348550005fd718c8400a5fe7208430006dd634c7201e5fe7310a20006fd61484400c6fe5358743004fd7118943005fd7090931006fc32586400067f650c910007bd5350b41005ee7210f21085fd7110c10005ff725053021efd760c840005fb7048610005bf7454b41007bd51d0d40007bd6350842006be6490b32004fd7690c42096fc7648440007f51010d510b6ff654c4200eefc64cca10097f61048510004fe7690d20006fe62cc84015fbf430cb41007de739493118efe5358f10115fc7055221004fc7650d52004ff76c863018efd6390f1025ff731952310067d6548730006ee62108310077d5354521005fd75d0531005bd7390940005ee720c921006fd650c740006fd5198b400fefe7694d4219dfe7308420006fc7258c4201f7e6554f21005ee72d0d52005fd710c820004fd76d0a10006fd6390841227bd74cc940065fe7095032005fe74989310057d75d83210bfdd63cc61022fed320cb40086fe6110e20004fd7398a10006ff7358442005fd7695232006fc6198232007fb2150110006fd32d854019ff7314c420006fe64cc650007bf43d8941007f721485300b5fe708c931007df3258232006fd3258440005ff748c921004ff73591210067f6518d402f7bf5490b31004fd7119132006fd7198a43007bc6410d21137de314c440007dd5350730007ee3248420007f72188440004fe76d0d21006fc6518931005fd74d953112efe10d8d101377e750c440006fd5398b10006bf64d0531004fd73d8550004ff7158e54196ff65087300067d6510c21004fd71d9232006ff6448550007bc744c940006dc7258c21005ff7355321006fe6408730077fa708ca10006fd644ca50006ff6588540006fc7358420005ec724c620004fd739
  | 39 => 0xd7518931246fd63cca50245fc7348650006fd7118943097bf404864009dfe73d81210a7dd30c8430007dd5308730004ef76508420077d5308650005fd71953212c7df500ca310d6ff644c820006fe7358720196fe63086400467f52189530257e75109310067f654854007fbf4310831006fc425865015efe53d8543006ff6150530005fe7418121006ff51d8f21006bd64d0e31004fe760c941006bc7359220066ff650c84007efe6310a41005be7498232226fe53d8d40077bd74982320077f65c8510006fd6590b200067c6518d10006fc7058432006ff4398a41007be548c9400c5fe7394941004ff7358a500277c544c650006fe648c910006f56108420004fc7258730005ec7250d3229fdc54cc93101f7e75c865015fbe5350f410c6ff63cc94104d7e751923209dff7510d21005fc724c440006ff658c930106fc6390921235fe7308640005fd70948310c5ff73507300b7fa404c44013fbe740c740007f510547410077e5054d41007bf744864007dfd73108320069f64d8d21237f7314c640226fe76cc9400077e52d0d52007fb501832110dfe7188430006ff75584420b5fe70d09310067d6588730005fd7090b32007df63cc9401cfec32d8132006ec6294931007bf41cc5400267e65d9531006bc735901024efe6394842007ed708c9210077e5050d52127f8500c420006fd76d0f210beff64cc420006fe735864201f7f52c865019ff830189300077e5110a50007f86090d52006fd7198830005fe74d8d21004fe7618d20005fa7688110006de74d8d21006ff65c874009fee434c9210b5fc7050931005bc7448430005ff7055232005be74cca50006f9435804132fbf548cb41117f561884300d7f6104c9100eeff63cca40005de7308440006ff64cc721006fd644c7202bdfe7390a51095ff7648610004fd71d8d52006fb4398251004fd7610c2114ff9700ca10005fc744c931007ec724c420007f72188530006fc644c721005be7408650005fe72d0d31006dc635452115efd630cb41266fd6390d51004fd7398a40004fd7688430006bf64d0d2119ff5310c420007bf4148540004fd768c810006dc63d812107fbf4310b31006ff7648540006ff7258443006ff4318931007ee324864014fef328ca10006fe628c650097f66148430007df32d8131007ed5250d200eff850cca10006f976c8220004fe72d855319eff3218930096ff64484200bff610cc510075fe7018632196ff3118931006fd6550720086ff6310c21005fd7388720007bd521094013efe648c440005ff724c5400aefe63c8640005fd7598232005fe7418131006fd644c420005fe7648530135fe710c84029fdf50cc931005dd7390931007f55150910076fc20d8d20004fd7610a31006fd72584430077d53c86500befc60cc521006fd7098a43004fd7199032
  | 40 => 0x8070002017004800023e0000340000000005000800001e001000000402c00102f000001400c005001c2f00000300088004000004001404c03b0038048001685011000006400300b00f800400000080000bc000001000000000c007802400c00800082b4018000000004c1a82b10368000062001000801c0380000010010028029005800400000100f807000800f00001fc0151df007812806200500e00080ea010034800402c006011000400402500001a400000401780001760000010014006002b910f985f8008006800407000001b014001600401e00e8006010001802000e0000288006cba01405e80780b0004000003400002b00102d80160590e402040400000100068528003011294000001e08d090402c002002006000000f03b801404a0000000010034008000801c0200061978458114000000292c018003000000c01200000d819c00400501001c40b063f00d80000000c0023000000400007a800c0700d7004ff7650f2019fed320c820007f510d0951095ff764843020fde5390730005fe72d81310aefe53d8532007bf4310a210effa40cc840006fd6148630006fc7358440005fe72d063014dfc73c8610004fd7610630007bd5310940077ef208ca20075fe70d9232006fd75d8d210067f65cc5400077d5210a50006fe7198830006ff61cc5500b5fc7058931077bf408c8401a6fc30d8931006fd70d8d21007f47154f21006fc7058c2123dfc73c8550006bd64d06500b6ff644c610007be5390b40006ff64cc520004fe7299231006ff6148550006fd64ccb20006fc620c550005dd7308720006ee62c8430005fd728c440005f970d0e10006ee62c8610004fe7298910005ff7254d43004dd7399121005fe76cc540066fe760c840004fe76085400adfe73953210af7e65c873007efe6310a20006fe7598b31006fd65c872004e7f51d8d52006fc648c910006fe7198840007bf7150c42006fd6510430007fb6090d520bfbf40cc640006ff5458632005bf7454931007f921d02400eeff63cc820106ff3298b43006ff6508740005bd7494c421377d7508440006ff6590d21004fe7610921237f5310c640005ec7250e21005fd71d0d51006dd7558c2113fbd418c740005fd73c8650007bf438cb40004fe764c540006ff650c941006be648ca20005ee72d0521005fd758ca41006fd64cc820004ff73591102b77f5354b31006dd634c840006ed628cb10007dd70d8d21007cc624c931006fe5358642004fd7608440005f5710cb100aefe43d8532007be71d0e42005fd7348640005fe7290d5223efd63cc950004f77648421007ec620c9102b7ef3259632006f87358041006be7299031004fd7198a50006fe65d8632005fd710ca40005fd739084209eff6318d21007bd32d0540004ff7158032005fd744c521007be53507400077
  | 41 => 0xc003000000201603b81f990a00b02b833a2640050f905e400203f00000d400000100000bc03e04c00180e800200e002826003001a00906780440090038d180d401c003800410e000002800001600100000200001271c2000802000704180e8016000006806448a011019801800000c000003c004000000804800400a006002c004000000003409a04a1a600140080a2000005408c001001064c00a00e001007024c0130b500240001cf000801403a009000007000e000010811415206302600600081d8000000c000001000806c658008022800000201100000000040000018024862001007003000000900b8134000000005014400005d0008030032013006070c00a002011003802e009015002404003500b00480300030740028000049014003000200106a0054106038030806400098b000000000000000a000413801500880881b6002001800440e00200782f000e00703a800005401500b1d0c02200c00400d404a00a009801c00601501a011402600f000800003c00000000141a800400402314e601e01e805001e005000012404a00200000ac056000012800002806755d80a40000c3006001c02401800b806806a000000800d1fa000004800000203801d8038f6a05900280180160cf0008008000045000001800a0ba000000c02202e000000002a010007011801c000001007000885400080000ba196001800c000062013006805a07801e82080260001de004803607e00a00840000d42588000008032033802401001a003007404800300d002900a028106064826800a099002c1741c9000817c37c3e702f804c054006054807c12e149017044c00000000000003260282e6809400000400e802805a0030050068008000002002c13201100000280000b1000249400207a00b004003c00643181d401e00700080f400c00d000000c0000000ee004800600300081a402a00b002000006406602682a811c010009800802a024005806c0240110230006e9a00900780a001400700080200b8015001808001001800080e4006003001001400203300de6640040040f9d45404a29d00c0598000019003001d5fc01208600000120000050064094025001002800a002004000c04c00700a800000015002980f4016000096803c0001c107b802000800e038000000600700081b0194000000007c05a00100380dc096001002000800800000500100040000ea001000c00100000080be052047808801400600e0004007489001000000005d000000006a1d80c5001c00c00600e801c00002d00380081120000130004000068231029400607102c002c34a02105a001000a003008808802e00701294e000000d000807400000400a0000934025000801000c01d00e000c004005005803802c0b800300080240020640008006013011867c0e600601d
  | 42 => 0x40008002025002800001400701000b047202f00582f401200400001c0003065009002190e1ee033000800008a005800000004a03000000b8006002800401000c00e813c03200a002001000200000680d008c001011800000200300980e00f807d0438390000000007800c002003004800400c00a0a3000c024003000000013606c0018a400220080610004012011007800000214200600f006800202a8030032001000006006a01f0520004036007000001535605e00d800001e0d3003806805e002004003000e00600080081e40030010ea4156005000806800202000000c401800705180000be0020120088a0a024000005800e005002000001403906d81a4006083006801400e00507800b401e09600395400000070000060076033020000012a0320050004002010000005400000802300980d600d00a81dcc9c00803c801c052037000001c00002b00f86300f001d0018030004004090000006e000002814c000000023000c02e03f00380983e6035007001000000001280e40a201600302d0000001029001c0420010040028000005004005c0d6054002009c00001c00380e0192011004801c01e00f01f000400c01600180043c0c750018040176049006800c002008003001400000e008aa9c02a03f002000801200000f800c006007017800419601000f00b0000100000001401608b0b8800c00675d034802006c016009801daa000000080f80000030ab800800600300283a003818f0040014026027001004400c0000908014002034007801403e01900b826000008300100640000020000018242000007800825200000e018c01d2c20018004016008003891800200100481f4022013011005c01c004002800c00a039004863000403700800240241170ca000c04602100000240040a0002000c4f200000900387e800500a810800801c0000144010002001000001400c187004806e004000806007a00a15e80e929e001006000000200300d80b01a2005003000000407400000040c407a000800800a0040030078028000000003413c02e065870008a00701c823005008403d00a402ae910009568000008000000000605b06d02380d203401b0064052006004800000401700080280040054bd0040074002aa002400b800201181d403401a01b00e8000000019800c00a0ce016801003009c000030c0060000018030de400b000803c0500d500006700dc006012802c05c00000000240123540158054040003006817605805100180d4b7c0000050074052231002009c002002026815000a000000800c00000c013001c04c000009002800402b006000d41c000019a28c010004006000412002013a80040d4012020000000e0120028008000009005002801239d00103980680102db001010e02d00700d0018ba410500d8000074018016000
  | 43 => 0x2010001805804e092038432801a00900102280173d30060118006044003007802800000e80d403400000022b401a1470428040052054069014005400b001802837000201880f000600500083092d4294005800008803a02b8320010000015819000600200600d40060050028018010010004009c02618400280300020090fa004800001c007806801e00000201bc19a0e7003002400802400900c80d000000000b0026007000014001e003004802400a02c0030028044001007846005600300600000200d001a001c006af400882540175e80000010012072038002402a04d020809426000701200941bc00a00c002c0100040088000010a0e00000103a400300041944260170008c0800e003002066838a0c5011004807e00d002800000000604880a803a026000011000407e0010ab803a00100f000000c00600000f8020030000834802a01c0ca00152c400000b81bc018002024804000000a03282b00000100078000096075009026000c0090609a3c02e02c00080cc0080010012128000179000000000c0000d800240020050020010000012000003c072041005093c01800d01700c5b6c059022003000001400000280000390000008000002000001402800201987880000060019f6801a08804d015400000f005019412e001189800001a0046498000002030001812c0f200f009863401401902f82680ae002000045000000100e004802206907380d000002b006800c1b8003001800000000e03201c4000000001007811200000581e400e015003001402403c00d002c02209a00009840200a700000000e4001082000415e00100000780a200710c000400e00000780442ca0ce00c005c0b80eb000860800c00900280300000007cf800000000000c091400e0ca0000174000002028005001603d00000b400600b005003c00a005009801402677c004000035e0a00000278138f5f00681a400a016004800000400001080b484200000100140101840060024000000001806002403000005280010620040b5007a0d201f002c59c02b00000ac088014003898c004000084077809c00301101bc08800c0110018000041011800803e0001a28004000003009802c002000008036800207300f800805e012004803800000900780840dc01100001e8004014010000003200000680140060f4001000004c00003386e800001d000827002e0020128ab8000000002000000603a007054400a01800c80300dc017005000000015b000841800c00000100bc004061002020c00001b0bc003c00806d00980e4000002090000000e00a31e81d417e00501380cc024012000007003600b000801000600603e80440a801f002800c056068008003000000b00100340ba19e002000403801300100700020180000028002074028000c3121f5004869403600500
  | 44 => 0x3600300000e442e00000e8014000028006008c00e00000001140000010338020000001019009000a0230308ff402c01e00780cc02200000d006000c008000801c01800100b80300ce002009800000a00900c0088010000000000400a000000800404a0140040088004007000804824e275015000c11a00000000dc0060240c2807c00c01205000000020400200008060001013004401000a00000040d8001000010c01e0000058030000006000804c006027008004c0020000128068038074000805c00a00002bb8b401a004016003820802a00680382e200f00580c00000211b2024800807f00000200120040060018022028029804804203700c802003600e0008008006047101801000000300e01e801801a00e800402000b000801000200700708840c82fb002000001603d010000405600603a800001400100b802c0320c00000028000007028801404a00111d800c05c006001000c01c003031006c02c16001a8054002002009000002a01b05f01600060680000260006005000006d7ec00701f800000a00000080180
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc7e7359642084295ef02b92c22000397d9532cc5400667d202ec1942000e7b8059432c80015f702a1ec0a90cb3798d730864000566412e8b184200cdf65dcd214c099d98c7192a2908632f58e74cc9410052ec2ee0b184247cde73594218c0015ef0c90843180036794d74d89300069e21aea3128600c3d751903248401d58a831064a08023fe1d6510b310066e3a0c6a8a4200cbc631d121080199f4c0b80651080337e0d71189300065fbb6e89088000c7f655c831500019bce0b1c64108034fd05750ca410066eb20e690e4000ade841c36348401b5e8139063200036edcc42502100073c3a864b008200cbd75d92644c4019bf0cb9c84190032f99072505300667c302e01924200c7c76d9521500019dd0e31264988031f9c56590b30004fdc0ae021c4000cdc31dd931100015b908b82c610847371cf63485100066eb9cc730c8400d3d751083150001cf2a6218c0a9003b318932181310047f438c890a6000c7f71595421084fb3e8339843a00031f9d8654c54009c7ec38c9b1a4245dcc738c921d000197b0c3a2a5190033b98970948310063ebace2312a6008fd811c9640c0014fb0bb82c7208036b1927290d210047ec3cc420c6044cee329db3250001a7e84ba865a08023f61a72d04300065f3a6c998a4212bba8090921500419b8e6b1aa521002bea0072584430074e438c9b1a4232c7e7159621cc001cf2643aac0208023f61a7290e5109e6e3b6e690e6000a9d841c163084014fd0c32a64880032fdd0644c5210053ec2eec90a8000ced659c831080018fce6ba8c4a18036dd0d7110b210056f406c831a4200ced7518b32504011fb0f21ec4a8803ad1d161484400047f436ea2126200e6f654cb2150001c7c84b2c83980023fa1b74549310056ec04e4b184200ade82d8c31500018feca3928688002b761b3298232005dbc0a65a0e8044cdc73d8d21500015db0d904a4208023f6077650b30006d6422e418a8015af7815c96110c015bb062a2c2191332fd8e74cc951004dec34e81086000ed98018c60484014fd0c328648800397d94638c9101966f41aec10860009de871cd21100018f8eca9aa4988029f61432d81410074fb26c721a4200eeb5098b21840019bf0cb98432804badd0161484400072e31ecb9928000ade82d8e31500979b8c7bae8690803ae90d43d8152006ce426e690e800fe9d8418c42484018fb0abb4a621002bd60654d853209f57192c89086000c7d655c232084018fce7b2864a009b3bd86720c44015e3fb1aea1968200e3b75909601044d7a9029926220123571cd53486501966f41aec10e6000c7f7459621cc0279b8c7b9a42a003f3761c63109210073cc2864b0082009f98718e20440019bee731243a0003bc14161c87200045ec34e81086010c7d515d8439444f9bcc93984220002be6183250210
  | 1 => 0xb01bb26419002ed60672d0d410047f43ec8992a211dd4734c5214400197ce732485900023fa1e3258440006d7190e8a90640eeba74d82608c8015db0231464a010b3760d76087300c66e31ae898a4200cdf831d94348401af0e0a9aa521003abd0c624c94015e6f31ae7a0c2000a7d85dd931500018fcedb2a62a0032be61c3298021006ebb1ae21922000cbd405cc6255001b3ee9b9a42980039e5d450189100065ea1ee2b0084008fe869d9214c0abc78cb21262a00035b5d64210921004dec388498a8054e3c6510931500019decab9062a00023f21d52d85300065fc3ac890860008fe87d8d414844dda862b0a622000397d96320c540006ae32ee690a80008fd81dd953108013bd0e39a42a0003b318f624c9400065eb22e221464009ec825c654cc8019bec6b8ca6908032f5d7644c521226cec20e690a8000cec64dc931080011fb0e284c59880367dcc4248540006bca98e0a908400d77315d4428c4019b8a93b664988026fa1e63508420047fc3acba1e4200af7815cd61c8001773003a262200033720d71988400066e39cc49088000c7d72d9731440018fce2b2884190032f9c064d8d210665fa02ec190800ccbd405d8321000197ce9b22629085b2fd01764c440006ce3a6e690e60008fc8759532440859de42bb043980023fe1d63108210063ebaac6214821acdf305ce6284001d9eca3126498a5f8fd53654c9410055ec08e4b2060009de87cc9311005797ee7b8ac99909b3b586720c4400065e3b0e890c802be5e8518f41484019dceda1484988031f5957398442006cea06e6908800097f8754b41940011fb03394c9980023fe0576cc8400061ebaac82146400e6e8598921840011ff02bb485980d33de19710c8210063f38acb21e40008ff8754961cc0012fb0a39287a0802bea0e52580410056f404a9b1a4200cde74d8e53484278fec6ba8649084f971cd65487300055ec3ec9a1e42008fe87d9521d00019b8ed29a429810f371cd6348440005aec28e690a6000e3d651d121cc0018fecbb9a8288003378c7764c440065f4402a41964000cbd645c2520c4016db0a2146490963c7d52540ca310047e432eaa1a4211cde73d8c62440015eb02196c0a08034fd9574cc910006cea9ae9b1260009ec825d1314840197ee9b12c0988037358d720c4400063ea92e7b0aa800abc84588604c4019dae531062200023fa1e32d85400b55ec34e898e80008fd819da4348001d3ec9b1886908023f6187454c2109c7ec3ec9b1a4200cbd645c443880012fb0a39286208035e54c7054a320066e186e6b0e40008fd8794d61908015f507292c0108032f1d9434854009f6639cc490e6042dcf215cc21cc0018fccbb9ac2210036e5d063881100047fc32e5a0c6025ef05058631080655b906aa2c61080337e0f764863000766320c71924200
  | 2 => 0x573191520ae6e31ee790a2000cde7018f41484015eb02396c2a98029f61463d81210066fb9ac290e8000cde305d821cc0459dd0f31242180027d60775d0f210066eb80e0b184200afa82d0c6054801d76eb212c020802b7e193054f420666f392c7194200e8fe87985608c823abb0a39a4288003379917308430006f4280e49884000cbd635c442d0001cf50a194c020802eb21152908320065f39cc9214a200cee7254b63500011fd0fb12c0988036d50d711093100736996cb90a201ae9f4058d3210001cf2a4282c390002eea0b43502101066e31ae7212a000cfb501d932440011ff0cb8ca7210033799373484200066ebaae1b1a4256f5731549538c4019eae4b0862200036bdc8424c5400065fb2ce81086000c7d7659531c80019bf0b3b6649886b2fd03764c8400065fba4e8b086400cf9701c1610c847dcee4b0a4218003bad4070988310863f39acb2184200cdf7394d61d00018f0ea392c020802eba0b434c9400053ec28c918e4000cef659c831d00011ff0cb9083181136bd0e720c54015e9ea1aea1968257cde7358e4294401d9ce8b1464188031f5da7510931006b7284e418aa000d3e851c941d00271fb0fb18c0908032fa1f43586420059e422a4194a045dcc325c831d00013bd0f29a42980031f1da5054d410047ec38c9192a200e9d73990210c0019f0ec30086a90033760b7359110006afb28e690a803acde7358e42104b9abea4b9ca5988033759773487400066f3b6cb9926200ed58358431100279bcc7b9a43280029f6147258c210066eb2ee690c8000d9e535d0614c00197eec3a243180035b6147250d320055e43286a0a4200ef35058721080011ff0eb1885080872fd007258440006dca1ee0a948400eb98019060484477a902990c098803b54c961cc4400066e386c698a42348fe869c84348401d3d07b26c690803abc8664084300065eba6c43026200e3c74d952144001d390e320c69091b57a1473486402fe9e2a2ea1928200cbf651d121840019bced29842980031fd977150d100063eb2ee4a0e6000eda80d8f6048489b38e6a1a42a00031f5497398a500066fc1ae23128000cbf845c662d0c0167b0a21664a0002af21170584320047f43c85b0a6044cbd439db32500015db0fb1064880032f9da42cc94000676190ec9928200abf8454b614c00197ac1ba2a4190032f1d9414c5400072f996cb1922000e796514360c8441c7a86b2c85980032f9d842cc9400065e422e231260008fd87994624c4013dd05bae82908029fe1570586430071faa4a8b1e4200e6d32d9432500014fb0a32063900023fa1f6158232006dda82e810e40008ff865c654cc8018fce6b2884108023f61a7294c4109e6f29eec90e6000c7f7659521c80019f0ec30686a90c7371cf70584320047e432e021262008fc865d131484019b
  | 3 => 0x890e6000add86cc153104855b90c996c098802bba084358a510066f326e690ca000cdd641cd219411f9bcc7b82a6108ce3f21d6348420006ceaa4e610e8000d9f74dcd211000175b09384649086a3f61e62cc8400056ec1ca4b086457cde7358c429445397ec73a665080031f59773487200047fc32e021c4200a7d850c961c80318fec6ba864a08023fa1f654c7200073d990eab008200ade841c163084018fecab9c42a00032f9c264948310074f438c831a42008fc865d632504699bce6b1c851083b7660c7054a320057d410e6b008200abf8654e42104018fee8b2a4398003791897110931006ceb9e8610e8000a7f855da32440bba7f08ba885988038f61365505100047ec3ca63128000add8399032884279bee9b1e62908023fe0576d0e200074fc00c831a4200c7e73d943244067d986031264980032f59674084200063e39acaa164000abe841c9610c0011f90eb1a432800337dd7634c5210065eb22e6214a026ef17058431100019bac7b8286108023f21d644c9100066fc1ae33108600c7d65dcd61108018fec2ba8c498803371937348510005bcc04a898ca00397f875482194001cea63b2862a003f2f5cd6410b320d67a886ec9942000bdb834854010001a7908ba864a086b2f50173988403b71f20ecb21220398fe87189324c001bace6b8884988031f59570108210053ec28e6b088400cdd82dd94310c27abee0ba8c6908d32f5ce64884300bf5aa02c39888012af88054d61c800197aed29c84208030fd957418d10006e6b946418a801d8fe87989328c0012ff0ea9843280033b9c262908310063fb02ea19082009be870c941d00839bcc6b9c839004f2f50d7198a4309cfa43a8298a4200e6d5318952504011fb02392c8980026f61f4388740005d64128390e8022eb74058621100015dd0e31264a0046f6a0c628c1100072eb9aca10e6056cdc635d63250401a7908ba88519003b520d614c4200ee7d384e73142000db8865d220440019bee739ac2100038f90f6550d100065e398c8a0a420edda831c1528c801daee6b0a4218002bde055398a31005cec1c8598e80008fd87d0f62544019bb0fb1864880032f1927290d1015f2f3aac61968200c7e76d95215000197b0d39683a00033b5c862185400073790aca10e60008ff865cc21080879be64bb064200023f61e62106500065f3b6c821a4211bd8834863044001b98e5992c0989a33718f7154d21006aea92e72966200cdc7018d4148401a7ee8a9a4328057b318d32c8540004eec3c6418aa000cbd87d0d619081ff2862a188498802bb20943d89310066ebb2e11906200add85dc763484011fd0e282c2190032f5d264181311deea18ae11926200cdd64dcd214400197eca3a2c498857b318e32c8510006da2a2e21928200cdd87d8e4248401d58a831664a0802afe0
  | 4 => 0xc84018fecab8864a003f3b4c872590300066eba6c63024200af581189315000176b02380c890803ab1d26248730005d64128290a8034cde7358c42884018faeb3206488003b318e32d81210057bc0a64b068200cfa7618043548319bce7b18c4a08575b4c9750cb21006eda80e690c2000e8f6418e32484019bce9b18c0908032fa1c648c921004df43e86a9282008fd869d253084018decb39062a009fe50c5414c74000556412c83226200abd8694e4210401b3a80b9842200023fa1f63505500065f31ee890a2000ced655c831d0001dd0a1b84c41884fb398d32484400056ec28e0b1842139dd86dcd210c08bb5a8739063a0003a7d5363505212be6e39eeab0864008fd819cb63500019ea20b8ec6aa04776a00734851000576412c898a2000e9d83d93634840197908b8cc4218026f61e42cc7400065fb26e098a42008ff8750f624c4012fb0a392c898802eba0b41487400063e3b0cb98a80008fd819cb63540019d8e631242880031759673087200065eba0c9b126200b3f8454f43548011f90eb2263100032f5d06418d21005dbc0a8718e8000dcd728c83190001e9b0a31264988023f61a7290f100047ec3865b0aa000cbc845c662950019df0cb90622009b2f611760c4400066f382c621842008fc865c83150001cf700b2843900ebb30c8644c9311866e31ce919242008fd861d1538c8011fd0d3b242a004abea0063d81210063ea92e6312a800a7f8654953904191f90cb80649091f2fd8d74cc9501a63eb9acb10e600fdcc431c9434c801c7ac8a9687280033e98c70548420067a18eec98880008fd86dcd2184001af2c0ba864208a2dd205534c6500047ec34e598c2000ed78358531080271fb0d39087108033b9da748c92114f2ebaac61942000e3d6495131940015f507212c0208033e9db6010d520066f3aaed1906200af8805d66210c279b8c6b8c64a08035e195738811000676318e4a0a4200e3e6454953084015f300320c0991334f54d74cc9510047f43ec690a8000cde7058c320840157b03398c890803974cb65cc5100065f39cc92104200ebb64d81435480176b0221043a0002bd60743d85420066fc3ac62104286f685054943c801d5f30fb04c119003a715163908210047fc32e79088000d3c845d442084015bd09b8ec69080337dd56350c210065ebb2862146200add85dc1630844fb9a62b9063a0002af61b74484300065ebb6862104256cbd439d8435480197cedb24869090b37d85730873000677c32e418c8000af9858c96008401b3ca9b9a42a00032f9c26494c210055fc22e4b0ca600af9850c960084014fb0a3266390802afe0d6410a510047f43ec890e4013daf439ca4348401cbe65b2e62a000337d9573084400073ca98a0b0e4000b3c8454931940012ff0ea906328002cf211520c650006ce39ee
  | 5 => 0x80ea5f21d5254c410063ebb4cb98e4000cbf76dd121cc001d9ec7b1064880038f9d56310a410063f39eca3128000cf8641c1524c4019bae621cc528003b5cc961cc4400063f39ecb212206bdcc321d1534c8ad9bcc6bac64108033e98f7054a420065eba0c83126200bb5811cc6448401cb8c7b2e62880032f21171189400067a882e2312a800cbc87591210c00137b0e21063a00cb379cd639482107e7a98aec2106200cbe76d0e2150001978c13a664a880379189710c9100067c312e030a8600e5d6394153908018faecba885108036b1c83250740006d72a2e418e8000cfa83dd92008001cde65b2a64a0002bb20973584420056ec2ee8b184200cde76953324c40197cc83928398002afe0d71191520066e31ae1a0a4200dac541c941484012fb0bb8264988039bd8b654851000736996ca1922000bb58110a3150001b3ce721043a00023fe05768c84009576c346490e4000c7f72d9541440019bc603b242980023f21d52d85400c66ec38c6a0a4200cbe7359042040435f501298c4880032f18f74485100057d41087304a2008fc8754d61c801fd5a863a2c4188035d5977154b3106e6e398e0b086400aee8218f6244001bb6a1b9a42880038f50f6590910006d7a18e4a0e4200cbe76d0c424c449d6e80b08622000397194634c510004f6412ea98a4211e5e75d8c32440011f90ea1ec2a911277a1f73485402672f3aec6192a200ced72188614c001cbaebb1884908023fa1c644c9500047f436e898a4200aed868cb2184001d9ec631264a0003335cc62085400063ebb2ea2126200cdf7390d62944018f8edb2a64880033b5c872584302366ec30e690c8032cde631c9318400187aebb20c69084f2fdcd644843012e7bc3ac21888000abc825ce64944011fd0f996c2a00023f61e62181310065ebb6872146200dda40dcd21100019bac9b9a4210002b7e015498c2120c7fc3ac62148200cbe73d9360484019b8c8b9842980033e19070548320065e3b6e890a6010ced215d8430840175b0538e87210031f19573189100947ec0ce5b1a2000cbf659d03108001978c83928698803b660363d81210947ec38c7b024200cdf65dcd414c401978e8312c098803abd0c62085400047f438a0b1e4229cdc73d85214c0014db0bb84c4188023fe19750c8410047fc3ac99942000cbf655d0614c0019baca39a43a00032f1db41485400065f3b4e5a1a820fe3d43594420c4019bec839a43080032fdd464cc521004bfc3aa421aa200bd5819c2320c4018facbb9a83900032f5d06418121006b7428e4a1c4200cf964dc1520c8019bec6b8ca6a0803b358a708c8310067ab8ac33046400cbd74190604c80197ee6392c8109a77310c7254d3215e6f982ed29e8200d9e7310821d00015f507212c010803379c263948210056ec04a8b184200c7d635d76
  | 6 => 0x63fb0aebb026400abc835c464548015eb02324639000337ddb734843025f2ebaca831a4200c7f865d4321042b97ee73264218003371907348550006cfc26e690e8000cde86dcd215004d9bac2b9842200033b9da708c9210063eba8c818e4000e3d6495121940271fb033b486909bb9ea03650c9102ee9f428e8a966244cdc635c34348401d3b0e320c69086337a1c63505210066ab1ae31904200eac54988420c4015eb02192c2200038f5d165087300065e3b0c921a4279e7a80d954344091abce6a9e8528002bd60432586500074fb26c6a1a4213cdf74d8d434840137b0f21262a00036dd917110d2108d7ac0ce0b086400cde7618d434840137f06b86852100337596730844000737102ea3128200c7e731946244001b38e9b9a42a0003a79cf4318941006bca98e0a966200e6d3259721c80015dd0532242880033b081760c7200063eba2ca10e6000e5c6518d32500016f3012a24328003978c575189310056ec28e1b1a42008fe8719132c80015f50e192c0208026fa1c424cb400066e326e690c2000a7d859cb63500e1cf501b2a6488003379c36390d210867bb12e221a4200cec645c831540015dd0521ac5288031f1cd65508420067db2ae030a8600d9f409cc211000197cec32486a90032f1917190d210071e20aea3128200d3f415d432104011ff0cb9e8310002bde0543d85520063eba2ca90e6015eae32993210c0015f30021ac31004f6bd0e7210d210071ebaac62148200cbe73192424840157d0da1a82908025fe1d53d06500063ebaec62124220e9e8418e42484011fb0e212c2180031f5d743189412366f300e69088000afa8290d60944013bf06b8085990032fdd163485100057a4328298a4200cdf865cc21080015bf06b286488077a7d0163cc8400066e380c6a8a42a1f7050443439440137f06b8c85a0003378c376487300047fc3aa73168200ef05058421c80011fd0fb22c49880337d9373484200065fb22e7b0242348ff8758e42884011fb023b2a6a10433d9857110c200947ec3cc51086000cbf655d0634400197ec6b8c84a00031f9c5659083200576412c890a20008fd86dcd21100018facbb8a879009f37d8573087400047f436eb2126200e5c315d4624c401b3ca839a43a00023f61a72d0e3111e5fb0ce810860008fd8798831100019bced380c69085b2fd8174181310059e422a410ca04dd77515d731c84019bb0fb1e82908033edd931500400063ebb2ca18e4023ecd211c163084019bce9b1ec090802cf21175c86502b76631aeb1924200d9c73d0521500012fb0a392829884f37d9773484300065f3b4a99928000cec74189324c4578fcc8ba864208033ed41768c7201375b3a2c21888000eb581d0d6190801d58c7b246490917371ce6448630004dec388598a8000cdf70d8d51484014fb0b312628
  | 7 => 0xdf305da5308401af4c0ba884188032f1db74485400b65eb02e8302624ccdc635d53148441d3cc7a1c84108027de1d210874000577410e6b0e40008fd8798a31100019baecaa46418802faa0863881100bd7bc0ae6b084000c3f655d332440018fce2b2c85901a2f5e0565cc9310063eb02ea1964200abc82593438c0831fd0e32262908023f61a7494e210066fb9864b0c80008fe8794d61c80439ef0eb0c42200033558d7110821006ceb9c65a0e800097d851c94388401b3e81b9a43200cb9794f53189310074f39ac72108200c7d759c46250c2b8fee6b2e439800397d97634c5100047fc3ac72164000cbd765cc42904899be653b662a0002af61e64084300056ec3664b046400cbe769cc64484018fca1b9ac5288032f5d0745865309d6f41ec9b1a4242cbf615d021cc00197e65ba2c688003aea1e42580410066eb98e6b088400cbf435c46250001cbe65b2e628811337a1873485400065f318e89084000af78150f61480019f4c4b8083180033bd96720c5400056ec06eab1842008fd861c9540c41fd3cc7a1884108023fe1d53586420071eba2cb31e4000abd84d8d21c80019bce1b1ca6908033b9da5290d200056ec2ce8b184200ead43d88424c401b38e9b9a432009737cc373584200056e422ebb1a4200aec80552620c4015bf0aba6c69080337dce7358440006cfba2a690e6000dd8505cc21c8001978ecba262a00027ee1d218c1104a6bba96e2a9a6200db7435c442084015db0bb84c418803574c975189310047f438c498a8000eac5498a420c44bd3a80b1c6220002b761d54d8d21004fc43a429842000e5d3159431c8087abd0a39a42200030f5d764109310066fc06ec9906400cfb764854010027d9cc719243080029f21570586320053fc32a6a908428e7431d95314404b97a80bb46220002af6127358720006ba32ae21922000b3d8510931d0001c7aebb20c6908036bd0e72d05210075b98ac898c4000c7d615d760c84018fce2b2e6590003a7a1c64d8d210065fb22e031a424ccde73d8f4254401d3d01b20c690893a7501630c4400062ebacc62104212af5819c9618c0019deca392829084abea0232587200061e328e4a0a8000e3e639954310801978c8b98c0908023fa1c32583410066fbb0e69088000af5819cd61c8001b3ee9b9a4318003a76006418d210055ec38c92126239cbd635d332c80019bacb3984390003a7d917018d210057d418e4b0082008fc865c331484c9c78ca99682a004f3798f73487400047ec38c918e4000c7f74d9521440255f100a8ac3900032fa1b74549310867690aec21c4200eac631923248401d38e0320c6908031f5d764d81320055e422a63128600cdd74d8e534840197d0c3a2a49898f8f19432d05400065fb22e129a426ccdc63dd153484015bf02b86c690803a7d9370d8d210
  | 8 => 0xc8b9062100023fe1d53189100fe6e31ee6a122000cdf65dcd21d00011fd0f31263a00032f9cd64948210055f438c8a1a4213cdc63dcd2184001a7908ba88598802bb60074588310063eba2cb90e6000de7625c4424c401b3ee839a42a00036b1927290d520beed418e0a966200e7b8059632c80015b900aa6c690803376027618d210055e422e4b0ca627daf419c831d00014ff0ab2262880333d441760ca1000676c08e4b222000cbc645c64254401b6e633a0c0988023fe197010a310059ec28e990e80009f787484210c001c7aa5aa2c2210031fd9573085400056ec18a0b086400af5819c961d0c279bcc6b8c64100033799173086500065fbb0e4a1e8232cde7358e420840197ec8b846490803671d073487401965eb9cc810860008fd869cb41840011fd0dba464908035ba1472591310059ec288490e8000c7d851d9524c4016ef02a9aa4988034f21175189410065fb86c8a8a4213de5325c44348401d3ce8320c69084e3f61e325842000737a98c4a926200eb73119131484018fecab8864880033718f705052112e5fb1ce830262008fe870c960104015dd003a4c4188032f59674084300047ec0ced21aa4008ff874cb604c4279bcc7b9a4390003375d763d0d210065f322e321662008fc865c3424c40137b0739682a00038fd5254586320066f436e690e8000cdf635c343484015bb0d1926420057ab4c964c8430006bb98aea212624ff1f54952320c41b1ff0e98ec090802bba03759883107e5fa1aec2106200cbf60dd152cc4579b8c6b9e83908035761573086500065e3b2a890a80008ff865cc4208001d5e8631064a0803abd9362109310047f43886b0ca000aee8290f615480197ee83226498802bea1232982510069ebace62148200a7d850cb615000167b0a19283a00eb1f58d750c8410072f31ccb98e4000cef64dc9604c401bb0a0b98421011767a1073487400073c3ac64b008200e3e53d9153484479da42bb4421820f9e201659072034eb6c28e4a9a646ac7f7654d528c801b3c633a0c09880357d977348510005bcc04a910ca000abf865d232100018fecb39064880023f61f5198b310047f430e8a9a4200d3c65dd1214402bcdc64b2e4398003751cd41485100047fc3ac43026200e6d851d1620c4451fd0f3124220002bd60464485300063eba6ca1922000cbf645c4424c49997ac73a664a889f3b992720c4402476a18eca98a6000e5e3159531c80279b8edb1886908023760c7258440006dbaa6e29968200e5d3259731c80018faebb1884a091767a1273087400063e38acab1e4000c7d655c2420c4018faea3aac2190af3718e744c5210066eb1ae11904200c7f7694153904013bd0f99263a00035b58975108310047fc3aa6b088400cde635c242084013bb0f1906220002b760f72d85400047fc3aa63128032c
  | 9 => 0x65cc9400063e3b2a6a1aa432cde7358c42084018faeb31063a00023f61b75108310965fa02e331080008fc87591214c0e7cf501b2e64880031f54971189530957ac0ce4b084000c7e73d9431500012ff0ea9884a883abe20165582320063f3b6cb98a8000e7a2059561c8001cf0c632c60880ea3fa1f644c52112d7d40464b046200a7f86549538c4018fae9b2a42880026f61f43085400066f3b6c99926200d9f741cd21900015ef02b1e43a00a7b5ccb614c5300074fc3ec831a4215ade83d4763c847397ac6ba4c790002be616425802109e6e31cec21a42008fd87990624c40197ced2a042a0003bcd4161084200063f39acb2164000cde70d8e42484019beebb82c610802bd60432586400066f320e690e4029cde7358c42840018faea318c4a08023f61f639095000676bacc51908200d6d325d442c84019b8edb9a43a004e7761b73487300066eb9865b0a8000cbc76109215001d7d100a9465900032fdda744c74010e5fa02ec1088057ecc32d95324c40197ae6b8ec8a90d31f58d750ca210066fb98c490a80008fd87d94424c4279b9073b08690803aea0e42580410057ac0ce6b088400cdf635c432504011ff0cb8ca9190039ea1442980310065fb22e2212a227d9d415cc21d000137904b8e87a0002afe195350c421966fb2ae610e6000e3e74d973250001b38e63a24218002bba0b515843200736992ca1964000cbd655d3608c80197ce8b10c0988035ba1472505210065fb9c84b008200e5d751906348401cbec6a9aa4a08036b1ca52507400063eb2ee2a1884228fe869cb3144091cb8c7282a6a08032fa1c64cc5210867a30ae221a8400ade801c96308499cbb0a31aa2908033b991720c7201d63fb1aea1908200bb5810c941d00219ecc2b88872900337190734842000736c28c4a926200dad431c941484012ff0ab86869885f7660c7054b31006573b0c91924200abf815934394001d38a9b1e82908031fdd632580410a774284c590c2000eaf4318a3250133ed0a1902a5a08036755073485400047f43cc890a60008fd87d93325440157b0232286a90023f61c5498b310757d404c2b046400e797059431c8001b58e599283a0002bb209735844008e6ec30e690a2000c7d65dc563c80011ff0cb8084109175761473487400056ec2ee1b1a4200c7d655c0420c4658fae6b2843980029f6147258f411de6f39ec72124020cdc635ce42480019f0a0bb063900027ba1e32484202167790aed10e6000eaf74989210c0018fea4b88c4a9802bd606639864200737996ca99220009bf815ce42d00019b906b8cc5a1967c7d52548ca31006af286e690aa000d3d75d90424c401f622128884a00023f60672191500075c2a0853004200cdf64dcd21440015bb00326c6908023f21d6448610006cfb9e8690a80008ff815d843080019d8
  | 10 => 0x3122000d5e315d4424c4016bb0728a65280033b1c9614c4201a677434e529a42128fd8798a218c00193cc9b9a42180033ee0f7648020006ce3988490a8000b7980950319404fda862b0a63a00034f109750c84100576c14a33166000bb581d0d31d008997e873b664a00afa718d43d05210063fbaceab086400abf845c1610c8018fce2b2c842100357cc975189310676d39865304a20fcdc7358d42108691ff0cb9c42100023fa1e53d8540006563a0c4a9262008fc8758d21440011fd0faa2c219002afa0276191210074eb9ac62148256cde63dcd52d04019bcc839a4308223da1415290f200d47ec3cc59948045daf435c831d000197ce8b0cc119003ad2054358442004bfc2ae1a1a4200cec625c6524c40147b0a392c8108032fd9574cc9102666fb8ec6192a200cbc541d932504018fecbb9e428804f3718e7690d210066fc1ceda1a42009ec825c043884015790ca8884a00029f616624ca3000676392a4b0e6000bac8250e21d00011fb0c39283980034e19574881102e72e32a6598a8011cdc73d8f2144001cdecb1964288002e7a12708c8310047ec3cc810e6000cf776d0d21084019d8ec99642a004f3798d718cb410074ec24e1b1a42008df835c662100cdc78cb99682a0003675d153087300065eb2ee890a6043dcc325c8311010fcf100b2a8790002bb2096348510006edb9e64a022000b3c8454a329400157f0eb188520802af21165592320066e386c6a1a4200abc8458f21440219bce8b1e86108029f21953545212657ac0ceab086400cbe645c6428c8011f90eb226210003371d9324c54000677bb2a498e4000cdd74d8e32484011fd0f992c1a0802b32097058c21006dd986e890a6020dce539cb434c801978e6322a290803765cc638811000676bace5b1e4200cbf651d1218c001b5ae421062a0002bba1a32485100071f31acaa188400ecc628ca31500018fceab88c49884f3720e7690d210047fc3ac72162000eeb501892144001b6a86b888518803b318a320c5400857dc088730042008ff8759732440018fce7b28c2a00034f9d1520c6501473cc06cb90a2000cf987d82604c401c7aeb32064080027761f32981310071fc22caa0e6018cde63dcd41c80018facab8084190031fe1d65108320065fb2ee890e6000cec764c921500014ff0ab2242880033b990724c6200966f986ec90c6000cbe74d9331c84012ff0ab84c319002f5e05748c8310053ec2ce4b0c8400c7e7619632440011fd0dba2a6990031f9d57198a300063f3ace6312821acbd635d2608c8019dae4392c22004abd606725843007f56990e4b206000cdc76d8d43484019baeb31884108027e21d2150210004bfc3aa790ca011cdc73d8d41440a7ab8eb992c0988035d9d5711093109e6e3b6c721a4200cbd60dd1524c401978ed21242a00039718c
  | 11 => 0xc0015b906b92c22004f2f50d7198843006cea00e69088000cdd655cc219007597ae6b208218002cfa12514ca500057741486b0ca4008fd861c953d0c01c7ce8b2863900032f9cc6418121004de43a8690a8000db4845c4325040157d07394c810803a761c64d8d21006ed200e690c2000a7d859cb63440019baed99464200031f5d5711894100576c04a8b106200dad549c831d000157d09386c790803371d8734853000757a18c59928200cbd7698f429084d5ed03192c22022b8fd516550730006b6b2ae418e4017af4865073144001978803b242a0002bba1a4210931006af39aa410ca000af58190d61108019f0a03b264880023fa1f654cb410061eb2ae9996400097d851d23248401b5a80b906220003ba14070988310072f992cb98e4045d9c73d0d21d000197907bb2842104abea003258720005edc1a42a022000af987d4062440018bacbb9a43980037a8cb70548320055ec18c9212a0008fc875913284149ed0a190086a920b6ed5370549410066fb9cc49086000cbe73d904248401ab8ca39a42a00031f9977158c420066eb9ca73168000d5e549cc2194001d76c9b0486a90634fd0d750c9410047f43c86b0ca400ced659ca43484791ff0eb188510052bde0572586300066fbb260a9884398fc8758d42c80017af02bac64188036ee0d7488110006b6c2ce418ca000cde86dcd21940279b8c6b8c64a88032fdda63508420074e326c6a1a4200cbf439cb615000153b09386c690803ec50731501100647e432e518a6000cef655c83110001d3e60324a6908034f1d1534865000676bb4a418e4000af58114163c8429de0a0b0e42100031f5957388720006cfba4a690a6010cdc76191324c401d38c831e86908633718f73505210047ec38c910a6000e9c5418d414840155908b10c498802bde05755863200577434643024200cbe74186608c8011ff0cb946220063b318e32505212be6f39ecb2126220cbe76d0c424c8639b8c7b826290802be20954580310066fb28e69088045cdc63dc143484018daea31064a08033e1db6050d5200577410a0b086400cde7654e424c001b68e8a8a42880af371cd6354b410065eb2ee890a2000cdd7418f6048401b3ee6a1a43a00027721d534853009ecf326e69086000af7814cb615400197ceca9e84a0802bba1e62484300063ebb4ea214624bcdc63dd54348401b68c8b8884988031f99573d9721006d6a92e931e4000e753159431c80019de653b464a08033758d710ca100074eb1ca72108200af581192214c0017b10690a81080038f5d6640ca200059f424a2194a000d9c7390921500018fce2ba8c4a0803ab1906210931006ae992ea2166200b798095231940015f50f192c020802bbe156218931005dcc20e098a2000cf57648421100019d8643b264880033ed41768c4200066eb98c6
  | 12 => 0x3976177058c21006b610aea31a4200d9d831d1520c8015bd003a2c610802e760c424c74008d6ec3ec61922018d9e73d0c6250401cdeca312428800367dcc32507400067b988eca92620f8fe869cb434c8011fd0f192c020802afa107058c21004df416e6a0e8013cde63dcd218400117d0f3228298002af20964d0e100065fc32e22168048d5e7354c21940691fd0f192c390046b720d52d8d10004f7c3a41a1aa4008fd87d9431d000167b0a21443a0002be60032584200075d29c84b008200d3c415d46250401b9e4039a421000277e1d320c8400063f39acb2108432cdc635cc21500011fd0c39286880023f2197110d520066ebb2a610e6000cee70988420c473d988731265180022fa1e6450d100066e3a2c6a984200cf8761814354827baca6b8c65188032fdd96350c420066eb98c7b024200abe82d93434c40197ae83226290803379c363109210053f42884b086400e9f645c363484011ff0cb8084190039761463d81210047ec3cc42086000c7d7659631c80017b70690c8088003b9209614844000767b1c842124200cdf7518d41484018fb0abb0439810f371cc64485300067c3b6c121aa400dac74189524c4015bb00392c610802bd6067558632004efc1ae22106000cbc74585210c0011fb0fb1c84a88033de19711082100677b94c498e8000cbc76d0d3250001ada64ba8841904f371cf76487300066eb1ae02104268cdc63dc5535042f3ef02b98c4880034f9d251cca500047e43aca90a8000c7d655c432c80579bcc6b9e821004fa710d4358a3100636b2ce418e4000cbe401d931500579b8c7b8a8690802bbe09511894009e6fbaec621a4200a7d850c960884018f8ec32a42a0043790857110d210056fc32612988200c7d755c6628400157d0830cc11900357594734872000667b18e498a4200db4315d0604c4018fae9b2e42880033b9cb62181310055e422e6b084000c7e7359661c8001978a93b664a08033720d71189430065eb22e11904200cdf651cd21900015bb012a0c6909234f54e740c6500074e322e031a4200cfb87580608c8019bae6318c4a095bc710d5350d520063ec28eca1aa424cbd405d831100015bb0d982a7a10033e1907054a3200576c06eb3106200cbc74d89604c519abca239a43280035e58175108311cc7e43ac690e4000b3d8510b31500011fd0dba2a6908636dd0d710c941166bc3a864a042000daf845c831d00019790ea1ac221123c790d53d0e500047e43ac89946000aef825d16194c014fb0b31265200032f1d3644c5210066fba4e9b1a4216af88055161cc00197ee6322a2908023f6187454e310062fb2ee690a8000cbd659d0218c0659ef0cb8887108b75e1d532502100047e43a64b08800eafa8094662cc01d1ff0cb8465108032fd037158e540063e39acab0e4000cdd65dcd21
  | 13 => 0x47e43aa4b1e8000cfb64dc152cc40173d0938465188031f5977158c42006cf418e8a926200ebb64d8043548019beeab82c6108032f9db748cb400065ebb4e5a1c8400dd8501cd218400197e80392c32a04f371db73484300065faa2ec2106200cdf761cd21d0001cbeca99262a00cbb30c0624c9310071eba0ca31a2033cdd861cd210801f9b8c639286908332fd007258c4000577c02a93106200dcf639c8434841f1f90eb1a84210035d54f7154b3109e6e41ae33108616df1811c1524c4893bd073b242a000337a1276cc93121e6f430e690880008fe870cb61500019b8ed99262a00032f5d064181310067b882e2312a800e9f6418d43484015db0bba4c418802bb20965cc9100065f43e863128200cbe74188604c4516e902a966328002bd604628c5401463fb8eca98a20009bd831c941d00019f307bb240100031fdd365cc5100065e390e2b206039adc8355163c804fb9a42b9843a00027ea1f32501102b676bb2eb1964200eae82d0c625040197ec1ba2a49884f731ce32505210055ec20a0b1e42008fc8759131940019bb0abb464188363f21970d05310053fc3aca2106200abe84cc96194027ba8c6b888690803a7d8f32505400066fb2ae610a6000c7d655c3430840197ee7b8ac9100038f9d365cc91000677b2ce5a1a64009bc878c941d0001b70a13a66508002be607431815200757a18c52928200e6e32d9432440019bcc839a42880036b9ca420c7402466f39ac6214a000cbe735904208401daec6a8e6288047371cd6348510004efc3acb9926200adf845d7634840177303a1a81080933de1d618c4201dc7ec3ec72124000abe86944425000137d0f21264a0003375d763d05212556ec3aa831a4200cbe87d913148401d5c43322421807f1fdcd6550b30005cec1e8398e8012af4864c521440419bca6bb4859800337a027618d210ad6f418a0b1e4200cbc321d163440018fce2b2c862112357616730865000677418e4b2220009dd87993324c401cf301b2a6488043b3c856310c210057c41286b04a200cec724c960d040197ec639282a0003b3d8c620c910006e6398c490a2000c7d751903248001d9ac4b8464188d32f5cd64884300066fc32e610e8000cdd65dcd2184001cf30a214c0188023fe1d6510f210070ebaec831a4200cf4315c4644c0013bf06b8c85980036b9c8420c7400065e426ec9088000cee7098a520c401cde65b2c64a00477518d710c9100073cc06ca1922012afa80d8f6048401adc42baec190803ae19060d0d520047e432e219280138fd87d8e424840187acaba063900023fa1e644c9100046ec1ce5b0a8000cbf655d021cc001878cab8884a00035e59470548423df3d406cb21a2000d75755c4424c44f9dec2b9063a00032f1917190950134ee43a649888000cf783dd94110401b3ae6a9c85a0
  | 14 => 0xc549cb41c8401bacc239a42200029f61662cca40006ae98aea2106200abe8414163c84014fb0eb28841884a7e2017550d210056e41ae231280008fd8794c62504014fb0eb28639000337e0d71988304073da82cb98e4000cfa76d8243548cbc78cb19682a003fab50d621083100676432e41888000cbc649ca43484019bd0db9a43080e7371cd6350b2000576c16c63128000e5e6558f31c8095b9864bae869900397197630c9100047e43a86b14a200abd819cf644841d97ac0ba4c119003571947348510004fac08e4a1a2000b3d8510a31d000176f02a1e43a00031f195710c9400065f3b6c821aa400cde64dcd211013bc78a132065288025fe1570191210767c302e11924200e5d65dcd21cc0659b860bb043980031fdd965cc72013676b0ae41888000add80d90634840157f08b92c3980030f5d56410b32005cfc1a8298a8000e6d8518b3250401b5e8139062200cb1f58d750c8210063f39ecb10a8000aec8258521100019beec39a42a0002afa0c72592510045fc3ac83226200eda8018f60484014fb0a192c3a0003579ce7510b312666ec38c6a8a4226de6615c831100018facab8cc7900037614373485100047e432eb98a4200cbc7458d529083f9bcc7b9a842107737e1d630c8200bdf4402a598e4000abd841c1610c8418faa6bb4a72104f371d363cc5210065e3b6e890e6000a7d8598b41840019b8ec39a42a00d23fa1a72d05310065eba8c998a4200a7d8598b418c0271fb033b086908029f61662106300066ec22ed1906200b9d849c363484018faeab18851080357cc97510b31005dcc00e89088000c3d655d263c8001978c9b8aa6908031f5d97510a3138f3d406cb1922000b3e8494732940919bd0c39a43280030f5d6640c8210063e42cec19220008fe86dcd41484018f8cb390c68800397d9773485400053ec3eca19220008ff87594424c40197cc7ba2a421003b5a0d610c44022ecec20e690e8028e7b21dd56010401a7c84ba864208023f21d53d852011ee690ae61086026cf6215d82110001cf700b2e6390002bd6074358650006ceba4a610a60008fd861c943c4001978ed3a262a00029f61664c851007ece39a86b088444e9d74d8f32500019daca39262100026fe1d52d0d40006ba98aea2106200c7f655ca31500011ff0cb968218002bb209644ca500063f31aebb064200cdc7358521100019d90cb9062a00023fe1d43d85500065fb2ee890a6000cde7458e53084015bd012a2c6108031fd957118d400073710aca90e6000cdc73585219406597e86392c22180337d97734854000566412c69908000ced751883250401d3cc9b9a42180023fa1c644c7200865eb8ac821ca2008fd87d9443c84011ff0ea1ec4a895b9798d5354a420059ec28e9196800097f855c34388401a7aeba1842a00033bcca721915300
  | 15 => 0x7b2a42a00632fd8e74cc9410047ec36e498c6000cde641cd21940015bb032a6c69091b7360873486400053ec28c89964000e795254d60084011ff0cb968718002b7e0175d8d21006cfb9a8290a8000eb985909601044dd6ae8b0862200a3d50c7654c5100065eb2ae818e403bcdc635c23248401cd8ca31642880027ee017550d2100756326c4212622bcbf73dc5640c0019b906b8cc51804f3798373486300065f39ae7b224200add849d86348401b72e0380c890a17b3881630cb200047e432ea98a4200e9e831906348401cf30a194c1288032fd917194d2109f6639cc49086000ced861c9438840157b093aac21900337dcc325844007f57a1cc4210626dd3875909404400157f08a9ac2210038f5d46418d210047e43a65b0a8000c3d769d442904019dcc8b90632803f9b4c965108320047f43886b0ca400add859c96308401aeaa5b8aa7188833718e72d0d210063f398ca3128016afa8018b604c4019f4ec30486a90cb2fd0c72586430065f322e32164000a7d851c96110c259ba61bb2421800337d8d7090d211074e31a872124213cdc83dd921cc0018fecab98c4a0003371d953485300065fb18e890c2032cde635cc2194001ba906b8884988023f60676cc940006daa8ae831a2011d5e851cd21440018fecab90c6a00033759773486302266f39ec790a8056f543154d524c4899b8e6b22429809b73c8573084400047f43886b142000e3d4259541cc0a9a7f08ba8849894b57d4973949310047ec08e4b24a6008fd87944624c001d6cc990a42180bf5e1d73250210006b7392a420ca000add801d3634844f7a90299263a004f37d93734873000636bacc42106200c7d755c6628c0011fb03394c929913371cd64486300047ec3cc418e8000ccd73188214c0015bd01baec6908033b596720c4400047ec3eca18e4010af98110e60084011fb0f21ac3900035b614724c5210073cc2864b04a20fe9c6350c4248489f1865a1a64a0003ada0743586420055ec0ec9a1aa400c7d7519032440019bcedb1e869080367dcf414874000676b2ce418e4043cdd861cd21100011fd0fb1a42880023f61c640c7200065f320e4a0e6275e7a80d96424400199ec6b9062a003b3e981708ca210063fbb2ca18e40009f581dd4424c4017cb033846490803bc5873150040004dfc3c65a0e8000c7e7159663108011fb033b686a910fa75d163cc8400067c282ed18e4000cdf764c93110001978e8312a2a08033b5d762989310057741486b108200cee64dc931080018becbb9a42880031fa157610831004bfc3aa521aa244dcd821cd21500013790ea1aa5a0803379da7418d210047ec30e498c6000ade86d0d434840197ac739683a000337e0c7648530005dbc0a8698a8000e6d53189524c4271fb0d3948710803ab15374988310066ab1ee2a984200da
  | 16 => 0x2181310066eb20e690c200097f855c342cc4015dd05b1ec4880029f61442584320056e412c6188800097f855c3438c401b3ca8b9842a00039bccb658c9100065fb2ae810a6027dad415c831d00011fd0db9a42a0003a7e036418d210072eb1aa4a98820097d87944439404b97a81b9ac22012b3718f735512144f3c402cb21e4000fb11054743500199ee20bb065080032f59574186320075bba2c29086000a7f855c36350431d3d0831a8290803671cd41487400065e380c8a9a4200c7e76197324400197cecb98c8908032f5837454a320066ec24ed9926200cbf845c6620c00197e643a2c6880038f2116590831004be43acaa926200c5d75d8c324840167b0a39ec8908033b191720c7200063fb2ee6a1220008ff8759632440895b906a8ec6a0003371cf61485400055f43664a0a804cd5e7354e425442bb5e87390879088b3ddc961484300047ec08e4b246000e9f641c36348401cf301b2e648804f798c97110d210065ebacc91904200d3d7550c21d00019bee031aa2908033759773487300047ec3cc418c80008fd8718a314c031da8c6a0a6290802afa0a76d0d410047f43ec6a0a2000aec8258521cc0011fd0f3126220002cf614420c74023e6e39aca90a6000dcf639ca43484019d8ed292829000337e0d71189530065f3b68610a8000cdc545da320c40197ac8b88852828b9ea1443181520074fb9a86b08844badd8795063484015bb03386c6908033b1cc62549410063eb2ae610e403bcde735c262cc4011ff0eb2c84988038f21165108310065e3b28698a8000b9d8310b315000197ce632484880031f1db654c5400066e39ac290c8000abd83d9042484011fb02392c720002e760e424c74013e6eb0ae610e8020eaf43dd1620c4213ef0cb8887108031f58d75193211157d40464b044200af5810c961080019beeca9a439800337dd3634c521006773a6c531262009bd8794743500011f90ea92c3980023f21d644ca50006aea92e72926200cee625c2420c4699bcc6b9c43900033d5d921084302466ec30e690ca000f4e85189324c42397ec6ba0c6880033719676cc931004dec3e872928284e7a5114161c8001daee6b0a4220003375ce5398b410057ac0887b0a8400cbf84dd9210c00137d0fa1a42a00031f5957190b300073ab2e4290e6000ccd635c8311000197ce1324a4108032f61f6499131006afc2ee690ca026ee77258521100018feed32a63900031fdd165c87300065f3b0c7a128200cde845da320c4015bd09b82c6108039e54953580410065f422ed99080108fe86dd1324c4199f30c382a419083abd0e62908310065e3a6c8b126200b3c8454b31940015eb02192c3a009bb99c9610c4404c71faa6cb9928256d6d539ca43548011fd0e312c09880337d5276cc9310061ebaac82106217ef24058731100018f8e
  | 17 => 0x142000ebb4310a6008443de0a0b0842100034f6147250f400057ac0884b086000d9e845cc2150025d6a80b0a4220123731ce32486500065fc3ac998c40008ff815d8420c01d9be61b9ac40800337ddb324c4400065eba0c998a4200cdf635c0434840137f06b8885a003a3f21d64582321066e31ae72122000af7815d1618c8018faed3a885988037a9c86090d52006f2b0ae41888000cbc8759331880015bd00320c690802976147258c2100576412c9b126247cde73d8e42540019becbb9a42880c3b318e748c92100736baec42126200c7d755c062504279bce7b1ec0908027b2097110d520067d312e02086000e5c319d4624c4011ff0cb9082180033759673087400047f43c64b0e8013cdc83dd9210c001c7908b2884108023f61a72d0e510066eb28e690a2000d5e735d442cc535af6a6382a5a08033b1da32485400063f428eca92620e9f986dcd20840011fd0fb2263900039e61443181520055fc1ac82102000cf964dc1528c8019bb0fb1c86908037a9cb6090d52095dd406e890a8000cde74d8c324840197aeb32064108029f61770d85430065e380c8a8a4200c7e7159632c803b9dd0f31265180032f18c74549410065fa18e4b0e80129f5819cb634400157b0eb188520803ab2096310a4108edc982e99922000cbf65dd1604c4019dacab9063200032f21171988400066fba6c6a8a42008fd86dc931100019d907bb284210031f9cd650c7200056e412c71888018e5d8518d4148401cba65b2a6288003370c07648530006b7392a521aa200c7e755c46250c01d98c7b10648804eb7a0c54586320053ec28e4b188400abf835904288001c7ceb32042180035d9d57110a310055ec18a8b0c8400dd5735c4424c4014fb0eb2843980026f21d43c87400066fb9864b084000cbf845c66210c013bf0ea9843980032f9d86450d2110e7db0ae01086000a7f855c363484211ff0cb8887210029f614644c7211e66f39ac7a0c4000c7d75d0c624c4014fb0bb22659012ab7e1d5418d2100757aa0c59928200e7b750c96010401cf265baac020803a7d9270d8d210947ec3ec7b02424ccdc73595414c4014f90ab82c2190032f5957498f200063ebaae2312a600b5d839473294001cbecb99262a004776600734851021e6f39ac79088000e9e841c163084015eb02282c3190033d9cd61884400073c310cb1022017cbd405db311000197eebb2262908026fa1f43c87400055ec1ea8b0c8413cde86dcd2108001d3ae8326c690802bbe0964d8131004bec3ca3994a0008fc865ce54484577af02b2664988023f21d52587400047ec3e873146000edb32580604c4019b8c839a439015b3718f7354941004de43a64a0e8000cbd7654e42104011fb0faa2c21900337d9373485500065fbb6e890a6000a7d8599032440011fb03396c6aa08eb72193
  | 18 => 0x8bf2862a1a63a0002f6e0d21d02401247f436e6a0a2032ade83150624c481ed0a0a9663900036755373487400065eba0e8b086400c5d65dcd21c80659becab9842180029fe1564485300866fc3ac72184200c7f655cc62440018baebb1864a0802bea0e42582510047ec3ecb1968200c7e655c632c80011f90ea9ac3a000337ddb73486300063f30aea2166400cde849d8634840187aecba885208032f9d3621813109f72992c29086000cbf845c46250c0167d0928c652803bb69ce32982510047ec3e86312a200ade849c16308401d6cc990c421800337cc173189511966e398c4a8a6200df3505c4324402f97ec2ba0c0988032f5cd71191520065f3b08598a8000e9d80d9063484019f4e6b80c4880039b194620c910006773b0851924200cdd7310e62840011ff0ea16c2a8113731ce32485400047ec3cc83026200cdf63dc153484adcbcc6a92a620917379ce64086300ae3eb1aea31e4200cdd75d8d41484019b8edb9a43200033718d70109210047f430e8a9262008fd87192324c04dceceab0862200032fe117118954004df43ca6a0e8000cf9631c152108019baca39a43200031f58575193210965fa06ec9088000e5f73d9521440018f8cab8c6488002afa107058e210066e184ec10a60008fd8794e62d00019db0e314429800337d9073487200057ac08e7b0a8000cbd87d9131484019ef0cb888518802af60c64909210063f32ee6b0e4013cde63dcd21100018faa5b8ac7280032f9c0648c92100676b12e0210626ddb8759094044001978863b286a907f1fdcd65508320071ea16caa0a2000cdd86dcd21cc00177104a1a80880033ba1c624851042de7400849906433cde7358c42080011fb0c3928718803375ce5318910006eb39ce221262008fe8790961cc0011fb02392c72a0036e20d74881100066ebb2e91906245cdd861cd21d00018fceca9e86a905abea007258730006e7438c49926200abd81191424c0011fb03394c898002b721d5458c210066fb1ae221a4200d9d730cb415001f97ceca1c8499003375cc62d05310066f3b2e031a4200dcd728c83110001db301b18c0908033b5d662108311965eb9ac81086000dd5611cd2110001c7b09b2a86880033d9c9618c6300055fc1ae232242009be87cc941d00015b908b86c690802afa13634872009e6e186ec90e60008fd87d9732d00019bce0b1c86108aebde0574586530047ec0ce4322a600d9c84dcd21500013df0cb906390002afe0576d0e420071e422cb2104232cde7318b414c4014fb0b322648800367dd3734874008e6e39ac290c6000af58198a61d0c0176f0299682a0002afa1365d91310074e326c721a4200bb98310940840015b90ca188690802f6e0d21d01400057741487b122000cdf8758c32c8001a7e80ba8c4a18032fa0e76d09410063eba8873
  | 19 => 0x26fa1e4248740006cfb9c8490e8000d6e549c83194061d5a65b92c818003371d873484400063ebb4a1214a21dcbf405db3210001bac2039a42880cb3798d73087400066eb98c6312806bcdc631d153484019bae0b1ca4108e7371ce624863009e6e31ae518a8000c7d74d96324404b9f0a0bb46210003379937348730134f643a649088000ce8621c1524c4015d904b2e64a080337d4276cc9310073b90eca90a2000cf776c85218c05daf0eb1928108002eba12708c921006bca98e0a926200cdd655cc2108027b9ce719682908023fe1d42587300063f3b0cb98a8000c7c73d9521440019bf0eb1c84108026f61c424c74000677438c4a926200d6e72548319400157f0ab20c8988026f60672d0f400056fc02a9b1a4200cef651c931484bba78a03a2a59885b2f501764c4400bcfdc32e198c2000cdf635c341484653bf0cb9843980033b9c062109310066ebaac721042008fc865cf21500015bf06b266410003671d373485300065fb22e3a1a4200cbe74d9360484019beedb9a432000337a1f63d052100577c12a23126023cf6215d8210c001b3ee621243a0003575d573189310047e432e518a8000e6e85989328c001ceacb90c439824b9799765cc9310047f43c84b0e40008fe869d253484018fecab8c84880031f5d573189410055f43465a0a8000cdc649cc21540019b90b3b664988023f21973485400063fba6cb90a2000c7d7558c42084019bee631242980032f61c640c9210aed7a1ce521e42008fc874c961940013790ea1aa42109b37d85730844000676b90e4b088600cbd645c743840012f90ea926328002afa1c5458442005ddc1a82a022000cbd751913148431d38c7a1a82908035bcc975108210066f3b68721a4200afa82d0e60944011fb0fb2e65a08032fd8d71109400063fc3aea3126200bb581d0e31d0001d3ec621062a00023f21972cc5401d66e318e898a4200e9e74d9363484019baebb82c61084f3720d7198a530067d3b6c1a1aa400ee85018921440014fb0a32665900023fe1972cc4400056f406e9b1a4200abd84ccb6154099d3886b2a87188026f61f4388540005f4402a42146400abe87991210c00157d08282c31900376d4273084200ae3fb0aea31a4200cbd765c743908879be64bb662200036795273087401a47fc3ac62144200cbf761d121100019e8e6b0a422004f371cf63505210047fc3acb21e4213d6e325d46348401cec62b2863900036ed437448510006cfb9cc6a108400ddb509cc21c8001d3d00326c6908032fa1c640c9210074fc3ec9b1a4213ade83141618c80197ced21662a00023fe1d6310a510074e326c621a4200cdf65dcd21840019ee63bb263100031fdd432580410d5dc402a899280008fd8794d61c80019bf013b664988032f5d973908410072fb28c698a2000cdc865cc21d
  | 20 => 0x7d41885304a200af58198e61108018faecba885988023f21d53584420c65eb9ae332664009f78748421cc00187aea320c6908039e603658c910006f9c02e21922000abc82590644c40157d0c19682a00832f5ce6490b320863fb8aca2184200d77655c432440015790ca1e82908023fe1d43d8910006da2a2e2212620fcde635cc428800197f0eb226310002bba0254588310066fc32e610c8018cbf439db3250453b98e719243080033720d71189300d74ea02c69908000cec70189324c40137b0f28884a00033bd967290d210073d996eab008200e5f32d9531440011fb0c3a2a71080327593734843000737992cb1964048d6d539c83194001b3ee719283a00027be19720c4200d65ea06ec9908008c7f865d432884015bb0a392c6108031fd4c765493109ee639c64a8a4200e9f64d8f43484011fd0f21ec2900032f60d76908410047fc3ac72104200e6c629415250401b5e64ba4c119002bd6045098b310065e3b68298a8000a7d85d9332c80019b909bb26419003ae15042980310063eb2ee6a164039cde7358e42c801d5f50030ac119123371cf65485300063f31aea2106200af781553614c801cbac6a92a6108038f5d454189410063e3b4a0a928200cdf30dcd61948018f8c2baec0990033be077650842007562a0c42126263d3c545d432d0401cb865b2862a0003a7d8c428c5400ad7bc0ae4b0e60008fe8710d610801f1ff0cb988510002b761371d8d21006f5190e0a9064008fe87151610c80157b0fb2686908032fddb744843000676b94c418e8013dad439c8434840197e86b8cc5a00035d5d57110a310069f322ea2106200d3c845d4420c8019b901bb264190023fa1f4358a51004eec18e4a0e6000a7d859933244001d3ae8320c6908033b1cb32586500055e432a5a0a8013cdf75d8f314842d3f5003b4a8988033d5cd61084200066fb18e498a2000cde7058e5308401d38c7b24869080367dd373484300045f438c8a12607ce7a8510a60944575ef02ba2c2190031f9cf651891000477c3ac43126246dcc738c921900015bd09386c690802bd60772d85300055f418e4b204200d3d525d252d04011fb0e32665900f3b318e708c92121cef43ee69088000cbd8719131484018f8ec32c6488003375da548c83100666318e4a0a4200e7953d0c6054801a7ae8a906328002bd60743d85520065f31ce81084000abc8654f41500011fd0d3b2869085f2fd037158c400066e39cc490e80008fd87d9432d04018faea31062a0002af61050586320055ec00a83128200cdf76cc153d0401b3e80b9843200023fa1a764c540006daba2a39922000add83109610c8475bd01382c6109534fa1474549310065eb2ce9b046400cdd635c432080014fb0a392c6208032fd9170cc5210065e320e4a0aa000ccc7318921440357750121264a00
  | 21 => 0x829ce6494401abeeb992c0988034f211750cb410047f43e86b14a000aec82593604c401d3d07b20c6908035794173085500066f436e690c8000e3d7459431c80019bec6b84a690803379d964cc9310057641286b108245d5e851cd21d0001d6cc89084218003379d97418d210066ebaec61928200c7e615d4428c801b76e721280880031fd9572185400062ebaec62124200e9c80d9363484019bce8ba6c6908031f1d965549310657dc3865304a200d9d73d0c2150001d58a83a4c41880337e1276cc9310b57dc3ac03026223cdf615cc210c001a7ecbba2428800337e0d7198b430066e432e610ca010cef215d8430845397ac73a6650800367dce53507400056e402a8b18421aaf88054963c80019bf06b8cc4200e7731ce32487200057c42065304a200cdf30dcd629449997ec6ba664a8803375d7638c9410065e320e4a1a4215cbd73993210c001aec62ba8841891fb30c9654ca300047f43c64b0ca000d9c731d121cc001add0a3928699003ab9db648c92100756a18c49928000de8621c1524c40157f0ca9e87210033e1907054b310045e43ac89086000d7975d4360c8401d9ee73124398002bde0573586420063eb2ae12184200abc8650c425440197f07bb284210023f61e43d89500056ec1ec890e40008fe8710d62940011fb023b28690003375db324c4400757cc3c6530042008fd861c9548c41f9bce6b1c8421002b760375d8d210055ec24a6b088413ade8319363484012ff0ea9087280032f1937250d300063eb2ae32108413c7f635d463484018fce2ba8c49888bad501618844000737b28c49928000d9c74dcd211013bc7ceb3206528802de60254c865000676392a4b0e8000abd84d8b614c001b5f0939063a0002bbe1d62189310053fc32a4a988200cdf73189514c4019baeab1e86108033758d70d0c210fc7ec36e6a108400ade86d0e434840173b0721662a000337597734844009e3eb0aea31e42009be82dd153d0c01daec7a0a829080337a1b73485100074fc38c831a4200e5d3259531c8001cbccb31a639006337d9773507311966f31ae610e4000adf8359732500013d904b8ca690802b7e0d71189400063eb2ae32106415ece634cb21100015bf02ba6c69088737cc17608630006aebaae031a4200e5e319d4624c40175d05a0e43a0002b7e157058c21006dd180e890860119f4874c52144027b3ce6a1c8490802b760f6418d210072fb286518a80a2e7b5310c60548855e902996c098803979515418d21005d6412e898e8000d9f40dcd21100011fb0fb2c63900032f9d86410d21005dbc0a8610e80008fd8719221c8001c7acb31a84210023f6187250e5100737392ca18e40008ff87594618c82397ec6ba664880032f1917190d52006cec18e8a946400abe869d13150027b3ac9b9a42180039ba146254931005
  | 22 => 0xb8ec8a989ebda0432d81410074fb1e862124200c7d655c043084012fb0f32863900036dcc47454931005afc1aa418ca000af581151610c8219de42bb0871080277e1d64cc9310066f382c721042348fe878c961080011f90eb2a64a0003ec545415011006e6f39ac62102028e7621d9721440015bf00ba6c6908033759073485100066f402ed19062008fd87193325400157d08284c598802af61b43586420047e432e7a0a4200ced7298a61d0c0197ce032064908033799073484201ce6e39ac6b0e40008ff865c043084011fb0d39662200023f61c32584401472a18eca98a2058adf835c46254c0197f08b8cc521803b6a0363181210065e3b6c821a4229ed653d86314c0015dd01ba4c4188026fe0d76d0a420063fc2cec192209ee3c509923294401cf50a192c020802b7e0d64cca5000757194c81944000e5c65d8e3244001978c9b9a82908026f61e42cc540496af39cea312620fcbf731c9640c031d3b0831a82908027d6077510a310047f43e86b142000abd8694c4290401d3ec7a1c849088737cc1760843000677438c49928000e756548421cc0019bec6b84849080337dce73584420065f3b6872124216dd9831c1524c467b98e7192421008fb3c847058c210069f3a2a410ca000c7f72d95434403b77100aa664a004f3720d7198a430055ec08c8a1e4000adf835933284001b3ae8990c0988033e58f7054a420063eb96ca31a2000cdf635c64348401d18c831c64908023fa1c525843207e3eb9aca2106400cee645c83108001978e632282a80032fd9170d8d211a65fb9cc91086000adf815d763484013bb0f19063a00571f5cd65c87300066fb9cc490c8000c7c501d9524c4019dee431262a00032f9d970191212869fc22ea2106200cfb505d8310803b1ff0cb9c85900032f1517610a310076a192c21888010cdd835d843084539b8e6b1a43080031f1ce65584420066ec2ced9926200cdf7358521cc001cdaeab10c4988023f61f32584400047ec3887b12a2008fd871933244001d38c7b2086908039b19462cc9100065e422e33168646cdc7358d21900516e902a9e432808fb90856148430247ab98aa718ca000cec641c931484019db02392c8988023f61c648c9310063e32ce598a2000ade80950634840197ceda1c84988039bd8b65c8510004df43ac6a108400cbe7619243484019f2cab80c3190031f9cd65887200047fc32e620840009f5811c943c400197ac8b9082180032f98f74487201063eb9acb21660008fe8710d62944019becab9843a0002b7e0554d8d210066fbaae1b1a4233dae329d332080019bf0eb1865a08e73761873487200069e422ea212620097d859ca604c401b3ee839a42980023f61f65087400063fb2ae790a8000cbc7619143548019bf0eb1ca4108023f61c620c5500057bc0aa6b0e8400abe
  | 23 => 0xcc7200066fb2ce6108800fced321c96494c015f505b9ac020802af21d64484300053ec2cc598c2000b6f8254e329402b9bcc7b9e430803337e1d63cc8400063ebae863128623af787586210c001978a8bb665a080337dd36354d2113e76b0ae418e8000cdd64dcd21940015eb03a1ac2100036bd0e72d07211974f39cc81086057cdc63dd531484017b10690a80200023f61c640c9100af6731c6590c2000cbc7655131500015bb033a6c6908023fe0576d0830006bcb28e0a966200dae545c83150041d5e87ba4c4188032fdd874487300064f322e610860009ec825c4434844db9e62b90622000337e0d7198a53005afc1aa518ca000c7e76d9632440019bac9b9a439814b97195324c5404073c402cb98e4000adf835912144001d3ac9b9a42180023f61c5018931006cfba0e69088000cdc641cd21440011fd0fa1ec2a10029f6147258f10006b7992ea2146400abf84595214c0019bf0cb988419117679cf4308740007a610aea31a4200c7d7659732c8001978edb2286908025fe1d53909510061fbb2caa188400af9801d16194c0197ceda1c62a00031f59472507300063e39aca90e4000e9f309925308401cbaa5b1864a884f3798f73484200c66e39ec6a928200a3d851c9640c523c78a8b2c8418893ad501610c4400066fbb0e690a60008ff815d843880698fee6b2c43980032f5c164948210065eb06e8a966200e7a30d9463440018faa5b9ac9280023fe1d5398b4007e6f31ae6214a045cde63dc1430840157f06b20841083b6e841749823209e6e41ae3310605ad3f845d4428c40157b0da1c84108032fd9171d0d520067b98aed18880008ff8759332440831fd0e32262880032f61b7454b3109f6a39ac29086000c7d655c642c80019bccb3b66498802af21172584300047f43eca9968000cdc7058d430844f9e8e332264880032f90c7650d214871e2a2ca2106200e3d7519032484018fce7b2a42a00023fa1e4358b100074faa6c7a0a4200add8795363484019bac6b8865900033ed9370549311165fa02ed1088000cbc845c46250c01978edba243a00373de19710cb100066fb9864b0e40238fc865c3434c4019baec984a7a08026f6047250f400065ec2ceda12821dbba8090b325000197cec21062a0002b760c6418d210065ec22ec1086013cbf439d84348423dae64b0a631800277e0d71908320075cc20e6b008200af581188614c137cbea5b1864a884ebd606725865300576c06e93106200ade809d363484018db0a392c89884a3f61c32d81210065e3b0e890a6000a7d85185608c80157b0da188410802b7e1170d8d21004de412e7a0e8000c7d75194624c4019db0c39263100cb979cd65087300047ec3c85b0aa013dad439ca4348401d70e7212c020803371cd61487400065ec30e8a906400e9c8019363484018faa4
  | 24 => 0x4a000a79850c960084275bb0fb1c86908032fdd87448740006673b6c71924200ade83dcb6150001d3b07b20c6908031f5d664087300055f43687a0a420097d851c94348401b3f09b9a42a01bf978c7650c91000576c16863128600a7d8598b31900011ff0eb1c85288023fa1c3258650006b6bac842166400afb850c960104016f3012a2652804b2f5ca6488430006b6c28e4b226200cbc76109315000157f02b2686100029f616648c910005f8c0864a022000e3c419d46250401a7ac8ba88418802b76025498c210074e326e1b1a4200cbe635d021c80bbc78ca21662a00023fa1f43d8552004eec18e8a906413cbf439da43484019bae8318c0908031759573087300055ec3e873168200cbe845d8210c0018fecbb8a64a00033ddc66158232006f8402e219220008fd87d51618c8019bee621ac21000277e1d4310d2100766318c41922000ecc638c860484015bd0f2a2c610802af2195210940006da322e221a428ed3e511d12194001c7a84b2ac221002b760e42584320069eba88410e8000cbc8759131880015dd01ba2c4188032f102760c5400055e432a62128000cbf405c66295001c7ec8a9aa290802bd60673586420057cc0084b0c6000dda401cd21100015bd09b86c6908032f1da54485400065e322e32126200d9d409cc21100279b8c6b8c64880036b9c952d0d40004fcc00ed2a26200cdd87d8c32544011f90eb2243280033558f7150c210056ec18a4b086429bd883485308400173d093846499002af20964d0e5137f2e18eca1922000abd83d5062504015df04b20c8988025f6147250d310063fb1aea3126200a7e861952150001adc42ba8c990803574c97510931005dcc00e63224200d77315d4624c401d3b06326c69084f3720d7198b30004f6c36e498840008fe869d04348427abccbb9a4398002afe1943584420053f430ca98a80008fe870c961d00016f3012a065280023f21973949410047f438c89922000c7f7659532c80015eb02280c4988a38e507755804100737104ea3128200cdd86dcd21540751ff0eb1c84208032fd9173109210062fb2ae610a80008fe861d232484859bf0cb9842180038f5915254c210072fb2ec69928000d3e7454c21940013f50f19281080029f6177058e420071f20acaa0e6013cdc63dcd21540018fcecba884908032f10c7650d21006ceb9a8610e8000afa878c960084015bb03b1e64a0003a7dc36418d210863eb8aca218421de9d4058f32100011fb0e32464908031fd9573185400065e326e2a1a4200cf673585211000137b0e21062a00031f1957118d400667d302e01904232d9e645cc210c0019dd0d396869904a3f61e32d81210065eb22e62142013d5d65dcd21cc0015bf06b8cc4200032f5c1640ca510047f434e419220168fd87d93604c401adcc4ba884188031f5d965
  | 25 => 0x4018fecab8ec6a0003ec50521501101473a10eca90a2000f8c424c832d00011ff0eb2e86908033e18f7054941226cf424e610a80009dd8794c214c001978e9b22639089f37d867308740006bc382a6a928200cdd86dcd21d00019bac839a42100032f1da424c54009fa6c28c71924200c3c659cb4150001978e8b22c119003375977348540006ceb9c65a0a8000c7c7619531500018f8ca39262880823f2197390921006ceba66430262138fd819da53484319b8c7b9a82a81276bd0e7290e520065e3b0e890a8000c7c659cb634401f9b8c63a464908036edc270d9121004dfc0ae72128000cbe7650c424c4018facbb9a84210032f90e76d0d520057bc0a65b0262009fa870c940840011f90ea1ec290002be60443181522465eb1ce9994a000db4545c642c84278fae4b2c43980033b9d95290d200065eb22e22166200ade86cca604c42197b08bb0861084abea0364d81210047fc3ac6214a044ced329d83250001b38633a0c0988032f1917190d50006eda80e690a2000abe86d0e42544015790ca1884908023fe1d52d8d400055f436863128200d9f7454d214c00137d0e21264a012f3798f7550c210075bc0a86b088400a79850c96010401b3ee9992c0988033e99070548320073dbac64b008200aec8250f624404d5e902992c220002af2194390921006ce3a2a690e6000cbd74192324c801cdb0b31265180036795073485400047ec0ce43226000e9e8399032944018fecab9c84880032f18074581310072eba8c6212424dd7752dc553c84012ff0ab80c8988031f98d75193210063e39acab088400cbc74585219400197aeca1885288033d993714c9100967b882e331460009ed87c8343948013f10e98a8108003671d37348630004bec28ec2126200b3d8510931500013bd0f9926328003a758d53908410063e32ae63128013cde73d8f41484019dd06392c8988cb37dd56310c210074ec1cc8194a200dbb431c152d040167b0a21643a000397cc9654c720005f8c08652022000abd81dcd64880013dd053a262908023f61c505843200676c38c59928200c3d65dd121cc001b70a03a24308003379c1631082100766318c49928000cee70d88424c401b3c81b9a42a00032fdd9635084221e6f398c810a6000eb621990210c001978e732283900023fe19728c6300065fba6c690aa000c7d625d4624c4015db0c2126410002a7a107058c212f71e32c8598a8000cbc409da3250001a7aeb21043a00d23fa1e624c6100047e43ac69088000c7e635d4428840197b083b262a00031fd817518941217e818ee098a2000be48250521440015bb003a2c610803b520d61cc4400047f43ca7b0a8400e6f65d8832440275bd07292c319003379d06318121004bec28e4b1e8223cbd619d0210c001cdaeab10841884a3f61e32587200071eb24a899
  | 26 => 0xb374c37648630006b7428e498a4200db8509d03108001b5ca939063a00029b614745883119f6a188c498a6000bba801cc6448401d72a7212c0208432f5c56410c1000677380c52926200eac74989210c001b5e80b9063200029b61770588312466e39ac690ca023cef215da210c00167b0a21242a000277a1f324c6400069ec28e4a0e8000dac7210931d00112ff0ea9465280027be1d4210b310057cc0464b084000d6e215d463c84019d8e5b12c0988031fdd95254e410067dbb264a00800cbf28094432440195f100a90c49804f371cf63545210066e320e690c20008fd87190214c001dd6a031642880035d197714c9100063f286e6b14a820dcc309cb434c8011ff0cb8ca8190039b5d7620c910005d641286996800fcdf305da53108018faecb2c4390003671d073485400072fc2ae1b1a4226cdd619cc21100015bd01baac6108031fd9472505100055f420a03126200cde7418f60484011fd0f322439800277a1f324c5400066eb2ae61086000c7d75190324840197eca3a2c098803a7d5063505210cfb8284a21922000add80dd363484019bb0db9a421804eb7a0e54d8d211473cc06cb98a2000deb509c831c804d9dec2b90622004fb98c961484300056f406e3b1a4200c7c635d4424840197f0ea1ac221002b76027458c21005cec1e8298e8000af78154c624c535af4ca382a5a0802af6107058e2115e6e192e7322620097c8754d2194023bca64b8864881e3dc1425150d1008d6e41aa9b1a2011cde73d8f624401f97ae6b208418002bde0532584400066ec04ed99262238fc865c2324c4579bb0e31e82908433d9857110e422f69faa2eb216621fcde63dcd42c80011fd0db8262908036e50f7054941005774346590a2000aec8259132440019f2ed39e41100036d9457418d1047eea18ee0a9a6242dcd215cc21cc0959b8c6baa86908032fd5276cc94109d6f418a4b0c6400ced7218b31500014ff0eb2843980031fdd3654c51000736c2ee0b106256cde73596428c8015dd003a2c4188038f21165108320047fc3acb9928200cdf641cd210800173f06a0e63a004abd21941485100055fc3286214a200abe849ce62840019bec9b9a42980026fe1d4394b410065e3b2e898e8032ade83140624c491abb0a39a43280031f5cf65c85100c71ea1acaa0e60009ec825c65448401cb8c632864880030f5d564192320047f430e4aa26200e5e6359731c80018f4ec32c40880f23fa1e32580210ae6e31ae790a8000d5e54dcd2194001d38a8b1884108039d88565087300047ec38c918aa014af7815c9610c0015ef02992c3280038f94c6454d2109cf6c3c85192420ccbe629d2608c83597ac73a4c1190023fa1f63549410063e3b6cb9928000c7e7619432440015e302192c010802af21153586420063f39eca90a2042ecd21dc16308
  | 27 => 0xac0ca8b086400af581d0d618801d9f4c0b8465188033d44171189530065faa0ec9928200abe849c363484239b8e7b1a84880023f61e628c6300047f438c898aa0139f5819cb644c4018fecb390c6880026fa1f4354a422665eb1ae9992a2169fa801d8424c4fdcf6a0b2a63900032fdd16354842004de43aa4a0e8000cdf639c843484019baecbac64188023f61c640855019e76990e4b008600cbf7458d21c800169b0a21264190af975d5630cb410067b988eca126200cbd645c74308001b3ce9994c1190032f153764cb410965ea02e33108000d5f325d4424c40197aeab20c9190033b5c862185430053fc2ae0b0c6400c7d75d8c6250401abceb39884988023f61a7210c101de6f31ae119042009bf815cc42d00011fd0dbaa62908023f61c54584320b5f4402a498e4000b798095332940019e907bb2822095b750c5758c931007d8884a3a1a8021cbd405d82110001cf30a194c0208afb318e32d052100676324e418aa013cdc73dd9210c0018facab8484108039e5485018910006ce3a0e690c8000d75759c4424c4019becab9842a000337dcf61485500067db26e0a946400c7f74d9532440279bec1b9a42980038f5d36518d100047ec34e5a1c2020c7d73596420c8355f501196c099003b318c72505210063fb2ae231280008fe86dcd42440018fecab8e64a0002afa1d64484300074eb9ac72108222cbe71990210c001b590939063a00026f60f74548420066fbaec7a0a4200df0505c4324402b8fac6ba8659089f3799173084400065f204ed9928000e7b8059531c80015bb07b2865a08031fdd764581310066ec36e690ca000af5811d36154c479da42bb04218002b7e0d6590d21006f5a84e418840008fc8750961cc001b5ec939086908033b9cb62d81310057cc00c83026200aee82d9132544016f100a92a7188831fdcd6590b300047ec0cec21a840097f855c343c84419bcc6b9c84210033759573087300066e41ae23128000e3d65d0c42084219bee2b18861080277e1d320cb400d57d406c9b026400dd8509cc21c80319b8c6b8e869080397995634c7200047f436eba1a4200aec8258521d00451fd0f31242180036b1cb3250540004fdc0ae02146000bb58110931d000197e81b9ac32a0031f54b71592500063ea92e7b22a200d5f7354d2194001baee6a8a428800367dd073486300076cc00c7b0242008fc87595325052baf6a6382a5988023fa1c5458f21004bfc32ea2106200cbd7419363484211f90cb8886a10038f21165908320066fb84e1b1a4244d5d851cd21500011fb0f21ec2a80032f9cd6410a200065eb9ae3b224200abe8494d61908273db0e21464908a7979d5630ca10226cf420e690a800097f8754c42940514fd0c32a62880038f6136590910006dda82e818e4000adc845d56308401978e1322a61084
  | 28 => 0x3d9121c8001d98c499662a00032e59170104300d47ec3ec9b026400aec825d1610c8011f90eb2a8598803a715063d05210072fb2c6518a8000ee782585210c0011ff0ea1ac221002bde0543584420057d400e6b088400d6f215d7604c8019b861b9ac5880032e59170084300071eb2ee890e60008fe87cc961940019b8a13b664988423f21d644c6301ce6e39ec690e4000aba8690940440015b90f2a2c610802b7e0d6510d210065fc20ec90a8000e795314062440012ff0ab86c4988cb2fdce640843000676c38c510a8000bb581d0d31500479bcc0b9843180032f1db43c8540006afb2ee690a8000af7814c961900211fd0dba2a6988a76e8c274cca100067cb1ae0214200fcbd435d8420c401b68a8b888518803970c9658c7201453f430ca90a2029cde7358f428400197ce9310632800337dce624844000677b2ae418e8000add841c3634842d1fb0fb16c0988023fa1f43584200066f3b4c99926253e5c65cc931500015d900aa2c418883e30cb43909322666f396c7192a244daf435c8315000137b0e21463a000337dcd61484300061fb2ee890a2000add83193324400157f08b96c688002cf614424cb400056ec28e9b1a4200c7e73d9421500ad9bcc7b9aa5210027e21d214c11023ee639c6490aa000cdd655cc218c0011fb033b686a10323fa1b724c5300055e402c83226200cbd855da4210401a7acbb9a84210433d1c4644c9310055fc0ac9a1c4000cbe645c643c80019bac6b8486108039bd8b65cc91009d6f41c84b0c6400af980d8c604840137b0c3a242180032f10e76d0d210047ec3ecba1e4200cbd86dd1524c4019bcecb2e64988efb318d708c92123e6ec30e690aa000adf835c662d0c018fecab8c64a009abda0432584400047ec3ea631262008fc8759543c8401c7ac92a6652800397d97630c9100066ec3ec621a42008ff865c443880255f50129ac390133371cf6350951006b6a9ce5a1aa400abf8458b604c401abeca39a42880031fe197518f210057cc00c83024221af88054c6244001abceab9885988037614273084200057cc2864b008210ecd211d163084011ff0cb868710802be6163258041005bcc04a810ca000cbd65dd121cc001d5b05a18c4a08033ed4276cc91007fc6196862126434c7e7159421cc0015dd0f31243980039719763cc5100045ec30e89086000af78154f6150801978eda1a42a00030f59574087301a7673b0c719242228ff865c432c80011fd0fb2ac49880337e0d7198a300065ea1ae23128000cbc845c66290c01cb864b286390173c7d52544cb310063fb8eca9922077e78101946244001d9ae8b14641880337593734872013ecfa0ae610e8008c7c865d432484019baeca9c859805bae5d16018131006d6392a4a0e8000b3d8510832d00018faeb39cc5080038fd9774485400057
  | 29 => 0x2e64a0002cf61442885400047fc32e61088000bb9811094084099a7aa73a664a8802b76006418d2109e7a98ae33166000af58198e61c8089bb50039a42a00033b18971109310066eb98c630a8000db7645c4424c427de260b0a421811b76a0073486400055f436872124200c7d75994624c401d5e433244218003bc585215004021ee6c10e690880008fe871913148001a7908ba8c9908023fa1f43588100047fc3ac9994a000af7815c961d0c011ff0cb8886100039bd953248540004de43aa6a168200c7c7159532c800197ae832064908023fe1970d0e312b66f31ee6a908400cde7018e42484011f90cb86869085abe20152587300056f426ebb1a4200cf78758421c80019b8ec39a43a0003addd16148440005cec188498a80008be8719143c8001adce4a9686a880337dce43587200063e39ecb90a2000c7d7359721c801f9b8e6b1ac221003bad40620c91000737b28c590a2000cdc7318921500459eee4b0a42200a6bde0570584321963fb9aca10e6000dbb431c152108015bd013a2c6108032f19171909100065f3b6c9a1aa424ef270584311000157b0339ec8a90023f6047650d520062ebaac61904200cdf655ce424c401b5ce929063900023f61c620c54000677382c52106200d3d7510831d00275bd06212c3190029fe15644c9100055e422ca90a6000eaf43188424c4019decbb92c8988038f50f65505100069e422ea2146200dac845c831d0057a7e86ba865a084fab4ca64484300063ebaec831a4200e3d75d0c62504279bec9b9a42180032f1d161486300057c43864b008280d7a85dc152cc401b68633a0c098803b920961484300065ebb2c7a1c8400d9f7350d2150001ada64baec19084abe20154587200055f420e0b0864008fd8710d618800167f08a9aa5a08031f5957390b200071eb22a5a0ca000cee825d831c800197ce9b26c690803aea0364d81210055f424a4b0c8400a7d8519331c800157d0da1884908033b5c8620c54014eaec28e690c2041c7f7359641cc0011fd0c3b08498802bde0532d85400065e3b286a0a4200a7f8558d2144001d6b02322629080337d90734851000676c38c59922000ecf63d893250001cbecbb1e64a00023fa1c61582320057cc0c87b02a400c7c7694143548019bee721ac4208876e59170084300af2fb0aea31a4200c7d765d442cc80157f0eb1c8420802b72015418d210063e39ecaa0a2000d9c7494d214c0011fd0fb1a82900033b0ca768c91000636ba8c42126200d5e501cd21540018fac0ba8c7908023fe1d6590d210076bc1ac39888000cbe74d9063484019b8e9b1aa290802b76027618d210074fb24e031a4200aec82590644c4015bb073206528803ae60e425804100577410a0b1e42008fd87ccb615408797b08bb66420002af61252584420055ec00a8b0c8413ade8
  | 30 => 0x873000637b2ae418a8000e1d75190634840175d0538e87210031f5d57398a10004dec3ca32168000eeb5098921840659bcc6b9842200038e1d642580410057cc00c4302629ce5f52d8e32544019e8c9b8a6498803575d673109310065e200ec98a8029adf8758c32840013f10e90a80880fbda141524c7200047ec3ca23128000d3d719d4429040197ee6392c8080035b5d462109310047ec3cc518c80008fd86dd4428c4011f90cb868699113671cf434854011ee790ae61086013aed868c921080019f4edb0286a90032f9c2648c8210057ac08c430a8628e7b31dd560104011d904bb262200023f61a72950310066eb1ae02184200c7e76d973250095d98c6aa464908031f615760c7200065e3a4c490c6000c7f74d9632440018fd0abb063900029f61462d0541004fac3ca219220008ff875944348401cbaa5b1c64a880367d0073486400be7cc30e0a966233cbd639d3320800157f06b2084100029f616624c4200059ec2865a0e8000af58110961940195f100a98c4980031f1d8650c9100057ac0ee5b0aa600a7d85d9331c8001cde42b2c4398002eb20943087400066fc32e61088010cbf71590430840197ce9b26c4988ea3f21d644c6100053ec2865b024200c7e765d4420c4019baebb188690802de2016554f210063e3a8c4b026200af985909600c40187aebb2064908033b596720c7400066fc32e610aa000abd83d5161108011ff0cb8465188035b941720c5500066eb2ce610c8000cdc70d8d5348427abe60ba8c6908025fe1570d0d3200677c1eeca108413cbf435c66290c011fd0f31262100032fd017398a540069ebac8418e8000cdf639ca4348401978eda1aa4a0842afa1e6450731006af98aebb026400ecf6418e32484895bd07296c6a00031f9db65cc9100065f992e9b1e4000eaf4318952504014fb0b326628812b3718d75d0d210069e422ea2106200c7c865d432104019bac6b8ca7210026f61f32d074008f2ebaec61922000af581dcf61500019bb03bb286218025fe1570d09310057ac0ee9b0aa600cfb76cc940100015f300212c2100023fe1d43d89500c72f428c6a0a42008fd87190315403b1fd0c39286980037a9cb60d0d520057ac0c64b088013e6d3259521cc0019b8ec31a86908eb3798d7310420006f5390c1a1aa400cde649cc2194073abb0a39a439004abea0242587200074f406c9b1a4200e9c645c363484018faeb32065880035b614724c6200057741086b10204ce5d75d8c325441fd5e863a4c418907371cf74584320074ec00c9b1a4200cde70d8f41484019aae6b084318002bde0542d85300066fb28e690e8046d5d851cd21900018f8e2b2a85980c33798d73d0a100075da1886302a400cbd76d0e4294401af2ea286c1908023f618724c44000576c3ec42126200ade84dd56308401c7ae9b
  | 31 => 0x4200aee82d8521540273e90cb8886908031f9da5090d5200677b94e4b088000c7c655cf21500859f500bb043980e776a0073487200053ec28c430a8600ced75188424c401be662382a49891f371cf6348550005d7416869968000cbf645c443484011fb0e286c790803371da53505300063fb8aca9964000cae641c9318802d5790cba262a0003b918951485100065fbb6e890c6000abf8454963c8001dc8e4b0a62100ef371cf63505200074f422c62104200d7552dc553c84499ece6b0e62200025f6147250e3126e7b316e2a984200ef35058531080278fae6b2a43980033e98d7008420005ec41a42a0220008fe87d9531d004d9e8e6b0c4220002af60c54584420074e426c72124200e6e65189524c4018bacab9843900033e98d701042022ed7a1ce418e80008fc8759543484279be613b4a690803b94c961484400074f43ec831a4226e757558431100019bce9b1c64908038fdd36548510006cf418e8a906400add84dd763484319bca7bb283980cb3718c724c5100065e320e4a0a6200cdc70d8d41484019ee63bb26220002cf61442087400059ec28859968044cdf32dcd644c00197ecbba242880023f60472592500069ebac841968000e9c6418d43484018fecab9a42a00032f5d8748cb400053ec28e4b1c820097d8794432940011f90cb8ca6a1002afa137258e100065e3a6c89926200cbf639cb41500019bac7b82a610802ed60670d91210074f422c72104200e7a20d9462440279b8c9b9a43980033761b73487201a66f31ae7108400ecbf40dda32100435f100a88c48804f979d97518d210047f43ca7b0a4015cbd73593210c00197a80b8ec6aa062f560664cc93107f5da18853006200d5d755cc42cc425de480b0a42200923fa1b73485100062fb28e690a8024cf8505d831080011f90eb2242880037ccc7705493152fb428641a1aa400c7f7654953084275bd07a8ac3190031f9cf65c8540006ceaa2e610e8000d7a605d432104014ff0fb286488117671cd43487400075db26c1a1aa400cdd75d8e43484011ff0eb1884080023fa1e4358a512266ec30e690a80008fd8794662cc001a7aea21065a00039dcc7654c5400047f43ec690e4000cee20dd931c800157b0c3a2421807f3718d748c9210047ec3cc91922000a7d850c960d04011f90eb1a43a004f2f5ce64484300065ebb6862146200cee201c961cc01d9f30c382a51904abd21d61484400066faa2ed1906229dda801cd21840b1cb8ca19462a00039b194624c9400076b192c21888000cde635c042084011fb0fa88c498802b760c54189310063f39acb3088421cf787586210c00197acaba043980039e6144298251006ae192ea2106211dd5811cd2144133e5ea9902a5a089eeda04325074022e6e39ac690e80008fc8758d52d0467abb0a39a421000367dd3734
  | 32 => 0x1978eca1a64a00033d4437158e520074eb9e8631282008ff8759642cc4015bb09b86c690802bb60254988310053e432a6a8a8200cbe439db43484019baeab1c64108027de057390b4107f66318851924200e3e6550d611080157f02b98c89087737dc9634c8400053ec2ee0b184200c7e7359641c80014ff0ab2664880023f61c640c9500071f3acc819020269de839cb31100018fced3a884988023fa1872505300066f382e1b1a4200b3d8510a31500018f8edb2a64a00cf76a0073484200065eb2ce9994201acbf405ce62100455f500192c1108af2fd0d76ccb410074e426c62124200d9d7390821d0001b3ee6b1a84210023fe1d435872010f5d384c81086000dad409c831100018fceb39cc50815b739cd5210a320076631c842124200cde645cc21cc001c7908ba8c4a18034f21175189430057ac0e86b0c8410cdd7158c43084e5cbc63b2c6488003375d5630c821005ec41a432022000bad821c54310801aeaa5b8aa6108023f61f43584200065ea02e2312a8008ff865c0420c4011f70eb00c1192575e9947054b310ae5fa1cec21e4200abd8758e42104019dacb394879080e9fe195254c210063eb1aea2164220e3f43596420c451ceca2b0a63280033bcca768c91019e6f430e69084000af5811cb61500015bf0f2a6c6908023f21974cc52119e6e39ac69084000abd839d864484018faa4b98c4a88032f2127610d2107e5fb98e4b20626bcde631d153084019bae83a6c6908030f5977448720006ceb988410e8000bb58190b21d00019bce0b1ca410802af20964d0e50004eec1ce5a086013cdc64dcd210c0018fecab8c868808ebda044258430004dec18e4a0a8000e3f54951610c8691ff0cb88851910b3b48576087300065eb22e62104020ecc6390a32484015bf06b8cc5180031f59573908420055ec20e0b184200cbe74988604c4014bf0ab86c690802e760c420cb4000737b28c41922017bb88055331500019f2ecb9e4110002cf61473191210066fb26e690c2000cdf635c83150001a7ae928e652809f67506730874000677b2ce4188800feaf431d1620c40167b0a21062a0003a7a1f64d8d210063fb2ae31922072e5c31d963244001cdd0a31664a08023f6047258f4007f1fa1aca2106200a7d851cb6150c0157908b8cc4180823fa187250d3214e6e39ac790c2000abf8458d21440019bae0386c690802afa1a51d0d40005bcc04a9194a000cde70d8f43484011fb033b4a6a100337dce53587200047e432e72122000cef72189314c0019dce0b108418803a7d8f32d05400072eb2ac798e4033cbf639d33208001d5a8631664a08036d15171908210065fb26e0a9a4200d6c325d7604c8011fb0f192c2200031f9db654c9100063ebb4ca98e4000ddb50dcd21840319b8c7b9a82900036bdc8424c74009e6fbaec721a
  | 33 => 0x9b9d5621893100577420e0b10622badf8758c32d0401978eca0a42a00023f60476509300066fb1ae019242a0f705044043944018fcecba885188023f21d65485300967d086ec90c6000e5c6518e32440019d8e0312a498802be60074584320965eb92c91086000cfb709c1610c81fc7e86b2884190023fe1d650c9101473b28ac290ca032d9d645cc210c001b38e9992c0988033b9ca70d8f2100677b28e4b226200a7f8654d52d0401978e9b266290803575cd53106500066fb9ce6b0e4000c9d645cc210c001b58e919242100031f9957198c420063e3b6cb192200097d879d4424c41fb9e6039286990763fa18724c5304b6bba9ee2a966200cee861c9534c801cda42b28439810f731ce32484400047f43e64b088000e3d74d9732440011fd0faa2c790803a7d8c424c9400047ec38a8b0c640097f855c343084018fae9b2e648803abe61e32982510063fb2ae5b1a8000e9e8399232944013f301bb4a919003351cd614844022e6e39cc890a60008fe8790d61c80015eb02318c2a00033721276cc9310066ec3ec62124200dd5755c6328c401d390fb20c6908035b6147250e2109f6631c6490a2016af5819cd6110001cda65b2a428805f3ea187054b310065e380c898a42008fe878c960d0401d5e8631442a00033e98c7054b411147f43864b0442008ff815db428c001978e8b1a43080023fa1f43586500066f306e69088000e2f5418952504011f90ea9ec2a10033720d71189530957d40465b024200ade801d363484011fb0fb2c43a00039e9c16508730006d7b24e521a42008fd8710c62544014db0a3a4c4188031f1c56558c42006e6b946418e8000cdd635c83110001c7f08b2c8598003a7d8e424c9400066eb28e690c20008fd81dd953d08018facab8064108021fe19750c82109d6e41ac890a2000ce572584311000197eedba24320003ab990724c6200065fbaec998a4200d9e54dcd21d00015ef02b9ac2210023fe197310a100061faa0eca928200eb86418143548019dd06392c6880032f1917194d210bf5ba02c39888000d3f405d46250401ad8e4a92632804f379cf6318121247a6192a6994a000d9f73d0521500019bcc9b9a43180039761463181210065f438c898a4200abe84994624c4919bce7b2842980031f61476549410676cb9865304a200e6d85189525040187aeab20641085eeea0242cc5400047f43ec8996401bd78754c940440015f5003a2c2190023fe1d53587200667a882ec1902000aec86508424c4275eb03392c321883ab8ca6490b320075690cc81086027dcf215cc21d00015bb0b382c61080337dcc32587400067cb18e0a968200eeb5018b32440011fb0d39686080033b5cc62885400063e39acaa0e407af7050946434402397ac6ba664880025f61c650c9102be6e39ecaa0a62348fe8718931440
  | 34 => 0xa82ca18e4000eda8018c6048401aece2ba88518a2f8fd516590b300047fc3a65b0aa0008fd87141618c8018fec2ba884990032fdd4644c5210073dc02cb18e4000e7731d9531440015bd06392c2200032f213764843031e9faa2ea1968200aef825cd611004fb5e82b9063a00039e9c1650c7200cebc3a864a022048f543154d31940019bac6b84a61083abe20164582321066f31ae72164000cbe609d3608c8011fd0db9262a0003ab8c8640c9210055ec2ec93246400adc805d363484011ff0cb846410802bba085058632006773b0c91924200cde809db324c4015bf06b88c4a180337cc173d85540069e32ae999220008bf87590648c8015bf00aa2c610917379907348440004efc1ae22106400e6d85189324c4018faeb3206510802ed604428c7400865eb8ac82184200cec20dd931c802d9e8ec98a4288003175d563108210047ec3886b084000cdf76dcd211000197908b8cc5a00037614073485100066fb9cc490e6000abe8494c62504011bf06b88c4a00032f9d364d813200677b94c498c8000e9c649c363484019bac6b8865a084ebd60672587301047e432e72124000db7435c642c84011fb0fb2c63a01339718d53545212247ec3ec63128000eaf43d88424c4879b862bb064200e7371cd63487200066e386c6a8a4200cdc305cc62440271fb0f3144398002eb209438cb400066eb2ae610e4016afa80d93604c4014fb0a392c790002af60343586420065eb22e221460008fc865c6544c80173b0721262a00031f59571108320066f3b0c7a1a4200cf571986608c8018fec4ba8c498873dc142518c9100072fb28e690a80008fd87d9432d000157f0f32042180034f5c57510a4100757ba4c490e6000abf8359042940975bf0f2a0c69095b379cd7598b310073dc02ca18e4000cbe86dd152cc4015bb01b8ec69089b3e60176084400047dc3ac03026200cee7318a52504015bd012a4c6108023f61c4398a10006b7394a121aa427cee645c831100019bacab98422004abd60672584400063ec28eca9a4200cde70d8e3248467d9ca631264980032f1927290d500066e3b0e690c6000c7e76d953250041c7e86b2c841904fb318d32485400066ebacc72104200c6d75d88424c423bcc64b8864880038f9d165087300055fc0ac9a106000c7f7659531c80019beca39a42a008a3fa1e32582210065ab22e21904200cdc64dcd215401d57b0c3a465a0002b760c72584400057cc06c43026200e5c65d8d32500018fce2b2865900023f6047258c402656ec3ec6192a227cef619c831d001f9bcc6b988508002af61b744c4400066ec3ec6a0a4200c7d7510c62504011ff0cbac651884fa71ce64484300066f436e69088011cde73d8e424400175904a0a43a00032f98c74486500074fc38c9b1a4200cf883dd92008001bcf04b888690803
  | 35 => 0x1c363484015eb0221ac2100ef3b5d9708cb210056fc3aa9b1a4200d6d75d88424c401ade42ba865108029f614764cb400c4fac0ce9b126200ee85018b214400197aeab206410803671cf41487401066ec38c72124226ed67358431100019ee20b88c4a98029fa1442586320063e31aea21282009de87cc9315400167b0a21465a00026fe0d71109400056f424ec31a42008ff865c03208401b3b063a2a5988034f5d743189413071e32a64a0a8000cfb50dd932840014ff0ab82c3210031f98d7510a4115e6f31ae7a0c40009ee869c843484018fecb39662880023f61f65909312a69e280e8a926200c7d769d4420c4018ff0cba8659089f3758673087400063fc2eeca988400abd8715262d04015eb0221ac3290031f9d57398a100056f406c9b1a4200cf464dc532440015bf0c984a7a10032f1927290d520047ec38c9192a000c7d75990624c4015bb07b2664a8803379c063109210071eb2e872104200cbd74d83325440157d09384c5988a73761873486100065f3b6c9a1a4200c7d525c462550019aae6b08421011f371cd65486300ec7fc32e610e4000c7f750c9608844b5f100a96c68827fdc1411010a51004f743c64a0a4200abe8694f415000137b0e21663a00032f9db63d0941004de43aa4a1e8000c7d758cb604c801b38e6a0a42a00023f61f43586201e47fc32e02146400cbf645c443548ffcf6a0b2c6390002bba137058831006f4284e418e4065d3f545d632d0421f286232282988030f5d764109210047fc0aed29e8400cdd635c242084015bb032a0c6908030f59574087200065eb26e0a984200c7c505d832944279ec62b8cc521803ad1d161484300063ebb4ca18e4013adc835536348401d3ac7a1c841085b3e61870549310065fba0c8b126200cdd86dcd21080016db0528c65280036dd5171109310047ec38c918a6013add87d8c43484015db01ba2c4188034f505750c84109e6f31ee690c8000abe831c964040015eb02212c21904f7318e7210d21005afc2ae1b1a422be9e8418f41484015f504218c0a903f3718d73109210be5fb0ce83026226af78758621100dbee0a128c84880031f1c565508320066eba8c7a0a4218c7d7359541cc00197ce1320641080337a13764c832075f9404a319220009bc874c941500859bac2b984398002afa1b32d05400063eb2ae730e4000add859d3634840157b0da1c8528802bd60442586300063eb9eca90a2000af980986608c80137f0e99683a000317d9473485100055cc20e6b004200abc845c9618c0015bb0c194622004f37dd3630c9211147f430e4a0a2000cdd87d8d51484018feed2828728802bb61470988310056fc2ae1b1a4200e9d63d0c420844d5ef0eb0862200031f9cf65c85100063eb8acb9964015cbf439da43c84015b900ba2c61085abea0365d81313ef3d
  | 36 => 0x2839004a3f61e6288440006cfba6e690c80329df865cc210c001a7d0a39287a00031f1c56550b20006cf2a4e610a8000d9c74dcd21d00251fb0f314432009b734c5720c44000773b92c29884000cee649c831940d19bcc7b8aa7210cb5759573087300066f326e690e407ee788059531c80019bec6b8864a88033799373484300065f39ae6322a400cbe7019063484011f90cba4a690802cfe1570191210047f43ec6a122000e3d7499663c800197ea8bb085188039e54954580310074e43ec9b1a4200cdf635c432440019eaec88687288023f61e535844209e7b18ae33166000ee78258521100018facab8484190032fdd1614873000576c08c49928015ade83d5163c8401b38e9b9a421803b3e181708c9320065e320e4a0a2000cfa641c152cc4019bec7b8282908023f618724c61000736b28c4a926200abd84d94644c40176b0339ec8908032fa11760c4400057bc0acb90a6019e78750c96094457cbb0a31e8290802cf211528c6500657cc3865304a215cde73d8f41c844b97e80bb46220002b760f51189311e676bb4e11964200cec74189524c4479f2c2b8042180023f6047258343005d7424e11964200cbe74d86608c8011fd0d394868808f3e585701043009d7ac0ce4b0864008fd869cb438c001cbc64b2c6390002bb61474988310063fb82ca2184200e7b7514161c8001ab864ba8851880367dd37348540006cfa02e61088043adf8758f321000197aeab2464108023fa1f645823209ee631ce521a4241cdc63dd1314840197d08bb0422004737a1873485100047ec3e873142032cde635cc21080275eb03392c2219176b50d720c7400074fb18859928000e9c70d9063484011ff0cb8884100039e194628c1100065ec38c998a4200c7c655c76350001bd0a139062100026f61e424c7400066f3b66498a8000d9d54dcd21500191ff0cb80651080337dcc325822109e6f31ae51888000c3f765954210801b5e8639282908032f59171d0e200066fc1ae23128615dce738cb41c848f97ac6ba664a804b2f503764844022ecec24e610e8000c7d7459621cc0018fce6b2843900038f59543584420076a39ac29088000cbf841d943484018faa4b8ec6aa003ab19232181210072fb2ec719220008fd819da424c03daf0eb9928088003975497558c21005dac0e8718a8000ced721c961cc047fa06238262880023fa1a764c9401e66f39ac62144000c7d655c643c80011fb0f21ec4880033ed4176cca100067cb26e0a926224e9f4058c3110001cdeca3166488002bb61a32486100047fc32ea1904200cdd7310c625440197ac8b8885080033b5d4628c9310047f43ecaa126200cbc545da420c4019eaed90c43180031f5da5090e510072f192ca18e40128fd819c8644402197b08bb0872880367dcd53507400063eb2ae31964000e9c64
  | 37 => 0x9310066fb28e690a2000dad545c831d00019dd0e31264980031b5d7620c9411e66f39ce13166200cbc64dc543548ebc7ea9b2c84880772f50176cc8400069f32ee890e6000e9c54d8d4148401cbec7282a6a080337dcc43586520047fc32eb194822be9c63d0f41484012ff0ab8687190031f9d573189410069eb28e8a906400e9d87d906348499da8c6a8a62882438fd5165108310072e32ec79928029cde7358f418400197ecb3a66508003679d153087300055f434a5a0a8026cf47119132440018f8c2ba884990039bc856588720006f9a86e29922000aec8250f62544019bcedb1c869084abea0032d81210875c880e6b202000cbc63dd1215400137b0739683a000337cc173189540047fc0aed29c8400cbd655d332440014ff0ab82c21900337d8c7250d210065e422e33106020cdc635ce42484018facbb8a8598057731ce325472108ef8982e219220008fd869c8438400157b0232286900031f61576108311d67bc32e21948200e6f658c9215002db7420ba0c098802de2015254f210053ec34ca18e4000cdc76d0d4348401a7acbba24398002ede0573908410066fba0c6a8a4200cdd7310c62504019f2c6b8084100033799373486100047f43eca9926200abf815cf6448433cf50a192c1288023f21d32583410072eb1aa6a948400e9d64193324c42b5bd062a6c7908033ba187250d320057cc00c63024200c7d75d0e62840018f8cab88c4a00029fe1570d8d4213ed6a0ce418e8000cec72cc9611001d1f90cb846490802af21153189410065e3a2c690ca013cbf435c66210c01d3ec721664a008a3fa18724c5100055fc32a6214821fc7d7359542cc0018faeba1cc5180d23fa1872505310047fc32eb190422bcbf635d332d04019b8ec39a43200032f9da548c9400057d41487b02a400aee82151610c8019bceca18869095b9718d535494120e6f39ac72948232d5e655cc21cc0578fac6ba865a0802bb20162189310063eb2ae331884008fe8719132544019bec839a42a800337601768c83113d7b40864b0e800f8fc865cc424840137b0e19683a000337a03764c83209f57194c890860009be87cc941500899bce7b18c4a00032fd9574d89300057d43864b0042008ff865c432080019beebb1a82909f3ae15042982510047f43887b0aa400a7d859893184001cd8a0312a498802b761270d8d2100576422c43126200cf8509db3244001f62a2a1a80880029f616624c6300073c402ea3128600aec825d16194c011ff0ea1ec49811f576147348550006dcba6c71022000e9e7419363484018fcc2ba884190023f21d4358652005cec1c841968025e9f4058e31100011fb0e2a0c4988023fe197194c421966e31ae610aa0008fd8798a3194001bb6e799281080031f59773587200065e3a6c6a928200c5e765d46348503ed0a0a9
  | 38 => 0x200c5d651cd21c80019bce1b1886908033b9c362989310074e318c821a4200c7d765d4420c4018fced3a88598803671cf7448430004fbc3a4210a6000c7e7359721c80011f90cba864a08029f6144258632006af192ea2106200cbc849db4348487b9cc6b9062200b39ea1432982510055f41cec3224200a7d851c961cc0015bf00ba2c6108023f6077654e4200677b94e4b0ca600bac825d1315000197ce0324a69096797196328c540006aeb9aa410ca000e3d429956110801b68a8b888590a3f3718f7054d211167743cc490c2000cbf7419331484017b70690a81080031f5d3654c5100063eb0aea2166400e9c7350d61108019bce1b18649090b2f5857408730006b690aea190424cd5e7354f425440197ac8b8884180031f59672907300057d41486b008241c7d7359641cc0019beec982a7a08034f509750cb410056e402eab184200aee82d93624c4019eeec21a42108032f6187454b310066fb1ee098a4200cdd7518d4148401b3ee839a43a00035ee0175189430e73c3ac64b04a200e5c73d952144001d3f09b1c849080337219730855000676b2ce418c8000c7c7159543c80655bd07a88c4988027b2097110e2000636b2ae418e4000cbc7695131500d5b3887b92a6a184abd21d61484300063f32ee2b1e40008fe8710d62040015d904b2a42880032fd007258e540075d400c83024200d3d75190424c40137d0f21242a000337a1676cc9310065eb2ce81884013cde63dcd21440015d904b2662880023f2197494931006ceaa0e690e8000cbe7655332500579bcc6b9e83280026fa1c42487402b78f21aa7a1aa400bb58190821d002d5f501b16c09880337d9473486100066fb2ee69088000a7d85989218c0014fb0a316c09880337dd873486300065eb22e12984200c3d7559042084019bae9b1ec0908027ba087454d2127f2e32c6418a8042bd4814cb604c4017770890a60880023f61e32d81310071eb24a998ca000cdf865cc21c80019beebb1a86908039dcc5654c7200074fc26c62124200c7c655c6325000197acaba04390002f560670d8d210063fb2ae7b122000cbf761d1210c001b3ee721242a00029fe1952550310055ec1ec8212a2008fc865c341484015d904b82c2190a35d1c7654c9100063f38aca18e40009bd8794c42500014fb0a3b263900023fe197110a300be5ea06e2b188000abd8315062504011fb023b264a000367dcf4348740246af39aa620ca000cbd705923294401de6a0b0e43900032fd9474484300072e996ca1922000e9c631924348401d3ce9b20c6908035d5977154f210767d302e11904200a7d8598931900019bee6192c328042bee0443982510063fc32ea1904213e6e3259521cc001c7c84b2a8598003adcc7644c521005ec41a43a028000b798095331940893b906b88c4a0003379d954cc
  | 39 => 0x39ba60bb04218002b7e157458c210065e3b6c9a1a4200c7d525c662940014fb0a312c09884bba14262486100065fba6c290aa000d9d845cc21d00019dcecbac6490802afa1a531094000576412c999220008fd87d9632d00012ff0ea9663280036bd9272d0d520957d404a4b0e4000dcf20dcd210802b5ef02b92c329802b7e015418d210063e38acaa108400d3c845d442c84011fb0e31462a00032f9da540c5400066fb2ee690c8000cbc73d915148401d70c830486a90033b080764c5200074e326c7a1a4200cdf76dcd21cc089abd0a39a42a00033dcc771592320074ec20e0b184220f8f32d0e428c8011fd0d394a898803375c263948212ae9faa2eb2126200add8399032440019baed3a4641880337dd87348640006ce3a0e690a60008fe878c9608c4011fd0e32242a80a39e603654c510005d7416871968000cdc865cc21100019b8c9b9a42980039718f650c9102366f430e690c8020e9e8498e42084019dee5392c2218029f61662486403171e32e64a0a8000d9d831d1524c4017b10690e81200036b5ca420c7400c74e31a86a0a4200aef80551620c40157f08a92c39800367dcd43584420072f2a2a9b1a4200aee8290f625400157b0830ac1190031f5957190c420056ec18a03126200cbf845c6621000197ce7324a4108031fd94724c5100047f43c84b0864008fe8794d61108015f30b21ac0108036dcc574181310063f3b2ea2126400e5c6319731440013bd0f992c098803371db73485300047f43864b004245ecc32991328c0011f90cb9842a00033bdda524c7200065f3a4c330464118fd87d8f62440679b8e63124298002b7a027258c210065f322e32126000eae761923248401978e9b22c098a375794773486500056ec04a9b1a4226cf9805d831100239bce5b1c64880036e1427408420006aeb2ee690e4000c7f659cb6344001de6a0b0c62100cab7a0e5458c210063ebace33146000cf5635c4420840137b063a2a5210023fe1d3258440006cf418e8a946400dad7210831d00019dae631042a00026f61f430874007f4f424c62104200e5d6598d31c80011fb0f21ac2210033b989701083126ebb32ee2a9e4200cfa641c1528c84d9bec3398422000357951730865009f56992c89086000cdd7398e6110801cbd0bb82c6108023fe19710c8400066f3b0c99926200abe84dcb6154c01b58653a4c11904f3718f7348510006b6c28e4a0a4200cbc73191414400137f0ea1843a00023f6187254e310074f400c831a4200c7c7619532440018fcc6ba884108033bdca72584302572ebaaa831a4200dda40dcd2184001dd0a031064880026f60672d0d400072ebaec831a4200a7d850c9600849bce8cb98e428800337a1f63505210047e43a86b0e4000d9e744c8604c401cf44132ac3900031f9db650c9100047fc32eb1908
  | 40 => 0xde1d61084201473cc06ca90a2000a7f8759431c80019beed982a62103f1f54d7694c4251f3da9e86302a413db7435c443484019db06392c8880023fe0576d0c200055ec38c921a4200afa8294d60104019bcedb1886908031f9cd75189310066eb98e6b088000e6d2159421c80279bcc6b8c6590002b7a037458c210047e43ac690c8096d7665dc552cc4015bf02b1e64200036bd01720c4400074fb20c7a1a42008fc87591218c001ab862ba8c4988023f21d4358a310463e43acaa106400d5e325d4428c401a7ccaba043980027de1d21084400055ec0ce6322a418cdc63dcd414400197ac8b9885100031f5d3654c9100063fb2ee498a8000af581141610c8775b906a8ec6900032fd9774589310067cb26e0a9662348ff865ce21c8041cbb0a31c84908033761b73486400075c320c021aa400c7e855d821cc0011fd0f31263200036ddd15148510006ebc1ae22126200c7f865d432904019beedb9a42a00032f59171108320047ec3cc999220008fe87d8d42544018fd0bbb265080032f18d7408550004df43ca6a1682008fd87d8e4244039af0eb19280880034f59574087300a65f394c81086000c7f75189604c4018feed282a72100375d8d7110d2121f4f990c8a1a60008fe87d8d42540012fb0f3a884188033799373485100057ac0864b00420097d851da424c4adcbcc6a92a6108031fd967290d10006dd180e890c2000d9e53dd121cc001ada64ba8c9908033759673084200063e432ea192824ce5c6354d5150401b38e621243a00033b189710c941004df416e2a1e80009dc8754d21cc021bcec4b8886908032f18c744861011e7cc02ec10860009dd878c831500019ee62b88c8980039e1815350d520047bc3ac230c640fe5d8518c42484859bec0b9842980023fe1d64191310057ac0884b084000cdd86dcd2144127af6a6382a498803795d6718cb211065fb9cc92166400d7765dc532440019db02392c6880763fa1e624ca400047ec30e4a988200cdf82dd94310c018faa5b9ac328002afa0e72992510074ec3ec9b1a4200cbd74588604c4014fb0b316628811f37a1873485500047f436e4a9a8641cde7358c429040173b0621465a00023fe19750ca410047e43ac690c2000cbf849da434842f5f100a96c2980026f61e5390b40006cfa04e610c8000af781596618c8018faeb398c4a08025f61472507310066eb9cc730e4042ade871c1630841f9b8c6b9884a08027ea1f32502100067dbb662a008000abd821c5640c00157906b88c890803a7a1270d8d210057ac0ca6b0884008fd8794e62d040197b0fb266290803375cc32d85500073b98ecb18a8000ee63258521100013df0ea1084988033b1837258131006ce39c8490e8000afa8310a600840197ce6b2085289133b4ca76cc9400063fbb2a4a988242ced215da21cc04
  | 41 => 0x2ea3128600abd84dcb6154c019baca39a4220123379cd63d065000577404a93106200cef65dc9604c4018baea31884908033b5ca620c6402be3f42aec194a223cdf865cc21cc00197b0fa18c4a090f5761473484401473b18ecb98a2000d5c65dcd21440018fee8b284398002b761a320c4400065eba2c33046400af58110d6190801d5d0c32464908031f98575108310053ec2cc510c6000cbf645c03248401d3ee0320c6908023f61b73c84400065f3a6c9b026200cdc76dcd21500f9a70ea212810800397d9763cc510006b7428e498c4000cfb64dc1520c801cdec4b2aa498847731ce32485100074e406c831a42008ff865ce41c80999bce6b2c84988036bd507250521134f6c3c6590880008ff815da5310801c78c8a9aa290802af6034318941006af284e610aa000db731dd1524c4ad97e873b486a904f975d7630c9210063f32ae219640008fd8799221cc0014fb0bbb264a00039bd9632485100057ac308690842138fd86dcd21c800117f0eb20421800397ccb650c910004f7c3a41a1ca400cbe631d1529088997e873b062a00033761b73486100071f216caa122000adc805526308401b3ce92984298002bd21932d05410063ec2aec194a200e3c845d462504efcf4a2280c4880031f5cb65d8d1000636baac42106200c7f71d9542440011ff02bb064200033b9c0628c9310065ec1ceda128200cbf73d915148489bb30039a42a000397cc5650c7200056ec2ee9b1a420097d8794632940019e8e4b0a6318003ec44151d05400063f29eeca988426ee5725843110001da8c7a0a82908023fa1c64487200059ec288598e8000cdf7398d611084997e80bb062200027761e320c64009e5eb9ac89086000cbf74d8d21440419b8c7ba4649080397197634c5100066fb9ac29088000abe841cd61080759b8e63a2c2190032f9cd73d91522978faa4a89926215c7e7259421cc001abc62ba8c498803a72006418d21006cfa00e69088000cdf7398d61c80011fd0f992c3a0002af21163485100047f43887b0a8422cbd405da211000197aed39885208033b5ca62104300065eba0c91924223cdd615cc210c0018f8e732ac39012b3798d75d0c210066fb9c86b088400cdf7358521940013790ea1a43a0002afa1f43584422266f31ae1a184200af980186608c80179904b2664988033b595720c4402666f438c6a8a4247cdc73d8d415400197ce6b98c890913a79d363cc9400065fbb6e2a188400cbf329d363c8001978813b664a00632f50e76cc9410056fc02eab184200cdd635c0320840197b0c3a2a4988031f9d865cc94018d6f41ca4b1e2000db454dc532d04019eaec88085288037ad40724c4200065f3b6862124218de5325c432504011fd0e192c2200036dd0d7190821006ec286e690c20009bd811c943500019beedb9a43a008b3
  | 42 => 0xc8315001f9b8e6b1aa421002e7e0d414c7400055f420a0b086400ade86cc9604c4019bb093b0c6908038f54b54586420047e43a64b0e8000b9d849c2328c42bada64ba8c7908032fa1f64cc52100666b18e4a184200c7c76d9731500019bae6318c0908023f61c4398a500047ec3cc81922000cdf639cb43484011fb0f298c488002bd60450d8f210a65fa06ed908801d8fe8798932100014ff0ab266288002b7a027618d210047ec38a9b1e4200ecf73989210c001978ec322869083376a0c70548320056f43664302620fe9e8418c4248401b6e86b8884988031fdc565508320063eb2ee0a106400ced659cb438c801d3ec6a1c84908832f9d9431093219766218c4992621dcdf8758c32840014fb0b3144320003bad437098831006d7994e93046427dcf315c831d00014fb0a32263900033718d70909210067d320e0a926216cfa861c1524c4019bce131c84108031759573908320065f3b6871928000abd8315262d04011fb02392c7280026fa1e424cb401074e31e872124200ecc624c93150087d3ce8b1e6420083abd0d6290831004bec3ca2214a011df2305c432440015bf06b92c22000337d9673087400056ec06e8b184268af7815d5610c8011ff0cb9a42200a35d9c7650c9100053ec28c5a0a62008fe87109610c00157904b268718803a7d8d43109210057d43064a022000cdd64dcd218c08dbb30039a432000337dcf32583410047fc32e22106000abd83d5262d0401978c8b8c86880023f60672d91530047fc32e1a184200d3d7454821940015bb0d1946220086bea02325802114eaf428e690c2000ecd6354832c8001978e8b1a42100026f61e420c7400063e38acaa1884008fc8754f61500018f90cba865a080337d41768c8310047ec34e5a0c6000add80d9363484018f8cab886488003679d3321813100676bacc52106200cbc545da428c48b9bd0c39a43a0002a7a1270d8d210066e39cc490c8000ced625c2420c4011fb0e31462a809b2f611760844000676300e4b0262008fe87189315401fd38c7a188490802b720175d8d213a73d406caa1220009be8794543d00013f3003b084988023fa1b73505200047f43ec89926200c7d7699631c80018fcc6ba885908031f1d8654c9400066e432e610a8000e3d75990210c0691fd0f3124398042be604439825100677c32e418e8000adf81550634840197ae6b88c890913679cf430854000576412c89942000c7d755c06250c215bd093a2c6108031f1db65cc9100065f380c998a4200c7e765d442cc40197ceca1c849883abe2015298b300047ec3884b0c6000cdd631c931840019baed3846418803ba14062cc9100047fc3acb9928000e5f3159631c8093d3887b2a86990032fe1276cc940005cec24e11906200c7d85dd932840011ff0cb9c4220003671d073484400057dc
  | 43 => 0x639000277e0d71950320066fc1ae33148600e5c855c36348401d3f01b26c6908a737a18734861015e6f438c7a0a4200c5f659cc215003f1fb0db9a85900031fdda65cc72000676432e418e8013cdf65dcd21cc001a78e332a86210039ee0175189430065fb26e2a9a4228e7931dd560104011fd0fb22c0988031f9c56598f2000736c2cc490c2039cdc7358d41c80279bc873b086908036b1507250721006b690aea2104218dd6535c7438c4018fccab8cc790117679cd43087400065fb18e8908407de788059431c80979b8c6b9ca89089f3b586720c7400066ec36e690a8000bf3814c9404401fd5e86b10841891b730c9720c6400066fb9886b0ca000c7c50dd952cc4019bee7b0a42a00029f61464487200075b98cc898c4000cac641c931484018fae9b2e628809f750c770505310057d42065304a2008fc8750d62c40011f90eb2a8498802ee60e4250110004f6c3e41a1aa400cdd7558c4308453bb30039a4308003b3190624c9310063f3b2ea21262138fd87d8c42484019bee729ac2210034f5d153086500057c41aa8b004200b6d8510832884019bee6b0a43200023f61b73507200065f322e32106400abd8319242440018ff0eb2c841904f1fdcd65487300065f3b4a7a128200eac6490a3248401aba62baec0990031f5c765cc9100847e432e91926200c7d65dc1430840197aebb2662908023fe1973d042004cbfc3aa4194a000e3f84594420c401b6ea8b888518803ae610735802100577414c99922000e9f8019363484013bb073b242a00031f1da5054d4209e5ea1cec21a4200dcd7354a420c8019bb0db9a42200031f6157610a51006ce3a2a690a6000aed801d2620c40197aca3a242180031fdd365cc9100057d430652022000d9e535d021cc001978eda1a62a0002bb20973584200063fbac64b044200cdc505da320c40157b09386c690803a7d5063d05210fe6e31ee6a12a226cf4315da31100019d8c4b8864880afa761063d052100577410e6b088413cbf73991210c0019b8e0b1aa6108031fe19750cb410066fb1ae11924200afa80dd56110c279bce7b1c8490802af21952d0d400657d404a23126030cdc635cf42544013bb0f1906328002b7a1a320c5400065f3b687a0a420cdd9831c1520c801a7aeba1843a0002de2015254e410056f4346518a8000d79531c1520c8019baeab18841087fb318d748c92100677b28e4b026200c7f65dcd2150001abae6a9843280032f59170191310075db9c84b008200cf771585608c8015790ca9e86a000337a1b73485500065f3b28721242008fe871096194027adc64ba864908023f2197010d210053ec2864b048200add83d45610c801b730039283a000337d8f7050d214173c402caa0e4000db7435c4428c4011ff0cb9062200031fdd632582310065fc22e23126044dcc325
  | 44 => 0x320047ec3cc518e8000e9e7358c42904014fb0b3224288003671d07348630006cf418e8a966213cdc74d8c324843b9f0a0bb66508003bcd4161087200b57ac0ce6b084000a7d859883190001a78e2b2a84210036b952720c5400047ec0cec21aa413cbd439da43484279bce9b1e86908031fdc56550b2000677412ec1884000e6d5254e62104a1c78ca21062a0002cf61432d05400055f424e0b0c6400cbf72dc5640c00175904a1a64a0002e7e0d41cc5400066fb80e0b184200c7d75190214c00173d09386c6908032f591700c8210d67c286ec9942000bb882505404402b5bd06286c790846f620d214c1100065e204ec10a8000cdd75dc363484011fb0e32442a80023f61f63109510047fc32e7a0c2056daf439ca43548259be61bb24218003379c163d0c210056f43665b026200bb9849c232440011fb0f212c398002fce0532901100063fb02ea3128600cbf845c4625000197c803b242a00033b594724c6201463fb8eca90a2000cdd731cd61c801f9bcc6b9884100031f5cb6590d100b75d3a2c03026200c7f72d953144021d9e423a2c6108029f616628c6300bd7bc0ae6b088048f4f3254e32940f9b70ea21281080d33ba1e62487300047ec3e87314a000d5d755cc424c401d3b06320c6908033b1da524c5200065eb28e890c200097d851c9434c801978ec3a2431804a3f61f64d812129f8faa4a99926200d5f315d4420c4fdaf50bb82a4988033bdca72587300066ec3ec61928200d74315d4624c4019bced29c84980032f9907250e51005bc402a4a988200d79531c152d04315eb033a2c3298cb3719173087300056ec1ec99964000a7d859913144065d9ca631264988031f19773c85100047ec34e52a46200d5d7354f429400157b08282c2191ff9e201658c7200053ec2864b008200cbe631d121840015d904b0a42180032f5917110820006af3aae621262009f787484218c001d7301b26c0908027b20975505210063e3b6ca1922044cdc319d832500479bb06bb042181177360873487402773632c6590a2000cbc761d1210c001cb90cba8c69090bb3c877058c2109e6f39ec621242009df835c4625008bf1865a1a65a00029f61a75108310066e326e690e4000cbd659d0618c827b38e6a1a829080397a197518d21005dbc0a8698e8000abf815cf64548018facab9483981132f21276cc9400066eb98c7b122000cee74d8a324c4838fac6ba865208032f1907250d520066ebb2612988400af5810c960904019baeab1c86108035ee0175d8321006cfb9a8290e8000b788054953084add9cc6a94659009fb908561487400065f430e8a966200e9e83193634840137f0ea1c43a00033e9d860d0d520074eba6c831a421abba80dd13250001cbeca31a64a00f3739ca708c93200576c10c631280008fc8750b614c0014fb0bb22
  | 45 => 0xde4825c44348401cbc65b2a64880023fa1a744c5210057ac0e84b0c6000c7f7659631c802bd5a6532642180033759473485400055ec3ec821a4248cbf639d332940011fd0fb1a42a81239798e5054e420065fba6c290a6000e9c5498c420840157b09b96c29800337dd953507300047fc0aec2146000cdd655ce428c8018faeab88c4a18023f21d63507200066fb1ae518a8000cdd64dcd2184001b68a8b88841080376d4173087200047f43e86b0ca400cdf835c662cc001adca8b9063280023fe1d63108200063ebaae23126200af88250d60104019b8e9b1a62908af3718d73d0521006f3b12e219220008fe8790f61548659bca6bb043980031f59573907200071fb28e890a80238fe86dc1324c4279b8873b48690802bba0a4358b1000676312e32928200cbd8719232484015bb0b386c690803ec4415110940004dfc0ae62128013cde86dcd21c80018faea320c4988cf766007348420006dda82e99922000b9d8310b31d000197cec3268690863b560463505211066fb2ae72166200aee829d5610c8015ef02a9ec290117750c77050d310065fb98e4b24a2008ff865c3438c801b58a93968290802bd60472d85430063fbaec4b026200bd5819d363484013bb07b8aa8190023f61c64cc9510073dc02cb90e4000bb58110b21d00271fb0db9a42100025fe1570d8d210065fba4e8b0ca600c7e73d9762440014fb0b3146320003375d3630c9210047ec38c8192a216bb88055131500019bee1382c61083b7698f73482102d71e3288518a8000eac641c931484011fb0fa18c4988032fa0d76908411ceecc00e690e4000cfb63dc152504279bcc6b8c650803f750c47250d310055ec20c7b1220008fe869c8424c401d3b01b26c690803379c263108210055e412c9a182000c7c505da32944019bae639ac2100023fa1e53587400066eb2ae721064008fd87d9332c800157b09382c3190023f219738854000576412c290ca0009be87d0d21d00019bacab9843a00036790073485400072eb2ac698e4000d797219630440699dd0d39086908cb37191730843007e5f3b6872126420cbf435da420c4019bacbb9a4288002afe1d641913111e7790aec1086000e6f65d89325000176b0221262a009eed20532d074018e6f39ac72162000e6d658c921c800157f08a96c688002b7a18328c5400c63fb9acaa0e6000abe8414363c8401b58c939086908033bdd952507200065f324e521ca2008fd8798831940011fb0e32464880035e5947054b41004bec32ea2106200eb970990210c0011fb0f196c2a80573798d73c84401473c90eeab008210ecd2158c430842dbb506382a498802b7a0064d8d210063fba6ca1922000abe80d92648c8013f50f19280880023f61c640c9210047fc3aa5b1a2010cf6215d84308401abe62ba88518863ad4c571993
  | 46 => 0x8f8e7b2a8488002bd60472d853009f4e39ac89086000abd811cd64880019b8c8b9842a80031f5d46418d210063ebacc818e4000cbc545d8420c4014fb0a316c2a18032f1d262484300067ab92c39888026dcd215cc2110001af2cbb82a419002cf21152c865010d7d40064b004200cfb505d831c80018fecbb9a42880032f19173909212469ea9ce9994a000e9c649c06348425de460b0a4218052bda1b31c851019e6f39ac7a084000d6d75108328842577100aa242a0002afa127558432006bcb28e0a9064008fd81dd93210135b70a8382a5a0802af612635872025f6631ca91924200adf835c4624c0015dd0439ac2100029f617644872000576412ca9928000cbc645ca414c0019becb39842a0002bd604644c720006db3a2a39922000af98010d62840015bb0a3a2c610803675ce5390b400af36992cb90e6000c7f655cb315000197aecb1e85210e6b720d5258f20006f8286e29922000cdf64dcd21c802b9b8e7b1aa3908033b9c3628c9310065ebb4e72108200cdd635ca3110001cd8ca3124288002bba0864d89310066fb9cc490c6029cbd43dc56010c01bb6a0b984210002be2095358041004dec388518a8000cbf731cd648802dde0a0b0a62100033759373484300047f436e6a928200cdc809db324c401adce4a96872805abea0375587300069e38acaa1884009fa870c940440015f104a1ec0a9003371d863d0d210065f398c9212a000a7d851cd61c80015790f32242180933bc81760c4200047e43ac89086000d6f215d4428840197cc73a043280023fa1e624c6500074eba6c9b1a4200d78805d46250c013ef02b9c84880039ba14624c9310055ec3cc92166200cdc73d8521540019b8c9b9a42100027e21d31501100065fc22e33148000c7d755c0624c475d3e6432286988023fe1d53189411d66f39ac72908216bba80909315008d9b8e7b2242980023f61a7210e510073b98acb18e40008fd8794662d00015ef02a96c2980032f59171d0e5000577416cbb126200add809d36348401f62a32128088003a715263908210057ac0c84b088400cbe645c642cc001cf2e0b2843980023fe1973d0a100066e3b2a6a0a600c9fb865c03284041d3b0831c8490803579507348650006ceb9ca7a128200cde87d8d51484019d8c03926290863379cf6310941006cf2a2e610e8048f1c439415350c21ba8e232264988cf3d4c5760c4200047e43aca98a8000abf8359042840019dee0382c418802cf6147250f4100677ba8c49926225cbf40dcd6110001d7686214c1288038f5d6640ca51005cec1c851968000b3d8510932500019bcc8b9843180023f60472580430053fc2ac790a2000cdf635c042484d3ba862392a6988023fa1b73551210053f430ca9928000adf8359332440019dae4392c32985f2fd0176cc4400055e422cb90a60
  | 47 => 0x4008007008836c002033000803000600200f81ac0300000b18000004006001809c0800000000000010341002862c038001002817823801c279806c01401000b00100260ae00080000ba129009808403c0000000020ccc000000008001200102406d80ce0004b701100108f304a003cfb600007f802001000100210cc0100e000100e800000037780040060401991c700020fb00001e006e77200c00040160380018004a6407c3b30008002037015801006a0b7001004063a4d9009184806602e000002c00407300000d8036000000021001001300100340f6001011000000601000c8090010a2d002000c00000700100040a6022000000004c01604f800801000a05480000080ad47c800406e00400000a00060038dc81a800eccb00981180000030001dd800000000a00640dc00200700ac06005b00b800c00801500a0008004000000812403e005008801008804100e00f403200b00000ac00600b000001c00000600d8ac40bcc3600c005001800000100140180b700e003c002022000004829402b04b800000405400980480620786448000018c0700080440a40a100180401ac000004000000603d025019809c01300384a4006000004000c124018001000418001100200000020e603c8024000a24004827c00e0140080b0400800b001092800200f00106d401a45c00000340000000000000c5a002000002801003c02400101520050b0801004800b0050000030004000802d2de0433ed82b400024d00080a4022014000000c0e201e010000403608803a00640180343d6800401200a00183100e0001061014001801200180080c8005000012001a001173803806c0750068110014003004001008c143000010807e00817e0000004046004000001e003000004c05c164005804c000001002006000c00b0018148006011003000403605a000004d2ee00000801a40007ac000051000e00d001849400001811a002803a01f027807402265d04a001403600d0008034276063000004c00e02f01100081900c114a81a000c005031000402e0663ba001c09a00200a026009600700080300d6012001118806ade231800144e200b021820801a7f08ba865a080337dd463d05210057ac08c430a8000dd4735452144001b3ae619683a00030f195719094000576c14a63128000e6d7259431c8091adaa6b9063280033b5d95290f200053ec2ec690e4000cde855da320c40137b0f21463a000367a1173087400055ec18c9212a200cdc76dcd2110001c7ceba18c4a0802af20964104300066fc0eeca188600adc835c662100019b8e9b1aa6908037584373485100053ec28c910e4000cdd764c83210047d728239ac02084f6d50d7110d210059ec2ee1b224221cbe71992210c097ba863baa869883a7ea0376952320057dc2a86b004200cbd651d1218c001
  | 48 => 0x1036800408a01100000100e61030005be400004c0020054002008001801800006508e806c19a000076824c17200300080a400c52d0008940a1200c0808024022031007009c0040950510004000000001002420000c3360038004003005800c088003006000005002e000801401c60b00980a000e46401f81c01860270040000034010231801400419700280d80202e2001804001e07f31400540040010230d4400085e0198004000000001801000000800d008c012003087480c000107001811c02400f00200240240040840000014017001805c07c06600d800001c04f0268058000006000802801e1760010010004041000009401c00000880980a200001480240100000690004012008034012c03c000003800c000177001005e3d80000002ca01bc015000000800000700100040000020078008014000006147c1c800500000000ba57000503c41921dc006800c02c009024001400a0100058116fda00100080ac9760ec00025c82bc009029000c01200001082d802c0420052bf400000016100102ce000000001000a0030002e1000e00c03f0074002008012800000a046097013800001904080200381b800c800007c00000800180000604869e5c04a01100384ac01a096034800400602c0038000000000008005005e8cb001011001a01202680304fa2e6164801400060200527e80b60010340780004000010000000c02b2078000106005003006000001900c1d080080000070084000012002976c05a00000700240534bb0000a1007c0000138028072003114805c0260070020068002002044802c09e0450000014004001003000001000100102f8004000005805400000000218145fe02eac080000060246c816740005530000004038041006814400001a018001402c016000800400a00103e825c008000001800401e00000c800480001700000100546a1637001803401f05b00040860000020000002006003805000c03600c009c00000700280100b4000007000001417000280dc00602600d00c000000000a03e803400800500dc00006c009800cf3000400459e80000040050002cc0000003802c17e3f5007807c02427e0000440006000000802c00203d017806406000202282d400c0ed00a14d002e03f02f000401e02400980381761d605f000001800401e800c002000011b4845060050000034000c8b1378031d7600000000440f401d00980640000013bb805001405000580001b0043003002803201707d800c02800002e0000014000009003c0bc0020010038000007005003800000200280540040030008000000001000947801400f000001c0c22830070008058000001005801204b004156c02231c000802c00a00a00280b4008b2d00800480f800ea99110400800200700280c003019080000580300028150006c5b000802
  | 49 => 0x2800200350b800001404502300b4bda05e001000463001e009809000600000500000080050080004006042000800000e050532800908e01d00501380000070101434006005044010402e004021a4600d005e000001402402800a002c024e5301e80e8014096000009000006c04980ace121be009008537400900100000140133e080540001e5010814802e005004800000e000023000c16000002f802c000009023812d80401e01380001aa1742b92f8c006025011001c004009002000108c045000800404a53105c800802a000027802440e05c00f8000048008000800000400004d800c0a4008000001c01e05036a80508d2000058001401e007000000805200200000b0f0e008013404d61401000000f620c0020010ea400cad1005800c00400600083a007e00000101fc012008000800000200200101a076400103f8009b32001282803800604e0798000010000044006c02a00400b80c00100da00780a800400b01980191180bc00b003801000001a00bc006003000003808a0a600a002c0120b600114c83760130308034078000000800000600c03d000009400402084a8084be801a006c0000230018008038002007800800208d0068074044000006000c000002004000002e019000002000c00200b800c0000030000018008000265000004c01b0310024058192007801006e069190020824e32b010808000c0010721e7007a000229000400a000000800405001600e01a800a0170001b2c004000001803401a0050179c34002000001001806e006004800000200b002000001a00302e001400000001c8000014000000800144000200000000000cc004000400009a273b76c01601100982cc0fe094000002c02c0020000000000000006b5c41924ce00c000804202d00011280e400401283c800000100580480623b100080300140260000048006b22001002c01000b121000c03a02100e2fa801012d00000e4178001000000400200000081f407708a005030801000007e001838200100000000a4000000001400403a00100b803800100d13c40040110048024e4206c0060010082000000000000400000000000a60530070aa000604e01f0108020c8300480200b00130028000000001012000487c00a003823c05e00900d81540c800000186a4016d11016012807e052015014001000b0000000002138001803c000228000801cbac00a007800c006004471811800000c011801c00c0bd00e805c10e21101b800800c02e59a002c0240340840018000008000005808a0010c8001c00001c00100c406c0c4001010db14008001802c00005c0002cc015c03103880ec08500e001810402633602000ac00e0010238068008001002000802c2ee000841402e2ce01481340fc00172c8034a58271001016001204d00000000cc000000003c02a6b
  | 50 => 0x10028050026010800c00200300a81e400c00e0c4001c1ea00c010004400a0990008004002000005800001808b0028160a26000001a800c4e01400aae4000600d0080084016004034000800c00400000080000ba00580980ee00b7468008646547009804813c067000004c00c01d031008400001548502780080000168014058001030000c00c2dc00480e400a456000800400000201d800000620e0e000bc0041310110058006007001840c00006d0260054174008000004c016036006001c004002020812849ad8a000001402a00700980b407e0fb001000800000300000f002200600e85bc002001033000401401100b8008010036010800411001d009801403200c001001000a028007010c23e001004004400000001c8030bd4001007800009a05413a003c05803600680000280000118bd4008000164800c01a00500d8008070010001003000000636e800008e0080090044024002063816803600000002540ba00000c8030006006006849c01c060015800001236906f001800200109d87bc00001d00a8014004002014000001400a00080180000045f901a41220c200001c038c0004b6000014400000180000020f50010024098008000001000001000b005c00600706b0050006dc0001007a056001004805400000802900b80000dd00500383f0036000964408a41d01382d800e00002e00000004cd000009c098002028801435c01f00280a8006023002002403c153028806c00004600a801002c00201681b002004029b0000014000018000c0da07a000802803800100281a4002000008002400800900f8a0c00200001080d800000011f00004580080148608038002009800002408c00c000409a00b46300a000e002001800001e0c65ea800004201e081000004e0030030c14002004006003002200101c00040000400540008014012020002017a0174f7069401c003000005000802a00680000200840008000cee08300001d401601504180
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x40143c9458975189310061bdc98519131c840189e865ce32d05400070e241655d263c80014b596d0d71908210070b1d050189524c40152c94485750c8210060f9db855c0644840159593151710c94100713cc575588420c40149d94a1676cc93100533249731cd6108001c4e9518c725052100731a0d7258431100018b8801d9544c54000617614739892190001a998020064d8d210042f660609d3325440145f985d4631092100527e4d7698f42908014ae9290c7650d210050fe5173d952144001e1a4354f431815200627a1974cc8604c4018cc63a087454d2100517e4d7459521cc00113c985d152086500054b251859c8319400191d85dcc32507400070b19472cc9415000145f935d36548510006aca191094743500010be9890e76d0d210070b9d27259431c8001c1c9459573908320060fe1d7558c429040189c83e11719883000517e5564dcd214400107d98194724c510006336607318921440010bc9850171189540049b6548250f624c40129e942017558c2100617e15635c343084010be97a1d6448430006e420d414854044001c4c73d9632485100064e210805d46250c01478974c875580410060f5d98510a32d0001c1e7350f659091000527a5d64dcd210c001c6a725c1650c7200070b5d4541883250401c94731d161484300049e25d850c960104270dd98d9373487200070b616641c9318800159a90dd07348540005a324964193324c40123c9661432d05400062e61d70990210c00163b944c87558041006279cc8650e42484019b18744251d0d4000713c85655cc21cc00145c964c575d81320052ba4a439db43548e545f974cb65cc5100051b654865c831d000189c76e0d414c540007311ce32585211000183d851907250d310042fe61741d16194c0161d9521c6418d21007075d17359421cc001cab649cb6090d520070b5d17259431c80010dd97a0b638c5400066c61d1094442500014da9021276cc9310049e6588054953104010dd9814276cc9310049b65482593624c40145d98d9473485100072364c74189524c4018af40209764c44000517e5586dcd2154001a698254c505872000617a1f65cc9315000185c73e1564485300052e640845c6621000143d9518c7448420007231cf7498921cc00161d95e0364d8d2100437a60309d8214c00156990951720c650006271cc87991210c001a1f85d9170d8d210042fa60765d131d0001a598560063d81210062761d73990210c0014ae949c3628c9310053565e3258431100010bf985d8748cb4000437663641cd21c800149d941c36354d2100617195878c8315000149e9421973086500068e210805d46250c016399418c658c11000517a5b325d4424c40168d93150620c9410042f663651d1210c00145d95d90734872009e3521f73585210c001c6b90596720c720
  | 1 => 0x10050f65663dd1214400186d866147250e210050f65a655d021cc001954316147250d310050fa58415d462504014cd9718a320c54000527a53865cc21c800107c976143258041005a664287d90634840143d9621175108210051be5d3259432c8001c8c731d26248430007071cd43d95414400143d971057518941006271cc8650d41484014ac9650c72505210043be61721c96110c01c9a6350f7054a420052b65f4318a52504014ae96d507250521004ab66054188424c5096709154850587200061bdc985189604c4011bb985d0638811000527a507018d51484018b576e0573908410049b66265189524c401e2b70d5062549410060fdd3855c16190801c8e931d06254931004b324981950634840189e87d8f325054000533249635c8311000164d9314062549310061be1d7259431c80015999414073486100071354b73189514c4e5c5990d9773485100068b9d484588624c4012ae94a0375988310055664254dcd219400186d80614725913100527a5286dcd211000189c835cd711915200732a0c621c1524c401c2d75d9362109310060f61d7459431c8001c1f65dd373485404848f259851083150001c1d75dc06418d21006171cd85d8d21c800143c965d4420c5400051d644505d83294401c4e315d462109310052b249751913148401c4c73d9632485400052b249645c0644c401c8c74dce62487300062b1d082585210c0014ae96d0c72505210061761f658c831500014af97486640843000617617730c961d0001a4c63614428c921005356467058e5308401c59631c15354a42007255007358521100018ac642097194d210070e591605d4420c40152d95211720c54000563249845cc21d0001c5a631c15354a420042fa62635d021c80018d576e05758c83100533a48509db324c401d30509457418d10006275da849c2320c4014ae949c362989310051e25d5254d601040145d95a1b7348740005a56478719363484014cc925cc73584420056664074dcd211000186f879d562189310042f662701936348401a3465604424c5400050f65476192434840145c9560276cc93100533a4b641cd21840011d99814073485100052b251721c9610c0010dd9819073486100066c607709c36448401e0c215d46418d210042f261435c4625000183d75a1265189310041f660659cb63440010df985cc7358720005ace458390960104010bd9818c74484200062b5da849c232c840149f9650073484400070ee41655d021c80014ad9715062cc9410060f61d75990210c0018ac7420961486500058e640419d462504014e5910c8764c9410052765070d8d5148401c1e439d953d0d5200627a1f63909325000145d968c975108310054e640415d4625040113d97211520c6500068b60975150625040183f766147250f410070b25175988420c
  | 2 => 0x13fe30654415110940006966158018c604853745f9754b638c95100533a63635c83150001cc663585720c4400056c650505c432440010df985c07058c210051b24974d9531440010bd981c06454d2100734900735852110001c5965d4273087200051724d615d760c851945e9619473485100062760e73192424400185d65e0d71108320071a58a605d4420c40149e9420276cc9310070b614641c9314840145f9560276cc93100497e55809d1630840183c9761472590310052b249741d16194c01c58631c1535494100596241525d5630840183d8661472507400072318f649c84348401c1c7399543584420050f656631d121840018ce7620964cc9310062ba1072cc961940010df985d074d8d210043766276cc931500013b39160e42501100072618d43dc1525040183e7661442cc940004b926132585211000187b762015254c210061d1db8154d524c401c6965142720c720004aea40835c46448401a8c63a12708c9210063521873505214400195875e0d21502100072518c645c44348401c4e8518c725052100553648315d4624c4014b59110e76d0d210070ee41655d031c8001cc5728c9610c4400062720d735c464484018e880dd9524c72000437a6230dd921cc001c9563d0d71108210053564680dd9320c953a8f40209634c84000533a48549db324c40146f974856508730007311cc8258521100012e892604431815200713d9473189214400145f93589751893100719d94625c43244001c1e755ce640843000752548509cc21c800158d920c674181310042fa637458d2144001c8e7418932181310051ee59531c152108010be9810076485400062720f845c66290c0159a90e137348540007071947350521500019c47320941485100062e5d1801d16194c0145d95dd87348540006279cd87990210c0014ce92141768c83100723486645cc210c001a39642015254c210064721273548219400126d981406254931006476147310921500012b9981ce42580410058e65332dd5601040185d75e0d7198a3000738604621c1524c40149d94a1b7348510006476167310821d00014ac925d0745843200527a5070d8d314840149f965017308440007075d573990210c00189d87d8c428c5400071a5d450dc2620c40146e960c975d813200527a527098e520840149e94a03764c8320058d2454259561108010ef985c8725865300729d017258431100012f19121032982510070e1c875909601055da3b811d642580410070e5d27059431c8001c2d6261472507400078a1c354189525040183d76a12510ca50007079d17359421cc00183d851907250d210061b5d582d0c6250c0149f9759064cc9310070e5d17059421cc0014b59118c74484200050f658845d4420c40149e94e03764c83209d2765f6350e4248401c2d75d0c620c94
  | 3 => 0x430052725d64dcd210c00149e941c16354c21007134857558c420840183f7661442487400070e9d570990210c0018b8801d9544854000715654735852110001c1e735d165087300070b0857519063484014cd920c7764c44000437e61731cd6108001c4e951cc62485100071a654621c1524c401c8c63d927290d21006476177310921d00012da90e1e54d8d210070e241655d021c80016c591189324c54053f5494450dcd21440016b1901d1614844000723193639c843484019b1815c070191210070ba16641c9318800183e87596635084236f4c1d551909404400185c636147250d210060fe1d7459421cc00145e9619473485400068b60a75d0c62504014cc9259073485100052725186dcd21c8001c4f655ca320c54000517e5586dcd214400146d9688575193210070759473dd121cc00143e949cd75189430051765e315d4624c401c8c5418c7250521006934c5851d1620c40189d64e0d71108300042fa60409d8215000143d941db65cc9100062761f84d8e424840129d9819270d8d210051b654645c831c80014b59615171908210068d197814cb415000187b879c1650c72000527251731cd6108001a4f216177058c210071518f655c43244001c1f75d536350521006d4cc480549538c4014ae97d0c62549410042f66076109315000189e861d3325813100707dd073d95214400189e869d332181310058765487d90634840146d96cc975108210061718d851d2324840145d9859473487200042f6607019131484010bd981c064545210052ba527018a324c4018b9845c070584320042f2598790931500018db76e0d2150040007075d7645c06348401a9b80a036418d21006175d7835c46250c0189e73a127098b310047ca60505c43244001c3a90d957418d1000539648315c4644c00189d861cc7448430007265cd70990210c001479951897018543007072517598c42084014e892593705493100725dd073585211000189c7361070584320061ba19851c9434c80145f98d947348540006271ce84d8d21c8001a8e8458a708c831006271ce87991210c0018e8801c952587300050f65076d94324400149e96e13734854000713a17631c9314840161d95e036418d210064b6157210831d0001c5b90595730872009c3766064dcd2108001c4f62d9473485100052d644431d94348401475911437654b3100517e5586dcd21840010df985c070d8d210055a642549c8319400149f9460276cc9310070ea43655d332440015999414073485100070e5d17059431c800186e8761462549310052765286dcd2194001c689061472591310070ea4365dd1214400146f96485751082100713485655cc21cc00185d85dce62486300060fe177458d21440010bd9818c744861000535644641cd210800192d825d743189410070719773d05215
  | 4 => 0x4840198d7320943087400061be1e7259431c8001d28505497498f2000527a5286dcd21940018ba801da42485400062761a74cca608c801c1d651d3734873000535644509db324c40149e94a1b734861000627e1d73990210c00145d909d97518d21005a6a4287d9063484014d591141768c8310050f658845d4428c801c4d31595720c7200069a61750dc2620c401e0d85190638c92100517654865cc21d000146d95191720c4200049e6548250d601040162d9210675189410071ad4c621c1524c40197075e053250110006934c985109610c8010be98102760c540004ec6448250d4044001a99802006418d210058765470190634840183d879d743189410062ba1872cc94150001cc563585720c4400062760e631d152908010fb985c0705843200539647655c8311000123d9520d711912100527a52859db324c40149c9461b734873000693cc5851d1620c401c1c74dcf65485100062b9da849c2324840145d9519373484200052e64076d9043484014ac9261c644c5210073160d725843110001c1f65dd073485400050f656871903248401cb14044171189541962761973d0c21d000161d95dc36418d21005a56448019363484014f19714161087200061798f855c3430840145d970c575189310052e640845c662d0c01c2d7519362109310051de5d31d94315000152d92105751894100517a5f3259531c8001c4f31595720c720005a664387193634849b4779654b7154c210051de59315d4420c4014ae921cc645052142eb22016354832c800183f879d1650c7200051765464dcd21c800189c84e0d7198b430060f61d7459421cc00189d861cf74484300042f66263dd121c815f27b9854c43181520069658c80549530840189d87d8c420c5400060fd93855c3434840186d8658975108310061e60175190324400145f974cb650c9100056624154dcd21500010df985cc73584420051724d615d464c840189c84e0d719883000627213835c4624c00143d950c87458d100068e99080549530846585f865cd5308650007165cd7059421cc0018ae871d2624843000527650509db324c40145d95990734851000437a60301d9214c00195875e0d21501100049e654870c96010401c39755c264084300071ae41851c9644c4010dd97209638c44000517a4e76d95215000161f956006418d210070725175d8c325050b98e72a12708c93200627e10835c4624c00149d9310276cc9400053aa4a641c1524c40125f9560064d8d21006632117354a420c8014cc9259473485100051be59325d464c8401a9763604428c5400043766064dcd218400162d93d5062549410050f650615d7604c801c8c63d0c7250521006355db815d2320c40189d40e0d719884000517e63651cd2144001c687054c62549410054765473dd121cc00186d855c862185
  | 5 => 0x6500060f21d6550d611080189e86dd332581310052b65b325d2608c8eda3981dd64258041006934c585dc1620c40143e9610d75189430062760e73192424840189f8420d711894000617e17635c34348401c1e739d6640843000716d9450dcd2144001c1e735d664084300050f65273d972144001a59632015254c410042f663439cb61500014b59121276d0d2100497e55801d3634840185f875cd650873000527e59409cc2110001c59651417308720007079ce7459421cc001c2e645897510831007131cd658c921c80010be9810276cc94000533e4d811c964440018b9868c074484300068b65482590644c40185c8319571189400051e64071595420c80149d941c06354521005a564680d90634840199a80dce424854037f1360b651cd21440014ac945c872586530060fe1e7459421cc001cb14044171d8d54005b124983584311000169a90e1c64d8d2100517a5b315d7604c801673914cb7558041005176617518c424840183f875d664084300041f6607399561108019387520941501100060f194874c94150001c9473dd1614843000627a1f63109325000146d9688575d83210070e992605d4420c40146d97194620c910007321cc501892144001c59739c165087300050f25d425956110801c39749c16508730005a364c54188424c4016399010575189410060f61474989218c00189d839cc64909500070ba1474189524c40186d8698975108310068ba5482590644c40149e94a01768c83100617d97835c4625000146d95e19720c6400073164873585211000185c65e0d71189400052764f545d8428c401c696258175108310064e615801c941d000145d978c9650c720006271ce87591210c001ab28644251109400050fe59415d4321040107d981ce65587200058765687d906348401cc473e09614844000556642541cd2194001c8c6350c72505210052765270d8e32484014b890591701913155c8f2598510a315000198c7320941485400062e25387580604c4018cc7320961486500052ba4a631d12194001c8d9418c725052100723a5173188215000146f925d3654c510005356467018e4248401cd0505cd61084200061b60975d0c625040145d939db65485400070e9d27059421cc0010df9859073485100070e241655d031c800145f955907348510004a7a52809c9630840185c7661473485300071a548505d831c800113f985d251cca5000627613739cd61c800191d851d0734853000437e61731cd611000183d8699175108310062ea5387580608c95dc3b711d642580410061e619605d4420c40146f96485750c82111db164c82585210c0278d486d8d7110d2100527a5286dcd214400183c76614424c5400052da58315d0604c401c9a705ce640843000527652805da320c40149d93d5276cc94100633660631c941
  | 6 => 0x24c4016679154c6254931007231cf74989210c00183c6561c428c5400042f66273192424400183d76211520ca500061b60975994624c40107f97616620c6400072950172584311000164d928c57518931007134857558c320840183d76211520c65000527e5186dcd21cc001c8f631cb325054000716d8c7054d525040192d85dc8424c74000527650505da320c4215c5932097110d2100665206744c8604c40164e960857518d210061761c631943244001c5b9059673087200061b61d7259431c800189c732117058432004b664387953634840163b944cb7558041007269cd70990210c0018cc73a1a324851000566a4374dcd215000143e962117510931007315c832584311000149c9460276cc9310070b61474189524c4018cc63a1e3250521006271d98390931500018d873a007458432006171cf855c1610c80186d855ca620c6400042fa60431d94348401c8f635c8420c5400052be59405c8311000183c65a1f3250540005a564487190634840183f76614424c74000533a4b635c831500014e5910ca768c9100052ba527098a520c40145f9859473487200062ea0076dd12150001c4d82d9473485400062edd9801d121100016c59320961484400062e5d1801d1610c8dfc5990d94734851000732640731892144001279981d432580410055365c215d463484018ce865ca320c54000533249731cd6110001a4f3161770588310064b6167210831d000183d762115208650004372627650c43484014ae94a0c72591310042fa5c84595214c00113c985d1520c65000707d5176952320c4010bc9660672d0d4000517e59315d4420c40183e875947448730006271ce841c1610c80129e94a027618d210072358f405c831100010bc966047250d4000627213835c4625000183d851907250531007075977398d421080166b9254c50189100051b65a215d463c84019b087505215011000556642545cc219400192c849c9520c65000725151635c4420840143d949cf650c910005332497518d414840186f8658975108310068e505850c96010401c68706146254941006475d58390832d000189f84e0d719884000517e5586dcd21500018d863e017550d2100437660641cd210815143e9619774485100051765764dcd21c80274cc9261b734854000633a1872cc9604c40183d879d165087300042fa63435c46250001c4f825d563108210052725e64dcd210c001a2c9461474988310052b65f5418b325040146d9788175189410062ba12729c363c8401c1f651d373485400071a98a605d4420c40187b8698175108310051b65464dc93108001a4d216177058c21007231cc7498921cc001c2e85190724c52100687e14645c36348401c1f549da54cc9310043e65c840ca6094401a8d21a107058c2100566640741cd2110001c1d649537348
  | 7 => 0x4e410062e9c387990210c0010dd98141768c8310060f61d75d0c62504018ba70a127398a100052e640849db43484018778759521087300056664c501d12184001654914c9654c720007130cb655c8315000146d95219720c44000555245325d4424c4014ae961507250521004a7652809d86348401c556354b7154c2100517663651cd215000192d855c8420c5400056665050dcd218400152c92505750c84100437a60509db324c4994d59199676cc9310051be5d32d9432440018ac869c952d0d400060f61474189604c401476960c575189310061be1d75588624c4016999021c6418d2100729190625c4424c40145c935d365485100063361c628c8315000147990219750c8410043be61721c961cc001a8c63612708c921006171d686cc9604c40149d93d5176108310060f5d1859933244001c1c651cf4148540007169cd7059421cc00145d970c675189310062b1d8825d1315000152d95211720c7400052da58319d0604c40107f985d6640c91000527a50509db324c401e615214161087200060fa1975d0c62504014f19118970185430071a597509c831c800199573e054308740005a564683d90634840149f965037348440004b964480551620c4014ad97d0c620c9410060fe17645c36348401c9463d917110d2100725d00735852110001c2c94614725913100497e55809d8634840143d96909750c84146f1594773585219400143d951d874484300060fdd185991214400183f875d1650c720007075d673d0c625040159593d517110a310050f65c419d4625040185c7361662486300065c14187944324415523c96614424c5400062ee5387580604c4014ce9299073485100050fa52735d4624c40189d76612708c8310061b619851c931880018cc63209744c521006550c5851c9414c401c2e6498975108310051be5d2159421c800143f945cb65d8d1000536640849db324c4019587520d2150210005a564470d90634840189c7321165485300050f65476dd121cc0010be9890e76d0d5200693485851c96308401954815d573189310051ea5f321d56010401c6a9518870549310061b9d98510a3248401c69729c1650c720007075d67358c429040189c732116348510004ab259849c232484012d99021e5458c210061761d7359421cc0017a092505215011000437e6176cc9311000186f6261472505310062de1e64484210c001c4c651cc62485100061720d755c4624c401a384261432580410070b591625d4420c40149e9421973084400053324d811c96444001c4d9518c7250521006a3c86841c163084019387560442502100058e653321d56010401ac463606708c92100713614631c9414840194c71614424c8320061720f655c4625000145d95e19730855000527a527058e32084011b99814074486100051765e319d46
  | 8 => 0x21080010bd98d0c72587400052ba48431d9434840162d9210575189410061761b85dcd2194001e0d85d90638c9210061ee1e7059421cc00127995a0b735804100633619728c8311000199a801ce4248540006355d9819c2320c40129e94a0375d8d210061be1a625d4420c4011b99814274cca10006561d483485404400145d95ddb7348540006271cc87591210c00185f7661473485300070719773505215000183e76614420c5400064b6147210931d0001c396498175108310043be61721c9611000191d85dcc4248540006331cc8258521100018ba809da42cc9400070e188655d220440016349150a65584420068e909850c960104014ae9210e76d0d21006276137398d61c8001477974c5650c72000715a5473585211000191d851cc42487400068b485851c964084019707560432501100060f25d851c9640840186d85dca624c6400042f66063dd121440018d47360464485300070b58a851c941d000164d920c575189310069a61450dc2620c40189c73e1165485300052da5b545c4424c40183d75a127398a10006361cd801d1610c80146f974cb650c9400064b21072549319400145d97197630c9100041f66075189604c40161c936136550d100053aa4a631c152d040170d95109320cb4037f150c7655c4324414dd5251140734851000587657871936348401c8c631927210d2100497e558019063484010bf9858374549313b68ee0775909601040189e73e1e64084300051e656625c0418c00183d7661442ccb400051be59325d4420c8014ae949c062949310046ba63325d2608c80123d9520964191310061e61d7059421cc0014b59110076485400070bd01851c9644c401ca8649c86090d520061761773989219002789d86dcf434874000715185315d7604c8018d481dd9324c44000627210835c46250001c8c84d8d720c5400052e249645c0410c00147591141768ca51004a7663649c3634840183d86591751083100617e0c76595524c401ad08358521500400060fdc1851c964084018798754c501891000539644645c83108001c1f75d5063505210049b6548250d62104015b190211710c9410068b60975d0c6250401c69725c1650c7200042f66273d9360484018ac76209744c7405648f2598510b31500014ad96cca74982320070e597505d021c800183c7661442485400071a989605d4420c44d4e4974c9614844000527a5070d8d514840189c869d132181310070b9d17259431c80014ce92a1676cc9310073260c621c1524c4018db7620d2150040004b6a6332580604c4010bf98597744853000527a52659db324c40189f4060c72584400052d644409d831500efe625114062485100070b5d464188424c40143d951db6410d210069698c80549530840103d98194725054000713485655cc21c800187b76201525
  | 9 => 0x50d52005a6a4087190634840192d85dc8424c54000627d03835c66210001c3a749c1650c720005a664c6418043548015b194143714c91000535647651cd2110001c1d65dd3734873000593648319d4624c4019957360442087404e517e5d52d8c32544014af96502720c4400059364e65189524c40149d961d3734843000547654731d121cc001c2c945d4621093100517a58315d4624c4010bf985d074584320053a65c50188324400162e97d5062549410052ba4a439db4348401c4d951cc624851000553249315d4420c401c3990d9574cc9100058765470d906348401c8e9418c725052100752548505cc21c80018ae3221d644843000707dd373d9521440edc3990d9774485103bf0e504751c9601040161d95e1f64d8d2100527a58319d0604c40189c7660c424c54000627213835c662100010dd988c1760873000647211735482194001c8c631927290d210060fdc1851c9640c40127b98dd4325804100527a5e64dcd210c001a3b4161432580410052765286dcd2184001c1d651cc744873000527a5270d8e32484014cf9361c62885400051b654631c9414840152d95212720c74000437e6164dcd2144001c3965d41740c7200052b65c541883250401879875c1650c7200068b5d484588624c4010bd989c0648c92100517654641cd210800183d64e1570d0c210051ba58215d4634840143c9750a6558442007075d4645c063484012d591a027618d21005a5644801906348401cc463189710c91000716594509cc21c800183d879d1650c720006179cf8759421cc00183d76614748cb40007071d073d9521440015999314274cca1000732a407318921440015999414373485100052ba4b631d1218400189f8420d71988400061b61d75d88324400149d9420276cc931006b1589819c2320c40161d95a1c6418d2100725a51635c4420840149e949c163948210071a54c621c1524c401477915d3654c9100042fa60431d9435480185d85dcc32587200060f5d98510821d000189c8420d711893009e17e1b7354d2194001c8d63501720c4400041fe61751d5610c801a3481595435844200527652659db324c40187987194628c1100071c14176440429451b45e9619773485100060f195871083150001c94741cd6148440006a6e0280d936348401c1c73595435844200517e4d615d760c840189c7361363487200060f211755c4625040189c73e1170584320056c650805c4324400187b86581751083156d1ee59531c152cc40143d949cf654851000527a50505da320c40183d86a147250740007169ce7059421cc0014d79760d610c4400058b6546319232484018cc73209634851000533261635c83110001a3465604428c54000617a1b75cc9604c40145d95190734872000566241541cd21500016c59118a328c5400053564464dcd
  | 10 => 0x44038000362100000700c0080001a0005501b00002628d5580c024000070010aeba0050000900140280b0000200612200201876002130000008000020084e8080100640400209602801c2c945d4620c941004b56448055063484014e5910c8764c9100042f660401d9315000192d851c832507400068bcc9851c9640840185e7361d65087300049be6153189525040145f974c5650c7200068b194825052150001d503154c705493100527e5186dcd21c800189f84e0d7198830005a6a4f64d814354801c8f5418c7250521005396467058a420c401c4d7518e42109210056564c545c4424c401c6a729c1650c72000527a5070d8d534840145d93dd165087300043be61721c9610c001e194354c431815200713617631c9314840154c93485751082100437a5b8750c434840185c63e1570d0d214ff8c1951094442500016659114062549310069698c80549531040186d879c9650c72000533a4b545da320c40149d96dd37348430006631cc8250521d0001c1c945d563108210057464c505c4324400191d855cc42087405768e604759096010401c5b651407348510006171cf8558d2144001c1d75dc36418d2100723c86645cc210c0010bd989cc6490950006950c585989314400183c8799543584420062e20276553325000149d941c3634c5210044f65e8494732940018ac76209414854000476660501cd2184001c1f651d0734854000517e4d615d464c840183d879d66408430004a765280dc7634840169591a1f6418d2100587657701906348401ca8649c860d0d52004a7a5280dc76348401c1d649507348650007235cf4318821500014e591193724c4200052ea42765c0644842789c86dcd4348540006271cf8458d214400183e845d6731894100587e558019363484014ae921cc64545210053c644641c1520c8011e998140724c4200070b5d6321903248401cd173d4161084200060f5d98510831d0001673914c875580410056c647835d220440b185f835d571189530051765664dcd214400185e87d94734854000556642549cc2194001695911c06418d210061719687cc9315000168d93d5062cc94100716597505cc21c80df45e97ccb654c5100071a5c86518a304400149d93102760c54000647617741cd214c00154d930857518d21004b6a4087951630840185d85d8c7250d2100437a5f835912144001c4d315d562108310052765030dcd61c80014ae9298c74486100059364a319d4624c401cc873d4062485100042fa63435c662d00014ad9418372581310051765780dd9320c8018ad3221d64484300060fe19645d4420c4014cc935c87258440004a765280dd76348401a6b9061770988310053324964dcd2144001a5481595634c7200051ee59531c152d0401c8f64d8e7290d21006a3611629c2320c4014789061476
  | 11 => 0x142282a0c2014528530160240880002e000010050003a40028400002c0700000013c010090020002c00201ccf41c80c0000003081801000c008521722f40681800800c010090400740901e00c0000001e000000000eb052000088640000440086f0160d89e01603e2680d8c20a60415280100a0000080300200c02802022518038430000100580002c008000000001607b805006088350fd2ac014998022440107880210a0047d8010ff0a80201300042c010070b44f8100c707a060000000000000b8700000005584d006000000000200540b00002e1c4000270300000c00404c05c0a00200806000801000030028000780040800104a7501000030e0480007901a009aa00500407c1982002a2181507c0142780a80a29e0cc0a00000c378e41030546e45e02531a04d2e800380000000010320003f8020320084b00302000001000026054118040000c0008680080000b80701a358000000280000081f002004010c50043c4120ab09000000000000000058140000001180001e03000030006058000021b00000389b0500200f00035624400889004060011c10020a00003100800c1f80518c06c040060543c40005e000000fb81b0220389008f070000000091ac0d4fe816000010000180520540100000c36c0a00e0020006c80d0fc0501081215005d068000120601180405a001180000203f00c00300001c0382c01e000000040000400200801606c05015026008048ec0022d40780a060004000071e20640b0010000c81200001e03000000040
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x82c000c08230000108204038012b4800030400000002870000080000800030ca000001000004273523a904a0a808800380c651cc8250521500012c8d0920aa0e690a8000c0b66074140625493100445b5232904a0a42a00035207524941485404400101ed48cac388418a8000d12655901cc62485100068c32ea90a0b0843900033808324941485404400181d08330328e4a0a8000a2668084e0d7198840005489429930a212c2190024c5a91cc825852110001454512e8c00e8b086400a83291216147258c2100652322c0100326c690802c0ca44857558c3208401a154b8e1aa0c4a928200a8a289416143258041006851284830a392c898802c52a60c5531c1524c40142653a62c28e8b106200ca4645802006418d2100515144ba3003a2c3298038c183604621c1524c401948c8f01406c831a420081e2a1951897018543007060cac3a2128884a000315251660501cd2144001826cc32a398c490a2000b0368c215d46418d2100485b52328e599282a0002951a80c5531c1524c401c883a906a0a42a022000a86ea14354c4318152005923403a0e6b0a4220002078a76548250d60104014c8d0d0039c8490a8000a2668084e0d7198b430054194690b0a392c81080284ca84857558c4208401264d48e6280c490a2000b0369c215d46418d21
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x4521ba1d49250521501100071007520c92505215011000500db9194732094148540
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x28407287520c925052150110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x94e
  | 2 => 0x150e
  | 3 => 0x154e
  | 4 => 0xb4e
  | 5 => 0x16ce
  | 6 => 0xb8e
  | 7 => 0x184e
  | 8 => 0x3ce
  | 9 => 0x15ce
  | 10 => 0x40e
  | 11 => 0x160e
  | 12 => 0x3c9
  | 13 => 0x4c
  | 14 => 0x15c9
  | 15 => 0x40c
  | 16 => 0x58a
  | 17 => 0x94c
  | 18 => 0xb09
  | 19 => 0xb0c
  | 20 => 0x1549
  | 21 => 0x154c
  | 22 => 0xb49
  | 23 => 0x16c9
  | 24 => 0xb8c
  | 25 => 0x3c956
  | 26 => 0xcc9
  | 27 => 0xcc956
  | 28 => 0x15c956
  | 29 => 0x1709
  | 30 => 0x170956
  | 31 => 0xd0c
  | 32 => 0x160c
  | 33 => 0x209
  | 34 => 0x1409
  | 35 => 0xca
  | 36 => 0x249
  | 37 => 0x1449
  | 38 => 0x10a
  | 39 => 0x180a
  | 40 => 0x134a
  | 41 => 0x124c
  | 42 => 0x124e
  | 43 => 0x184c
  | 44 => 0x3d256
  | 45 => 0xcd256
  | 46 => 0x15d256
  | 47 => 0x171256
  | 48 => 0x188c
  | 49 => 0x138c
  | 50 => 0x20c
  | 51 => 0x8c
  | 52 => 0x140c
  | 53 => 0x24096
  | 54 => 0xb4096
  | 55 => 0x144096
  | 56 => 0x16c096
  | 57 => 0x150c
  | 58 => 0x28c
  | 59 => 0x98c
  | 60 => 0x128c
  | 61 => 0x25516
  | 62 => 0xb5516
  | 63 => 0x145516
  | 64 => 0x16d516
  | 65 => 0x148c
  | 66 => 0x168a
  | 67 => 0x10c
  | 68 => 0xa0c
  | 69 => 0x180c
  | 70 => 0x130c
  | 71 => 0xa4c
  | 72 => 0x134c
  | 73 => 0x164c
  | 74 => 0x104c
  | 75 => 0x194c
  | 76 => 0xbcc
  | 77 => 0x16d556
  | 78 => 0x15d556
  | 79 => 0x15c256
  | 80 => 0x40256
  | 81 => 0x160256
  | 82 => 0xccb56
  | 83 => 0x170b56
  | 84 => 0x40b56
  | 85 => 0x160b56
  | 86 => 0xd4c
  | 87 => 0x14cc
  | 88 => 0x3d456
  | 89 => 0x15d456
  | 90 => 0x41456
  | 91 => 0x161456
  | 92 => 0xcd6d6
  | 93 => 0x416d6
  | 94 => 0x1616d6
  | 95 => 0x3cb96
  | 96 => 0xccb96
  | 97 => 0x15cb96
  | 98 => 0x170b96
  | 99 => 0x3d856
  | 100 => 0xcd856
  | 101 => 0x15d856
  | 102 => 0x171856
  | 103 => 0x8e
  | 104 => 0x19cc
  | 105 => 0x44c
  | 106 => 0x1a0c
  | 107 => 0x74c
  | 108 => 0x1a8c
  | 109 => 0x160956
  | 110 => 0x943d6
  | 111 => 0x1343d2
  | 112 => 0x94cd6
  | 113 => 0x955d6
  | 114 => 0x1355d2
  | 115 => 0x95716
  | 116 => 0x94d16
  | 117 => 0x95616
  | 118 => 0x135612
  | 119 => 0x14092
  | 120 => 0xe8956
  | 121 => 0x94e96
  | 122 => 0x178956
  | 123 => 0x95796
  | 124 => 0x41256
  | 125 => 0x150256
  | 126 => 0x150b56
  | 127 => 0x151456
  | 128 => 0x1516d6
  | 129 => 0xb9516
  | 130 => 0x150b96
  | 131 => 0x151496
  | 132 => 0x15512
  | 133 => 0xcc3d1
  | 134 => 0xe9516
  | 135 => 0x150e96
  | 136 => 0x179516
  | 137 => 0x151796
  | 138 => 0x168b96
  | 139 => 0x169616
  | 140 => 0x3d352
  | 141 => 0x15d352
  | 142 => 0x41352
  | 143 => 0x198c
  | 144 => 0x24416
  | 145 => 0x25616
  | 146 => 0xb5716
  | 147 => 0x8b56
  | 148 => 0x16cb56
  | 149 => 0x96d6
  | 150 => 0x1556d6
  | 151 => 0xb8cd6
  | 152 => 0xb9716
  | 153 => 0x151856
  | 154 => 0x9856
  | 155 => 0x1443d6
  | 156 => 0x1455d6
  | 157 => 0x1843d6
  | 158 => 0x1855d6
  | 159 => 0x94416
  | 160 => 0x94596
  | 161 => 0x958d6
  | 162 => 0x58096
  | 163 => 0x18c096
  | 164 => 0x150596
  | 165 => 0x1518d6
  | 166 => 0x143d2
  | 167 => 0x155d2
  | 168 => 0x161352
  | 169 => 0x3ccd1
  | 170 => 0xb4416
  | 171 => 0x144416
  | 172 => 0x16c416
  | 173 => 0x8256
  | 174 => 0x15612
  | 175 => 0x9796
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 10 => 1
  | 9 => 50
  | 8 => 980
  | 7 => 6938
  | 6 => 6558
  | 5 => 1279
  | 4 => 44
  | 3 => 3
  | 2 => 1
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
  | 9 => 2*((h/23+packedAt gbK9 (1300+(h % 23)*6) 6) % 50)
  | 8 => 2*((h/375+packedAt gbK8 (36260+(h % 375)*10) 10) % 980)
  | 7 => 2*((h/2354+packedAt gbK7 (333024+(h % 2354)*13) 13) % 6938)
  | 6 => 2*((h/2186+packedAt gbK6 (386922+(h % 2186)*13) 13) % 6558)
  | 5 => 2*((h/461+packedAt gbK5 (89530+(h % 461)*11) 11) % 1279)
  | 4 => 2*((h/49+packedAt gbK4 (3564+(h % 49)*6) 6) % 44)
  | 3 => 2*((h/8+packedAt gbK3 (276+(h % 8)*2) 2) % 3)
  | 2 => 2*((h/1+packedAt gbK2 (103+(h % 1)*1) 1) % 1)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffff0fc07c0f83ff0ffc03c003634cfe3277cc
  | 1 => 0x7803f0007ffffc0ff07fffffc4bcb3303f88ff
  | 2 => 0x8003ffff800fffffff8003fff8c0c3c3c3ff0f
  | 3 => 0x3fffffff0000ffffffc003f00fc03fc0ff0
  | 4 => 0x3fffffffffff0000000003fff0003fff000
  | 5 => 0xfffc000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0xa87b02c41d83a19704e41a41812104563233cc
  | 1 => 0x308920002494a48110294a94802c1130168055
  | 2 => 0x110555880094a2aa900212b18c0c2c0c15d0a
  | 3 => 0x22299ad4b20010cce52b0022f00ec03680ea0
  | 4 => 0x2443ee3673ce73c00460c20c37f70003bfe000
  | 5 => 0x4780003802004200880300303edafba8000000
  | _ => 0
def gbRaw : List Sig := (rawDecor 63 gbPos gbNeg).map Prod.fst
def gbPools : List BoundPool := [(0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555, 7, 0, gbRaw),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 6, 0, gbRaw),(0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333, 7, 0, gbRaw),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 5, 0, gbRaw),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 6, 0, gbRaw),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 7, 0, gbRaw),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 5, 0, gbRaw),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff, 6, 0, gbRaw),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 6, 0, gbRaw),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff, 8, 0, gbRaw),(0x55550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555000055550000, 5, 0, gbRaw),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 5, 0, gbRaw),(0x555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555, 5, 0, gbRaw),(0x55555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000, 6, 0, gbRaw),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 5, 0, gbRaw),(0x30303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030, 5, 0, gbRaw),(0x33003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300, 4, 0, gbRaw),(0x33330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333000033330000, 4, 0, gbRaw),(0x333333330000000033333333000000003333333300000000333333330000000033333333000000003333333300000000333333330000000033333333, 5, 0, gbRaw),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000, 4, 0, gbRaw),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 5, 0, gbRaw),(0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff, 5, 0, gbRaw),(0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000, 5, 0, gbRaw)]
def gbAtlas : Atlas := ⟨10,rawDecor 63 gbPos gbNeg, 0xfeeeeeeafce0ecc0feeeeeeafce0ecc0feeeeeeafce0ecc0feeeeeeafce0ecc0feeeeeeafce0ecc0feeeeeeafce0ecc0feeeeeeafce0ecc0feeeeeeafce0ecc0, gbN, gbR, gbH, gbI, gbPools⟩
end PEqualNP.Outside.L_meta_37247
namespace PEqualNP.Outside.L_meta_37247
open PEqualNP.Outside.L_meta_37247.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 26 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_96 : Interval s0Atlas 4 96 38 := block_range (n:=38) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 134 := (concat bs0_4_0 bs0_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 48 := block_range (n:=48) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 48 := bs0_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 1 := bs0_6_0
theorem alls0 : ∀ k ≤ 6, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
  · exact alls0_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_2_0 : Interval s1Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 4 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 24 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_96 : Interval s1Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 117 := (concat bs1_4_0 bs1_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 46 := block_range (n:=46) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 46 := bs1_5_0
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
theorem bs2_4_0 : Interval s2Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 1 := bs2_4_0
theorem alls2 : ∀ k ≤ 4, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_4 i (by omega) hi
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
theorem bs4_4_0 : Interval s4Atlas 4 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 2 := bs4_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 1 := bs4_5_0
theorem alls4 : ∀ k ≤ 5, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 10 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_96 : Interval s5Atlas 3 96 16 := block_range (n:=16) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 112 := (concat bs5_3_0 bs5_3_96)
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
theorem bs5_4_1344 : Interval s5Atlas 4 1344 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 1345 := (concat (concat (concat bs5_4_0 (concat bs5_4_96 bs5_4_192)) (concat (concat bs5_4_288 bs5_4_384) (concat bs5_4_480 bs5_4_576))) (concat (concat (concat bs5_4_672 bs5_4_768) (concat bs5_4_864 bs5_4_960)) (concat (concat bs5_4_1056 bs5_4_1152) (concat bs5_4_1248 bs5_4_1344))))
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
theorem bs5_5_960 : Interval s5Atlas 5 960 57 := block_range (n:=57) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 1017 := (concat (concat (concat bs5_5_0 bs5_5_96) (concat bs5_5_192 (concat bs5_5_288 bs5_5_384))) (concat (concat bs5_5_480 (concat bs5_5_576 bs5_5_672)) (concat bs5_5_768 (concat bs5_5_864 bs5_5_960))))
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
theorem bq1_3_0 : Interval q1Atlas 3 0 9 := block_range (n:=9) (by decide +kernel)
theorem allq1_3 : Interval q1Atlas 3 0 9 := bq1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq1_4_0 : Interval q1Atlas 4 0 14 := block_range (n:=14) (by decide +kernel)
theorem allq1_4 : Interval q1Atlas 4 0 14 := bq1_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq1_5_0 : Interval q1Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq1_5 : Interval q1Atlas 5 0 1 := bq1_5_0
theorem allq1 : ∀ k ≤ 5, ∀ i < count q1Atlas k, checkRow q1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq1_3 i (by omega) hi
  · exact allq1_4 i (by omega) hi
  · exact allq1_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_3_0 : Interval q4Atlas 3 0 9 := block_range (n:=9) (by decide +kernel)
theorem allq4_3 : Interval q4Atlas 3 0 9 := bq4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_4_0 : Interval q4Atlas 4 0 14 := block_range (n:=14) (by decide +kernel)
theorem allq4_4 : Interval q4Atlas 4 0 14 := bq4_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_5_0 : Interval q4Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq4_5 : Interval q4Atlas 5 0 1 := bq4_5_0
theorem allq4 : ∀ k ≤ 5, ∀ i < count q4Atlas k, checkRow q4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq4_3 i (by omega) hi
  · exact allq4_4 i (by omega) hi
  · exact allq4_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq6_4_0 : Interval q6Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq6_4 : Interval q6Atlas 4 0 1 := bq6_4_0
theorem allq6 : ∀ k ≤ 4, ∀ i < count q6Atlas k, checkRow q6Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq6_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq8_4_0 : Interval q8Atlas 4 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq8_4 : Interval q8Atlas 4 0 4 := bq8_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq8_5_0 : Interval q8Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq8_5 : Interval q8Atlas 5 0 1 := bq8_5_0
theorem allq8 : ∀ k ≤ 5, ∀ i < count q8Atlas k, checkRow q8Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq8_4 i (by omega) hi
  · exact allq8_5 i (by omega) hi
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
theorem bq13_3_0 : Interval q13Atlas 3 0 39 := block_range (n:=39) (by decide +kernel)
theorem allq13_3 : Interval q13Atlas 3 0 39 := bq13_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq13_4_0 : Interval q13Atlas 4 0 24 := block_range (n:=24) (by decide +kernel)
theorem allq13_4 : Interval q13Atlas 4 0 24 := bq13_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq13_5_0 : Interval q13Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq13_5 : Interval q13Atlas 5 0 1 := bq13_5_0
theorem allq13 : ∀ k ≤ 5, ∀ i < count q13Atlas k, checkRow q13Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq13_3 i (by omega) hi
  · exact allq13_4 i (by omega) hi
  · exact allq13_5 i (by omega) hi
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
theorem bq18_2_0 : Interval q18Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq18_2 : Interval q18Atlas 2 0 3 := bq18_2_0
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
theorem bq20_2_0 : Interval q20Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq20_2 : Interval q20Atlas 2 0 3 := bq20_2_0
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
theorem bq21_2_0 : Interval q21Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq21_2 : Interval q21Atlas 2 0 4 := bq21_2_0
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
theorem bgb_2_0 : Interval gbAtlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 1 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 3 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 44 := block_range (n:=44) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 44 := bgb_4_0
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
theorem bgb_5_1248 : Interval gbAtlas 5 1248 31 := block_range (n:=31) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1279 := (concat (concat (concat bgb_5_0 (concat bgb_5_96 bgb_5_192)) (concat (concat bgb_5_288 bgb_5_384) (concat bgb_5_480 bgb_5_576))) (concat (concat bgb_5_672 (concat bgb_5_768 bgb_5_864)) (concat (concat bgb_5_960 bgb_5_1056) (concat bgb_5_1152 bgb_5_1248))))
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
theorem bgb_6_5760 : Interval gbAtlas 6 5760 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5856 : Interval gbAtlas 6 5856 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5952 : Interval gbAtlas 6 5952 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6048 : Interval gbAtlas 6 6048 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6144 : Interval gbAtlas 6 6144 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6240 : Interval gbAtlas 6 6240 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6336 : Interval gbAtlas 6 6336 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6432 : Interval gbAtlas 6 6432 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6528 : Interval gbAtlas 6 6528 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 6558 := (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 bgb_6_288)) (concat (concat bgb_6_384 bgb_6_480) (concat bgb_6_576 bgb_6_672))) (concat (concat (concat bgb_6_768 bgb_6_864) (concat bgb_6_960 bgb_6_1056)) (concat (concat bgb_6_1152 bgb_6_1248) (concat bgb_6_1344 (concat bgb_6_1440 bgb_6_1536))))) (concat (concat (concat (concat bgb_6_1632 bgb_6_1728) (concat bgb_6_1824 bgb_6_1920)) (concat (concat bgb_6_2016 bgb_6_2112) (concat bgb_6_2208 bgb_6_2304))) (concat (concat (concat bgb_6_2400 bgb_6_2496) (concat bgb_6_2592 bgb_6_2688)) (concat (concat bgb_6_2784 bgb_6_2880) (concat bgb_6_2976 (concat bgb_6_3072 bgb_6_3168)))))) (concat (concat (concat (concat (concat bgb_6_3264 bgb_6_3360) (concat bgb_6_3456 bgb_6_3552)) (concat (concat bgb_6_3648 bgb_6_3744) (concat bgb_6_3840 bgb_6_3936))) (concat (concat (concat bgb_6_4032 bgb_6_4128) (concat bgb_6_4224 bgb_6_4320)) (concat (concat bgb_6_4416 bgb_6_4512) (concat bgb_6_4608 (concat bgb_6_4704 bgb_6_4800))))) (concat (concat (concat (concat bgb_6_4896 bgb_6_4992) (concat bgb_6_5088 bgb_6_5184)) (concat (concat bgb_6_5280 bgb_6_5376) (concat bgb_6_5472 (concat bgb_6_5568 bgb_6_5664)))) (concat (concat (concat bgb_6_5760 bgb_6_5856) (concat bgb_6_5952 bgb_6_6048)) (concat (concat bgb_6_6144 bgb_6_6240) (concat bgb_6_6336 (concat bgb_6_6432 bgb_6_6528)))))))
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
theorem bgb_7_4704 : Interval gbAtlas 7 4704 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_4800 : Interval gbAtlas 7 4800 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_4896 : Interval gbAtlas 7 4896 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_4992 : Interval gbAtlas 7 4992 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_5088 : Interval gbAtlas 7 5088 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_5184 : Interval gbAtlas 7 5184 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_5280 : Interval gbAtlas 7 5280 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_5376 : Interval gbAtlas 7 5376 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_5472 : Interval gbAtlas 7 5472 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_5568 : Interval gbAtlas 7 5568 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_5664 : Interval gbAtlas 7 5664 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_5760 : Interval gbAtlas 7 5760 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_5856 : Interval gbAtlas 7 5856 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_5952 : Interval gbAtlas 7 5952 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_6048 : Interval gbAtlas 7 6048 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_6144 : Interval gbAtlas 7 6144 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_6240 : Interval gbAtlas 7 6240 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_6336 : Interval gbAtlas 7 6336 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_6432 : Interval gbAtlas 7 6432 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_6528 : Interval gbAtlas 7 6528 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_6624 : Interval gbAtlas 7 6624 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_6720 : Interval gbAtlas 7 6720 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_6816 : Interval gbAtlas 7 6816 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_6912 : Interval gbAtlas 7 6912 26 := block_range (n:=26) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 6938 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_96) (concat bgb_7_192 bgb_7_288)) (concat (concat bgb_7_384 bgb_7_480) (concat bgb_7_576 (concat bgb_7_672 bgb_7_768)))) (concat (concat (concat bgb_7_864 bgb_7_960) (concat bgb_7_1056 bgb_7_1152)) (concat (concat bgb_7_1248 bgb_7_1344) (concat bgb_7_1440 (concat bgb_7_1536 bgb_7_1632))))) (concat (concat (concat (concat bgb_7_1728 bgb_7_1824) (concat bgb_7_1920 bgb_7_2016)) (concat (concat bgb_7_2112 bgb_7_2208) (concat bgb_7_2304 (concat bgb_7_2400 bgb_7_2496)))) (concat (concat (concat bgb_7_2592 bgb_7_2688) (concat bgb_7_2784 bgb_7_2880)) (concat (concat bgb_7_2976 bgb_7_3072) (concat bgb_7_3168 (concat bgb_7_3264 bgb_7_3360)))))) (concat (concat (concat (concat (concat bgb_7_3456 bgb_7_3552) (concat bgb_7_3648 bgb_7_3744)) (concat (concat bgb_7_3840 bgb_7_3936) (concat bgb_7_4032 (concat bgb_7_4128 bgb_7_4224)))) (concat (concat (concat bgb_7_4320 bgb_7_4416) (concat bgb_7_4512 bgb_7_4608)) (concat (concat bgb_7_4704 bgb_7_4800) (concat bgb_7_4896 (concat bgb_7_4992 bgb_7_5088))))) (concat (concat (concat (concat bgb_7_5184 bgb_7_5280) (concat bgb_7_5376 bgb_7_5472)) (concat (concat bgb_7_5568 bgb_7_5664) (concat bgb_7_5760 (concat bgb_7_5856 bgb_7_5952)))) (concat (concat (concat bgb_7_6048 bgb_7_6144) (concat bgb_7_6240 (concat bgb_7_6336 bgb_7_6432))) (concat (concat bgb_7_6528 bgb_7_6624) (concat bgb_7_6720 (concat bgb_7_6816 bgb_7_6912)))))))
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
theorem bgb_8_960 : Interval gbAtlas 8 960 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 980 := (concat (concat (concat bgb_8_0 bgb_8_96) (concat bgb_8_192 (concat bgb_8_288 bgb_8_384))) (concat (concat bgb_8_480 (concat bgb_8_576 bgb_8_672)) (concat bgb_8_768 (concat bgb_8_864 bgb_8_960))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_9_0 : Interval gbAtlas 9 0 50 := block_range (n:=50) (by decide +kernel)
theorem allgb_9 : Interval gbAtlas 9 0 50 := bgb_9_0
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 7 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 18, 50)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 32, 33),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 34, 50),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 20, 21),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 5, 21)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq1 (cert : Complete q1Atlas) : Lower true (roots q1Atlas) (target q1Atlas) 6 := by
  have ready : Ready q1Atlas (asRow q1Pos) (asRow q1Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 0, 32)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq4 (cert : Complete q4Atlas) : Lower true (roots q4Atlas) (target q4Atlas) 6 := by
  have ready : Ready q4Atlas (asRow q4Pos) (asRow q4Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 0, 2),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq6 (cert : Complete q6Atlas) : Lower true (roots q6Atlas) (target q6Atlas) 5 := by
  have ready : Ready q6Atlas (asRow q6Pos) (asRow q6Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 0, 2),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq8 (cert : Complete q8Atlas) : Lower true (roots q8Atlas) (target q8Atlas) 6 := by
  have ready : Ready q8Atlas (asRow q8Pos) (asRow q8Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq10 (cert : Complete q10Atlas) : Lower true (roots q10Atlas) (target q10Atlas) 5 := by
  have ready : Ready q10Atlas (asRow q10Pos) (asRow q10Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq11 (cert : Complete q11Atlas) : Lower true (roots q11Atlas) (target q11Atlas) 5 := by
  have ready : Ready q11Atlas (asRow q11Pos) (asRow q11Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 0, 32)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq12 (cert : Complete q12Atlas) : Lower true (roots q12Atlas) (target q12Atlas) 5 := by
  have ready : Ready q12Atlas (asRow q12Pos) (asRow q12Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 12, 28)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq13 (cert : Complete q13Atlas) : Lower true (roots q13Atlas) (target q13Atlas) 6 := by
  have ready : Ready q13Atlas (asRow q13Pos) (asRow q13Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq14 (cert : Complete q14Atlas) : Lower true (roots q14Atlas) (target q14Atlas) 5 := by
  have ready : Ready q14Atlas (asRow q14Pos) (asRow q14Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 4, 20)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq15 (cert : Complete q15Atlas) : Lower true (roots q15Atlas) (target q15Atlas) 5 := by
  have ready : Ready q15Atlas (asRow q15Pos) (asRow q15Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq16 (cert : Complete q16Atlas) : Lower true (roots q16Atlas) (target q16Atlas) 4 := by
  have ready : Ready q16Atlas (asRow q16Pos) (asRow q16Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq17 (cert : Complete q17Atlas) : Lower true (roots q17Atlas) (target q17Atlas) 4 := by
  have ready : Ready q17Atlas (asRow q17Pos) (asRow q17Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq18 (cert : Complete q18Atlas) : Lower true (roots q18Atlas) (target q18Atlas) 5 := by
  have ready : Ready q18Atlas (asRow q18Pos) (asRow q18Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 5, 21)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq19 (cert : Complete q19Atlas) : Lower true (roots q19Atlas) (target q19Atlas) 4 := by
  have ready : Ready q19Atlas (asRow q19Pos) (asRow q19Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 32, 33),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq20 (cert : Complete q20Atlas) : Lower true (roots q20Atlas) (target q20Atlas) 5 := by
  have ready : Ready q20Atlas (asRow q20Pos) (asRow q20Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 0, 2),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq21 (cert : Complete q21Atlas) : Lower true (roots q21Atlas) (target q21Atlas) 5 := by
  have ready : Ready q21Atlas (asRow q21Pos) (asRow q21Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq22 (cert : Complete q22Atlas) : Lower true (roots q22Atlas) (target q22Atlas) 5 := by
  have ready : Ready q22Atlas (asRow q22Pos) (asRow q22Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) (pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p) : Lower true (roots gbAtlas) (target gbAtlas) 11 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact pv
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeeeeeafce0ecc0feeeeeeafce0ecc0feeeeeeafce0ecc0feeeeeeafce0ecc0feeeeeeafce0ecc0feeeeeeafce0ecc0feeeeeeafce0ecc0feeeeeeafce0ecc0
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certq1 : Complete q1Atlas) (certq4 : Complete q4Atlas) (certq6 : Complete q6Atlas) (certq8 : Complete q8Atlas) (certq10 : Complete q10Atlas) (certq11 : Complete q11Atlas) (certq12 : Complete q12Atlas) (certq13 : Complete q13Atlas) (certq14 : Complete q14Atlas) (certq15 : Complete q15Atlas) (certq16 : Complete q16Atlas) (certq17 : Complete q17Atlas) (certq18 : Complete q18Atlas) (certq19 : Complete q19Atlas) (certq20 : Complete q20Atlas) (certq21 : Complete q21Atlas) (certq22 : Complete q22Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 11 := by
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
  have q0 : Slice true (roots gbAtlas) (target gbAtlas) (0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555 : Sig) 7 :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have q1 : Slice true (roots gbAtlas) (target gbAtlas) (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : Sig) 6 :=
    slice_correct (ms:=fixRows 0 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq1 certq1)
  have q2 : Slice true (roots gbAtlas) (target gbAtlas) (0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333 : Sig) 7 :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have q3 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f : Sig) 5 :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have q4 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : Sig) 6 :=
    slice_correct (ms:=fixRows 0 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq4 certq4)
  have q5 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff : Sig) 7 :=
    slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
  have q6 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00 : Sig) 5 :=
    slice_correct (ms:=fixRows 0 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq6 certq6)
  have q7 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff : Sig) 6 :=
    slice_correct (ms:=fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds4 certs4)
  have q8 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000 : Sig) 6 :=
    slice_correct (ms:=fixRows 0 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq8 certq8)
  have q9 : Slice true (roots gbAtlas) (target gbAtlas) (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff : Sig) 8 :=
    slice_correct (ms:=fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds5 certs5)
  have q10 : Slice true (roots gbAtlas) (target gbAtlas) (0x55550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555000055550000 : Sig) 5 :=
    slice_correct (ms:=fixRows 1 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq10 certq10)
  have q11 : Slice true (roots gbAtlas) (target gbAtlas) (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa : Sig) 5 :=
    slice_correct (ms:=fixRows 16 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq11 certq11)
  have q12 : Slice true (roots gbAtlas) (target gbAtlas) (0x555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555 : Sig) 5 :=
    slice_correct (ms:=fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq12 certq12)
  have q13 : Slice true (roots gbAtlas) (target gbAtlas) (0x55555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000 : Sig) 6 :=
    slice_correct (ms:=fixRows 1 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq13 certq13)
  have q14 : Slice true (roots gbAtlas) (target gbAtlas) (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa : Sig) 5 :=
    slice_correct (ms:=fixRows 32 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq14 certq14)
  have q15 : Slice true (roots gbAtlas) (target gbAtlas) (0x30303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030 : Sig) 5 :=
    slice_correct (ms:=fixRows 2 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq15 certq15)
  have q16 : Slice true (roots gbAtlas) (target gbAtlas) (0x33003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300 : Sig) 4 :=
    slice_correct (ms:=fixRows 2 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq16 certq16)
  have q17 : Slice true (roots gbAtlas) (target gbAtlas) (0x33330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333000033330000 : Sig) 4 :=
    slice_correct (ms:=fixRows 2 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq17 certq17)
  have q18 : Slice true (roots gbAtlas) (target gbAtlas) (0x333333330000000033333333000000003333333300000000333333330000000033333333000000003333333300000000333333330000000033333333 : Sig) 5 :=
    slice_correct (ms:=fixRows 34 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq18 certq18)
  have q19 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000 : Sig) 4 :=
    slice_correct (ms:=fixRows 4 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq19 certq19)
  have q20 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0 : Sig) 5 :=
    slice_correct (ms:=fixRows 32 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq20 certq20)
  have q21 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff : Sig) 5 :=
    slice_correct (ms:=fixRows 48 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq21 certq21)
  have q22 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000 : Sig) 5 :=
    slice_correct (ms:=fixRows 32 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq22 certq22)
  have pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p :=
    List.forall_iff_forall_mem.1 (show List.Forall (fun p => ValidPool true (roots gbAtlas) (target gbAtlas) p) gbPools from ⟨build_valid q0 [] rfl, build_valid q1 [] rfl, build_valid q2 [] rfl, build_valid q3 [] rfl, build_valid q4 [] rfl, build_valid q5 [] rfl, build_valid q6 [] rfl, build_valid q7 [] rfl, build_valid q8 [] rfl, build_valid q9 [] rfl, build_valid q10 [] rfl, build_valid q11 [] rfl, build_valid q12 [] rfl, build_valid q13 [] rfl, build_valid q14 [] rfl, build_valid q15 [] rfl, build_valid q16 [] rfl, build_valid q17 [] rfl, build_valid q18 [] rfl, build_valid q19 [] rfl, build_valid q20 [] rfl, build_valid q21 [] rfl, build_valid q22 [] rfl⟩)
  have low := boundgb certgb allCuts pv
  have lift := lift_ok (u:=true) (ms:=fixRows 0 0) (raw:=fullRoots) (T:=fullWord) (xs:=[]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 0 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277071594 * 2 ^ 32 + 4242599104) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37247.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,4]⟩,⟨.or,[3,4]⟩,⟨.or,[2,3]⟩,⟨.and,[2,3]⟩,⟨.or,[0,1]⟩,⟨.or,[9,10]⟩,⟨.and,[1,8]⟩,⟨.and,[2,7]⟩,⟨.or,[5,13]⟩,⟨.and,[6,14]⟩,⟨.or,[12,15]⟩,⟨.and,[11,16]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,17⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 11) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071594 * 2 ^ 32 + 4242599104) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071594 * 2 ^ 32 + 4242599104) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37247

open PEqualNP.Outside.L_meta_37247 in
theorem PEqualNP.Outside.L_meta_37247 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071594 * 2 ^ 32 + 4242599104) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071594 * 2 ^ 32 + 4242599104) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allq1 allq4 allq6 allq8 allq10 allq11 allq12 allq13 allq14 allq15 allq16 allq17 allq18 allq19 allq20 allq21 allq22 allgb)
