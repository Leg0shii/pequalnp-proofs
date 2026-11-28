import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, children closed at the parent by
-- restriction pools (closeChild of the model), and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37017.Model
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


end PEqualNP.Outside.L_meta_37017.Model

namespace PEqualNP.Outside.L_meta_37017
open PEqualNP.Outside.L_meta_37017.Model
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

def SBf (j : Nat) : Nat := [7, 7, 6, 5, 7, 8].getD j 0

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

end PEqualNP.Outside.L_meta_37017

namespace PEqualNP.Outside.L_meta_37017
open PEqualNP.Outside.L_meta_37017.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x14f8060020004400000800900c2200300009380000001fe10ff42fd41fd40fd30fe42ff32bf41fe20dc32bc40fe32ff41fe40de32fc40fe41fe31fc41fe21ff20fe30fd42fc32be40bc42fc21ff30fc42fd43fd31fd20fd10bf43ff31fc10fd21fc43ff43bd41fd32fc20fc30bd43ff10fe43ff21be42fc31ff40
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x1030000000300000200002d0501848d00000000000181808181028000830300080000060080000200010003808000079d8a800080010100028000808f858100ba008001020517838081030000030015840084821b001d980000071cb00080014f94840ae29a855c534827aa2216750c319faa2413e540cb3a87195b94a319e2a2413c544427aa918db14943b7290213d5390abea6884fd5020aea98813e509027aa898e7550329e2a6435e538827ca1a0cf953319eaa4433e548833884194f14941bba8a413e544c67aa998cf552439e2a4216c524c27ea990cfd51219e2a4653f548427aa8185b149109eaa6659f5350e7ca1a1cf141439ea9e83cc32486e8a290678ca40ce190813f5150e7ea6a0cf940429f2a063cc32c8678a4a1e750d309e2a2653f548c278a8985754f42af29e839f430ca7ca5204f95010cea1865cf420cb6ea2a0cf55310e6190419e53102bca419678cb419f296833e54c827aa6215714d109f2808178504867aa810dbd49309e282835e53d0b3c64a0d714d21d621065cc328831884194754f419e2a0413d5490774a0204f5532096292873e54cca78a890d754c10cea98813e548c67aa3204fd51309ea88815f534867ca820ddd45309faa2213d5190a7ca5a1e7d5232aea9c419e428cb3865204f950219f2a6613d531023aa6205794e21d621665ac5250e7aa818ded4121afa9a419e53d067ca910e7908329f284853d51d0f3a8798670cb41af29465af5250edaa518d7d4d42cea1c639c428ca7ca4214f54e40b6a90213c548c27aa9105bd4943aea9c433f544ca7ca821dd145309faa4659c3250738a9194f55032af298813d540433ca8194f95310e6210653d54cc39ca419678c8409f2a0615e53042dea4885754f41cea9e839f438cb5ca4214f94a42
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x40a005410000000440020800c010102108408800000e04010016400301200201d011c318953d068c6250d30a3189438c68e6010832c3150320820c6254c40a398b548ca1d6395310c3d8c5250f0c520c941c550c514c30f6254f4187189531030d4394a318758e5090a1d650c8408b189531021f6354642a5584548cb0e520ca40c3189531028d61108328758e540868e6290832a3988548cb0f53149438e181544c62d6510832a3d94420cb4832141218b18953d070c540c9218758c540824c6254f41c3950328828c6254f418758c54c861d63141418b189544c70c540cb21a3189430c61f658c8408758e54c823561152328318953d070f6254c4093189531028c6250f30a3594420ca2e62d523087195434c21d6315210a3189531021f658cb418759432d063561150208758e544c70d43149308718953d061f6354640
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x814400228338ec629287215c7651083281aec2a064105047250c514c282b88a819041031c96314141818e4b18a90840c7258e54c4206392c72a043039cb6354640
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
  | 4 => 2*((h/97+packedAt s0K4 (4455+(h % 97)*8) 8) % 165)
  | 3 => 2*((h/48+packedAt s0K3 (2280+(h % 48)*6) 6) % 60)
  | 2 => 2*((h/10+packedAt s0K2 (490+(h % 10)*4) 4) % 10)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffff81fffffff81ffffffff03ffffe3ff1ff
  | 2 => 0xf03ffffe07ffffffe07fe07fffc1ffffce3e3f
  | 3 => 0xffc07ffff80fe07fff83ff81fffe0f01f3cfcc
  | 4 => 0x7ffffff0007ffffc0001fffff001fc0ff0
  | 5 => 0xffff80000000007ffffffffe00000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x1105108c412248100594a8a25012915414d0d5
  | 2 => 0x248a29103244942960294454a6412aa8ca262a
  | 3 => 0x42934a2490e904caaa8275113aa40c0d634b4c
  | 4 => 0xb2c74492481d974d34c1861cd39c031bc0db0
  | 5 => 0x8c307871c70e1e7f1c739e780e3188c1ffb000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0, s0N, s0R, (fun _ _ => 0), s0I, []⟩
end PEqualNP.Outside.L_meta_37017
namespace PEqualNP.Outside.L_meta_37017
open PEqualNP.Outside.L_meta_37017.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0xa00404004000000000018000208a05400200000001f0c104014054000100014008608024bfe10ff31fd30fd32ff41fc32fc40bf43fd40fc41fd21fe21fe41be40fc30fe20fe32fc43ff20ff21bd42fc20fd10fe31ff42bc40fd20ff10fd31ff40fe42fd41ff43fe30fe43fc21be41fe40ff32fc10fd43fd42ff30bc41bd43bf42fc42fc31
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x3060883014e09814185474000000000c8800014040149400040810102408c0000060581c142c0000740c1800900818f4000c04700000040000140019153000100118f4300c001edca4184f54a40da20e213e50d0ee8a2a1ddd45429ea988375510c27aa7204f152219eaa0653e54c42eaa2104fd4943da20a213e54c827ea8984f95321da28a85b75150abaa6104f54c409f2a4653f544c67aa5a1ed104219eaa6413d544ca7aa9195d14530ba28a41775148278a2a15714d209b28c813e5484278a9184f55331bb28e65cd320ca7ca320cf553309faa2213e51d0f688390ed104319e28a873d54842eea2a1d794f21baa8e656e52cc67ca120cf550309faa463345150e7aa9214f95042da20e633d53d0a7ca821db54b319f2a6613e540c27ca1206d94441baa8c813f548c368a2a1cfd52219f280835f5348268a2a15b149109ea9c833d5408678a898cf950319e2a0216f524c27ca81057d4d10af298413c548c67aa990cfd5121dd280813e51d0a7aa4204f953319faa2413c5050a7ea8085b548309eaa6213c544867ca810cf15130db28c8177514c2d8a4985d944309eaa48776519033ea6a1dbd4910d7a92853e544ca7ea6a14f953329eaa063b75150ebaa790cf940409f288833f548827aa420cf54a41bb288413c544427aa9995d546329e282873c544827ca1a14f94440ae29a213c548836aa3204f950329eaa0413e51902eca3195d14542
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x2c3a92031c1310006a958841087145310510c994841cc63461553308758c540429563104318b588548c63565104318d185521023461553208e181544ca346154f428d185540ca3661d52208758c548871653107218d98650d0a3661d50108d59441086346154c408d98650d0f2452105108d18552d0e2d62150108d185544ca3661d5230
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 134
  | 3 => 26
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s1K6 (i*5) 5
  | 5 => packedAt s1K5 (i*16) 16
  | 4 => packedAt s1K4 (i*27) 27
  | 3 => packedAt s1K3 (i*38) 38
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt s1K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/51+packedAt s1K5 (768+(h % 51)*6) 6) % 48)
  | 4 => 2*((h/72+packedAt s1K4 (3618+(h % 72)*8) 8) % 134)
  | 3 => 2*((h/15+packedAt s1K3 (988+(h % 15)*5) 5) % 26)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfffff83fffffffc0ffffffff81fffffe3ff1ff
  | 2 => 0xe07fffc07e0fc1ff0f83e0fffe1e0781d27ecc
  | 3 => 0xff83ffff800ffffff003ff07ffe007ffe38f0f
  | 4 => 0x3fffffff001fffffc0007fffff801fc0ff0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x21000889100200002284a108802290a404b055
  | 2 => 0x4b199187249492cb05a168d3b214350cd256cc
  | 3 => 0x862aa2120d29315550425a4555404659630b0a
  | 4 => 0x145344244981a5a69968108669996011b80da0
  | 5 => 0x1863873871ce39f8ee739ce071118461ffe000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaaaaa0faaaaa00faaaaaa0faaaaa00faaaaaa0faaaaa00faaaaaa0faaaaa00faaaaaa0faaaaa00faaaaaa0faaaaa00faaaaaa0faaaaa00faaaaaa0faaaaa00, s1N, s1R, (fun _ _ => 0), s1I, []⟩
end PEqualNP.Outside.L_meta_37017
namespace PEqualNP.Outside.L_meta_37017
open PEqualNP.Outside.L_meta_37017.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x8031041000f710bf43bd40bd43bc41f510f421f721be41bc42bf40be42
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x1000c08ea9e81345150ec8a4884754c42
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
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
  | 4 => 2*((h/11+packedAt s2K4 (192+(h % 11)*4) 4) % 12)
  | 3 => 2*((h/15+packedAt s2K3 (108+(h % 15)*2) 2) % 4)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x7ffc1ffffffff03ffffc0ff83fffffe7e31ff
  | 1 => 0xf81ffe03f03f07fc3e07ff07fc3e0781b3cecc
  | 3 => 0xfffffffc003fffffc007ffffffc007ffc3ff0f
  | 4 => 0x1fffffffc007fffff80007fffff801fc0ff0
  | 5 => 0xffe00000000007fffffffff800000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x90444448820841008a494848805294a4161055
  | 1 => 0x32cc8c3926524b2c16c2d943a434350cb2c6cc
  | 3 => 0x4191109068a484554104a2954a804259416b0a
  | 4 => 0x651a21224c06969a6590308673296011e80da0
  | 5 => 0x861c39c38f38e7e3b9e73ce062318461ffb000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeaaee00eeaaaa00eeaaee00eeaaaa00eeaaee00eeaaaa00eeaaee00eeaaaa00eeaaee00eeaaaa00eeaaee00eeaaaa00eeaaee00eeaaaa00eeaaee00eeaaaa00, s2N, s2R, (fun _ _ => 0), s2I, []⟩
end PEqualNP.Outside.L_meta_37017
namespace PEqualNP.Outside.L_meta_37017
open PEqualNP.Outside.L_meta_37017.Model
def s3K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (i*5) 5
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt s3K4 (5+(h % 1)*1) 1) % 1)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x1ffe07fffff81c1fffff03fe0fffff007e73fc
  | 1 => 0xe0fff81f81ffffe0f81ffc1ff0f80fffb38ccf
  | 2 => 0xffffffe001ffffff001fffffff000fffc3ff0f
  | 4 => 0xfffffffe001fffffe0001ffffff001fc0ff0
  | 5 => 0xff00000000001fffffffffe000000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xc22231451041240529272126014a690c16315c
  | 1 => 0x4a6450c832930ca05b09650a90d0aa54b284c5
  | 2 => 0x8488a2034524114b04128a552a0144a9415b0a
  | 4 => 0x14d1049260365a729640c219cca58031e80ea0
  | 5 => 0x18e1c71c79c79f9ce79cf38188c608c1ffe000
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xeaeae0e0eaeac0c0eaeae0e0eaeac0c0eaeae0e0eaeac0c0eaeae0e0eaeac0c0eaeae0e0eaeac0c0eaeae0e0eaeac0c0eaeae0e0eaeac0c0eaeae0e0eaeac0c0, s3N, s3R, (fun _ _ => 0), s3I, []⟩
end PEqualNP.Outside.L_meta_37017
namespace PEqualNP.Outside.L_meta_37017
open PEqualNP.Outside.L_meta_37017.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x2d80410000001802000801c9001000000240082ff42ff32ff31fe31ff41fe30fd30fc43fc41ff43fd40fe42fc30fc32fc31ff20fd21ff40fc42fe32fc10fd10fd42fe21fd20fe10fe41fc20fd31fd43ff10ff21fc40ff30fd41fc21fe20fe40fd32fe43
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xc40002330000020001007c00000400003400000000000000001810000001030010280000001c08d10002c0290082600962009040ba28a6576510c2f6a0994fd5130b6a90617651102f0a0995b14941bb28c417a501067aa918db948309f2a4637a508c67ca9904fd5121af29e4175518827aa8084f55021af298435f53442baa610db14910bba8a6575510c2dca421cf552209f2a4413e540cadea4884f95331bca80436d52cc6dea4a0d754f209e2a24379508c678a8984f55030ae29a21785050edca598d7d4d409f2a0213d54c8278a8885d544409eaa663745150af6a0a1db54843bd280435d5310aeea2a15794c429faa2653e540867aa8194f95030ae29a813f5444278a8995e54041
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 40
  | 4 => 64
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (i*5) 5
  | 5 => packedAt s4K5 (i*16) 16
  | 4 => packedAt s4K4 (i*27) 27
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/27+packedAt s4K5 (640+(h % 27)*6) 6) % 40)
  | 4 => 2*((h/70+packedAt s4K4 (1728+(h % 70)*6) 6) % 64)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x7ff03fffff8307fe0ffc1ff0ffffe018e73fc
  | 1 => 0xf83ffc0fc1ffff83ff07fe0ff0f01ffef38ccf
  | 2 => 0xfffffff001fffffc0007ffffff001fff03ff0f
  | 3 => 0x3ffffffe003ffffff8000fffffe003fc0ff0
  | 5 => 0xffc0000000003ffffffffff000000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x309118a290425014a849d0930194d21886315c
  | 1 => 0x52922864129212816942528510a154a8b284c5
  | 2 => 0xa1245101a524252c1084a52aaa028953015b0a
  | 3 => 0xc52882492034a9ca5290210ccc4b0063580ea0
  | 5 => 0x630e38e39c73e739ce739c0888c1183efe000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeee0eee0eac0eac0eee0eee0eac0eac0eee0eee0eac0eac0eee0eee0eac0eac0eee0eee0eac0eac0eee0eee0eac0eac0eee0eee0eac0eac0eee0eee0eac0eac0, s4N, s4R, (fun _ _ => 0), s4I, []⟩
end PEqualNP.Outside.L_meta_37017
namespace PEqualNP.Outside.L_meta_37017
open PEqualNP.Outside.L_meta_37017.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x3031000400404c000b1ce09e0040801c0543200fc42fe10fc41fc20fd31fd32ff30ff21ff10fc40fc32ff31fe20fc43fc31fc21fe30ff42fd30fe31fc30fd43fe43ff43fe42ff32fd40fe21fd42ff40ff20ff41fd21fe40fe32fe41fc10fd10fd41fd20
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x87fa20842fea8905794c40eea1887be41506faa898cfd5130dea10857e50102f8a610df95230bf28683bd43d03eea2995f15231bea98417d5490fba87987790d30bea94877f514caf8a690df94240faa8c417d52902fca3a05fd5032ef18a63f731c86faa5105d54440df212856d520c2fca2187e90040bf298637d528c3de65197b0c821bba8a857d520c2fca821ef50b41bf29487785050ef8a7887d54440bf2a221f6510c2fca7105f55231fba08437e500cafaa321df95332beaa66574514cafaa9205f55032bea8c41be4350efca210df15132bf298817c54486fca7215f14931bea96877e53c87e86390df54321bea9e857d5110efea690db14931fb90a217d528c7dca5085f14e21bf2a4417c54cc6f8a0a0fdc8621fd180617651882faa121ef55021bb288817e544c3f240105d14542bea8e817e53482faa1995f54610bf28643ee42c83ee21087d4c710bf298417f51483eca2206f95021bf28441f920443da40107e50040be28a617f504c6fea090df54430bf294617e5310afaa718df94642bfaa465bf4210afca110fb8cb20bfaa0617c50487bc64995fd5210ef98461df310c6f8a2a07d54430f2908437e500433a8621dfd5320be2a4217d53907dc42905dd4532fa10e21ec21483ea82885f55230bea80877e51ccbea4210dd94430fd280437d51cc2faa9215754c21f6a12417e5010efca318df95020bea8e85ef4290af8a0a1fd10721f6292637e51886fca420fd90510bea8065f75150b7887205f55220bea8483f920842faa8905f54d10bea9c43ee320cbee6318dfd5321bf28665df430c2fea0a16f10c40be290217d53c86fca418dfd4c21baa8c417c540837e85214f15130bf286877d52cc6faa3185f95210fda0061de4310fdc8421774c431f6a10857f53506faa020dd54430be2a6657c514cafea4a05f54d21aea98817e518c3ba60185794c21ef21e61f631443dea4a0df95032bf288657d548cafaa7a0df54c21eea98817d540c2faa9085f54b10bf296817e5110ef8a9197d14542bea98837f548c37e85a0dfd4530bfa82877c540c2fca8905f54232be294217e54042faa6907ecc230bf294817d520c6fca1a15f94e10bfaa621ef324cafca4085f55031bf29661fb40cc3f681205fd5221bf29065bf43d02fea810dfd4543bf2a6417e50107d8a4a0dfd4d42fb188637d52d06f6a0a1df94e41bf294857e51906fca8215f94730bf280617d52103de41105f55110dfa08837e509077a84a0f7cc832f7a92637e54102faa110df15220bf2a643bd40103dc64907dcc531b6a90817d53102dca4205fd5121bfaa4637c540877c80a077cc030bf29e41ed52102fca3a1df54e42eea98437d54cc2faa3a1fe4c030bf29843bf4390efca198db54a10f6996417f53442dea4a0dfd4941be298417d54c82fca8995f55021
  | 1 => 0xc03008000002901c06290171843000c001540b00c19008240000100816078270d40403809000111340001802000d3004000000002801000040094301006008000000111c0a002faa5087d50441f721241fb20883f0a0a1dfd4e21bf290857c54886fea4a1df54031ef992637d5090afaa7205f95232bf2a0617e5310efca818f74c832fa988637d54c86fea7885f95021fb988437f515037aa8187d4c510beaa663ef21886fca690df94840bfa9a81f610443f680a057d4d40bfa9021fb304c2fea89977ccb31b7a92637e52d0fec8220db14941bf284637c54cc2faa8987dc4010be2a0657f54cc2faa7185f94f40be292837d52906fea898dfd4f21ef29843ec42887de8510df94f41beaa0217e530cb7a8621fd08510fda8287f741c86fca910df94242bf28c65dc430c3ee4290df94210bfa92637e510c6faa6215fd5331f621043ed320cbba86987b94830bfa9a417f540c77a86a05f95041bca80437d510cbdaa5087d88421f7a12857f53042f8a5885f94b10be29c417e51902f8a9905fd4132efa9a81ef420877a8220df14c10dfa12837d538837ea8985f54642bf28e857f524c2faa010f7d0d43bfa92217d50cc7e86210fe54021ae29a817e530c2faa7a05f94042be28a41f741506f8a898dfd5110bf290417e50082f8a818df54e10bfaa261be540c2f8a990df95330be282657e52cc6f8a4985f94d10bea90213d540c3de4210fdc8710be2a2217d52442fca421df94a41bf288857d52d02f8a4a1df95131f710241ed21086fca721dfd4141dfa04817f53c82faa118df94821bf2a6637c53c82faa3995f14543fba0c837c54482f8a0a15f94410bf2a4637e53106faa2215f94420bea94437e5190fde6510fec8120beaa621ec32886f8a6887e44010beaa2437d53c82fca3905fd4a10beaa0417d538cafaa3195f15010be29c217d52cc3ba6598df54440faa0e21ef32086f8a9886fd0040bf294657e508cadca4185f14131bf284617f54ccbdca4205f55132bfa9c217f54082fca4187b4c920bea86857f53082faa420dfd4542fd080217c52502fea8085f94620dfa18877c548c2f8a790df94f10f6a90613d54086fea7107bc8020fc200617f52c42faa920df94a31bf284877c53482fca890ef90e40bea88417d530427ca810db94a10fa208437d548867ca8187d90710ef298817c5244378a898774c931bf28043be43103be87185f54640bf29821f651883dc4390778c130fa28a657e54c42fea9105f94441be29a857c544c3f621086fd0641ef98c637e52442f8a2a15f54341fb18e21ed42c83f440887e88020ef994657e52843b887185f94440be29a83dc53502faa1a1de94021fd882217e53903d843907b88521bf29e857e538877e86a05f54720bf29683f510042fca018df14d40bea8085df4390efaa7887e10330bea9
  | 2 => 0xb80901c010700000000000e5000010000100242000070081003c00004020380a028060fc02028002581200416020001f001008660040c27c110006700009000050000a00022014b705c2404c241d0000005d000010c809004010081c02c000c1510580416c000300418800000120b007014150742d000000000501802058000340200493004041640f0540001403000cc0001e03c16028246441a000020100400015010144dd3204c0000421000010582a26800008273c416008160b01a57002118222f0120180a479fa0080a01c311a9921f88d00003028000081f2e0000280301000004000000b00000028f9018011780000
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x1520c35553cc421f1ccb310867661150209b58b54cc67661150329b59432086796014c218f99052c436732145329d997214431c5490d30ad18542d079b6050c43a71814310e5d6315021a7d954310e7b60551319758c54882e56210421ce55250087546154c21b9189414427b654c0309d98754cca3d6595021b9185320cb3654544309d987548831f6550c439e181544ca6f6254d21b9584420866f62547409e983548ca766114c209d584548c26e6215230c715143cc2776550441ce55150087665294430d914b314c6e46250441d954a511026c6255131c7551300c31e5454c21b358c21c826d62150319b98a544c6796015031c718d540c35b43141439798e544867960d52329b195424826d6214c109798f540879b43d00309bd89544c67661152309d58453082776155132b958432086776154d219e983540866f6254730cd185540871d5310c40f194d210867561d5332d9947208826e62d50309b98b54cc6e46150b209e580540876652544308fd954210b674214542c750d5010f4c52cc9318f993530871e5494c21ae1814310e75611502097996434c35853d0140cb5534208675650c4219d98453882d4614cb319e596100425d63152108f59053842e4614c9209ed9510042d56308510b61814310e776154843ce952500879943d03309b18951cc27661951329e983530867a6014810e9951210874d53cc821c755253087655294430b998a10442746154843dc9845050ee461508429b98853042746154b40e9d0b41086756114e209dd8554486d86050f309d984540426e62150319e195204423d64d4f10d914b415063e6495130d3189530871c53d0d409b988540435653544409758c52c426d62d4e109bd954210a986050c43da9885050e3e6414c218f596540c26c6254d108f997435026c6254740d9549510c2ad6408720d554d511027561d5030d394d521029c6350040d354e5210277654c4319b58b540c25f654c832b658c40cc34e53948409d18552cc27b60551309b588548425e63152209dd85544832c62550218f99053042d863500408f990540c3586054c409b588548c23e64d4f109718d54442e4624c5109d987540c25e63150218f590530863d64d4f209718d544825e6314b109d984540c23f6550040da949208423f65504419bd8954486b564085108f59053042776154b30b9189310c6cd63085209b58b548431c5350d40d9949511033954d00308f593530875a5394021f154d210867561150329bd9521086776154d209b98a509067661152209d185534823d6414810da5885050e5e63d53209798c530867a60d5231c7152304c27960d50218f59053882756115220dc5845050f984310030c754e43102e462507109d9845050e5d63150209758c540435a5354021f8085204423c6454d208fd9153443565394440
  | 1 => 0xa0501000ec06000140c000780400001306e04f20000410170780400080001c0a365c090063c01825f6022b01858070100006040001c00570000c365e0007c00000480cb001018781602001243a00000742000000482200000004603000022a0000050000e008000005010000005018bc2c002380806034e86824060081804030300800010200000002a00800000a01822001c1bc0001008380201000040000028cc022b00000091c02c782047012d40401000016c019e800942400020240f0581400051103cea05000180045040010a14028000e020009c00000185a7960d4c218f191534423e6414e209dd8552d026d629401097195434c23f6454d209b58a544c71d54d0c30e61814310e6d6294241b9986204831c5390140c7551530863e6414810b958831086e461509209b988530825d65d0c309dd95100426c62551108f99353c823e64150219b594420873a43141439b98a508c63f64549109d586508ca746155120ce951500874d53548409798c540826d6214e10d954821c42d86050d30d9549511025f635491097d954310e5d63d53109b98b538425c6354910cb952520c23e6414c209798f54c426d62150309bd95320ca7960d5231cb552520c23d6414c20c7151434c2756194242c7550430c2f260085109d185544ca766194242b918d210865e6314810b9991210865e6315210e9551210867a60150219759653086776548421cb14b425066e62150309b9885050ed563087109d59441087355494430cd553410863e6494d21c7553300c27561d52209bd8954442e56288421d994b108429c644c030d654e500865e6315030c754f40102ad64085209d984530425f63551109ed95401027a60150329d584540c31f5410e309b1953248276619423297d95300c25d63d5320c754d401026e6214e10b919121086e4614cb2097d8d544c32d54548309ed81544ca7561d4e209bd895110f5553944409b98b548426c62544439b588540431d6315130da982528426e62152109d195414425f654c4318f990538427b65480209e980540c66e62940108f59052c4274654c510d654d500877260946209758f540867a6014c21ce181540c39a43103309d987520425f6355120d954421c825d6395121ce153304c36765484219b5885050e796510030ae191300c25d6314810b9d9521086b86050f40b918931c426e6215020ad59021c427561141438f59253487665294440f8486500865e6315010cd551510c23c6454910d9548214425d6510c309bd8953442b86050d40b9d8121086756195132a75924310ee66348421bc986204423f6550c438f994544c27661d4e20cd952510c27860551318f59643102796015032ba980214826f65480209b58a508c7e12154021cb95
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x18200510004020f055454d21086d0ba04290221319ce6448421d24e23028621e91711814310e533a4c690843985896114143932ed218819874153485500870cb288620061461c14354043c30a83028698544735482144344b90c0a1887865d46050c43a48e8a90428868a721814310f0c318c0aa061705cc2148110a32eba1e801872154485500860e3b2a898061861506050f30
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x80c09755c86050c43c81725c46050c43c11755c46050c43
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 586
  | 4 => 379
  | 3 => 23
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
  | 5 => 2*((h/251+packedAt s5K5 (15822+(h % 251)*10) 10) % 586)
  | 4 => 2*((h/196+packedAt s5K4 (14402+(h % 196)*9) 9) % 379)
  | 3 => 2*((h/14+packedAt s5K3 (1127+(h % 14)*5) 5) % 23)
  | 2 => 2*((h/8+packedAt s5K2 (180+(h % 8)*2) 2) % 3)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf81ffff03ffff00f1e3f8ffff1fffc0013f3fc
  | 1 => 0x7fe0f8ffc1f1fff01fc7f1c0fe381ff8eccccf
  | 2 => 0x7fff00fffe01ffffe007fe00ffc01fff0f0f0f
  | 3 => 0x800000fffffe01fffff80000ffffe007f00ff0
  | 4 => 0xffffff00000001ffffffffff00000007fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x8c2101184200201020982463048c43001515c
  | 1 => 0x114a21228c82a0500e42908a5211495064c4c5
  | 2 => 0x22845245106540a720052414a48292a30b0b0a
  | 3 => 0x714a4882940653a54900020c92700c5b00ea0
  | 4 => 0x4418c00e318989cc9926493800040306dea000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeeaeac0feeaeac0feeaeac0feeaeac0feeaeac0feeaeac0feeaeac0feeaeac0feeaeac0feeaeac0feeaeac0feeaeac0feeaeac0feeaeac0feeaeac0feeaeac0, s5N, s5R, (fun _ _ => 0), s5I, []⟩
end PEqualNP.Outside.L_meta_37017
namespace PEqualNP.Outside.L_meta_37017
open PEqualNP.Outside.L_meta_37017.Model
def q2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def q2K4 : Nat → Nat
  | 0 => 0x20100103734ed21be42bf41bc42dd31fa10f910df31bf43bd43bf40bd40bd41ef21
  | _ => 0
def q2K3 : Nat → Nat
  | 0 => 0x80280100000804754f40f090a213950d0f4a8290ce54042e298a43355110a3aa621744c510
  | _ => 0
def q2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 14
  | 3 => 9
  | _ => 0
def q2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt q2K5 (i*5) 5
  | 4 => packedAt q2K4 (i*16) 16
  | 3 => packedAt q2K3 (i*27) 27
  | _ => 0
def q2I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt q2K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/11+packedAt q2K4 (224+(h % 11)*4) 4) % 14)
  | 3 => 2*((h/17+packedAt q2K3 (243+(h % 17)*4) 4) % 9)
  | _ => 0
def q2Pos : Nat → Bits
  | 0 => 0xfcb678f39e331ce71e3e319e718399f781c86e
  | 2 => 0x7f3fbf03efc3ff07e7cfc1e381fc1e39fa0c93
  | 3 => 0x9fc7dffc0ffc1ff807f07e03fe0fe03e04731c
  | 4 => 0x1ff81ffff0001ffff8007ffc000fffc00783e0
  | 5 => 0xe0001fffffffe00000007ffffff0000007fc00
  | _ => 0
def q2Neg : Nat → Bits
  | 0 => 0x9488818c284244a2440908614a0889508c826
  | 2 => 0x0
  | 3 => 0x201001200400480048020200a0050020101118
  | 4 => 0xd0037241012a928400956528084a55002702c0
  | 5 => 0x1aedfc8a49a202d69529f9d34d60458547ec00
  | _ => 0
def q2Atlas : Atlas := ⟨5,rawDecor 61 q2Pos q2Neg, 0xfffafff0fffafaf0fffafff0fffafaf0fffafff0fffafaf0fffafff0fffafaf0fffafff0fffafaf0fffafff0fffafaf0fffafff0fffafaf0fffafff0fffafaf0, q2N, q2R, (fun _ _ => 0), q2I, []⟩
end PEqualNP.Outside.L_meta_37017
namespace PEqualNP.Outside.L_meta_37017
open PEqualNP.Outside.L_meta_37017.Model
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
end PEqualNP.Outside.L_meta_37017
namespace PEqualNP.Outside.L_meta_37017
open PEqualNP.Outside.L_meta_37017.Model
def q6K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def q6K4 : Nat → Nat
  | 0 => 0xa064402000bf42be41f510f710bd43bd42ef20bf40df30bd40dd30bc41ed20bf43
  | _ => 0
def q6K3 : Nat → Nat
  | 0 => 0x800008002000824b54b438ea988339501063aa7a14b54841f090221b140443a26088724c120
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
  | 3 => 2*((h/17+packedAt q6K3 (243+(h % 17)*4) 4) % 9)
  | _ => 0
def q6Pos : Nat → Bits
  | 0 => 0xfdeef8773e7cfc733e7f988e3c718cf3f8a427
  | 1 => 0x7e777f87cf9f1f83c78e60f3cf8e0f3c8158da
  | 2 => 0x9f879ff80fe01ffc07f07f03f00ff03f06631c
  | 4 => 0x1ff81ffff0001ffff8007ffc000fffc00783e0
  | 5 => 0xe0001fffffffe00000007ffffff0000007fc00
  | _ => 0
def q6Neg : Nat → Bits
  | 0 => 0x0
  | 1 => 0x8080008102002404081000104402041008084a
  | 2 => 0x28382910a40949205402a9029124a02a126114
  | 4 => 0x5003d2220152924200a552a402494a802582a0
  | 5 => 0x1b5dfc44a958036aa549fccb2b60628a47f400
  | _ => 0
def q6Atlas : Atlas := ⟨5,rawDecor 55 q6Pos q6Neg, 0xfefeeeeefefeeaeafefeeeeefefeeaeafefeeeeefefeeaeafefeeeeefefeeaeafefeeeeefefeeaeafefeeeeefefeeaeafefeeeeefefeeaeafefeeeeefefeeaea, q6N, q6R, (fun _ _ => 0), q6I, []⟩
end PEqualNP.Outside.L_meta_37017
namespace PEqualNP.Outside.L_meta_37017
open PEqualNP.Outside.L_meta_37017.Model
def q8K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q8K3 : Nat → Nat
  | 0 => 0xc100002e986d20ea21bc82f987710
  | _ => 0
def q8K2 : Nat → Nat
  | 0 => 0x2007848110c93048344c110
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
  | 0 => 0xfffffffffffffffffffffffffffeaef1b77c27
  | 1 => 0xbf333e3ba0da
  | 2 => 0xdfc3cfc3c31c
  | 3 => 0xeffc0ffc03e0
  | _ => 0
def q8Neg : Nat → Bits
  | 0 => 0x0
  | 1 => 0x42444211044a
  | 2 => 0x241814820914
  | 3 => 0x1801a92012a0
  | _ => 0
def q8Atlas : Atlas := ⟨4,rawDecor 15 q8Pos q8Neg, 0xfeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeea, q8N, q8R, (fun _ _ => 0), q8I, []⟩
end PEqualNP.Outside.L_meta_37017
namespace PEqualNP.Outside.L_meta_37017
open PEqualNP.Outside.L_meta_37017.Model
def q10K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q10K3 : Nat → Nat
  | 0 => 0x1022f995e30ba6374caf98dc30
  | _ => 0
def q10K2 : Nat → Nat
  | 0 => 0x70009541cca5504308d42cc6350830
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
  | 4 => 0x76fe1fcff03fce3c
  | 5 => 0x78ffe00fffc00fc0
  | _ => 0
def q10Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffa010010012080045
  | 2 => 0x1224284484922512
  | 4 => 0x941501921248a28
  | 5 => 0x7851aae4986af80
  | _ => 0
def q10Atlas : Atlas := ⟨4,rawDecor 54 q10Pos q10Neg, 0xfcfcccccfcfcc0c0fcfcccccfcfcc0c0fcfcccccfcfcc0c0fcfcccccfcfcc0c0fcfcccccfcfcc0c0fcfcccccfcfcc0c0fcfcccccfcfcc0c0fcfcccccfcfcc0c0, q10N, q10R, (fun _ _ => 0), q10I, []⟩
end PEqualNP.Outside.L_meta_37017
namespace PEqualNP.Outside.L_meta_37017
open PEqualNP.Outside.L_meta_37017.Model
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
  | 1 => 0xffffffffffffffffffffffffffffffffffbecf
  | 2 => 0xffffffffffffffffffffffffffffffffffdf73
  | 3 => 0xefbc
  | _ => 0
def q11Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffff4205
  | 2 => 0x2412
  | 3 => 0x1828
  | _ => 0
def q11Atlas : Atlas := ⟨3,rawDecor 14 q11Pos q11Neg, 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0, q11N, q11R, (fun _ _ => 0), q11I, []⟩
end PEqualNP.Outside.L_meta_37017
namespace PEqualNP.Outside.L_meta_37017
open PEqualNP.Outside.L_meta_37017.Model
def q12K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q12K3 : Nat → Nat
  | 0 => 0xc0005e329865b0cb7995c32
  | _ => 0
def q12K2 : Nat → Nat
  | 0 => 0x2390a32
  | _ => 0
def q12N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
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
  | 3 => 2*((h/8+packedAt q12K3 (75+(h % 8)*3) 3) % 5)
  | 2 => 2*((h/1+packedAt q12K2 (26+(h % 1)*1) 1) % 1)
  | _ => 0
def q12Pos : Nat → Bits
  | 1 => 0xfffffffffffffffffffffffbfc7fffe3fff1ff
  | 2 => 0xfffffffffffffffffffffffdff8ffffc7ffe3f
  | 3 => 0xebff0f3ff8e0fcc
  | 4 => 0xf3fff03fff00ff0
  | _ => 0
def q12Neg : Nat → Bits
  | 1 => 0xfffffffffffffffffffffff4070220a092a0d5
  | 2 => 0x20864414425462a
  | 3 => 0x1512e8669086b4c
  | 4 => 0xe248eb92418db0
  | _ => 0
def q12Atlas : Atlas := ⟨4,rawDecor 30 q12Pos q12Neg, 0xfcc0c0c0fcc0c0c0fcc0c0c0fcc0c0c0fcc0c0c0fcc0c0c0fcc0c0c0fcc0c0c0fcc0c0c0fcc0c0c0fcc0c0c0fcc0c0c0fcc0c0c0fcc0c0c0fcc0c0c0fcc0c0c0, q12N, q12R, (fun _ _ => 0), q12I, []⟩
end PEqualNP.Outside.L_meta_37017
namespace PEqualNP.Outside.L_meta_37017
open PEqualNP.Outside.L_meta_37017.Model
def q13K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q13K3 : Nat → Nat
  | 0 => 0x20000b82e18df30ba6178c6f195c32
  | _ => 0
def q13K2 : Nat → Nat
  | 0 => 0x8e428c65906328c424c2510530
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
  | 3 => 2*((h/16+packedAt q13K3 (90+(h % 16)*3) 3) % 6)
  | 2 => 2*((h/1+packedAt q13K2 (104+(h % 1)*2) 2) % 4)
  | _ => 0
def q13Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffdff3ffff1ffff1ff
  | 2 => 0xffffffffffffffffffffffedfc7f3fe3f0fe73
  | 3 => 0x76ff8fcffc7f0f9c
  | 4 => 0x78fff00fff800fe0
  | _ => 0
def q13Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffa0180202049440a5
  | 2 => 0x122324452122a652
  | 3 => 0x9416819484a2b18
  | 4 => 0x78a4eae920ccde0
  | _ => 0
def q13Atlas : Atlas := ⟨4,rawDecor 30 q13Pos q13Neg, 0xfcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0, q13N, q13R, (fun _ _ => 0), q13I, []⟩
end PEqualNP.Outside.L_meta_37017
namespace PEqualNP.Outside.L_meta_37017
open PEqualNP.Outside.L_meta_37017.Model
def q14K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q14K3 : Nat → Nat
  | 0 => 0x80008ae995d31b86178c2f98df32
  | _ => 0
def q14K2 : Nat → Nat
  | 0 => 0x408d42cc65504308d420c2550732
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
  | 0 => 0xffffffffffffffffffffffdff7fcfc7ff8f3cf
  | 3 => 0xffffffffffffffffffffffedf99f3f8e3f3d33
  | 4 => 0x76fe1fcff03fce3c
  | 5 => 0x78ffe00fffc00fc0
  | _ => 0
def q14Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa010010012080045
  | 3 => 0x1224284484922512
  | 4 => 0x941501921248a28
  | 5 => 0x7851aae4986af80
  | _ => 0
def q14Atlas : Atlas := ⟨4,rawDecor 57 q14Pos q14Neg, 0xffaaaaaaffaaaa00ffaaaaaaffaaaa00ffaaaaaaffaaaa00ffaaaaaaffaaaa00ffaaaaaaffaaaa00ffaaaaaaffaaaa00ffaaaaaaffaaaa00ffaaaaaaffaaaa00, q14N, q14R, (fun _ _ => 0), q14I, []⟩
end PEqualNP.Outside.L_meta_37017
namespace PEqualNP.Outside.L_meta_37017
open PEqualNP.Outside.L_meta_37017.Model
def q15K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q15K3 : Nat → Nat
  | 0 => 0xc002e18de31be6574c2e995f30
  | _ => 0
def q15K2 : Nat → Nat
  | 0 => 0x4004008d420c6350b3099400c6650332
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
  | 3 => 2*((h/16+packedAt q15K3 (90+(h % 16)*3) 3) % 6)
  | 2 => 2*((h/15+packedAt q15K2 (104+(h % 15)*2) 2) % 4)
  | _ => 0
def q15Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffddf39cfc7e39f70f
  | 3 => 0xffffffffffffffffffffffeffdff3f8ffe39f3
  | 4 => 0x76fe1fcff03fce3c
  | 5 => 0x78ffe00fffc00fc0
  | _ => 0
def q15Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa21829041288a305
  | 3 => 0x1020004084100052
  | 4 => 0x941501921250c28
  | 5 => 0x7891aae4985af80
  | _ => 0
def q15Atlas : Atlas := ⟨4,rawDecor 57 q15Pos q15Neg, 0xffaaff00ffaaaa00ffaaff00ffaaaa00ffaaff00ffaaaa00ffaaff00ffaaaa00ffaaff00ffaaaa00ffaaff00ffaaaa00ffaaff00ffaaaa00ffaaff00ffaaaa00, q15N, q15R, (fun _ _ => 0), q15I, []⟩
end PEqualNP.Outside.L_meta_37017
namespace PEqualNP.Outside.L_meta_37017
open PEqualNP.Outside.L_meta_37017.Model
def q16K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q16K3 : Nat → Nat
  | 0 => 0x400003a887431ee21d087b90f731
  | _ => 0
def q16K2 : Nat → Nat
  | 0 => 0x4049643c86510d10a442442990b31
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
  | 0 => 0xffffffffffffffffffffffdff3ffff1ffff1ff
  | 2 => 0x6afc39cfe3870ecc
  | 3 => 0xfffffffffffffffffffffff3ffc1fffc07ff0f
  | 4 => 0x7cfffe0ffff80ff0
  | _ => 0
def q16Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa018800104912055
  | 2 => 0x152b9297213266cc
  | 3 => 0xc41350a4844cb0a
  | 4 => 0x38221ac92608da0
  | _ => 0
def q16Atlas : Atlas := ⟨4,rawDecor 29 q16Pos q16Neg, 0xfaaaaa00faaaaa00faaaaa00faaaaa00faaaaa00faaaaa00faaaaa00faaaaa00faaaaa00faaaaa00faaaaa00faaaaa00faaaaa00faaaaa00faaaaa00faaaaa00, q16N, q16R, (fun _ _ => 0), q16I, []⟩
end PEqualNP.Outside.L_meta_37017
namespace PEqualNP.Outside.L_meta_37017
open PEqualNP.Outside.L_meta_37017.Model
def q17K5 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q17K4 : Nat → Nat
  | 0 => 0x1c000c003080e200002fc43f0c3e907e31fe21f8cbf087f32fe43f443e18fc20fa43fcc3e10fc32f821f4c3f907d31fc41f4cbf187f31
  | _ => 0
def q17K3 : Nat → Nat
  | 0 => 0x2204010000000300018004344138a0354c431ad42cc6d10530b5418cad50420b6418ca790e219f4344334c832ad428c6790f21b441482b90810b641082710d20b5410c2d907329f43482b90a31af424c2b50830ac424c2dd0530ad42042790c20af424439484219d43886b908309c43442750f219d43082b10910b541ccadd05209e43042b90b31b6410c2750c10
  | _ => 0
def q17N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 24
  | 3 => 39
  | _ => 0
def q17R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt q17K5 (i*4) 4
  | 4 => packedAt q17K4 (i*15) 15
  | 3 => packedAt q17K3 (i*26) 26
  | _ => 0
def q17I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt q17K5 (4+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/15+packedAt q17K4 (360+(h % 15)*5) 5) % 24)
  | 3 => 2*((h/20+packedAt q17K3 (1014+(h % 20)*6) 6) % 39)
  | _ => 0
def q17Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffbff7fffe3ffff1ff
  | 2 => 0xffffffffffffffffffffffd5f8e73fc71c7e93
  | 3 => 0xe6ff07cff81f8f1c
  | 4 => 0xf8fff80fffe00fe0
  | _ => 0
def q17Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff4010000009040025
  | 2 => 0x2a264a4642496692
  | 3 => 0x1942d41a90932b18
  | 4 => 0x78486ad24c24dc0
  | _ => 0
def q17Atlas : Atlas := ⟨5,rawDecor 29 q17Pos q17Neg, 0xfaaaaaa0faaaaaa0faaaaaa0faaaaaa0faaaaaa0faaaaaa0faaaaaa0faaaaaa0faaaaaa0faaaaaa0faaaaaa0faaaaaa0faaaaaa0faaaaaa0faaaaaa0faaaaaa0, q17N, q17R, (fun _ _ => 0), q17I, []⟩
end PEqualNP.Outside.L_meta_37017
namespace PEqualNP.Outside.L_meta_37017
open PEqualNP.Outside.L_meta_37017.Model
def q18K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q18K3 : Nat → Nat
  | 0 => 0x4000012e98fa10f2217cc7790ed21
  | _ => 0
def q18K2 : Nat → Nat
  | 0 => 0x314c521d131443848510
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
  | 0 => 0xbea673b7606e
  | 2 => 0xffffffffffffffffffffffffffff3bbc3bbc93
  | 3 => 0xdfc3cfc3c31c
  | 4 => 0xeffc0ffc03e0
  | _ => 0
def q18Neg : Nat → Bits
  | 0 => 0x424880910426
  | 2 => 0x0
  | 3 => 0x241415020918
  | 4 => 0x18016a2012c0
  | _ => 0
def q18Atlas : Atlas := ⟨4,rawDecor 29 q18Pos q18Neg, 0xfffafaf0fffafaf0fffafaf0fffafaf0fffafaf0fffafaf0fffafaf0fffafaf0fffafaf0fffafaf0fffafaf0fffafaf0fffafaf0fffafaf0fffafaf0fffafaf0, q18N, q18R, (fun _ _ => 0), q18I, []⟩
end PEqualNP.Outside.L_meta_37017
namespace PEqualNP.Outside.L_meta_37017
open PEqualNP.Outside.L_meta_37017.Model
def q19K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q19K3 : Nat → Nat
  | 0 => 0x405203b98f431ee43d443a10f710
  | _ => 0
def q19K2 : Nat → Nat
  | 0 => 0x8000a442442990b319643c86510d10
  | _ => 0
def q19N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
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
  | 2 => 2*((h/8+packedAt q19K2 (104+(h % 8)*2) 2) % 4)
  | _ => 0
def q19Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff3ffff1ffff1ff
  | 1 => 0x6afc39cfe3870ecc
  | 3 => 0xfffffffffffffffffffffff3ffc1fffc07ff0f
  | 4 => 0x7cfffe0ffff80ff0
  | _ => 0
def q19Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa018800104912055
  | 1 => 0x152b9297213266cc
  | 3 => 0xc41350a4844cb0a
  | 4 => 0x38221ac92608da0
  | _ => 0
def q19Atlas : Atlas := ⟨4,rawDecor 27 q19Pos q19Neg, 0xeeaaaa00eeaaaa00eeaaaa00eeaaaa00eeaaaa00eeaaaa00eeaaaa00eeaaaa00eeaaaa00eeaaaa00eeaaaa00eeaaaa00eeaaaa00eeaaaa00eeaaaa00eeaaaa00, q19N, q19R, (fun _ _ => 0), q19I, []⟩
end PEqualNP.Outside.L_meta_37017
namespace PEqualNP.Outside.L_meta_37017
open PEqualNP.Outside.L_meta_37017.Model
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
  | 3 => 0xffffffffffffffffffffffeffe1fffe03ffe1f
  | 4 => 0xf3ffe03fffc00fe0
  | _ => 0
def q20Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff40640108248920b1
  | 1 => 0x24ac285909932594
  | 3 => 0x1101502242244a0a
  | 4 => 0xe091ab493064f40
  | _ => 0
def q20Atlas : Atlas := ⟨3,rawDecor 27 q20Pos q20Neg, 0xeeaaee00eeaaee00eeaaee00eeaaee00eeaaee00eeaaee00eeaaee00eeaaee00eeaaee00eeaaee00eeaaee00eeaaee00eeaaee00eeaaee00eeaaee00eeaaee00, q20N, q20R, (fun _ _ => 0), q20I, []⟩
end PEqualNP.Outside.L_meta_37017
namespace PEqualNP.Outside.L_meta_37017
open PEqualNP.Outside.L_meta_37017.Model
def q21K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q21K3 : Nat → Nat
  | 0 => 0x10010bd085d31be63bc87690f910
  | _ => 0
def q21K2 : Nat → Nat
  | 0 => 0x314c521e12144344c510
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
  | 2 => 2*((h/1+packedAt q21K2 (78+(h % 1)*2) 2) % 3)
  | _ => 0
def q21Pos : Nat → Bits
  | 0 => 0xbea673b7606e
  | 1 => 0xffffffffffffffffffffffffffff3bbc3bbc93
  | 3 => 0xdfc3cfc3c31c
  | 4 => 0xeffc0ffc03e0
  | _ => 0
def q21Neg : Nat → Bits
  | 0 => 0x424880910426
  | 1 => 0x0
  | 3 => 0x241415020918
  | 4 => 0x18016a2012c0
  | _ => 0
def q21Atlas : Atlas := ⟨4,rawDecor 27 q21Pos q21Neg, 0xffeeeeccffeeeeccffeeeeccffeeeeccffeeeeccffeeeeccffeeeeccffeeeeccffeeeeccffeeeeccffeeeeccffeeeeccffeeeeccffeeeeccffeeeeccffeeeecc, q21N, q21R, (fun _ _ => 0), q21I, []⟩
end PEqualNP.Outside.L_meta_37017
namespace PEqualNP.Outside.L_meta_37017
open PEqualNP.Outside.L_meta_37017.Model
def q22K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q22N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q22R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q22K3 (i*4) 4
  | _ => 0
def q22I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q22K3 (4+(h % 1)*1) 1) % 1)
  | _ => 0
def q22Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffbfcffcf8fff873f3
  | 1 => 0xdbf19f3f1c3f8d9c
  | 2 => 0xffffffffffffffffffffffeffe1fffe03ffe1f
  | 4 => 0xf3ffe03fffc00fe0
  | _ => 0
def q22Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff40640108248920b1
  | 1 => 0x24ac285909932594
  | 2 => 0x1101502242244a0a
  | 4 => 0xe091ab493064f40
  | _ => 0
def q22Atlas : Atlas := ⟨3,rawDecor 23 q22Pos q22Neg, 0xeaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0, q22N, q22R, (fun _ _ => 0), q22I, []⟩
end PEqualNP.Outside.L_meta_37017
namespace PEqualNP.Outside.L_meta_37017
open PEqualNP.Outside.L_meta_37017.Model
def q23K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q23K3 : Nat → Nat
  | 0 => 0x10c302e986f20be61dc43a886d20
  | _ => 0
def q23K2 : Nat → Nat
  | 0 => 0x4324c120e12044344c110
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
  | 4 => 0xeffc0ffc03e0
  | _ => 0
def q23Neg : Nat → Bits
  | 0 => 0x0
  | 1 => 0x42444211044a
  | 2 => 0x241814820914
  | 4 => 0x1801a92012a0
  | _ => 0
def q23Atlas : Atlas := ⟨4,rawDecor 23 q23Pos q23Neg, 0xfefeeaeafefeeaeafefeeaeafefeeaeafefeeaeafefeeaeafefeeaeafefeeaeafefeeaeafefeeaeafefeeaeafefeeaeafefeeaeafefeeaeafefeeaeafefeeaea, q23N, q23R, (fun _ _ => 0), q23I, []⟩
end PEqualNP.Outside.L_meta_37017
namespace PEqualNP.Outside.L_meta_37017
open PEqualNP.Outside.L_meta_37017.Model
def q24K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q24K3 : Nat → Nat
  | 0 => 0xc100002e986d20ea21bc82f987710
  | _ => 0
def q24K2 : Nat → Nat
  | 0 => 0x2007848110c93048344c110
  | _ => 0
def q24N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
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
  | 2 => 2*((h/8+packedAt q24K2 (78+(h % 8)*2) 2) % 3)
  | _ => 0
def q24Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffffffeaef1b77c27
  | 1 => 0xbf333e3ba0da
  | 2 => 0xdfc3cfc3c31c
  | 3 => 0xeffc0ffc03e0
  | _ => 0
def q24Neg : Nat → Bits
  | 0 => 0x0
  | 1 => 0x42444211044a
  | 2 => 0x241814820914
  | 3 => 0x1801a92012a0
  | _ => 0
def q24Atlas : Atlas := ⟨4,rawDecor 15 q24Pos q24Neg, 0xfeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeea, q24N, q24R, (fun _ _ => 0), q24I, []⟩
end PEqualNP.Outside.L_meta_37017
namespace PEqualNP.Outside.L_meta_37017
open PEqualNP.Outside.L_meta_37017.Model
def q25K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q25K3 : Nat → Nat
  | 0 => 0xc100002e986d20ea21bc82f987710
  | _ => 0
def q25K2 : Nat → Nat
  | 0 => 0x2007848110c93048344c110
  | _ => 0
def q25N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
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
  | 2 => 2*((h/8+packedAt q25K2 (78+(h % 8)*2) 2) % 3)
  | _ => 0
def q25Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffffffeaef1b77c27
  | 1 => 0xbf333e3ba0da
  | 2 => 0xdfc3cfc3c31c
  | 3 => 0xeffc0ffc03e0
  | _ => 0
def q25Neg : Nat → Bits
  | 0 => 0x0
  | 1 => 0x42444211044a
  | 2 => 0x241814820914
  | 3 => 0x1801a92012a0
  | _ => 0
def q25Atlas : Atlas := ⟨4,rawDecor 15 q25Pos q25Neg, 0xfeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeea, q25N, q25R, (fun _ _ => 0), q25I, []⟩
end PEqualNP.Outside.L_meta_37017
namespace PEqualNP.Outside.L_meta_37017
open PEqualNP.Outside.L_meta_37017.Model
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
  | 1 => 0xffffffffffffffffffffffffffffffffffbecf
  | 2 => 0xffffffffffffffffffffffffffffffffffdf73
  | 4 => 0xefbc
  | _ => 0
def q26Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffff4205
  | 2 => 0x2412
  | 4 => 0x1828
  | _ => 0
def q26Atlas : Atlas := ⟨3,rawDecor 22 q26Pos q26Neg, 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0, q26N, q26R, (fun _ _ => 0), q26I, []⟩
end PEqualNP.Outside.L_meta_37017
namespace PEqualNP.Outside.L_meta_37017
open PEqualNP.Outside.L_meta_37017.Model
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
  | 1 => 0xffffffffffffffffffffffffffffffffffbecf
  | 2 => 0xffffffffffffffffffffffffffffffffffdf73
  | 3 => 0xefbc
  | _ => 0
def q27Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffff4205
  | 2 => 0x2412
  | 3 => 0x1828
  | _ => 0
def q27Atlas : Atlas := ⟨3,rawDecor 14 q27Pos q27Neg, 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0, q27N, q27R, (fun _ _ => 0), q27I, []⟩
end PEqualNP.Outside.L_meta_37017
namespace PEqualNP.Outside.L_meta_37017
open PEqualNP.Outside.L_meta_37017.Model
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
  | 1 => 0xffffffffffffffffffffffffffffffffffbecf
  | 2 => 0xffffffffffffffffffffffffffffffffffdf73
  | 3 => 0xefbc
  | _ => 0
def q28Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffff4205
  | 2 => 0x2412
  | 3 => 0x1828
  | _ => 0
def q28Atlas : Atlas := ⟨3,rawDecor 14 q28Pos q28Neg, 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0, q28N, q28R, (fun _ _ => 0), q28I, []⟩
end PEqualNP.Outside.L_meta_37017
namespace PEqualNP.Outside.L_meta_37017
open PEqualNP.Outside.L_meta_37017.Model
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
  | 3 => 0xffffffffffffffffffffffffffffffffffdf73
  | 4 => 0xefbc
  | _ => 0
def q29Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffff4205
  | 3 => 0x2412
  | 4 => 0x1828
  | _ => 0
def q29Atlas : Atlas := ⟨3,rawDecor 25 q29Pos q29Neg, 0xffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00, q29N, q29R, (fun _ _ => 0), q29I, []⟩
end PEqualNP.Outside.L_meta_37017
namespace PEqualNP.Outside.L_meta_37017
open PEqualNP.Outside.L_meta_37017.Model
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
  | 3 => 0xffffffffffffffffffffffffffffffffffdf73
  | 4 => 0xefbc
  | _ => 0
def q30Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffff4205
  | 3 => 0x2412
  | 4 => 0x1828
  | _ => 0
def q30Atlas : Atlas := ⟨3,rawDecor 25 q30Pos q30Neg, 0xffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00, q30N, q30R, (fun _ _ => 0), q30I, []⟩
end PEqualNP.Outside.L_meta_37017
namespace PEqualNP.Outside.L_meta_37017
open PEqualNP.Outside.L_meta_37017.Model
def gbK10 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK9 : Nat → Nat
  | 0 => 0x7500400820950530805010450c31401403882016ca300000040201007f0c401ff10007fd0001ff42007f90801fe30007fc8401fc21007f54c01fe52007f50c01ff32005f55001ff43007f54001ff30007fcc401fe51007f50001fc41007f04001fd54007f88401fe43007f50801fe50007f0c801fd21007f54801fe20007f4c801fe41007f95001fd41007f94c01fd51007f8c401fe40007f4c001fc20007f100017f54007fd0401fc42007f0c001fc43007f8c801ff20007f48001fd10007f4c401fe10
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x8a2000bf98a50005e8c2990027d6510001fe1946200ffd8121007f88618002fd64c8401fe32660009f59410007fca621803fd30c8001ff21c6200dfd5130005fcc7a0803fe54cc801fe98e8000ff90f30007da8490002fd6494c01bfb12a800bf58442006faa919003df320c801fb90c4200ffcc8320077e84a0803fd2044001bfaa04000bfd8543005fac728803fc32cc001ff98c8000ff10e50007f88798802fd628c001ff21e6400bf59331007fc42a0003ff31100017f3166000bf58321005ecc310003fc32c40017eb122000ff0c730007f86318003fe6290c017e31aa200bf58a43004facb2a003ff6250c01fe10c6001ffd4843005fac910802ff63504017eb1c8000ff98e42007f8c899002fd63884017eb106200bf58440007fc4320002ee6210001ffa142000ff54530006faa888002fe62d0401bfb2a6400fec8220007fca398002fd6394801fe21c4200ff90f10007fe6420003fc6150001eea1a6000ff88440007f8c8900037d54cc8017eb226000ff50530005fcc588002fd63d0001ffa12a000ffd0b20007fe87990037f54908017eb068400df55330005fec688003fd50c8001fe10e6000ff50f21007fac198803ff4188001ffb126000bf58630007f884a8002fc6348401fc9806000ffd8d100057ec898003ff4344001ffa0a6000bfd8142006faa918002fd6494801bfaa28200bf58a21007f8c498002fe6244001773106000dfd5320007fe84190037f54840017eb24a200ffd8530005fcc729003fd32d0001fea066000fe48020007fac919003fe3210401ffa126200bf58231007fa8419003fc43040017eb246400df19521007fc6520802fe6210001ff3264000ff8c940005fcc618803fe524c0017e3128200bf58b30007f863a00027f65484013eb2e8400dfd8154007fc8790002fd6490001f72124000ff10e32005fac990002fd6094c01fe1968000ff18943007f88718803fc41cc001f69964000ff0c420007faa919003fe544c001ff18a8000b758c40007f88510003fd3048001bfaa26200bf18950007ee4288002fc63500017eb182000bf18d50005fac788002fe63840017eb1c4000ffd0120007fac721003fb20480017eb006400be98021007fa80880027d65d0401ef21a6000ffd0f10006fccb98802ff644c801bfaa44000bf18951007fa4398002fe6348001ffb224000bfd8d40007ee4388003fd218c001beaa28400b758c21005f8c6a1002fc6350401fe1926000ff90d30007fe6418002fe62840017fb22a601ff14043007f86298002fd6308401fe10e8000df18154005fcc421803df32cc401ff20e6000ff94f32005fac690803fc418c001fea1e4000ffd8b30007f24108003fe4248001feb206400ffcc940007fa8290003fe514c0017eb266000bf58d10007f8c898803fc4344001ff98e6000dfd5143
  | 1 => 0x3fa2044001fe1948200ffd8d21006feca88003fc6344001fea1c4200ff18543007fe84880037f54cc001fb20a2000ff54d20007f8c090802fd6210001ee9966200ff19130007fca6900027d65cc401bfaa46400af59030005fac508003fc3250001fe9862000bf58640005f2c010803fc430c801ff2146200bfd9331007f862a0003ff644c801fe9966200ffccb20007f88408003fe42cc801fe2146200ff90f31007fec898803ff31480013eb2c4000bf98e42007fa8090003fc3294001bfaa46200dfd5332007f86220003fc434c8017eb044200fb50b20007ee6318803fc4394801beaa24200bf98c42005fec990002fc63c8001ffa146000dfd5110005fec0a88037f5404001fe1908000df99432007f84218003ff42cc001fe18c8000ffd9110007fe43a0002fd610c001ff2166000fb8c832005fac818803fd524c0017fb126000bfd8532005f8c790803fc2150001beaa06000bf58e42005f8c498003fd424c001ff992a000ffd0130007fe6190002fd6390401ff9942000ff58f20007f886900037f548c001f71924000df55240007fe86908037d54500017fb128200bf18d52005fac52a002fd6010801ef9926200ff90b10005eac310002fd60d0c01fe21ca200ff10b10007faa819002fe63884017eb046400bf98e40007bc6499003fc2190001fe30e6000ffcc931005fac621003fd64cc401ffa1e6200bf59243007fe4298002fd61908017e3126200ffcc1200077a84a0803fc328c001fe3166000df55331007fe4188003f7614c8017f3146200bf98c20005fac010803fd51cc001ff32064009f59743005fac219003fd5310c01de21c8000bf58d20006fea988003fc614c001dea168200bf59030005f8c4a9802fc63550013eb286000fe48110007fa8398003fc6448401fea1a2000dfd9521005fec890803fd5448001ff9968200efd0a4200ff8a421803ff6348001fb90a4200ff48430005fcc5a0003fe548c801ff9928200ff10430007faa799003f7314c401bfaa28400ef50f40007fa8498803dd43cc001bfb1aa800ff48540007fca5980037d65c80017f3106200ffd0730004faca19003fe320c4017fb1e4200ff58643007dc8590003ff4388401fe90c8000bf98e41007ea6218803fc424c001bfaa64200bf58e32007fc6490003fd43cc8017eb14a600ff10d21007f8c690803fe43c8401ffa126000bf59121007fe8190002fd6404001ef21e6000ff90d10007f8c888003ff6350001ffa0c6000bf58740005fcc521802ff624c4017fb0a6000bfd8910007ee6390802fe628c8017eb226400ff18d40005fac020802fe6210401fe9922000ffd0820007fc4218002fd6110c01ff98a8000ffcc430005fac898803fe54cc0017eb0c6400af99030007fc8498002fd6288001fea1e2000bf98e20007f86408002fe6395001fb1
  | 2 => 0x41007fc65880037d544c401ff2a26400bf58843005fec898803fd53d0801fea1a4000ff90c21007f660980037d5450401fe21a6000ffcc110007fca890002be6408401fe2106000fd50710005fac5a0802fd63d0801ee9906400df59432007fe6488003fd53108017eb168600bf98e51006faa890002ff60550017ab086000ff107200077a86a0002fd620c001ff2988400bf98b31007faa790003ff4354401ffb1a8200bfd8950006fea890803bf4390c01fe214a000ff50c21005fcc6880027d6510801ffa14a000ff50a32007fac990002fd60cc4017eb204200bf59120007fa64190027d658c401ff9946000ff90d32005fac520803ff32cc0017eb008600df55143007fc8390003bd4310c01de3226000bf59110007e8c299003fd40c8001bfaa06000ff55130007fc8619003ff644c0017eb006200bfd8943004facb90003ff42cc4017eb1e42009f59443005fcc5288037c6355001bfaa28000ff8cb40007fc8618803fc320c401fb28a2000ffd8730006fea920803ff30c40017f3108400fb8cb20005fac121803fc43540017f31e4200bfd8520007fc8690002fd6490801fe1924000ef50842007fcc9990037f654c001beb2e6200bf58c20005fac810002fd628c4017fb266400bfd9152005fcc690802fd6290001fe2166400fd08510007fa62a0003fc4384001bfaa66200ff10f20006fea920002ff6050c01feaa26400df19510005fac928003fd4244001beaa26400ff10b30005f8c4aa003fe438c801ffa066000ff58032007fc63a0002fd6090401ffa022000ff8c720005fec890002ff6050401beaa06400bf58b40005fcc410803fd43484013eb288200ff0ca40005fac7180037f5488401fe2186200bd98430007faa5980037d5490c01ff31e4000bfd89530077c8720003fd42cc001df2188000ffd9121007fe6310003fd21100017fb1aa2009f59421007fe65a0003fc4308401ff3066400bf18d20007fe8729003fc434c403ffa808600ffd0430005fec0a9002fd648c001ffa1ca200bf18940007f887100027f654c8017f31e8000ff55320007fa6088003fe4348401fe21aa200bf59032007fe8619003ff430c401ff90e6000b798c40007fc8710802ff604c401fea986400ff18d41007fa8798802ff64cc0017fb22a000ffd0d20007f86218002fc6344001f79926400bf58e54007f86418003fe64cc4017eb262000bf98c400077c84a1002fd6394001ff90c6000ff94c32005fec888003fc32104017fb22a200ffcc820007fe6498002fc6250c01ffa062000bfd8f20007fe8519002ff6150801ff30c8600ff10a30007fec998002ff61500013fb2a2000ff58a430077e86a0002fd60950017f314a600bf59241005fcc610802fd638c401fe1088000ff4c940007fa8590002fe62080016f3184200ffd0c21005fcc78800
  | 3 => 0x63c07c163ea23800140d20e03e00010008a8070040b8020402607000018041e8121381a1596205800038025f80000822000401e8344606a4d01e008940781c130667a8060002c00000600640480c0a02a0d01005834060146b062008060880245042068240c8021083474012018000194a428d60006a050545a0040100c118020999e030045103c0981e049180b8980381e0b8022e80e000ea03944068022580801006b4000019bc058500e000078302e83085842030022902c008000383e1600a0522600003ff43548017eb066400ffcc630007f88718002ff6048401beaa64200bf98830005fcc7900037e65c80017fb1a8400bf58b31005fac128803fe424c801ff994a000ff08530005fec690803fe54c80017f3168600ff10f32007fe6520002fd6488001ff9966200ffd8940005fcc419002ff63548017fb246400ef90d43005ecc220003fd40c4001beaa26000bfd8d20007f8c690003fc43c4001ff3066200bf59332007ea42108027d65d0001fe2126400fbcca32007f88798003fc32540017f31e8400df55020005fec898003fe21cc001fe9964000bf58620005fcc518002fe6304001ffa1e4200ff98032006f8ca99003fe420c401fe90e8000ff50b31007fec2a0002fd6190c01feb066400ff50130006fea921802ff6254401bfaa26400bf58732005fac210003fe218c001fe2106200ff48530007f88790803dd324c4017f3186000bf98810005fac408002bc644c0017bb0a6400ff0c720006faa921002fd648c401fe2124000ff54120005fac7080037f540c801be32a6000ff59332006f8c4aa003ff6150c01feaa66400bf58f41007fe40900027f654c0015eb204200e750c43006fea818802fd63100017eb0e6000ff55330007f8c6a1003fe414c0017fb12a800bb58830007fe6298003ff210c003fe2988600dfd5120007da6419003f531440017f3188601ffd4443007eaa288003ff31d00017fb02a600bf58742007f88210003fc414c001fb9884200ff4c941007fc8698802fe63940017eb0c2000bfd9321007f86510002fd62c4001dfb226001ff14443007f886a9002fd61c8001ff90a8000bfd8940007ea8288002fe6295001bfaa04200bf58c41007da64900037d54840017fb206400ff4c520006faa990003fe648c801ef9946400fecc230007e86390802fd60d0401fe2184000ff4cb41006faa910002fd62940017fb026400bfd8d54005fac528803fe53d0801ff9946400bf98a40007fe4220002fd60948017e3122000ff18940007fe8290002fd61d0c01ff90c8000bf98a41007fec6a1003fe540c801ffa106000ff88740007ea6388002fd609080176b108000ff50c32007fe8790007ff5310c01ff29e4000ff88530005fec6a8002fd6484001fea186200bf98c32005eac220002fd63c80017eb108200bf98c
  | 4 => 0x1800006068a412044020002881a070080b01801008150661182a001844b92001802018040082e0286a17070001201200003920148060200403818008ea0200000812218000080e11800028307d9e0549220583001a42000160d88000012078120280c170040000489022000140980a01836000c81f0b21d82c050241c3460000a1b8000181000002000000001200002080920cb3014006009260403ca181003800042
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0xe638844013efe64887300c7ed21084400067c6519130006fe62cc310006fd64cc430007f721cc3100b6fd7608430004fe7690d3004fed2108730006bd6410830045fc740c93008fbd6448430006fe76cc530005fe73d08200067f65d0d21045fe74d8530005fd7218543035fc7448110005fd7010b3006f7d6508440005fd76d0f20006fd6310a20004fe7610d311477e7510f21006bd6448430006fd7458031006fa7458021005fc765093000e7c5218d54006fd624c3100077f6510930007787055330126fe6408530004fc7359310004fd76d0f20006fd42583310c6ff6019110005fe76d0d210067d5458642005d57308510004fe7610d3203dfe71d89300066f5498830075fd76c8430006df63cc940005ff7250730077f661c8440026fe6110c210077554cc721146fe76d0f2108efc3058720006fc6218540005de73d0b3006dfd7008640006bc6494530005fd7219130006ff630854005dfe718c540005fe730c9400ef7d548cb400077d548873009ff62150c2103dfe7190930006ff62189400c7bd740844005dfe7118940006fe63c843002ffa7010d20007f731c84400077e75cc7400067d5498a1005ff421503100047f7655220147dd4310f21006ed620c8310047e76d5132005fd70950320076d654c832077ed62c84400077d54cc52000f7c5210e51006fd7298f4110dfc744cb310f77d54d0c310f5fe740c831006fd648c720004fd768cb100067d54d812106dfc7050c21096fe6088440006fd6488730007de4318930005f7714cb400bdfc740c63003efd7608530007f52108630055fc7448730006dc638c540006fd624c110005fe72d873002f7d54d0520005fe7688540006ff64cc5200077f54886400077c65485300077f540c5400077d7518d200df7d54d0f201377e75d0d21006ff6318d2105fdd310c54003dfc73085300177d54d0832086fe64cc832147de4310f21137bc434844017efc43d8954006fd7118d20006ff4358b31006fe7498f200067e7598f1003dfc761053004fde7308730005fe7388630127f571d0c2102dfc744c52013fdf4350e210067f6519110006fe7298f100befd76106300077d54cc9410067d54189100077f7255330005f571c8310005fd708854008dfe7018d21096fe30d8910004fd7608440007bf4250530006fc63d03200067d65993310073d7519130146ff43d8542005ff7050d21006ff7558331006fc6308540005fc73c8640007bd4348540006fe7358341006fe635032006efc401891003dfc715493005fbe740c54003f7e751053002fee7210d2004ff43108730007de434cb31006fc641812106f7e65084400a7ee2190d210aefe61d0f20004fd7018d410affa60d0c210077c6510930007f46390510006fe6350310146fe64c8430007dc63cc1100057c76551321477f54c8440
  | 1 => 0xd21004ff7654f20006be6408430004fd7690c21006fd43988310ef7e6455232006fd62d03100eefc648c9200defd7610f200079d4310c3106ffa7008630006f554d8532005f57110a31067ed21087400066f5458830005fd7190b300477f5410530137de4310d21005fc7350520075fd76c84400067f65d8530006fe43189310077f54cc940006fd648cb10007de4308730005ff7255130007de43c853008eff6018121007df43ccb310f6fe640c630006dd6388440004f77158d20007dc6350d210defc4398a40006ff64d89300a5fd7690c210067c6518d10007df6350d2104fbd7408730007f731c8730004fd7098e51006ee620c4300079d4310f20004fc7650d10005fe7310932005fd7418d210a6fe3198f41004fd760ca50004fd76d0c210067d54d8930004ff7058a31004fe76d0d10005fe72d8543136fe6448430007f54308510007fb21cc230006fe6350b200077f75484300077d548cb1002fbc64d01200057d75d01200077f735512002dfe7390d20005fe73d9110026fe6110c200077d750c940006ff43d85200067d5498d20005f97008430006fd644cb20005ff7158a430f77d5410831005ff72586430057d75191200b77d7508430007bd72d9130007df324c540006fc4358a51005ff70487300057d750c930006fc4398b31006ed7218d200077d54cc120007dc6390d21007df6390d21006fd6408530006ee739884008efc76486300067d5498e10005fc7254530007fb434811008dff7648630006ee62cc830007df630c5400bff97010630006ff64c853003dfe7190530006ff615013007f7d7510d32016fc4218d42006fd62d01101277d54d0c210af7e65d0c210bfdf310c6300df7d7599320004bd7498d21007f64308510005fd7210e30046fc644c120065fc7308740005bd740873004f7d75107300077c7655120004fd70d8543006fe4398831005fe73105300177f5410c320047e76d51300c6fd76084400047d76d5220005bc744c3100057e731895403efc624c310037fa7010d100067f5418d400077d544843011dfe740ca310077f54c8730006fc7650f21006fc4318951006dc7098c21006fc639092010f7d759933108fdf3048430065fc714cb400047d74d9530007bf43c85400077e6510f20077bf40c8440005fd7110d30007bd740cb40006be640c43005fbe7408540006dd7098c210077d5490d32005fc725053006fee62084300b5fe7110c30006df7098c21006fe7098f42135fe7418121005be76d0d40095fe7090e21007f72188430067bd740c740097dd30884300afef21d0e21006fc72580410077f75d912109efc7650c210077f65cc1100077d544c31010ffb40cc5400477d54d0530006fe63c8640006fc4358630006fc64d8530007dc630c54000e7e6510f20007ed644c832004ff7650f20097d
  | 2 => 0x57d7419532005fd7008530006fe64583310b6fe4118d1004efc61cc1200063f64d5130086fe64cca3002efe7610d20005fd720c640005fd700c8310079d4310f32005fe728c740007bf434854002dfe7418d20027f91010c10007dc638c540006fc7458021005fe7610d20007f77150c21007bd71d9130005f67690510005fe7610530005ff7050931056fc4298e40006fd7018d2013fee72d0e21004fd7098e5208fbf404844004efc64cc310006dc634c9400077f5448730006fd63884400adfd76d0c21007df32cc630005f4724c431136fd76d0d210b7f97008430056fc64cc3200057d70d8954006de63484400ddfe74ccb2003eff61185300047f765533107efe644c8320077f5488530005fd70ccb4104dfe71d8b30086fe64cca50004fc764c120077f430c8510005b57408510005fc7348530007f942cc130006fd6150320005ee7290f32004fe76cc940035fe7390d10004fd7098f42006fc62cc110007bf64c85300079d4310c210aff621d0c2113f7f5410e21006fe7690d32006bf640c530005fe72cc53014dfe744863014efd76d06300079f7250c4312dfe74cc830006fd545833200e7e6510e200067d654cb410067b5458021006fe6390b10007f76390510137dd4310d21006fc6418530005fd7099032007bf4398643006fd42d81310057d749973106fed6208430005bf744c320007ef6390920005fd7010e210077d540c630057de7310b30005fc73c8530007be430864005efd76085400067f6318d5418efc42d8d54126fe6408630005fd70993320047f7459410045fc74cc530004fe7690530005fd720c630005fc7648530006fe6348430006ff4358732056fe6310830005fd721873002f7f5410d20005fe7210530006be64cc83008fed6248440004be76191300077d54cc110056fc64cc110007f4430c72107eff4358a43006de7098c210067d5458f20004fe73989100067d65d0f31006ff6418d10006fe74d8121066fc62d0310007be4350f21006fe63c84400067d54d8f210067d5418f20006fe63d0a1008ff66148440006fd7098c210077f7155330004fc735925204efd76107300067d54586400077f54085400077d75cc640004fd760c8400067f54580310047f74594320a7fb1090d10005fe73c8540005fd72cc6300077d54c854006fee62084400077c7548540005ed7210c320077d54d8d10006fc64d8d10006fd64cc62003dfe710853003dfc7150930007dd43c8530007dc634c120007dc63cc940004fe76cc540006fc735802112efd76d043005eff625031006fbe6408430007de43d8930007df320ca40006fc4358a50005fe76d0930016fe640c8310377d54d0910016fe640ca310067d6510a20006bc64cc530005f5710cb10005fc73486400077f6455132005fd700c7200077d54cc5301377e751
  | 3 => 0xe7308430005f4714c832006de63c8440006f97358021007bf7448640006be7619130047bf4210930006fe760c940006fe7298c41007be4350d21006fd7098c420077f6588530004fc7358a410057d7655032006fc4358831006fd76cc540005fe72cc6400077b7055330007de4348530005ff7254c43006fe7690d210067f5498e4208efc4058b101777f4218954006fd64583320067f6218954136ff6419121007da43cc130006fe6498f2000e7e6510f310177f540cb400077d5448540006bf64cc930006fc435802105dfe7188540006f43298620005bd76d0e43025ff7610c21005fc7690d21005ff714c940004fe731891004dfe71d9330006dc6310d10005fc73487400067554d8532006fe6310a50007f521086400067d658cb40147fb40c86400073c6455120036fe7610d10076fc64c8630007dd43485300077d54cca30007df320cb40005fe73d85400063d7559030007bd4310c21005fc73c8740077fa40c8440005fc73505300077c735513212dfe7488430006fc435832110efc43d8543005ff7650f20005ff7155130005fd72d8730007f431c8530007dc434c832007fa42cc130005fd7010530006fe6348640126fd7610c21005f97010c30007ef62085400067d5458910004fe73d9032005fd710c830004ff7648640006dd630c8400d6fc43d8540026fe6110e52076fe30d8520005fd7090c31004fd76d0830005ef724c320007f721885400b5fc7408430006fc7650d21005fd7010d20005fd70ccb310ef7d54d0a320067d5458332006fe634cb4108efc40589100dfbe6410f20005fe7610d10005fe738864006efc6408430027bd6410f100bdfe7110a30006bf640853012dfc74c84300047d76d50210057d75d0f200c5fc7308440006fd50d8121007f921cc230007bc6490930007f842cc230035fe7418d10006fe7098c21096fe40d89100057d75d0130007bc6450930007df320c9300aefe639933109fee2150d210067f54580320069d4358043004fe76cc94109ffb1050d10006df7198c400dfed7210f200079c7250c430077c65105300077d5408630016fe640c8400069d6390c40006fd7018d54006fd6310420007f643c852106fdf30086300477d54d0930007bf4398a43006ff644853004dfe7118b30005fd7294530066fe6488440006fd63d0b20005fd7418121006be72d9130006fe4358331135fe74d8121075fd70c86400f6fe640c7200b5fe710c8301377d75191210057d7510f30006fd73d8121085fc7454f320377f5410d1012dfe74cc43010f7d54cc740005fe72d0530005fd71d0a3005efc31592100057d7419510006fe625011010ff940cc440055fe74187300bfef21886300b6fc4118d100077d544c9410077f6510530004fd76d0b3108dfd72884400577f5410b3005efc61501300077c7155330
  | 4 => 0xc21006bd640c830005ff7150130004fd70189410a6fe6158643005fd7118940035fc7610d100067f65481100057d72d8d54147f671d0f210065f5498c21005fd70d912109efe6150f320077c7255330006f443185320077f5490c31004fe76d0530006ff64d81210077c6588530007f731085400a7be6490c21006bd64104300077d5490d31006fd63d0a5006ff56108630005fe76cc540006fe7018d2113f7f548874004dfe7190b3005efc3158341005fe7319120006fc6348110097bf4088640086fe64cca10007f431c864009ff42150f10007ee644cb200dfbe64d0320005fe76109300c6fd760c4400cfdf310c6400feff43189400df7d5410720005fd7090f3205fbe6450310004fe731895400e7c5018d54006f4439862000f775110e510877d54d0f32006fc6350520007f431c87400057d75d0f3209dff7650f100077f5490c2104f7e75107300bfee2148630006fc63d8940045fe74085300b7dd7308430006d563cc4210057e765513206ff56108640006ee7298f200067f7655132007bf4250730007bf6448530055fe74c8730006fd62cc110007f4434842110efc64cc520006ff64d8d100bff621086300a6fe6190f32006bf64d853003dfe71949300f77d650c740176fc43189540077c7655130105fe74cc93113f7e75d0e21086fe64ccb3105dfe71cc9400067d5458e10004fd76d0832007bf4290b300047d76d52310067d54189410ddfc7458f20007dc634c9400063f65d9130007f8214c030005fd7110a3013fbc4388440005de7310730004ed72d9331007f940c8120004fe76d0d20004fd7610a30077f661c864003dfc7155130006fd630874009dfd7490c2108efc6448630026fe7610c210067e659903210eff4398e41007f743085100077d5458f20007bd4388540006ff4398831086fe64ccb20007bd74cc940004fc764c91006dff7008440006fd64cca100a7f42190f1003fbf4110530006fe6498331007df63cc940005ff7050e21005fd700c540005fd7090c2107f7c6455132005fc7258643026fe6110e30006fc74580320063c65d9130006fd4358221005fd710c940004fe73d89400afee21d0d21005fd7010d1004dfc7154b30005f970085400a7dd3190c31006fc43d8910004f77159132006fe4358221006ff3258032006dc7198c400067c6518d21007dc43cca320077d75cc530004fe76cc931006f73258440006fe3258041006ff74580320b7ef2108430006f5610c4400079c6490d30136fd7610d210067d6558f2005f7d7508540005fe73104200065f5458c21006ff7650e21005ff7059332006ff63d0520005fd7318121004fd768c720006fe76cc940005fd700874006fbd40084400077d65d0f200057d759923203fbf41905300067d5458620005fd71cca300067d65d0f200057d7519330005d
  | 5 => 0x6fd63486400063d64d50210067d5498b310477d75d093010f7d54d0b31004fc73583410057e7218154007df7348630007de43c8730005fd70108310a6ff6290f10006bd64884300077c6590d21186ff4218d540067d65cc830005fc72547300067d5418d21006fc43586320057d7595032016fe640c8300777e65c8430005fc7350910006f47358440006fd7018d42006fe7158042095fd7688630076fc3098b10005f9700c640007de63d0f20006fe7358041006fd63c8640006de63d0f20004ff7058843077f430c8710005fc734844013efe64884300b7ed2108430007f761c8530005fe7390a31004fd7610e200067f65d8d210077d540c6400075d54cc832004fc7358720004fc7359120005fe7218543006fe7690f21007df320c8400a6fe7690c21006fe7418d100067d5458a30006ec62cc9100077f5490f320069f7650c4305dfe710c9400067f5498c2104efc62cc310006ff624c11002dfe748c920005fe72cc440056fc64cc1200067d5458630007f543cc421045fc76d053010fdf4390f310877d65ccb40006fd6390b1006f7d6508430026ff1018d41005fe7210730004fe760c930006fe43d8530005fd72cc64005dfc760c540075fe720843004efe6310430006fd640c630005fc73c84400057d750cb30005f57190c310befc41d8d100077d5488430077f561c8440005fd720c5300067f65d81210067d65d0832004fd7098d21006fe631042010efc4298e41005fc73553200047d76d5320007f7215011002dfc7610d20055fe74d8b30005fd7110f30006fc6418930045fc7610930007de43cc9310047f745963108ffa4048440136fc76487400477d7510930004ec72591100b7de7308430006fe7098c41006fc7648540005fc72507300067f6518930026fe6110c1010f7d54cc440006fc3258041006bf6410d20005fd70d08320577d54d0730095fe7108440005fd72d0630097df3088430006fe6458032146fc64c8730006dc634c11005ff97008540006fd63d0a10007f643cc421004fc7650520005fd700c940006ff6318540006ff7650d21006fd640c81012dfc74484300077d54cc31006ffa700864009fbe6450c21005fe7610d2107f7d54109321277d65087400affb10d0d10086fe76ccb40006ff63d89400077d75cc740146fc4398a41006fc4358a30007f461c87300bf7e75086300067c7655330007bf6410930005fe76cc9400047d76d501011efe648c7200b7f4310843004dfc7150b30005fd70c8530005fd74cc832166fe6454c320f6fe640c4200eefe648c831097bd6488430006f463c8510006fd62cc3100077f75485400077f6548530005ee7690920045fe740c530006fc631854009dfd7650c210befe41d8d100067d54d8d200067f6510d10006fe7498f10004fd7018953076ff64c84300077f545
  | 6 => 0xf310c530005fd71d8b3006eff6408630006fd425803210f7f5410f31004fe7398a500076d548cb20006fd7098c41007bf4388540007f84388110146fc64c8530006de630c840007f431c84400577d54d0b300067d65cc840004fd760c420005f9700ca400076d544c832006de63884400077d64553310067d650c841007bc6450530005fe720c630005fe73d89400077f7055032006ff62d0110045fe7410530006f463c8521004fc7650d20006fe6388640007bd4308740005fe72cc730006fd4358720076fe40d85200067d5418d41005fe72d0730006bc7259030005fe73887400067f54d81210067754984301077c645513107efe644cb20007f4648c51006dfd7008440006ff61d0d52077de30c8530006fd6408630077fa30c8430045fe7418530106fc4258e41006fd64cca30046fe76d09300477e75d05300ddff7610f20006fe4358720005fe7290530004fe76cc530007f941cc1300067f6510d2114efd76d0a30007bf4390d21007df328cb40007f731c84300ddfc744cb20006fc6318121005f97010a300057d7218d54005fc7350930004fc7650b3003fde634c310007f841cc23008eff6448430005fe73485400df7d5410f20005fe73d91200067d5418f21077be40c85401477d7510f2106dfd76086400057d7510b32097f66188440005fd70c8740006fe6358e420077c6550d2108dff7048440007f674cc631007dc7348630006f44358620006fd7418d210cfef21886401477e65c8740006fd640c420006fd76cc4400067f654c1100067d5498a400077d54c8120077f561c84300077d5418d20006fd4398910017dd4310c3211f7d658c740005fd720c740006fe439891003dfe71d9130006ff6418d20026fe6110f200077d5450f21006f974580210067f765523204efe6388430005fd7018d21007dc63cc12006ff63008510006fc6250130007f743c8521006fe6350f21006fc4358b31006fd7458032097ed628844008dff7048430106ff64191310cf7e7508640007dd43c873009eff6250f10086fe64cc8200067f6518d21006fc4358a3113f7f5488440136fc64487300057d75951200577f54107300067d650ca20005ed7290c32005dd7308540007dd320cb40006bf6418530146fc43d8542004ff7058910027fa6010c21006fe42580311377e6548740007bc6450d21006fc7458332006fc4398a511077d654c740005fc725513013f7e7510e21007f52108530006fd75583320077d6550c3206efc3018910004fc7358041006df6310d10005fe738853014fbf42d063000e7e6510c2100e7c6510d21005fb7050f20005ff725533013fde4310e21006bd6410c300077f54c8430046fc4258e40005fc7650d21006fc4358430006ee62d0b31005fd7198a4303dfc740c53000e7f6418d540077d5490f210e77f5410f10
  | 7 => 0x83320cfee21486400077d544c320006fe6310b10007bf64885300077d5450d21147f571d0f21005fd71d8940046fe644c1200077d5488540106ff4358643006fc74d8121006ff75d8121005bc744c320015fc744c832005fe7690d200afbe64d0c21006ff7648730007dd4348730007be4308440005fd7010730004fc7358a400777e65c84400073e6455332006fc63c85400076d54cca32006ff76484400cff9700c640007f431c8730006ff7158043005ff71553300076d544c920005fd72cc530006fe42d8132007dd43885301377f5448440006fd6408430006fe6348440004fc76509310e6fd7610f1005fde7308540006fc43d85200067f65d8930004fd760cb10005fe72d85400177e6455032127bf4310c21005fd70d09300057d75951300047d74d9510006ed62c8310005ff71509301277f54d0c21005fe73085400077d540ca31007f843481100077d5490d2103dfc76085300077f5448430007bc64c8530007de43487300aefe61d0f32004fe768c92016efe6494c32005fe7294530004fd76cca100067f63d8954006fe43d85320057d75d083205ff4310854013ffb4088640025fc7154c430077c7155320047dd73d0530007de430c930006fc6218530006fe7098c4206efe7608630047fa7010930027df3110e3103ffa70085300057d75d03300f6ff4218d4108f7e6548430066fe760c740006dd63cc440007de4388530006fd64cc8200477f54d0530017fb400ca40057bf4210b30004dc73591100fdfe740c420007f84348210005fb70553300a6fc6190d30005f4714cb40005fd71cca40006fe63087400a5fe7310c21004fc7359220004fe7398b40004fc735901003efe614c3201277d5410c21007f52108740007fa21cc230004bf7650842006fc6310920007f643c862118f7f42d8d540cefd760c640006fc63d01100eefc42d8d420067f7655120006fc64d89300057d75990320aff421d0f100077f54887300067d6510a31006ff640c930006ee620c440005fd7008730007ed74cca32005f970cc7300b7bd74084300077d75cc4400067c755803105fdd7308540006ff6488530005fd7294730005fe73909320067d5458d200047f7459720097bf4088440007fb21cc130025ff7610f10005fd7010b32005fc7350a32007bf64105300077d54cca40004fd7610e10006fd7690e32005fd7010f100277e6510c21005fd7210d30005fd70d0910007f461c8530027ef2110e2107efe644cb3106ff66108430006fd76cca30005fe7690d21006fd7690c210f7fb400c5400adfe7410c2102f7e7510d2003ff970105300067d6510e2003efe760853008dfd7288430004fe7608530017df4390c32005fe73d0b20006fd640c430006ff4358221004fd760c64005efe3158341007ec628853005dfc73885400befd760c63003fd
  | 8 => 0x77f65d0530007bd711913009efc7650e2104dfe7194b301877f4318d54007f921cc130006fe7198c42007ef62885300067f65109300057d7510f20127bf4308740005f571d0f100077c65d05300057e7218d54005fe7210e30005fe73d0931095fd7088630066fe61d0320005fd718cb40055fe7408730006fd75583310577d75d0b30027f62110c21006fd7258341006bc6408530004fd7098e42006ff325834111f7d5410e31005fd72cc7400067d54d8910027ee2110d21006fe4258231016ff4118d42085fe7498332005fe7388440006fd4258232006fe6250310006fd61d0e52005ec7250120005be7408630005fd74d8d2103f7e7508530067df310c740005fe764854003dfe7110930007bf4390f21006bf6410d10007f943c8120096fc40d89100077d54cc910005fd728c7400077d548c831086fc64cc910004fc7358810006ff63c8540006fc625011006efe760844003fef21885300a7be6490f100b6ff1018d100063e7559021004fe73d9151005fc76cc9400077e750cb400067754d8532006ee62cc840004fd76d0430005fd71d093004fbf4110730005fe72d8d40067fa7008740004fc7359110004ff70587430077f54c854002ff97010d200077f7055232006fd7218d10004ff7058a43146fe64c853005fed2108540005fe731081004fbf4190730045fe74109300063f75d91300067d54d8540096fc6488630007df32cc530005fe7690d100077f6550d210077d645523213efd76d0e21006fd32583410067d6510f310057d75cc520004fd70d89540077d65d0c320a6fe7690e21006fc43587320077d54cca100077f6590d2107f7d654cb40006ff625013008fde3048530006fd7098e410067d54988320477d75d0530005fd70d0a320067f6518d101377d7510d2106fdd6308440087fb40cc940007f721486300cff62108640005fd7010f31007f743cc421004ff7650c32006fd7118d40006f943580210057f7548530007f543c8621007fa43c8120004bf7458d200077d544c52006dfe7010c2109f7d6550c210067d54d85430057d75c8120006fe4358432006ff43d8951006fe6350110045fe74485300067d5458321007f72150310075fc7050f21006ff76484300077d6510f20006fd64cc83008ff561484300057f765503206ff6610863012dfe74c8430127fb4008540004fc76509100075d544c832006fc4398a30006ff644c520005fd74cca32166fe6454f3208dfd7648440075fd70c84400a77d6590c210077d540c5300377e7510d10007be4350e21005fe7208540006ff62d8530004fd76ccb41004fe7690d3108ffa3048430117f97010e20006fa4358021006fc7158032004f77158d21137f67110d21006fe63884400067d6510f200067e655803208fbe4048540056fd76d0b30006fd6310810006fd715
  | 9 => 0xd658c8410077d54d85300063f6455120006fe62986430067f65109320067d5458d21075ff76c8440005fd7290d3003efe4158331006dc7498c210077d54cca32006dd6390c2108f7d6548440004fd7610c2008dfc7050d2108efc3058b101377c6455121005fd76d0f32006ff62cc110045fc76d09300bfbe740863007f7e545513205fef21085400057d75cc5300077f540863003dfe71191300067d65d0c2109efe6150c32006fd760ca400cefc31d9110006fd76cc940006ff64d8d21004fd760c4400077d654c320045fe74d8930077be64c8430006bd6410f10067ef21887400067f5458332004fc7358740075ff76c8430006fd640ca500aefe76d0e210067d5418d4208dff7648440004ff7058642047de73d0530004fc7650930006be64c8430135fc76d0d2103efd76105300077d5450832006fe43d8931005fd720c4400063c65191300067e7518d400677e7508740004fe73d9121006fc63485400bdfe71cca300057d75d09300077d54cc930005fd7288540005fd701093212efc4218d4008dfe70d9121007be74cc540005fd71cc9300067d5458c20006fd4358432006bf6418930006fd745833106ff64008510005fd7110930006bc64cc93004dfc71553300063f6519130046fc4158e40004fe7318951005fe720c6400047f7459421007f76108730006fd7158342004fc73580420057d74195210067d54d8d2109ff96050c210067d5418d10006fd63d062008f7e65484400067d654c320004fc735832105fbd740854008efc3058910005ff7650f32097fa40884400e5fe748cb100577d7510b30005ff7048540047bc64109300057d7510f32007f543c8510037f97010d10007be7219130136fc6448530006dc63cc1100077554d8532006ff7258043005ff764c320005fe7310a30007bf7448440005de73085400477c645513014dfc74cca300f7f9400c440007ee7290c21007f731c8540004fe7398a54005fd70c87300057d7510530004fc76487300077d544c83206ff71008630006fd6458f20004fd760c7200477f54d0930007bc6448530006bd72d9130005fd7010a310efde4310e32007df32cc740007f842cc1300047d76d503005dfe718c940004fd7098d20005ff7150330004fd76d0630007f7648c51011ffb408c540007f52108440055fe7418b30007dc434cb310d7f97010e10004fe768c9400077d540c940005fd7498032004fd76908310077d5408530006fe7358021006ff43989100a7f96090c21007f643c85100f77d540c740006ff614c120004ff7058a510777d65c84400177d7599032005fe72cc740006fd64c8530077ee62c8430005fd7118d40006bc640c53006efe6008430006fe4358031007f930481100067f6519132004ef7259110006fe63d0f211477d54d0f210aeff62d0f1007efc4358a43
  | 10 => 0xc91015dfe740ca50004dd73d9320007ef648c9200077f71553320077d54583310af7d65d0c210067d5458b310067d650ca310057e7318154006fe73580310067765d8532047bc7119130006fc6350320056fc4198e40095ff7088630004ff705844304fde63cc310077df30c86300bdfe71d0a30006fe63907200057d7599332005fe73d0630004fe7608540005fd72cc4400e77e7510f100077c75486300067d5458430007bf4390e21004fd7018d51096ff64884301077d544c740005fb704cb400067d54d8542005dc7348430005fd74ccb310067f65cc110005fb7050b300067f7655130007df32cc640055fe740c730095ff76886400dfee7210f2007ffb404c940006ff6408730006fe6350d210577e75d0730006de6350c21005fd71ccb400063c75d9130005fe7290730006ee62ccb310057f755833203efc415833108dfd7648640005f7714c9400a7ef2190c211377d54d0d21006fd64485300077d7018954004fd70d894308fee624843006ffa7008440006bd64cc430005fe7318121007f52108730006dd7498c21006de6390c210fefc4318940004fd768c831005fd72d8543007f77150f21005fd70d0f210067d54586320057d75d0a320077c65d09300a6fc1098f410063d64550300877d54ccb400047d74d9521006fc4358810137fb40486400477e7510930005ee7210d2006dff70084300177e650cb400067f65d8d100defc64c8120004fd7018951077ed62c8430006fc6418d20006fc4398831007f44308510146fe64c8630004fb7059132005fe721043005efc61501200067d7518d40006ee62ccb41006ff6418d210077c7255332136fe64485300077d750ca300067f65d0910006fd63d082014dfe740ca300067d5458e20005f57110f10087f940cc840007f743c8621067df318c740005f47250710005fd7210630005ff7458332006ff7458031006ff4358720005fd7110c30004fd7098e41007f731086300077f65d09300077d540864013f7e6588740006ff745802103fee2148530007ed6350b200adff76d0c21007bf43d8540095ff7688630006fc63d09100079d4310f21005fe7310720007be43c864007f7d5410d32006fd63886400077f54485401277d5408740136fe7610d210067d7518d2003ff621085300a5fe7198a4310f7f54cc7400077d54c8310006fd760ca30004fd7610830006ff61d012001dfe740c8100bdfc7488630127f94008440006bc7159030095ff7688440007f9700c94014efc42d8d4008ff56148440006bc64d853013efc64887301877c4218d54006ff6348540007ec62885400c7df310c440007fb4048110006bd64d0430005fd720c730006fe6350120005ff724c540004fd76cca400077c65d0d21107fb404c540006fd7098f200063d6455020007bc645011010efe64cc4400067
  | 11 => 0x4fd7098b43006fd625011008fed6248430006de6310f20005fd740c831147ed7210f21035fc74cc110005fe739053005efe7608540007be4348640005fe731912105dfc73085400067d5498c20007de6310f20135fe7418d21006bd71d9130075fd76c86400079d4310d21007fa41cc130006ed6210830006fd735804104efc41d8131136fe64486300077f54884300067d65cc8320057d7510d32005fe7294730006fe6350c21005fd70cc94003dfc7688530007bd740c940006fe4398821006fd7498c21007795488110004fe7398d210cefe31d911005fbd740c540066fd760c74004ffa7008730004fc7359021004fd7098a430067c7655120077ee62c84400067d54d8d10077bd40c844010efe64cc43004efe61cc320116ff43d8940007de4388730005fe7650d210977e6588430004fc73584420eefd7610e32005ef764c8320f7df4390c31007dd32cc7400577f54d0730004fe76105300c7ef2188440006fd6310b100073e645523209ff43150c21004ff7650c21056fe76d0730006fe5458331006bc6418530007ed7290e21006fe63107200077d5418530006be6448430004fc7358a54005ff7458032007bc430864008fee6248440057dd73d0730056ff4198e400877d54ccb410057c7655121006fd76cca40007bd7219130047bf42d0530005f9708c7400077f715513208efe3058720086fc43d89430a7de6390c21004fd76d0a30137bc64d0d21007f543c85210077d5458032075fd76c8630006fe7458031004fc76485300a7f43190c21005fd73d8121025fd7610f10005fd70d0c21007df32cc440005fe72d043009ff47150c21007f7214864016efe6494f32006fd76cc640006fd6110e50004ff7650f10007bd4310f21005f570cc421006f8439802109fdd6350c2107efc644c9100075d54ccb31006bd6410c32027fb1010e10006ff7358041007fb43c81200077d544c910005ff704c941007f84348020027fb1010d10067ee2148740005fd7210f300057c7655130006ff7158342004fe7318941075ff76c8630004fe73d9110095fe71084300077d548c940006fe7458021004fd7608630087be74ccb40005ff7055032067f62108740005fd70ccb40004fe7610730005fd72d05300067d650cb400075d548c932004fe76d0930075ff76c8640006f56110430076fc64c8430006bf64c8530005fc72553300077e75cc540006755458620056fe63d0430007d6434c4310f77d540c440004fd7098b31005fe768c940004fc76553300077f65d0d2106dfe70d0c2111f7d548c740076fe30989100077d54c863005dfc714c940005fd70d0b31006fd7018d210077d540c42009efc6350e21004fd761043002dfc74cc120006fb4358021126fd76d0c21004fc764c540005fe73c863009fef2150c210067f6218154006ff64c
  | 12 => 0xd71d0b300f77f5410c31006fd4318910006fd43d8121005f97008630007f421d0110006fc4358420006f44358430006bf64109300067f650c9300bf7d75086301477d65c87400077d5450a32005fe720c7400067f7655032006ff64cc53013efc6488530004fe7610d100df7f5410f2018eff42d8d54057de73d0730005fd71d9330087df4390f3205efc6250310005fe73c8120004fd7018d4204f7e7508730006ff6218930005fd7010720006bf644853004fef2188730004fd76108100067d545873206ff7100864012efc4118d40006ff7358342006df7158c40086ff4398e42004fb764c03007f7d544cb40077f561c8630127df4350c210063e7559030097be4088540056fe63d08300057d7519132006fd64087300067d5498b30006fe63d0820007bc6490530006fc4398810097f56188440006fd7098f420057d73d8954007f431c8430006fe43d8121006ec7458830005fd71cc8400577d75d0730007bf64d05300077d5448630004fc7358021005fd76d0f31006dc7158c40006fe431891000f7f5210d510067d54d8520006fd6350b20006dc634c1200067d6599032005f97090730006ff63d0910007f743c8510047bc6410530005ef764cb200067f545802100e7e6510c30006fe638ca4108fdf30486300077d5450e2109fed2150c210067d5498e40005fe7310a20006fd4398b10007f543c8710086fc64cc931006fe6498032005fd721854013fed72d0e21046fe644c1100077d54cc820055fe74487300067e6598f20004f77158b300057d75d8730006fd62503100a7ed2190c21005fd70cc520005f9700c7300077f5490f21077f561c864006efe6008440006fe7258031007f443c85210067d5498a30007fb41cc230005fd7610f20106fc644c5200077d54d8121006fc4358a10004fd7018f210057f7548730005ff70593310877d54cc840007bc6450120066fc63d0310004fd7610f2013f7d7510e21005f97010930006fd64cc832006bc73590210defc43988200077d54983310077f73553200077d5450c320067f5418d21004ff7650b31006ed620c84009eff6118543097fa30884300067c7655320005fd70d0d21006fe4398b100057d75d0320004fd7610c31076fc40d85200057c7655110056fe64cc120004fd76cc440007bd4210930007795448110007be71d9130027f67110e21006fc4258031095fd708864009fde6350c21005fe720c5300077f75d91320befd7608630006fd43988210aff960d0c2112fbf4210830005ff7150b30097f5618843008efc7648430005f970cc430006bf64d8930004fe7690730005ed720c72006dfd7008430007f643c8710007f4214c110006fc4358331005fc72501300df7d54d0b20007dd4388730007fb214c030005fd72cc73010fdd4310f31006fd53d8121005fd7090f21
  | 13 => 0xd100ddfe740c720005f97090f30006de63d0c21005fe7219330006fe63d0a50007fb42cc230005fd71ccb300067d6510e31106fc43586430067c7655232005ff7154930005fd7110b300077d54cc320037f67110d100377d7510d10016fe640cb10005fd72d8d400077d65cc320007bd43c87400977e65884400067c6519132006fe42583321277f5410c21007795448210067fb10d0110005fe73185400057f754c1200aefc63d0e210067d65d0b311277d75d0c21006ee62104300075d544cb31006ff7648640076ff64c863003fde7310530007f8424c030005fe728c940006fd6348740005fd7490d21006fc638854005dfe710854002dfc744c120006fd7418d20006fc42d8132004ff764cb41004fe761093012dfe7408430007f721886300067d65d0b201077d54d0931006fe7358032005ed7210f20007bc6490d100aefe76d0c210077d750ca40005fc764c540005fd7095332005fd7090d21006fd640c831004ff76552320ddfe748c7200057d75d05200077d54cc5400077d6455332004fd76d0a100067d5498c300c7f621084400067c765513006fdd3008430137ed7210d21016fe640ca20015fc7458032004fd7610e5006dfe7090c2109dff7650c210067d65ccb40007f7310864012dfe740c430005fe72cc4300073f64551300057d7510730007f841cc130005f9700cb30004fe7610d2008fbd4048440046fd76d0530005fc724c740005de7310930027f42110f1006fde630844007eff6419132006fe6310a200cdfe71cca40005f97010630006fe7458032006ff644c910006fe63d0d21004fd7018931006dd630c440006ec624c94102dfe74d8d20007de634c320007bc6488530006fd7118d420047f74596200777d65c84300bdfe7110e300aefc41d8d4106dff76084300577f54d0b30006fe7418d20006ff61cc12009fbd6450c2114efc41d8d4007efc4158e42005fd709933114efd7610a300c7ee21484400cfbe7408640027dd3110c31006de634c310007f643cc721005fd7219330004df7359110006de63cc4400067c7655032006ff6110d52004fd76cc840007fb30481100077d7318954004fc73592210a7bd6490c21006bd64d0830006de634c32003ffb104c110005fe72185400077d5408730056ff4298e40025fe7390c21004fd7610720007de43cc530005fc7348110006df7458c2100f5f5394c43005f570cc721005fe7310920006f663c87100aefe61d0c3208fbe6448430004fd768ca41004f7764842110ffb40cc640016fe6459032005fd740ca3104dfe7110b300077c6510d101277d54084400077f54086400eeff4398a43005fd710ca30006fc43582210067d5458a430077f7548630007bd4310d2101efd7610c10005fe728c540006fe43d893002f7d7510d20007fa21cc13008efc6448430005f
  | 14 => 0x5fd7010c21007f721487400077c6510d21004fd7690a310067f6510d320067d6510830006bd64d0c21005dc7350130146ff4398821016fc4318943066fe640c440006fc64d81210a6fc6190d32005fe720c440006fe63d0c210057d7519130006fd64885300077d5490e320977d65884400077d5418930077f661c843003ff4214c310006fd6110e52004ff7648630004ee72d9331126fe64087300177d54d0c32007f443cc421006fc42582310bdfc74086300a6fe6190e32006fc4398a50005ff7454c320e5fc74cc310006fd644c832045fe741893013eff43d8941004fe7690b30005fc76505300bdfe710ca30006fd7358021006fc63d012004efe41d8131005fe7210d300577e7510b3003dfe7118930096fc30d8910007f7214853008efe4058720005fc735012014dfc74c8630006dd63cc840097ee6288430006fe63c87400eefe64592320bff9700863015dfe74cca500057d7018d54005fe72d913009efc6150d200c77e750844003dfe71885300067f6510d3008dfe7019121005fe7310930075fe7010f21095fc7050e21005fd7008540005ff7050832004fe7610b30026fe6110c301377d6548740004fd76106300077f5450f21004fd7018d52005fd70cc740006f643d8532016fc640c930004fd76d0620005fd7088530026fe3118d4104ff621087300077f64551310afde63d0c21005fd720c430004fd76cc8200477d7510d30005fd7290f30007f543cc7210067f5418d4102dfe740c920007bd74cc74017f7f43d89540aff431d0c2114dfe74cc630006fe6458f20005fd7010c31035fc744c1100067d654c832006dd6308440007ec6390920006fc43d89510077c7548640004ff70588310077f540c940005fe73d06200057f754c832006bf64d0d21115fe740ca200077f5488540006fc43d8530005fd70d0b30076fe4098910005ed72d0f20007bf64d0930005be74085300047e76d5121097de308853000775541853213efe648853005dfe71d8d400047f7459731006ed628c84102efc4358a400077d54c86400067e6558331055fe74d8730006fd76cc8400a6fc6190d20006df7298c40005fe73c864007f7d544cb41005f77048421006fd64c86300877f5410f320b7bf4110430007df320c94003fdd7310530004ff7058632075fd70c8430004ff7650832007f9214c030006ff6388540005f77150310095ff7088640006fe4318930006fb7358021006fd76ccb4014dfe74cca3006efe7608640005fe7310d21026fe6110f320067d65cc320027be6410c21006fc7358341005fd7010f200057d75cc7300afef21d0c210077f5490d210afdd63d0c2106fbf4008640077f630c85100057d73181540057d75d0b300067d54d8f2000e7c6510d300a5ff7690c21004fd7690720007bc7448640004fd7610c21007dc63d
  | 15 => 0xe640ca30005fd7210c30007be43886400077d750c930006fc63d0520006fd5458331015fc7454c32006fe4358032026fc6110d300067d6510c21006ff4398a51045fe740c9300067f5418d10006fd7358341004fc7358841136ff4358a41006fd6448630067f421d03100077d5448640016fe640ca50077f661c8630007795448020006fe4358910186fc4218d54005ff7154c43006ff6318d41097ee6288440006fe638c841007f73108530006ff6318d420077d7559331005ff725453003dff764c310146fd76d0f21067dd310c740007fb40cc1100067d54587300adfd76d0f100077d75cc54008dfd76486300067e7598e41006fd7018d4102f7d54d0d20057bf42d0730007f72188640006bd6410f32137bf4310d21006fd7690d21005fc7350b200067754986200bdfc7388630006ff43d8121066fe64084400067c62d81540067d54189310067d5458e40006fe4358332004ff7648440007be43c844003dfc74885300eeff41d8d42004fd7610c32006fe7458331147fb40c8540006fd7690e31005fe76c854011f7d5410a3106dff76084401077d5410d31006fc43587200067d54d8943097be6488430006ec4398830007ec648c920005f4714cb200077d5450b310057d7419530006fe7690d31007bd4348740004fd70d89530067465d8532006ff43189100f77f540c740006fd64c8430067be740c7400bfef2108630006be64884300077954cc230006fc4318931006fe63d0310005f5710c831005de7308630004fe73d932108eff6448630006ff76485401477d5410f2103fbe7408530006fe63d0320005fd7010f321477f54d0f21147bf4310f21006f764d8532005fe734863005dfc7608540005fc7350110005de73d0530007dc43cc931005fd7190d3002f7d7519120127ee72d0c21006fc4398910004fe760c940006ff63909200077c7355120006fe7358342007be6450320004fd7098e2113f7d75d0e210077d5490e2113fdd4310e21127df4390c21006fd63c87400077f65d0d100077d7218d54004fd76d0a500069c6350d40004fe7398d10005fe72cc540006dc7298c400077f54085300067d5418940006fe7198e42007f431c85400077f5450d21006ff4398b10017be740cb400afed21d0c21006f43298440006fe6458332004fe73d8121005fd72d0730005fe73d0520007f5210843004fee21487300ef7d7510e32006fd7418d100057d75d053003dfe71cc93008f7d65484300077d7155132005fc7348540025fd7610c210067c7655132004fe76d0d2108efc7648440004fc7359250006fd760c940005fe7608540045fc74cc930006ff74d81210a7dd6390c21007ee644c832006bc6418930046ff4158e40026ff6210f1014dfe7488630007f743c871006ff440085100077d544cb31006fe53d812113f7d54d0e21
  | 16 => 0x8a511277e75d0c210877d7599332005fe769093004ffb10cc1100067f65cc9100077e7318954005ff70590320063d64d5030006bf640c9300077554c8521005ec724c120007bf431894013efe6488630005ff7650320046ff4258e40005ee7290d20007f73108740006ec4358830005fd70908310067d5498820005fd72cc430097df3088630005fe7310b10007f443c8621005de7690d300067d5458a10027f67110f100077d54c853002f7d541092010dfe7498331006fd74580210eefe648cb10005fd72d8540047dd73d0930006dc63cc120005ff7050c211377d5410d210e77d7510f10007f843c82200077c7548530007bd4210b300077d548863014efd7610e30004dc7358910007bd4308540006fd7498f10004bf7458d10006bd640c4300877f54ccb40007dd320c940056fe64cc110006ed620c830006fd648c83108ff661484300077d5418d210477e75d0930006fe624c110005ed7290f200077c73551300077c65085300073d6455232006fe4398a31006ed6290831147bf43c8740007f761c8730077dd63c8440005fe73c831006ffa7008430006fd4358b1014dfc7448630005fe73c8530006fe7418d21006bc64c85300377d54d0d1010f7e65cc740006f44298430004fc7358221135fe7410d210077d54583320075d54cca32006fc63d85400067d54582320067d54d8d42006df6390d210077e765513203eff624c3100077c7255132006fd63084400477d7519130006bf64105300067d65580320bfde73086301277f5408740106fe7610d3103dfe71d0930005fd7088740006ee74988300f5fe748c831005fd700c841005fc73c8540005fd710ca40005fd70d0e210057d7510932006fd7018d40004fc7650730004bd7690c400057d74994320077f6508530006fe74583320077d75590320bff43108630005fd7194930007be74cc9401077d7519131006bf7359021006fe63487400067d6510810006de7498c210077c7055032005fc7250330004fd76d0c32006fe4358b100a6fe6190c320077d54d8d210077f754864008dfe7010d21006fc325803107efe7610d32005fc76cc5400077d540c81009dfe7118943005fd7118930005fe720c730005fd7010c32065fe71ccb40005f97008640005fd700ca41006f57118d10007f421cc110006fc3258241004fd768c841006fc634c941046fe644c31000f7f5210e52005fd7210530004fd76cc640006fd4358910006fd640ca31006be640c8300067b54980210067f5418d42005fe7688530056fe76d0b30086fe64cc84000677541853209efc6350c21097ed62884300067d654cb40007bc6490d200079d4310c32005fd71d89430bfdd73086300079d4310e210afbd64d0c21006ff4358432136ff435864200775544c5100a5fc7158a43007f743cc721006fd7098e42016f
  | 17 => 0x7fb41cc1300bfbd7408630005fc7650d10115fe74cc62008dff7648640005fe7399320006fd7198f42005fe760c94004fde7310730006fc6350110004fe7690920007f72188530005de7310b30006fc439883009efe6150c21004fc735891006ff710084400077d5408430006bf6410d3006fbd6408430005fd7090e210b7ef2188430004fc7359320005fd71d8d40005bf744c1200a6fe6190c21006fd6388740004fd760c8410057d75d0c32007fa214c03006fdf30084300067c65191100079d4310d10005fe76c85300b5fe7110830006fe54580320067e6599320004fc73590200067d5418943116fc43d8940005fd71d0830005fe73c8740006fd735804208fdd6348440004fe7398b410077e7218d540377c64551100df7e7510f20006fe62d0110066fd7608740027be6410f1006dfe7188440147f940c8440006bf72590300b77e7508430006f873580210077d54983320077f7558332006f464d8532005fe730863008dff7048630086fe64cca32005ff7050a32004fc7359251007bd4310e21004fc7359121006dc6390d21095fd70884400077f54c86300077c7055332097bd40884400057e73d8954066ff62d03100067554584300f6fe640c430004fc7655120006ff63d8540007f72148440006de63cc31010f7e6455331086fc4198e4206efe30189100077d70551320077c7548740006fc43d85320067d5498f20005ff7458331005fe7388540006bd640843000e7e6510c320077d54d8930004ff7058a410057d7508530047bf7119130127bc43084400cff97008640005fe72d8530005f5700c721006ff4258331006de63cc320006ff7358042005fd708ca41047de73d0930005f57110c31006fd76cc740007f843c81200067d5458420005fe73d05300e5fc744c310007f8414c030006775458620004fe73988400077d540c720006fd760c840006dc6350d21047bc7219130006ff61d0130077f640c8510077f630c8710006fd6458032067be7408740006ff6250110004fc7654d20007f47150f21137fb404854012dfe7448430005f9700c4300077d540ca30006fd6448430005fd70cc941007be43484400aefc61d0d20007df328c9400cf7d750864014ff97010a300067e7518d20004ef7258d10006bc64d89300077c73552320067f76553200277d6510c21006fc4358031076fe3098b100077f6510d21096fc64884300bfed2108630136fc4358a41015fe74cc8320067d5418d20007dd430c831137f57110d210067d545833113efd7610e2109efc6250f10006f84358021006bf6488530076fe60c8430007df324c7401377f54d0d210377d751911000f7f5110d52006fd614c320007fa700c9400a6fc6290f10005fd720c5400077d750cb40004fe73d9120005fd7218530007ef62885400079d4310d20004fc735
  | 18 => 0xd540ca410477d54109300cefd7608640006fc73d81210073c6455130006ff6350520006ff640c5300cdfc7388640035fe74cc9100067d54d8530007f72188740015fe7498032095ff7688430006fc76551320077f7548530007f930c812006ff661084400d5fe74cca1014eff41d8d400067d5458a40127dd4310c21005fd7090a31005fe739092004efe6308430004fe76d0931006ff7650c210057d75d0b20006ff4358910005fd710c930007de430ca31075fe70d0f21005fd7690f20006fd43580210177d650cb40006fe7298e41005bf744c1100057d75d0d200aefc63d0c21005fd70d093109dfe71d8943005f57110b10006fc43d8931006fc7358042086fe64cc8301277e7510c2109efc31593310a6ff1098f4113f7d6588740005f97008530047dd731093005fdf310c5400067c6318154006ff62d8543006fd7690f21006de630c440005fd71cc83002fed7210d20026fe6110c32006fc7358342004ff7655032005fd7110830006ff64c8730005fe73486400067d5458643006fe4358021004ec7258d10005de7308640005fe7210f300a6fc31d913102dfe74cc520066fc61d0130006fd7498f20006fc4358432127de4310c21004fd7690f200047f7655030006bc64545300077954cc130005be7408730005fd74cc9310c7be7408440006f742584300076d544cb2003f7d75085300077f5450e21007bf4358a4304efd7608730006fc6350d21005f9700c830005fc76c8530006bc644853002dfe74c812004fdd73107300aefc61d0d52005fd7290530006f874580210057d75107200077d54ccb20026fe6398643006bf7159030005fc735031009dff7650c31004ff7058442005f97010e20005ff7154b300077d5450f32006fe7498c210277c5110d51006fd4398b31006bd6410f31005fd70c8540006fd6458331004fe7690d200067d54d813112eff4118d400cdfe710ca400057d70189540877d5410b321277f54084400077f7055332126fe6408430006fe63d0b20006fe6498332005fc764c120137bf43487400077f5490c32005f6768c510005fd7090c32006fc6350f210077d5448530027f96010c210077d5450f310077f5490e210057d7518b300067d5498c320077e7355132006fc4358032007f443c8510005fc73509310c5fe71cc840006ed62cc440076fc30d8520004ff7650c3106dff7608640026fe7610e21007ce434c832004fd7610f10007f52108540005fd7090b32005fd7498332004fd7608640006fd61d0320004fe7690d10005fc73593200e5fe740cb10005fd708c841047bc64d0530005f4714c940006fd75d8121005fe76d0d10006fe4398b31007de63cc320005fe73d0a30004fe76d0730006fd76cc630007f721487300077d5498f20004fc73584201477d54c8740007f731c8630006bd64cc830
  | 19 => 0xc520076fc4098910005fd7190f30005fd7119330005fd72d93300067d5498f210067d65ccb20005fe7308640006fe7098f410077554cc531006ff431895104dfc7488730005de73d0730005f47348421006f642185320067d54d8d40007de438c831006fe7258041005fe76d0d20007fb40c812006dff760863008efc764864013fbf4310e21046fe644c320006fc64d8d21006de63cc8400076d54cc932006fd640ca30005f97010d10007bd74ccb40006ff64cc9310077d6455032007df32cc54004fbe7408730005f9700c540006fd6488630006fc4258332006fc76487300067d5458e420067d54d8d41047bc64d09300047f76550320057e7655130004ff7654c4200e7c6510d32006ff6408530007bd4388740007be72d9130004fd7098c210cfde73086400077d540c5401477d54c8440006fc6350910005fe72d933003ff970085300077f7548740004fe7608730004fc76551300067f65d0930027ef2110c21007f7214c1100677d7508740004fd7098c41005fe730c540126ff431894105eff61185400067d5418d400057d7510920005fe73c84400077e750c940005f97010e10006ff62d8540096ff64886300cff4310864000575758c510006ff6448730046fd761093010efc64cc530095ff7088440006de6310c21006ff4358b100e77d54d0f10007bf4308540045fe74cc9300077c7548440005fd70d8d21146fd7610f21006df7498c21005fe769053014dfe74c86300077f5408730004fc7359210147ee7210f21007fb42cc130007f73108440007ec6208530005fd71d8930006fc7158043005ff7650f31007f5430c721026fe7610f10006de6308440005fd72cc540137bc74484400067f654c910005fd73d9121006ec62481100077d750c84003ffa7010530007ee74cca3204dfe71ccb30006fc43189300067d650c830005ff725013005ffa7008540006fe6308640005fd70887300cfdd7308640137f940484400b7ee2148430005fe76485300057d75d0730006fc4358830007bc43c864010efe64cc620005fd728c5401377d5448740004fc764c940005ff714cb4010dfc74583310067d6598f2008efe50d81210b7f621084300977d658843003dfc7150130007de430c5300077d548c7200177d540c841006fe32582410075d54cc9310f7dd4310c310f7fb400c640007be6490f200eefc4398a4308dfe70d8d21006dd6310c21005dc73503300cfef21086400067e7518d420a5fd7690f10005fd718c94003dfe7110d30004de73d9320006bc7359030006fd7218d41006ff42d813104ff421cc3100079f7150c430067f765533203fbd4110530007f6430c7210077c7655132005f97010d200077d54980320067f63d8154005f970105300077f544863006fed62084400067c765533205efe6150320004fe76d09100077
  | 20 => 0x6efc6408630006fc63d0f2112efd7610830005f9700c940006ff7558332006ee62d0830007f7218844013f7d5410e21006fd7458332005de7308530004fc7655132005fe720c430007bf6410d200077d544cb2009efe3159331006ff64d8530006ff6150120007bd42d0530006fe62cc110007de43cc9300077d54cc9400077c7548730006ff63d8121006fe4358831006fd43583210077d54c8730005fc7355120095fd76886400067d5458b300057d7510930006fe735833208efe305891006efe4018910067f97008740006ed62d0430006ff640c920066fc31d8141005ee768c920004fc7648540077f640c87100bdfc73086300e77d5410b100cfed210864012fbf42d04300067e65993310079d4310f10007f721d011004eff62cc310005fd700cb4004efe7608730004fe76109320077e7255132007f940481100057d7655320006fd6258643006fd6310a50006fe435832104dfe71d0b30007df7348430004fe7610d21006dc7458c210077f54c8640097f6618843007eff4258e42045fe74885300077d6550f311877f4218d5405fdf318c540027de6310c21005fe7290d30005fd7194b300067d65d0c32006f43298430007de434c832004fb7648020006fe630844014eff42d8d40004fe76cc9100077d54d8d20005fd7090932004fd7098f410063d6455332004fe73d9152006ff64d8d20005ee72d0d200067c7558332147df4350f21006fd64c8730005fd72d9130004fd7690b1010f7d54d0f31006fe63887400077d5408540007bf640853006dfd76084400047c7655130056fd76d073003dfc740853006fbf4008440076fe4098b10005fe73d9121095fe7010e21004fd7018d54004fd7610a31056fe64cc310004fd7610a50004fe73d93200067d65ccb31006fd7018d10006fc6418d210067d650c810004ff7058b43045fc74c853012eff4218d400067d650c840005fe7390930007dd43085300077d540ca2005fef2188540036fd7610d10007dd43cc83217eff43d89540066d54988300077f54cc540006ff64cc930027dd6310c210067d5458720005ff7050b31006fe760c9300067d6510c3005f7e7508540004fd7018943067be64d03100076d654cb20005fc7254c43005fd72d0430005ff725473003dfe7190d30006fd760cb40004fe760c5400edfe74cca3203efe7358331007de4308530007dc6310d10006fd64ccb3105efe760c540045fe74cc530005fd721073008efc40587200057d731895408efe6048430007f821cc230005f970ccb30005fd700c7400aefc62d0f10007f73108730005fd70d052003dfe710c930006bc6454930055fe740cb300defe7610f2002f7c6455120005fd710cb400077d5488640005fe7218730005ff744c832076fe60c8440127fb400864000f7c5210d520067d5498910004fe76c
  | 21 => 0xe740c950006ff32d8141016fe760cb40005dc7348630005fd700cb10007dc320c630006fc4398a10007f9700ca40006fd5458032007f574cc631006ed62cc430006fd6310720005fe76d0530005fe721063017f7c43d8954005fc764c94005fee2148540006ff7258331006fd61cc320006fd639072003ff43108530097dd6388440007f54348421006fc76485300067f75583320057d7599320137df4390d2102f7d5410d20006f643185320ef7d658cb400057d75087300057d75951320067d5458432006fc4318910077bf40c8640006fd715804305ff621085400047c7655110005f4724c710006ff7458332027ed2110c2108dfd7648430006fc62d0130026fe6110e32137ee7210d21005f970084400077d54908310077f70551320f6ff4318d4110efe64cc630005fd710c840026fe6110e5008efe6048440077de63c84400ddfc74cc3200067f5498e4103fdd73085300075d544c93106dff7008630006f44398430005fe73485300077d544c540004df7358910095fd7688440005fc760c940005bf744c310005fb7050d10006bf64d0530006fc43d89300076d548c9201477f5410f210aefe61d0c210c77d75084400077954c8220007f643484210477d5410530005fd70d0530004fe76cc930004fe768c540004bf7458910006fe6350e210066d54588301477d75d0f210067d6558331107de4310d31005fe73106300047d76d5331006ff43580210077d54cc931004fe76d0520006ff4358a510077d540ca40116fd7610e20027f43110c21007ef62085300cfbd7408640006fd43d891013ffb4088540077dd30c8430005fd748c8310047f7459430005ff724c740007be4388440006fe54d812107fde4310d32006fc4398b10005fd7118b30006ff6310920047bf72191300077f6510d10007f9404c120005fc7650120007df43cc83203dfc7388530006fd640c8300067d54d8532006fd6488430006fd4358831005fd71cc940005fe7218d4013ff57110e21075fe7090f21006fe43d89101377d5448440004fc7650d210067d6510c10004fc735884003fef210853008efe3058b10004fe76d0b3013f7f54d0e21005757118154085fc7458332146fe64c8730007f731c8640006fc63d0d21004ff7654f42006fe7158043004fd760ca40007dc7348430006fe7218d40065fe710cb40005fe729864307f7d7519132006be71d9130006be64cc430007de43d853006efe760843011fde4310e31007de43cca3208dfe70d0d21007f443c871008dff7048640006fe7198f20004fd7610420007be711913004efc4198e10005fe7390720006fd7218d54006ff4398b3114dfc740ca30006bd6410c2106ff43008510007bc43486400577e75d0b30057dd73d0b300076d548c8320077d540c920087fb40cca40007be4350c2113efc43d8941
  | 22 => 0xc21004fc735932108fdd3048430006fd74d8121005ff7650c321277e6508740004fc764c520005fd76d0c3202efc6448110006fd7358342006fd640ca200d6fd7610e100057d7218154006ff6418530007dc430c6300067d654cb31057dd7310b30005fc73c8630007f72148430005fe73d0910006746518532005fd710cb30006fc63c81200a6fe6190f200077554c8510005fd7010930005fe721913003efc315833110efe76cc7400077d5490b3205dfc7688540005fe72d06300067d5458032006fe624c310047f97010930007bf429093006ff661086400577d5410b30005f970087300067d5458d10007de4318530004fc7358a50007dd6310f2003fed21085300067d7518d42037bc6410d10006fd725833104f7d750873000e7c6510d10006fe7118d40006fc7258031006fd6308640005ed721072018f7c42d8d54005fe73d0a10004fe7398d20066fe7608740067dd730874005efc63503100077d54481100377d5410d100063f6455130006fd64cca50006bf64cc5300077d5448730006fd64cca32135fe7390d210077d65d0f310057d7499720007f7214c31014dfc74cc630005fe7390b1004dfe7110f300047c76551210077f7155120006dd6310f20006fe7158032006ec7358840086fe64593320057d7510c32005bd7408530005fd72986430fdfe74cc8200057d758c720006bc640c930005ee7210f32004fe7690d21007fb414c030035fc744c910005ff704cb41004fe73d8540006ff6218943006f576cc631007db314c03006dfd7608630006bc6488530004fd7098d10005fe760c540007ec62085400077d54cc630005de73d0930006bc64949300067d654cb201777f431895413fbf4388740007df6310d100077d540c930006fd644cb31005fe7208530006fe76cc540005fc7650d200077f5448640005dd7308740005ff7250530006fc6218543136fc43586420067d54d8940087dd4310f320047c7655132137df4350d21004fc764c941007ee7290e210077d548ca41007dd32cc540006fc7358041004fd76d0f100079d4310f31067ef21087400077d548c540005de73087400f77e650c7400077f7255130006fc43d81210077f7548440035fe74d8d10007f443cc7210ef7d548c84105dfe71d8940006dd63c8440045fc744853005ff9700c540004fe7690d3200f7c5110e52007dc634c110006fe63d0620017fb400c94006ffa40084400e5fe74c8310027bd6410c21007f72188730006fd64487300077d5418121007f9404c11003fde7308530005fd7110e30006f721d8121005fe73085300077c71550320073d6455332004fd7018d21007f7430c721007bf6450d21057de73d0b30005fe7348740006ff6350910006fe7258043005f9700874005efd760c5400077954c8120005ef7650b20005f5710ca41155f
  | 23 => 0x47d76d5032006fd640c7200077f7155130007bf4318540006ff3258331147df4390f21007dd43ccb3103fbd74085300df7d7510f2004ff97008730006ff62d0130004fd7098843006ff43588310067d5458830007dc43cca3006ff71008430007f76108530007f721cc1100067f5498f200077f5490f31005fe720c54011eff42d8d410067d5418930006ff764853005dff76503100277f5110e51006fe63c8310004fc7650530006fe631081006ff561084400077d5450c31007f721d0310006df7258c4006dfe7188430006ff648c920017f9400c840135fc7610d2103efe760c530026fe6110e20006ec62509310067d5498a43004fc73586400067d5498e42055fe74ccb3000e7e6510c10006ff425803209efe6150f2002efd7610d20006fe63d0110006ff6488730126fc6408730006f5610c430005fd7119130046fd76d0930095fd708843011efd7610e31004ef764c83205dfe7118d40005fe73d093008fde6348440005fc7648540006fd4358b31005757508510006dc63d0d10006f443d85320077d5490a310077d5488530006bf64d09300067c65191210477d5410d30005fd7190930007f731c8530006ff4358321006fc631894013f7d5488740006dd6348440004ff7655320004fc7358642007f42150110004fe760c530004fd760ca41006fe7218d54006f46308510005fe7210c3003f7d751053008dff7648430036fc43586400057d7510d2000779544c030005fd7090f31004fe73d895413ff940884400177d540cb4008fbf4048640004fd7610c10146fe64c844004dfc715033006dfd70086300aefe61d0e52005be7408430006fd7098f10005ff7250330005fd74983310067d54d8132004ff7648430005ff7048530026fc6110d200077d7018d54006fe4358b31006f654d8532005bc744c1200077d544c1200df7e6455320095fd7688430004fe73988200067f765533004ff46108730005fd729073009ffa6050c210077d544c9400067f5418d200047d74d953204fbd4110730005fe7319110006fe7358042096fe6088430005fe72cc6300067d5498e20006fe4358632065fc73887400077f7548730007fb30c81200aff671d0c2106eff64084300077f54c853014fbf4210a301377d75d0d210077f54886301377f5410d21006fe4358a31006bd6410f20005fe721853008dfe7090d21006fd7098f410067f54583310c5fe710c840005fc7348630006ff7458331004fd76cc6200047e76d5110067de7308740007bd6410f20005fe7608530006fc624c110077f440c8510006fe76cc9300c7f97008440005fd7019121006fd63c8440136fe6448730005fd71d9130004bf7650c43007df320ca30037f57110d100057f76553310067d5498830006ff73d81210077f654c110067f43108740004fe73189400a7fa609
  | 24 => 0x73258430005ff7050f21045fe74c853006dff7008640005f7714c310005fd7210430006f464185320063d64552320057d7510d30006fd6498f20135fe74d8d210c7f43108440005fd7010b10005fd71189430067f65d0d10006ff4258232004ff7058643006fe73d812106fbe4008540005fd74d81210077d544c110006fd43d8520004f7764c431007f94348110004fd76108310b5fc7488430006fd640cb100b6fd7610430005f970cc830005fe7290f30005fe768c5400067d54d8931055fe74887300ef7d5410e32004fd7098c420077c7255120005fd7010d21005fc76c854003efc614c120006fc43583320067d6599320127ed72d0c21006df630c5400477f5410930006fc63d812106ff561084301477e75d0f210bfbf4110630007f431c86300077d75cc630046fc644c320056fe7610b300067c65d81210c7dd7308440005f97010f30006fc71580420f6fc640c5300077f544853004dfc74087300077d5450c210077d540cb10006fc64d8d20007f731c8740006ec62d0910067bd740874003efc644c310136fe76d0d210057e72d8d54005fd7319121095fe70d0e21055fc74c8730006ed76cca32146fe7610f21006fe43d8520004fe7398a40006dc7258c4012efd76d0830004fd7098f21007dd4308730026fc6110d520a7df3190e31005f57190f10005fe7348440004be76d0d400b7be740843004dfe710cb3008efe4058b101777c431895405ffb1050110007fa4348110006ff73583410effb408c94009f7e6550c21007bd43c85400d6ff43d8540006fd32d8141046fe76d05300b5fe71cc830066fe31d81410077c71551300057f754c3200c5fc7388440006ff7650f21004fc735834210f7d65cc7400077d5490c210077f5408430005fe730874009fef2150e21006fe545833200e7f5318d540057f7655320176ff4318954006f76418532046fe7610930056fe64cc320005ff70487400077c65c8530006fc62d011009fdf3150c310c7ef210844006f7e6508430004fd76d0820006bd6410c31006ff7358021055fe74cc730026fc6110d320ddfc744c3200077d548c920006fe63d0e21004fe7690932006fe62d031003efc4158e10005fe73d0a320877e6455332006dc630c540006775458430005ff744cb31005fd70cc8320067d5498d2105ffa700c540046fc644c110007fb424c030004fd7610b1004dfe7190f300077d54509310a77e6590c21065fe718cb40006ff43d8910005ff70553320047f7655320005bc744c110045fe72909300ef7d75992320077f65c8530004fd7018954007bf4358643005de73084400067f5498f10006ff6318940007ed7290c210a7ef2190e21047de7310930005fc724c54008efe40589101477f54c8740005fd7288530007bf43d8940006fc72580430cdfc7308640004fd7098b41
  | 25 => 0x8d410e7f57110f100067f6519121007bc6408530066fc61d0120005de7310530005ff7454f3213fdf4390e210077d5418d100077c7255130005fe7310a31005ef72503200077d54cc620006f4421853200e7e6510e310067f6519130075fd70c863004fdd7308730006fe6258a43006fc6418d100057d750c92006dfd7608430005fd7218d40004fc7358b4003efe7610530126fc43189410079c7150c43005fd70d0730004fe7690930006ff64189300077f6455121026fc6210f10076fc4098b100ddfe7498f200067d5498d10006bd64c8430004ff705843211f7d7510e31007be740c940095ff7088430006fd7258043004fc73584400a7f62190c210067f65cc930006fc4398a310577d5410730076fc30989100077d5490e31004fd76084300073f75d9130004bd74d8f200077c7355320005fe73d8121155fe74cc950006f442986200077d54cc6401377f54487400067d65ccb41004ff7058841007ee6350b20077f440c8710007fb40cc320007f7214854014dfe74086300077d54c8430004fc7358b1010dfe74ccb310e77d5410f100057f754cb200057d7518d20086fc64cc9300afdf31d0c31006fd755803212dfe740c830077df30c84300057d7510e32005fd70cc9100073f64551200177d540c8400b5fe71d08300077c75484301077d7510d31006dc63cc9400067d54d8941006f47458430007f821cc130006fe63d0120006fd54d81210adfd76d0c31075fe7208440006fd7218d400fefd7610c20006fd64cc630004ff764c832007ed644cb20006fc4358b10006ff764874003ff46108530006fc4358620005fd7010f210067c6318954004fd7690f1013f7d54884400067d65d0830077bd64c8430004fd76d0c31006fc7458031006fd4358732006fd7690e21006fc6350120006ff7648630146ff4398a410057d7510b30006ff7258341007bf64d0d21004df764c8320defe64c831004fef2108730056fd7610b30007bf4390c21006fa735802114dfe740c630086ff4298e42006ff7558032005fe7318940005ee72d0520006ff7158332037bc64d0110005fc7350320016ff4318d42004fd76cca500877e65ccb400077d549093204dfe7119330006fe4358732006fd64ccb20007bc4388640005fe7308440006fc7458331126fc640853002fbc6410d20005de7308730006fd6348440005fd72d8530016fc640c920146fc4398821004fd760c8101277d7510c21007f74348421147bc43c84400c7de7308440007bd42d0730007bf6410d10005ee72cc52010efe6459331005fd70cc540136fe6448440006fb745802110fbe74cc7400067d5458f210057d70d8d540077c7155232016fe640c81006fde3008530007bd74cc540007f73108430004fd7610c30004ff765533204efe761073006ffa3008430006fc4358910006f
  | 26 => 0x10290048028000003814401a01300800240340e700080012d400000b98e071e01b000801000001a07a1d0800400302f801804e001001001400800300000a40041ca00b00100060470038000008016000003c0060030010014006097006000003a065007800004c3210020024b020040040010aa001f000009c0000ae25b80f800000201000041aa005000802c01400000000900040eb000000000c001019800000600106b80d007600000d000088c05f000000003800b03382c809c0870a0806004011d005800c012017003009001808909380000b8002001801003200300300040fa1d3003041c000007004000400602d019000001a00000100bc00a0181ac00140d80110218b6405400100f0a64032003001800000600000000d809c11000000b400200001680bc002078000007c020001000802c09002a0758060002040001800400204d14c807003400600580040060060030008012000006000808800b000802c02204300000a4024028015807400000300a001834c03c00c804400800a02880140620020048000a5800101083805a8009000012801630c0028000a0c25f00580000220010000010014013005806c00e006022859019c0160048000002000000001400000662480082b400e00b000001600100000dc00600f00000000000050260004000007002005c00603700080b8a5e00000005a84b600300500980a400101700300000000060198000000003802000c02703b006001005400605b400000101980a804a0030220150000011000800023000d001821002849d00b819004400006980f00ca06601200c80120000100004030013016800403000200810a80100000348338000002000800c000016067007008c05d002800804e12000b813c07802a0010010022008006000002a2c4007007000000212b8000006000000004c008007000005c0622ac000002404e00001a00a8026001018002827c03e003808c0863e6000800000800d013800418e007014000000800d089000001003000003b805a005002800004200920c000000013a0f3800000006201283200000610650004048144021803400003400f809c006000013002400200103a83d0124000000000401a49202c8038006001013000000a00c00002540be002000002800e04b0000020000015061800400401b002b3ac00a00901e80c400a0ad000019800e00000f00040000000a100e40000020000238032002181817401a00300902600080040f4002800a03a0000308018000006002801601b01c005830806e006000000402100382a016004900780001520000048000000017000004000001c000001c196001004861c000000071803800400b008800008800100000140082890b2802448000603783c803608801b80000000000067d6510c32004fe7398a10026fc411
  | 27 => 0x2b09f805c01a09d000003c1c800001e800000002f000807c00a01003d9618004005003004401e02502b810c00600403c80688da06e00202ac00000f00080b000400104a80b40b28c4000801c002048003801c024002016801c00600200986f800800b004000801e00c025000027a005014800c0260c8000005404600100380f80320040d280602020030040018318050001007c00006a000800406a000268800009c01800f808400e04e000001005e007002007519200a00082d403e0220800054000000000804c01806c002001012c00401d01cc04c02100301b0018008015800400c00a00000002b406000b000000602c01100d0000010004000c01000100280000020001e3b21c06801501c00040060061ea9f1402c03a0000068014022000000000c08e0388000bf2004015029c00a00022f800400400400503000480200000a0000004a01500cc000002038805801e0d000516e400602b079801c0060020170180084004000000800a00a003361c1520000018130000e4400f0d280082393a380880a802b00400300160762cb000409a04e000000000605c030800000200601503480e200b01082c003a000000000014c0360000484086000016807801001303500102ba001003031400400d0000004068000002000875000054a802000000413800a0014015000008c0920050048e8000c09b00980b423a04605a81f800e000000093800a00000c004002400001507400b80030820004000025025009c01803900e005c04c020006802400c01300b000c000005000006c006009000008400001800303b80ae000003001c05e01901d80140060540040030018001001003800809705e000428402c0000068444001003004400a0004ad002c00c00b0438034008002000001808603c00300540041cb00c8000000000009001c0f400100a802400600e003800000402a00180040160010008060000a4d01500000ce00000d802000001100e80340260080002adc0e800702100001c40010c2000000e00004600100109240768004018131008002800e0440088128022024000809007a001000001800e000045078009201d00184e8006031240815c0360010000094000000008800c00405b03d8020028030025008d3b4008010003c03e01b0008184086001013804c018007002800012002b01400d40120001010038122017001800400204500902a80407c3007013410c004002800411200000003b403e0820068004002000005804402e0ad008801000205201c003003e03e07e81fc00a050001009c01e01b022800450e1fc00880a406005100a000001c004003010800e00b000003c0b60000018d2801003100f000c00000b00000058c4000035066402e0000110520000028000014c0020032ce800801201e01b8294000054027802400200
  | 28 => 0x7401e00a00581e41d001200000840940330018050006026019800463a00710500040d60170068004076004001812800a04c04e002100e00400203400aa0000f30078054099000087c006057000004800013c01380100180040d90078036006000000c00a04800b0000028000048a33000006601080740f070900b800c11000e027001001004f003008400a00900181bc05203f00a8000004000000000800000007b013833e02102e80180540000070ca431402100c03380020a5001008400002d012800800601a003809c020029000811000e0080000050062016116002003c00100184e400c006000000c02c2360029a9405a061000000001400400000404de0ba00300f002c0820060000000019005801401e017045801800400000d001000615000600200002d20020ba400401400b802009e0000000000002034002001408800703380a408e000002001000e00e057003c000020000008002e0040338584028006010800000000000483581220011a4800000a000008979c0000e5004800001e07d0ce815000200000687b806600002d808800809b00000dc00000d0028014002006036802c05a006000937800c00300f800002803c01480994b600000e001c060026000000055a01800001c000000f025000000001600280
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xcbe845d8410c0018fce8328c688003371cf63885400053fc32a99864000cee7458b310c001b9cc539842200533d0c57690c210053fc32a99964025cbf425d8420c0014fb0a21ac4880035b550724c12000536c10c6312a800cbd649cb410c0438faa8bb662200031f10176d50210073a322a9b0a6400c7f76551218c0018fce9b2ec6908033799273085300047ec04ed99282008fe869d9434840137d0d3a04298003379cd6310b100174e3248619260009f78748421d00019f6803b264a00023f21971109300063fc00ecaa2640087c8755162cc001974c8b80421803ba7d0163c84400fe7dc32e021c4000cbc76191414c00157b03b92c8180032f19372545300063eb2ae3990800daf88050c62440010fb0faa4c7880032f1007648540056cf3a28610e6006d3c74551304403d8faa8bb686188035d550714c8320071fb26a810a6000c7f401d9544c8013ed07b8242108032f9d942109300063fb2ae7b024200cbe71d90324c0018fcecaa664880032f184744c120006afaa4e610a6019cde609cc211000b8faa93b682900438f99154cc8200074fb20c621a20178fe869cc214c0018f8ec39aa8900031fe157098d2000736aa0c499282009f98710e204400157b033b0c898003b5e0563c84400057cc30869004000cf6745c46344001cb8eab1a422004ab761a4388730006dc21ae010c8000cde76cc832500015bd09384c6108038fdd464485301465e324e520a6000eae21991210c01137d09396c2980032f1d3624c110007caa188798e4200e3c71194644c04b97884bb684180032f5917210c300063fc2aed21062008ff805da420c4018ff0b3b086908032f19272185300056e41ac8b1e4000c7d855d832100011fb0039ac4208031fe1776484400047fc3ac81906000cbf845c06348401cf50a39ac010803e550c43c85100061eb28e89864029cde869cf414c0019f70cb80641801f79085720c5300047fc32e22186008cbf429db414c001d750839ac0108171f55170988430465e422e13188400d9c7390d21900018fce9b2864980023f61f64cc5200465e424eda126000e3d85193624c03f978e8392c0218027720d70d05300061eba8c81926000cfb731cd6008401cf6a839ac0108932fa117608440004bfc3aa819260008fe8710d6008401cdecbb1442980036ee1170087400047ec3e86312a200cde7358e21100019bd0e31a86908027de1d21086400056f426e13184200a9d841c263084499bc86bb686108033eddb424c03000577410c9b126000e3f64d51214c0019b8e6a1ac4880032fd9172cc5300074ea1ce4b008624cbd87190214c00157b0e320429807b8fd095418d410069eb2ce81086000e6d5418b3244065f2842a1887880032f5d074583310064e3a4c69864000c7c8759532d0001cef0bb26c29909fa71914388530
  | 1 => 0xaeb31842200236760e74085300063f3b2a998a4000cbc73190214c001cbaca21a64190023fe1d64cca10024fbc32e221e2000b798510d20440019dce83166488003e650c43c81200071eb22a8b066400af98710d60084019d8423b242980029f61743d89100063fa06ecaa66200ddb835c0214c0019f6ec21260180023f61e63907200057ac366390c8000cbf649cc214c0018faeab0e819009be39c94310d210047f43887b024200c7554dc562cc0019bb01bb264190174f1d1544c1200072eaa4c69864000cee72d8b614c001d6ac990a42180038fd91544c5200047f43ec6a12200ddd8305c0214c0018fcecaa06298037ae9c264084300063ebaec62124000a7d86d514308401d5ec831042980038fd9154cc5200065e326e2a92602fcbc64dc9544c0011ff00bb08518803a79cc64085300066f384c721842009bd87190214c001d6ec998842980031f5d965d0c320076a18cc6108800087d87d506348043c78c8aa662980025fe1d54cc6400057c43e86b004200cbc7650d215001ddae2131e42200231fd517098c410066ec1aec1088000db9845c021900011fb0c39e42200938f6146408530006baaa6e29968000cdf739cd60d08018f8e932ac0190038f1d564484300053ec30e6aa64000ed97390d6008401c7ec8aa6c2980972f1d164c84300063fa10ecaa2600acbc7459121cc0014fb0b3a6c090803751ce43484210066fb20e690c601de3f435526290c01cbacb31e87900025f21d544cb200063e40eecaa64000db7740853044039a7b0a3a261880372f5c264084300074fba2c69088000cbf649cf214c0015f3012a2c01909a3f61f6418d210053ec2ce8b006400eb464187214c001da8c790a60880025de1d54cc7210956e4328710a6000cde8718d325001ddae20b1e4220002b761f6310d100056e41ae8b06641b8fc8759132c800157d053b0c8980023fe197010c210a75b3a48630a6400e3f6455232480019b8ed21a4298003b558f21484400063f3b2ea1928000adf8758c43c80014ff0caa4c7900a63fa1c63501200065fc24ec10a8021e6d5458b31100011fb0d39c43200174f19175d01200072eb2e879906400afa8610d204400137f08b80c6908cae7a077250c4300775c12e6b0042008df8798c21100018fced3ae63a000277a0c72545300056ec10e2b188000cbd845d8219000197ce332664180771fdd954508320046fc3ac61088000cde835d843084011ff0eb2062180eb8f99370552320063e3b2a89922000e9e6458c43c8041978c8b8c86980226fa1273485300666f324e61088002c7d545db420c801a7ceb3a662a006f4f9d15498f200066f39ac69088008cbe869d0214c001978e9312608809b8fd0d54586421371ec28c890a6000d6c425c863550011f90ea1ac5880033b88476485400063fc3aa9b126025
  | 2 => 0x673d05300065eba0c83024200abb845cd6008401c78ca32042980373ed9170084300063e210ecaa26000c7c87553604c40137d0f21a4320002e7e194310f200066fc3ac71088000c7d655c432d0051d3886b1e422001e3f6027318910006ddb22e010a6000e3d85190624c001baa86b8864188034fdd464485300074ea1886b162000e5c6518d4348401b7621ba2608800367d0e73087400053fc32a8996620acbd869d021cc0011fd0e21ac40809aaf61f64d0d211271f322a81086000c7d765523290401abccb3984220002a72117098c21006bcaa2e018a8000c7f42dd9540c8015bd0438ac62000277a0f70485300063ebb6a810c8000c7e76d96214c001c7ec8aa064980031f9db6510d100056f418c9b1a2000c7c765512150001b38c939842980032f19273885300075ac0ec830a6000e3f645536348001af0cab8042980031f19276551320055ec3ec810a6014cdd835da430840153d08384c6108533d98673d06200066e21eeca1842088fd869cf418c0451fd0e3128098002b760c74580210055ec34869088007ed91098d30c402597ce2b2042180023fe1d63084400043fc3aa93104000df0815c043440019bce6b1c8588003976147258c400063e410ecaa26000cbc645ca514c00197ec8b9062980039bd9462885300ce7cc02ec10c8000a7c86553314c065d3cc2a18861902b2f9d164087300865ec38c99926024abf8759043084013bf0e99064a001f3dc427608530056cf41ce810e6000bb9809cb644c0011f90ea1ac4880039e60062d81540365f3a6c9992200ad5f549cc42cc00197ec8b8ec4980031f5d954cca1006ef8b0ae01086005e3c435516290037b5b043a261900373b609760843000677426ec9906406abd87d90434405997cc9ba2a7990033ee1970cc4300b67a18aec1086006db6811d130440019d8c7396829000397d517098c210075dba086b0042008fc8750f60484099f220bb08608003a759073484300063fbb6ea9088000c7d655cb311004dc7cc8aa24218003975956310f200057a4328790a200eeb710593210c0014fb0a21ec49800397d526390c21004fbc3a421086021eb581193314c001c78ca32242980025f61f54087300071fc2ec998a602ee3e641c954cc8015eb02320c2980031f1db64551210063e3b6a890a6000e7954d0d60084012f90eaa260880031f59571cc83014e9ec2ce810c60038fe87d85404c001da902b1842200023f61a72cc4400056ec08e4b188025cbf425db410c0011fb0e21cc5988032fd92720c530036dac08e89822029cbe869d0218c001979093b04298003371cd435872000676c26ec9906400aed8210c624c001c78cbb2442980029f61674583310057cc0087b0a40118fd871936048401878ec322a8980032e591700c430004bfc3aa810a8000af9831d16008401cb
  | 3 => 0x610c60008ff87553604845397ce9b1842a009f2f9c464085300063fbb0ea908800bcf7109d821500113bb0f21e649800397d506310d10006f4312e010a80008ff805da4308401da8c6a1e4290802fce0143c85100063fc2ae13188200e9f6418d434843d9f280bb0622000b8f991540cb100065ebb4861088008cbc429db424c0011fb0e21cc41802e7da04760c940004fac08ec1928000d7954dc132d004fc7b0b3244218002b7a0e624c11000676b90c430a60008fd869cf428401bb72c8b804218003ad0c564084300063ec2aec1908200e795450d60084011ff0cb906320057b90874358b100065e324e690a6000d9f649cf414c00197cc939662180031f59572cc430006bcaa2e010e6000e7765d84214c0011fb0fa1ec09080367e127308440006773a2e431a4007af8865013044001adf0bbb265900234f19175d05300065f308e8986400097c8755130480531fd0e31a80880026fe1d42109300055fc22e6b004200d7b545c02190001c7eca3244298003971946310d1000676426ec99064008fc8750d60884339e8e3b2264880036d1d3214c3100465f322e12186200bf1800c7219006573d02392862180b1f55176d0c320053fc32a8b006400c7f811d9544c051d5b0432642980023fe1d6310420006cfb24e7a1260008ff865c831100319ec42bb0422005b3ee1970106300063f3b6cba1a2000e6d5458a420c40153f08b84c6108373e1917008630006afb2ce6212600dcfb635c0214c0015eb02192c1208223f61f64185300065e324e528a6008d5f549cc414c03df2ac238a86218029f6177258331006cf3b28621a4200ebb745d160084498faa8bb6861085b3760d760843014c7fc3ac99946000e3f659c8644c0015bd013a4c6108439755163cc8400dd7dc02e4b008600cde801cd62440011fd0e212c0188031f10c76551320063f3b2a998a8000e755410f614c8018f90eaa2c690002fc60031c84300072faa0e13184200d7b655c0414c00197ceda148498022be60273580420047ec34e62162000d7b545c0210c0011ff0cb8064188232f2127610530006cfa04e61088000e79549cd6008401daec618e42a0002fc60331087300053e432a9b1a2000cde309cc62440014fb0a3a6c0908038f61564884300065fba2c29864000d5f751cd218c00197f05bb286218022fe1d64084300465f3a2c810a6000e79859d160084018fb0abb463900032fd9171d0930004ef418e4aa260158fe8798d4308401d3a8621ac3990038f1d464485300063ec2aeda184200c7f875536348001d6ec990c429809f8f99354884300047f43e64b066200c7d54dc1628c4018faa8b84c69000b67dd87250c430063dbb2a89004000c7d755c463500018fcedb2e8298003975d563084400065fc3ac99086000cf77610d2108401ceb0a21ec2990035719
  | 4 => 0x1c800179d0732265900027761a73086300063fc2ae131e8402b9d861c94310c43d6d0232662980033d61c63c85100047f43ec890a6000af684cc9610c0011f90cb8664a08032f20f76508420069fba2a8b066200cbf749d160cc4018fcedb2e84980033ed02768c540004bfc3aa810a6000c7c855c263d0801bb706b80849809b2f9d364d8d210053fc32a91086000cbe71d90434c0018fe80bb6a99880337e1d63c84401366f21cec21a4200c7f615c063550019beed21a6419002be6024258031197ccb02862184200c7c8755161cc01d97ae132642180a72f9d1640c630035cfc3a8621a2000ecf2198c2110001bb281398422005b3bc8576084300071fb96ca3226000eb970d90214c001da862b1842200028f610651911000577410e8b00620097f8755032480018feedbaa4398003a7e194310c2104e5f31ce810860008fe861d832500018feec382a8190031f61476509310063e3b2a8a1a42008ff865c4320c0319e842bb06220002d761443cc93100676b90c430a8600cbf649cc414c0011fb0d39e8310002afa0b71590300073daa2e6b00420ee9d30593210c0259bee131c4220002bd61b43c87100047f43c86b12200097d84dd560cc83b1ff0cba46418802fc60043c85100047ec3c86b0042008bd869d0210c011978e8b1a4320052bd20562586430067710ceda1a4200a7e86553614c001b7108b8062a0003a750c4358b310055e422e13184200abc845cd60084014fd0d3b2a8990023fa187350120006b6aa4e598a40008fd869cc21100019bf09bb26419002bea1a41cc130006ae32ce7a126026f1c43d5143484019f7013b042a00026f61e430864012e5f3a0c610a8000a7c8655130440014fb0a21ac1990025f21975d09300063e3b6e2aa26400d7b545c021d00018faecbae632002b2f9d364087300073daa6e6b004200af88750d600844fcbaa931c42200032f60a76d0d400066eb98e6b068200cdd8718f43440299ee20bb48610853751c6434cb310063e30ae6302a8008ff805d8329040197cedb2242980033dddb2148440004fcc00e4a0a6000dd4631c532500199ed0c38a65a00038f1936510d100065e3b0c890a6000d9e7350c21d000197ec8b8864980027720d708853006e5ea02ec10c8000e7483553614c801b3e613a043180023f61e4398910197c690a862184200cbe819db4350001cbecbb1a86908023f21d614c3200ce7a10aec18c8000cde8798d30c80155f700b9ac02106f2fa18744c3200047f43e86b0e4000cee825d821100019bce6b1843a0002bea18438811004f6a10cc79862000e3d75590210c021d5d043266498003375d07498c210047ec30e69088000c7c80dd954cc4019bd06bb486108031f5d57098f100076a3186390a8000a7c86550634404fd38c8a1c439800277a1a7310530004eec04e
  | 5 => 0x80031f9db54085400076790ac61088000c7c761cd544c821c78c8aa66498002be60042d81320047ec30e6a064000c7c74595600c8018fecab86c6908025f21d54486400074eb9ac8108600dcf5815d821100018f8edb2e8298016e7e1d4310d200757d40087b0a4024cbc641c9414c043e7680aa663200027da1c2150110004bec38cba126000f954310c21440018feec3aa42180031fdd954486400063f3b6ca20a6000c7c76551325041df608190a80880033b5c872580430065fb20e690a6013ee42150d62c4011a7ce8aa06298047a7d0163484400071e390ca322600eed51098f21100017750810e61180031fe167610d320066f3b28610e6000af581109608c413dc842b1661880bf8f193725513006f6b884c61088000c7f855c2630842f9f70cb80621809b1fd527610d210063ebaae431aa800c7f7655142cc4013f10ea1a40880021fa1f54583320047ec04e73168200e3c64197414c001d68c990a42980023f600764c9410076d21886b004212cdf7058e211000f1fb0d3984318002dd60470553320053ec20eab066400c5d541cd6244001aeaa838a65a00031f5d9540ca410063fb2ee090a6025cbe641cd40c8001978eda1282980472fdc2644843006e7b882ec1086000d9d309d0210c001cf6e9aa2c0108039b55062509310057cc04e8b066400cbc649cb614c0016f30038aa898002db616644cb200047f438c4982200097c87551210c001c7ceb32042180036710e73084401278e21ea8a184208d9c649cc414c00197ae9324c199002b761e63d0c2105e7ac30e2992800097c865d4214c0111fb0fb20c498003ad0c464085300257ac388730860008ff8758c42c4001978c8b88c4980023f21d32d814100736aa4c5a166200af980d09608c8019bc6039ac39009b1f55276d0d211974f18ac821e621bd3e7455332c80011ff0eb1c85880032f9c571d91300063fbb6e4aa66000c7f759d1600c40137b0fb204298002bb60843580320e6baaa2e221e2000cbf649c8214c0218feecaa28619002bda0843984300063fc10ecaa26028e5f5498f21100011fd0c39a84880033d5d921084300066eb98c7b024221d3c7455160cc4018fcecba86498017a79d94310d20004fbc02e22146200c7d545c06348401c7ac8aa062100023f61e63107200053ac0eecaa264008fe8710d61080011ff0cb8064208376ed91700854010dcec36e2a188600e7785d90614c8015bf0eb1886108023fe1d640c4200063fbb6ea908600097d87d50218c0011fd0e21ac588003375d17098c21006bcaa2e01088000cbc645c8614c0179ed0c38a64a00031fd9570c853014c7f43cc6a064000cdd8798f43c8001c7ee8aa2c0190023fa1e435822102d5ec3ec821a40008fe869cc2150001abaa939843a00032fe137650c210071fb2ec990a6000cde7358c4
  | 6 => 0x76ab1e639088000d3d74553328c8018fec2b86c4aa0031fddb75486300063eaa6e0b106211cec82dd9211001b5f100a1ac0108031f58973189540075790ac81086000af983dd16008401cdaa8b1641880023f21d54580320065e3a6c29824000dd8835c021cc001b3a86b80871081f7c18570085300065eb22e22186000c7d545c263884011fd0d39e429804b2fdc164884300063f42aec1088000b5e831c9544c0018fae7b10c4aa03bb544163c8440004eec3c8610a6000c7d545c263084018fd0abb08790003b518c214c1100957c40286b044226cde439db43484014ff0caa48518802b76127098c211ae5ec38c928a6000c7c76d9743484011fb0f212c118803379c06390d210073d42ce8b004208e3f41551639000b8faa93b68690072bee0171580430063fc2ceda0a6000cbf749d360484018fcecba865a0002b7a077298c401974e432862184207cdc835c263084019be87398c4a0837b5c416308440085cec36e4a188600a7d841d5600c401d3ac9b9a42180031f59571d0830004ef434e62126000a7f86552430840193ae83a4c6108035718d73189540055f4368630a8000c74635c4605500197b0fb266298002ae21173580210063e3a2ca9966200d5c751cd218c0011fd0e31a8488002dda0470550320073daa086b004200cf883dd92008001d3a8621cc41882aaf21162cc1100047f434e7a0a4000cef76991320c8018facab886420003b558d21084400047f436e2a0260008fe8710d620c401aeaa838a65900031f1d97055132004dfc3a8610e8000e3d75190214c0018fe803b2a8908031fe0376550320056fc3ac79908000e3d64552210c0015790ca168298002af60473590300063f3a6ca31a200de9f4058c21100011fd0c39e42a00027e60073c85400871e21aa9b128600ed78158c211004b97ce8b266418003ba20973580210076d398e6b004200e9d43dc56010c099e862bb086108033761c638c5400057dc02e8b006400cbc76d90214c00f1fb0fb26c29800337dc87258c400072ebaac61908002f8e621c94310c018f90eaa2c6908029fe1954cc6200054fc328621842088fd809db414c0018fb0b3b464a00032fdd274580320063ac08ecaa22000c7c859d8214c01197ce8b184320002bda1032984300072faa0c721a4200c7e7459663c8001dacc798e42200032f1d864509300047ec3cc62162000e9d4310d620c40157f08b84c6108031f5d954cca400047fc32e42186027f1f4355243884014e90caa642908031f196731911013f2eaa2c71088000d5d549cc2190051cbea8b1e4220003b598d21084400455ec3ec9a126000f954310f31084014eb0a326c2990033dddb21484300065fb22e5a0a6000c7f549cf604840197cecb90c8980031f5d763d09100071eb22a91962000c7f851d9214c001dc8c2310429
  | 7 => 0xfe86dc9404c0015eb00210c2990023fa1f42d81310063e32ce63224200c7f87553604840197d053b686a0053b908643588311274ebb2862184200e755410c614c81dd6a20b26421801a3f61f64d8d100465f3a6c9b126000cde7358e41c800197ce3b20c498002bd21943085100066ebb487190620b9dd87ccb3150001aeaa839262188027760073484300047fc3aa8b006400cbc845c26390401d5b04326c4980034f5d464085300063eb2ae21906000cfb76885300c001c7eeb32242180a3a719243c85300065fb22e22126004cdd835d84308401c7ee2328c8980032f9c56410830006baaa6e29862006f997050c43440014ff0caa06518803379cf4318951006bcaa2e010c6008d79545c0414c001c78c832e84980023fe1d63087400063f302e431aa800c7c759d1600c4018fccab84c998802be600325803106f5b882c81086000cbc87593210c001aeaa8b8663908039e5d354580210063f3a2ca1944000d75541c931c4001d3a8621ac39000357dd77348630004fbc3a4210a8000a7d861d521100014fb0fb2e8690802af61a43084400774ea02c79088000dba749c03250001b7708b8042a00034f19674085301265f422ec2184200cdc7358d21d00118fea8b84c6210031f9db54085300074ec10c6a1a8000f954310f21884018f8ec32886908025f21d544c9400075790ec910a6000e5f5498f43084011ff0eb18840809fe59c54310e210071fc2ec99926000af586cc42190001b6ac33a042180031f21d5458f200066c31ae018a8000cbd74992600c80f3f10cb8082980035d597714cb400065fb22e110a6000a7c86553324c0018fecab80c6908039d61443185320047f43c86b004200eb564484210c051d3aeca188790857b90874358831005dd420429806021e3d85193314c0018f8edb92a8980031f9db54cc9400463eaa4eda0a601dcbe645d2320c411978edb2082980cbe6c414310d100063ebaac5a022000cbf7418930440015dd0221cc4180473b20b764843003d7b40e64b0662008bc865d0214c0011fd0fa1ac1108779b551628c8410267b30ae221c6000eb6640c7210c00f1fb0d398831801b6e1917010d10004bfc3aa81944000c7f421d954440018fe87bb2a81909f8fa1664884300ee3f3b2a921a6400af9800c960104019bced21842980029e21954cc1300066e3b66498a8000e3d64552320c401c7ac9aa64218037374c176086300ce5f422ec10c8000cbf749d1600c401adeecaa26590003375cc73d812110e3eaa2eda166222cbc74dc96010c019bce131e8610803a75cc64085300073ac02a9b0a6400a9c8650c434400d76d0831c828801b4f614744c1100063e21aedaa66200d6e7655232480011fd0d39e42a005e3fe197010f310066eb24e61086000eb461190214c00157f04b8ec898002bc60043586200
  | 8 => 0xdaa6429805b7c085700c4300053e432a831a4200ed48198f2110001d68c890842980232f2117098c410063fc2ae13188400c7f85dd932d04014ff0caa286190031fe1d54d8d100063fa02edaa0640ad3e7455021cc0019bcc6b8e642000376a0d70084300074fc328621a42008fe861cd544801d7e50021e42880029f61f5418d420047fc3aa8b0664059f9809cb635000197ec9390869806f8f99154c83100076a18ec610a8000c7c76dd5215000bf32e0a18869006fe35c94310f200065eba0e8b00640097f805cb63550015bd02394c620003a750c435843200736baac41908007af681d8b614c00f5ed03b26c298003379c5630c8400072ec28c69928000abc825c7644c0019df05bb242180a38f19354c85300057ac0c86b006200ed463d0f214400797ce8b20640805b3d1c46350910046aeaa4e6212600097f8755331500018fee3b2e8498003751cd43484210066f39ac7a142000cec219da43484011ff0eb2065880023f21d32583410063f3b2a819280008fe861cf214c00197c833b682980029f61464d89300065fba2c49822000e5d5498f43c80018ff0b3b082980031b5507258d1003cfcc04e7b222000c7d75d8b404c00157f0ca188610802b7e017498c211274e21ac610880008fe87d0960cc401d5e4232042980031fe157098f210075ab26639086000d5f549cc21100111fb0fb20649806337cc5760c4400063e42ceda1a42008fd869cd21900016f30ba0240880031f9d954cc5300066f39ec62124000c7c859db414c0011ff0eb204318002be60343580210071eba8c81926000cfb645c0214c0018f883bb2a990003371d943485300e74ebb28621e200ecbf70993210c0018fb0bb82c5a18038f21764c85300057dc02e8b06621de3e64552320c4019bce6b1e84100032f9db64c85300069eba2a99926200af581188615000197ae83a2c1990027720d70085300063e42cec21a42009f68708530440019bee739ac02100b3e501760c8400457cc04e6b068200dba845c0219000197ec43a26188003a79ce640843019f1f326e2aa66427e3e85192214c0018ff0b3b084990231fd5276109300066f31ee0a184200e5f65d8c434404fc78c8aa442980174f614744c1201474ec18c990a6025d3e74d50210c0018feebb12608805737a0d76d0c210066e31ae018a8000c7d765d432900038f90cba8869905e3fa1c4358630006cf424e610e8018de4215c8311002f97cc13a04218003a7d936350d210053ec2e87b0a4000e9c64cc8324c0018fb0abb686190023f21d64486300063ebb2a91906200d9c7350d21d00019bce0b84c610837374c17608430006ea39e4290c6000d7554dc53250001a7ce93a865a00cba72194310e210865f322e9996621bbae8498d42c80018f881bb2a81908f2f9d1640ca310067abb2e998c62008
  | 9 => 0x4310f210063fc10ecaa2201f8ff875933208001db5063a2c01089b97d5263484400076db9ce6b00421f8fe87d89404c001ce90caa6c299002b761b320c8400076a31e4398220008ff8754f604844b97d08bb084180025fa1f54486400be7cc02ec10c600187c875516390801b68e990a6088002bde057218d540053ec2887b024200af9801d3604840197908b80c6a08023fe197110a300065f38ac81906000cdd635c7321002f9bd0d39842980023f61a73107200057bc32421088008d7b545c0424c0014fb0932cc8190027e60073486400076cb9a86b004227cbc64dc9414c0010f90eb2a65a006b2f1d37158043006dd21ae010c8000cf776c85218c001cdd04318c4aa0031f5d57118d2006e7c202ec10c800087f8755363c80015f301324c1990931f55176084400072eaa2c621e4028e9c4350e62084019be87398c4aa002bd61b31c84400047ec06eca184200c7f655c8434c04b97ce8b266218096afe1d64d08300057cc0086b142000c7d85dc1628c401cbaeab1887900133bc857610c21006baaa2e19884200c7d76d50218c001cbaa9b1e64a00032f18b744c31013f5b408c910a6011e9d30591210c0018f8ec3aa439802f2f21276085400074ec16eca188610cdd439ce62d04018facab96821809bab60864485300047f43c64b008200cfb865c03290015a7d0b3a043980032fd9172d853013f5ac08c910a6000a7c86552214c0015f30021ac310002fce01430851000577410e6b008200e5f54dc263084012fd0faa242180377698d70084300066f38cc61908000e5f5498d43084018ff0b3b686908031f59570ccb410063ebb2a81902000cdc649cc214c0018feec3aa43180031fe157018d210465f3a6c830a6000e3c64194424c0018faedaa4861080357d5273087300463eaa4eda126000c7f411d9544c8018ff0b3b0429802779085720c730004efc04e610c6026e9c4358d211004d97d0e32242980027d61f430c72112d5fc3ac82086000ed43118c215001b3f70cb8042180021fa1a76551300063eb2ae22106000db4211d130c4001c7ec8aa642980029f61f65d09300057cc24e6b004200c7c87551610c80db70e8a0240880031f9db5490d210cef810ae018c8000c7f655cc64484438feecaa2861884fb908543588310863f3b2a92126400e3e6499443c8005c78c8aa0649003f2f993744c8320065ebb48610c80009df8750c214c0014fb0a21ac1908032f1d864c85300057d424e6b0042008ff865c43210001d5d05b26c4980038f193651053002fc73928621a401ee9c6490c314c001c7f0bb244298072afe1d6410f100863eaa2ed9908004cf47118d3250401af2a8b8463a00023fe1d640ca500063e3b2a89824000d9e73d0c2150005cbaa8392c6200026f61c43086400063e43aa8b0e4000a7c8655120440014fd
  | 10 => 0x10c6000cdc73d0d6088401d3e623206298003ad19331c853012f1fa12a831a8029cbd869d0218c001b3ce6a1842a00031fe0c76551210063f3a6cb99220009f9801cd41480019bb0d3984220002afa1864085300066f3b26598a8000aef8058a420c42f1ff0cb86659885abea0e73580210076cb84c61088000c7e76d9743484019bae639ac020802be21942cc1300053ec2ce7b024200e3f65d91214c0015df00b146420803ad99321484300065f3b0c810a6000e9d7498c21100018fb063b2a8880232f9917090f320047f438c690a800087f8755063c80012ff0eaa065208031f9d954cc9310076690ac61088000c7c87551600c801d38c9218c2980032fe1d64cc4300075bb26c390a600dcf5815d8210c0015eb0031e42908029f61742580320f66ea18e6b088400a7e8655132440019eee338ac0218035b551720c720056cec1ce810e60009f787484214c001c78eb32242180021fe1d5418f210063eb2ae11908224e5f5498c2110037d3aeca18879000376e0d70087300063ebb6a8108600187c87551639004b57f0eb2682180032f59171cc83002eb6aa4e5a0a4000cde73d0e62440018ff0abb062100033d990714c8320465e324ec2126000af6860c7214c02d9da42bb042180023f61f64085300072e41aa8b1e4027f1e7550c4388401adacbb926190002afa0873590300047ec38873122000e3f65d90214c00f5ed03a12c198802b76077298c40006773a4c59966226cbd87191214c001d5b04320c4980031f1957018d21006afb2ce610a6010f3b4055332900014fb003b2a8190031f2157098c210b67cc02ec1086000af58610d21084010fd0e3b2a8190029fe19540c8100065fba4e8b066400cf476c8521cc0013ef00b8865208c78f193735512014c7f434e7a0a6000d9d849cc21d00018f8863b2a8908573d08576d0f100057cc30429806021cbe7459332cc4011fd0e21ac2190223f60276d09300072ebaac79888000af58690f31084018feea3a2c0188027d61e43085100066e43ac71088000abe86191214c021978c939c84980a32f19371509300463eaa4ec20a6000d9c849cc21100015dd0e21ac418037a74c164084300047e432e31928000c7e74d9760484019bb0839ac488002fc60043085100063e3b6caa1a42008fd809cf62550018fd0abb042180023fa1f4358021005ddc22609022000e5e6598c43c800197d07bb2842100367e1d4310f210463eaa2e131e8208cbe74d92214c001d9a4331842200031f5537058910006bcb2ee09968000d9d409cc21100014fb0c3aa43a00031f1d47458031006ae21ae6312a800cde73d8e42480014fb003b2a9990033798d72cc4400074eba2c61088004cf7105d84308401d6c43b2042980029f61742582320053ec2886b006400cbd87d93324c001c7d0ab2442180a3e35c9
  | 11 => 0x4c0019bee8b84c6108037618d7010d100063e42ceda126008cbe87d93314c0011ff0eaa2c1988035d594714cb400066f31ae02184200c7e76550324c0019daecba665190172f1d3644c5200074e32487b126000c7d855d841c80019df09bb264190031fddb73553200047ec3887b024200d7a655c021d0001d3a8621ac1108031f1d86510d100465e3a6c890a6000afb8790d6008401d5d05b20c498003378c076485300063dbb2a89806000add83d9063484018feecb22a9988031fa1876551320063fc3aa8b006406c7d549d843440018feecb2a87988023f61873c86400065fb20e790a6000ed663cc42110001c7cc8aa2c1990031f60c76551210047ec34e71088000cf5635c442c40012fb0faa662a00031fddb5450c210057cc0086b106000ddb635c0434405dc78c8392a89009397d516308440006aeb2ce610e8000d7872dc154cc001b76c8b8086880025fe1d54cc5300057bc32421086000abe819cb644c0012f90cba884980033d5db310843014e9f42ce810c6008cbc845c263d081dd6e2132642180035755173087400075dba486b004200ced7298a6190c014fb0a3a2c019002af219421093000576c1486b006408c7f545c263d04014fb0b3a2c1990171fd527610d2002e7d202e131682008ff805db32d04018facab8665a00032f1d864885300965f38cc81086000cec74189204400193ac939842180035ed5170085400065fb24e420a6000cde635c243084011ff0cb8665a0803b65c1630844006fd820042a022000ade82dc663100279e8e2b2265988023fa1c6350f2112e3faa0e6b068200d78711c154cc0271fb0f31e8610837b5442630844006e7a882ec108600087d87d5263904011ff0cb806520887e55877150c430071fb2ce23226000c7f76dd521900018f90ab84c62107a3fe1d648c8310047ec34e790c8006cbc74d9132440017e30198e42180031f61676cc9410071fb22a818a600dd7a655c0210c01b9f500bb043180031f10d76d53200057dc0286b0e4000cbe71190324c001c78c9b2e86908176e1917010d200063fa04edaa24200cdd635cb31100018fe863b2a8880038f1d154580320055f436863128000c7d545c0624c44f97b0e324429809b97d5163484400045f434e810a6000e5d7598f43084011ff0eb204298002bee0142580320057cc0084b046200e5d65cc931d00017710898640900238f1095458e4008d7c40287b024200abe811cd640c0013f30139663180026f61273d8121005f8c006390a8000cbd87d93214c001d38c6a1c42a00038fd9571191300063e3ace8b066400c7e7655232480019b862bb662200031f10d76d50320066eb20e69086000c7f541cd6008401ceaa831e42908023fa1f32d814106e7db22e010c6000c7c761d52150001b9ac539842200031f61576084300066f324e6
  | 12 => 0x277a0e72d06300053e432a99922000add8319063484018f8ec382a9990029fe1574583320063ec2eeca186200e6d7558b3110001cdb0a39ac42009b3750e7610d210063ebb2eb98c6000cde7358c21100018ff0b3b684980031f21d54586320065db22e010a6000c7c76d97424c001c7eca32286908376e99170084300075a18cc81086000a7e861cd54480051ff0cba06518803a7590434c832006eda04e610c8000e7a85d0d60084011fd0c39a42980023fe1d63907200047ec3886b0042008ff874c960d04014fb0c38aa91901f3e619700853000775410e6b004200c7c7459563c8001d76e93a2c0108023fe1d640c8311165f3a2c81944016cfb865c0218c0531fd0f21ac1990772f9d164cca320063e420ecaa26430e3e641cd548c801ce8c8aa0c2990438f61464cc9300066f39ac79088000cf8409d821500019bd0d3984320002bee0d745802100756326c410a6007add879c2630840197d08bb042180375e595700844007e3eaa4ec2126400cf784dd9310c44fe7680aa44320003b558f31084400063e21cedaa24200cbe71d93324c0011fb01bb265a08039d55243d85320053f434e4aa26400a7d87d5263c40011f90eaa2c19880277602730843008f4ea02c69088006c7d549db4344001aeaa838a64a0003ab88764485300077541486b004200cde73d8c625001bdaa20b1842200033798d720c4400063f3a2cb9964036cbe87191524c001d72e0b2042180031f5d975cc4400063e400ecaa24200b9d81dc94310c018fb0abb6841900357552730854000757b26c510a6000e3f41597420c0011fd0d3b2429805f79085720c630006f5b12e010a6000ade839d360484011fb01398c4a0802afe1f64085300074fb266598a60009bf8750842cc02bde503a1ac01086b8fd0d54d85400075690ac81086008abd87d93414c0015bd07b26c6900232f2117098f410047e43ac690c8015cde8798d43084011f90ea16c0988036e21170087400465f3a6c81926008cbe87d93324c001c7ec8aa0c2980832f9d364cc9310074eb1c8790880078fd809d8414c001ced0caa6c2990029f61443d89100053ec20ca31a2000b77815c863550011ff00bb68598802bba084358830135cf426c6a1a4200cf77690d21084012ff0eaa0651801e7720e76085300066f31ce41888029d3e74550218c001978c8b8e64980037620d70109300071eba8c998a6000cbd645cb310c00b97ce9b26629002b57d52731073012e9ec2ce81086032f8f2150c43884378faa9b82c5a18038f59354484300045ec38c810a6000cdd74dc26308401a78e9baa42200032f1d1624c3100465f43ec81926027b9f8750c4388401d3a86218c48800337dc47158c40005ea41a4210c6000c7c76d95214c00197ee931261880236e19170109300053e432a921a6400c7e74d9462
  | 13 => 0x71e320cba1a4204cbd845d843084499bc86bb08610802ba60043588300071eb22a99946407af9809cd601044d57d09bb242980031f9d865d0d210069e422e031aa800c7e541d9544c801d6ac9988421803abe2014398910006aebae6598a60008ff8759232c400197ac8b906218003bae0974580210066eb24e610c6000c7d545c262cc40b1fb0fb2464900031f61576d0b310047e43ac890a6000a7e83d8860550019be86bb486108023fa1872545300066f3b28610a6000abd86d0e6190c11978833b6829801e7761e43cc5300072ec2ee2b1880008fc8755160cc8018ff0eaa2c199003ae9c364085300063f3b6a818a8000b9e82dc54310c018f90eaa2c7908031f60876551300064e324e610a6024e9d83190214c0019bac6b9062200232f1db6410930004be43aa89922000abd821c5640c051e3886aa287908863f21d644cb310057a4328790a4200ade831936348401978c8b9662980029fe195450c211371e326a890a6000e9d43dc96010c015ed0239ac0210023f61873486400457cc04e6b068400cbf645c0214c00197ee9322c1988035d55171c83100076a31e8610a201fcbe74590310801bd6a20b2042180023f21d54d81210047ec3ec72124008c7d545c263d08012ff0eaa46390002be60264983310063ebaae031a4000cbc845c26390801cbea931887900032f60b7650c4314e5f3a2c99946000b9d82dc54310c1b9f4c6b8043980031f1d86550d210053ec36a99086000e3f64553624c0019ecc838a659007be59847150c430063e42ae031a4200ead21190214c001cbce9aa4c6108033edd8414c0300053ec2e86b0e64008fc8758d21d00018ff07bb2a99000397d506350d2100778c0e86b004200e3f64d52214c01dd3e60b2642180227e21970109300072ebaac62184200cdd639c83110001d3a8638ac021803370c676cc540004be43aa890a8000e3c85d91214c001abecb39882980029f21954d8d210172eaa2c61908032d9d7650c43084018fce832ec09081fbc2057358021006bcbaae01948008cbe74d90214c00137f0ea1842a007b4f9d1548c83106f4ea02c61088000c7f76591540c84dd3b063224298003379cf63d85400061fba8c890a6030cbc641cd5448001dacc790c42200031f1da72551320074f416eca18860baf9809d1600c401abea939843180037690d7008530197cb10a862184200af98090b604c8016d904b8aa8990031f18e72181540071ebacc81086000e6d65991320c801c7ac9aa042180029f21954cc1100066f434e610a8026e9c6490d214c0158fea93b0859801b4f9d15418d10006b6b2ae5a1e4000cbf721c9640c001db28621ac0108031f9d365d85300563faa4eda0e6000e9d6458c43c80018feeb3a2c199003a750c43589100063fb2ae23126000cde73d8c615000157d0da1e42a0
  | 14 => 0xf709c2630840157d02392c8180029f6174358b310073cc28e8b0042008ff805d84308401b3d0939842a0002be6137358021006ce39a8690a801be3c645532048001d7108b9ac0108034f9d6740c9400acfbc3a879884200af580908614c8011ff0eb1885100032f9db64d05300067ac26ec9886200e9d8118d435000daf6a8b8086880038fd915408530015cfc30e4a188626f8d7250c434842f9bd0f31a61880031fe1576cca400f736aa4c41888007cf4615c331480018fcecaa664a08034f9d1750cb40006aeaa4e610a6000d7b545c0214c001cbea831862a006f2f9d1640c7200063ebaac620e400087d87d5063508013f30139c84900023f21d435802108736aa4c59968200cf776c852190001aeaa8b8865880031f10876551320062eaa6e6b1220059f9809cb61500018faed328879009ae7a0e4350d2102e5f3a6c831a4000d9f72dc54310c0197cedb2442980023f61a72d04300057b4368790a4200adc8358b4044001d3ae732042180032f60376508420072f42ce93184200cdc8758c2110001cbb0a31c62a00029fa1b54085300043fc3aa83126200af58110d600c42f5f50e39ac0108bb2f1907255130006bc32ae021a2000c7f76dc1540c801b3e613a04218003aee1173580211363faa6ec9088028f1d7550c43c840197d0fb204298003761cd30481100047f43c86b0e400ccf876d0120440019f4c8b8042980234f9d154cc9300051ec24cb3206400eaf6418a214c0018feebb0a609009f8f614648853000677396c5b0a86008ff875933294001f328621a4088003ae1d043580210063f3b2eb98a800ddea625c02110049c78c9aa0429802357d5273d05300073caa0e6b004200c7d811d9544c0398faa9b82c2218439d55332584400057c43886b004200c7d545c263c84019d843bb242200023fa1f43583210067dbb0869004000e7486550614c8018feec3aa43200029f61474583310047ec3c863122026e9c7458d2110001a7aca3a261900023fe1d63d08200065eb24e4188600097f8755021cc0012f90eaa265988029f612655803205d7b408c7b0a800dbf28010c21440018facab86659880397552634c3100ae7b38ce931e2000c7f42dd954cc4019bae6318c090803b558f218844000576c16c831260009dc835c4428c02997d08bb486108533d1c6634cb41007ca40a8621e4200c7c8755163440018deecb2a64190033798d710c84014cdf424e690c6008cbe645c243cc401af6a8b8064a0003975516310c211cdcec32862184202eae82190324c0013f50e21a40880035e9d5700c9400075cb80c810a6032e9c6250c43c401b9f6c8b8042a0093a71924308530004bec04e7b12a800d9c7498d30c8001c790bb204298002bba084358a300053f436a890a6005cbe74d9232480099da42bb0861080337900735891000
  | 15 => 0x8a026088002b720d74580310066fa1eeca184208cbc76d93414c00baf6a8b80869009a3f61f64d8d210055ec34871088000eb764d84214c0015ed0e21ac21800357d0e73189540053ac20cbb0a6400c7e745943204001b3ae821e6519003679ce43084400053fc3acba184200cbf649cb314c0018f90ab84c620826bee0173580210047ec3e873122000e7a851d160084019eae238ac02189f8f9915488430136ce3b28621a4200c7c439db54440015f700a16c0988231f5517098c4105d7b40ec5b0a8000d9f8750c43084019f6e93a2c0108966fe1a74084301071fa1aa8b0c8612cbf70992210c0335f50e3a2c0108032f192720c5300067dc04ec10a6000afb8750d600844b97882bb682180031f5d9750ca300073daa486b004210d9f76dc94310c015bd0d21862980027d61c43085100072eba6a931842008ff8750e624400197ce3b26c4980031fe1776484300071f322a93066416af68110d610c00197c803b242a00025f61f540c9400065f43ec890a6000c9d641cd210c01d5bb0d21e43980023fe1d63d0a100047fc32e420c602bcbe7459332940018ff0eaa2c1190038f19464885300066f324e610e6000e3c659c8644c0013f30039a84880027761e4308730006bc32ae020a601cc7f545d843c40015f700a1ac110803b518c21cc110006b6c2ced1924000afa86087304c01197e853b084980021fe1d5498a30006773a2c41906000c7c8755160c844d97ce9b26c0908038fd91544853006e6f982ec10c601ee75541cd6110001cdacb32265900778fd0554d8d420053ec32a89964000a7d851d160cc80197ac8b8e84180029f6195458f200063e42cec212600097d87d50210c047aeaa8b8885188031f1d9544c52000756320c410a6000cbc645c8314c0018fac6b90c6aa002bd61b310844005c7ec3ec5b0a8000cfa83dd9200800157b053b0c8980036d1d0214c110125cf41c86a184200d9d435c043c840197908b80c6a10035e595708c7400073d3a6a8b004200afb8050c62440019f109bb24010003ad59321884300066eb1ae21908024abf875934308401ceca8aa6c299002bde1921086300469e322ea20a6000e9c82dd94310c014fb04318c0aa0032f19273c85300057b4188530c4000c7c851d9214c001b76c8b8082980034f1d0754844000677108ec90a6000cde8718d30440019bd0d39843a002357d5273d09300072fc2ae131842008bd87d90214c001bd0c4b8042980023fa1873485400063f3b0cba0a6000c7c841d95448401d38c9218c4980031f10476551300076a40cc61088000d9f8750c43484010f90eaa2c4880038f19154d85300056f418e8b006202cbe645d0320c40157d0da1282980032f19171d89300047f43864b0062008fe87d0f60484498fea8bb0861081f3761a73086301474e3228790a6000cd
  | 16 => 0x3185320065f3b6c9a126000de7825c3310840197ce2b2086180023f61a72cc4300063fc3aa8b066200e79545cd6008407978e838ac0218029fe195458f200063ebb2a810c8006db9801d130440539f70cb80861800b2f1d16458032137cab8a8621a4200cdc8758d211001b9be60bb04218092afe1c6408530006dc322e010a6000e9d81dd94310c015f30839ac01080357d50734863000676312e1a122000abc845c063484018f8edbaa43a00376e99170084400065e3a2c298640008fd8798f20c40015bd07b26c6908029f61664583310071fb22a81924000a7e86553624c001c7ee4328c89805e3fa1a73105300064f3b28621a4200dd473c85210c0015bb0fb1862a00035719673109300055ec36873148629cbe74593318c0010f90cbae80980029fe19544cb200075b408c9b0a6002dcd435c8430c801d68c990c4298003379cd63d0b200053ec2e85b026200e9c6418d43484018fce8b286518802be602649803200773414c790e2004cf87610d2044001cbeca31a6088003a72194310d21006baaa0e69084200cde745d26308401b3ec939884980823f61f64cc931006cfc24e610c8000cbc829db43500018fce9b2e64980036ed0d70087400063e3b2a898a8000c7f859db42440019790eb22421801e3f61e43d85300063ec2aec1088000cbc71191524c001a7ccb3a0421800337a1a73084400071fc2ec9b0a6000a7d8510b604c8019bcc939842180036ec40744c110006ae3a8e69086000c7c8755160cc801d6b02326c298003378c676cc540046ce324e7a0a6000c7f76d51210c001fa66390a6018003a750c4398b10077e8186429822000c7f405db5408451c7cc9aa642180038fd9154189300063ebaec7a0a4000eb9741d1600844fd3aeca1887108032f9db43085400063e3b2a890a600087c8755163080018faa9b82c219093a79d16308440134df424e7b024200cdc8758f21100013eb0039a4210802bba0863d894001736aa2c41908000cbf649cf424c0019bcec99064a003ab721943c85300365f3a6c9b1a2000cbe71d93424c0018facbb8243a00031f1077655032004be43aa890a600dcfa805d821900011fb0e31842a00031f9d1650c8300075790cc81086000e78855cd6008401d68c99884298002be60043582210071e328c8a1a42078fd869ce218c00157d0438ac818002be60064181210063e43aa8b066200ade8718d43484018fe833b6a8980033b08776484300066eb24e610a6007cf4219d8314c039aeaa8b8885880032f5d2649833102ed6c10e89824000e5d545c263084018fecab888698052bd61e43185320063aaa6e2b1a4000cde7358f41880018faecaa065200032f60f765084203e5ea0cec20a6000dd9835c0218c005c78c8aa0649807b1f5517610831004bfc3aa998a4000c7d655c032d000db70e
  | 17 => 0x86000cdf739cf6048401b3ae821e64988035759573087400047f43cc6a1e4200d5f75dcd210c001adaa9b926190023679d243085300074ea1886b00420097d8719443440014f90cb82a8990023fe1d43189100067ab22e21906200af987d0d60084011f90cb8864a00032f59171108300053e432a921a4200cbe76191214c0011fb0f192c1208031f9db65109301274f3a4c61088000abe86d0d2150001978c8b8864980029f619544c83205e7cc32e010a80078fd87d8b614c00197f08b84c7a08223f60276109300066eb20e690c6000e5d54dd16308441a7ce8aa6649886f1fd517610f2019f1e326e2aa24000c7c8755162cc0013b906b80849903b2f9c964084300471f322a89862000ebb4310d600841197ce9b264298003179cf63d89540071f3aec810a60008fe8710b604c8015db0e21cc4180031fe03765532006e7d202ec1088000c7d73d8860550211f90cba6649887f2f19072501300065e204ec10a8000cdc7358d42c80018fb0bb82c4218031fe167610d100274e98ac82186200cbc649cc214c011abaa939882980039e1d354580210057cc0064b048200cbd7419063484014f90caa064980036e50d70087400066f41aec10860008fe869cc32500015f300212c1990033518c714c9400369f3a2a99922000cbf64dc1214c0019eac8b8865880031f21d54d81210067d3a2e8b004200af98610d20840015bd0d218c2980037ad8970085400ac7fc3ac99886000cbf645c3214c0019bac9398439809b2fd0e7610d210074ca1886b004200d79545c0210c0015bd063a2c0108a63fa1e635031000779c0ae6b004200cbc645c6524c025b7080b8442a00039ee0154d81310067bbb6869084200af986087308c073b3ee238a862184b375c263884400063fbacc8b066400ade831d160cc41b5f50121ac010837adc4264084300057b4366390a6000c7e76d94214c001cbaebb188688002be60043589100065e422e1318420097e87d512150001b38e831a60880029f61471580320055ec14e3b226000cbd645c4320c00b97ce9b26c6900039d61432984400053ec20ca31a4210c7d545db32d04013f30039a42a0002afa1b42909300072eaa6c621a2005af9809c96010c014fb0daa4879880317dd9544c8320047f43c84b006200d9d849cc21500011fb0d39c85880029f21954d85300075b3266390860008fe861cd414800197d05bb2862184f2f2137650c210e7cab8a8621e2008d9c649cf424c0059ba8639ac420803a758e43484400e69f3a2a91962000eb664484210c001978e7b2442980033bdca72580430071e32ec990a6000c7d54dc1618c86997d0e322a2980033e58d7008740004bfc3aa810c6000ade82dc56310065d3cc2a1887990c38f1907355120004ef434e7a126000c7e76197424c001c7f0bb2064980039d5524
  | 18 => 0xc401d3d0431a86a00023fa1f43589100071f322ca21e4000d3e745d731d00011fb01398c4a88023f60076509311465e324e410a600de9f30590210c00197ceca1682980031f5d762d01100076790cc71088008d3e74d50214c00187aea32662980036ed917010d20087c7316e4a1886298fe8790d600c8018fd023b2a8980033b589700c8310073ac28c9b0a64008fe861c9544c00197ce332064180037590c714c8320075cba686b0042008fc8750d61c8049c7e86aa0c4a08763fa1e43588310f71f322a8188400097f8755331880015bd0d21ec498003a79926310f200871fc32c8aa66400aed82190624c0019bce131886108627761f32cc4401471ec2cc990860008fc8758930c40011fd0d39a429808f1f5517610a310063fbb0e6aa64024cbf405db43084018f886bb6a8108033edd074580210065fb24e7a0a6000c7d765d432100015f700ba2c1990035b1897218d54006bcaa2e010e8000ecf2158e21100011fb0f31c85880033b58970908310076b10cc61088000e5f549c26308401b38e721a422005b3d88576084301be5ec38c92926000a7d8510f61480019eaed3a663188023f21d6350b200053fc32a93066200af980909608c4016db0a32464900039e553735802108e6eb84c69088000cf781dd921100111fb0fb26c4980025f61c6510930004fbc3a421088000aed8210e628c0259bae0b1c422000277e1d43087300ae6f3a4c62184232f9a6050c43084019b8e6b1a4220002bba0843d89300071fb28c990a6000cbf845c263084014fd0caa6c68807b67dd87150c431771e320e4aa26000c7d76552428c439aeaa8b8e87880023fa1f32583410063e3b0ea90e8007af68190f614c0019bce6b1884080032f5d064d8121006bdb8ee0aa66000a7f86553210c0014fb0daa242180031f9d165cc8320076bc0cc79088000c7e76194414c001ceaa831e428805a6fa1272d043008f4f982c89086000cde309d8214c00157b0939ec0908036e9d1700c94000676312e199220008fd869cf20c40014ff0ab8ac19909bc75d54310d210057ac30879884200cdf839d8214c001cbaa83a2c6108026f61a740843013f8e21ea8a1c42008fe869cf42440095eb0e218c2990038f61564c84300047ec04e6312a800aee8290f624c001c78ec322a8980731f55370587430775a884c99086000a7e861c9544c0018ff023b2a8990030f5d464085300063e21eecaa64008cfa405c263d04019e909bb262188039720d54d8d100047ec34e69088026cbc409d843484018faecb2e87900e38f99071552320066ebb6641908000afa8750d600840197ac8b9682180029f61743587200063fc2aed9942000d79545c02190011978e9b2442980133e4417610f100066f39ac610c8005db9801d13048009be4e221c40880032f9db6410530005f8c06621
  | 19 => 0x23fa1e63487400047ec34e62084000e3f655c8644c0019b8e231a64a0002b76006390d210063fbb6a890c6000d5d545cc2150021d5b0432664980031f9d975cc53006cfdc32e010c80009f78748421cc0019bce7b1842a00038f1d864551200dd5fc3ac821e4026c7d549d84348401dd5043a2c01085e3fa1a73885300063e3b0e4aa26032f948150c4308401c7eebb22429809ba719143485300063fbb2a899064008fd869cc21900319e862bb04220002bba0843583320063fb2ae3992600097d87d5021900378faa9b82c42180367d0273086400ded7410e89864000afa841cd6008401dac42b1842200037cd03714c9400065f322e39906010e3f4255263908014fb0c38aa8190039e5537458021004bec38ca20a600dcfa805d821100018faecaa66310003ae50c435802105ef810ae018a8000e5c855c263084019b8c6b8086880023fe1d42583310055f4368610a8000db8845c021500010f90eaa2c69004eb720f7650c210065e208eca0a6000cbd87d90324c0012ff0eaa462a004e3f61e63d0e210a47e43ac4b0c8600eaf21592210c001af6cab808498047375c163484400063ebb2a818e4000c7c74d953244031bacc339842200033718d720c540066dac20e29968000af48648421cc001ceaa8210c2990a74f9d1540c6300965eb82c91086000c7c40dd954cc41b9bee1318422006f2f9d16498f200075bb206390a6000cbf649c8614c00197b08bb042180036e8c274084300066fb1ae418a8021cbc7459132cc401d3d0231a86a0087a719243cc5300057ac0ec630a8000cbc641cd214c0018fe853b6a8980029fa0b63d81540053ec2887b126200ee58218c2144049e3aeaa1886108732f9d1648cb1000677c16ec908803be3e641c154cc8019dac4b84642088a3fe1d640ca200072eb2e8799662008fd87d8f41480011fd0fb2264880a3a719143c87300053ec36a81086000c7f655c4644c0019bce7b1e42a00033761a73085400065e40ceda1a8000dd5619cc21100018ff003b2a898003371d0634c1100063ec2ced1924024f1c43551430841baf4cab8042200031f9d9540854012e5f434e81086000cbc82dd94310c1137f0e32042980025f21975105300074eb1c8610880298fe869cc424c0011ff0eb2063900a39755263c8440006dc21ae01088000e3f7455160cc4018feecbaac9988232f9d3640c5300047f434e621a4202f8d621c94310c0197ceca1842a00029fe19540c720004ee41ae020a600bcf8809d821500015dd0521ac1990029f6174358432004fa43a869084212e9f4058e211000197ceca1886908377c9857008430004dfc3a8621a42008ff865c0430c4111fb0fb2062980025fe1d5418d200066e31ae518a8026f1c435514348401978ec32042980972fa1176d08300057cc3a86b004200c7c7459560c
  | 20 => 0x76398c49022000dbb845c0325000197ac939086180025e21d544c0300056fc3ac6108800dadd8690c21cc051e3e86aa48790802ee61021cc130006cea1ae02184228eae82193214c0018f8853b6a8980232f1d364085300061e3b6c8aa26000ead21990210c0019bd06bb664200029f61f5418d400047f43886b0e4000cbc7418930440531ff0eb2065180025f60273189540067cba0e8b004200cbd81dd94310c01d72e8a1ac01083737dc163084400066f41aec1888006cbe861d130440014f90caa6c0908031fe1d54d85300057d426e6b0042009fa8710d208401bbb4c6b8042200223f61a7310a300066ec00e6b122000e6f65d88214c001d6c42b2042180023fa1c43589100043f434ecaa26400a7d8655160cc40197ae83a2c01880337dce73580210072eb28869966213cdd8798f4308401cdb04318c4aa0032fd9172105300065ebb6872184200d7b855c03190001c7ec8aa662980023f61c32580410065fba4e8b0042008ff805da428c40f9f1013b042980023fa1c32580410ef1e212a9b1a84008fc865ca414c04d978c8b8c849800f3ee197010e100073caa086b004200c7e64dd5320c8014fb0c38aa9900232f9d364485300071e3a2a8b066200c9e649cc210c067978c9b8aa898003a750c4398b3106d7d40686b004200c7f43dd954cc40197ee9312608800337e03764c8320deb6aa2e5a1e4010cbc645d3324c4019790eb2042180a39755163c84400063f3a6ca31a4200cbc845c063484195f700ba2c0108029fe195450f310071e38eca3226011afa8018f60484012fd0faa24298002d7614434cb310056ec3ec79928000e9e73d90214c0158fea93b685980023f61f43189100043e43aa8b1c2000b9e83d91434840197ceda1c8690803679cc43086400047ec3c84b006200e3d645533208001cf30a21ac01080bced01540ca400063ebb2cba1e6200cf9645c0210c03bc7cc8aa465880032f9c464949300357cc04e2b008600c7c80dd9540c8175f3013a2c01084abea004358221004eec30e690c601ecbe74592320c4015f70fa1ac0108031fe0b76553310be7dc32e01086015cbd845db430845997cc9ba2a6190032f187744c1200065fb98e6b204200a7d86d52430c8539bd0d39e84980034fdd15458032126cfbb2862184211add8690d21cc0011fd0e31a86908cbe38854310d210057bc328790e2010cbe645d3328c8018f8ec392a998002b7a037498c210066fba0e8b184200cbf7690d43084019eeeca1a42108032fdd3624c110004dfc3a8621842008fd80dd9420c8115f10ca026090003ba60874580210076da1c86b00420087c875516108001af6cab8086880026fe1d4310f210075b40ec9b0a6000ed9731cd600843ba7ce8aa665190031f59570c87400053e43aa8b066400c7c76d5121cc04997886bb686108
  | 21 => 0x831d16008465e3ccaa1886108032fd9272d0530006ed21ae010e600dadc8650c214c001d3a8621ec090802b7e1e63084400071eb22a81962000cf8645c0214c04ba7d0b3a042180038f19764485300047e432e418a80008fd809da424c8119f480b84c7a10031d5537158d210e63eaa2ec216200dfd03008530440498fea8bb68610803ba60a43580210053f436a921a4200e7b54d0d6008401bac863926218802b7a087198c401271f326a81086000c7e76550214c00f5f30139ac01887b1f551760c4400063e3b6a890a8000ced769d3328c8018fcc2b98c4aa003ba60b435802102c7ec3ec9b1a401eb9d861c54310c0137b0f2184220003371cd4358b100065f3b0c990a6025cbe74592210c0118faa8b84c6210031bdd9544c8320072eaa4c7a184200cec211d92150001cf2a8ba2c0108029f61870553320de9e3a2a89864000b6d821cd54c80019d8c939662900031f1d1654cb200069ebace8192800ddd9635c02110019dc842b1681880372fdc164084300f72eaa2c61888000c7c85dd92110009d6ae8218c2990031f6157610a310557dc02e6b068200adc83589404400197ec8b9086980031fd517018d210055ec08e4b206019cfb865c02110001dac8621ec299002bee0143580210063fbb6e0aa66400e3d64553210c0018fecab9662980033b8867690d210065ec22ed2184200eb970990210c0019f4e6b9ac0108872f19273905300063f3b2a999280008fe8710d60c84015730839ac010887e59877150c430075bb20c390a6000add87d8e4348401cbb0b3a4c6108035ed51700c5400077541686b004200cee74988310c00197ce2320c4980031fe15760c6400363eaa4eda1220009f98710f204800f3f10cb80429802abee017358342006bcbaae01928011afa8010d6244001db4e721ac0108023fa1872501300ec7fc3ac99946400e3d85193614c0179f0eca0240880029d61065185320057ac08c430a8600a7f86551420c8015ed0da1e42880029fe19540ca20134de422e031a4200a7d8519363484235b90ca1a42980933750d7610c21004fbc3a8618e4224e9c6450c214c0013ed0fa1a42108032f99172cc4300071e320ca20a6000c7985dd9200802397ae0b2242180037650d70085300063fc28ecaa26400aed80189424c44d978c8b9482980035e551700ca400065fc22e131e8400abe84dcf604844dc7cc9aa242180035edc870553300063ec2aec1902000a758510f614c801d5e4232442980031fe1576cc8200074e326c6a1a4200af7864842190001bb106b8082980023fa1872505300053f432a9b1a42008fd809da43484011fb0e31e84880023fe1970d0b3100578c0086b086000ade801d2630843dcbaa838ac62000277a1a73085300065e322e110a601fd3e74550310800dd3aeca18868806f1f5537058841006
  | 22 => 0xb266488002be60373d81210563faa4ec20e600dcbe71592210c001d5b05b26c4980023f6007358a510075bb264290a6000ed663c8530c40018daa9b92c688003975516390c210c67790aec1088012e9d30592210c0011f90eb2243980023f61c32582410055ec16e2b206000cbe645c8310c0017b106a0260880031f9da75cc5400065fc3ac9990600097f87550329002dbc842b90621805ebda1b31085300075b326621086000d7b545c021cc0019bce331e6420002af61073580210071e3aec890a6000c7e76d533150039d3ceca1887880031f9d06518d21005f8c006390e6000cfb76c85300c0018fecab8ec498002af61a4350c2114c7fc3ac818c6000a7f84d9464484015b900ba4c6108032fdd264583320047fc32e21948000db9845c0211001bd6a213204218002b6a0c74580210071e32ec810a6000cbd7419363484019b8e6b1e42200025f61c65d05300073aaa643b02420087d87d5063500011fb0fa12c019003e5e054310f210063ec2aec21e4000c5d7318c62550013eb0fa1842880232f1d364c8530006b6b2ae421e4008c7d549d8424c0018f8ed39aa8990029fe1954484300063ec28ecaa26400e5f74d52630841f1fb0f21cc598813b90844358b100061f3b0c8aa26000f2c6455232480030f90cba886980031fdd571583320067db9ce6b0042148fc865c6434c001ab8cb39842980023fe017610831075f84028790a20008fe8718d4148001b7686b8042a00123fe197110e300047f43c86b162000e7b549cd600844ba7ce8aa04218002b7a0e6458f200076710cc69088000ef18010d61880015eb02318c2a000367d9273085300063bb12e2302a8008fd87d9021cc0015f301192c0208a38fa1664c84300057dc3886b004225c7f541cd6010401d3a8621ac1908021f21d5458d210053fc22ea31a4000cbf649ce214c001bb306b8042180023fe1d6408730005ea41a421086011cbd72592210c005c7b0a3206498002f3a0c648c92012e5f320e6a062000eb621190214c00197f0eb224218002b7a047258c400047fc3ac99966200af98010d60084014fd0d39aa899003ae9d074580210065fb96e2b206000cdf72dc5631000197f0eb2042180432f1d164583320054fc328621e4000cbc74589304400157d0d21a869088f1f9d95490d310ee5e324e521a6000c7f855da320c4018f90b3b086880573dc4176d0c210053fc32a918e4027e9c4358e21100018faecaa484188023f61a72d06300fe5f3a2c99904005f8d7250c434801b9f460bb042180032fe0376508420267b30ae22186029cde869cc424c00197b0fb204298003370c07648530007e998842980601acbe7459332840018fceb3a0c6900031f614764c5200063fc06ecaa66200d7b545c02110001be68038a64a00025fa1b75485300063e3b6ea90a6000afa
  | 23 => 0x8430006afaa4e61086000ade83d93634401197ce9b20c4980029f614435863205c7ec3ec7b0a8000af5810c9600c4019bd06bb662200174f9d1548c92008d7d406c7b024200a7d8519363480014fb0a21ac3990238f191544c1201374e3228690e6000d7b655c0214c0016b906b82a8990021fe1d5498d210069e422e0312a800eb464d87214c0019b2c6b8042200031f9957099032004bfc02e431aa800cbf87590320c0015f301a12c0190032f5d074d8121004fbc3a4210c6021b9f86dc54310c1b97e80bb0422002b57d5273d0b300053fc32a81086000a7d8510f614c801db6e6b9ac0108023f21971909300063fc2ced98a6000c7d801d954484018f8edaa286908025fe1d54cc630066f210ae418e800dddb635c0214c001c7b0ab204218037b69c263084400063fa06ecaa06400eb87490d60084019bee93a4c61089b8f61664484300063ebb2a81884000ade8398d4348401cbaa931a86108031f5d9540863000576c10c63128000e5c83553634802b5bd083a4c6108038f1967119130004ef41ce5b0a8000cbe71d90214c0011fd0e21ac1108932fa1c64085301265f422eda184200a7d85d0d62440019790eb244218002afa1273d81210de5e3a2c8b1e4008cbe87d90314c0018faecaa4861084e7d61f43cc4210072fb28c7a1a2000e755418c214402dde50239ac0108032f592721043006e6eb84c6108800ddb8405c021500018f8e8b2a64190033d5d921084400057cc0086b08600097d87d5021500019b8c9398431805f3798273084300071fb28c890a6000d5f549cc21900015bb013a4c6108031f20c7655121005dc422609022027e5f5498e21100014fb003b2a8990039d55032986200065fb24e690a6002cbe74593320c81f1fb0dba264190031f9d954cc9300053ec2887b0a6000cf9645c0320c00197f08b84c62086f2f9d164ccb200469ec2ce810a600dcfa805d8210c0014fb08328c89906779085720c6400063ebb2a818c8000db774c8530c40018f8ecb8aa89900a3f21d644c8320043fc3aa931420008fd87cc960d040df2ae2a188688003379cf63d89400065f324e418860009dc835c0428c4015f50e21ac0108029f61065191210047ec04ec21a4228e3e85193214c001c7ecbb2442980031fd0c76551210065e310e89862000cec725896190c01ced06aa6c2990133d8857610c2107c7ec36e899662298ff87593318c00137d0f21a42200031f9d95490d210056ec16e2b18800097c8755130c8001978c8b96c2980031fddb735512012e5f422eda086005e9d7650c4348019b6d0838a65a00234f191751093000577c12e2b008600ddb409cc21500014fb0b322c7900031fe0c76551101471e322a990a6000e7b5450d6008401c7b0ab2242180032f987744c320004bfc3aa99062000cdc73d8d21500011fb0f
  | 24 => 0x2600087f875506348001d6b03b26c2980032f1cf64085300075a18ec810a6000cbf645c4624c0018f8edb82a899003a750c43989100071f42ac99086000add8098e43084015bd03b92c620092afa1b64085300455ec3ec820a6000cdd731cd60108471ff0eb2065188031fddb544864000c3e432ea21a6400cdc734c960d0401a7eca3a2608800b9d55032984400075710ac89086000e5d851d163084011fb0e218c4a8892afe1e64084300057cc0664b006400af98090960cc8018fce9b2ec6880939755263084400065eb92e3b226000c7f75dc560cc801af2cab8043a00232f1db64d093006f6d382c61088000aba841cd60084011fd0d3968298003a7e194310e2108c7ec3ec9b024200a7d87d50634800f5ed02326c298022af61f641093005d7a40a64b068200de8825c04348001cbaa9b1c86908032f9c564cc830005bcc2e869022004cfa105d843c40018f8edb22a8990036e50d70085401974e30a8621a4000a7d8499664cc4018feea3a2c1990032f1db64485300043fc3aa931220008fd80dd942cc4018bf0bbb2641900337a1073589101274e3228610e6000af9801cf60484014fd0c3aa42980033e99170086300073cc2e86b004226cbe74d90634841b9bae0b1842200232f212761093019f1e326e2aa26016cf67118f42440015b906b1260880033d590714c8320074ea1887b122000c7d859db324c4199f50cb8042a00032fe1d640c4300063fbaac29864000cf87650130480015eb03b20c2980032fd9172185300063ebb2a9990400d9fb865c0218c0014ff0caa264190031fd9571d093006ef4b12e01088000cf5641c532c80018faa8b84c688003a7e077650c430063e218ecaa26000c7c401d954484013f30e21e411009f97d5163884401271ec2cc81086000d9f721c94310c01ae906b88c0aa0061fe1d54d8d410071e432ea3226007cf8764c120440013f301394869807b2f19073505300053e432a990a601ee3c64550314c00dd3ceca1886880033b9d27298f2013e5f438c910a6000c7f761c554c8001c7eca32042980972f9d1640c83001c7e43ac2a0640298fe8790d600c4018faa8b80c790803379cf63d09100e65ec30e89862000eb664c86210c0019d8433b686908023fa1e43d8121006afb2ce7a0a6000cdc73d8d4148021d38c921e6498093a79d94310c210066f3b665192800bdf1801c53250001e3ecaa18869089b9755263484400071fc2ec990a6000adf8758c3110035a7ce8aa665080031f9d67498f10006afaa4e610e80008fd869cf21100014fb0a21ac1988032f9da72191300063fb8acba106030e3c641cd544c0018f8ec32a42980029fe195490e310053f430e2aa26000abf87590210c0019dce63168488002bb60843988300071e322a831a40108ff865d3328c801938e831a608805b6d98674
  | 25 => 0x4011fb0039ac2210031f21676105300053ec2e84b066200ed9831d160084018facbb9263a00023f21d53d81210de3eaa2ec20e4013add879d263084299f0ed21a40880038f19154185301272eaa2c61088004ee42110d620c4012f90eaa264a08031fdd95450c210f75b408c818a6026f1f435524348401d38c6a1e42a0003275d94310c210076b2188630a640deba70590210c0018fd063b2a8908029f61664583320057cc0086b0642008fc865c8414c00147b08328c89804f3d0877650f100066f31ce59888000a7d84dd560cc8012f90eaa243980038fd9154cc9300ddcfc3a8621e400cbd4814cb31d00239e903bb242200023f61a7210c300057b408e8b006400a7d8499560cc4018fd0abb686108036650d7010d1012e7dc32e02146000c7c76dc554cc00157d0839ac0108031f210765511002e3eaa4ec21a4000cee625c342cc401cbaa831a60880932f10d76084400053e432a818a6000cbd87d91214c001abaa939842200372f5c16408430006cea1ae021a4200a7e87d51600c4014ff0caa261900038fe17640c53003d7cc04e6b004200add80dd263084018ff0ab84c7a08031f9db65485300063fc2ceda1a2000d5f659cf424c001dcec5b084298002be60243580210075d3a686b0042008ff805db420c8018feed32887900a3c79d54310f210057dc0287b0242008ff8758f4188001d58c9b1442980031fd95710c9300053ec32a899662008fd87d8f42440015f30c20a60180038f59354884300053ec2ce6b066400c7d759d263c40015bb003a4c610823671d14348530044eec3c8618a6014cf4615c6434c0011ff0eb2663100033698d70084400066e188ec98a8008cbe74d93614c0018fcedb2886908035e55170085400047e432e021a4200afb804cb60504013b906b86429806f1f55176d0f200063e41eecaa64000c7c761d5214c07597cc9b82a9990033ed0176086400063e3b0e6aa26000cdf739cd60104015f30021ac0190227761e430c93000676b1ae420e4000d5c659cc414c0019f4c6b8042200771f551768c8411267ca02ec1088000cf9105c06355001c78c9b2e829802b2fa1a74087300057cc04e8b066200e7764553614c8011fb0f192c0208029f21971551320065fb24e5b0a601cc7d54dc161108011fb013b0849909b9755163484400465e424eda0a6000c7d655c8430c0010fd0faa2c0188031fe1d54d8d210bc7f430e6a022000d9f649cc414c001d5d04326c498003378c07358b100063ebaae231a8400c7d75d8740480015bf0eb1864200033d1db2148530034fc43a809822000a7c8655143484019bf0eb18422009b1fd5276d0d2110f2eaa6e2b188026abe86d91214c0011ff00bb465208031f5d954084300063ebb2ca21e4000bd6831923144001972c8b8042180025f6027218d54046bcaa2e021
  | 26 => 0x33760d76d0c210047ec3884b006200ebb4390d6008411b3d073a042980a2e7e1d4310f21006aeaa4e610c6008d5f549cc424c001a7eea3a243200e6e7e194310c210071eb22a81086000e7b855cd60084017750810e60980033b98970ccb310063fc2aed1962000abe81dc9640c001cef00aa6c2990023fe1972104300063eb2ae01908200e5d654cb31d004fd3ceca1887108033758e72cc4400055ec26ec90a600ecdd7098f2110001c78e5b28c8980023fa1c4358430006cca1ae021a4000af98790d6008411af6a8b8082980023fe19740c8310057cc04e8b006400cdd731cd60d0801da8c621e42880036e211700c9400066e384c6a184200e3c655c4644c00b8faa8b84c5a1803a750d7158043007caa188618e4225cbc74591210c001c790bb244298003a75cf64085300f6eaa1ae2218620ad9e7490c21cc0015f10ca1e4090003ad1876408530004ee41ae02126000cbf74d8530480017730138ec8980778f191548c9200047ec34e720e4000dba845c02110009d6ce8218c2990032f9c464cc9300074e422e13184218ef2811d1600840b97ce9b2064900026f61f4308540044fcc04e7b0a8000e9e81dd94310c49e3e86aa486108023fa1a734854013f4ec18c910a6000af683108614c801970c8b80429803b2f9ca6408430046cf3a28610a6000cdc7650d21cc03dd6b0232062980023fe1d43580210063e426ecaa64025cbe74590210c00157d0da1ec4a0002bee01425823210ecfbb6e2a18860acbe64dc1430840157d0da1ec2a00032f9c972d91300051ec24cb326400ae3e6455330c4001c7ac8aa242180032f5d074580210657a40a65b028212e9d4058e211004dd5d0432242980a74f9d154cca300053f43aa8b0664059f88750130480013bf0e99065a00031f5d954cc6400074e3266598a6000d7b545c0218c005a78e8aa2c019036bea0043580210063faa2e1318420097d87d50214c0019f2c6b80422002f6d610714c9400071ebaec810a6026e9d7650c43484019b8e7b1a84880033e98d700864000774c10e6b004200c7e645d9540c8015f30c212601800397d526310c210053a432a9b0a6400abd86d0d6290c011f90eb2242180872f61c64cc5300063fbb6ea90a60238fe8790d610c815abea939e839800b1f551760c8400165ec38c819260008fe8790b604c801cbaa831a60900023fe197010f3213f4e3248710a6000c7c76551424c401978e9312618800376e0d70105300043fc3aa931a2000cdc611cd404c0012fb01396c6aa0031f9d975cc7400053f43ea8b066400cdd701c2630845197d0e326429800397550634c94000756c16c83126000eae21191214c001a7aeb3a662a00031f1db71551300067c322e010e6000cbe645c4320c0019baed99662200972f19073501100065e320e790a6000c7f655c06448
  | 27 => 0xe32ce7b024207af68190d60cc41b9ee20bb042200029f21954909320055ec36872184200c7c811d9544c0018fced3a864a00032f59272cc4301479da02a990c8005d3c645d4434800197f07bb2842103f2f993744cb310065fb16e89862000eb681190614c0019ed09bb2621881ebd20542583310076bc0cc61088000cfb865c3320c0019b8613b042980028f61065191320063ec2ee0b108204dd47110d32cc4011f90ea1ac1908028f61065191210065e322e010a601be9e7650c43c804b978e8b24421809b8f19154485301063eaa4eda126200e9f845c26308401cbaa93a4c6108463f61f63d81210053ec3ea931c82228fe871894044001cf700aa2c1190023fe01760c8411265fa1aec2184200e5d54d8c31500015bb08384c6108033ed0276085400067dbb2429806000e9c8650c43c842f5ed0221ac3180938fa1664084300569f3a6a810e6000cdd869cc21d0001f2a8621e43880034f9d275cc7400053fc32a93006404af78710e61880012ff0eaa04320002be21e43580210072eaa0c6a1a420097e87195214c001cbacb31a61900023fa1f644c5200063ec08ecaa26400cbf87592210c04997880bb086108029d21954c8510006ec31ae018a8000e3f64552214c001f2f02a18861084e3f61f62d85430072f3acc61088000b9d821c54310c015f301ba6c090803ae9d143580210275b3a08730c400acbe7498c2190001d3ec999064980023f60276d093105f7210ac4a062011cdf7098d211004b97b0d3a04218002bda1b43085100047e43ac690880008ff865c0430c801b390939843200838f191544c52006ef5312e01086000b6e821cd5448001d74e032042980778fe1964552320063fb2ae43226000a7d861c1540c801f2a8621e42908039b55062d0910004bfc3aa81086000d6f429c863550018fecab968298073e59c54310f1010f1e322a998a4000cf9645c0218c0014f90caa0c2980029fa1b548853007e3eaa6ec9968200c7d821d95444001d6b02320c298002b7a0c74580320063fb2ae19922032e9e6150c43c800157b0f320421809f8f19354885300063fb2ae22126006d3c74551204404df2ce2a1886908029f61464d8d100047ec34e598c8000e7585190614c8118fea93b68298003c71954310d210c65ec22ec1088000a7d8510d62cc401abaeb990649800357d5073484300056ec00c6a1a4200c7f619cf62550019bee739ac1a08023f61f42583310055f414e3b226000e5d8598d30c400f9b9073b04298003b6d0d43580210066f300e69086000e3f85d90614c0019dc43bb242200031fd0e76d5121006eda02e610a8000c7f85dd9320c8018f8e932ac198803379da43cc9310071e322a9b126026e3e85991210c0011fb0e21cc508003979cc63189540066e39ec4a026000ddb635c031500014f90caa0c09080
  | 28 => 0x49cc424c001c7ee3b28c89806fe39c94310f200765eb82c99086000e5f5418f32500018feecb2a61900031f19570191210c67cc02ec1088016cf47118d20440012f90cbae829804b760c170885300071fc2ec890a60009dc835c3424c001cb8ca31c8690803a72077650c430bd6f400e13184200a7c86551324400157d033b0c8980033b88776484300be6f41aec10c6000db421dd130c40014fb0832ec090802b761d63084401271f428c810a60008fe8710d620c0015f30021ec4880931fd5176084400be6f434e620a6008db8645c0414c0019bce6b1885100031fdd871553300053ec36a9218420d9fb865c02110001be702b8086880031f6167690d310065ec0ceda1a8007ed42198d30c4001aeaa8b886520802b7a0c74583320066f438c69824026c7d54dd92110001d3a8738ac0218a32f61c64c85300073cc00c6302a800e9d435c96010c01d5d04320c498003a71936310d100f79da02a818c8000cdc7498d30c8001d5e4332442180038fd9354c85300063f3b6cb21a4200cbf711c5640c021c7cc8aa665190227e60273d894000676b22e418e4012cbd70992210c011978c93b68298003979d563084400053ec2886b0e4000c7e761944348401b3c613a042980031f5d9548c720006bcaa2e010a6000cde76ccb31500013df0cb908790002bee0143989100065fc0ceda1a8011cdf7058d211001baf2cab8042180029f21954d89300076d39a86b004200c7d755c86350049c78c8aa0429805e3fa1873481100056ec26e13184200d9f8750c43884012f90eaa243180023fe1d63107200f5cfc30e2a188625cbc641cd404800197b0fb2442980023f6007358a411371f428c890a6000eac6418a214c0011fb013b686908231fd5276d09300067dbb0429806000c7e7655031500011fb0fa1ac0108033760d76086300447ec3ec998a6000d7554dc12108401d9c42b1a4220002b7a0c64d8d200047ec00eca1a4200e3c6455363480019dae8b1064188033d9cf21d81210053f432a9b024200d78855c0315000197aeca1886108377a58970084300057b41c8430a641b8fc8759163c80019bcc6b8686108031fe00765512100576c16c631280008ff87590320404b97e82bb684180029f61442583320063fa16ecaa64000d7b855c0315000197ce2b2684180032fd9273109300063e204edaa2420dbf08050c21440015bb0d9966220003abc8764085300071fc2ec9b126000cbf829db43500319da42bb042200032e591700c8300064f438c6a1a8000add821c663100011fb0f21ec0908933750d76d0c210e69e3a2a898620008ff865c0428c437a7b0a3a261900023fe19701083100778c08e8b004200abc815cb644c0019b8e6b1c42200038f5d7640c9300063ec00ecaa264008fd8798c21d000197ec8b8886980032f9d864885300063
  | 29 => 0x1863180031f597714cb400063f3b0ca2126027e9e6150c43084014fb0a326c298002bb60a431893002dd7420c7212400097f8755320480019bce6b1882100023fa1f63485400056ec0ee4b18800bdb6841c532500014f90caa242980029f2195408530006773a4c59906006d79545c043440015f50f21ac0108029f6126598f2008d7c40286b0e4000e9d431c96010c01c7f0bb204298003b520563c84400063ec20ecaa24211cbd70991210c0019ece8b086218062bea127458021005cf410e2a188600cbe76d90214c02d97e82bb082180033e59170085300071e322a8312601cdb6811d130c40015bb02394c620003b350d620c831046aeaa4e7a0a6000eb764484214c001c7ceab2042180033bdd9644c8320063f3b2a918a8038e3c641c5544c0016bb06382a9990029f6144358432006cf39c8610c801cc7d545d843c40019bce3b1e64a00027ba1a7210d200072fbacc69088000e7b80553604c82397ee0b2242180cbc75954310c210757d40086b064208cbe645c24308401ceec8aa0c2990034fd9674085301375b408c890a6000c7e7499663c8021cdaa931664200031f9db65c85300047fc02ed1908200c7c87553604c851c7b0a32642980031fe1676109300063ec2aed98c400dcf5105d821100015eb03314c3218032f9c464d8930004be43aa8986200097d87194214c00197f03bb2862187f4f9d154cc8200067dbb6829806000e9c6418c4344039b6b023a261880031fe14764c9100065e324e598a60079be849cb414c0498faa8bb086108025de057218d540063ebaec3a026008cbe74d93324c001b7486b8042200633ee19700c6400047ec30e6a062000c7e76194214c065f2862a1886108023f61c4398a500067d322e0108601cc7d545db43c40018f909bb2a9988eb8f99370553320066fbb0869906400c7565dc532d0011abaa939e84980035e551700c9400463faa4ec20a600097e87d5121cc0175ed03b1ec2a0003b598c31c844004ef810ae018e6000a3d8499664cc401d6ec998e4298003ad19361085300065fc22e13188418cf6815d82110001af220b80c6aa0031f9d365d89300053b432a9b0a64009fa87085300c0018f90ab84c7a083f1f5527610d320075d21a86b004200af581188614c04dd6b0232242980021f21d54586320066fb24e610a6000cfa645c021cc0014fb0c3aa42180037650d7008730006dbba642982201bd6d545c841c804b8fea839ac021003b518e43c85210465f322e12186400e6d5418920440011fd0f31a86908033761a73086400066f39ec7a0a4000df3615c0214c0014fd0daa286908025f21d544c83200637c2eec9906425abf87590420c0019bcc6b8087900038f19365d09300063e3a8e8b066400cbe71d90424c0018ff0abb465208031f59570cc8320766eb82c79088008d9c6
  | 30 => 0xca311278f3aa862184200dd8835c0214c001c7f0bb20c498022af211624c110005ddc22619024000a7d8018c625503797ce8b246390003a718d434854008736aa4e7310801bcbd861d130c801b9f060bb0431800b2f19073509300056ec1ce9b024200abd8690f21100015bd08384c610853ad5d243185320074ea1887b0a400dcbf405d821900015eb0c18e42200021fe1d650cb400047ec3ec610a8000eb621990210c0010ff0cba887900031fd9572d85300066e380c6a1a42008fd8718f41480199eb0c38a65a00032f1cc64885300047ec30e6aa64000e9f31d90314c001d3ac931887900372fdc264084300065e320e4a8a600097f8755032c40275ed03b16c2a1802b7a1a43cc9300074eb1c871088000e5d8518d30480095eb0e21cc3100029d21954185320057a4324210a6000cdf83dd943084018faecaa065880032fe1276085300063eb2ae198e8000c7d855d843084015b908b84c6108038fa1564084300065f40eeca188600c7d655c2640c8010f90eaa2c7908023fa1a72cc54008c7ec38c7b024228e9e7650c43c84011ff00bb686108031f99673993200055fc22e031a4200a7d85dcf60484018facab8c65a00031f9d86510d100047fc3a84b006400c7f76551210c0014fb0b322c0190038f19464c85300072fb2ec721a42009dd801cd218c001d730839ac0108232f19276d09300067d426ec9004000cbc645c3214c0019bd06bb042200035e551700c6400ff1fa1aa831280008fe87d9121cc0014ff0caa2c1988031f59571ccb400465ec34e810a6000c7d759d06348001a78ea3a243200031f1d9544c94003f7210ac49862000cbc76d93214c00badaa93908690003b558c31c84401471f322a990860008fc865ca3150001c78c9b2884980563fa1e6350e210073caa4e8b004200c7e76d503250001c7e83b2e8498002be20d7458021004bfc3aa81928026f1e7550c434841b97a80bb042200031fa157610c210055ec3686b0c8600a7d8519360484013f30039262a0003cbd91548c9200047ec3884b046200d9e409cc21500019bce2b1e6420003375cc73580210063ec00ecaa260008ff8750f60484019b8c6b8664a00021f21d5458d1013fcab8a8621c42009dd869cc2110027bc842b90c2a181b2f618744c110004bfc3aa81946200cde7118f32500235f500326c0908026f21974085300067abb6621088000adf8758f3110051f1ce4a188790802bba0b63d894002ebcaa2e021a4000c7f76595430c84b97ce8b2642180033b9cb62d85400063fbaac49822002ead82190324c00b97d0c3a260900039e55243580210de9f3a2a818e40298fe869cf424c0013bf0039a431806f5b5517210f200065f3b6c82126000a7d86551600c8011fd0f21ac1908031f21076551300065fba4c8b006400e3e85591210c0017ab022
  | 31 => 0x420dced825d8211000187eca3a2608800376a0d70086300063ebb2a9196200ddba405c021d00011ff0eb2463900023f600735864205ef210ae418a801bc7d545d843c80011fd0d3b242a0042e7e1b7250c430047fc32e22106000e3d75d93314c0015dd05b26c4980031fa0076551210065fba2c49862000c7e7619643484018f903bb2a8190035799673087401374f3b28621a4200a7c86550624c0018feec38aa8190971fd50735834200676b90c430a8000c7d7558f42c80014fb0ba1ac1908038f9d464085300447ec34e7a146007af68110f614c001cf2a83a2c0108038fdd564484300065fb22e39926000cbe769c4644c00157b0439ac8180035e19570109300e65f3a2c819620088fd87d93324c0014fb0daa442180031f21776484300f71ec28c818a6012e9f30592210c0015db0221ac4180038fd915418d200076b31e43986201ecbd87190314c0010f90eaa2c3180032fa1f64c8530006dcba2e01928000c7d65dc132d04018fec6b90c6aa09fc75d54310e210063e3b0e2aa26000afb845cd60084179f0eca0260880831f5527610d3101736aa0e6b108000adf8758e4308401bb48139842200033e5cc73580210071e32ae432260008fe87d8d4148001d38c6a1842a00972f9d1640c4300066f41aec1908021e5d5458f311001d9bee131e42200031f5957110c30006ddb22e0212600ecdf7058f2110011978c93b0829800277a1a73d05301165f3a2c998c4000cf9635c021900531fd0f21ac19880337d9273086300075ab2063908600cafb805d1600c401bd704b80869001b1fd527610d100074fc328621e4200c7d851d9315000157b03396c8980033e591700c4300073bb2ec390a6026cdd439db434842397ae532442180032f9d86490530005bdc2a609022000cbe76192424c045978c9b9280980031fd0476551300fc7e43ac4a062000abe86d0e21500012f90eaa2c199002db60871552320066f426ec99064158ff865d332cc401978c9b8242980031f185731895414e5f3a2c81946000aed8018932504019dd04bb0421804f3720f7650c210072e3a6a93184200cdc73d0d62440011fd0fa1ac58800337613764c8320065f3b2e23226000abd87590210c0017e30198e439800397550638c540005b6c32a899640008fc8758930440019bf0eb1a42200373e1917008430006ddc22e018a800097f87550320400d97ce9b20c6880032f1db64885300ae7c3b6869022000d5d541cd218c0018f8863b2a8880031f9d165ccb310465f3a6c998a6018cfb865c0219001f978c8b9486980a74f9d354086300065ec3ec818a6021cbc7459160cc4015f300318c090826bee0173580410063f410ecaa26000e79851cd60084019f2c8b804398002be6004258031006afaa4e610a80008fe861c931500018fce8b2e641800b2f991740
  | 32 => 0x137d0e21a4320003b598f214844000677312e19968200cfa635c021d00015bb0f3184220003e550c43484210074fb26c621a20008fe869cc31500018f8833b6a898002be60232582410063eb2ae132662008fc8750960cc4011bb0d3984220093ced0154086400065e3b68690a8000e5f7558d21100019f0c6b8042a0002bea1f43580210957d40087b122000c7d841d9544c8012fb0e32e86908031f9db54087300072eaa4e13184208d3e859d0214c00f97e833b08298002bea0f74580210043e43aa8b06641ecbe74590320c43dceaa8b0862200377c985700844000774412e8b004200abf815cb644c001d5ec9b10429802779085721873003d7b40886b066200c9f649cc214c05797ce8b2065280032f5d843086401478e21ea8a1e4210cbe645d3320c8019f6c8b8043980023f61a731081012e5f3a2c8908600ad9c7450d21cc0011ff0eb2664180033710073589100066f39a863122000c7f635c36255001cb8eb31a4220037768c17008730125cfc3a862184200cf781dd9210c0139f50cb8042980023f21970d093100778c08e6b004200e5e7598f430841d97ee0b2642180175b55272d0d200571e322a99824000cbd645c8410c00b8faa8b84c5a0802be60043580310065f43ec910a600bbd4814cb315000b97b0c3a2609000337213764c83203e5fa0ced20a6000cdc7358c21100012fd0faa243180039755063d0d100165e3a2c89906410e5d54dc96310035978c9b8a8098003378c473583410066e21aed21842009bf8750c438841b97ce332442180035759673084400067db1ae010a8000af6840ca6188001da8c621842880029f61743d81210063ec2aed9888008c7f545c263d0811a78c8bae84980031f9d9548c9400074f39ac8108600ddf1615c0211000173b023928621803ada0764185300065f204ec10a8000c7c84dd9540c801d3f05bb286218039ea1443580210569ec2ce810e6032e9f6250c43c40015bd0f31a86108031f20c76551100057ac1086b086000c7c8755162440015f108b9ac0108473d20776484300267a30ae221a6000e3d85190614c0015bf08b84c610802bd61831c86401379da02a890c8000dae629d0210c001a7ae8aa4641880b1f551760c8410057cc1ce8b004200add8098d430843973f0ea1887880373e99170087400063eaa2e131a4200c7f859d8324c0019bb0c39a431805b3da057608430087c6b16e4a188629cbe74590218c0018facab9663a0002b760b7198c40004fcc04e598a6014ee42190d62c40011ff0eb20421809fc710d5450e21135cfc3a8621a42009f9801cf21900018fb0abb687900023f61c43189100072eaa2e9318421bcbc7459132c80013bf0d39842200025f61c6510d210057d41ce8b004200e3c6419443440011ff0eb1843200732fa18744c31008d7d406c9b02
  | 33 => 0x1800400600100000dc054007039853400a073012822000c03e061801c000022048321800c000007017000000800380f404e00500280d800400b015801000001a00000000bc000000034c0e800200301e401a00100600d0d8400e0cd000000e000001804400001b009009001a00602a8014000003018003817400100005f000a1d000282a406003b00c8000000054000000417c14400280e8058015010002800007500586b000e0020b402ec000002010822400058904581a40860010050068000036042811c0000002060000022007000801000400e035002801800003c800000600300001bc1b80000030ba804001000000bc01802500480b002000800c80100060000020000122005016001401e087010000000207300f8014000005003837012001600000f03cc01504d8a3801e00c02902e802a00d000000506096000c0228346003001003c01205800a800806200300c80140021b9008823400013200100e006800500103f002800e037004800400e000001802009c003000002409f002000803601b0018394004002000000400401b00492fc00001d00f804c01001500a018c0020c20e9012407003c000006804c02a533801c0000020000198196055546003800004000f800027c03e0038040096006000001c00601f47d001801000101281bc000003000009009201d00080602e00520c2000000407701c80ec00a01a008802800000000881541f84a7009800400801300180040700090ca9d2803601c00680600000140180000010033032015000a000000005423000f0008050042009004802c03202a001001000a00700000dc0362850300000238000000001001c02d001800c058028012029c02200e000000000003400001ac00c0690048001a0a01b003001000200706c85a4004023001012800c21300501f404c00301800240140821290028006000044005401200c000000000400f022800805801b0000010a9a016035837400600c000000400001a00089381e00d0007000800403700580080000f70048028042003017800803403a00930f400000001a00000ca179008807c0000220063f418ecaa22000aec825c56010c018f8ec392a899002af61373d81210065e40eeca1886008ff865c8310c065f1e42a188610802e72194310d100072eb98c6312a800e7554908614c8014ff0caa285988232fd0676d0930005b7c32a89964000c7e769d432d00013bd0639282980176ba08744c1200469f3a2a810a6000dad629d0210c001d38c921ec29800397d946350d210074eb20869966213cf910dd943c40279f0eca1a4088003379cf63d81210056cc18e8b004206f967150c43440018fe87bb2a9900023fa1c63481100063fa1aedaa04209cf876cc1204404b978e8b204218003ad19031c85300075690ec810a60008fe869ce21500
  | 34 => 0x90a380000ce00601a0250022034000018003000100082f800203b02081f001804d04481b400806501a80d4022003002000c02a03a0088074076001004000804406b00080b004c0000118000006000003013800400200e82412f001b00a80300d600b00780d800000705e800413600d000823c06c0190a6800401600c00780000ea30d008005801c003008000400026f000000c06e006000001405200a004800029c03a009800400e00101a006400c00600f001800000e00c80002880020d200b00eaa0300400200100630010038024000007024400e000020800000c2e200080280a800000081700100020258144000000009802c03009b001005c0140050058068006006000000037801b007002c000000000000000000a00201dc0e623600300000840000018008000185000001803200402886ec5de07100100100100060000014000054004011402000000200b400600000000300480fc002003001003215782a400000a008008400002c000800800c00606083940000120000014118727010002c006001000004801e0110a6800000a05a002800004c00000180a001c07000282301d0002024801400400d022803c004042005807003e12a006803400002a00a80fc00e0040050074022009002001c00000101585ec00e025010803000000007198e40060020008038018009003800400c050001009c0020b1000004c01a030001000009802c01f0000000000007802402406f0aa80380ca01c010000800400c001835400a00b000004007420e002801401c01600000a50ee922000005496200b0060000000011000001814a00100482800001a201d8024016032000004c000000012007c01402f04c806800009203e05500cc00700a80b000e00100100a0a24037040800c04e00000f00d80a004a00001280300000738020002389003005803605b024800008c017000002000e00f02500b014a00200501b808013500000000000000000254026009044820000600001d007002601300b015800200100f029800a0310200ab803e0480ce800000c04119e000c0900680820194016000080806801e01e05f809004e0020f9812c000229003002802a001042000c01002b01e801001a0bc001801008801602202d007a00000800500103a500100080023890000024404010003812801000000a00a80980a8000001403c022029000008c000006000001e002000000011a00004000100380011d1800c0002a503b071022404d0260f340060120000008000005000028013a001001802800612c000000007c0a7000800002000f002000000002100880440120410058054030020000000000c0c10318008088005027002004e001000806c00a00800e801c026016000001c0002af003808000000a04e8088018011001000800200300800040081100
  | 35 => 0x3e006093002003003e01d009c24c00b00902cc01c00505c800006c5ba033008804a00000f00140400a900b017800202301c003001200a00681d000004100d005006a021006003007811800500040061cb12200fc02e00e000008000400201b852c0020190a100b001c03a000006000406e001803400802b001002000200600080a000e010002803400000b000802c01203400000140180670c80000012002007800005200900a810000400012f000801e266000013c072132002000400e00404988a800e00b001000008400e00c000405617200700480be0a101f001402e00f003807c00609e02f802000a01e02081c836a00a003000400000401380000c200a00304e00200430110008000001000004c082143002000002033903300a401c0e8005805803a00500500b000001000000b0006002007801808c002001003001c002004001001808700b802025400a000817c0140f4018000000003c033004c03a00400f01dc01203100000240d000000702c809c00b04a801000400d35680040ae007000000402604100200040080220398008174009000031c03a027096000003001300208a003e004006010003a00000000002c4001002000009a00000001c000c24e006000000c03a000017c006007003801400e00000080f800601b00600000241db034800000200802580a000200200400720be02403a002c04201304a000c00e00600080086700140028038000003030801000000300280000ae0bf060004c00000000000004ca005001963011a00b00f000000a007000809804404f56b004003c002007067000c6c4039000000000000180dc04a0631a7007405000100d801803200400280ec008010071121c00000100180b4000000042006c00a00100200000bc0030198128000000000002000200304400281a2000002004c000016001000010600f001801c0000a3042800c0840ea00100000a200a0218044
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x4010bf985d074580210052e64271593420c0018ad8658a74084300042fe6276d0c215000107f97600631895400497a63545c26308401c1e745d66308440007265cd70d90214c00149e9619273085300041fa6276552324800145d961d473484300070ed91545c0214c0014789058d7218d540051b64841dd954c800183f879d4640853000707190659cc414c00183c642197510930007165d57098c21100014d9909c563cc8400060f19187d50214c037a9b8050d72580430051725d5418d3250001c3b65191700853000627e61741d2630840189f875cc64085300041fa63431d9544840143f945d67418d2000696a15831d1600840143f985d464085300050fa5e85591210c00183f87d915418d2000536e59835c0210c00127a98d5173580210060f61c65d90214c00162e921c765191300042fe61741d3604840187876600715513000437e59801cd210c00145c97550634c11000627d038758c211000107e98d517098c21005666407350d215000149d961ce43484400062761d7498c211000143e9721764485300050fe51759d263c4001c1d755cf64085300070e5d570590210c001ae08120973580211ce276617650c4308401c2c6455272cc5200043ea60409d8215000183e64a1f544843000617e0e831d9544400117898551700c640006279d18798c211000183e85a117608430004ae2617450d60084014af9260676d0d4000707257649cc214c001a1f845517098c210062d619619d0210c001a598560c74580210052b65c64d88214c0016d1900c46308540005a364b81dd94310c0107e9810676d51300051e640431d95444001a9a7460c745802100687e17845c2630840183c74e19545803200726592835c0210c00183d87d9464085300060fe56869d0214c00183f87d91540c9300072559073c85210c001a3a95a10735802100437a60309d8214c00183e64e1d540cb100058e64071d94644c00183f8761564084300060f9d38655263c800107e9621d5448530007265d17098c2110001a38852117358021006a559083484210c00129d96a0b7150c430062e21b645c0214c00185f879d563084400063661d7058c211000145f9360076551210041fa63545c063484014759218d71181540061d5d7815c8635500183c64e1d54c812000627e1e73990210c00107e9810e76d51210051725d5498d30c40018d78798d21084400047ce5d8010c2144001c968418c714c94000627192831c9414c0012b9981d043580210051ba4a605c8635500189c84e1d6308440007076547498d30c800189d84a0d76084300051de59541c5320c80183d87217640853000517e5d5418e31500018ad87484640853000635985869cc21100014799010a76d513000715550631c53250001c1c74dd56348440006275d1801d26308401c39955917008430
  | 1 => 0x60f214845c2630840183c74e19544c3200041f2617558b4044073c96215d94310c210062d61c31190214c00169990a077650c430050f65f64d50214c00183c84d957018d210051764c40dd9540c801c3864d957010d1000527e417650c4308401c1c959d94310d210062e1db844c12044001ae281a0b4358021006a650d8010d6008401a3a85a1073580210050fe5d6455232c4001c1e749d56308440006271d283989304400187a98dd95448020005a624d7450d600840149d969ce430844000527a5b8750c43484014ba9621170085400068ee57845cd600840186f766087355320005b16483198c21100018bb875c264084300049de61540ca618800145d96d527308430006a650d8010f624400185f54e1e63084400060f21375589304400189e8750c43587200062de1e64484210c00145f965527308440005366408758c21100015369420d7118154005a964831590210c0014b5971933108530006b2a0d821d16008401c9a735c2640843000707a55649cc210c00149f94618734863000526259435c043440014d693990714cb200070e190655c0424c00143f946007655121007169d57058c2110001a7185604735802100527e5d4310e624400185d875d663084400070e257645c0214c001c998458d70084400051ee41831d95444001ac983a087458021006aca11811cd600840183d875d764085300060f19387550324800117898551700c5400041fa63431d9544400107d98d5273d8121007079d673190214c00107e9621d544c9100051b64843dd954c8001ca4211d1624c310006a3e0a82dd94310c0183e87d935448530006a650d8010d608840165a931d3545802100517a4c419db544c00189e8750c435891000527a4c621d130c400145e93d087655130006175538758c211000189c845d17098c2100527e51869cc215000189d862127308440004a7e61439c96010c0149e9718d43485400050f66375191214c00183f8659674084301cf23c857650c430840143d94a0c76551210060f190865d7424c0010df985cc7358341007269c273990210c001ce061189700853000716d50635c0315000149c9750c435891000636e1d7098c2110001c95911d0634c1100060fa1b659d0214c001a1d84d507098c210051b249635c8635500189f7420d624c11000707593549cc210c001a1e956107098c210052b64b81dd94310c014799010e76d51100070e656645c0210c00183f87d9154085300060f61d75190214c0018e421e19720c4300058e64072194644c01b4b996d0d70087400062761e73990210c001c1c6419673109300442f663649cd214c00183c6421d544c12000627cc387590210c00183f875d564084300041f660405db5408439a9b8050d71580430071c640635c4605500129f966087150c43006ac213815cd6008
  | 2 => 0x840127b9855073580210052be5d21990210c0018d5870c4630854000566650835c021cc001a3884d5173580211cf234857650c43084010fb98dd8214c03000627e538758c2110001cab6418970085300fd0fe5d6455332080014d9901c4634c94000726190635c0434400146d94e17764c8320060fe1f645533148001c9a735c3640853000517a4c405db54084012bb9850c43580210070b1d154189204400183f86dd15458032005a62517390d600840183e7461b5408430004aee61741d1600840125d98d507098c210060f190865d7414c001c3a95591700843000707a5376551320c80143d97e1764cc530006aaa11821cd60084010f596a0f7048421006a6612731cd600840189c43e1d630844000527a617650c430840162d921c465191300041fa6343dd954c8001c1e955907348430005a6e614310d600840143f9759354084300042fa62419db414c0018b787d91210853000716d52635c021100010bd9819272d853000635e19619cc2110001599901ce434864000707191549cc214c001a99702194310d10006a350c825c56010c01c595458d700844000627591809cc210c00143d941d474580310041f25d8510d62440010dc989d943085300060fa5587190214c00146c92604765513000786a154310d600840189d8750c43580210051e640421d9544c00183f875d664084300062e61d70990210c00183d8759354084300051765f5498c43c8001a958650c43484210041f2607655132440012db9850c43580210041f261545c2630840147691e0f7655320006a55c48650c434400189d7460c74580210041fe6076d51214c001a994360043589101cca765f8650c4308401279989d3545802100726591835c0210c00107e9721954485300070e9d570190214c0012ba989d14358021006aca06841cd6008401c1c64d96731053000687214845c26308401c1c64d96731093000517a4c411d9544c001a3a84d5073580210060f25587d90214c001cb061d91700853000633619629cc211000183d87d97640853000517a4f419db544c00143d9719764085300052b65f64d88214c001d89432097010d2004527a4e87d90214c0010f6985d921084400041f65e83d886055001c1e9519273085300061761b549cc211000107c985d9548cb100069a615821cd600840107d9810d76d50210051da60635c46055001c1d651d2634c32000627611701c26308401a9b9850c43580210068ee17845cd600840183c84e157098f420058e64072d94644c001c3964d51700843000633e1a629cc211000183c87991545833200707593541cd210c0014b9909c464cc9300063361a629cc2110001a6b85e0973580210043ee61741d1600840145c97550634c1200061de06811d9544c00143d97a156408430006a650d8010d60c8401c9a739c3640853
  | 3 => 0x2100627e1d7458c211000189c7420d624c110006279d38758c211000146d92103765503200687213545c26308401c95435c4715804300527e59309d0210c001c1e76d954310d2100627e1f8650c430840183e74e1954084300041fe6154dc1628c401a8d43e09715804300617e0e831d954484018cf8658a73084400051ee59545c0210c001479901857318154006a661d4310d600840183c841957018d210050f25975190214c00145e939857318954006275038758c211000183d861d075484400060f61f85d90214c00107e981d9544c5200060f6107499560cc40183d8719065d05300068e654845cd60084014af974876408530004a765c8650c43440018af8658a740843019527a5383dd94308401c9a745c2630844000726191435c0214c001a997460c745802100734600631c53250001ad281a0c7458021006b860981d0d6008401c1c65d92730853000437663435da430840107c985d9548c8310070e25376551200802149e9720b7650c430050fa5f85d91214c0016c5920c463085400051da4f625c4605500143d9721764085300060fa5787590210c001c39755c2640843006d36259435c0214c00149c989d94310d210052765b849cc21100018da70e1d630844000687654845c26308401c1c741d563484400051b25d541893250401aa884e0973580210060f19387550214c00143d97e1764085300070ea54645c0214c0118b886d9170105300070e191545c0214c001c1c6419673d0530006b260d821d1600840189d845cc73580210051ee59545c0211000183c6421975105300042fa617650c4308401c1d759cf6408530007075d573190214c001c1e959927308430007265cd70190214c00145c97552634c3200041fa6176550210c0018b88619170085300063661d7098c21100010ee9808776484400041f261545c263c840145d9310276d51210068710c8655143484014b990a077650c430060fe1e85590210c001c1d9519273085300062761d73190214c07389d84a0d7690c21004b524d80108614c801a1c64a0c72551300060f9d086553324400107e98103765503200627619309d0210c0019d030a1c214c1100059524d80553614c801659931d354580210062de19619d0210c00107c985517098d200060f19387550324c0018d4819d932cc5400050f653751d1600c40149d96e1d4310c210062d985869d0210c00147996d5170084300060fa55869d0210c00185f86996730844000517a4c421d9544c00183d879d464085300060f61a659d0210c001cc66198a73084400061761a659cc2110001a698560874580210072cd93615c0214c00107d9621d544843000786d514310d60084010bf985d074580310042fe61741d160cc801ad28360474580211cd27652835d843084018e42121d624c3100051e64076194434
  | 4 => 0x4c001a3864600715513000687217845c263084016a5920c764085300051765c6518c4344001c1f64d527308530197a10854310d62c40016c592206630844000707a557650c430840149d9310076485400051765b549cc2110001a3984d507358021007265cd70590210c001a3b845517358021006a56194310f3108401c9a745c163084400051d245625cc6255001c99745c163084400060f61e75d90214c00149e9499273085300042f26276508424c001ab28161073580210060f61c64197424c00189d30e1d6408430006a6611731cd6008473c97105d94310c21005a664c7490d600840145c93589731895400627e1e73190214c00189d875cf64085300060fe14849d8214c0010dd9810073589100062e1d8844c12044001c9a739c06408530005b164831d8c2150001ab081e117358021006a6e1d4310d600840143e971976448530007071d15418d3044001c3865d9170085300051e640811d9544c0018bb879c064085300061d20d811d95444001c9a8458d7008440005a3a4b81dd94310c01c35655867408430006a59c48650c43440018bb875c064085300050fe61651d130c800143f976156408430197251c56410d32cc4010bd989c764d893000635619619cc2110001c39755c364085300060f99087551210c001a2c64a08735512000437e59809cc210c00127b98550435802100437e61731cd6010401aa984a0873580210068710d86d5143084010bf985d0745833100627192831c9544c001c3a959917008430007866154310d60084010be96e1d421093000517a4f411d9544c00183c64a1f54485300070edd1549d16008401c4d6558a7308440006879d78650c430846589c97e194310c2100635e1d634842110001476912037655032006aa611821cd6008401c559518c714c9400042fa6074589304400183d87e17640c5300462e21b645c0424c0012b998dd043580210060f61c64194424c0110bd981cf64085300068ea55841cd6008401c1d7519332cc53000527e59435c0430840189d84dce73d812100725a447418d3044001c1e759cd640843000437e61731cd600840146c925d57218d540052e64287d90214c00189d86d02730844000687a56841c2630840149c935d074580311cf250c57650c430840162d921c76519130005a964831990210c00189d875cd640843000636e1d7058c2110001c399519170085300068ea15841cd60084012789855173580210060f61074995600c801d1954d02730864000707993549cc210c00183e8419673d81210042f6617690c211000126f9855062509310072658c435c02110001d9143e057010d100062764d87190214c0010bd96e1d4310c210060f21d64551210c00189f875cf6408530006b8a06821cd600840189f8718d43085400072618d435c02150001ad18360474580
  | 5 => 0x5300051ea5b545c0214c06549c985d94310c210051be49811d9544c0018e421a1f4358b100068e655841cd600840183f86996740843000617619549cc211000147996d517008440005ac64031590210c00183e742195418d1000497261545c2630840189c6461e43085300051b648639c86055001c59755c1630844000437a6043dd943084014da9620d700853019627a0f7690d4308401ca66198a74084300043ba6021dd9210c00107c989d954cc530006ace13815cd6008401c1d955d94310c210042fa60411d9414c00189d879cc64085300062d61c61190214c00189c64e1d430853000566259435c0434403b43f9759154cca32006875d78650c430840107f989db5408530006b4a05831d16008401c3b405d954086400060fe1b7455160cc401a5954a0c74580210056664c845c021d000183f875d4640853000696616831d1600840129f966047250c430068ee14845cd6008401c9576e054310c2100627e5f8650c4308401ab16460031c84300041f65c86550214c00189d86502730844000627e1e73d90214c00189f8650d7010c21006a35cb8650c43c80012db985cc73580210060f655869d0210c0018b78719121085300069c615811d16008401aab8420973580210072350d721c96010c010df985cc7358042007079d27598c2110001a398455073580210052764c409d821500010ef985c872580430060f1d186551600c80107f98ddb544843000527650301d9214c00107f9760863181540060fe1e75590210c00189f875cd64084300052ba4b81dd94310c0145c9360076551210060f99187d50210c001c1c64d9673d05300062b1d0825c56010c0143d941d47458332006ac611811cd6008401c556558673084400060f21f64551214c0014799010676d51300060f6127499663c8001c1d951d0634c1100069a61582d0d600840149d9718d43085400050f65f85d90324c001c5a755c2630844000527251801cd6244001c986450d70087300060f65587190214c001ce362d8570085300041f660639c8605500189d8758e43084400060fe1c6455063480014cf97485630844000707dd564dcd210c00189d8750c431891000617e1d7558c2110001a1f84d517098c210070b595629d0210c00183e74e1954ccb2000627a1d4310f604840549e97e0b7650c430071cd97615c0214c00107e9810e76d511000627a4d87190214c001c1f65d927308530007269cd70190214c001c3a64d5170084300043da6176484210c00143f97591540c42000635204734c960d040125d98d5063cc9400064ed03875502190001c958418c714c9400050f65c65190214c001c1c43ddb5450c210046d66074085304400189c8650d7010d2100627a617650c4308401c3a755c164084300051764e74d97604844349e972077650c4300517a5b549cc21
  | 6 => 0x110001c1e759ce640843006eb8609811cd600840149c9750c43582210041f25d8655132cc40107d98d5073580210051764c401d9544840189f7460e74d81210043ee61731cd60084014ac9260676d0d4000687e14845c2630840189c9461a730844000517a4c401d954484016c59220563084400051d245821d9544c00107c985517018d210062ee1d70d90214c00107c981d954485300060f65787590210c00183e74219540c5300052765273d8f604840149f9758e43084400060f9938755320c40010f7985c471580430041f66176d50210c00183e875935448430134a766364d8d4348401c1f435d95490c210060fe1e75990210c001c1c6519273085300042f66062dd130c40018ac74e0971580430041f26176550310800129c9850d715804300687211545c263084015999420d70085300050fa5376dd5214c00149c935d074583320058ba4871194644c0012bb9461d435802100527e59409cc21100018b9875c0640853000627e1d73990210c001c1f95d9273085300850fe5974553328c80143f975915408430004b6a4c8710d600840129f97e194310c2100617d538758c211000183f852117098c2100639087865c831100018bb76a10214c0300070e190655c0414c00183c95a1a74085300060fe1d64550210c001a3a8455073580210072c193615c0214c00107e985d954cc62000437e61741d2630840145d97d526310c210450f65f64550314c0014ad971906208530197a10854310d620c43b43f965d1548c8310050f25d85591210c001c595498d70084400041fa60401d95448401c1c7559073484300041fa60615cc625500189e8750c4358b100041f26376551210c001c3b65d9170085300060f9d286d50214c00185f879d663084400068e656841cd600840183f871946408530007079d17558c211000b43d97d91548c9200042fa63745893044001d91432057010d100060f61f64d50214c00145e939d065d81210062e61e70190214c001a3a9521173580210060fe1f64553314c00187476604705533200517a4c615cc6255001279981d3545802119527a4f84dd9430840183c746195458331007075d673190214c0011b598084744c3100070e591545c0210c0018ad8698a74084300041f26176553328400186c98dd9544c8320041f25d8655132c8001cab64d8970085300042f663649cb614c001636911c865191300060fe1f64550324800183e7421954cc930007075d573590210c001a366460470553320052be5d21190214c03d49e97e077650c43006a5e0681dd94310c01a1c95e117098c210050f65f64550214c00107c98595718cb400060f9d38655031c800145e93d0a76d51300062720c845c263084010df985cc73d81210442f66076d90214c00189d6460073484300068e616841cd6008401c3b64d517008
  | 7 => 0x84400062de1d64484210c0014ba96d0d7008540005a964831190214c001c3a755c264084300062e61d70590210c00185c7620d70551320060f61c6419743484018d58718c43085100051764c40dd954cc401c99735c2640843000527a5a849cc2150001b914360043c85100041f26276550214c00107e97219544c91000527a4c62dd130c400189d869ce4308440007251d06308530440010bd98188744c310006a39cb8650c43c8001c1c64d52730853000687a1365d8d43484019958750c4308510004aea508710d6008401c1e759cf640853000527658849cc211000145d9310176d50210041fa6040dd954cc40183f87d9464085300060f9908755130c4001c988418d700c5400042f65e86d0c215000146d92d0f76553200f50fe5d64552320c401c1c761954310d210060f619659d0210c001d8943e097010d200052e64071191524c0018b58718764085300069ce17815cd6008401c9a735c164084300068710e86d514348401c2e94dd9544c83206d3665a435c021cc04b4b99021d640843000527650309d8214c001c947418f214c110006279d18758c211000183c84e157098c4100707190659cf424c001a999321173580210070ee57645c0214c00149d909d94310d21004a765f8650c43c800145c9655273085300041fa60615cc6055001aaa84a0873580210072658e435c02110001c386519170085300041fa60429db544c00189d875ce64084300062761e73d90214c001c5b5458d70084400049e6635410d600840149e989d94310d210041fa5e8655132440014799010476551300060f1d086551204400183c64e1d54cc52002ea6601439c96010c01c9a709cd64084300070b65376551320c80107d9810d76d53200061726376551320c80189c64e1d43087300051da4440dd9540c8010be9810276085400041fa6276553324c40107d9819673d81210042f66271193624c00189c94e1d630844000707d947418d3044001c39755c0640853000517a5b439cc625500125d981d35498c2100627213745c26308401a595460c7458021004a7e5f8650c43c8001639901c4651913000627a1a73d0c2150001c1d75193320c930007079d86550c4348401c3564551710cb100060fe5587d90214c001c2e7455062cc9100052d65c64d84214c001635911c86519130005b16483158c2110001ca562586740843000627618439cc21100010dd9819273086300042f65e86190214c0015999321170085400060f21d6455160cc865b84216087150c4300437e61701c2630840da998050e71580430051765385dd9320c801a3884551735802100635987869cc2110001ad186cc4214c030004a7e5c8650c434400145e9310276d512100716214635c0315000189d879cd64084300068710f865514308401e195450c435802100437662869cc2
  | 8 => 0x214c0014db9650273084400060fe1d6455032c4001a3885e1173580210070765376551320c801c1f645527308530006aa210825cd6008401a3b84d51735802100726e10635c03150001aab84e0973580210045ea63545c031500018d57620d21084300041f26376551320c80107c985d954cc820006276187390d211000183e8619674085300042fe61741d1600c801c3a755c364085300060f61f85d93324c00185d8560d760844000725dd94310d2108401a1f95e117098c210041f26276550324c00189d875d163084400060f1d38655160cc40183d849d06518d1000731589619cc211000146d921037655331005a62517350d60084014b99690d700844000527e51801cd624400145d97d506310d100070e193545c0214c0014af9748564084300072664c645c0214c00145e9310a76d513000687d0f865524308401e1954d0e43580210052ee59845c02110001699931d043580210058d64472d94644c00143e9719464485300061761d7558c211000107c976144358332007071d15498d30c8001c1f959d94310d210062761b309d0210c00183c8521276085300050f663651d1304400183d871906510530006b418d800c72150001c986490d70085300051de45821d9544c00126c98551629083100617619659cc21100014b59719121085300062b61f21190214c01b4b89650d70085400070e193655c0414c0010df985cc73583420069c61581d0d600840189c64a0c72545300041fa60409db5448401c6b65d8970085300062e61d70d90214c0016949650c4308510006b8a06821d160084018b58788464085300068e257845cd600840183e74219540853000627a1d6390d211000189f879cd6408430004b62617350d6008401636911cb65191300041f6588755130c800189f875d263084400051e259545c0214c0014b597d9361085300060f61c641944344001aca83a087458021006279d38798c211000183f852117018d21007290877458930c400107e985d9540c81000707d94649cc214c0018da70e1e6308440197261d94310d204400187776a0470550320049e663541cd6008473c94815d94310c210052b65f64188214c001a1e84d507098c210068e615841cd600840146d9220c76551100060f616845d8210c0018b9879c3640853000696a16831d1600840185e85a0d7608440005a52594310f214400183c6421d544853000723a487498d30c800185c76a0c72551300060f61c65190214c001b914360043085100450f65f64553324c001ab08121173580210066c1028708540440018759721954c851000687a54845c2630840189c83e117098c210050fa5b75191214c00147796550714cb200060f214845c0634840189d86e12730844000627190835c2214c00107e985d9548c7200042fa6087590210c00189e8460d760
  | 9 => 0xdc00122000a500e000000200138e21bc0400180014676c1a000002000050000180b40d8140d8000ba00d2925d40487f09e0001e00c01e070340220140300004f03201041800092000019a900c0d8958000182391b8020000c40002d01201c030fa0720540103b060010310220200301a0030460000103b0740e8028021600000c801000014020460160188485f00c03006017006014350180400100d166006000bc80912202467063004009ef8090300101680000022878800000000020190280000180103801c18000020044000050000cc000240220040001e0480018f8010220a00000303a2f0018a9220400198090020002882e07038d268000020000f0170160244401904808c000720020bc0202b0040000981300200c000010084ac068270700000280905001009802014004118265b2048020a50380303d8bb00603403807000214000040081d00700905813c1b80310800419b3307a078038480081b80c804000011a10ad1aa7640000d00002c0980039a134041590240041c8940000a40288a1cc05c000030000000600000a0000300001a0180680e00401400005026014028e301007c001a90ba014010030008140200005e02c06820006014068040580780681c022000840960420100700103608802800034010038cf0020000105a1d859c57006002008040010022300080e00620832803030024930ad028038018bb875c164084300061b1d8825c5544c8018ba70e1d64084300061da0d811d954440012b990a067619130007075d074d52630840183c74219544c1100070710f765514308401c3a6455170084300060f99387550210c0010dd981c26350c210060f19387553314c0018af8698a740843006eb8609811d16008401c1d755ce6408430006a650d8010f614801149c9361f6448530007236487498d30c8001c1c64d9673d09300050f653751d160cc8018f176603310843000533e5d2198c211000107c97619544c8320072a193625c0
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x40d4a00100000000030000200002000409801100401862c3b24188c610a8000a1968883604765511000603f2ebaf0ca188610803891715c08650c434400190dcc30aa1886b00420081d2a19218d71181540055214ca1b002184288002c19a01d86550c4348401868c3b20188c610a8000a256a07418c214c110005323462050e10a8088003892715c08650c43440014c8d2061438429822000c2561c9650c430851000603d30caaeca188610802898a750d8010d608840190dcc2a8a1886b004200c2961d920c464085300051314ea1b0021ac4880031939750d8010c214400154853286c008790a2000a07a9c43e195450c2100483b53a1aecaa4861080241ea910f765514308401252d48423a2c49862000e246118018c714c940
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x58e
  | 2 => 0x3cd
  | 3 => 0x4d
  | 4 => 0x58a
  | 5 => 0x98d
  | 6 => 0x94d
  | 7 => 0x9ca
  | 8 => 0x9cd
  | 9 => 0x168a
  | 10 => 0x168d
  | 11 => 0xa0a
  | 12 => 0x180a
  | 13 => 0x209
  | 14 => 0x1549
  | 15 => 0xccd
  | 16 => 0x170d
  | 17 => 0xb09
  | 18 => 0x1409
  | 19 => 0xe8a
  | 20 => 0x178a
  | 21 => 0x18ca
  | 22 => 0xca
  | 23 => 0x12ca
  | 24 => 0x10a
  | 25 => 0x130a
  | 26 => 0x124d
  | 27 => 0x150d
  | 28 => 0x138d
  | 29 => 0x15cd
  | 30 => 0x24d
  | 31 => 0x8d
  | 32 => 0xb4d
  | 33 => 0x16cd
  | 34 => 0x128d
  | 35 => 0x144d
  | 36 => 0x20d
  | 37 => 0xcd
  | 38 => 0xb0d
  | 39 => 0x140d
  | 40 => 0x154d
  | 41 => 0x12cd
  | 42 => 0xa4d
  | 43 => 0x134d
  | 44 => 0xecd
  | 45 => 0x17cd
  | 46 => 0x44d
  | 47 => 0x1a0d
  | 48 => 0x5cd
  | 49 => 0x1a4d
  | 50 => 0xe8592
  | 51 => 0x19cd
  | 52 => 0xbcd
  | 53 => 0x14cd
  | 54 => 0xd4d
  | 55 => 0x164d
  | 56 => 0x2cd
  | 57 => 0x58e92
  | 58 => 0x198d
  | 59 => 0x14d
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 10 => 1
  | 9 => 52
  | 8 => 843
  | 7 => 4440
  | 6 => 4616
  | 5 => 1077
  | 4 => 26
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
  | 9 => 2*((h/38+packedAt gbK9 (1352+(h % 38)*6) 6) % 52)
  | 8 => 2*((h/288+packedAt gbK8 (31191+(h % 288)*10) 10) % 843)
  | 7 => 2*((h/1543+packedAt gbK7 (213120+(h % 1543)*13) 13) % 4440)
  | 6 => 2*((h/1538+packedAt gbK6 (272344+(h % 1538)*13) 13) % 4616)
  | 5 => 2*((h/373+packedAt gbK5 (75390+(h % 373)*11) 11) % 1077)
  | 4 => 2*((h/36+packedAt gbK4 (2106+(h % 36)*5) 5) % 26)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x7e0f03c1fe0fffff87ffff80013ec73813f3fc
  | 1 => 0x81f003fe1ff0f807f87807ffc6d979c0eccccf
  | 2 => 0xfffffc001fff0007ff8007fff8e181ff0f0f0f
  | 3 => 0x1ffffffe0000007fffff8003f01fe07f00ff0
  | 4 => 0x1fffffffffffff8000000003ffe0007fff000
  | 5 => 0xfe00000000000000000000003ffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x1201004026014a3180ca3481800a431801515c
  | 1 => 0x905001d20a90d0528850552a8258594064c4c5
  | 2 => 0x64a76400152a00a55500a25518a180ab0b0b0a
  | 3 => 0x213aaaa5400001066625c0062d01ac05b00ea0
  | 4 => 0x41ccd33999cca5c00001001837f40006dea000
  | 5 => 0x7800e0310188c600444604603ffff7f0000000
  | _ => 0
def gbRaw : List Sig := (rawDecor 63 gbPos gbNeg).map Prod.fst
def gbPools : List BoundPool := [(0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555, 7, 0, gbRaw),(0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333, 7, 0, gbRaw),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 6, 0, gbRaw),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 6, 0, gbRaw),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 6, 0, gbRaw),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 5, 0, gbRaw),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 6, 0, gbRaw),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff, 7, 0, gbRaw),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 5, 0, gbRaw),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff, 8, 0, gbRaw),(0x55005500550055005500550055005500550055005500550055005500550055005500550055005500550055005500550055005500550055005500550055005500, 5, 0, gbRaw),(0x55550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555000055550000, 4, 0, gbRaw),(0x555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555, 5, 0, gbRaw),(0x55555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000, 5, 0, gbRaw),(0x30303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030, 5, 0, gbRaw),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 5, 0, gbRaw),(0x333333330000000033333333000000003333333300000000333333330000000033333333000000003333333300000000333333330000000033333333, 5, 0, gbRaw),(0x33333333000000003333333300000000333333330000000033333333000000003333333300000000333333330000000033333333000000003333333300000000, 6, 0, gbRaw),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 5, 0, gbRaw),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f, 5, 0, gbRaw),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000, 4, 0, gbRaw),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 5, 0, gbRaw),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000, 4, 0, gbRaw),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 5, 0, gbRaw),(0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000, 5, 0, gbRaw),(0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000, 5, 0, gbRaw),(0x550055000000000055005500000000005500550000000000550055000000000055005500000000005500550000000000550055000000000055005500, 4, 0, gbRaw),(0x555500000000000055550000000000005555000000000000555500000000000055550000000000005555000000000000555500000000000055550000, 4, 0, gbRaw),(0x55550000000000005555000000000000555500000000000055550000000000005555000000000000555500000000000055550000000000005555000000000000, 4, 0, gbRaw),(0x303030300000000030303030000000003030303000000000303030300000000030303030000000003030303000000000303030300000000030303030, 4, 0, gbRaw),(0xc0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c, 4, 0, gbRaw)]
def gbAtlas : Atlas := ⟨10,rawDecor 63 gbPos gbNeg, 0xfeeaeee0feeaeac0feeaeee0feeaeac0feeaeee0feeaeac0feeaeee0feeaeac0feeaeee0feeaeac0feeaeee0feeaeac0feeaeee0feeaeac0feeaeee0feeaeac0, gbN, gbR, gbH, gbI, gbPools⟩
end PEqualNP.Outside.L_meta_37017
namespace PEqualNP.Outside.L_meta_37017
open PEqualNP.Outside.L_meta_37017.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_3_0 : Interval s1Atlas 3 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 26 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_96 : Interval s1Atlas 4 96 38 := block_range (n:=38) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 134 := (concat bs1_4_0 bs1_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 48 := block_range (n:=48) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 48 := bs1_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_6_0 : Interval s1Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_6 : Interval s1Atlas 6 0 1 := bs1_6_0
theorem alls1 : ∀ k ≤ 6, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
  · exact alls1_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 4 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 12 := bs2_4_0
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
theorem bs3_4_0 : Interval s3Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 1 := bs3_4_0
theorem alls3 : ∀ k ≤ 4, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 64 := block_range (n:=64) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 64 := bs4_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 40 := block_range (n:=40) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 40 := bs4_5_0
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 3 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 23 := block_range (n:=23) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 23 := bs5_3_0
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
theorem bs5_4_288 : Interval s5Atlas 4 288 91 := block_range (n:=91) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 379 := (concat (concat bs5_4_0 bs5_4_96) (concat bs5_4_192 bs5_4_288))
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
theorem bs5_5_576 : Interval s5Atlas 5 576 10 := block_range (n:=10) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 586 := (concat (concat bs5_5_0 (concat bs5_5_96 bs5_5_192)) (concat (concat bs5_5_288 bs5_5_384) (concat bs5_5_480 bs5_5_576)))
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
theorem bq2_3_0 : Interval q2Atlas 3 0 9 := block_range (n:=9) (by decide +kernel)
theorem allq2_3 : Interval q2Atlas 3 0 9 := bq2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_0 : Interval q2Atlas 4 0 14 := block_range (n:=14) (by decide +kernel)
theorem allq2_4 : Interval q2Atlas 4 0 14 := bq2_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_0 : Interval q2Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq2_5 : Interval q2Atlas 5 0 1 := bq2_5_0
theorem allq2 : ∀ k ≤ 5, ∀ i < count q2Atlas k, checkRow q2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq2_3 i (by omega) hi
  · exact allq2_4 i (by omega) hi
  · exact allq2_5 i (by omega) hi
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
theorem bq12_2_0 : Interval q12Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq12_2 : Interval q12Atlas 2 0 1 := bq12_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq12_3_0 : Interval q12Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allq12_3 : Interval q12Atlas 3 0 5 := bq12_3_0
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
theorem bq17_3_0 : Interval q17Atlas 3 0 39 := block_range (n:=39) (by decide +kernel)
theorem allq17_3 : Interval q17Atlas 3 0 39 := bq17_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq17_4_0 : Interval q17Atlas 4 0 24 := block_range (n:=24) (by decide +kernel)
theorem allq17_4 : Interval q17Atlas 4 0 24 := bq17_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq17_5_0 : Interval q17Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq17_5 : Interval q17Atlas 5 0 1 := bq17_5_0
theorem allq17 : ∀ k ≤ 5, ∀ i < count q17Atlas k, checkRow q17Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq17_3 i (by omega) hi
  · exact allq17_4 i (by omega) hi
  · exact allq17_5 i (by omega) hi
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
theorem bq19_2_0 : Interval q19Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq19_2 : Interval q19Atlas 2 0 4 := bq19_2_0
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
theorem bq24_2_0 : Interval q24Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq24_2 : Interval q24Atlas 2 0 3 := bq24_2_0
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
theorem bq25_2_0 : Interval q25Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq25_2 : Interval q25Atlas 2 0 3 := bq25_2_0
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
theorem bgb_4_0 : Interval gbAtlas 4 0 26 := block_range (n:=26) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 26 := bgb_4_0
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
theorem bgb_5_1056 : Interval gbAtlas 5 1056 21 := block_range (n:=21) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1077 := (concat (concat (concat bgb_5_0 (concat bgb_5_96 bgb_5_192)) (concat bgb_5_288 (concat bgb_5_384 bgb_5_480))) (concat (concat bgb_5_576 (concat bgb_5_672 bgb_5_768)) (concat bgb_5_864 (concat bgb_5_960 bgb_5_1056))))
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
theorem bgb_6_4608 : Interval gbAtlas 6 4608 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 4616 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_96 bgb_6_192)) (concat bgb_6_288 (concat bgb_6_384 bgb_6_480))) (concat (concat bgb_6_576 (concat bgb_6_672 bgb_6_768)) (concat bgb_6_864 (concat bgb_6_960 bgb_6_1056)))) (concat (concat (concat bgb_6_1152 (concat bgb_6_1248 bgb_6_1344)) (concat bgb_6_1440 (concat bgb_6_1536 bgb_6_1632))) (concat (concat bgb_6_1728 (concat bgb_6_1824 bgb_6_1920)) (concat bgb_6_2016 (concat bgb_6_2112 bgb_6_2208))))) (concat (concat (concat (concat bgb_6_2304 (concat bgb_6_2400 bgb_6_2496)) (concat bgb_6_2592 (concat bgb_6_2688 bgb_6_2784))) (concat (concat bgb_6_2880 (concat bgb_6_2976 bgb_6_3072)) (concat bgb_6_3168 (concat bgb_6_3264 bgb_6_3360)))) (concat (concat (concat bgb_6_3456 (concat bgb_6_3552 bgb_6_3648)) (concat bgb_6_3744 (concat bgb_6_3840 bgb_6_3936))) (concat (concat bgb_6_4032 (concat bgb_6_4128 bgb_6_4224)) (concat (concat bgb_6_4320 bgb_6_4416) (concat bgb_6_4512 bgb_6_4608))))))
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
theorem bgb_7_4416 : Interval gbAtlas 7 4416 24 := block_range (n:=24) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 4440 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_96) (concat bgb_7_192 (concat bgb_7_288 bgb_7_384))) (concat (concat bgb_7_480 (concat bgb_7_576 bgb_7_672)) (concat bgb_7_768 (concat bgb_7_864 bgb_7_960)))) (concat (concat (concat bgb_7_1056 (concat bgb_7_1152 bgb_7_1248)) (concat bgb_7_1344 (concat bgb_7_1440 bgb_7_1536))) (concat (concat bgb_7_1632 (concat bgb_7_1728 bgb_7_1824)) (concat bgb_7_1920 (concat bgb_7_2016 bgb_7_2112))))) (concat (concat (concat (concat bgb_7_2208 (concat bgb_7_2304 bgb_7_2400)) (concat bgb_7_2496 (concat bgb_7_2592 bgb_7_2688))) (concat (concat bgb_7_2784 (concat bgb_7_2880 bgb_7_2976)) (concat bgb_7_3072 (concat bgb_7_3168 bgb_7_3264)))) (concat (concat (concat bgb_7_3360 (concat bgb_7_3456 bgb_7_3552)) (concat bgb_7_3648 (concat bgb_7_3744 bgb_7_3840))) (concat (concat bgb_7_3936 (concat bgb_7_4032 bgb_7_4128)) (concat bgb_7_4224 (concat bgb_7_4320 bgb_7_4416))))))
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
theorem bgb_8_768 : Interval gbAtlas 8 768 75 := block_range (n:=75) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 843 := (concat (concat (concat bgb_8_0 bgb_8_96) (concat bgb_8_192 bgb_8_288)) (concat (concat bgb_8_384 bgb_8_480) (concat bgb_8_576 (concat bgb_8_672 bgb_8_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_9_0 : Interval gbAtlas 9 0 52 := block_range (n:=52) (by decide +kernel)
theorem allgb_9 : Interval gbAtlas 9 0 52 := bgb_9_0
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 7 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 24, 28),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 24, 26),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
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
theorem boundq4 (cert : Complete q4Atlas) : Lower true (roots q4Atlas) (target q4Atlas) 6 := by
  have ready : Ready q4Atlas (asRow q4Pos) (asRow q4Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 0, 2),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq6 (cert : Complete q6Atlas) : Lower true (roots q6Atlas) (target q6Atlas) 6 := by
  have ready : Ready q6Atlas (asRow q6Pos) (asRow q6Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq8 (cert : Complete q8Atlas) : Lower true (roots q8Atlas) (target q8Atlas) 5 := by
  have ready : Ready q8Atlas (asRow q8Pos) (asRow q8Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq10 (cert : Complete q10Atlas) : Lower true (roots q10Atlas) (target q10Atlas) 5 := by
  have ready : Ready q10Atlas (asRow q10Pos) (asRow q10Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq11 (cert : Complete q11Atlas) : Lower true (roots q11Atlas) (target q11Atlas) 4 := by
  have ready : Ready q11Atlas (asRow q11Pos) (asRow q11Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq12 (cert : Complete q12Atlas) : Lower true (roots q12Atlas) (target q12Atlas) 5 := by
  have ready : Ready q12Atlas (asRow q12Pos) (asRow q12Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq13 (cert : Complete q13Atlas) : Lower true (roots q13Atlas) (target q13Atlas) 5 := by
  have ready : Ready q13Atlas (asRow q13Pos) (asRow q13Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 12, 28)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq14 (cert : Complete q14Atlas) : Lower true (roots q14Atlas) (target q14Atlas) 5 := by
  have ready : Ready q14Atlas (asRow q14Pos) (asRow q14Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 24, 28),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq17 (cert : Complete q17Atlas) : Lower true (roots q17Atlas) (target q17Atlas) 6 := by
  have ready : Ready q17Atlas (asRow q17Pos) (asRow q17Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq18 (cert : Complete q18Atlas) : Lower true (roots q18Atlas) (target q18Atlas) 5 := by
  have ready : Ready q18Atlas (asRow q18Pos) (asRow q18Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 0, 4),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq19 (cert : Complete q19Atlas) : Lower true (roots q19Atlas) (target q19Atlas) 5 := by
  have ready : Ready q19Atlas (asRow q19Pos) (asRow q19Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 24, 26),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq20 (cert : Complete q20Atlas) : Lower true (roots q20Atlas) (target q20Atlas) 4 := by
  have ready : Ready q20Atlas (asRow q20Pos) (asRow q20Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq21 (cert : Complete q21Atlas) : Lower true (roots q21Atlas) (target q21Atlas) 5 := by
  have ready : Ready q21Atlas (asRow q21Pos) (asRow q21Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 0, 2),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq22 (cert : Complete q22Atlas) : Lower true (roots q22Atlas) (target q22Atlas) 4 := by
  have ready : Ready q22Atlas (asRow q22Pos) (asRow q22Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq23 (cert : Complete q23Atlas) : Lower true (roots q23Atlas) (target q23Atlas) 5 := by
  have ready : Ready q23Atlas (asRow q23Pos) (asRow q23Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq24 (cert : Complete q24Atlas) : Lower true (roots q24Atlas) (target q24Atlas) 5 := by
  have ready : Ready q24Atlas (asRow q24Pos) (asRow q24Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq25 (cert : Complete q25Atlas) : Lower true (roots q25Atlas) (target q25Atlas) 5 := by
  have ready : Ready q25Atlas (asRow q25Pos) (asRow q25Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq26 (cert : Complete q26Atlas) : Lower true (roots q26Atlas) (target q26Atlas) 4 := by
  have ready : Ready q26Atlas (asRow q26Pos) (asRow q26Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq27 (cert : Complete q27Atlas) : Lower true (roots q27Atlas) (target q27Atlas) 4 := by
  have ready : Ready q27Atlas (asRow q27Pos) (asRow q27Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq28 (cert : Complete q28Atlas) : Lower true (roots q28Atlas) (target q28Atlas) 4 := by
  have ready : Ready q28Atlas (asRow q28Pos) (asRow q28Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq29 (cert : Complete q29Atlas) : Lower true (roots q29Atlas) (target q29Atlas) 4 := by
  have ready : Ready q29Atlas (asRow q29Pos) (asRow q29Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq30 (cert : Complete q30Atlas) : Lower true (roots q30Atlas) (target q30Atlas) 4 := by
  have ready : Ready q30Atlas (asRow q30Pos) (asRow q30Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) (pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p) : Lower true (roots gbAtlas) (target gbAtlas) 11 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact pv
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeee0feeaeac0feeaeee0feeaeac0feeaeee0feeaeac0feeaeee0feeaeac0feeaeee0feeaeac0feeaeee0feeaeac0feeaeee0feeaeac0feeaeee0feeaeac0
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certq2 : Complete q2Atlas) (certq4 : Complete q4Atlas) (certq6 : Complete q6Atlas) (certq8 : Complete q8Atlas) (certq10 : Complete q10Atlas) (certq11 : Complete q11Atlas) (certq12 : Complete q12Atlas) (certq13 : Complete q13Atlas) (certq14 : Complete q14Atlas) (certq15 : Complete q15Atlas) (certq16 : Complete q16Atlas) (certq17 : Complete q17Atlas) (certq18 : Complete q18Atlas) (certq19 : Complete q19Atlas) (certq20 : Complete q20Atlas) (certq21 : Complete q21Atlas) (certq22 : Complete q22Atlas) (certq23 : Complete q23Atlas) (certq24 : Complete q24Atlas) (certq25 : Complete q25Atlas) (certq26 : Complete q26Atlas) (certq27 : Complete q27Atlas) (certq28 : Complete q28Atlas) (certq29 : Complete q29Atlas) (certq30 : Complete q30Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 11 := by
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
  have q1 : Slice true (roots gbAtlas) (target gbAtlas) (0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333 : Sig) 7 :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have q2 : Slice true (roots gbAtlas) (target gbAtlas) (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc : Sig) 6 :=
    slice_correct (ms:=fixRows 0 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq2 certq2)
  have q3 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f : Sig) 6 :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have q4 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : Sig) 6 :=
    slice_correct (ms:=fixRows 0 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq4 certq4)
  have q5 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff : Sig) 5 :=
    slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
  have q6 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00 : Sig) 6 :=
    slice_correct (ms:=fixRows 0 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq6 certq6)
  have q7 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff : Sig) 7 :=
    slice_correct (ms:=fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds4 certs4)
  have q8 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000 : Sig) 5 :=
    slice_correct (ms:=fixRows 32 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq8 certq8)
  have q9 : Slice true (roots gbAtlas) (target gbAtlas) (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff : Sig) 8 :=
    slice_correct (ms:=fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds5 certs5)
  have q10 : Slice true (roots gbAtlas) (target gbAtlas) (0x55005500550055005500550055005500550055005500550055005500550055005500550055005500550055005500550055005500550055005500550055005500 : Sig) 5 :=
    slice_correct (ms:=fixRows 1 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq10 certq10)
  have q11 : Slice true (roots gbAtlas) (target gbAtlas) (0x55550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555000055550000 : Sig) 4 :=
    slice_correct (ms:=fixRows 33 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq11 certq11)
  have q12 : Slice true (roots gbAtlas) (target gbAtlas) (0x555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555 : Sig) 5 :=
    slice_correct (ms:=fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq12 certq12)
  have q13 : Slice true (roots gbAtlas) (target gbAtlas) (0x55555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000 : Sig) 5 :=
    slice_correct (ms:=fixRows 1 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq13 certq13)
  have q14 : Slice true (roots gbAtlas) (target gbAtlas) (0x30303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030 : Sig) 5 :=
    slice_correct (ms:=fixRows 2 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq14 certq14)
  have q15 : Slice true (roots gbAtlas) (target gbAtlas) (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c : Sig) 5 :=
    slice_correct (ms:=fixRows 4 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq15 certq15)
  have q16 : Slice true (roots gbAtlas) (target gbAtlas) (0x333333330000000033333333000000003333333300000000333333330000000033333333000000003333333300000000333333330000000033333333 : Sig) 5 :=
    slice_correct (ms:=fixRows 34 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq16 certq16)
  have q17 : Slice true (roots gbAtlas) (target gbAtlas) (0x33333333000000003333333300000000333333330000000033333333000000003333333300000000333333330000000033333333000000003333333300000000 : Sig) 6 :=
    slice_correct (ms:=fixRows 2 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq17 certq17)
  have q18 : Slice true (roots gbAtlas) (target gbAtlas) (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc : Sig) 5 :=
    slice_correct (ms:=fixRows 32 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq18 certq18)
  have q19 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f : Sig) 5 :=
    slice_correct (ms:=fixRows 36 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq19 certq19)
  have q20 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000 : Sig) 4 :=
    slice_correct (ms:=fixRows 4 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq20 certq20)
  have q21 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0 : Sig) 5 :=
    slice_correct (ms:=fixRows 32 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq21 certq21)
  have q22 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000 : Sig) 4 :=
    slice_correct (ms:=fixRows 8 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq22 certq22)
  have q23 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00 : Sig) 5 :=
    slice_correct (ms:=fixRows 32 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq23 certq23)
  have q24 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000 : Sig) 5 :=
    slice_correct (ms:=fixRows 32 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq24 certq24)
  have q25 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000 : Sig) 5 :=
    slice_correct (ms:=fixRows 0 48) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq25 certq25)
  have q26 : Slice true (roots gbAtlas) (target gbAtlas) (0x550055000000000055005500000000005500550000000000550055000000000055005500000000005500550000000000550055000000000055005500 : Sig) 4 :=
    slice_correct (ms:=fixRows 33 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq26 certq26)
  have q27 : Slice true (roots gbAtlas) (target gbAtlas) (0x555500000000000055550000000000005555000000000000555500000000000055550000000000005555000000000000555500000000000055550000 : Sig) 4 :=
    slice_correct (ms:=fixRows 33 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq27 certq27)
  have q28 : Slice true (roots gbAtlas) (target gbAtlas) (0x55550000000000005555000000000000555500000000000055550000000000005555000000000000555500000000000055550000000000005555000000000000 : Sig) 4 :=
    slice_correct (ms:=fixRows 1 48) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq28 certq28)
  have q29 : Slice true (roots gbAtlas) (target gbAtlas) (0x303030300000000030303030000000003030303000000000303030300000000030303030000000003030303000000000303030300000000030303030 : Sig) 4 :=
    slice_correct (ms:=fixRows 34 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq29 certq29)
  have q30 : Slice true (roots gbAtlas) (target gbAtlas) (0xc0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c : Sig) 4 :=
    slice_correct (ms:=fixRows 36 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq30 certq30)
  have pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p :=
    List.forall_iff_forall_mem.1 (show List.Forall (fun p => ValidPool true (roots gbAtlas) (target gbAtlas) p) gbPools from ⟨build_valid q0 [] rfl, build_valid q1 [] rfl, build_valid q2 [] rfl, build_valid q3 [] rfl, build_valid q4 [] rfl, build_valid q5 [] rfl, build_valid q6 [] rfl, build_valid q7 [] rfl, build_valid q8 [] rfl, build_valid q9 [] rfl, build_valid q10 [] rfl, build_valid q11 [] rfl, build_valid q12 [] rfl, build_valid q13 [] rfl, build_valid q14 [] rfl, build_valid q15 [] rfl, build_valid q16 [] rfl, build_valid q17 [] rfl, build_valid q18 [] rfl, build_valid q19 [] rfl, build_valid q20 [] rfl, build_valid q21 [] rfl, build_valid q22 [] rfl, build_valid q23 [] rfl, build_valid q24 [] rfl, build_valid q25 [] rfl, build_valid q26 [] rfl, build_valid q27 [] rfl, build_valid q28 [] rfl, build_valid q29 [] rfl, build_valid q30 [] rfl⟩)
  have low := boundgb certgb allCuts pv
  have lift := lift_ok (u:=true) (ms:=fixRows 0 0) (raw:=fullRoots) (T:=fullWord) (xs:=[]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 0 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809440 * 2 ^ 32 + 4276808384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37017.Model.Repr at out
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

def mono : List Gate := [⟨.and,[0,4]⟩,⟨.and,[0,5]⟩,⟨.or,[4,5]⟩,⟨.and,[1,8]⟩,⟨.and,[2,4]⟩,⟨.or,[1,7]⟩,⟨.or,[9,10]⟩,⟨.and,[2,11]⟩,⟨.or,[0,12]⟩,⟨.and,[3,14]⟩,⟨.or,[6,15]⟩,⟨.or,[13,16]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,17⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 11) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809440 * 2 ^ 32 + 4276808384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809440 * 2 ^ 32 + 4276808384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37017

open PEqualNP.Outside.L_meta_37017 in
theorem PEqualNP.Outside.L_meta_37017 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809440 * 2 ^ 32 + 4276808384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809440 * 2 ^ 32 + 4276808384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allq2 allq4 allq6 allq8 allq10 allq11 allq12 allq13 allq14 allq15 allq16 allq17 allq18 allq19 allq20 allq21 allq22 allq23 allq24 allq25 allq26 allq27 allq28 allq29 allq30 allgb)
