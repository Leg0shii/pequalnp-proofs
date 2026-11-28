import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37995.Model
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


end PEqualNP.Outside.L_meta_37995.Model

namespace PEqualNP.Outside.L_meta_37995
open PEqualNP.Outside.L_meta_37995.Model
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Atlas := Nat × List Decor × Sig × (Nat → Nat) × (Nat → Nat → Nat) ×
  (Nat → Nat → Nat) × (Nat → Nat → Nat)

def top (g : Atlas) := g.1
def first (g : Atlas) := g.2.1
def target (g : Atlas) := g.2.2.1
def count (g : Atlas) := g.2.2.2.1
def record (g : Atlas) := g.2.2.2.2.1
def tip (g : Atlas) := g.2.2.2.2.2.1
def locate (g : Atlas) := g.2.2.2.2.2.2
def items (g : Atlas) (k i : Nat) : List Decor :=
  let d := top g-k
  let v := record g k i
  selectLive (v >>> (10*d)) (decodeBank d v (first g))
def vals (g : Atlas) (k i : Nat) := (items g k i).map Prod.fst
def roots (g : Atlas) := (first g).map Prod.fst

def SBf (j : Nat) : Nat := [8, 4, 8, 7, 8, 8].getD j 0

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
      testAll (k,ws.length,ws,preCov true ws,[],links g (k-1)) ws)

def Ready (g : Atlas) (r s : Fin 152 → Row) :=
  properPairs (target g) r s ∧ (∀ a ∈ first g, faithful r s a) ∧
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
        exact decode_faithful _ _ _ _ _ ready.2.1 _ ((selectLive_sub _ _).subset ha)
      · simp
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
      exact poolCut_sound (ready.2.2 k i hi hn) _ he h.1.1 hc

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

end PEqualNP.Outside.L_meta_37995

namespace PEqualNP.Outside.L_meta_37995
open PEqualNP.Outside.L_meta_37995.Model
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
def s0Atlas : Atlas := ⟨7,rawDecor 62 s0Pos s0Neg, 0xfcccfcc0fcc0f0c0fcccfcc0fcc0f0c0fcccfcc0fcc0f0c0fcccfcc0fcc0f0c0fcccfcc0fcc0f0c0fcccfcc0fcc0f0c0fcccfcc0fcc0f0c0fcccfcc0fcc0f0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37995
namespace PEqualNP.Outside.L_meta_37995
open PEqualNP.Outside.L_meta_37995.Model
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
  | 0 => 0xfffff03ffffc183fffe0ffffc1ffff0073f3fc
  | 2 => 0xf83ffc1f07fffc3c1ff0f03fe1e07ffaccccf
  | 3 => 0xf003fffe007ffffc01fff003ffe007ffcf0f0f
  | 4 => 0x3ffffff801ffffe000003fffff801f00ff0
  | 5 => 0xfffc000000001ffffffffffc00000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x210011842000200442601118c022310c01515c
  | 2 => 0xa225228c84a90941d0a90a2952145254a4c4c5
  | 3 => 0x454a45106952129c2152a052a540a4a94b0b0a
  | 4 => 0x4a7388294c1b5ceab41888833999c031f00ea0
  | 5 => 0x8c630e318e639f33399ccce0311100c1fea000
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xfaaafaaafaaaf000faaafaaafaaaf000faaafaaafaaaf000faaafaaafaaaf000faaafaaafaaaf000faaafaaafaaaf000faaafaaafaaaf000faaafaaafaaaf000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37995
namespace PEqualNP.Outside.L_meta_37995
open PEqualNP.Outside.L_meta_37995.Model
def s2K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K6 : Nat → Nat
  | 0 => 0x8010000000004000e0000c000114000002100018000b0015c00000c000000004f00000a004080100000fe42fc31fe20fc42fe21fd21ff20ff32fd41fc43ff31fd43fd31ee21fd42ef20fc30ff43fe43ff41fe41fd20fc41fe31ff40fd40fe30ed20fc10ff21fd10fc21fe10fd32fe32ff30fc32ec21fe40fc20ff10fc40ff42fd30
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x8857e54486fca8207bc8720de2a2217e53107de6210fb14941be2a663ec420cb7ea88877cca32bf29e437f548c3dca3905f94d21dfa0883ee530877aa8185f54420f6a9461ef4250bd842907bd0d20f610c41df320caf8a2a1fbc8621b628a41ec41c82faa998df14532f790021de5310bbca7a0dfd4e10bf28041ed43c83de42905f94021bf2a2417f54c82baa7a0df15231f7a1e417c5050ebca6205f95020bf29e837f505077aa8197750d30b7a92637e5090af8a4085f15031bea94877e53087d8a010f754c10f621e413d54cc6faa6906f10440bfa82637d544cbda85905b14943f6a0e41ec41886f8a7885f14943be292837d54086fca118fb88710bfa9c41ec43886fca818f74c431bfa9a83ed32086fca8987b10520bf28c877d518c2f8a9997b50621be29a43bd54043d886907bc8310f6900217e529077e8320fb54a10f7a10657e51d03de8210dfd4940bf298877d5310bda82907b08720fa98e21df4350fdaa010fb94843fb884217e50d0af8a790fb50e21f7a9843ee51086faa9195d94430f7996417c5150afea8197bcc821f6292215d53042b8a6885f54e32de20c817c54083da84905fd5330bf29041f5310c73a8621fbd4d20bf288437c51502fca4217e8c030faa08837f53087f480207d54430be2a443ee21043f280205f54d21eea98857e54ccafaa7087b08430beaa0213d54043d842107b90720bf2a421ed50887da41885f54242bfa9841ed43483d8a110df54a20f718e41df53443be63985fd4121bf28683bd54cc6dca4105f54f10bea94437f548c6fca11877cc530f618e41ed54087da4210fb50a21bf290877e50882f8a710dfd5221f720c43be54042faa010efd0d40df20881ee41482f8a8987b8c520bf296837d52cc6faa0197b94021bfa8a417d508cbdca9907b90c21be282857d53d0afea2986fd0040df21a87ee31887de6310df14d20bf28481f541c42fca5195fd5130b6a94417d52d077e85217b0c821f629e41ef42ccbdca5085f94640f729e41ec31482dca421df54743dea0a81bf41d03daa610df54c41bea8e417f540c6faa0215f55031be2a2417f53042faa4185fd5220bf29821ef54483d86310db54b31bf28c617f544c6daa010df54f40be2a6217e548c2dca5a0df54e20bea8887ed428cafaa5084f95010bfa9a217e54043dea3907b08510bf29081dd438c6fea7905f54c21f7904417d544c2daa5a0fbd0320fb88021ef42c83de85215fd4930bfa96217f54487de84905f94221f610c81ec51483baa7a0df95231bf29c437d510c3ee6298df55220bea80837c504c6faa1a17d90710f7a14437d50d0efaa9087b88740b6a90617d518437c83205f54e319f2a0657c53083de80905f94a30f6a9021ec21503be60185f94321bf2a443bd43502faa7215b94840dea10857e50ccafaa3997b90932
  | 1 => 0xe43887d8a890770c430f721a41de304c2faa9885f54f41ee29a21ee32482f8a498df94010bfa8a877c52443ec4210fbd4f20af298857d500c7de65195754c42bf2a0657c5350bbca6085f54841bf29865f531443d86510df94b31fb08221ed520c3d864907bd0c21b6a90817c538437ca8185f94742dfa0a817d540ca7aa8197b54843bf29881ee50886f8a8085f55320f790221ef525077e86a15794c10f6298437e51882fca420df94831bf29043ec41086fca5887b50421b6292637c54c87ee8320fb48110ef21a65e651086fca6886fd0e41fc880217e5110efca018fb10c21f720641be4250b7c82a0df14d10b629221ee21443bc8718fd48421bf2a087ef50886faa6086f50c41be29281ee54886fca4195f94f40bf2a083ee21902f8a610fec4110be2a0617f5350b7a8621fb94520bf28c83ed40c82f8a898fb8c832f7186415f53443dc80905fd4931bfa92837f53886fea0a15f55321eea1887de430c77a80205f94e41eea9881ee21502faa5a05f94e43bea9087ee41087ba63987b94b31af29e837e51ccad8a4a0fb50120f6aa241ee52102faa920fb88630bf2a085f541443f641107e88020be2a4656e52903daa4207d90441dfa1e85ed53c83d842085f94e20f7182417d51cc3d843885f95110f6a8a416f52507f660985f94a31bfa9a416d5210efca310df54632bf29e21ee32087eca2205f94210ee98a617e52cc2fca521df95131eea1e616e51086fca3907b10b20f610881ec54c82f8a7105b94621dfa1e81ee520c2fca810f78c531f6a1043ed43087bc63187b88530be29a837f548437a86a17d54440bf28885ed424cafca2087d44010bfa90217e51d0efca990df94b43ef21e657d5490bdaa910fb94a30dea1c837c504cafca3987b0c421f721043ec51c83dc6210df55243ee18c617e52903dea498fb90842bfaa021bd41d03ec82885f94441beaa4637f544cafaa898dfd5232bea8443fb20482fea8105f54332f72a0437d54082faa3215f55330f6212417e51102fca020df14141baa8861be40503d88510df54740bf288637f54483dca6907b54e21fda04817d53442faa520f74c832b728e417e530c7d885997ed0140f698c437d540c2faa8885f54a40fb18a21ef43886fca9905f54c40f610e81ed31c82f8a890fad4120beaa461ed54c837e8721ef50f42bfa9e21be540cafca318dfd5310f710e613d540c3f240105f54440bea88657d54486fca3195fd4532bf29e41ef30c82faa5885f14520bfaa043bd43d02fca0215b54221f7904217f53487de8410df14f20bf28c857d5010fdea488778c932bfa9e437d5190efaa418fbcc120bfa8265ed30c83dea810df95330b6a9481ee21843da41085f54442fd080217e5010efca4885f94e42f698a417d51903ba8618df54c20f7a9c43ec5250fda60907ec4210bf29
  | 2 => 0x8002178961281002812040000c02c00860000482a0180704c030005a828af000000760090e070080e00e00a4c01a1e0000a1717a0300004800000140ba1803064a100a0a0e403022000000b0fe2d0020503803076000160b0180504c038d603800050140b00e2800c129460003427800000020d80034000078c4000280301809002c706e5e8037c80003078058421e80e018180e800aa006160040005e420041601405808808000a8260590c0002a06002270000101010001430028937603804028043f80600848000040881801030000020b84a0580c028186e012b5002020de06062df80a00918088620100a61012010020c9761c80000000000b2008200c800480100c84002000098000c06e0004a000009a014030240780002002040024604e14826060080a806088300080417034060380c854059ae01820018780684c0a00e008d43c85a26800278000481a0000016002207bcc720f7a9621ec218c3ec63885f54810bfa94217e54c42faa198df94040ee980617e5090e7ca998df15032bfaa643ee54482fca998fe4c0309f2a061ed53483d8a498df94241bf29c216d52842fea2a17bcc520beaa4816f52c43be6318df55120bf2a0617f5050fdca4085f15132bfa8a816e52cc7dc43105f94810b7294617f540c3d843985f94030be292617e53d0afca8997794c40bf296816d52042f8a6a07790f30f6a96637e520c3dca5207b88120bea92215d53102fca2105fd4910bea84637d50c86faa3a17bcca21bb288817d52d0efea6a05f14530bfaa665de434c3daa5207d94430f729c437f54cc7de83905f54a31bea9c617e508cbda65905f14c10dfa1883bf40903ec6218df14a10f62a0437e52843dea4a1df94e40beaa443bf4310efaa4207b90920f698843ee42c82dca4085f94343b7290616e52842fea4a1df15320f7a8241ef50087dc42185b54a30f721443ed32886faa5985bd4910f6210437e50cc7dc43907b4c920b7a92877d5090fde649977cc431bea9e43ef21086faa3105d54440f62a443ef41886fca6905f94432fb90c436c52c42fea8885f14b10f7a0a41ec52c42f8a91877d0e43f710a41ed21482faa120fbc8020bf280657e5290af8a8887b884209e2a221ec30c82f8a9985f95220bea9c81ef54c83ba86995f54e41f799241ee21486f8a810f78c4309faa2217d53886fca6187b0c120f6a10857e510c3bc8621fb14e21f7aa443ec40c83dc85197b48720be2a4417c50487da40107b08530f6a8e41ee32c83f661187b10120f719443ec21843be61185f54a30f721e41f721487daa5a0df94c20f629a41ef51483ee82a0df15210bf2a4657d53c83ee6318fb88440f699065be54cc6faa9996fd0842f729683bd41107d865907750f32bea8683e
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xf41c82ae640c821b3d8d544823e64949109798c540ca5d63952219b596420872d54884309bd89531063f65500409bd8951cc26e6114910b358c40c82eb6054d208f992538863d6494e21d354c534826e6214d409bd89540c66e6215010cbd52214426e65101209798c505074d53948409bd94210c36a5248020c7d954310e5f6550c43d9147314823f6550842d9544210c2e66114c219b596520426e62141439b98854842e960d4f209b98a50d0e5e63153219b98b548426d65c80109798c54c825f654c8329bd895190e5d63153209b596320866d6294f109b98a509066d62940319b18951d02e66115021d390d5210f2d54948109b18951d0e766114143d9d44215031d5454c109b588544c26c6550c219798c540c26f62544408f990538829f6550c439bd895110e7561951329b195424ca6e6510e218f590538834c53d49109b58b540425d63153219b597420cae6610c320d9946211026e62d45439b189544c76960d4b10b358f5488677654c431cb15120442cd6310a219758c548826f65084109d584540825e63953109b18954cc2ce63d47209bd8951d026f6588430d9546211026c6154a409b988540c63e65d0540d314c214431d544c8329b189544c27a6014c218fd954310ee96015021d594e51102ce63d04218f990530866e6294f10ab990324826c61548309b58b54cc6ac6250f429b98a54c426f6254f10b958430482cd63140219b185521026e6215230ab992538866e62d50309b195324826c6254f40b9987430867a60150218f99353042ad64cc520b398c42886e96008540cb551520c26e6294031e350d424caad6414221d9d8951102cd6310832d354c210426d6215330ab592538866d60d49318f191524431e5454c109ed9540102796014c21d394e520426d6588430cb952520426f6255131b358e548866e6214141d394e211026d6294043ab993310866e65085109b98a544c75653544408f596540426d65886409798c54042cd63d47209d584548831d53508429d984540832e54948308f590534826c6154a3097d8d544426e65c8520cb153204426f6588630e3d894310e6c6550d20cd545401027461551209b58a50cc63c6454d109b189518c23d6494d10b398c50086d56190c31ab59053c826d65cc5209b98a501067661152309b98b538425e6395110ab99032c826d62d4543c750d5210ee960147209b189540c6ad64cc7209b580525067561d53329b195438866e650c1209bd954210a6e62d53319b588548434c5348110cb553420ca6f62551328f990540c31d548c430ab191534823d65950329b189511026e62d52319b58a500431f54d4d109b98b530826d65d0720d914431482e5610c3209b994524438d4310c21f848110042ad64140219b195414826e6510d208fd91524433551904408f99253442e561d0c21
  | 1 => 0xc25d6594c109b588540c23c6454630e350e5210e6c654c7209b988520426c6548110cb55054c826d6215010b398c54c826d65084109b996424cacd6315320ab59331886ce6310320d514e31443655188430d314c524423e6414c209dd85544c32e54084109758c544832d5448010ab590534826f6550520cb550420865e63d5221c7952530426f6550e219b988540ca6e62d45309b189510c26c654c520c754f40102cd6310b329b58a509072e5454b319bd94218c31d54cc832b918554482cd63d0421d354c21102756114c20b398e548873554c40108f99253487665108720d394e521023c6454d20ba580314825d63951219dd85534832d5494b31cd551100429d63d0641c714d4350b6661944219bd95430865d6590c31cb552520c25f6354910d394d521026e62952319bd8954c431d5390440ab990304825e63150209b994430866e6214c209bd8954487365494430d9d8a511023d6414810abd91514831e5450e319e181544c65e63151209b58a54c434c5388510a75924310ead640c920a758f41d023d64141318f59252442e960087109b1895110e7b65480209b997324831d54cc0309bd95434832c54509209b99731c826d65cc4219b98a50cc6e96094d20ba582514832f43548439b9875250f6451085409b588548c31d4394443c7551300c26f6054b41f8885100434f5348110d9549510c32e54480109bd89544c26d62d52308f596540c27965840109bd95310863e6515110ba58054c834d5388410d998752c425e6395121d394d200423e6414810cb55320042776155120d9944210c31e5350e41d394d52d066d62d4540ab993318866d6094b41b358c404832c54d49109d58453882cd63d05209718d52443665108420d354d52042ce63150219b597414826d6294d21ba580414825e63148108f990534826d60149319b58a534425c63551109b189519026d6214e10d394e52d06e661152219798c54882ae640c320d394f200426d6508430b9185534826d6510f20ab99053c83696014b109bd9531482ad640cb209ed95300c26e62949109dd95411072e5450a21d9144214c25d6315010b398f548866d6295121b398f418866e65d07209b5885050f2f54149109ed95100426f6254f409d584548c27661150109b98b540433654544308f59253c429d63d0441cb953200431d531044097195434ca6f65480209bd89510c36451105209b98a53442e960085309b996214434d53908429758e54c425c63551209b58a50d0eaf6454d209b9845250e6d6215331e350c438874f53c8110a7593318c66d65886309758f548872c5408510b9586430871c54d4d108f99053c86746550510d5546310c2e96008640b358c54086ea600c5209bd9541c82e960084109b596210423d64d4810d354d521026f6254d10ab59053086e6610c120b358
  | 2 => 0x6095120b358f418876462944408fd91534834f53885109b98a5090e6e62d4c109b98a50d074c6254c42cb95221043665188620d394e21042766115030b318d514834e5354810b398f41c834d5314f209ed81544c65e63d50109b988540c34d43548439b997424838d4310f208f590538426f6550f20ab99053483c5310c4218f590530826e6194a409b594430872e54548109e580540c6b561d0c41c7151430c65d6315210b9984404834e5308440d354e211034d5394b41ab59351c834c534c920ba58221c423d6494c319b99731482e561101209bd81520426f6508640bad81514826d60d4943cb951520c25d6314141b358c424826d6094b319b594218c25f63546409b99741482eb60551209d984548838d4354843b318d544827661951329b5805250e7661d5030cb50d5210f2d5410b20cbd53204426e6215331ab59030c826d6295110d9189510c23e64951109b986520c33551d00409b189534431c5350d409b988540825d63949109e980540c76652544309bd8954cc2ea60105209b596210823d64d4c10d354e520425d6315021b998440c825f6355120b358c508869d63d05408f590530873554544309b588535030d4354843ab990530869d64cc7308f990530429d64cc5309b583525075551cc0309d195314432d54108328f59053c82ce63109209b99443c82e96014c21d9946210c2e661d5021cd54441102ce63142219798e548866c6254f109b58a50d066c65509208f990504c66e6214131b998753087675108530d5545300c36462944309b986521031d5350040cb150524426f6254d219b58b514c26d6294243b998720c42ea60150218f993538866c62551109d98754ccb345490510b358c42c826c6550720ab99050886ae64d47209b58a548c6ce63101208f99253c426e6295110ba980530866e62153309bd96210426e61948439b5825210ee661c81109798c548426c6254c41cb95252cc65d658c430d354c530866e6294231cb550544826f62551108f992530c6e56110320d994a51102ae640ca21ba58221043356115110c7151434c32d5408410ab590320866d6510821c7151434cb666114b10c7552530426f65484219b58b548c66e6294e419b98a500432c5488510ab59331086cc6250f329bd9531c825d63d50109b98b548c26e6194a30d954a51102ac64545209b19543c832f5495221d954a510c3676294430cb950210c2ce6310b20c715143cc25e6394d10c7d50534423d6590440d9d89510c3665254440ab993538866c62546439b594320866e6214e10b9987538865d6314810d9549511034f53d49109bd8152cc66c6154843d3d4c214426d62141318f990538427960150219b996304836451d052097d95300c31d540c430ba580218c34d530cb20d394c210426f6588440c754f4210a6c62553109b58b540
  | 3 => 0x1e87200c360440400c0a0780502413018010042d01400000030a40100c090380608699024000241600c0400400008000702a000120981603009058080246c0341600c000e00a00004ba81f000000f400000ed0580d00000014000001004978000003241900404010230000200401004bb018000140406c011043a0104b02c080000002425070010f822000040001900001000000d817094000640603c6d05c1105c06004000200a0080000403018000000604c3e08c0211400000211080401c010100000800080021380312801000030980602c050b830018020001a0084e000270040b018000a8000340e25c11064000880500003014080380c00c5c000ed0440103001050056040001c3805525000060440401809010000100104004024020002d044000000800408670020340e0000600000058852203605411000010041700007034020041d0000008405000004840a01c2b00c1a0040c00e0205c24184080540e004050840001012000000212d0580200005010020d0070041a02c2a01c04036e96014f20cbd53524425e6514d109b98b540826f6550421d9146214834d5348010c750d5010e6d65086409bd9520042ae641402197997314c2ae64cc5209b58b548426d6510d209b594438866e6214c10d554f100426f654c832cb550540866d62d4e10ba58351c826c61149109b996404832d54084309b58a544c75553440108f990540423e6414f209798c530432f5408510b918520c426d6508440b9185204431c5450f329d5845050ecd6315120d9189511023d6494d21d394d328874f5394e219d584540c38c6250c43ba58354c82766114c209758e544c63d64d4e21e9504410863f65504419b597410866f62547438fd91534426f6588640d314f204425c6550d30d3d4c524426e62d45409b596211026f60548439d98453882776548421e350f42ccb1c5414d10b398f414832e5488430cb55221042cf6354520b9986430866d62d4c109b588540c66d65108328f59053c87555354440b9d8553482746154d20b358c420866e65c8110d354f20042ce6310821cb551520435553944409b58853042ce6315120d994a510c3665108440e350c434825c63546409b988544c2776544010b998453886e661d52219bd94211026d65cc7209d587540c25d6395110cb189540cb2d544c8328f990540ca6f6254630d354d52d066c62547308fd91518c26d6294e419b58a50106ae64cc720d354c32086ad640ca21d5584534426d6054810d9544211025e6315021ab590304825d63d4810d354d4210a6f6254640cb552320ca766114c109b98a5010e7461551309b58a508c6ad64d4e2197d95310c72f54481109798e524425d63150208f99352043355494430a7593310c66d62141419798f520423d6414c10d5544310c2e76155120cb55152cc6e9
  | 4 => 0x40001c1e1680101c0001039238bb164050fc7505c1307804
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x4024104e3803c028000c18000200628225623350100e004c1ac8a986590629545805408706b22a629e419254d6008410c18eca1aa421d0c7454c5348306b22a62984343dd54310e21a1ae42a2869846970195430863238aca21a4183dd94354843cc0a2b00429860d5458c42c830732a8621c43435d2534ca21cc4c2b00a58860d6550c4348306aa2c621043835915314d20e42a8902200850d739514288713320a398a41439d35394e21a18eaa18869050d7414d3248306aa2c62a043835516315120c1acaa18879050d7214d43503122a0c290221465c05450c31c1a8630aa421d0d731514248286b90a8a1863835516310832c1acaa188610e60515802150306a1ec0a9087435ca5450e31a88e2a98a690649535805308706aa2c62a641439cf5495221c1ea8b1ca910d0c735505448323318a3a0a418a5516008410c18caa1a849950d7215143cc3a0a9a4088021435ca5350e41c88a630a4088524715505448306b26a729c4383591530c821
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x2601000a04815954310d20a04815516315120a0681dd9435484380c875954310d20c05641c55314d2080e879954310e21
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 801
  | 4 => 781
  | 3 => 56
  | 2 => 6
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s2K7 (i*5) 5
  | 6 => packedAt s2K6 (i*16) 16
  | 5 => packedAt s2K5 (i*27) 27
  | 4 => packedAt s2K4 (i*38) 38
  | 3 => packedAt s2K3 (i*49) 49
  | 2 => packedAt s2K2 (i*60) 60
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 7 => 2*((h/1+packedAt s2K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/56+packedAt s2K6 (704+(h % 56)*6) 6) % 44)
  | 5 => 2*((h/274+packedAt s2K5 (21627+(h % 274)*10) 10) % 801)
  | 4 => 2*((h/330+packedAt s2K4 (29678+(h % 330)*10) 10) % 781)
  | 3 => 2*((h/32+packedAt s2K3 (2744+(h % 32)*6) 6) % 56)
  | 2 => 2*((h/9+packedAt s2K2 (360+(h % 9)*3) 3) % 6)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xe0fffff07fffff81fc3fc3fffc3ffffd11f1ff
  | 1 => 0xff07e1ff83f0fffe1fc3fc383fc383feee4e4f
  | 3 => 0xfff801fffc00f8ffe003ffc03ffc03830f8f8c
  | 4 => 0x1ffffff00fffffc00003ffffc03f00ff0
  | 5 => 0xfffffe00000000ffffffffffc0000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x22004011002000002004404884048888009095
  | 1 => 0x44518222194150160c4184111841117066464a
  | 3 => 0x8a32d54528eaa1aae222ea82aea82a1b0b8b8c
  | 4 => 0x1ca51988528832cd56a8220433327023b00d60
  | 5 => 0x10c6110e630cc4f19b33332702204043dd6000
  | _ => 0
def s2Atlas : Atlas := ⟨7,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaaeeaa8888eeeeeeaaeeaa8888eeeeeeaaeeaa8888eeeeeeaaeeaa8888eeeeeeaaeeaa8888eeeeeeaaeeaa8888eeeeeeaaeeaa8888eeeeeeaaeeaa8888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37995
namespace PEqualNP.Outside.L_meta_37995
open PEqualNP.Outside.L_meta_37995.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x1804800000400813020030010100c00400020041830c0002fc30fc10fc20fc31ff40ee21fe40fe30fd43fc42ff42ed20fc21fd10fc32fe43fe32ff43fd42fd31fe41ff20ff32ff31ff21ec21ff10fe31fc40ff41fd30fd32fc43ef20fe10fe20fe42fc41ff30fe21fd40fd41fd20fd21
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x1c18522082801a104830005e01003898500080011e480020038d3230000010004000006c0863604180180c099f5a82413e540c2baa720db54b41d72a6416d528439aa610f394f20bd280433d54cc67ca8194f55030e7298433e548c678a8985b54a30af2988175510c2dca3905b94621afa9a216e52842dca4185b94421b628a415d53d067ca8085b14b10aea9881e651086baa7907a48110b6a90816e52102baa6215b94a40b6a84435d530875ca810fa48210b7296636950086d8a4885794c21af29e833e54cc6d8a4a0fa54021d6aa0435c53502dca421de54021b6a90216d5210f9aa7904f55032b72946176510c27ea8885bd4941af298856d520c2bea6a04f553209faa2616d52902d8a498dbd4910b7290413d54042baa6085bd4b109f2a6413c544427aa918d794f20af298216e52d06eca2204f95021ae29a217551102daa010d794e41b7290219d4310fd4a010eb55320b7a92636d52cc6daa5104f55021
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x7038000c350d5210f295454021c355153c830d5454c219a19520443495354021d294d500872a5454021
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 8
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
  | 5 => 2*((h/35+packedAt s3K5 (704+(h % 35)*6) 6) % 44)
  | 4 => 2*((h/51+packedAt s3K4 (2484+(h % 51)*7) 7) % 92)
  | 3 => 2*((h/16+packedAt s3K3 (304+(h % 16)*3) 3) % 8)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xc1ffff83ffff0f07f0fe1fffc3fff81e89f3f3
  | 1 => 0xfe1f0ffc3e1ffff87f0fe1c1fc383fff764c9f
  | 2 => 0xffe00fffc01ff1ff800ffe01ffc03fe1878f1c
  | 4 => 0xfffffe001fffff00001ffffc001f80fe0
  | 5 => 0xfffff000000001fffffffffe00000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x44020088040010008012024440488844009131
  | 1 => 0x88841110902a00283104208884111298324486
  | 2 => 0x144aaa290d548353888b54156a82a545858b18
  | 4 => 0x3954cc42a906a59d5aa11021b3270189d80ec0
  | 5 => 0x219888733198c9e66ccd993822040611ef6000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeaeaeac8c8eeeeeaeaeaeac8c8eeeeeaeaeaeac8c8eeeeeaeaeaeac8c8eeeeeaeaeaeac8c8eeeeeaeaeaeac8c8eeeeeaeaeaeac8c8eeeeeaeaeaeac8c8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37995
namespace PEqualNP.Outside.L_meta_37995
open PEqualNP.Outside.L_meta_37995.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x2d80410000001802000801c9001000000240082ff42ff32ff31fe31ff41fe30fd30fc43fc41ff43fd40fe42fc30fc32fc31ff20fd21ff40fc42fe32fc10fd10fd42fe21fd20fe10fe41fc20fd31fd43ff10ff21fc40ff30fd41fc21fe20fe40fd32fe43
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0xa437e51082fca3995f15121bf280217e544437a80205fd5021efa1c657e5190af8a99977d0c32beaa2617c514c3bca720fdc8521beaa461dc5350afaa1995f14d40df20a835d53086faa3217b94840df2a021df308c2faa4185f94b41bf296877f53842fca7885f94442de21c813e540437c86a1df54742df20881be43902fca8085f14543dea108575510cafca7105f54443deaa0437e5390fee4310df94241be2a2657d52c42faa120fdd0641bfa9a217d50087ba6598dfd4c21dea16837c5150afea690fdd0541bf288437e520c2fca610df55220fc900417d51d0fde41107b0ca21fd28065f9300c37e84215f55310beaa4657d52886f8a818ef90f41eea1a61f651102fca1195f94840bf280637d538c3bc6418df94e40be2a643f920842fea9185f95331bfa8a81fb50506fca6205f94632faa0883dd53103dc409077d4d21bf28861bd540cafea6905f54841de21e833d54c82fca6215fd4f10ef994657d53887f660985f55331bf288637d52d06fca7a057d4d21be2a641bf40903dea498fec4210baa8881f710043de4310df94020b7294615e538837aa918fb48720bf2a2617c52842f0a0a0dfd5032ee99065ef32886f8a918dfd51329f2a6417d54cc3f681105fd5221bf2a2437e5090efaa620df94e42bf284437f51482faa190df15230bf28865f621087ba6218df14d21fa880217e50d0afea818f790f30ef19661dc430cbf641105f55030bfaa2417f52c42faa321df95221af29843bc544c3f081107e8c220bf28e87ed21482fca2205f55320ee21e637e54c87dca4087e4c120bea90217e54842fea8105f94841bf298217d53906faa6105f94630ef992637d508c6fea2985fd5121dfa1a857c54cc3be86a1efd0f42de20c81dc53486f8a0997e88110bea8e655c53486fea9986f10d41beaa0637e51907ec8220df54c42faa8865be43103de84a15b94810ef98a617f54042fea5085f94321bfaa2633e54086fea9905f55120bea8c81df43cc77886205f15210af29881dd31cc2fea6085f95232ef98c637d5490efaa2107d48421bf29e417e50842f8a498df94c41bea88857e54086fca0204f55021dfa08833e540cafaa598dfd4143f790e417e54482f8a0a0df95031fc200217e50d06faa7884f55231bea84657d520c6bca6085f55231f690843dd300c2fea710df54243fca8043de53042fca1995e94021ee1946379500cafca820df54331be2a0617e540cbf680086f50f42bca84857e51cc3b864987d4c521fc282837e52842baa720df15220bf298637c504c6fca4215f55020f6a16417c538437aa9907b509209e2a2613c54443f480205f15331bf2a6417d5290efaa4885f14f10bea90877f5250efca8187bc8520f6196417e52906daa5187bccb20bea80877f53502fca9884fd5110bf29c837d50d0af8a6085f94742
  | 1 => 0xd52103de65195f54720faa8881ef32482fca410df94a32be29e413d540437aa8087bd0a42dfa14817c52442faa7105f54032beaa421bd41107f2a0197d4c621ef182617e530cafaa0217794c40beaa0217d518cafaa5207b14931ee992637e5410b7ca8196f10440bf280877e54102fca7085fd5321bf28e816f524c6faa1a0f754c21ee190637e50087ba87985f14c20bfaa0617f5050afea998fd8c521bea8083fa20082fca9187dcc531bea84437c540cafaa810d794e41bf2a2637f50486fea9195f94c30bea88657e54882faa920df15131bf29065ef21086faa5985f14540bf28485ee42c837c84a15f15221f729461ee320cb7e85a0fecc230bf28e41fa300c2faa3085f94032bf290417f5350af8a4a0df94b31bf284815d53882faa2206fd0740beaa2217c54082fca2087d90710bf28061f641442faa7a15f94831bfaa421fa208437ea8987b90920fa988637e53d07de6410df14d42beaa4817c548cbda64197bcc932bd284857c53087be6218f710e32df2a6417d54c87daa4205fd4f20bea94417f504ca7ca918df94620be2a0217d510c2f8a090fb50842bea94217d52d02fca4087ed0310bfaa441f631886fca5185fd4810dfaa2217f524c2fca918f710d31ef980617d50d0fbca610df14143df202816e52102fea48877cc730fc984417e52c43bc649877ccb31dea12837c53c86fea098df14930beaa0657c53887f680907dcc631beaa2657e524437c832057d4d42bfa9841f840c42fea790df94b40f6a9461bd42102fca6905f54e10de2a221fb10442fca521efd0941ef194637d51cc2fca220df94c43fd90241be43506faa910dfd4d41bf29481f840482eca2195f55121fda02817c54482faa6207bc8020b6a9021f9204437a83a05f94c20bb288817c5050bf460906fd0840bf29661be54086fca6887754e41ef18a637d544c77e82a05f54f21bfa92817e51887f2a1215f54a41bea9461bf4310f7e80206fd0e43bf29a437e53887ba62985f14520bea90817d53042faa5a1efd0641fb18863df320cbf280207e84010efa1a635c5350afca1a1df54d20bda82837d538cb7e85215f14e20be29a417e51902faa610fb54810bf2a0417d53d02faa6887e94021bea9e837e528c7da40105e54021be29021df5350afea2a15f54630ef218877c53506fea8985f55332bea8c41f710842faa518cfd5130fb082217a500cbb865985f94443dea1887dd4310efca9987b88521be292877e5290afca821df95332bfa92837f5150efca7a15f54031bf2a2657e50882fea498cf55032be29a217f54ccafaa3a05f94843bea9e417f514cafaa718df54e42aea9881de434c2fca198df94643b6292637c52502fca118d754c10bea8485df4390ef8a810f754c10fb28865ee4210bf681205f54e40dea0a817f50507bca7107e94242bea9
  | 2 => 0x42c0440c261236e0070280500c23020030240a000140296f030f901c21004000088901c010d07c000020140c0742a06c4f0287e2200f000060e40300a48020150200219c050bc000040902c0002c0d01c15130310dc01018010242a00004008030f0000740106c4d7a03509c06000000208b000260a00c000b2000000940403805000fe2d0061c4260880000d1603c020180a0040401c1a39dec1005406c3c06802000390114500c02004ab00833040020b823000020040701c0203c1900033000000009305c1e07008044011a8182c00b018074741f0c403004450040007c022440003c0000008008000000e02001000001600203c1603c0c2183c014001b020024011a410000000280000c00040080e41e0000b06838004032140100400bfaa221f9100437a86a15f94f21faa0e217f53882f8a5885f15130eea9c41de324cbd86410fd50510bf280837e518c77a85205f94042be2a2217e508c2f8a2995f15310f619241be548c6fea9885fd5231beaa4856
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x8505076952d00109758c540834e53548408f592528c27765504419798c505063e64d4c2197d8d544827661d50329ed95200825e63d5031ba982424823f6550842ba98a30483b141d0310b658c404835a63942428fd95401034c528c5319bd89544c6b860507409e19530482756114c209b588548423d6494d108f59252443385448110c7151314c33942141419d98453c826e62d4c209bd95210871d5454c218f191524434e5354810bc58440882766115220b9584328863c6454d208f59251cc25f654c8329b588540c65f654c030cb551520423f6454d10c754f421023e6515130a759032cc34d53948109b98852043365494432c7952328c63e64148109d98454082756114f20b558432cc31d5494c10cd90d511029c6350941b6980324c25d63152109d986544cacc624c431ce951500865d6594c109d195414431c53d0d42dc946500ca5e6394d21d698c505074c6254c219758f548867a60d4c219718d521063d65904409e19520442cc63487209b988540c26e62d4e10d354e52102b8644c2209e596100425e6394242da548400433551904409e983548ca7a60148109798c548825d63942429718d52d029c63508409758c540427661150328f592528425d63947429d586544ca7960d5032c794f419063d6414810dc181511034c53885219758f54042cc624c530d394e521027b6544010b318d214823e6495130cd553100426d6214c10cb952520431c54cc5308f99053c86766115010b9189318867765440109b98b530436a6014931ced0a5090a3e6414b109758f54087556114d21d554d210866d62d5010c718d540cb1e5454c10da580524c65e6314b10ce952500caad640cb208f993538865e63d4a10a718d42d063d65950329b58a5090f695244010d5d0d510cb5a53540218fd9541106b461509419d19531486cc6350b208f990540431d54d0c328f990530425d6394321b958432c825d658c8319798c530867b60551109b58b548c2796510010c7950328c66e6295131cb990524c65e6394321ce551500cab864440109d18554482b96010c40da98252102ba64c8220ce904505063e6415021cb592528c32e5250840d694e50087b241103109e983540873551104409d984530823c6454e10ab590324823d64145209b18953443c4328c621b318d42483573254432b9584324837151540329758f548823e64d4c10ce15310442b66190d418f59353c434d5354840cd551510cb1c5490d30cd551100425e63d4810bc584404826e62d52309d584548835a534c2208f992520823d6414f208f992534435a6094e20ce952500863c64542219bd95320ca3e6414f209798c548425f63548419b189544c67a6014c21b398a304c35953540219dd85544831c548c930f20c9304825c63551219dd95310c63f6550c439758e51d026f6254f10
  | 1 => 0x423e64d4f209e580540c65e63d5310cb5525204278605513197994534867561152309ed95300c25d63141419e583548ca6e62150209b98b540427960149319b588548c2d5610c8318f59052c434e539481097997324c63e64949109758f520431c540c9308f99741502766114c2197d8d544cb3443544409798c514833551500409798c540871d53508409d185534825f6355321cb992528c23c6454d109e58252d0e5f6354910d994a51102d661d0d319b98a5090f3b42141419798f548829d640c9309798c520423f64549109b59652042796094b418f990524c6d5610c930c755153042776154d209b58b538427960d5331cb590524c74d53548109e181548863c6454332da982528c26d62951318f99251cc27661d53309ed95401025c6355120b318931cc23e64150329b997324827b60551319798c530425f6354b40b658c408823e64947328f99051482ba64c81208fd9150cca3f6454221cd552510cb7251540328fd91534823d64d48109d587540ca5e63947428f992528c25f6550c438f993520425d6510c329e980540ca5e63d5021bc58440c42cd6210c32cd951510cb2e5450b208f59053087555354440ce152204425d6314b10ce951500cb6552544409e98053083565354440a7992314c6ba60909429758e50083655294440c754e43102b86050540cb95152043683254021f1cc9318873860550109e58354c865f6355121da485500873843141419b195424823d64d4e219758c5148354514c5308f99252843596314141cd584544425c6550d30ce551500867960d4c21d510d510caea62101209b988540427b6055221c7952530435553884219b588540c27a6094b418f596540865e63940209d984548c23e64951109b588505076a62141419e98354cc72e6295320d394f208825e63150309758f528426e6215031d554e51102ea600c920d514e314867a60d5321d3149324c73551d0040ce552500865d63150219798f548865d63152208fd91538433954940328f593530874d53cc8219b594320871d63151309b98a50cc66f65480209e997404825e63d5010dc546500ca5f6354b10d594e511023d64944319758e544866d6215010da54a100434f4314931d314b324c69e63905418f99053086ce63881209718d52c431d5494c21bc18141c423c64540318f59053c874e52cc2309798e544876b21540219e980540865f654c4318f59353c831e54cc6319ed81544865c63553219e98354083696214141d658e5090a5c63549109758f54c423e649443197997434c63f64540319b988548c27561150309d58454083354254440b318d21086796014c21a798e411027561150328f590524c73a43141419e580540871e5454c219b18953c436561149318f590530433954d00109dd9521087595394021a798e419027561d53309b98
  | 2 => 0x12000203c280004a714214000a8120b05880001e030040000a180c026b0583f134400028020765018062d0a01a04020101c060000834cc010000000ef0a804fc1c1c00412700125c24910f804004b000280e000d0105404026f40019010183c015d9207400040040a6ba2034000205894000a0000c00040186004000e8080a0100076330e0001c0421000000138000105e02000081a4107275be13020081c0f01804022e0000002010080c240c020004000078744e04000201001070242211000380a1d000000914010c408f119010002b0080c68080f000100001928001d0280c00020402c0004138000601000ec321326018ea00020023d64d4c108f99353c425d6594c21b5584328c7a94210120cdd09511027960150329bd89534866e62152109e181544869c6350a40dacc9500863e6515110ae191304827a60150319e98252d0e5e63150108f990530827a6014f218f592520826d62d4c109758c520423d6414c209798e51d026f65508429e58053c871e5494c21cd152414427a60d50328f59251ccab86050441d54c9510cb4c43149319bd89534427661150309e980524c76652544409e583540866d62943318f596540425e63150209b988530
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x1f738c80280c073019258d6214141a8ce3a18a498e1454584324c3062a0c498a61585c86054440a64e3218a0a0d887350840482a439a42a8043075d8540c93098ced9926310ea142584404828c39a84282832c5da4110310d10c81926090689635084048314b22c02926383990528c531a28e6a12a22061654584328c698b8086a88818598d5190440c88c428a6298589740c93048330b0ac029263515c84354432a34e7208a0a0d307150850506e0b8864982418a1915244010
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0xc80645c4324c120a8083509611012088987190324c120
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 632
  | 4 => 473
  | 3 => 29
  | 2 => 3
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
  | 5 => 2*((h/231+packedAt s4K5 (17064+(h % 231)*10) 10) % 632)
  | 4 => 2*((h/220+packedAt s4K4 (17974+(h % 220)*9) 9) % 473)
  | 3 => 2*((h/16+packedAt s4K3 (1421+(h % 16)*5) 5) % 29)
  | 2 => 2*((h/1+packedAt s4K2 (180+(h % 1)*2) 2) % 3)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfe1ffff03c7fc70f1e3f1fffc703f07c19f673
  | 1 => 0x1fe1f8ffc07ffff01fc7e381f803fffce6487f
  | 2 => 0x1ffe00ffff87f8ffe007fc01fffc7f83078f9c
  | 3 => 0xe00000fffff800fffff80001ffff8003f80fe0
  | 5 => 0xffffff00000000fffffffffe00000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x42443011809088030209048cc1189118089631
  | 1 => 0x84884122092300300c42211108212660624846
  | 2 => 0x48409244901401452005482452484909058298
  | 3 => 0x819564892841929a56900049a4b20232b80d60
  | 5 => 0x1119800e326624ec9926927000c00c43d76000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfeeafeeaf8c8f8c8feeafeeaf8c8f8c8feeafeeaf8c8f8c8feeafeeaf8c8f8c8feeafeeaf8c8f8c8feeafeeaf8c8f8c8feeafeeaf8c8f8c8feeafeeaf8c8f8c8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37995
namespace PEqualNP.Outside.L_meta_37995
open PEqualNP.Outside.L_meta_37995.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x3031000400404c000b1ce09e0040801c0543200fc42fe10fc41fc20fd31fd32ff30ff21ff10fc40fc32ff31fe20fc43fc31fc21fe30ff42fd30fe31fc30fd43fe43ff43fe42ff32fd40fe21fd42ff40ff20ff41fd21fe40fe32fe41fc10fd10fd41fd20
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x2657e54886fca3195f14143bea90217d53082faa7a05f94343dea1683fb20882faa510df54440ee29a437d52906faa118ef55021be28a81ed21087f260905f95041be29a837e544cbf461105f94a40beaa4817d51ccbf0a0a0f7d0e32f6a10857c548c7bc86987e88110bf28443bf41906faa808774c730ef98a617d53906fca990df15031bf28643bd41d02faa3215fd4d42efa1a877f52843dca4084f55231b729021be41102faa8985f94c40fa908437d50906fca1085b94a30bf29e41dc430caf8a498df94421bf2a261df318c6faa2105f54342bca80655c53487de84a17d54432bea8c817e540c3dc84215f94730bfaa0637d53c43b86518f74c030bea84657d540cafca618d794c10bf298877f53886faa890fe10310fca8043de53042fca1995f54332bd280437e51d02f8a098df15330be28a873c544c3f681105f14f10fda0481f531886fea6085f54331be2a4617e5090efaa7205f94a10f7a1485dc324c2fca890df14e10be29e437d520c6f8a8085f94630beaa0417e53d07da64197bccb20b6a9461ef21c83d865905f94021be2a2657f53882baa720ef95010afa9a85f531486f8a5885f94f21bf28e87bf41502fea8194f95010bea8085f840482f8a6085f94840df21c817e508cbf220085f54910bfaa0215c5350bba8621df94342be2a663dd53882fca318fd94440dea00817c53c82faa0195fd4d41beaa241f7318c6faa998fbc8520f619241ef324cbbc64995f54e20f7992415e53906f8a2996f50c43bea8e417c52442fca1185f15321bfa9a817651102f8a9905f14542faa0e217e52087f680a05f94443deaa641dd530877e84a0fd8c621ef18261f95090b7a87a15f54840beaa0437e530cbea82885f15120df21e83bd54042fea9197e880209eaa0217e540cbba86985f94e10bfa82436f524c6f8a8195f55232f629263f7314c77c86205fd5021ef29c837d5490ff2a0195f94a41fda0021f631486fca120f74c931bea8c217d53d0afea4a06f50941bea84437d544c6fca6186f10d41bf29a437d54906fca420f714d42aea9c41df434c6faa5984f55032dfa04817d510cbf460185f54b40be2a221ef21087ea8220df14c20bf29c43fa20843dca5187b0c821bf29c837e54c42fca4105fd5121beaa4217e548c3ee8320df94410bea9c857f54442fea4a1df14d40bea8e877e500c3dc64195f94831fa98863bd4350afaa1a0df94341be298437a5090bde6410dfd4f20bf28e41ef328cafaa5085f54a20bea84877e52c42fca9905f94810bea9687df310c6fea9885f548419f2a0657e548cafea0996fd5130beaa061be41507b86418df54a43bf29e85fb308c2faa2185f94a30bfaa2417f52442faa990df14d42bf296637d52cc6fca3105f54343bfa9021de324c3be6598df14930bf2a6637f53c86fca5a0df94641
  | 1 => 0xd518cbf620885f15310bf29a41de328c6eca2197794c40bea9c21bd41502fea8987d54440de20c817d5210efca918f7cc730dfa1a856d52042f8a9195f95210bfaa441bf4310ff640907e84010baa8881bf4210bf460905f54f41bf28c43f920442fca6105e54021af29881fa40103f4a010df94d10eea9881ef2008278a8885fd5332bea94617e52cc2faa6215f94832ee98a61df320caf8a8185f94242de208817d53042faa3185f14520bea9843ed52042f8a7106f95231be2a4217e544c77ca810df54d20bfaa2637d5010fec6218df54643be2a2437f514cafca621778c531be290217e5410ff681885f54d10be29a41df300c27ea888770cb30bf284417f5150ef0a0a0df94a31be2a043ed20082fca321efd0441fb884217d528c6f8a4a1fb88521fb082217a500cafaa790dfd4931bf2a0417f544cafaa718df14d10bfa8287fb40482baa6205f54242dea10857e5290b7e83a04f95320bea80637f548427ca918dfd5221bea9e41df43cc6d8a498df55230bea8c41f8408837e80205f94442bf28c857e50cc77c86a1d754c10bda8283dd53042fca2205f94231bea8e817d54ccafca3995f94a43fb28865be43506f8a4a0dfd4540bf2a0857e500cafaa7197710e32ef29c417e51082faa690df94a32f6194433e54087ee4290fd90710df2a0657e520c2fea8187d90510ef984617e51d0af8a0a15f55320bea88877d520c3da85905fd4c21bea96217c514c3be8721efd0a40beaa4437e5390efea7085b94840dfa14853f544c37887a0df94f10bf290877d50086fca7105f55031bf28021dd43cc3dca4205754c21be2a4437e53d02f8a898dfd5321bfa9283dd32cc6faa9105f95220fda8283f940103dc859077d4d21f6a124175510cafea6885fd5331bfaa463bf42102fca9996fd0e43efa18657e50107ec8220df55231fd28065ef20883f240107e10010beaa4857e5010afca5a1df55132de21c81f721886fca620fd88421bea9c61f9300c2fca018df94040be2a665de320c6fea9987b54840beaa2217c54883dc84905f94c21be292817e5390afca8905f54e21deaa463ee20482fca4215f94441bf2a0437e510c77e85a0dfd4d20be28283be4250b7a85207bd4931bfa9e21fb10843be65197bcca21b6a90817e510c2bca7105f55310de2a221ef21887f660986f90640fba0a837e50902fea8105f94020bea94817c52842faa620f74c832bfaa641f920842fea0a15f15130bf2a2217d52d06faa190ef15130bea8e85ed21c83bea6a17790c43dfaa221fa5090afca72057d4d21bfa8a41dd310c6fca2195f54442fa88021dd53907ee20085794c21ef196617e540437886205f55330bfa8a85dc43cc6fea9185f14d21df2a6417f514c2fea0a0dfd4b10dea0883be405027aa9905f94b40bf29821ed21483be6498ef50840be28
  | 2 => 0x1c4bd000092c4240040101c31054010001a00000004000183d22003020010c0a302c0220c1c0bc3a01c4d018150080f0003e0080c0681f03405120090187a0980002400026586b00501000001f20000a01c17154000340d0400803c0203c1a1640207c0a55800004030c80421026120130003e01000044cd03c120240501c0b04c07000020440802c1001c0904009000381c82f05016104510080004400008033c40b024020003a00c000080004c0900c380b801000030000c0000e1900b0041507800028f201c290a85212c0e0001e004020cc030100c11800000080001101001000080085208000004010dccb094040100002cb4030120104400013010100041305c010023800019001980100b010230200309839010000d8b10000a01004be28243de53086fca9985f54041bfa92617d53102fca818df15020bfa82637e5010fbc87986fd0f42bf28c817e52442fca8205e54242bfa98417f53486f8a710fb54a30ee21a63f930882faa3986f550329eaa0437
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x324c35a6394242c714f4350a3f6454332d310c524c63d6414c10c7952530436952440109b58a544c6ea60909209798c548434e53948409e583548ca756195132b9584324827661150309d58453083573254432cd545401027761551209d58754cc35a5394021da588505067960150319798f548863e64951309b98854842766115220c755253086ce628c130ce152204423e6414c21ae9824250b4d5354840d554d210873854481109e596100433551d00409758f52042766114c208f19150cca3d6494820ced08505067a60d50329d584540cad5610c93097d8d544ca7b60552219b594320874d53948409bd8953487365494432d354f32087695284010cd552510ca7b60551219718d54c863c6454e109d984548c23d64947309e195304825e6314141d394f20883356115110c754e431027a6014c218f191534427461551209b98b548c35a63141419e594400423e641481097594430ca6e6214810ae191308832e5450b209bd95200825e63d5031cd951510cae4624c62197d8d52d02b8644c1208f994544429e6390541c755153042ad640cb209bd89544c6756114f20a718d425065d6314b10c7951530425d63d4a108f191534833742544408f191524423d659502197d8d524427a60148108f590530826d6594810bc58440c431d5350840d54c9510cb7151540329798e534871e53d06418f590524c7355444010b9584328865e63d52209758f540871c540c9309d984540425c63551209e58354c865e63d48108fd91538427465505108f992510c67561d50328fd954210acd6210c3297d8d52c433942141419b58a50cc6d5610c8319d98754cc23e64d48108f990530431e54cc631c7951530866e6214c10dacc9500867661150208f990524c63e65d0540d3d0c524c74c528c5319dd95310c65f63553219d584548823e6414f21bc584408825d6394321b958432c833954d00109e18154887c7324c6219b98b540437060544409e98354cc66d62d5010cb590524c63e64947308f593538866f65484218f191508865d63951218f592510c63f6454031ce55250086d661d0d319e181544867a6014c209dd95100425d63141418f59353c823f6550441bc584404827661150329758c540874c6254c21cb990524c65e6394020ae181411069c6350b41ec50740c423d6494d108fd91534825e6314c109b588548433554c40109758c548827a60d4c219b588540c31c54cc5309798f54c433a545402197d95310c63c64540318fd9152443595354021d510d510ca5c63551218f59352042796014f21c7950328c67b60551109758c540426f6254f109bd89534426f6550842d658c50506cc63484219798e51d025e63d50219ed95401025c6354b40ad986435063d65950329798c540826d62d4c108f592528c25f654c030ced0a5090a3e6494820
  | 1 => 0xb7251540329d584540826d6214c10dac85500865e65d0d319798c540c3364354440ae993204823e6494a3097d8d544825d6594c10c7551530865e6314b10ce90c505063f64542219758e500825e63d4a10d994a51103695210010c7553430cb5743544329e980524c74c52cc93197d8d54486ea628c1208f593530433a4114141ec90440c427b6544010ad185425071d6315130c7152324c36561149319e580530871d53d08409d987540ca3d6494a10ba988404836a60149318f99052c423d6414c219798e51d0a5d63d5010d6982538836552544409e583540866e6215230b318d42483655294440d354e520425d6594c21d354d520425d63d5220f10ca318863f6550c438fd95401027960d4c2197596320c67a60d50219dd95210869e63904408f596540425c6550d30d9949511027a6015032d5584534863e64d4c219e58252d0e796015021cd546411023e64150219dd85534823e6415032b3189314c2766114f20d554e210863e6415010b318d214825e63943219d986544ca5e6315010ce552500ca75611523097d95320ca3d65904409d185534836a6094a309bd95320ca5e63148109b98850507386055010da98850506d96310120a718d421025d63148109ed95200826d6294243d594e511023e6494d10ce951500cb1c5490d30dc946500ca6d62d52308f99251cca3e6494a10cb55252042d96310220a798e419029c6350a409b98a5090e3e64d4f209718d524436952d0010cb952520433542544409798e5090a7960d50329b189544c71c544c530d658e5090b384314141dc546500cb3a54940219e98252d069d640cb308fd9153442b96010c408f992524423e64d4e219b98b530432d54548109b988540c2786548110c7952328c65e6514d21ba980324826d62152309e580524c6f06050710cb951520427a6094b43f20c9304823e64d4f109798c54883555354440b3189310c7555394440b398e204823e65151309b58b538426e62d4e109dd9541106796094b419e980540865f6550c439e983548ca6e62943319b588540c74e52cc2309e980540c76921540219e58354cc74c524c931cb98a54c823d64949108f990514827a65d0120b6980324c25e65cc931cd10d51102ad640c920da580524c74c5388521b558432cc26e6215031cd551510cab86050740b318d42c827b60551318f59053c865c63548419798c530865e6314520ce153104425c6354b10ae181415032d6494a30cb9494210354538c521b5584328c63e6414c20cd152414436832540218f590520427a60d5321ce551500873a54940328f992544434e53548409b189534436a60948409b588505063d64d4c219e181544c72e6494a309ed95300c31d5494c10b318d21c827561150309758e51d029e648c5319e580540ca6e62951319798f540425d6394242a759
  | 2 => 0xe000d8080019000000a000004800292081810070506400000b16c0000000100601018180000000001e020282c0e01048040008010000211258000a000000000010001840000a80006080317c000c0108c34055e858000000838000404800020c081ac300a0483412020000400040500004c90100096013f03800030002c003600000020f00800000904800007501809a60000000000000000080000004000a000100002008000e0c0000016250080002030281002080180800053217c00000080002010a00c00041100020010500808150dd6c060500d8806900186c000103058fe080908408010327c020000000060b0187c060000e5c0488429400636111b0121b640005c04570000600000000002598001504018540a270000c020300338160000834340600010008f0a80400020080802000000a6c65509209b18953c423d64145209b997324823e64d4c109758c514834e5394810d5145314c23e6414f20ea508404825e63150218f59251cca6d62150108f59053c82766114c219e98053c87395454032d694d308825d63152109798e544871e5494c219758f548865f6354841b318931cc26e62150209b98b530823d64d4f109758c540826e6215010d394d52043595394021cd544411035a5354021d594d511027a60d50208f59052c431c63550329d19531486ba64c82209758f54c42b864440109758e51d
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x25a002600000084432018a1915244010c28a8b08649851a73904505068a39a84a888185951610ca31c18a83126298616635464110350a12c220241461cd4214141d10c819260905457210d510ca58bb482206214c9c64314141cc2c2b00a498d89740c930482633b66498c438a5916014931c1cc82946298c1d76150324c324b1ac4282834c1c54214141c88c428a629854671d0c524c6a439a42a8043585c86054440a62e021aa2205887350840482e0b886498241a258d4210120
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x100c80645c4324c120a8083509611012088987190324c120
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
  | 5 => 2*((h/231+packedAt s5K5 (17064+(h % 231)*10) 10) % 632)
  | 4 => 2*((h/276+packedAt s5K4 (17974+(h % 276)*9) 9) % 473)
  | 3 => 2*((h/16+packedAt s5K3 (1421+(h % 16)*5) 5) % 29)
  | 2 => 2*((h/8+packedAt s5K2 (180+(h % 8)*2) 2) % 3)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfe1ffff03c7fc70f1e3f1fffc703f07c19f673
  | 1 => 0x1fe1f8ffc07ffff01fc7e381f803fffce6487f
  | 2 => 0x1ffe00ffff87f8ffe007fc01fffc7f83078f9c
  | 3 => 0xe00000fffff800fffff80001ffff8003f80fe0
  | 4 => 0xffffff00000000fffffffffe00000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x42443011809088030209048cc1189118089631
  | 1 => 0x84884122092300300c42211108212660624846
  | 2 => 0x48409244901401452005482452484909058298
  | 3 => 0x819564892841929a56900049a4b20232b80d60
  | 4 => 0x1119800e326624ec9926927000c00c43d76000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeeaf8c8feeaf8c8feeaf8c8feeaf8c8feeaf8c8feeaf8c8feeaf8c8feeaf8c8feeaf8c8feeaf8c8feeaf8c8feeaf8c8feeaf8c8feeaf8c8feeaf8c8feeaf8c8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37995
namespace PEqualNP.Outside.L_meta_37995
open PEqualNP.Outside.L_meta_37995.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x2001400450403800c400a3a30002aa282140040000089040027fd5001fd3100ff14005fe5200ff04005fd21017f88405ff2100ff4c00bff5300ffc8003fc40017f90809fe41017f8c805fc4200ff94007fe53017f08407fe43017f54805fc52027f1040bfd5100ff08009ff4101ff14c03fe2000ff90003fc3001ffcc40bff51017f50809fd41017fcc807fc4300ff44003fd5000ffc4009fc5400ff8400bfe51007f8c403fd40027fd0c03fd20017fd480bfc5100ffd4009fd4300ffd0009fd54017fd0807fc31027f95005fc32017f4c803ff3002ff54c03fe30
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x4007854100030080c6820183c009c6000080010d02e480080001404080c04100c18000404016c040c001400040c008d5ccc98002148080004180c1802c84ca064c0e00188280064057e312620bffd8a31057fcc11882eff628c407fe18c620dff59631067f8c918812fe648c40fff2926203bf9863105ffea51882bff208c40dffa026203ff50d31067fea918837fd518c40d7fb02620affd423104ffeca98833fd548c41bfe32c6207ff50931057f82118827fe514c40b7e32c6203ff8ca3101fb86518837ff518c417fa90c620affd8231055fec118806fe608c4137fb2a620bff94a31047fa8298806fc608c407fea1c6200f78c531037fc8098812fc648c407fb98a620affd023101ffc649882ffd428c407fe9846209ff1953103ffcc498823ff544c407fe992620bbf58a31037fc409880ffe434c41bff28c6203ff14d3101ffc8718833fd418c411ffa0a6207ff1493104dfaca9881bfd604c407ef98c6209ff5953101fee631882bfe408c40dfe2826200fbd893101ffe649882bfd208c407ff9946203ffcc131037fa409880ffc538c4057f3126203ff4ca31057f8c11882bfe108c411ffb22620aff8823103ffc429882ffc528c40dfe8826203fd0c531037fc209880fdc314c413ffa8a620aff1423103ffec498802ef624c419ffa0c6203ffcc23102df8ca98836ff658c407ff29a6206ff94131057fa2118823fd644c411fe20a6206ff54131045fec89880fff534c417feb146202bf18a3106dfacb1882ffc628c407fa18c6207ff5493104ff8a298822fd644c40dfe3026207ff4853101ffa609881afd604c40f7fb12620aff94231067f88318837ff658c415fea84620bff8863101ff8611882bfc208c417fea946208ff99131047fc829881bfc204c40b7f32a6207ff9093103fba6498837fe658c40b7f32c620cbfd923105ffa4318823fc544c4037e3026208ff5513101ff86498837fc518c407fea9a6203ff10d31067fcc918833fc548c40fff90a6209ff9953101dfac71882ffe428c411ff2a2620cff90631067fca91880ffe314c417ef1946203bfd8d3101ffe629881bff104c407ef9826207ff5893103fd8c49882fff218c407ff29c6203ff10e3101fbe649880ffc328c407ffa1a6203ff54e31037f8809880fff538c419ffb24620bfd8863101ffc609881ffc424c4057f3146207bf5893101ffe6318823fc644c4077fb0a6207ffd0931037fcc098832fd648c407fe182620aff1023105ff8851882bff108c40576312620bff0863101ffe871882fff428c40dfe0826206ff5013103ff8c49882bfd408c407ff1846209ff54531057fac118812fe644c407fe18a6204bf1913103ff8429881bff204c40ffb10a6201bf9813103ffea49881ff5214c419feb246206ffd8131055fac11882ffe628c40dffa826206f74c131
  | 1 => 0x4800007c693c38980002201026481000200c002c3120000014043c1c1c04000
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x183c10304002ad2431b861874a0e022c6000074000820020030243b5021c0000008094095a4d80c10e0103eec71d8931006ee51d8931006ef41d8931006ed65d893108eef31d8931006ec65d8931006ec50d8931006ec64d893105edc628c531006ec54d893108eef71d893101edf618c53108eed30d8931006ee10d893103dee76d8931006ed74d8931007cf628c53108eee30d893108fe431d893108eec30d8931006ed75d8931085dd728c531006ef65d893108eee31d8931006ec60d8931006ef74d8931006ec74d8931006ed54d893107fd6218c53108eee43d8931007cf73d8931075dd708c531006ef54d8931006ec51d8931006ec41d893103eed73d8931006ed10d893101fd7618c53103eed71d8931006ee70d8931006ee54d8931006ee65d8931006ee50d8931006ef40d8931006ec75d8931006ed50d893100cde768c531085df728c53108fe771d893101ede768c53103fcc73d893103eee71d893108fcc31d8931006ed40d893103eed31d8931006ed51d893103fe471d893103eee76d8931006ee60d893108eed43d8931006ed60d8931006ed64d893105ecc628c531007cd30d8931006ec10d8931006ee75d8931006ef51d8931006ee64d8931006ee74d893101dde768c53108eec31d8931006ed70d893108eef53d893101dde718c531006ec40d893107fcc628c53108fe731d8931006ef10d893105ede628c53108eec43d893107fd5218c531006ef75d893108fcf30d893108eef30d8931006ee41d8931006ef50d893108eee53d8931006ef70d8931006ef64d893103eee73d8931006ee40d893108eef43d8931006ec70d8931006ef60d893108eec53d893103eec73d8931075df708c53108eef73d893108eed53d8931014ee76d893101fd6718c531006ed41d8931
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x24300000400a040381000140040000002a840000010080001c538100600038000018000716aa0a9b126200a6e859d3624c4015cd02206c49881f339db628c53100477c3ac9b126200a6f855c3624c4014db0b326c498802aba1351d89310053642ae1b1262008ee87043624c4011db0e206c498802b360c10d893105d67436c518a6200acd83103624c42359d06286c4988029b61410d893100573408a1b126200aac845c3624c42359d06206c4988023ba1c50d89310047743881b1262078ed87043624c42359d06386c4988029b21510d893100556c26a3b126200aaf845c3624c40155b08086c4988029b61440d893100536c2ce9b1262008ed87983624c40155b0932ec4988029be1510d893100566c18e1b126200aad849d7624c4014dd0a206c49884b339d930d89310053742e83b126200e2f54953624c40155d0932ec498802b360c50d893100536c2e83b1262008ed87997624c40155f08b06c4988023be1d60d893100476c3cc9b126200ae581103624c40155908b06c4988023be1d65d893105e673b6e7b126200a6f85583624c40155908886c498802b960450d893100476c38a1b126200a6e85043624c42359d06086c498802abe1110d893100556c20a1b126200a6c85583624c40178902986c4988029ba1664d893103d67436e7b126200aae84143624c40155d08086c498802aba1275d8931
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x122f9855054d8931
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x3
  | 3 => 0x4
  | 4 => 0x5
  | 5 => 0x6
  | 6 => 0xb49
  | 7 => 0xb4b
  | 8 => 0xb4d
  | 9 => 0xb4e
  | 10 => 0x1449
  | 11 => 0x144b
  | 12 => 0x144d
  | 13 => 0x144e
  | 14 => 0xb5451
  | 15 => 0x144b53
  | 16 => 0xb5453
  | 17 => 0x140c
  | 18 => 0x9cb
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 206
  | 6 => 102
  | 5 => 64
  | 4 => 1
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
  | 8 => 2*((h/34+packedAt gbK8 (1560+(h % 34)*6) 6) % 60)
  | 7 => 2*((h/103+packedAt gbK7 (7622+(h % 103)*8) 8) % 206)
  | 6 => 2*((h/48+packedAt gbK6 (4896+(h % 48)*7) 7) % 102)
  | 5 => 2*((h/49+packedAt gbK5 (3776+(h % 49)*6) 6) % 64)
  | 4 => 2*((h/1+packedAt gbK4 (70+(h % 1)*1) 1) % 1)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xc3fff0f0787f0ffff8e01f80fc51067c19f673
  | 1 => 0xfc380f007f87f0e03f001ffffcae3990e6487f
  | 2 => 0xffc00fff8007ff003fffe3ff0330c1e3078f9c
  | 3 => 0xffffff800003ffffc0003c0fe03f80fe0
  | 4 => 0xfffffffffffc000000003ff0003fff000
  | 5 => 0xfffff000000000000000000003fffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x40486030080901219820c48218000224089631
  | 1 => 0x84108300308210422101092ce0061890624846
  | 2 => 0x6a8124548005aa048a4a425209304161058298
  | 3 => 0x249a95d5000093495900432c0ae02b80d60
  | 4 => 0x22040ece6666cc9e0006001843fb0003d76000
  | 5 => 0xb327800c044088100018006083fdf5d8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefeeafeeaf8c8feeefeeafeeaf8c8feeefeeafeeaf8c8feeefeeafeeaf8c8feeefeeafeeaf8c8feeefeeafeeaf8c8feeefeeafeeaf8c8feeefeeafeeaf8c8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37995
namespace PEqualNP.Outside.L_meta_37995
open PEqualNP.Outside.L_meta_37995.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs2_2_0 : Interval s2Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 6 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 56 := block_range (n:=56) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 56 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_96 : Interval s2Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_192 : Interval s2Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_288 : Interval s2Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_384 : Interval s2Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_480 : Interval s2Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_576 : Interval s2Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_672 : Interval s2Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_768 : Interval s2Atlas 4 768 13 := block_range (n:=13) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 781 := (concat (concat (concat bs2_4_0 bs2_4_96) (concat bs2_4_192 bs2_4_288)) (concat (concat bs2_4_384 bs2_4_480) (concat bs2_4_576 (concat bs2_4_672 bs2_4_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_96 : Interval s2Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_192 : Interval s2Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_288 : Interval s2Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_384 : Interval s2Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_480 : Interval s2Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_576 : Interval s2Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_672 : Interval s2Atlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_768 : Interval s2Atlas 5 768 33 := block_range (n:=33) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 801 := (concat (concat (concat bs2_5_0 bs2_5_96) (concat bs2_5_192 bs2_5_288)) (concat (concat bs2_5_384 bs2_5_480) (concat bs2_5_576 (concat bs2_5_672 bs2_5_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 44 := bs2_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_7_0 : Interval s2Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_7 : Interval s2Atlas 7 0 1 := bs2_7_0
theorem alls2 : ∀ k ≤ 7, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_2 i (by omega) hi
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
  · exact alls2_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 8 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 92 := block_range (n:=92) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 92 := bs3_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 44 := bs3_5_0
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
theorem bs4_2_0 : Interval s4Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 3 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 29 := block_range (n:=29) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 29 := bs4_3_0
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
theorem bs4_4_384 : Interval s4Atlas 4 384 89 := block_range (n:=89) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 473 := (concat (concat bs4_4_0 bs4_4_96) (concat bs4_4_192 (concat bs4_4_288 bs4_4_384)))
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
theorem bs4_5_576 : Interval s4Atlas 5 576 56 := block_range (n:=56) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 632 := (concat (concat bs4_5_0 (concat bs4_5_96 bs4_5_192)) (concat (concat bs4_5_288 bs4_5_384) (concat bs4_5_480 bs4_5_576)))
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
theorem bgb_4_0 : Interval gbAtlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 1 := bgb_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_0 : Interval gbAtlas 5 0 64 := block_range (n:=64) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 64 := bgb_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_0 : Interval gbAtlas 6 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_96 : Interval gbAtlas 6 96 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 102 := (concat bgb_6_0 bgb_6_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_96 : Interval gbAtlas 7 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_192 : Interval gbAtlas 7 192 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 206 := (concat bgb_7_0 (concat bgb_7_96 bgb_7_192))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 60 := block_range (n:=60) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 60 := bgb_8_0
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 8 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 8 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefeeafeeaf8c8feeefeeafeeaf8c8feeefeeafeeaf8c8feeefeeafeeaf8c8feeefeeafeeaf8c8feeefeeafeeaf8c8feeefeeafeeaf8c8feeefeeafeeaf8c8
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
  have low := boundgb certgb allCuts
  have lift := lift_ok (u:=true) (ms:=fixRows 0 0) (raw:=fullRoots) (T:=fullWord) (xs:=[]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 0 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075690 * 2 ^ 32 + 4276811976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37995.Model.Repr at out
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

def mono : List Gate := [⟨.and,[1,3]⟩,⟨.or,[0,6]⟩,⟨.and,[4,5]⟩,⟨.or,[4,5]⟩,⟨.or,[2,8]⟩,⟨.and,[2,3]⟩,⟨.or,[0,10]⟩,⟨.and,[7,9]⟩,⟨.or,[11,13]⟩,⟨.and,[1,12]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276811976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276811976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37995

open PEqualNP.Outside.L_meta_37995 in
theorem PEqualNP.Outside.L_meta_37995 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276811976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276811976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
