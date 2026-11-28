import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37997.Model
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


end PEqualNP.Outside.L_meta_37997.Model

namespace PEqualNP.Outside.L_meta_37997
open PEqualNP.Outside.L_meta_37997.Model
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

def SBf (j : Nat) : Nat := [8, 5, 8, 8, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_37997

namespace PEqualNP.Outside.L_meta_37997
open PEqualNP.Outside.L_meta_37997.Model
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
end PEqualNP.Outside.L_meta_37997
namespace PEqualNP.Outside.L_meta_37997
open PEqualNP.Outside.L_meta_37997.Model
def s1K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x9d43
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (i*5) 5
  | 3 => packedAt s1K3 (i*16) 16
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt s1K4 (5+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/1+packedAt s1K3 (16+(h % 1)*1) 1) % 1)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x7ffff83ffff83f07fff07fff83fffc0f39f3f3
  | 2 => 0x87c1ffc3e0fffff8707f8783fc3c1fffd64c9f
  | 3 => 0xf801fffc00ffc3ff807ff803ffc01ff0e78f1c
  | 4 => 0x1ffffff0003ffff800003ffffe000f80fe0
  | 5 => 0xfffe0000000003fffffffffc00000000fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x800880400040008090088880444422009131
  | 2 => 0x2112910909522128342485112428894c524486
  | 3 => 0x12a52290d2a406538859502aca8152a2a58b18
  | 4 => 0x5539c42a9836ab9d5d0c4443733380c4f80ec0
  | 5 => 0x663187331cc733e66e6e667062220308ff6000
  | _ => 0
def s1Atlas : Atlas := ⟨4,rawDecor 61 s1Pos s1Neg, 0xfaaafaaafaaaf0a0faaafaaafaaaf0a0faaafaaafaaaf0a0faaafaaafaaaf0a0faaafaaafaaaf0a0faaafaaafaaaf0a0faaafaaafaaaf0a0faaafaaafaaaf0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37997
namespace PEqualNP.Outside.L_meta_37997
open PEqualNP.Outside.L_meta_37997.Model
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
end PEqualNP.Outside.L_meta_37997
namespace PEqualNP.Outside.L_meta_37997
open PEqualNP.Outside.L_meta_37997.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x1c000c0000880980020423c0380003480009fc30fc20dd32ff10fc32fe21fc40ff40fd42fe32fd30fe31fe41fc31ff32fd32bf42ff43ff41ff21bd42fd31ff42fe42fc10fc41fe43fd10fd41df32fc43ff31fe10fd20fd43ff30fc21ff20fc42fd40fe30fd21fe20fe40
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x821dc53442faa2207714332deaa641be5050b7e85996f95320b6a90617e54486faa3186f14142dea12617f53087ec83886f95010beaa243cd32087f44108774cb40dea12637c54886f8a2986fd0932dfa10637d544c6fea6a07790f32ef99083bd420cbbe6318fb50842aea9c857e518cafaa118efd0f42bfaa2617c53c877e84186f50a31efa1c87be5150bba65885d94440ee21e63dd438c7baa7906f50921dea1661cd32886fca8907794e41ee990813e54c877a87a05f94e20eea1e61bd439077e84197715332bea9885bd42902fca910fbc8220aea9c83bc43103b8a3995f94e43bf284657e51c82faa6105f54c10dea8e85ee52043be65885f14520bf29487ee42c82fca618df54420bfa9e417c5150efca8887b54830beaa065dd320877ea4a15f55031faa8861ee4210afaa7106f10640be2a0617d510caf8a610df54810f690a415e53d06f8a0a17794c20bf2a0617e50886daa5a0df55132ee990217d52c42bca610df55110dfa14417e500cafea8886f50941de2a2217f504c6faa9185f54620dfa12417d528c3be64085f95232bfa96217f5050bde84a17d94420bea9c61ef21c83bc86995b54b31bea8485de430c7ec43887bcca32bf29e41be43902fea4a0df55130bf296215d5310bba64a05e54021ee28a655d53c877aa7a15f14e109f2a06575510c27aa9215f54610f799265df314c2baa6205f54642bfaa6657c54cc3da85195f95231dea1465bf4290afaa01977d5132bfaa4616e52d06f8a2a16fd0d42bf29a218d424cafea6887bd0a42bf290817c548c7bea1996f50b32bfa8a817e52106fca0087750f32dfa16837e52083ba86997754c42ee21a63dc438c37a8418f7d4732ef29e413e54c839a65907750c31bf29c83df32d02fca7215f94c40bf29485ed424caf8a4a1df54720f7190657e50cc7dca421df95330dea1061ed320cafca5986f50c43bfaa4417e53082fca01877d4d10ae29a21dd5390bbe64106fd0b21b7290617e53c87ea20085f94021f7290817d54043baa2997dd0541bfa9221f910043da64907b08420aea9e41dd32082fca1215f54e31ef99483ed52043be639867d0b32bea9483be540cafca3997ec4110dea82857c544c2f8a4a0f74ca41beaa0437c54482fca120df54043f7192417e510c2faa7a0cf55320bf288635e53043f420087d88421b729663fb10842fca3a1df54a21f7290617e544ca7aa8105f94c30bea86657e54c42f8a9106f55231bf280817f54887be6410dfd4a10bea8687bd42482faa998fdc4210cfa12657f52043f480205f94043e6a1265ee21082faa5985f54321bfaa0637c54842fea790df94342bf2a0855f53502f8a818fd54420f6a12417f54cc3dc85197b90932df212857d53d0b7ca6a15f94842beaa6657d50cc77aa80877d0f32dfa1081df328877a851077d5332
  | 1 => 0xe5410edca4085f14c20beaa463bd429075a85905fd5310bf280637c54c8778a1a15f15032fa98a217e54ccb7aa2a15794c32bea8443ee32887baa720fdc8521aea9c65bd42d0378a6a17794c42ee992837c54443ba65a0df15132fa90a217e54842faa8185f54c21fb18a217e51086f8a7105f55321bfaa4657e50ccb7886a16f10d41ef298217d53907bca2995f14540be282877e51106faa3997750b32df286857c54cc7da6410fbd4910bf28865bd420827ea8986f95231bf2a043de530877e82a05f14d42df21e83dd320c6eaa2107b8c821be2a263df320c27ca998df94740bf28c61de5390b7e84886fd0740ee990657d53886fca7207ecc230efa92657e54082fca12077cc831de20881be548cb7a8410df94910be29e41de53102faa4205f94641ef192657e51886f8a9997794f21bfa8a617f53c42fea6105f14e21be29a43ed32886fca610efd0a10eea9821f5414427ca8185f54e429faa2217d54cc2fea2a1774c830de2a261ed21c83f2a010f70c430ef21887f920082fea6086fd0c43be29263bf42c82faa7a07754f41ef99065af5250afaa321fe88020efa1861fb304c37a8510df14d41fba0c83bf4210afea4a1df14d40f6a9081dd424cafaa5085f54910bf280857d54902f8a29977cc940bfa9a85dd54ccafaa7086fd0a319f2a463be43102f8a6905f14910f6900417e5310edaa4085f94210dfa1261be540c37e85185f94d20af298857c54042faa1a0fb54b31bea9487bd540cafca418fe50040dfa0c83bd40103be64905fd5231eea1887bf424c6fea7086fd0921efa8a657d518cb7a8598dfd5132bf290877f54482faa421f74c920bf288217d53c86f8a0995f54f10b729081bf429037ca810ef55020bea9463df32103d843106f50a30bf29c21dd32882faa7205f55243ef994417f524c3dc8410efd0b30fd180617c52042fea908774c841bea8885bf53d0bbca0997d94430ee29a817d51d0f7aa6a15e94021be28283bf5050b7a86a07b88620bf29a437e528435a85194f55010ef212657f524c6fca2105f14121dea1883dd434c2fca7a15f95040fd904416d5210efea2906fd0040f719641bd424caeca2184f55232ef21a61ee42886faa690cf15130faa8881f721886fca8086f509109eaa0437e51d0a7aa998df95220fb20883ed32c82fca7a07dc4010ef99643dd53082fca2215bd4910bea8063df32d07ea6218ef10f41f790843bf42507dca598df14d10aea9843f9204437c82205f15021dea16417e520437e85196f50a10bea9881bd548cb78a2a1774cb21be2a4617c52c43f680a07715132fc980617e52d0efaa121ef90d43bea9e41ad42483f6409077d4132bfaa041de50cca7ca8215f94220f790c43bd4210afaa1a17b50b20fc90421de54ccbbc8718fe88110bf29461be54083bc87985f94243bf29
  | 2 => 0xc00356c116c0017c010041101c0a1f04600dc3010620bc2e0001b000030530d0000200403008aa0086838c090b00206c030180b0000105c3301002068063c80107007007d8a4887790b32ee994437f50487bc60986f50441dfa10837f54487b885996f14f42bf294633d540c27aa990cf15110bfa9a43dd51ccabaa6107d50441fb20a217e51882faa4185f55241bf2a261f531c42baa7a0df54042bfaa2637f50506fea81977ccb20ef996633e540877c80a07710d32bfa9c435d530437887a17710c30df2a643dc43ccafea6907794f41beaa465dd314c2faa1197d48710bf28887df308c3ec63886f50b41f6a9683be43d0bbaa790ef50b21bea8c81de314c7ba6598df54443bea9883bf42043be869977cc431ef18c61ee204827ca8106b50932af29c83bf42502fca918774c910fb28881bd540c3be8798df14c10bf298657e50c86bca7905f54e32fb10a21ee42483be86a1f74c730df29e85ef214837ca998df94832bf28c633d548c77e81205f14a10bf28c81f541c439ea4997755132df21a837d52cc6daa4206fd0b10be2a0417d52d073a85997714132bfa8a657e508c2faa010df55220bfaa061bd415037e8620ef50d42bfaa663ad42086fca990f74ca10cea12657d54887f6812077cc910bf28e615f53442f8a7885f94b40af29c85bd43d0afca5195f94440f7900417d51cc2bca61077d4d40bea8e85bd421037ca3a15f54d10bea94817c504c6bca6205f55120fd280437d520c77a84a077cca10d6a14437e520c39a64906fd0b40beaa4857d528833a8621dfd5021bf28683be41902fca710df95032be292617d510c2fca7a0f7d0d31ee99641dd504cafca9907d48421bf29885bd42106fca3215794f21ee18c617e508c7be6498df54b40ef99465bd54087be64985fd4543dfa1663bd41d037e8520d714d40dfa1c877d52d0fba6218df94020beaa6217651082fea4a06fd5110dfa1a81df328c3bca3996fd4542bf28083dd324867ca8087b94b41ee212656e5210fbe6518ef90541ef99661dd328c2fca7885f15320b629221dd324c2fca321efd0820dea10217d52107ba6598774c931dfaa261bf42087be87185f54041bfa9c4175511037ea3a16f54342dfa9a857d51d02fca598fb48421ef99243be4350bbaa620774c030e721265f7314c6f8a9195f15121eea8665bd54c87ba6518df14940bfa82877e52906fca898df54d20ef99481f610442fea6a0df94821eea98437e52d07da8410df55210fb98c63de544cb7e87a0774ca40beaa641ee214877e8510f7d0b32f6a9087bd42c42faa120fb50a21de28e85de310c2fca818f7cc030bf2a0837c54c42fea0995fd5320de21c817e50d0f7ea1a16fd0e419eaa0657e53107be849977cc941beaa041bf411067ca9195fd5010deaa6637e54cc6fca5205fd5321fb188637
  | 3 => 0x30580904421000080000604ac500026070c70280f08400011b600c010b0020f03b080480040006c00304120240001d240080001c0000020004020000004c8000012000100041535400002670080308c04000792b0010780c00a177b01c0003300800000010000128c240251925936528200000513820000020ec0e2840700c1802031058000401f00c2a05c51000190a0120080d05c0b0902105800000000800301421114001e0120000600c04010410100200005000010c804020070000010426006c302c07028000000015805b3cac200010c840050760d002170a40000e0000101400004ba00011000544b4c4000000101900005000d300ad00007b5c424000220040b000187442102002030661f0bd5fc000041d516380741c0300102002008003f803038ea130140881a01c0709409020100000b0017b0580319001134090102502801004110081e049a80f0130
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0xb314c29e63909428f592528c26e6215020a71814310e766114132d394932d069e6314342c7152304c23d6494831cb951520434d43548438f994544431c54cc9308f992530c63d6215130b598754ccb8d42109329798f540c65d6294e4197597321023f65508429759732d071d544c03097d95320431d54cc8329b98b530431d5350820da8c9500874c4354b31e350b504ca3f6454d10cd584544432f52509408f99053c869d63d47428f992528c34f52cc910cb549420434f524c9318f590514831d54cc810d34ca51c83355494420e3981424ca3e6414910d354932d032d64149109b98a544434f53d4910d3549320426d6215330e3509320834d52ccb41cd952510c27960d502197597430c32f54d4910ea181424831d6395231d3949320425c6354342cb55152cc74d53948408f994544c36551c8020d994a511031e53508209e98052042cd6210f318f197424432e4354840c7951320425e63153219d5845050fe12148110cd509510c25e63150208fd91500c7715148020cb195424825f6355220d394d320871f53d0910cd54740103a742484218fd91534825d63d53109798e544423d6414c108f992520431d53d0b21d9546210826e6295131cb949429034c524cb10c7551530826d6214141a758f411066d62d5030a7992310c25d63151208fd89548c65d63947409718d544423f6454e10f14ca210871e53d0a41c714e405029c6354142cd50a510825f654cb41d398d52103553294430d3149324434d5390842cd15241442ad6295231e3509320ca3d6414121d54c9511031d54ccb219b58a534871d5350a418f99252cc31c5450c319798e528434d53508429798c525072e5250b41c7550544cb1c544c910cb50d5210f4d5308420da4c9500865c635522097595329074d52cc830cb54b42cc65e6394820d398a5390b4c53d49109e580540865d65cca41ced0a50086cd6210e308f992538865f635404197d89530432d548c8328f992534871d544c820a7993514cb2c64d49108f99251cc23d6494e21c795153c878d424cb208f590528434e6294c21a758e51d0a7561d5030d354d52d06d563905109798e534431d544ca31e354d42c834d53908219d98753082cd62d53329358a539065d63d53208f191518825e6315010cb50a51c836552c4010e350932cc76551480209798c524432d42145209d19521442ce6550932c714d435032e5250810cd95151082d56390710e350d5210e756114c20cb54d420871d54cca32cbd49424c72c54149108f997424c34d524ca10d3549321063f65508308fd954310e6d65884209b988530834d63948409798c520432e5250b3097d8d544c23d64d4f208f99251cca3f62550109b588548c25d62d4d10c754c411025e65cc9408f58a540c23f65504418f59252c434e524c841ad5865350b573294440
  | 1 => 0xc25d62d4d409758f54c863e6414f20c754f42c82766114143d3d49324434d52cc0308f992528c78f424c9208f592528c65d6394b10c714f435031d5494c219758c504863f6454e20ab58843d074e6394810c7553320c34c524c931c7951320834d524c840c7953318c66e6294910b5584504ca3e65d0d409b98a53c423e6494831d24c9500865e63d5121d354b32cc72e52508319d984540c29e6314142e350932d072942540218f58b544430d5350821b358b318c65e63152208fd95420831d548c4308f990524c25d658c4308f590504c63e6414e20a7990424ca3d6255020b35885350335429444097d95320831d5390c40a799351ccaaf6550b209798f540431d5350840d3549329025f63546209b58853503a942940219b98a534431e5350810ab592424835553944209d58454083395454021e3185424cb2d54548309b58854cc6d56195132e3d0d424cb1e544c821d5544310c31c53d054097d97321038e544cb209798e524427765484219b988548434d524ca30c754f4290a6e62153309d9845050b2c5250941e390d424cacd63c87209b588530423f6550a318f596540872c52d0910d394e521025e6394a409e983540869e648c630c7951438c7573254420a799251ccb4e6294e41e950a210865d6594c109bd95210872d5250a30d394d320cb2c6550932d390d5210f1e544cb219bd8951903355114542cb949428c34d6294e41d9549511026c6254d10cb549420c33654544308f597420ca6e621503197d89539062d6215130d3d95320869c6454132a798e5150b8f6150932e3509328c25d63d5020c718d540c2cd63c8621cbd95424832d52d0040c7550430c23d6414132cbd49424426d62951108fd8954cc71e53508429798f5150b5743544308f592524423e64d4f10b3d9532c823d65d08209758e52d038d42141328f59053087595394021cb149424c75a53940219759532d065e63d53219758e548878e61509329758e544871e544c83097994434c65d6394841d398e52103ab60509208f590524c69c6354342d54c9510c25f654c431c7153314c2ad62d0441ba580218838d424cb30d394932902d661951329798f54c423f6454221c755054cca3d62952319d984530834d5350821d358e520431c5450d328fd95401025f65cc8108f597420878d42cc821c718d54cc71e5454f209b5885050f1c5350940cb54942903553294420b3987524cb4d6214d408f596540c25e6514d10f24c9500863d629533197195324431c5450d30c754f420423e6494832e3d4b424ca3d64948209758e52086d561cc831c795132c82cd63c8520e3d91424cb4d635481097d95329074d3214520a75924310e5d63953108f593530435551cc0309b988538426e6215032d394932d023d62d5130c755253082d4614c9319b58a534432e5494810b358
  | 2 => 0x63d5021ab592320865e63d502097d8d50d0b2e5450a329ed95200831e53d08208f990540874d534802097994424cb374254430cb55132c834f654cb208f992534431e53508219718d519029e63d4742d358d521029d64cc431e350b514cb1d54cc8219758a530427a60150319758c54c874c654ca21e3d51424cb4f654c920d394d520425d6394820d394932082b46150941ad98753d0b645288510cd95251082796014c21cb54b421029d648c932d394e520432e62151309d584548826d62d4c108f990540c26e6214810b3583524cad461541329b98a54c426d65948109798c544831e5490e319e583530871c544c930ea50b204829e6390541cb90d52d06ad6294d42cbd95428866f6548020a798e411023d64d4f10ab593210869d63143429758e52043374294420a7d894310f4d3254221c794f42c863f65d0830f1cc9210866e62d5010c754f42907555354440dac8550086cd6390b20a7592514cb2d42d413297595320431d54d0f31d398a53c825d63149418f191518c32e64548439758c540838d60509328fd91524431d53d00409d58754ccab561d4f428f19150ccb4e6214d408f195424431e5454c20d64c9500872d54c8020c7952530431d43548439d984530431d5454c109d195414431e54cca329b588540c2b561d0841c754d4210b4d32944218f191524432e52d0810d358c524438d424cb10cbd9542c82cd638c920ad5845050a5d63d5221cb59152cc69e64141328f592528429f63543428f992544431d53d0820d3548310c31d53508219798c514825e6315021cb54b42042b561143428f59252cc31c5450f30c755332c825f63549109b988544c38d424c910e3d8d424cb8f424cb20c7d53324431e54ccb31cb991520c25d65cc820cd55110043553294440cb54b42d033554c4010c795253c863c6454e108f58a54043655294430cb99152d074f544cb20d394d32c83c93294021cb552210832d5494830add855050a5f6254c40c7d954310f2e5454830cb509508865d6254c20d3d0d520c23e6494b109b988504c73443544409758c548423e6414121b9586320871e5350b21cb949420825f635512097995325032d52d08419718d548432d5250a41ea509208432d5448020d594e510823d6494d21cb98a54087696014910c754c43d0a5e6315210a759331cc2cd6390920d3949328c32c54d49108fd95420863e6414d20e3d09328863e6414131cb50a510871e544c8329d987540835b32940218f990524c71f54cc930e350932d023d6590440b3195424ca7a6015021d34c9500873742944308f990538423e64d4c20c7152434c32d4254021c350d5210f1d5454f21d319532483394254021c7551530863d6595020ab58f5250b374254440c7551320cb8f6550932e3509320c74e52cc840e350a324cb3551904409b189518
  | 3 => 0x640ce552500875732544408f99054083374294440cd551510831e5350b20b558754cca5d6315021c754f42103692154021c7953320c34f544c920d354d521023d6494f109b98b54cc65d654c84097996434c3656114910e3509329063e6494a10c794f420431c54cc910c754d42d071f54d4d10cb54a411023f625502097d8d508865d6510c30dc485500865f654c840d95442108355514c030e350932c869e6494532d310d520c32d548c821e3509504ca6d629513197588535031d5410f32cb552520423f6550c41d394932cc74d5390b20e350932503cb604c9208f997424431c5350910d354e52d078d42ccb2097996424cb2d54548109b588538434f524c941ad98450d0b8d42945328f992520c38c4350932e9d8542886ce6210932c7553328c72d5350b20cb195428869e63947428f592520c32e52508308fd9742cc72d52d0830c7d50438c25e6314940cd509510834d52ccb309758c548823d65d08109d586544cb2d42542329798f540cb1e5454c21b358a544ca5d6395110f218132482ad64909329758c540432f52d0910d594d511034f544ca218f596431025d63153209798c504874d53c8020cb549401031e53d0842b3592424ca6e6214d409bd89518c25e6394b108f992520866e62141418f590520425d6214d10c7953328c63c6454d20a759351ccaad62d0740c7553320825e65cc53097d8d544425e6394810a758f41d025d6314810d5544514cb2f4354843c7952530865f63546408f590524c31e53d0b41cb55232c826e6214c108fd9150ccb4d524cb418f191500c65e63951218f99353c865e63953108f59353487655294440b358e428865e6314c20cb95252cc63f6550810cb551320871c53d0940c794d439078f6050932dc54620082ce6190932d314b324438d42cca21f24cb204826e62d5030e3509320426d6295310e350a504ca6c65509209d19531442766195132d3551320871e544ca31e3509320874d52cc831c794f4290a3e6414c219798e51d023d65d08309798f520423f6550832cb991520432e5454b31c7d4d425031d544c8109758e521031d5494f20cb10d521033a54540219b189519025c6355120cbd49425074d538842097997434c65f6254f419798e521063d6414910b3d95320863e64145209d984520438d4394843e3995424cb2d64548108f992520832d64948109e983530865e6394821cb94942cc78d42cc9209798c528431d5390f4193588535031e535083297997434ca3f6255030a758f5150a5d63145209d987540c38f6250932ad9865350a3d6494d10d9549510c32f65508219798e52d03695284010c7952530838d544c821cd545401026d6590821f24c920842b46154142c7d50534434d544cb20e3509328834e5394b41d510d510c31e535084097596530823e6415010d358d52d065d
  | 4 => 0xf993520426e6215331c795332c874e5354b41b358b310c72d52d0b41abd95420863c65d0930ea509204431d540c430ab592324823d6494c318f990530425e6314c219bd89534426d62d50108f592520cb8d42545329b588544c3e22188110c7d51324c29e63d4542c794f419063c6454d10ab58b41907555354420d5546310c23d64d4c21c7151314c31e53d0840e3d8942ccb0d544c821d3d4c524434f4354b31ab98a4350b1d5310f41b358f210865e6314b10a7d9150ccb5551147329d185534825d6294f41d358e52d07355494430a719150cca6e62d4543cb951420863d65508108f992544c25e65cc910d554f10042cf6255132c754f4210b573254430d354d42c831d5350b21b3588430c32f5414910d394932103a46150a2197d97329075553440108f592520426d6294f10c7953320869e6414332d5cca510823d6414f219e195204423e64141328f59053c829d6414332c7553430c34d524c0309718d524431d5314d42c754f42d071f53509108f59742cc63f6454630c795332c832f6550a32cb990524438d424c921cbd4d42c838e544c821a758c5050b4f654ca21c754d401029d63d0641c715053442ae6210d428f990528425d6314b108f993530429f6454132e318d424cb0d544cb20e3195424cb8d4214532c7551320c27b654c0308f590534835553944409798c5050b8e5350b20c754f42087665294430cb95142c832d5250b31e3151424cb1d4354043d394b32d063c6550930cb949428432f5350821cbd4d424823e64d4d219d984540431e53d08219798c54c833942940219e596100434e524c8309dd95411072e5494830b5d85504cacd6210d319bd95320cb1e5350b4197195434c25e6314c109798e54886cc6150932b358a539078c6050932d3149325063d6494b318f59251cca5d6394a41d398d52cc65d6590c318fd9542cc63d6550a318f990540cb5732944308f59542cc71d544cb319798e51d0a3f65d0a31e3585424ca3d64d4c208f597428c74e5354840c755043cc71c5450f329e580540c75532544209b195424cb2d53509208f99252442766114e20e3509320c2cd62cc730cb94942102766115220d394b320434d52cc8109d584538832d6295231cd544411032e52508329d584540c25d63d5010c7553300c26c654c920c755132c863d6414b109798f548873b4254021c795332042af6254d42c754c431025e63150329b588540426e65c8520e3509324c32d42145328f990520432f65509329b58b54cc62d62952318f995424c23e6494b318f596540cae56190821e3509324c74d544ca21975973208677654c431abd95428cb1d5314f42cb98a548cb4c53149109d984548c25f6550c319b994524431d5494f218f993514cb4e6314910cd54451d0a5d6314a109d584504cb4e6394b41c754e411029e6390
  | 5 => 0x4208769524401097995324431c53d0910b3d81424ca3e64d4e2197197324436942540218f191508863e64d4f20a7593318c66d62150318f997415031e5454c109b59632086ad60d49429d587540838e5350821a758e5150a6d62152109718d518823c6454e20ab588439038d424c9209d58753083374254420cb592520c34f524cb109d98754cca5f6254c20a7d954310f2f64d49109798c505063f6454620b3996424cb4e6354810ab588435072e5450842ab59321c832d5250b30cb54d428869d6494732cb94b420c27a6014c21a7592424ca776155120b398b434ca6e6215010a7d8d5050a3d6494730cb149424431e53d0e418f99443507c532887108f590530832d5250a10b558450cca7b6544010cb55021083c53288510d3d8f52442776544010cb548411025d63d4542ad59231c425f654c821e355132c831d5410d32ea509500863e64d4c21ab58b415025e6394b41b3988434cae96008420a718d401031e54cc832b598450ccb8d424ca1097597320426e6214143ab588544c27b6550040cb98a54c83355454430cbd4d42886cd6215332b398e424caad64c86219758a53102756115230cb99252cc7c93248110f1185328873a54940219d185544825f654c832e350932103593294021c7551320872f5250b109758f544869d64d45329d984540838d424ca31d354a310c38f424c821a7590504caad648cb20d3d49324c31e54cc820c714d415032e6494810c7d4f42503556114d109798c540c31c54d4d10c714d4350b4d524ca318f590538426d62d45438f588544435653944409758c525023d6595010ab592420871d5494c10a7593314c23d6414e209b58a544872d42946328f992510c6b5648c510c795253c825d6394910d594d510834c63d4910a7992324cb722154021cb94b42cc65c6354221cb992520c25e63d5320cb549420c69e648c531c354d42c823d64d4e218f595420c32d6494b31ab593214832d6215130c794f420cab66114142a7191300c38d424ca40e3595424cb595354021cb10d52d07665254430e350932106d66114132cb991521031e544cb31e3509325069d63d054097195434cba542887108f592520878f5250932c755132c834e6590932d398d5210e6e62150309b58a548c63e6494f10c755153c825c654c9409d5845050b5a53540219758e51d0aad62d4f42ab592328868d64909329758e529034d52cc840d3d51320871e5350a41e950a214425d6314910da14a204426e62952318f59352042ad6214f42c758c544c23e6414b1097596530871d5350810d3949328423d6494431d3551324825d63951319b988548c23f65d08109b588504c71f544c910cb591520c29d63909429758c505065d6314142ab9875250a6d6294e419798e521026e6294e4197d9732d066f6550842d9949511023d64d45328
  | 6 => 0x1480c301500e0400502500000dc8aa60000581680c00a0000001e05a0000001400c14c030330ac03c0a0040002c4b20190520100031001800490829008548be80704a1722a80100e0ac0d0030f60900a0060362c80b80a0500149300a0be160bf125002178000e900c0200181e04e0003f0a000804c048010040000e16800000c0d0050002680b98d2d80380000000c03c0d08804000d6f80600229c04804784018008190700700388c0100983c80111c040068000e20940c86f0000180e80700001c0387b0000380d0030040240026000a010140030b20200d0000600303800a000000138f200201cb580c05c0d8030850080000082e0260680a8530000207082d090025ad16101a0484d83b0000683c01901c01c090060121042403203e00260b96004000000000080302a01c00409001011006008eb0000083100182e01406802809008000000941de004128010f2000a200000a0800000126605c000030f606db68030540080080c0080186e0661740400980906c0740189f2a20000b0021f20440480700801c0281c048060008040180841e8d40001f80e80c0020100a8041cc0300284b010414040f5032010000a92900740a00000208c0d0000820002394e0109d83d8d1030000020030021d002801030244068390000380100a0040181000000200411a1f006794198000201281800d00000003800026000390570000182880d008000038100061f00000b0020045c89e0100285f006012114010190000545800500055c380000080300a06c0340440080301413800903004000000033121801d80000a2482104700001c0200004054c0301100001000007002004328000402d80102e0000008482908c0002c0060a0004010100060143800001011005801c754d42c834e6354830d354e520425c65cc940cb14942c42ad6210c40c794f42c834e6354b41da909500866c6255110cb98a548c7c7614ca21d354d520425e6394a419758f520429f6150c439dd8553483354254440b3582424cb5b3254021d514e314438d43509328f995424425f63552109718d501073542944309758e52d073643544409758e528438d5350821cb551320cb2d5494b318f990530838d424ca21c750e5110e5f654c030cb99152cc65f6550c43b3593524ca3d64d4f219bd89544425e63d5021b358e320871d5410d31c755332cc7655244010b358e
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x9860e5358b4190782a126528861835516210c30c92a6b00421048d7218d4010287baa8499663c850a2154021a1ae9292641042d721915384306b22c72902185991518c430a1ae7292841060e655093250286b9ca4a1683235ca6390541a8ae331aa421c4d7298e51d0306b2a849902143dd5424c830e12a6a12a010d0d72952438c70631aa4a0081435ca544c810a4ce3b2a849968542d85504cb06aa2c42a665255c46050c43c1ecaa1265a0c2c7654d4248306b1ac52a463135c86354041a1ee4a1aa421c1d76953318c6b0b8c84a8043435ca5350810a1ae529a8520d0d739494204286b90c6aa061131d9544c920838ecaa2601850d731494244382a12652888143dd5424c81089ae531ea98866161580524420fbb2a918861435d0524c93191ae531c8220723424855008647bb28428265c254d4294021a1ae529a842048d72191300c324b1ac029221435d2524cb3185ae5324a39860f54588438c30732a8499221439d5424c910a1ae431aa998e0c6550d424cb82a1264a8881435d65350821a52e1a9a8410e0d6458d5204287baa86a908723dcd60d4942a1ae7b2a8510d0d759513208686bae849904323dd942d453291ae5324631860c5458b314c342a12c2282658a1954248110e12a8994a010d0d72953328c686b90a898a61435c853d0940b0ce3b2a849944d7298f5448686ba4a499461835cd6295231a1ae42a2649850f7650d5210e86b90a8a1a61435ca544c830c52a8b00421058771581424ca86ba0a499221135c86355210c1ce8b14a720d4471551324830739ac52a463435c85450c31e0a84992a21050d74d953288784a12652804352dd53254021c28c6a8a802060d73588544c306b2a84994838398d5290440e14a8992a010d61718c95008784a1264a8043d04ca2154021a1ae429e86a050d72953318c6a23aa6510a2183d913254221c1aca32a849950c7550932442a4b9e42a8043705c4604c920b42e2302849050d739494290292b9086a88818395162cc631a1ae529e8520e0f635095088706322a498061839d16214d40a1eeaa12641052b75509500870632a8499221435c85350d40b0ae2302849952974c85500860ebb0a998a61465c05450c3185ae5326a690e0d5358843d0616b90c8a8063435c85350540a1ae52a26598d8671181424cac238a8499283235d261d4932a1ae8292658860f655093204306aa2c421a63435c85390140a1ae42a4869842d7299353c4286ba4a499061435d2524c810c1ac8990a29058571d95424ca94ba464a8043a150a6114132a1cea3028499705424c9510c286b94a6a1683435ca53d0e41c1aa6b10862061464545300c29238aa6a1241235ca648c430a1ae7292850848d7298e4190307b26c7a9221435d5424ca31a1ae7292842068561185424ca873aa8499261525c3544c821
  | 1 => 0x45570000000504010d1a04000100264b110101090b0001080204030000060001060002000000025000000222161710000204000c3b000001030f050b190b081a0700050c040b0801000403c2364900011a00330108000001ab000000330a3a0316050d0708011d170300000033010000164710020006a1ae832a649050d72951438c686b92a899041435ca5350e41e0a84a88a29950d72951328c706b1a8428a4183d95424c82091ae53246298e48654c92044286b98a4a16218359542cc82191ae730ea4a148d721814310fa199242a8043235cb6150c43c1aa8b108798f05424ca510830b31aa320881435cc5250941a1ae529e8320d457210d510c247ba2c1a9265435c853d0540a1ae632a8490549739095008706b22c6292218358d6215130a1ae429a84a070a535095008707b2a8499081435d2524ca10c18a6b1682a050d72153324c286b90a9182618354d6214f42a18e0a1aa421d0f7150d5210f85a1264a8043c25513254021b0ae332a849960e6454a310c26338ccaa1265495c66454843c1ae8b14a720d177150e5110e86b90a8a1e61439d76150932c1ce6b10a8985247550a2144286b90a8992218a5916014910a1aeaa12640858671995424cb06ba2c429a81435c85350910b08e2b02849970942cc95008742a10c299263a15086154132a1ae42a662
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x63000000000000c04080d8795162cc631a05819cd6295231a05819d16214d40a0582191514c030a058298d5190440a0582991518c43080d8715162cc53080d87191524c030a058218d5150040a05819cd621513090581dd94354843a05819d16294e4180d87991528c430905811c14354843
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 890
  | 4 => 1340
  | 3 => 228
  | 2 => 14
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
  | 6 => 2*((h/28+packedAt s3K6 (704+(h % 28)*6) 6) % 44)
  | 5 => 2*((h/324+packedAt s3K5 (24030+(h % 324)*10) 10) % 890)
  | 4 => 2*((h/467+packedAt s3K4 (50920+(h % 467)*11) 11) % 1340)
  | 3 => 2*((h/118+packedAt s3K3 (11172+(h % 118)*8) 8) % 228)
  | 2 => 2*((h/18+packedAt s3K2 (840+(h % 18)*4) 4) % 14)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xfe1ffff0ffff87f83f0fc3ffe1fff83f44f3cf
  | 1 => 0x3fe1e1ff0f0ff87fc7f0fc387e1c3fc7bb4d33
  | 2 => 0x3ffe01fff00fff8ff800ffc07fe03ff8c38e3c
  | 4 => 0xc00001fffff0000fffff00007fffc000fc0fc0
  | 5 => 0xfffffe000000000fffffffff80000000fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x2000010000008000001004800240800001045
  | 1 => 0x84484222241500814310441122089286194512
  | 2 => 0x2884954442aa441a9888aa8255412530c28a28
  | 4 => 0xa1d55988aa83552cedaa220479938192ec0f80
  | 5 => 0x3119910ecccc664f36ccf32711020624f7e000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeaeaeae8e8eeeeeaeaeaeae8e8eeeeeaeaeaeae8e8eeeeeaeaeaeae8e8eeeeeaeaeaeae8e8eeeeeaeaeaeae8e8eeeeeaeaeaeae8e8eeeeeaeaeaeae8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37997
namespace PEqualNP.Outside.L_meta_37997
open PEqualNP.Outside.L_meta_37997.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x1c118e00268a000001001280141500002392000000fd43fc20fc21ff21fe30fc40fd42fd30ff10fe43bf42fc32fe41ff40fd32ff41fd31ff30fc43fe31fe32fe42fc10fd40ff31dd30fd10ff43fc41fe21fe10ff20fd20fc31fc30ff42fc42ff32fd41bd42df30fd21fe40fe20
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x2617d524437aa810df95130eea9c817e50042fca319774c010bf2a241df30042fea5885fd4d21bf294837f53c877c84a17b54840be29a217d538c2fca9107d90510beaa6219f42cc3eaa219774c431bf2a0817c53c87bea9985f95043bf28081df318c77a84085f55230bea8c657d548437ca7a15fd4f109f2a0417d5090ef8a0a1dfd5132ee990657e50d06b8a6a16f90440be28a857c540c2fca2195d94432be29c437d52842fea710ef10e40efa96619f424c2bca6186fd0910be2a2637f520437c82a0dfd4532f790a417e5010bda84904fd5110dfa1481de41cc2fca121df55120bf2988379500cbbca5987e50040bf29e41fa100437aa8086f50d42ce2a261f521443baa4985f54241beaa465de53842f8a098fe8c030ef982417d538cafca690f750f30dea1683be548c7ec4210efd0b32dea12413d548c67ca9905f94232afa9a43de414c2faa7085fd4131bf28c417d52042f8a6a0ef10640bea8663df320cafca321f790c43bfaa241bf428c37a8520df54743bf286877c50486fca9085f94431bf28663dd434c2faa308774c120bf284815d538c3bca7206fd0740bf29c857f54c86faa3a05f94f42df2a041bc41102fca5884f55010bf286857e52d02faa010df54f40dfa1e8576511037ca8196f55320bea8463bf42102fea9187e48210dfa12637e530cbde84a15d54432bf29c83f621c42f8a6907e4c120ee90e61bd428cafaa8185fd4d20f690e41bc43103dca4205fd4520efa8e617f53883be85985f14f109faa261bf425077c87206f95321fa98a437f548c778a8885f94021de28685bf420c77e8621df94030ee20e617d520c2faa7a0f7d0c32ef98041bf5250bf220086f55232df28a85dd214c3de40105fd5021efa12617e530867ca9195f95131beaa2617f524c7ee21085f54e31df29a85dc43cc2fca8106f54742dfa12817d52906baa7086fd0842bea9621bc4350bba60106f50820ee20a617c53086faa6215f14e20ef28e61bf420c3b86418df54232bea9c43bd54c86fea6a0dfd5110ef292617d549077e85906f50841bfa9843be43103f440106fd0b31bea8865bf4390efca221fd50441ee21a617e5010fdc84905f55231bf29485dc438cb7c86a0df94841be2a2437e51102fca9905f94743ee2a2617d52d0fb260905f55330af29c83dd514c2fea6087e48110ef29c83de21cc3bc87985f94031bea86837d51cc3ec6310df55240fb10a213e540cb7e8590df14810bf28c637e53042f8a2907708730deaa4637d528c2f8a6a05f95121f7994657d51c82faa9215f94c40bea9661ef324cafaa3185f54e41bca8043be51d0af8a5885f54242be2a465bf51d0bbaa7107790d30fb90a43be4350afaa910f794c10bea86657e508c27ca810df94820af298437e520c6fca7205f54e42efa9a857d520c6f4a010f7d0d43
  | 1 => 0xd53083ba60887b4c832fd102217d5010efea818f64c220ef206617c524c2fca6905f55243faa0a217e51107bc6518f6d4130bea9441bd420c6faa6905f94910bf2a643bd428c3f4a010f714730bf28e41df308c278a8987790130fd882217f52503be64985f54840dea1481f641106f8a8105f94630df21a877d519037aa1a15f14910deaa041dc40cc37ca9197710f31dea00817c530437e84107d8c431be28a65df328cafca5085f94830be2a065bf41906fea0a15f55320ee98e615f5350adca408778c130eeaa2617e501077aa8195f55321bf2a0857e540c7b8a6a16f10f42fb28841dd54cc33ea8984f55021eea0e61dc31cc2fca118fe8c220bea9463dc324c3be87987710c32bf294613c544437a84a0ef50b31bf29a217d52887dc40907ed0240ee992637e54ccbba85985fd5221af29c21bd42103baa3986f50540ee98a61bf428c6faa1a15f95010ee20261f5310c6faa110fd54440bfaa263bf4350af8a2a1df153319eaa465ed21086faa8107750530efa1a617c53486f8a990df94220fb28881fa500cbdc4290f750330eea9841dc328c7b885985f54c10bea8643ed52043ee20085f54643fb98c637e5390fbaa5987b50b20bf28c837e50907be87196f90f42dea12817d54882fca918df95132ee21261df310c6fca41977cc320ee28a617e500cb7a84215f94730ee29a437e51902faa8197750130bfa9e41dd424c3be60185f94f40ee18a61f741906faa018df54620bfaa0657e50c877a85906f50832bea8085dd300c2fca4207754c10ef2a6617d54486f8a8086f10f41dfa9e857c548c3baa610efd0821dfa08837e528c77ca990774c320dea1061df21cc2fea9907ec8220f790e417f51502faa6205fd4e10beaa265de320c6fca2185b54810be29263fb405037e85a0f7cc730bf298877c544c37a8590df95221ef18a637d531075a84907d94432bf28c857c504cbec83886fd0a21fa908437d53882f8a4a04f55032bf2a061df214c37e85105f94621be2a6213d5490af8a8996fd0b30bf294877f514c3ee6298efd0a10be2a421dd4310fbea690df15110fc98061f9500cbbe62987d44010bea9e41dc32cc2fea4a0df55331bea8065df324c6faa818df94b41beaa2217d53442b8a690f714b30bfa8a87df544c37e85887794e20be29a855d530437a8490df54442dea08837e52043f240107b90842bea8e857d540877ea1a15f94c30dfa1261df32cc6faa790fd48710df286857d52d03bc84985f94421be2a4637a500cafaa9995f15031df21e837f54843f480207d8c521ee996637e508877e84995f94e21d7a9285be419037e85a05f94020be2a6617f54082faa420df14142bf29687bc544c2fea8086fd0a32ef29881bf5150afaa78877d4930bea8c85de42cc2fca2087b90b20aea9881df434c6baa7105f54a40ee29
  | 2 => 0x88090680b070000840e02402038001e4193fc0095c0003409071061240b80003060c80000102401148750002e0006d01c0d0a4001381401401020af000e7010000ac1e00c5e060290000000c0002c020e83807c040381002c3415001004000581201c1b0080d00c2406c2701c00001720205f0a400000281e0053a0001a0060a005194000c41c0301e070901700a1a00e068ea010270841103800090af01c030501b030020040b06406008e0134011f0060300501cc90c81704c0707405004125580b07c020080e7d00700c021740031a3801c0801402000190980001800548541c80101806088190bc0e010080400101c3001028204110a81308457004030880b049030b06d0180805c0103000010191c00e01806014360081a03c01074005a40205c01000000000100002018400f01abf29885f610443f460905fd4d10bea9a437d540437e81205f94740dea8a857c514c3de4210df54e40dea1043bf4290afca6106f50a10dfa10657e52086fca221778cb30efa0e61bc5350afca9985fd4c20be2a441ef4290bbe82986f54f42ee10a617d5290efea9107bc8621fba0a837c52842fea890efd0540fa98c43df514c2daa4206fd0040bf29863df30882fea0a1d754e41de29e85dc54cc2faa610dfd5232bf28e857c5250efca4215fd5130be2a241ef20882fca7a0ef54d42dea14437f504867ca990ef14142bfa82837e548cbbe61085794c10bf29e21dd539077a85887788530bf29e437e528cbbe61886f50b30bf2966375510837ea0a177d4130bfaa6215e53102f8a9906fd0810df2a0217c538437a85105fd4d42bea8e657f5150af8a7907b48520bea9663bf5350bba61105fd4943bea9e859f5350b7ca0a14f55321dea0e817f524c3f441087795130bf28e657f54cc6f8a2a04f55320faa0e217e5210fba61085f94e20ee98621df40cc37a84987710d31bea98417c54ccbda40106714d42aea9c81ed4210afea0995f95032f7190657d50106eaa2207ec8120fd98261bc435077a85995794c20be29283bc51d0afca820fe4c220bf2a6637d511027ca82177d0f31fd88421bf42106faa898efd5110dea1681dd32cc3f2a010d754c21ef18e617f52842fca810df54843be2a4437e54c43be8098778c930eea98813e540427aa8105f94210bea86877d52d07f661187dc8621dea8285f551083ba64987794530dea1e857c530837e84905f94a40f7290217c50506fea9986fd0a41bea88416e5210378a2a16fd5130cea16617e544437a849977cc110bea8861ad42c82fea4885f94420dea18877f53502bca7105d94420dea1263be54086fca9186fd0921ef192657f540c2f8a810f7ccb30eea9c21de53082fca12177d0e43bfaa6657e50ccafca7084f95231df202817d5110f7a84886f50a31ef29843de314c33a84985794e40bf296615
  | 3 => 0x4c1a002090040c1bc4301c0014c001b40d004294cc340940200001000050080110c2002c2203013014120f8030
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x4544c32e54508428f59742042da6090930a7195424c37251940329e580540c7e12148110b9189314871d53d0a20a758c50d0b1c54cc530d594e510833742944409798e51d0b1f5310d42d510d510ca9e648c730b358840cc33b42540219758c52c4335549443297996414c35553544408f992544431e5494c209d98453086d960d4b30d3949300429e6314342b6580328c67a6015032b658351cc2766115220a7994544c23c6550930c714f4350a5d6314142ab58a5350a5f6548730b6582424c38f53d49428f992528c71e54cc010c714f5150a9e648cb308fd95420831d5494c209d587530838c53d49429e58053c866d62d4c10a758e5150a5d6394742cd5445150a5e6314142add855050ab46154142c755330c826e6214810ad5845050b374294432c7552530865d63d5021c755253042b66114342d9547200831d63151309758f540427661150309758e50d0b1f65509309d587540cb5843540329d984548c39b54d41309758e50d07cb214c1209798e509075a6094e20a718d42903365454420e6191308829d6414b30cb949421034d5354840b698021cc3354254440c7951300823e65d05409759641cc32e52d08108f593530429f6354542975965308756514c020cd952510cb2e62953209d987540829d64085309dd95411072c5250931b3d89514c33554544209798e500832d5250a10c754d42102d5610c8319ed95300c23d65d0a3197d8d54482d962d4130cb90d52103695244010a758e50d0a3d64148109798f54043a942481109719542cc25e6314121cb549428c31d544c020b5584328c63e6494d10c7953318c6766114810e3d8d42c825c6354910cb551200827a6015031e6509308825d658c8318f596540863d6494431cd553100423c64540319758c505073554440108f990540823d6414f21c794f428826f6254d109758c504865c6355321a759251cc23c6454e109798e508867a6014c218fd9150887a9424c1209e181544871f6454e108f99353487c8624c1208f990514829d60d4d42f2485304835953882108f593530863d65950209798f520431f6355232e350b30c831d53d0821cdd0a510823d6494a3097582530865e631481097997324c71c5414930cb549420c66d62d5010c7551530432d5250810d6d0d500cb1f6550b30f2d8930483722154021c7550438ca7661141429798f540c36552544409798c540c23e6414c219798c548823d64145209b988505065d6014d21ce551500875953540219d587540825e65101308f99251cc29d648cb309d984540ca5f6354720b5987434c69e64c85308fd954310f354254432da54a100425c6354720cb949420c27561152308f592528c7a94248210d5547300823d65d0821c754d42842da608c930c794f429035953880208f191508873443544408fd91500c69d648c730
  | 1 => 0x867561149309ed8154486b561143429e580540878d424c320dc545200823d6494730d594d51102d96094930ad98753d0a9d64949309798e5010a5e6514d218f593520425d63d5221cb55152042da600c930a7588544c32e5250820c794d428821c6550930b6d9530882d56114b309bd95210867661d50329798c53082d561103308fd89548c63d62151308f99252442d9638c120a7d8d5050b4e53948108f59252c429d648c930c754d420871e53d0a41c754c43903596394021c754f420429e6410930cb949420c73542944208f59353c82796015032abd9542c82ad64c8720c7d4f424865e6590130d654e500863f65508329718d52106d86050530c7191538429e6414b30c7951530872e5494810a7592314c23f6454332b6580320c79b424c1209798e534865e6394341c794f420832d52d0b418f99252c423d6494832b658051cc35732544329758e501063f6454e20e318d42c825d63942429798c530863e64d4c218f19152443c9424c120c7950328c73742544208fd954210a9d64d47309d19521442db6050530c7151514c2746154d20c759353486d960109308fd91518831e5454c20c794d429032e5250a30a7592514c25d6315021e3509320cab66114142c718d54c869d640c930c794d421025d63d5020ce552500cb2d5250040d6d95308823d65950329798c540825d6054c109ed9520082d96008530c794f420867461551208f593534863d6414a109798c52442d461549309e980530838f63509209798e50d0ada60c85308f99052c427661d53309bd95200825e63152109758f548433b4294032b658054cc33a5494032d694d500871d5454c208f59353c431c54d4130b558754cc23c6454e209e59610042d66114930d354b3004389424c12097d95300429d6494b30ad587421065f6550c43a798e419025d6508530d354e520435a534c0309758e51d029e6514d42e350b304832e6454810d698d500865d63d5220c7553430ca756115032e6d0b504c31d5350a40a798e50d0b1f6454e20dc545500cad66110130c795330c834e5354840b558432cc31f63553219758e508871c6355032cbd49424c73942540329d984524c27661d4c208fd89540825e6314b10d54c9510cb1f54cc1108f59252cc65d6510c32b6580414c31e53508309e195204425d65cc010c794d428439b644c1209dd95210869e640c9309d984540434d5394840a759321cc25e6394242ce552500867a60d53318f99252842d960951309718d54c825f6054c21c7191538829e64087309758e500865f654c8329718d544831d5390c40e3d89424c23e64d4c109758e500831e63d5110d698d500ca3e6414c10b5984324c26d62150319b988548c25d6315220c7151304425d6314810d658d50086766114f208f992528c23e64150328f990520433643544408f99
  | 2 => 0x21540219758c548433742544408f59252cc2da60085309758c528439854d41309d58754cc23d6494830a759021cc31c53d4942c7d5130442ad64c852097d9542cc26d65948109b588540c31e54cc020ea50a30483394294032a7592424c2756114c20cd544411025e6314a10c794f41907365454432a7593214c31c63553208f597420835b3254032c75533008274654c5218f590524c69f6454530d654d200823d6494d108f596411029e6390440b6582514c25e6394021c755130c82bb60545429e580530866d62152108f994544433554544329758e500425e6394041e650b504c32d52d0040d554d510823d6255020cb54b420435743544328fd91534423e6414c20b6583214c29d6394142e318d424829e64947308f592520872f5250941cd584544427761551209798c540432e64948108f992520823e6415021cb592520423e64d4f10b3588404c2cd6210c328f99353c863d64d4e2197d8d524423f6550a319b988540c26d62152308f191518823e64150109d586544cb1d53d0a10c79945350b2d52d08409798e50c865e63d4a108f992520c71e544c0108f597420ca9e6394d42d64c9500ca5c65485309b98a544c63d6414c209718d544873a54540219e98053c863f65504418f99053c865e63d5221ce509500866c65509209d584540c29e648c930c754d428825e639512197596530825d6014d42cd50a511029e648c531a798e51d0a5e6314c10b6d81514c29e64c87309798f540832f6550b20e6d91308823e64944319758f54442b86054542ad58753d0b2e5450b20cd545401027a6014931b6980424c25e631502197d8d52d025d60d4d21b658052cc31e53d0810a758c5050b5a5394021c754f429069e63d47428f992520ca5e63d52208fd97428c65e63d50218f995424433542944328fd95420423d6550810a7d91524c23d6414121c754f42082d7615493097997434c63d649482097d81539071c5490d30cbd95424835551145309e583540869d6414930c7150324c29c63509419d5845050a6f654c832cd54451d0a5f63553208f191534423d6414f208f993520425f6354b10a718d421031c5494930a7992524c2756115220d5545300836552944409758e509063c6454332b5584524c23d6414c21c755330043555394420d594d510829e65d09308f1954244277654401097195424c2f06050510ea50b204829e63141428f990528434e53948408f590524c23e64141218fd8954042766195132ab58853d0a7a6014810cb949420429c6350b41cb54b42106af6254d429dd85534823e64d4f209e983530867a60d5021d694d308825e63145208fd91534823c65d0910d9545200831c6550b308f990524c65d63d4a109e580524c63f64549109d984540833b42940219e58354cc63e6494b319798f540c65d6594c10c714f424
  | 3 => 0x21975973008278654c120c7152324c33954540329ed95401029e640cb309759421cc32e54548109b988530431d5350820c7993534865f6054c1097d95300829d640cb309798e500426c6254d10cb949428423f65d08108f58b544431f53d4942c794d420432d6454810c754f429031d63d5110a7197424c31d544c010cb195424826e62d5010d554431cc29e6494b30a799351cc25e65907308f588544423c6454d20ead81424825e6508730b398840cc31c54d4530cd546411025f6354841a758e51d0a3e64948308f997424c29e63941429798f544431e53d0a10a7992314c3725154032c714d5150b54514c5309b98854042b66190d41c794f420c25e6394740c754d429063c65d0930d9549100423d6595010d954b100429e64945309b588505067a6015021a7191514c23e6494732ea181424823d6414b10a718d5050b2e6454840ae580431023f655082197994214c2d66110330a7995424c25f6550930d698e50087692154021b658021cc2ce62101309798f54c433a5454032c714e5050b1e6515130ab58b53d0a6f6550842c7551530865d63940429758e54486d66114b30cd952510823d6494a10c7952328c65d6394321d354d520425d63145208f995424c25f6355121cd547401023e65d09109d58453c833742544329dd95310c6db60551309b988540c7394294021b6980414c31c6550930c7952530429c6354542e3d8942cc23d6414910cb55320082d6610cb30ce952500872d5250a40a7990524c398644c120cd552510831c54cc110d994a511026e6215020cb549429065e6314141b658354cc23f6550040b6d81524c29d63d4742c714c5050a5c654873097d95214c3715188020cd15241442d5610c930c754d420431e5350a418f592520431f5350921f44c1100439b424c2208f992520431d63d51309758f54c423e64d4c20c795253086d561101309718d52c426e6215210e95092108754538c521cb549420c31f54d4130c794d420834e52cc010f24c2204829d62d51308f59251ccb99424c1209758c524435551147308f990524c31f5410d3097d95300c27960d4c219758f520423e6494b30a7990214c23d649483197195434c32d52d0b409758c540823d62950109b58a544c63d64d4f218f99053c82b46150941d5584534867a60d5032d694130082766114c209b588530426d62150109d195414423d6414c10c795130c823d64949109758c540423d62d5130a7992544c23d64d4c20d654d208425d6590530d554d21087555394440d554e210871c5350921cd509510832d5494810ab5835250a5e63d5210d3549300435651cc0208f992544c31d53d0840e3509304831e5350821ab592424837151940329ed95100425d60d4d4297d95310c63f6454e10a798e415071f6355320c7951530431c544c5308f58a548c771
  | 4 => 0x216cff004011000002c02000020c82b00005000d8024610880fbfa722301300c050c0000244d035bb418bd0040a014000042001c3803405044b802c34020100040001003318021940005c00030850000000830010100b02004c01030000000c05c281040c00a820801dd600500c000023b01000000060000f028020000c00402014292880035c0501444008000040110000274062000000053410000283600004000050480039c032d00100c00008020044218c4c0980022d58024006b00000c140000001c4c6000002012000020d51901c0010c00000090240c018550f809048290080c004000040b00c0300c20826de1c401771d4002ca0340281812680181941e10c00070021780301c0101401000031fcc40016a00003040009ec0004c04008040200002c000cc07004040483309c1e00001080090040302c000080129405070000100400000001d20300001c0000c0401c07000000040102c000200c0040107c0701c12018cc09401004d0001790001fa280000c0101c006c8000000502c12000060000c00562022340040a43744340030040000044000000140006c240002a9f4000140314c1404c000380d16c022b81414011000001a91b0181304c3b0000000c0b0240500a24018360000000c02030000840200001010eb264010000000c050040609afc6dc03050020022c0000e0a001154ab0180000001910009718d52d027561150208f9935388758654c120c794f421033b42540328f99052443994010130d6d95304825f6355132d594e511032f5250940a75805350a3e6494821b3189514c3ca424c120a7191524c32c43548409e583540ca3d6550a3197d8d54c874e535481097997434c26e62d4c10cb949429025d6094e41d994951102d661d5330cb54a411029e6394542cb548411036b2154
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x38001011a2008714353360e0008900081020201280006c30c00002061010702c2ca8b086518d297010d521020ebb0a819261071d95350a10c28a8b08a498589731814248294b80a4a12638598d5190440930eca12611060c6518d424820f3accaa1261a2dd9424c120d12c4a008098741524c1100420e3b2a898641c154d4248421a62e021aa22041e76d4d424860e3b2a6a1441525c84354032e0a84992a2195197014c5050a643b284982410b5c86454031b12e990a6090589721913048344318c0a1241a2190624c120950eca1260905c171189304820f3b6a898221a45854010130b12e031a849050d72950328c670b80c498a438614c6054542e428490aa010d887650930482a2b9086a886585151610c930e1284992a019614535845050a86b90a829261c45513044010a1ae42a064984c972181414c2a2392a228a614c1c15114542e12a6a1241086887650930482463b28498241625d0624c120838eab26429858a76509304822cb80c6a9083625d2424c120c30ca322609060c54189514c2443b2849824186951600ca31932e031a842048c7650930c824cb84c720881385c86050510930eca1260905a171181424828a39a84a88818398d5290440
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x8320020041010000000a0582951610ca31c08655c06350920a098098d5290440c80645c4624c120888865d3214c120c08655c8644c120c80635c46050920911801cd4254440a118098d51904409088754d4248210a0582151611493088a869d9424c120a118014d6114142a0982951600ca31a0582151610c930
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 820
  | 4 => 894
  | 3 => 68
  | 2 => 15
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
  | 5 => 2*((h/280+packedAt s4K5 (22140+(h % 280)*10) 10) % 820)
  | 4 => 2*((h/410+packedAt s4K4 (33972+(h % 410)*10) 10) % 894)
  | 3 => 2*((h/36+packedAt s4K3 (3332+(h % 36)*7) 7) % 68)
  | 2 => 2*((h/19+packedAt s4K2 (900+(h % 19)*4) 4) % 15)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xc7f8ffff078ff1f871e3e3ffe383f0fe0cf4cf
  | 1 => 0xf87f0f8ff80ffe3f81fc7c707c03ff1e7348f3
  | 2 => 0x7ff00ffff1ffc7fe007f807ffc7fe1838f3c
  | 3 => 0xff80000ffffe0007ffff80007fff8001fc0fc0
  | 5 => 0xfffffff000000007ffffffff80000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x50082101101022001020809120889044041445
  | 1 => 0x831242122124c04180c4242244112618314892
  | 2 => 0x242004244201000a2200490409204880828128
  | 3 => 0x1106ab4895086494d5690009725a024d5c0ec0
  | 5 => 0x2644cc00e64d89276992724e00600c91ebe000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfeeafeeaf8e8f8e8feeafeeaf8e8f8e8feeafeeaf8e8f8e8feeafeeaf8e8f8e8feeafeeaf8e8f8e8feeafeeaf8e8f8e8feeafeeaf8e8f8e8feeafeeaf8e8f8e8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37997
namespace PEqualNP.Outside.L_meta_37997
open PEqualNP.Outside.L_meta_37997.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x10934d04000200000108b00014074069e043006000fc42fc30fe21ff43fe41ff21fd30fd40ff10fd32fc32ff42fe30bd42fc41fd42fc10fe31ff41fc21fe32fd41ff30ff31fd10dd30bf42fc31fd21fe10fd20ff40ff32ff20fd31fc20fe40fc43fe20df30fd43fc40fe43fe42
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x621bd42c82faa1995f94343deaa043df54cc3b886195f94030be28a41ed52102fca321df94d21bfa9a817c548c2fca9197d44010bfa8a61dc434c7eaa2105f54b41be2a041bf424cafca020f754c10eea02613d54c86fca1216fd0a41be28a617e54883da84215f95310ee992637d51103ba65985f94a43f790a41dd53843bc83985f54321bf28441be40502f8a9987750b30ef98a613e54c837882205fd4f10bea8e87bd41502fea6a0fbd0a42faa0a217c51503ec8388774c220deaa465fb40903b8a29867d0930f7190655c5350af8a9085f54e41dea1221f521443b865987715130bfaa2637e51d0ff480205f54343bf280217c54883ba64195f54f10be2a221df5350b5ea4a15f14c21dfa1643de314c2fea998e714d42baa88815d53102fca320ef55020bf280875d53043be86985f14910bea80875e530c2fca6197b4c832bf28e81f651083de41106fd0540bfaa0637d53c83be43985f15010dfa16617d508c6f8a790ef50040fd982617d53d037ea8885f94431be29a21f9304827ca8105fd5321bea9c817e54c82f8a8996f50820be298217e54482faa5985fd5210bf28c657d500cbbe86a1f754c21dfa08837d51cc2fca618ef50a10bfa92215e530877aa7a16fd0810bf298217c54c42f8a7105f94410bea9c21df51cc2faa9207790c43bfa9a43df4390efca818ef95320bf29063df30042fca790df94020dea1665fb20483be84985f14f20beaa6217d5290fbca9985f94021fb880217d520437e84907750c43bfaa621bf429027aa9905f94732bf28c41de40cc2f8a7087e44010ef98241bf424c7bca7086f15110bea9081bf424877e84196f94742dea10857e52cc6faa318774c030bf296877f5150bba83985f94e10af29841de324c3bca8985f55321bea9681f551103b886985fd4132faa0e217d518caf8a89077487309f2a463bc53d0afca8105f94f209f2a0857e51103f4a010df55121cfaa261bf4290afca7a07d48710be2a261bd42c42fea6a17790b30de21c817d508cbf240885f94241ef99663dd53103de84a17e8c120bea8e65ef324cbec42886f10d41eea92617c535077a84a07708530bf29465dc5350afca890f74c930efa96617c504caf8a0a15f54640bf28885bc43102fea0a0df54742dfa8a857e544cafca4086fd0b20ee18e617f54082fea9185f14f10eea8a617d5110f7e8418df94432df2a0437e50c87be81987790530beaa6417a500cbf420085f94e41beaa4415d53882fea8186f90f42fc90041bd42882f8a098efd0840df20c817d5390b7a8518dfd4520fb98a63de524c2f8a6a15fd4e20bea9087dc40cc2fca7105fd4f21dea8a859d42cc2fea918ef50c43bfa8243bf5250afca8215f94f10be28a85dd54cc37c82a0df14943be298417e53d077a8598df94230fc90421bf5350bda429077d5130
  | 1 => 0xe53083be65985f14940bf29a21f7108427aa8087710130bf29881bf409033a84985b94840dea0e817c54c86fea8996fd08429f2a043bf42d02faa718ef50b40bf2a6617d528437a85205f94210be2a065df524c2fea4a05fd4532ee99663de53086faa790df54b43dea16617d521077ea0a16f50941bf29e85ed20082fca118df94331bea9441dd52cc2faa8986f95010fb20883df438cafaa121efd0b10dea16437e50103ee4290f7cc310bf28665dd434c2eaa2105f55241eea8e61de434c37aa81977cc931dfa86853e540cafca3a15f54e20bf290837d528877e84a07714b30bea9e857f54ccafea2a06f90e40be28243df320cbbe82985f95021dea10217d510caf8a2997710e329eaa065be43506f8a9997d4c521ef29821dd30c82fca2187750330eea9c81de214c3b86518dfd4b10bf290857e528c6faa8087d88421f6a1641fa308833e85987ec8220bea9883bf420c37ca8197ec4110fc98441bf42882fca2104f95010bf2a6436d52102faa8187794e41beaa665df308837e802076d4130be29a437e544c6fca4185f94c42bf29a417e528c37a84905f55110f7102415d538437aa3a16fd0a31dfa1663dd30442fca8204f55231ee2a6617e544437a8490d754e40f6a90217d51882fca318f7cc730fd10221f741907eaa21957d4d42bea84857e51cc2faa610f78c730bfaa2437e509037ea7a177d4530bfaa4437f548ca7aa8107714930af298213d5490af8a998df14143ef192657f53483b260905d54432df21285de304c2fca018df94243ee28e61ee4210afaa9985e54021efa9a437c540c37c86205f15232beaa065dd53082f8a6906f95231bb288417d52442f8a898fec4210fa988635f53487be87985794e10bea9c61bf41d02faa018dfd4930ef28a617e5310ff260185f55243ee984217d54842fca8085f55242fb90c437c54887ba60107e88020df21e833f54443baa7105f55331fb20a21de314c7dca4206f50831dfa14657e52102daa40877d0b30beaa4617d530837887a16fd0941df21a87dd31cc27ca91977cc030beaa2657e54107de40105f95032dea10817e53106fca9085f94820f729021be5150afea4a0df94421f690843bd428c3f441086f15130bea8861fb308c2fca3205f54830bea8083dc414c3be64986f10640ef196617d544c6faa518df55020bea8c857d528c3bca5987dcc631fd280653c544c37a84985f14930dfa1261be4350afca5a07710930bf2a443bd41106f8a498f710f30af29c417e52c4278a8885f54442bf28e41be5350b7a86a16f50a21bf2a663df310c738a8985f94e40dfa1043bd54c87de4210d794e41dfa18877e50d0bee82a0f78c831be2a2439f5350bb843985fd4143bea8c217d52cc77aa6a177d0d31bfaa221df430cafaa918db94810fd180617d5190f7a85a0df94032ee98
  | 2 => 0x940d0280b66400001076585700093064000dc00018120000002137010030080d0200f01000038a402c08054780a4050a0000204c01800000ad0008200402024025dc7d03c0000528188000e4057a40519016126710a0074f016000000a4f803409008295743c00003424bf0003d2d62600c171540000839001eb00800038bf1780b000260000801c000a4260f8430382f0001a005e30580302c0200051000050140d08c022280302c43001b6004040bc10010128880b0040e0141000002008040e0060000b005d50700032010020190100a04cb40180e0024100c020023d04c026ec0d04c240f4010001b010010003d004000d40800c000000b0000500c5f0f803000030003209c000681420c23030000040009c000102e00004018690000e33401020130240005056000120cc092280abf296617d54886fca3185794c40bfa92637e520cb78a3a17790f30bf2a461f6314877aa9905fd5320be28a87bd43d0afca821ef50821ee98863d930883bca3987e54032f7212417c52842fca8987750f309eaa465dc320c6faa690df94e43fb10e217d54087eca2195f94e42efa0e61df214c37e8721df95231aea9843bc5050bbe65195f54e21bea9483bf42d077a84185fd4943be290217e528437e8510df15320bea96213f544c3be61905f54221deaa4637f52842f8a6a05d94440ef10e617d50906faa3a077d4130bb288657f5150fec20887714d21bf28c437f5308778a2a15f95332ef298817f54883be6318df54331ee98021ad424837ca810770c930fb188637e5110eb8a690f794e20dfa1a857d53483eca2205f54c10de29a85bd428cbde4310df94c30dfa8e85bc43d07de43905f94221f7994657e5190b7c82205f54e32bea9a217d520c7ba60906f94342ee98a61dd53906fea9987755130bfaa0217e5010b7886a15f55120dfa1221dd414c2fca8185f54a40bf28683de404c37ca990dfd4f20ee216617a50087be60886f94142ee90a61bf428c2faa1a15fd4e10bf28883fb40502baa6105f55232bf298437e529037e87a177cc230fa908437f534437ca7a16f54342de286857e5290afea8905f54042be2a0637e508cafea810dfd5130bca8065f9500877ca9197794e40aea9c61bd54042fea4085fd5032bea86837d5310a7ca990f790930bfa9c437e5210fec6310ef50832bea9881ee214877e841077d0f31be296217f5050afca4885fd4131bea8043bf41907da43905fd4c20ef980417d53d06fca710eb50b20bea88417e52d07b88798df94a41dea8285ed42482f8a0a0ef50932ef19463ee42c82fca410efd0a10ef29841bf544c2bca7205fd4c10ee20e615d539077a8420fd50441ef984217c538877a8520f70c530be29283bf42ccaf8a918ef50931beaa063bf42107f280207d4c6219eaa0437c54087be80985f54720eea12617
  | 3 => 0x2000000000d038160200304816000040c80600c00558042982107617000729900401406000010280002005134af054170c00200c370043c08c7a00414000140052401408010060246d0001400d0601c0023c08000010200e1b01300000000001
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x6100426e621502097d8d51c83ab60509208f58b544c31d544c020c794f42102af6550b20ced09500ca5d6394740c7953300829d648cb308f992520c25e63943429d98754cc2da60105308f597420429d6215130f2909304832d5250a108f595428c67a60d5331b5984404c31e65151308fd91538435932540329718d54c82db654c2209e580540ca3c6454e109e980540ca3d649482097d95424c399424c2208f993530427b60551219758f54887354254432cd552510835953482109759641cc25f6355121c7952530832e52508308f59353c425d63d5021c718d54c829f63545428f99053c871e5350821c7952328c76551c80208f990530823c6454332ced0a50086d96014730dc545200831e544c0108f993534865d63d502097d8d54c86776154d20a7191524c31e544c3208fd89540425c6548530e6191304823e6494b30a759351cc23e64d4c21a7994544c31f63553208f99053c829e640cb30c7d95424c31d5494c21cb949420823e6494732c7152324c35a504c0208f99353082d962d41309798c548823d6215110e3509304831d5350821b5987434c71d5350a41b658352cc32c52509319758c5050b1c5350921d554d510831d5410e32cdd0a511025f65487308f997424426f65480209d195314865d6314141a799021cc31d5454c21ce509500872d6494810ad9845050b1c6454e209758e50d0a9e6394d429798c530865e63d5310b658351cc32d54548109798e50d063f6454e20f2485304829d640cb309e583540ca5e6590530b5584404c33551147429758c540433954540219758f528423d6414f20c754d42082b761541428fd91534825d6094c21cb549420c74e5354840cd951510823d64949109759653086da608c930c7553430cb9b42d4130b698021cc33554440109d58453c823e64141219d584524c25e6394d219d584548c2d96095130b6980424c2766114142cb949428c35551145309e195204427661152309719521cc2d661149309759730042d86050530d698e500866d62d501097594430cb1c53d0d42b6d81544c25e63943219dd85544823d65950108f590524435b654c220d6d95304825f6550c43e6500404c2796014c218f995424425d6594c208f990524c27661951329798c540425e65d0d31c794f42842d9600ca31d658e500865e6314a108fd9542042b561143429ed95300c25d6394221ae1815150a9d6494530b6d81514c26d6215030d6cc9500cb1d63d5130ae58043102d46154930e6d91304829c63508408f992520ca3e6494b108f59641103a942c8120b3588430cb3742544409758c54843355114542cb952520423d641412197d95320cb1c53d0921b598432cc31f5310d429e983540872e5250831c754d428829c63541429798e5090ab561d0841d5584534865d65cc020c794f420c35a5354021
  | 1 => 0xc25e6508730bc181414425d63d4810cb54b42d06756115220cb991520425c6354b10d9949511035a6094e209d587540825f6354b40d394d520425d6394042a718d425065d6590530c794d420425e6314c10b398840cc29d648c7309e583540874d53548108fd91500c69d6314342cbd95424827465505108f597420ca5e63141218f992534426e6215010d514e314871d53508108f992520431d5454c20e6d9130883344354440c7151514c2d6610c9309e580524c65f6054c10c7953318c72d52904409758c520431e53d0a41ab58853d0a7661149309798c540872f6550b20c755330c8277654c431a7990424c29e6394142cd55310042d56114930c719542cc34d5354840cd152414431c6355321a798e51d0b2e4354840cbd49424c71d53d08409718d51c836552944409798c5308354514c5308fd97420432d52500408f59251cc35a6354032e3d8942cc27a6014c21c798f544429e6495130a7592524c25c6550930c7195424c29f645453097596530433554944328f191500c7574354432975835350b1e5350a409b588530429c65d09308f191538829e6414b30b3189514c23c6454620b3d89514c3544354432c754d428438d42cc320b5584320c6746154d209719542cc25e63d52208f597420825f6355320ce951500ca1c65509309b58b530431e53d0a208f59053086766114c20d5945300827b65500408f992520871c5394142a758c5050b354254420b558432cc3a86050920cb591520423d6494b10cdd0a510cab6611434297d9530042d5610ca319d587540cb1c5494930a7590524c23e64149319e983530875a63540218f58954083c93088120d654e20082bb60545429798f540c2cd6210130a7593214c23e64d4f10a759052cc23f6550040c7152434c23d6414520cb549420434e524c0108f990524431f53d09219758e50042b56114142c7d91538439b424c120a7d8d5050a3d64d4d219758f54842b461541428fd954210b1c6454e10cb54b421027960d4c219bd954210a7661d4c20a7995424c2d56114b30e318d424823d64d4810c754f4290358654c1208f99053042d960087309d195214423d6550810d9549100432e52d08109758f54442756115032ce952500869e6494930cb949421025e63150209758f54042d96015330c7d5130443374294420c755330042af6254d429b98b530429e63905419798e544865f654c4319e983540ca6d6594810c714c5050a3c6454221ce551500ca3d6494431dac85500863d6595021c7552530425f63551209d5845050a9e648c5309d185544823e6495110cd546411025e63d50219d987540829d6394742b6580414c26d6295131a758e5150ada60085308f590530837251540328f597428c72d5250a40e3d8d424831d5454c108f59053c865c6354841a799232cc23d65d08219e59
  | 2 => 0x6008530cb54b42d031c6355032c795330c831e5454c10d54c9510cad960945309d984520426e62148108f59353c86756114c20f2189304829e6414930e6d09308831f6550b309d58754cc31d63d51109e195304832d52508308f59251ccb1d544c0108f592520874e539484097d95214c25d6314a109d984540823c65d0910a798c5050b3942940219e980540c73b42540219798f540432c4354840c794f420863d64149308f59252cc23f6255231cd551510823f6454d10a758e50d0a7960d53319798e500866c6550920a799351cc25d63947428f992544c2d561103308f197424c2d66114b30e650b504c25d6094e419e580540871d53d0821a798c50d0a3e6494a309798e501065d6394321a7992324c25c6354910b658354cc2ad6294d429dd9510042756115020ab5835250a3d6494810c7d8d54c871e544c0209798c520423d6494a318f994544426e62d5010ce552500863e65509308f99353c825e6314142cd952510ca5f6550b309b98850507355110440c794d421036552c40108f58a540427a60148109dd954110755510c7309e580540c6d96010930ce952500ca3e6494b31c714f5250a3e64d4e21cd50a511023f655082097d81530865e6394042a7997424c35953882108f992510c71d53d0820dc946500ca3d6414b108f992528c71d53d0a41a759251cc23d64d4c209799641cc3394254032d694e50087695244010a798e419023d6215130dc546200825c6354b408f59654082d661d5330d994a511029e640c9309798e51d032e5454810a7191514c3354254440d694d300c398644c22097d95300c29e6494b30dc545500ca5e6315030ab58b53d0b555388421e3d4f5250b2e5250a109d984540432e5450b20ab59321c825e6510130ea509304823d6494830c754d42102b461509419b988548c25e63d50209d98453c823e65151309758c52c425f654c020cb549428c33551d00409d984540c23f6454910c7d8d548ca9c655093097996404c29d648c930b6982424c2da600c930d554e510825d63d53108f590524c71e5350820c7153304434d5394840cb553200829e64c8730e9509210869e640853097195434c2b661d4f429758e509063e6415010cb552520432f52509409758353486ad6490920c79945350b5551cc020b6583214c23d62d5110cb98a54c82db6050530c714f5150b1d53d0a20a7590324c31e5350a10b6d81524c3722154021d5cc9510ca3e64d48109798e500433b42940328f992520823f6550821da485500865d63943418f990520423e6414a10a758f51d0b365494420c7d4f5250be12148110d594d510827a6015021ce552500cb4d52cc010cd584544438f6250930d9545200826f6548421c794d420c29d60d4d429bd89534435953940218f191534829d6408730ad986435071c54cc530b6983214
  | 3 => 0xb10ea509208431d6315130c754f420431c54d453097997324c72d52d084197d8d521065d6395121d654d500865c63551209758f548827b65440108f592534435b43540328f191524423c6454d10d594e511023e64150329b988530425c6355321d5947300831d5390c40d5545300825f6355132cb949429026e6215030b558754cc31d53d0a109758e501072f52509419798c548423d6494a109758c524435a534c220cd951510ca3e6414c21ce50a500ca3c6550930c794d429071e53d0a40c759353487cb214c1209d984530869d64c8730d9549511026d6215230a7592424c34e52cc010d594e510834d524c010a7590214c29d6494b30b6580320c7584354032ab593214832e6494810c7151304423e64150218fd9150887555394440b358840cc23d6414810a798e411029d648c5309b588505066d6215010a758b544c25f6054e41d394e520431c544c530b3988404c27a6014931e2509304827a6014c20e3d8d42c823e64d4f21a799251cc31c54d41309798e509072e5450842c7d5330443374254420e6d53504c25e63d5031d354e520433643544409dd95210878d424c32097580534863d64d4e21c7150524c2e4624c5219d987540cb555348421b6582424c23e6494910c7d53504c31e5350a20cb548411025d6054c10c755130c825d6315220f2d89304823e64947308f99052c429e63d47428f99051483d13044010a7992314c71f6454e209759421cc3354294432cb54b420438c53d4942cb99152103712154021a799231cc23f6454332c7951530823e6494a10c754d429033a5454021c7150324c356535444097d8d524423d64d4c10c7553300825d6508530c7951530863d65950329798e500825e65085308f590530425c6355121b598440cc26d6215031b5d85524c31e5494c21f250930483a94248110a718d429023d6414a1097596320c65d6314520dc546500cb1f5350921da54a100425d63150219bd95320cb1d5494c208fd954310e5d6314121a798e50d0a7b6548020cb551200823f6255020cb54b401027661152209b988548438d424c8328f997415029d6014d42a798e5150b1e540ca31d554451cc32d5250a41e6509304827561d4c209d984540ca3d62952318fd91518826e62150319798e51d0ad5610c9308f59353c83354294420ad58753d0b1e53d0641c7d50434c33742544329b588548425e63d48108fd97428c6796014f21c795330042d960949308f59252cc66e629513197994534875553544408fd95428c71e64d4d219d584540c35963540219798f548866c6254d10cb949420425d63940219798c524431e5494c10a7d91524c25e65d0d30a718d5150b3554544328fd9541107a9428c1208f592520cad9638c1209758c540825d6014d42c754c439038d42cc1209d586544ca7a6014f21cb19542482d9
  | 4 => 0x730040e01c5000c0112c0000c010000094c12000040342211d580004504c0100c000540125d2202002004020300000001000b002c0402404004070002a14053494000003a01c020800600c0300c33330380103800034000070f05f0000400804048040d8000a4011043b000010044a0141343414054010040101400050090e026134000a400018000209d008010040d0034501c005200702c1a000970144b0002a0000101c0400c02174180040804c03844020300000427120523a844004010040c00015000070083d0fc2b0b40a02c0003c0400402048073940c0581e00800000011f400110040081b0bc3001c100000001801010051ac040001f03509000110042d098021ab240080206c010000000c1101c460180b388000fc0500004000341242a058b809c400140011400008000009a00004004006ed8e001230001a04c000000b0a0060040103432000f02e8000340c01000018040505a0080501c293a0180c00004008000080205f0001700400014030000c0b405020050300b4a40000c0003800018042081000000044051380901037008000180001c0100c01041b002c2f0380505c3601003000b6000050442800000278110280003c051e41a01c0401400e318d42c823e64150209798f52842d96014b308f195424431c53545429758e500823d64948319798c50506786055121a79945350b3551500408f593530865e6314520a758e5050a9e64945309758e5090b1e53d08108f997424c31e53d08208f592528c23f6550832a7993214c3595348020e6153504c23e64948319798f544425e6314b10a718d42d065e63942219798f548425f6354
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0xc00e83003000015000000100e81070614000020000000480800000001001c40100044802401700008018002000002000000002450000000000a04006990eca12609072142485500870c298c0a8a85525c84354032c28a8b086498498765093088388aa260880214a5c04354840838ecaa261905a171181424824c3b28498241221d9424c120918eca12609058974189304830a2a2c229261515c84354432e12a6a12410860c54189514c2c4ba64298241d05493044010d10eca1260904e172181414420f3b6a898221075d8540c9308b2e031aa420e1654584328c70d2a2c019463079db5350921a1ae42a064987055350921086c4ba48498241265c06350840a28e6a12a2204997098e4110345bb284982418598d5190440c1cc6a9482206886418930482543b28498241325c860505309c2e03126290c1c75593214c20e3b2a6a1441079d66550930c28a6b08a0a15897219130482c53b28498241a45854010130b12e031a849048c7650930c828cb80a628285435ca540ca31a52e02928498d89731814248344318c0a1241705c4624c120e1284992a019588765093048298b8086a888186194644c120838eca9a850842d72191500c686b90a829261c15093254432a60e0a88a2a168962500404c306328c6a1241511c95114530
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x10850c04300a118098d5190440a0982951600ca31c08655c06350920a0582151610c930a05821516114930c80645c4624c120a118014d6114142c08655c8644c120888865d3214c12088a869d9424c1209088754d4248210a098098d5290440a0582951610ca31c80635c46050920911801cd4254440
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 820
  | 4 => 894
  | 3 => 68
  | 2 => 15
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
  | 5 => 2*((h/322+packedAt s5K5 (22140+(h % 322)*10) 10) % 820)
  | 4 => 2*((h/361+packedAt s5K4 (33972+(h % 361)*10) 10) % 894)
  | 3 => 2*((h/71+packedAt s5K3 (3332+(h % 71)*7) 7) % 68)
  | 2 => 2*((h/12+packedAt s5K2 (900+(h % 12)*4) 4) % 15)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xc7f8ffff078ff1f871e3e3ffe383f0fe0cf4cf
  | 1 => 0xf87f0f8ff80ffe3f81fc7c707c03ff1e7348f3
  | 2 => 0x7ff00ffff1ffc7fe007f807ffc7fe1838f3c
  | 3 => 0xff80000ffffe0007ffff80007fff8001fc0fc0
  | 4 => 0xfffffff000000007ffffffff80000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x50082101101022001020809120889044041445
  | 1 => 0x831242122124c04180c4242244112618314892
  | 2 => 0x242004244201000a2200490409204880828128
  | 3 => 0x1106ab4895086494d5690009725a024d5c0ec0
  | 4 => 0x2644cc00e64d89276992724e00600c91ebe000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeeaf8e8feeaf8e8feeaf8e8feeaf8e8feeaf8e8feeaf8e8feeaf8e8feeaf8e8feeaf8e8feeaf8e8feeaf8e8feeaf8e8feeaf8e8feeaf8e8feeaf8e8feeaf8e8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37997
namespace PEqualNP.Outside.L_meta_37997
open PEqualNP.Outside.L_meta_37997.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x128003840a000000008080000020002000000000003060000004445380208000000010016140000a0000300000000c1408e00ff14003fc3001ff94c07ff3101ff14c07ff4300ffd0005fc3200ff44003fd20017f8c807fe3100ff08005fd52017f90805fd2101ff50c03ff50017fcc805bf4201ff54c05ff2100ff50003fc40027f95003fe10017f508057f5200ff54003fe2002ff94407fc43027f50403fe4000f7cc003fe50015f54809fd5401ff4c403ff30017f1080bfc51027fd040bff51027f10405bd42017f4c803dd30017fd0805fc5201ff90c03fd30017f88409ff5401ff0c403fc1000ffc800bfd51027f90405ff52017f94803ff1001ffd4c05fc21027f15003fe30
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x3
  | 3 => 0x4
  | 4 => 0x5
  | 5 => 0x6
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 66
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 9 => packedAt gbK9 (i*15) 6
  | 8 => packedAt gbK8 (i*26) 17
  | _ => 0
def gbH (k i : Nat) : Nat :=
  match k with
  | 9 => gbHint (packedAt gbK9 (i*15+6) 9)
  | 8 => gbHint (packedAt gbK8 (i*26+17) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 9 => 2*((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 1)
  | 8 => 2*((h/57+packedAt gbK8 (1716+(h % 57)*7) 7) % 66)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x3f0fff870787e1fffc701f81ff14419e0cf4cf
  | 1 => 0xc3f0e07807f87e1c0f801ffe1f2b8e687348f3
  | 2 => 0x3ff007ff8007fe00fffe3ffe0cc3071838f3c
  | 3 => 0xfc00007fffff80000ffffc0000f03f81fc0fc0
  | 4 => 0x7ffffffffff000000000ffc001fff000
  | 5 => 0xffffff80000000000000000000fffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x4012101008080242410448042000082041445
  | 1 => 0x41104218030822084880892c1c018628314892
  | 2 => 0x2aa04224800554081250251804c1050828128
  | 3 => 0xa800094d95d500012e4ad00446b02b815c0ec0
  | 4 => 0x20881076e6667993c003001888fec001ebe000
  | 5 => 0x33cc9e00c0441102000c006110ff7d7c000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefeeafeeaf8e8feeefeeafeeaf8e8feeefeeafeeaf8e8feeefeeafeeaf8e8feeefeeafeeaf8e8feeefeeafeeaf8e8feeefeeafeeaf8e8feeefeeafeeaf8e8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37997
namespace PEqualNP.Outside.L_meta_37997
open PEqualNP.Outside.L_meta_37997.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 1 := bs1_4_0
theorem alls1 : ∀ k ≤ 4, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
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
theorem bs3_2_0 : Interval s3Atlas 2 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 14 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_96 : Interval s3Atlas 3 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_192 : Interval s3Atlas 3 192 36 := block_range (n:=36) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 228 := (concat bs3_3_0 (concat bs3_3_96 bs3_3_192))
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
theorem bs3_4_1248 : Interval s3Atlas 4 1248 92 := block_range (n:=92) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 1340 := (concat (concat (concat bs3_4_0 (concat bs3_4_96 bs3_4_192)) (concat (concat bs3_4_288 bs3_4_384) (concat bs3_4_480 bs3_4_576))) (concat (concat bs3_4_672 (concat bs3_4_768 bs3_4_864)) (concat (concat bs3_4_960 bs3_4_1056) (concat bs3_4_1152 bs3_4_1248))))
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
theorem bs3_5_864 : Interval s3Atlas 5 864 26 := block_range (n:=26) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 890 := (concat (concat (concat bs3_5_0 bs3_5_96) (concat bs3_5_192 (concat bs3_5_288 bs3_5_384))) (concat (concat bs3_5_480 bs3_5_576) (concat bs3_5_672 (concat bs3_5_768 bs3_5_864))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 44 := bs3_6_0
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
theorem bs4_2_0 : Interval s4Atlas 2 0 15 := block_range (n:=15) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 15 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 68 := block_range (n:=68) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 68 := bs4_3_0
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
theorem bs4_4_768 : Interval s4Atlas 4 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_864 : Interval s4Atlas 4 864 30 := block_range (n:=30) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 894 := (concat (concat (concat bs4_4_0 bs4_4_96) (concat bs4_4_192 (concat bs4_4_288 bs4_4_384))) (concat (concat bs4_4_480 bs4_4_576) (concat bs4_4_672 (concat bs4_4_768 bs4_4_864))))
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
theorem bs4_5_768 : Interval s4Atlas 5 768 52 := block_range (n:=52) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 820 := (concat (concat (concat bs4_5_0 bs4_5_96) (concat bs4_5_192 bs4_5_288)) (concat (concat bs4_5_384 bs4_5_480) (concat bs4_5_576 (concat bs4_5_672 bs4_5_768))))
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
theorem bs5_2_0 : Interval s5Atlas 2 0 15 := block_range (n:=15) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 15 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 68 := block_range (n:=68) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 68 := bs5_3_0
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
theorem bs5_4_864 : Interval s5Atlas 4 864 30 := block_range (n:=30) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 894 := (concat (concat (concat bs5_4_0 bs5_4_96) (concat bs5_4_192 (concat bs5_4_288 bs5_4_384))) (concat (concat bs5_4_480 bs5_4_576) (concat bs5_4_672 (concat bs5_4_768 bs5_4_864))))
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
theorem bs5_5_768 : Interval s5Atlas 5 768 52 := block_range (n:=52) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 820 := (concat (concat (concat bs5_5_0 bs5_5_96) (concat bs5_5_192 bs5_5_288)) (concat (concat bs5_5_384 bs5_5_480) (concat bs5_5_576 (concat bs5_5_672 bs5_5_768))))
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
theorem bgb_8_0 : Interval gbAtlas 8 0 66 := block_range (n:=66) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 66 := bgb_8_0
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
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 5 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 8 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefeeafeeaf8e8feeefeeafeeaf8e8feeefeeafeeaf8e8feeefeeafeeaf8e8feeefeeafeeaf8e8feeefeeafeeaf8e8feeefeeafeeaf8e8feeefeeafeeaf8e8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075690 * 2 ^ 32 + 4276812008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37997.Model.Repr at out
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

def mono : List Gate := [⟨.and,[4,5]⟩,⟨.or,[0,3]⟩,⟨.or,[0,2]⟩,⟨.or,[2,5]⟩,⟨.or,[4,9]⟩,⟨.or,[6,8]⟩,⟨.and,[7,10]⟩,⟨.or,[1,8]⟩,⟨.and,[1,11]⟩,⟨.or,[12,14]⟩,⟨.and,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276812008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276812008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37997

open PEqualNP.Outside.L_meta_37997 in
theorem PEqualNP.Outside.L_meta_37997 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276812008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276812008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
