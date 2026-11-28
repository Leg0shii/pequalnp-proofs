import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37367.Model
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


end PEqualNP.Outside.L_meta_37367.Model

namespace PEqualNP.Outside.L_meta_37367
open PEqualNP.Outside.L_meta_37367.Model
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

def SBf (j : Nat) : Nat := [4, 6, 6, 4, 7, 7].getD j 0

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

def mirrorSteps : List Move := [swapRows 33,swapRows 84]

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

end PEqualNP.Outside.L_meta_37367

namespace PEqualNP.Outside.L_meta_37367
open PEqualNP.Outside.L_meta_37367.Model
def s0K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (i*5) 5
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (6+((h/1+packedAt s0K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffffffffffffff
  | 3 => 0xffffffffffffffffffffffffffffffffffffff
  | 4 => 0xffffffffffffffffdf83fff801ffffe00fff0f
  | 5 => 0x6ffc1ffffe007ffff007f0
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xffffffffffffffff80884259325896ecb65b77
  | 2 => 0xffffffffffffffff811084aa54a92b755aadbb
  | 3 => 0xffffffffffffffff8221093469324dba6d36dd
  | 4 => 0x247a11c771c471dc0fc70e
  | 5 => 0x1843de0781f87e1f8e07e0
  | _ => 0
def s0Atlas : Atlas := ⟨3,rawDecor 62 s0Pos s0Neg, 0xc000c000c0000000c000c000c0000000c000c000c0000000c000c000c0000000c000c000c0000000c000c000c0000000c000c000c0000000c000c000c0000000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37367
namespace PEqualNP.Outside.L_meta_37367
open PEqualNP.Outside.L_meta_37367.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x2d0a024026100600061395a080e0bf41bd41df31dd31ef21ed21be40bc40de30dc30ee20ec20f610f410
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x22000195414c74a8290f14c521
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 14
  | 3 => 3
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*5) 5
  | 4 => packedAt s1K4 (i*16) 16
  | 3 => packedAt s1K3 (i*27) 27
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (6+((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s1K4 (244+((h/4+packedAt s1K4 (224+(h % 4)*5) 5) % 18)*5) 5
  | 3 => packedAt s1K3 (84+((h/1+packedAt s1K3 (81+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0x3f80fffe03ffffff01f83f07ff07fffe88e3f
  | 3 => 0x3fff00fffc03fc0ffe003ff83ff83e030f3cc
  | 4 => 0xfc00000fffffc000fffffc0003fffc003f03f0
  | 5 => 0xfffffff000000000fffffffffc0000003ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x80840a022048480016284508450842a8334d5
  | 2 => 0x5155294651a92934781522a46aa46b55288a2a
  | 3 => 0xaa64aa6a94a3b215bab0433d233d2381b0d34c
  | 4 => 0x3346cd8d193223a6dcd9ea0843ce71063d03b0
  | 5 => 0xc3870e0e1e3c3c38ef1e73ce720842183eec00
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xaaaaaaa0aaa0a0a0aaaaaaa0aaa0a0a0aaaaaaa0aaa0a0a0aaaaaaa0aaa0a0a0aaaaaaa0aaa0a0a0aaaaaaa0aaa0a0a0aaaaaaa0aaa0a0a0aaaaaaa0aaa0a0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37367
namespace PEqualNP.Outside.L_meta_37367
open PEqualNP.Outside.L_meta_37367.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x19000428000180058800394016b000480030000bf41bd41df31dd31ef21ed21be40bc40de30dc30ee20ec20f610f410
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xa0195414c74a8290f14c521
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 14
  | 3 => 3
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (i*5) 5
  | 4 => packedAt s2K4 (i*16) 16
  | 3 => packedAt s2K3 (i*27) 27
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (6+((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s2K4 (244+((h/4+packedAt s2K4 (224+(h % 4)*5) 5) % 28)*5) 5
  | 3 => packedAt s2K3 (84+((h/1+packedAt s2K3 (81+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0x3f80fffe03ffffff01f83f07ff07fffe88e3f
  | 3 => 0x3fff00fffc03fc0ffe003ff83ff83e030f3cc
  | 4 => 0xfc00000fffffc000fffffc0003fffc003f03f0
  | 5 => 0xfffffff000000000fffffffffc0000003ffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x80840a022048480016284508450842a8334d5
  | 1 => 0x5155294651a92934781522a46aa46b55288a2a
  | 3 => 0xaa64aa6a94a3b215bab0433d233d2381b0d34c
  | 4 => 0x3346cd8d193223a6dcd9ea0843ce71063d03b0
  | 5 => 0xc3870e0e1e3c3c38ef1e73ce720842183eec00
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xaaaaaa88aa888888aaaaaa88aa888888aaaaaa88aa888888aaaaaa88aa888888aaaaaa88aa888888aaaaaa88aa888888aaaaaa88aa888888aaaaaa88aa888888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37367
namespace PEqualNP.Outside.L_meta_37367
open PEqualNP.Outside.L_meta_37367.Model
def s3K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s3K3 (i*5) 5
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s3K3 (6+((h/1+packedAt s3K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0x7f01fff80fffe07fe07e0f83ff07fe07f44e73
  | 2 => 0x7ffe03fff01fff81ff800ffc1ff83ff818739c
  | 4 => 0x800003ffffe00001fffff0001fffc0001f83e0
  | 5 => 0xfffffc0000000001ffffffffe00000001ffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x108100881024000028a1104220842a28194a5
  | 1 => 0x2aa529946a548ae8f0548aa35546b415544a52
  | 2 => 0x4c954aa528d91a2b75410ce919d23950586318
  | 4 => 0x68d9b3464c91d34db9e7a8421ee710619e83e0
  | 5 => 0x70e1c3878f1e1c71de79cf73908421861f7c00
  | _ => 0
def s3Atlas : Atlas := ⟨3,rawDecor 55 s3Pos s3Neg, 0xaaaaa8a8a8a8a8a8aaaaa8a8a8a8a8a8aaaaa8a8a8a8a8a8aaaaa8a8a8a8a8a8aaaaa8a8a8a8a8a8aaaaa8a8a8a8a8a8aaaaa8a8a8a8a8a8aaaaa8a8a8a8a8a8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37367
namespace PEqualNP.Outside.L_meta_37367
open PEqualNP.Outside.L_meta_37367.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x1d52008002c01180442451800953801ab041f4c70d805600880481c7800078a00028092100082802e680000010aa80000180262c0000000c86003800018a81010b022410004000000000080ff43df43fe43be43fd43fc43bc43dc439c43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x9c78001ec006a3c8d48631061dcea7e2b000aa090011c001f0b9605e0b40074ae261f9f0d25302000cc0014140a80000000005e000000032320000000378001c3736000000021000001400134b27d11084a25b3804054001297c4000121fcda3e11970ca3a00130b45d0e0781006310000e000019c00410513ca43d39980806b2412cdc461d854661b098445c160d09c0074001d8042d3d0047863160141a00001c8303600000600000000c249250e470002203c0003388646829229a0242b03050309810904800302088000000182000001808201800004020000830006028400808101088081000287d794e439f29c871e5390f3a8621cf94c43cf298875e5410f3ca821e7d4843cf290879d5210f38a421e7d4443cf288879d5110f38a221e7d4043cf280879d5010f38a021e710f42af29c855d5390b3887215d94642baa8c855f5350ab8a6a16710d42ce218859c43cca7ca9194f55232ce21c6576518caeaa3194fd51329e2a2659c434cb3886196710f41af29c835d53907388720db94a41b6a94835f53506b8a6a0e710d41ce218839c43cc67ca918cf55231ce21c636e528c6daa518cfd51319e2a2639c434c7388618cf953219eaa6435e53c86baa790e710f219f2a4433d54886bca710d754e21ce21c439c43487388610f948421ce21e815e53902baa7206710e40afa9a815c535033886a05bd4940b6292817751502e8a2a06710c40ce21e613e548c27aa9186710e309faa2613c544c33886985bd4930b62926177514c2e8a2986710c30ce21e419c438827ea8904f15120afa9a415c534833886905dd4520ba28a413e540827aa8105794c20aea98419c43082eca2105d54420ce21e219c438427ea8884f15110afa9a215c534433886885bd4910b6292213e540427aa8085794c10aea98219c43042dca4085b54810
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x21b96028018a19e80001f8000001c800d8c110f050000079283a01a80000003100015209a1994109700000a800000138000058800001e168000070d00001c000680001780000880000015801b0018000e0f8006000b13049d91899d018a19120914800b80211f0c810e80840117000c0000a04006364c20812001801208080a59875210e9561d4843a59865210e956194843c35485210e8e62d4443a358b5110e8e6294443a358a5110f155114443a3d895010e8c6254043a5d855010e946154043a39885010e8d6214043a59845010e956114043c510e5190b144354642c510e518cb144354632c310e529070c4354a41c310e528c70c4354a318718d54c861c6454f2187d9443c861d6510f218718d548861c6454e2187d94438861d6510e21e110d210870c43d4940c310c525031443d4540c510c515021c6315130c310f524c30c4314930c510f514c31443145308798f544821e64d4d2087994434821c6510d20c510f514831443145208718d540821c6454c2087d94430821d6510c20c510e510831443544208798f544421e64d4d1087994434421c6510d10c310f524430c43149108718d540421c6454c1087d94430421d6510c10c310e520430c4354810
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
  | 6 => packedAt s4K6 (6+((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s4K5 (825+((h/15+packedAt s4K5 (720+(h % 15)*7) 7) % 72)*7) 7
  | 4 => packedAt s4K4 (3827+((h/43+packedAt s4K4 (3483+(h % 43)*8) 8) % 170)*9) 9
  | 3 => packedAt s4K3 (2738+((h/22+packedAt s4K3 (2584+(h % 22)*7) 7) % 108)*8) 8
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfffffffffffffffc0fffffffffffffff0fffff
  | 1 => 0x7f03ffe07ffc0ffff07c1e0ff83ff03ff44e73
  | 2 => 0x7ffc0fff81fff03fff801ff07fc1ffc0f8739c
  | 3 => 0x80000ffffe00003fffffe0007ffe0000ff83e0
  | 5 => 0xfffff0000000003fffffffff80000000fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x11040241048000002942410904215140194a5
  | 1 => 0x2a48a64324915d1cb0290a8d2a35a0aa744a52
  | 2 => 0x4c292a890d23456d550213a44e91ca82b86318
  | 3 => 0x68b2cd12483a69b669cf41087738830cde83e0
  | 5 => 0x70c30e1c71c38e3b8e739dce04210c30ef7c00
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeaa8eaa8a8a8a8a8eaa8eaa8a8a8a8a8eaa8eaa8a8a8a8a8eaa8eaa8a8a8a8a8eaa8eaa8a8a8a8a8eaa8eaa8a8a8a8a8eaa8eaa8a8a8a8a8eaa8eaa8a8a8a8a8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37367
namespace PEqualNP.Outside.L_meta_37367
open PEqualNP.Outside.L_meta_37367.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x800f003a00119003932c56a0b00008d0804a911004e4948054001931420e0d36250070a5c81a3e54c0b22507810c00603106408003341142288149ff43df43fe43be43fd43fc43bc43dc439c43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xf41026008fa6a11820000702914f200051041a35239a000641c8001e000e8a434630d84c221200064000000000ae4e000c80200000f0e27e171e07e18000ace60000024a000349280038001246c001680c006018800ea1f00000b60037800ee4d14000006d0000000002e0000025000002e7c3a000dc0b020b0ec5f060584c0e1b93c66591f158387f0a91028611d0bc40512a9c0001e40178e46221994ce5a12108a6220009ca46610800ba48201b0f63b1e918a80003000604b358d054580203870280000d8b00098082818000838300000a85028009898c00818110000083918200148100800003805794e439f29c871e5390f3a8621cf94c43cf298875e5410f3ca821e7d4843cf290879d5210f38a421e7d4443cf288879d5110f38a221e7d4043cf280879d5010f38a021e710f42af29c855d5390b3887215d94642baa8c855f5350ab8a6a16710d42ce218859c43cca7ca9194f55232ce21c6576518caeaa3194fd51329e2a2659c434cb3886196710f41af29c835d53907388720db94a41b6a94835f53506b8a6a0e710d41ce218839c43cc67ca918cf55231ce21c636e528c6daa518cfd51319e2a2639c434c7388618cf953219eaa6435e53c86baa790e710f219f2a4433d54886bca710d754e21ce21c439c43487388610f948421ce21e815e53902baa7206710e40afa9a815c535033886a05bd4940b6292817751502e8a2a06710c40ce21e613e548c27aa9186710e309faa2613c544c33886985bd4930b62926177514c2e8a2986710c30ce21e419c438827ea8904f15120afa9a415c534833886905dd4520ba28a413e540827aa8105794c20aea98419c43082eca2105d54420ce21e219c438427ea8884f15110afa9a215c534433886885bd4910b6292213e540427aa8085794c10aea98219c43042dca4085b54810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x1b81800000000000091f911815000000001a00109d1680141e1aa0000d800000170311960a0019208e8000210f801f050019938980000d101c000000120881060294a1958b1e87078000059280001b00000c8f0c0a800008009c849786801302000400000000000000188000038000000b9d8000000e00020814002000c080000020100380000234101a59875210e9561d4843a59865210e956194843c35485210e8e62d4443a358b5110e8e6294443a358a5110f155114443a3d895010e8c6254043a5d855010e946154043a39885010e8d6214043a59845010e956114043c510e5190b144354642c510e518cb144354632c310e529070c4354a41c310e528c70c4354a318718d54c861c6454f2187d9443c861d6510f218718d548861c6454e2187d94438861d6510e21e110d210870c43d4940c310c525031443d4540c510c515021c6315130c310f524c30c4314930c510f514c31443145308798f544821e64d4d2087994434821c6510d20c510f514831443145208718d540821c6454c2087d94430821d6510c20c510e510831443544208798f544421e64d4d1087994434421c6510d10c310f524430c43149108718d540421c6454c1087d94430421d6510c10c310e520430c4354810
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 45
  | 4 => 129
  | 3 => 68
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (i*5) 5
  | 5 => packedAt s5K5 (i*16) 16
  | 4 => packedAt s5K4 (i*27) 27
  | 3 => packedAt s5K3 (i*38) 38
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (6+((h/1+packedAt s5K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s5K5 (810+((h/15+packedAt s5K5 (720+(h % 15)*6) 6) % 55)*7) 7
  | 4 => packedAt s5K4 (3827+((h/43+packedAt s5K4 (3483+(h % 43)*8) 8) % 170)*9) 9
  | 3 => packedAt s5K3 (2738+((h/22+packedAt s5K3 (2584+(h % 22)*7) 7) % 118)*8) 8
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfffffffffffffffc0fffffffffffffff0fffff
  | 1 => 0x7f03ffe07ffc0ffff07c1e0ff83ff03ff44e73
  | 2 => 0x7ffc0fff81fff03fff801ff07fc1ffc0f8739c
  | 3 => 0x80000ffffe00003fffffe0007ffe0000ff83e0
  | 4 => 0xfffff0000000003fffffffff80000000fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x11040241048000002942410904215140194a5
  | 1 => 0x2a48a64324915d1cb0290a8d2a35a0aa744a52
  | 2 => 0x4c292a890d23456d550213a44e91ca82b86318
  | 3 => 0x68b2cd12483a69b669cf41087738830cde83e0
  | 4 => 0x70c30e1c71c38e3b8e739dce04210c30ef7c00
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xeaa8a8a8eaa8a8a8eaa8a8a8eaa8a8a8eaa8a8a8eaa8a8a8eaa8a8a8eaa8a8a8eaa8a8a8eaa8a8a8eaa8a8a8eaa8a8a8eaa8a8a8eaa8a8a8eaa8a8a8eaa8a8a8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37367
namespace PEqualNP.Outside.L_meta_37367
open PEqualNP.Outside.L_meta_37367.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x540225ca43005050b006a10000309dc2f00dc983785de81767c0345684508003802400080070000280740062a007201100f96807201b4360021333c8d31a58412b240480006200e80000000000041020010000061c90102046010a0048300ff95001fd5400ff15003ff43007f90c01fd4300ff10c05ff51007f94401fd51017f14403ff41007f90401fd4100ff10401ff31007f8c401fd31007f0c401fe21007f48401fc2100ffd0001fe40007f50003fc40007fcc001fe30007f4c001fc30007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a2002bf99510007faca88002fd6544011fe32a2002bf19510006f8ca8800a7c6544001ffb222000bfd91100077ec888002bf644400fff3222001bf99110007fac888002fd644400ffe3222001bf1911000778c888006bc6444011ffaa22007ff95110007faa88801ffc5444001ffb1a2000bfd8d10007bec688002df6344001ff31a2000bf98d10007fac688002fd6344001fe31a2000bf18d10007b8c688002dc6344011ffa9a2000ff94d10007faa688023fc534400fffa1a2000ff90d10007fa868801ffc4344001ffb122000bfd8910007dec488002ef6244001ff3122006bf98910007fac488002fd6244001fe3122006bf18910007d8c488002ec6244011ffa922000ff94910007faa488023fc524400fffa122000ff90910007fa848801ffc4244001ff9922000ff8c910007fa6488003fc3244011ffa8a2003ff94510007faa28800ffc514400fffa0a2003ff90510007fa828800ffc4144001ff98a2003ff8c510007fa628800ffc3144001ff90a2003ff88510007ec4288003fd2144001fa90a2003ff08510047fea088003fe5044001fea822008ff1411003ffe8088003fe4044001fea022007ff10110007fe6088003fe3044001fe9822000ff0c110007fe4088003fe2044001fe9022003ffc411001ff62088003fe1044001fb0822003ffd941001dfeca0800ffe65040057f3282003df99410014fcca0800ffd65040017eb282003df59410004faca0800ffc65040077e3282003ffd901001dfec80800ffe64040037f3202003ef9901000d7cc80800ffd64040017eb202003ef590100057ac80800ffc64040077e3202005ffd5010027fca808003fd5404009fe2a02003ffd8c1001dfec60800ffe63040017f3182003f798c10005bcc60800ffd63040017eb182003f758c10005bac60800ffc63040077e3182005ffd4c10007fca608003fd530400bfe2982004ffd0c10007fc8608003fd4304009fe2182003ffd881001dfec40800ffe620400d7f3102003fb98810005dcc40800ffd62040017eb102003fb58810005dac40800ffc62040077e3102005ffd4810007fca408003fd520400bfe2902004ffd0810007fc8408003fd4204009fe2102000ffcc810007fc6408003fd3204001fe1902003bf9841001ffea20800ffe5104007fea882003ff1441001ffe820800ffe4104007fea082003ff1041001ffe6208003f73104007ff1882003ff4c41001ff8620800ff43104007ff9082000fdc841001ffc420800ffd2104007fe1082003fd08410005fcc008017ff5004001ff2802000ff5401002ff8a008013ff4004001ff2002000ff50010027f88008003ff3004001ff1802000ff4c010007f86008003ff2004001ff1002000ff48010007f8400800fff1004007fb8802003ff8401001ff4200800ffd1004001fa8802003fe44010
  | 1 => 0x3fd430c01bfe2186000ffd8430007fcc21800efe610c001feb086000bf58430007f8c21803bff510c001ff2886000ff54430077f8a218037ff410c001ff2086000ff5043006ff88218003ff310c001ff1886000f78c430007fa6218003fc310c001ee1886000ff88430007fa4218003fc210c0017f300600dffd0030007fc8018003fd400c01bfe2006000ffcc030007be6018003fe300c001fd1806000ff4c030007ba6018003f9300c007ffb2e2003bfd971001ffccb8800afe65c4007feb2e2000bf5971001ff8cb8800efc65c4007ffb262003bfd931001ffcc988006fe64c4007feb262000bf5931001ff8c98800efc64c4019ffaa6200bff95310007faa98802ffc54c4007ffb1e2003bfd8f1001ffcc788002fe63c4007feb1e2000bf58f1001ff8c78800efc63c4019ffa9e2000ff94f10007faa788033fc53c4017ffa1e2000ff90f10007fa878802ffc43c4007ffb162003ff98b10035fcc58800ffd62c40017eb162003ff18b1001df8c588033ff52c4001ff2962000ff54b10067f8a58802fff42c4001ff2162000ff50b1005ff88588003ff32c4001ff1962000ff4cb10007f8658800fff51c4007ff28e2003ff5471001ff8a38800fff41c4007ff20e2003ff5071001ff8838800fff31c4007ff18e2003ff4c71001ff8638800fff21c4007ff10e2003fd8871001ffa4388003f521c4007fe10e200cffd4310007fca188003fd50c4019fe286200bffd0310007fc8188003fd40c4017fe2062000ffcc310007fc6188003fd30c4001fe1862000ffc8310007fecb08002ff6584015ff32c2002bf99610007facb08002fd6584015fe32c2002bf19610007fec908002ff6484013ff3242001bf99210007fac908002fd6484013fe3242001bf19210057fea908027fe5484001feaa42009ff15210007fec708002ff6384001ff31c2000bf98e10007fac708002fd6384001fe31c2000bf18e10057fea708003fe5384001fea9c200aff14e1004ffe8708003fe4384001fea1c2009ff10e10007fec508002ff6284001ff3142006bf98a10007fac508002fd6284001fe314200affd4a10007fca508003fd5284015fe2942009ffd0a10007fc8508003fd4284013fe2142000ffcca10007fc6508003fd3284001fe1942000bf58610057fea30800ffe5184001fea8c2003ff1461004ffe830800ffe4184001fea0c2003ff10610007fe6308003f73184007ff18c2000ff4c61001ff86308003f43184001ff90c2000fdc861001ffc4308003fd2184007fe10c2000fd0861001dfcc10802bff5084001ff2842000ff54210057f8a108027ff4084001ff2042000ff5021004ff88108003ff3084001ff1842000ff4c210007f86108003ff2084001ff1042003ffc4210007ee210800ffb1084001ffb2a2000bfd9510006feca880027f6544011ff3
  | 2 => 0x400affea6a0003fe5350001fea9a8015ff14d4000ffe86a0007fe4350003fea1a8001ff10d40007fec4a0002ff6250001ff3128000ff58940007f8c4a001afc625002bffa928000ff94940007faa4a0057fc5250003ffa128001efd094000ffc84a0007fd4250001dea128001ff10940007fe64a0003fe3250001fe9928000ff0c940007fec2a0002ff6150001ff30a8000ff58540007f8c2a000efc615002bffa8a8000ff94540007faa2a0057fc5150003ffa0a8001efd054000ffc82a0007fd4150001dea0a8001ff10540007fe62a0003fe3150001fe98a8000ff0c540007fe42a0003fe2150001fe90a8000ff0854000dfec0a0057ff5050001ff2828000ff541400aff8a0a0007ff4050003fda028001ff901400077c80a0007fc4050003de2028001fe10140007fec998002ff64cc027ff3266001bf99330007fac998002fd64cc027fe3266001bf1933009ffca998003fd54cc027fe2a66013ffd0f30007fc8798003fd43cc027fe21e6000ffd8730007fcc39800efe61cc001feb0e6000bf58730007f8c398053ff51cc001ff28e6000ff547300a7f8a39804fff41cc001ff20e6000ff5073009ff88398003ff31cc001ef98e6000ff8c730007fa6398003dd31cc001fe18e6000ff88730007fa4398003fc21cc027ffa066000ff90330007fa819804ffc40cc001ffb246000bfd923008ffcc918006fe648c001feb246000bf5923008ff8c918006fc648c023ff2a46000ff5523008ff8a918002fd638c023ffa1c6000ff90e30007fa8718047fc438c001ffb0c6000ff9863001dfcc318003fd618c0017eb0c6000ff18630097fea318003fe518c001fea8c6012ff1463008ffe8318003fe418c001fea0c6011ff10630007fe6318003fe318c001ef18c6000ff4c630007f86318003dc318c001ff10c6000ff48630007f84318002fe608c023ffa046000ff90230007fa8118047fc408c001ff9846000f7cc230007f66118003ff644c0017fb226000efd91300057ec89803ffe644c0037f3226000ff59130005fac89803ffc644c0037e3226000ef1913000d78c89803ffe544c001feaa2600fff1513007ffe8698003fe434c001fea1a600fff10d30007fec298002ff614c001fbb0a6000bdd8530007fcc298003fd614c001fe30a6003bf18530007e8c298002f4614c021ffa8a6000ff94530007faa298043fc514c01fffa0a6000ff90530007fa829803ffc414c001ff98a6000f7cc530007fc6298003fd314c001ee98a6000ff0c530007fc4298003fd214c001fe10a600fffd0130007fc8098003fd404c01ffe2026000ffcc130007f66098003fe304c001ef1826000ffd9030005fec818037fe640c0037f3206000ff59030005fac818037fc640c0037e320600dff95030007faa818037fc540c0017f318600dffd0c30007fc861800
  | 3 => 0xe28c4203ffd062101ffc831080ffd4188407fe20c4203ffcc621007ee631080ffe3188407fe98c4203ff0c62101fe8631080fff218840dfb90c4203ffd822101ffcc110802fe6088407feb044200bf5822101ff8c11086fff5088437fe284421affd02210d7f88110803ff64484017fb224218ff9912100dfcc890803fd64484017eb224218ff1912100df8c890863fe5448401feaa24218ff15121007fec690802ff6348401ff31a4200bf98d21007fac690802fd6348401fe31a4200bf18d210c7fe8690803fe4348401fea1a4218ff10d210cffea29080ffe5148401fea8a4203ff145210c7fe829080ffe4148401fea0a4203ff10521007fe6290803f73148407ff18a4200ff4c52101ff86290803f43148407ff10a4203fb88521007fec090802ff6048401ff3024200ff58121007f8c090802fc6048431ffa024218ff1012101ffec81080eff6408407ff3204201bf9902101ffac810802fd6408407fe3204203bf190210bffca810803fd540842ffe2a04203ffd8c2101dfec61080ffe63084017f3184203ff58c21005fac61080ffc63084077e3184217ffd0c21007fc8610803fd430842ffe2184203bf9842101ffea21080ffe5108407fea884203ff1442101ffe821080ffe4108407fea084203ff1042101ffe621080ffe3108407fe9884203ff0c42101ffc421080ff62108407fe9084206fd48421007ca421080fff6008407ff3004200bf9802101ffac010802fd6008407fe3004217ffd00210bff88010803ff65900017fb2c8016ff99640015fccb20003fd65900017eb2c8016ff19640015f8cb20006fd6490003ffaa48001ff9524000f7ca920007fd5490001deaa48001ff15240007fec720003fe63900017f31c8000ff58e40005fac720003fc639002dffa9c8000ff94e40007faa72005bfc5390003ffa1c8001ff90e400077c8720007fd4390003fe21c8001ef10e40007fec520003fe629000d7f3148000ff58a40005fac520003fc629002dffa948000ff94a40007faa52005bfc5290003ffa148001ff90a400077c8520007fd4290003fe2148001ef10a40007fe6520003fe3290001fe9948000ff0ca40007fec320003fe61900077f30c8000ff58640005fac320003fc619002dffa8c8000ff94640007faa32005bfc5190003ffa0c8001ff906400077c8320007fd4190003fe20c8001ef10640007fe6320003fe3190001fe98c8000ff0c640007fe4320003fe2190001fe90c8000ff0864000dfcc12005bff5090001ff2848016ff1424000ffe8120007bf4090003fda048001ff1024000ff08120003ff65500017fb2a8015ff99540015fccaa0003fd65500017eb2a8015ff19540015f8caa0006ff6450003ffaa28001ff9514000ffaa8a0007fc5450001ffb1a8000bfd8d40007fcc6a0003fd6350001fe31a8000bf18d
  | 4 => 0x80fff318c407ef98c6200fdcc63101ffec11880ffe608c4017f3046203ff58231005fac11880ffc608c443ffa846221ff14231107fe8118883fc408c401ffb2a6200bfd95310fffcca9880afe654c401feb2a6200bf595310fff8ca9880afc654c401ffb226200bfd91310f7fcc898806fe644c401feb226200bf591310f7f8c898806fc644c43fffaa2621eff95131007faa89887bfc544c43fffa9a6200ff94d31007faa69887ffc534c43dffa1a6200ff90d31007fa869887bfc434c401ffb126200bfd8931007fcc498803fd624c401fe3126206bf189310fffea498803fe524c401fea92621fff149310f7fe8498803fe424c401fea12621eff10931007fe6498803fe324c401ef1926200ff4c9310fffea29880ffe514c401fea8a6203ff145310f7fe829880ffe414c401fea0a6203ff10531007fe6298803f7314c407ff18a6203f78c531007fec098802ff604c401ff3026200ff58131007f8c098802fc604c43fffa82621fff141310f7fe809887bfc404c407ffb286203bfd943101ffcca1880afe650c407feb286200bf5943101ff8ca1880efc650c407ffb206203bfd903101ffcc818806fe640c407feb206200bf5903101ff8c81880efc640c43bffaa0621cff95031007faa818873fc540c4017f318621dffd4c31007fca618803fd530c43bfe298621cffd0c31007fc8618803fd430c439fe2186203ffd883101ffcc41881afe620c407feb106200bf5883101ff8c418877ff520c401ff2906200ff548310eff8a418873ff420c401ff2106200ff508310e7f88418803ff320c401ef9906200ff8c831007fa6418803dd320c401fe1906203bf9843101ffea21880ffe510c407fea886203ff1443101ffe821880ffe410c407fea086203ff1043101ffe621880fdf310c407ff1886203fd8c43101ffa621880fdd310c401fa9886203ffd803101ffcc018802fe600c407feb006200bf5803101ff8c018877ff500c43bfe280621cffd00310e7f8801880fff65884077fb2c4203ff99621015fccb1080f7e65884053f32c4203ff59621005facb1080f7d65884013eb2c4203ff1962101df8cb1080fff64884077fb244203ff9922100dfcc91080fbe64884035f3244203ff59221005fac91080fbd64884015eb244203ff1922101df8c91086fff5488435ff2a44200ff552210d7f8a91080fff63884077fb1c4203ff98e21005fcc71080fde63884016f31c4203ff58e21005fac71080fdd63884016eb1c4203ff18e2101df8c71086fff5388401ff29c4200ff54e210dff8a71086bff4388401ff21c4200ff50e210d7f88710802fd6288437ffa944206ff94a21007faa51081bfc5288435ffa144206ff90a21007fa851081bfc4288401ff9944206ff8ca21007fa651081bfc32884077f30c4203ffd462101ffca31080ffd5188407f
  | 5 => 0xa410077a8520807fc42904077f30c8203ffd464101ffca32080ffd5190407fe28c8203ffd064101f7e8320807f74190407fe20c8203fd1064101ffec12080ffe60904017f3048203ff58241005fac12080ffc609044bffa848225ff1424100ffe8120807fc4090403de2048200ffd9541005fecaa0893fe65504057f32a8200ff59541005facaa0893fc65504057e32a8203bfd914100ffea8a0807fe5450403df2a28201ff551410077aa8a0807fc5450401ffb1a8200bfd8d41007fcc6a0803fd6350401fe31a8200bf18d41127fea6a0803fe5350401fea9a8224ff14d4100ffe86a0807fe4350401df21a8201ff50d4100ff886a0807bc4350401ffb128200bfd8941007fcc4a0803fd6250401fe3128206bf18941127fea4a0803fe5250401fea928224ff1494100ffe84a0807fe4250401df2128201ff5094100ff884a0807bc42504037fb0a8224ffd454101ffca2a0803fd5150407fe28a8201ffd054100fee82a080ffe4150407df20a8203ff1054101f7882a0807f44150401ffb028200bfd8141007fcc0a0803fd6050401fe3028200bf18141127fea0a0893fc5050403ffa028201efd014100ff880a0803ff65cc4017fb2e6223ff99731015fccb98803fd65cc4017eb2e6223ff19731015f8cb98803ff64cc4017fb266222ff9933100dfcc998803fd64cc4017eb266222ff1933100df8c99888fff54cc445ff2a66200ff55331117f8a99888fff53cc401ff29e6200ff54f3111ff8a79888bff43cc401ff21e6200ff50f31117f88798803ff62cc401ff3166206bf98b31007fac598802fd62cc401fe3166223ffd4b31007fca598803fd52cc447fe2966222ffd0b31007fc8598803fd42cc445fe2166200ffccb3111ffea39880ffe51cc401fea8e6203ff14731117fe839880ffe41cc401fea0e6203ff10731007fec198803fe60cc4017f3066200ff58331005fac198803fc60cc447ffa866223ff14331117fe819888bfc40cc407ffb2c6203bfd963101ffccb1880afe658c407bf32c62029f9963101ffacb18802fd658c407beb2c62009f5963101ff8cb1880efc658c407ffb246203bfd923101ffcc918806fe648c407df3246201af9923101ffac918802fd648c407deb246200af5923101ff8c91880efc648c443ffaa46220ff95231007faa918883fc548c4017eb1c6221ffd4e31007fca718803fd538c443fe29c6220ffd0e31007fc8718803fd438c441fe21c6203ffd8a3101ffcc51881afe628c407f73146200bb98a3101ffac518802fd628c407f6b146200bb58a3101ff8c518887ff528c401ff2946200ff54a3110ff8a518883ff428c401ff2146200ff50a31107f88518803ff328c401ef9946200ff8ca3101dfcc31880fff518c407ff28c6203ff5463101ff8a31880fff418c407ff20c6203ff5063101ff88318
  | 6 => 0x17fb2a8600dfd9543004fecaa18a3fe6550c057f32a8600ff59543005facaa18a3fc6550c057e32a8600df19543014f8caa1806ff6450c03ffaa28601ff9514300f7ca8a1807fd5450c01deaa28601ff1514300dfec6a18a3ff5350c01ff29a8600ff54d43147f8a6a1807ff4350c03efa1a8601ff90d430077c86a1807fc4350c03de21a8601f710d4300f3886a1803ff6250c017fb128600ff98943007fac4a1803fc6250c0d7e3128628ffd4943147f8a4a1807ff4250c03fe2128600ffd8543005fec2a1803fe6150c01feb0a8600ff1854301df8c2a18a3ff5150c51fe28a8601ffd054300ff882a1803ff6050c017fb028600ff98143007fac0a1803fc6050c017e3028628ffd4143147f8a0a1807ff4050c03fe2028602bf5965101ffec92880ffe64944037f324a203ff59251005fac92880ffc64944077e324a202ffd5251017fca92880bfd5494405fe2a4a203ffd8e5101ffcc728802fe6394407feb1ca200bf58e5101ff8c72880bff5394405ff29ca202ff54e51017f8a72889fff4394401ff21ca200ff50e5113ff8872880fff6294407ff314a206bf98a5101ffac528802fd6294407fe314a202ffd4a51016fea52880bfc529444fffa14a200ff90a5113ff8852880efe6194407ffa8ca203dfd4651017eea32880ffc5194407fa28ca203ffd065101ff8832880fff6094407ff304a200bf9825101ffac128802fd6094407fe304a202ffd4251017f8a12880b7c509444fffa04a227ff1025101dfecaa8803ff64544017fb22a226ff9915100dfcc8a8803fd645444dfe322a201bf19151017fea8a880b7f5454405ff2a2a202ff55151006faa8a880bfc5454401ffb1aa200bfd8d51007fcc6a8803fd6354401fe31aa200bf18d51017fea6a880bfe5354401bf29aa202ff54d51017f8a6a880b7c535444dffa1aa200ff90d51007fa86a889bfc4354401ffb12a200bfd8951007fcc4a8803fd6254401fe312a206bf18951017fea4a880bfc5254405be292a226ffd0951007fc84a8803fd425444dfe212a202bfd8551017fea2a880bf75154407ff28aa203df9455101ff8a2a880f7c5154405fa28aa226ffd055101ff882a8803ff60544017fb02a200ff98151007fac0a8803fc60544017e302a202ffd4151016fea0a880bfc505444dffa02a226ff1015101ffecb2080eff6590407ff32c8202bf9964101ffacb20802fd6590407fe32c8203bf1964100dfac920807ff5490403ff2a48201ff5524100ff8a92080fff6390407ff31c8200bf98e4101ffac720802fd6390407fe31c8225ffd4e41007fca720803fd539044bfe29c8201ffd0e4100ffc8720807fd4390403fe21c8203ffd8a4101ffcc52081afe6290407feb148200bf58a4101ff8c520897ff5290401ff2948225ff14a4100ffe8520807bf4290403ff2148201ff5
  | 7 => 0x300100100600900700304100100902f00900200100002201b05200500100400500800200b01600100000201000200c00200e00100100200100900100000200000200200700600c00100000a00d00000600a01900600200502300400000400300000000100b00c00200000800e00200b00000200200700001900200100100600c00500002000400b00300100200d00400100a00100100000000100700000600100700200100500700100501a00000100300200000000200100301400100501e00a00100001400300601a00000000200700200000000002700000000100700200000300200a00000600300000700200000100000400300a00101000600000200100900300f00500f00800c00200400101200000000100100200700000000000600a00601c00200001a00000000000000200100600000900000000800800800500100200000000400301601000e00200400102101200000200000102d00500000000000000600a00500100200200900100000000500401500200d00700600000a00200101300000001200a00000300000001600100d00200100000000000400000000400700000100b00b00301000100900000000f00b00600201000502700000000a01000100300800100201600100800800202b00100100000000100000600000300500100001f00b00100002e00100200500000800000a01002d00100700002d00800200200000000000000000201200300a00e00100000001000100000000100000702800d00000400000200300100100000300401200000000dfec8aa007fe5455003bf2a2a801ff1515400f78a8aa0073c5455001ffb1aa800bfd8d54007bec6aa002df6355001ff31aa800ff58d54007f8c6aa002fc6355001ee31aa800b718d5400ffe86aa007bf4355003fe21aa800ffd8554005fec2aa003fe6155001feb0aa800ff1855401df8c2aa00bff5155005bfa8aa802ff1455400ffe82aa007bf4155003fe20aa800ffd8154005fec0aa003fe6055001feb02a800ff18154005f8c0aa007ff4055003fe202a801ef10154007fecb21802ff6590c53ff32c8602bf99643007facb21802fd6590c53fe32c8602bf1964300dfac921807ff5490c53dfaa48601ff9524300ffaa921807fc5490c03de2a48601bf98e4314ffea721803fe5390c53fe29c8601ffd0e4300f7e8721807df4390c03fe21c8601f710e43007fec521803fe6290c0d7f3148600ff58a43005fac521803fc6290c53ffa948629ff14a4300ffe8521807bf4290c03fe2148600ffd8643007fcc32180efe6190c01feb0c8600bf58643007f8c3218a7ff5190c53fe28c8601ffd064300f7e8321807fc4190c01ffb048600ff98243005fcc121803fd6090c017eb048600ff1824314ffea1218a7fc5090c03ffa048601ff1024300f788121803ff6550c0
  | 8 => 0xcf9b0500a4a41e0007b46f48c19720003880b200015e91e49ac465e2b9e17e11a5d4000000000b3cc4e5f08ac0ac7a94c94fe1d1ada06e000b285ff8325a938747b374000000a183f90006e800043b00036d0000003bb329a6081228304002200072c000000a621e24662a64600340a2a4017d95554846e5dc1642860000008f74bc8ce6f50000d6c2cabe86c4134fa2e83a2a48b34000a0200035400096a69cc0c1e971b8fe4d8ca97ec000000981000ac60004a7000438365cc6000621530ab243c89e3e41132e011156264f6c47ca83b3010e604c3fd5f856bc3059b4ab47a0007b90000000000000000001580005045368920003f700039a4515066b8c6263806c000000000753000c560004793fc26e5070110009c80da0000002fa282324aaeb36000c940007f0000000adeadcb0e3490006ce8672600000000001181e05b10009d41de6f27c8ca278c0003c2bee000b6600000024c096728b8d22ab44497c1e1204f61d0ac451490602045e0a8b1997627ab90a4e3c059631e66801b05b0e0cdf4304cbaad590bb23724ec9ae3fbbba457a46bf4080b5c16284a9c64c36d809724a31641205244c0c20ba1414fb5605664803e0116c983f171280878a661aea2220f53e898841c3fa00009ecca0003b900046c2324c29a825e000000000000b740003d6000a388e60004545e3b2e94800097c0000005d65a53ac9be23e18251198c00039ead8550caf8521260b449ccc21593a407800100e00900000100000000000100300000700100600000000000400000200000000700100200300000400600100400200401600800000000000200000100300401f00200200000100000200600900000a00000f00400100000000500400300100202e00100100300600400100800e00200200000000800300100d00200000002200d00200000100000000100801200400100100300201100500000700400000000d00600300500000500500700100d00400401100000900100000600701a00201500002b00000000001b01500000100300400200700900400000000000000000100800000000500000000600f00d00700000400000102400f02200101601800201d00300001600a00201e01f00000000400000000000100701500300200000100702a00200000100700d00000000000000a00000000000200f00300600300100300300100000900101200c00701000101000100100702d01101500900900400a00400702001c00400300500200200000d01400000000300700402900000800c00900200003202801f00300700300100a00000100000100300000400302900000c01700000000100b00300000100600900103000000200000001a00000c01100100200201e00100200600100000100300100100000000100f00000000001200000000100000100c
  | 9 => 0x7010000000002ba34d7beafe4e40003b4000bd400070a40b21730436a000b2652e369576000a7c0005aa1c8b40cc403381e67ec2668f61636e8cc83e35c73ecbd1fc1f22d359400000027e0003bf670000000ace0003d3000884000000000a03cbb3c12d26554340002fc1b4000000a2a028b6eb0673a61c2d600045f90802600011c45a0009e6000be245d0fc29e00028ea664910cea769445fc6732384c6546c861683412a809a56eca88108f867cbf227481c6f71c66be22560695c018415000a5a1a65220001f030c000000000000b03000000614cbfaca295762c1888c6a0398000000cdb00000049f3b100000041665f000067690962c807ce2b24ac477af65c20009a044000006a0b8b880100ff8543d100000097a9a27096222c9cbc6f029c0000006d050a000a3e4d60000000f865ec960006716ee0132d08b4bbe39f000090000ac20003fe0005e6c8c498a1c3833f57664523ab76a34b8b25ee61d38e1ee307bfc0c827294a000c1c4f40007481a8ae0a7a736254bc69645568dc0008f46291fa9a62f0236000708b9a1e600000034ccc000037a334000000c5e28c00002b0005da61f03538fae817a2f405d4ce00037667d5f4bf03e90000008ca0006da00065760cbc456c0002f5aac000980c140003d76720006ffc8a2b8cadb62574bde8724358819d073208600065114e4377faa3267aac000081a00060000066a5f6cb87d59ce52000000039d3f30a400061b7e606f0009789ee92954e6b600000039b6200000d8000000000306202000b243ed414000bb83e716c22e6e68c3af4a149201bc0000000000003180000000000000000007390000007c274e0008aa000b56c9c2dc9e4b427062160e87ad62b9925bc00000000000088a62d71a12c00057c0004b24b00003d50129578c821a7d21ba2ee1d517226c43dcb2896822946000682c3a1ac3b502990e0fb070000cba3e50dc000000518ba847d154c6a93c000218000b467f64436ec46459c92458e1c04cc8482be5a2a0a57e8ee79867b8340327d8b323de49e34a27806542832044f4d4a4483d0878389ea181276bb06897303eb77a1769f29c42b41dc000b64a6e3287540f693619c67fc7a0b6932214000c6ec1059ebdc000c908508861668368b0200444000ca09e20009000006531b00008cb01e0c40bc538a5c5693730b545c81843eadfb58bae00055e000cd49f4302b0a66200032c0a0cde58cc660302309167ea00000073815224821ca0400000080600059a21e0008f62984b61227cc35e83067938257a6b3bf64dc3795a795f142680b6c8206c82bf000000000000be828700000005648491a459cd60003cd0006a20000c60007187ab2f10000000540000000af0f02569cc4824fc074b9ca3c5a4912a36c080008455a868d8ec9ba83a1d468b00000842f83c78e3
  | 10 => 0x1322640009c240435db0c000000c9a0000000000000001300006fe000000c2031a7006b2a5052ab180000000004ff95d3da00093056480a98a8c04a2b540ec3448c244d28566355c0c0bce6594566981b801dbfba2caa447218c5783ec0b079e7f442eaa287616f55ac0238093877876876c00e4da00014879c4aa9aa468b003b21d2c3c03642c6528437b14f87e818aa3a77e4e233a9c03cbbec8d0294b725de2503863c31041f6a4cbe68de31011484eb9651e29223c11e1747dc470042cb980287a80c4460000ea32295a13b0006b79844af000000b800009d8c747ba934bfd0007a58ba000000425c7e9dc5a67346c6ab632aa8756f0068e0000ac8c4cbaa0000ee2849745707c66b1a9200000000036448a4080006767df7863a71284103cc4189bc3ea00059d3620001f45c80000008331500d24c438c6941128582cea1630a0000f7000000000c423c9146c446331ce7daa7499a75aa5e592b92000ca600004a00049075037c000000922cb05b4478000000000ab83d80002ea4ba79400000000000000000042400035bcb6000000000000000a7e62800078267400017000025505e00000047100061565b0007b80001026394235af33e000062000000000c2a00005834e34600089847f00015ca0500000000050263117c4cf53424300027c666c956c275e000bd05fa12ea223b0000060186000000bea0004369264fd7d64414d0a2e4750000008903f80008d400000038dc2e000019000000000406000a26000c6c00000000000000000035a0000d0c70000524b760000002660003a600009c634024219a0e462cc846f35900079a18e3ae05c96024029d42a00029b0000009021a20001f10485b8af873c476704b2278411b000000000b4cc009b6000000b7c000bb4000000cb38c671e13950fb176086bc8fa00061eb129ac00000098e0000be208031ba216e714481a8e3774486ca064c764ae7de62f246066c9e1cd3f633c8e85cc4830006919280000000ae85c000c5c4a00002d4000000326a100004a89820004555f292c0009b43f4252b98996000134b4a0006306b47561b5270360000000bbc8703b65847a07d482800029a00068843f1960000000004ad5d2000b7023400012a69a000000bf3147367617a8269701c862b820000009e00000002cba1e3af0007d7acc00000000016023a4860000003084177a200000060437e473af2000000bf87424881cc3bd94ec540009fe000000000b08a52b5a28aafc088487000249632000b2ca857969faa8880e94c42697e65db947fe02a3b35baaa6461a420003f288818000010ec3800065c6b91fe22c5c446d000000375000856000a9e2206920000000000005289b22970002c100000000000000000019829f0000000000003ad0003a02bc95e0002e20008d81f360a77400000000000
  | 11 => 0xac63e7aa9900004960cc3612a58e40009ca000c5ac1a20ea8a0000000e20001a05580762da804b6aa061be624cb70612c366000000053200091800020c000000b8a0006e00004395990000003514096108a462375c385039390b7e7a403c702a9a0000001e10005d19980000005d825800091000000068ea634a3c1258a3ceb4e00000087c000be00168c45120005880003381ae391a3482e0003a1b8600068c226ca563715621d000000015000c3600082c0000000009db1c29f810aaee6a4ae60004c810851636891c1da000c4865a2a219436ccae1ec1f82d16ae6a85e066e6de6d49d20008010004f951c2aa7608640007fc33f8eda5872a64662a19e5409428a05b06f925b4ee082a5652d000aa0cda40784468593e816bca4b40fa8fc4890001c4300000000ca77721b2aaa00048e9de000405b1a70e56a00057200020493a9dd000c243f04008d66780001440f21922a0979a96a6acdcad06d20008e264c63a8bd6400004a4ab000000000022400000000026800000000000048d8749523a844b63513539416a3dccaa0000004eab7a580092bdaa644932b0bb6cb5ba4c7c6cc8787b6c9272085f70707a4e8684c848240fd6832c24327e2421950a24a5f244ad2554ad633dc0e3965ae4588a21d805033bc50a9021017103ba302c68429047d047e8946bd9f653c7264423365be733000c68a2851092a09849905f5c03ee675cd7b0192e758619a27000b8c45b00020a000000000837b79000cac5d0cb16af6dc000940695b14000648000330431cd22c4508860342bc04b89e58b66260000000000002fe96c4d24ca000a612d8000ad4c04a1a6540000000000ca000381357bfa0f9744000000a86000000bc89a437095400000025a5862909561a468ab1008c30e82ab200003322c0384000494cd80000000140002de0000003782ae4500e7000000b7806da990007b32894de000abca1263c9a3000c060006018bb9662420005e41d30f48824a100015a6e40000000000d42c8cab96850ea0c3925cf7eeb0240c2f8bd6000a548a8866a176aa046a782ca47414a0000000680006640000000009d9a72485a196f80000008be212c883c7bd8000000b480007400000008da0000006fc0000000001100008b821352c6505ce3d9389000000c647f2af031c69385e00036fc0a4534332067227f8000000a9859f74a2454277bc00087eb041906fa00000c17854c2887e4c3e314000b2a04403a0005980004693bcc52a8c6778bc4e67a748c32e6362f65b6cce000c586180003df100000b16b3840ea94000000a840006a690a00000014c6c06866565820000006ba6b00006f60006e28260001cf7c099429652b88e1e47e03c526a08aba644ac778c9000492000000000835764c7800000000053e00a89a0008a65a076e7bb0000009869d603844e
  | 12 => 0x4e00e4cd000000000038a0006d619a2ec4f2000138017000000000b680001ebc725ac76b9da10d5ea788072aa868177c84086a1151376adb3e348bacc603d2cb40002ef50302e3ef00066c00062709479255242213c7464952b65ca0003523b88006b55e500000000085a3e6696000a680005c60000aa0002f20009fc0009700003ca3d4a9c000000bcc7a813a61100005a5443b78140004c072414918864241d1b646b4be505b5eca47c474cb842c58ef00070c0008f2000000c917ae00042900000037164e31200000004e000106000a80000c4047cae20003ddc4a4f0000ab4b1c13600039c0000000000004a57aca08b3aaba41a5fe41f1240000002e699c9f000038b97b3589583c621f60e53a3d00840009e8bd20007190004a948b280a2050c00000000027d0003be10b3c8b605427a600040a7707761ca53fae413f02c00035313e140716c933aa41986e6bb5260000004204a6463cccc2279062e22836b62c35f90c86184cb1e8ea0000002acc34be469e00000048f00071f2cc6fbaec00026260200089c000b056ea0003e299e7b007c18f42b6d3355afa8f01aa1ea7b224e1e3658b8ec828ae71cca31edb5035021564a5ec3c400042d5b296ebfe00400000054a0fec32c16cddb7b6250a600036625c8460de687b3000000000072e07e000000340000356000000c8e18441bba03db34f2a4752000000000000000a001d6568cbe00000061a0958d29b861264443ac28a70227710000b5278051a10c1e803e36300000009b01a46a0000009145e80008804023a90009eca6c002bc23ba2e486808e6
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xd6454010006de6354010006dd6354010006ee6254010006ed625401004cff769001001cfe769001000cfd769001001cfc76900100b67e65900100067d659001000ebe6490010006bd6490010006de6390010006dd6390010006ee6290010006ed629001001df67190010005f5719001004cff76500100ae7e65500100067d655001000ebe6450010006bd6450010006de6350010006dd6350010006ee6250010006ed6250010004fd76cc0100a67e65cc0100067d65cc01009ebe64cc010006bd64cc010006de63cc010006dd63cc010006ee62cc010006ed62cc01001df471cc010007d731cc010004ff768c010004fd768c0100967e658c0100067d658c01008ebe648c010006bd648c010006de638c010006dd638c010006ee628c010006ed628c01001df6718c010005f5718c0101afd4318c010004ff764c0100057f754c01002d7c754c0100867e654c0100067d654c010005bf744c010025bc744c01007ebe644c010006bd644c010006de634c010006dd634c010005ef724c010005ec724c010006ee624c010006ed624c010005f7714c01001df4714c010007d7314c010004ff760c01001cfe760c010004fd760c01001cfc760c0100767e650c0100067d650c01006ebe640c010006bd640c010006de630c010006dd630c010006ee620c010006ed620c01001df6710c010005f5710c0101a7d4310c010004fd76c801019e7e65c80100067d65c8010196be64c8010006bd64c8010006de63c8010006dd63c8010036ee62c8010006ed62c801001df471c8010157e721c8010004ff7688010034fd768801018e7e65880100067d6588010186be6488010006bd6488010006de6388010006dd6388010036ee6288010006ed628801001df67188010005f5718801017fe42188010004ff76480100057f754801002d7c75480101767e65480100067d6548010005bf7448010025bc744801016ebe6448010006bd6448010005df7348010005dc7348010006de6348010006dd6348010036ee6248010006ed6248010005f7714801001df47148010007e7214801001cfe7608010004fd760801001cfc7608010025be7408010005bd7408010166be6408010006bd6408010006de6308010006dd630801001df67108010005f5710801015fe4210801001df77644010006f77644010004f7764401000777754401000774754401001f76654401001f756544010007b77444010007b4744401001fb6644401001fb56444010007d77344010005f67344010005f47344010007d47344010005d4734401001fd6634401001fd56344010007e77244010155f67244010155f47244010007e47244010005e4724401001ef7624401001fe66244010006f5624401001fe56244010006e5624401001df7704401001ff37044010006f6604401001ff26044010
  | 1 => 0x81000ebe6490810006bd6490810006de6390810006dd6390810036ee6290810006ed6290810004ff765081001cfe7650810004fd765081001cfc765081021e7e65508100067d655081000ebe6450810006bd6450810006de6350810006dd6350810036ee6250810006ed6250810005f7715081001df47150810004ff76cc81001cfe76cc810004fd76cc81001cfc76cc8102167e65cc8100067d65cc81020ebe64cc810006bd64cc810006de63cc810006dd63cc810036ee62cc810006ed62cc81001df671cc810005f571cc810207d431cc810034ff768c81001cfe768c810004fd768c81001cfc768c81002d7e758c8100057d758c8101fe7e658c8100067d658c810025be748c810005bd748c8101f6be648c810006bd648c810006de638c810006dd638c810036ee628c810006ed628c81001df6718c810005f5718c810004ff764c81001cfe764c810004fd764c81001cfc764c8101ee7e654c8100067d654c8101e6be644c810006bd644c810006de634c810006dd634c810036ee624c810006ed624c810005f7714c81001df4714c8101dfd4314c810034ff760c81001cfe760c810004fd760c81001cfc760c8101d67e650c8100067d650c8101cebe640c810006bd640c810006de630c810006dd630c810036ee620c810006ed620c81001df4710c81001df576cc410006f576cc41001f7665cc41001f7565cc41001fb664cc41001fb564cc41001df673cc41001fd673cc41001ef763cc41001fd663cc410006f563cc41001fd563cc410006d563cc410155f672cc41001ef762cc41001fe662cc410006f562cc41001fe562cc410006e562cc410007d632cc410007d432cc410005f570cc41001ff260cc41001df576c8410156f576c8410004f576c84101577675c84101577575c841001f7665c841001f7565c8410157b674c8410157b574c841001fb664c841001fb564c8410005f673c8410157d673c8410005d673c8410157d573c8410155f473c841001fd663c841001fd563c841001df672c841001fe672c841001ef762c841001fe662c8410156f562c841001fe562c8410006e562c8410007e732c8410157e432c8410005f570c841001ff260c8410014fe7598010054fd7598010014fc759801000cfe749801004cfd749801000cfc7498010004fe7398010004fd7398010034fe7298010004fd729801001cfd7198010006f7319801001ef431980101c6f7219801001ef4219801001cfe709801001ef7109801001efb109801001ef81098010054ff769401001cfe7694010014fd769401001cfc76940100167e65940100067d65940101bebe6494010006bd6494010006de6394010006dd6394010006ee6294010006ed629401001df67194010005f57194010054ff76540100167e65540100067d65540101b6be6454010006b
  | 2 => 0x57f7550c1002d7c7550c101467e6550c100067d6550c1000ebe6450c10006bd6450c10006de6350c10006dd6350c100279c4350c10005f77150c1001df47150c10036ef7598810036ee7598810036ed7598810036ec7598810036ef7498810036ee7498810036ed7498810036ec7498810006ef5498810006ee5498810006ed5498810006ec5498810036ef7398810036ee7398810036ed7398810036ec7398810006ef5398810006ee5398810006ed5398810006ec5398810006ef4398810006ee4398810006ed4398810006ec439881001eef719881001eee719881001eed719881001eec719881001eef519881001eee519881001eed519881001eec519881001eef419881001eee419881001eed419881001eec419881001eef319881001eee319881001eed319881001eec3198810036ee7098810036ec7098810006ef5098810006ec5098810006ef4098810006ec409881001eef109881001eee109881001eed109881001eec1098810004ff7558810014fe7558810014fc7558810004ff745881000cfe745881000cfc7458810004ff7358810004fc735881001eef7258810006ef5258810006ec5258810006ef4258810006ec425881001cff715881001cfe715881001cfd715881001cfc715881001ef4715881001cf4715881001ef4315881001eee215881001eec215881001ef4215881001ee42158810034ff705881001ef71058810006ef7558810006ee7558810006ed7558810006ec7558810006ef7458810006ee7458810006ed7458810006ec7458810006ef5458810006ee5458810006ed5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef5358810006ee5358810006ed5358810006ec5358810006ef4358810006ee4358810006ed4358810006ec435881001eef715881001eee715881001eed715881001eec715881001ee4715881001eef515881001eee515881001eed515881001eec515881001eef415881001eee415881001eed415881001eec415881001eef315881001eee315881001eed315881001eec315881001ee43158810006ee7058810006ec7058810006ef5058810006ec5058810006ef4058810006ec405881001eef105881001ee7105881001eee105881001eed105881001eec1058810034ff769481001cfe7694810004fd76948100167e65948100067d6594810236be6494810006bd6494810006de6394810006dd6394810036ee6294810006ed6294810004ff765481001cfe7654810004fd765481001cfc76548100167e65548100067d655481022ebe6454810006bd6454810006de6354810006dd6354810036ee6254810006ed6254810005f7715481001df47154810034ff769081001cfe7690810004fd769081001cfc76908102267e65908100067d659
  | 3 => 0xc7598c1000cfe7498c10004fd7498c1000cfc7498c1001ede7398c10006df5398c10006dc5398c10006df4398c10006dc4398c10034fe7298c10004fd7298c1001cfe7198c1001cfc7198c1001ede3198c1001edc3198c10006df7598c10006de7598c10006dd7598c10006dc7598c10006df7498c10006de7498c10006dd7498c10006dc7498c10006df5498c10006de5498c10006dd5498c10006dc5498c10006df7298c10006de7298c10006dd7298c10006dc7298c10006df5298c10006dc5298c10006df4298c10006dc4298c1001edf7198c1001ede7198c1001edd7198c1001edc7198c1001edf5198c1001ede5198c1001edd5198c1001edc5198c1001edf4198c1001ede4198c1001edd4198c1001edc4198c1001edf2198c1001ede2198c1001edd2198c1001edc2198c10006de7098c10006dc7098c10006df5098c10006dc5098c10006df4098c10006dc4098c1001edf1098c1001ede1098c1001edd1098c1001edc1098c10004ff7558c10014fe7558c10014fc7558c10004ff7458c1000cfe7458c1000cfc7458c1001edf7358c10006df5358c10006dc5358c10006df4358c10006dc4358c10004ff7258c10034fc7258c1001cff7158c1001cfe7158c1001cfd7158c1001cfc7158c1001ef47158c1001cf47158c1001ede3158c1001edc3158c1001ef43158c1009cff7058c1007cfd7058c10006df7558c10006de7558c10006dd7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c10006dc5258c10006df4258c10006dc4258c1001edf7158c1001ede7158c1001edd7158c1001edc7158c1001ed47158c1001edf5158c1001ede5158c1001edd5158c1001edc5158c1001edf4158c1001ede4158c1001edd4158c1001edc4158c1001edf2158c1001ede2158c1001edd2158c1001edc2158c10006de7058c10006dc7058c10006df5058c10006dc5058c10006df4058c10006dc4058c1001edf1058c1001ede1058c1001edd1058c1001edc1058c10004ff7694c1001cfe7694c10004fd7694c1001cfc7694c100167e6594c100067d6594c10246be6494c10006bd6494c10006de6394c10006dd6394c1002f5f5394c10004ff7654c1001cfe7654c10004fd7654c1001cfc7654c100167e6554c100067d6554c10005bf7454c10025bc7454c1023ebe6454c10006bd6454c10006de6354c10006dd6354c10005f77154c1001df47154c10004ff7690c1001cfe7690c10004fd7690c1001cfc7690c1014e7e6590c100067d6590c1000ebe6490c10006bd6490c10006de6390c10006dd6390c10004ff7650c1001cfe7650c10004fd7650c1001cfc7650c10
  | 4 => 0x4110006df6384110006dc6384110006ef6284110006ec628411001dfa708411001ef6768411001cf67684110007776584110007746584110007b76484110007b46484110007d76384110006f66384110006f46384110007d46384110006d46384110005f77284110005f57284110007e762841101c6f662841101c6f46284110007e46284110006e4628411001df6708411001ff3608411001e7f7559410004ff745941000cfe745941000cfc745941002e7f54594100067e545941002e7c5459410004ff7359410004fc735941002e7f535941002e7c5359410004ff7259410034fc725941002e7f525941002e7c525941001cff715941001cfe715941001cfd715941001cfc715941001e7e515941001e7c515941002cfc705941002e7c50594100067f74594100067e74594100067d74594100067c74594100067f73594100067e73594100067d73594100067c73594100067f43594100067c43594100067f72594100067e72594100067d72594100067c72594100067f42594100067c425941001e7f715941001e7e715941001e7d715941001e7c715941001e7f415941001e7e415941001e7d415941001e7c415941001e7f315941001e7e315941001e7d315941001e7c315941001e7f215941001e7e215941001e7d215941001e7c215941002e7f70594100067e70594100067c70594100067f40594100067c405941001e7f105941001e7e105941001e7d105941001e7c1059410004ff7559010014fe7559010014fc755901001ebf7459010006bf5459010026be5459010026bc5459010004ff7359010004fc7359010026bf4359010026bc4359010004ff7259010034fc7259010026bf4259010026bc425901001cff715901001cfe715901001cfd715901001cfc715901001ebe415901001ebc415901000cff705901000cfd7059010024fc7059010026bc4059010006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf5359010006bc5359010006bf7259010006be7259010006bd7259010006bc7259010006bf5259010006bc525901001ebf715901001ebe715901001ebd715901001ebc715901001ebf515901001ebe515901001ebd515901001ebc515901001ebf315901001ebe315901001ebd315901001ebc315901001ebf215901001ebe215901001ebd215901001ebc2159010026bf7059010006be7059010006bc7059010006bf5059010006bc505901001ebf105901001ebe105901001ebd105901001ebc1059010004ff765501001cfe7655010004fd765501001cfc76550100167e65550100067d655501000ebe6455010006bd64550100273c5455010005df7355010005dc7355010005f7715501001df47155010014fe7598c10004fd7598c10014f
  | 5 => 0x36f46288510007e46288510036e46288510005f6708851001ef7608851001ff36088510034fc76485100067f65485100ce7c6548510006bf64485100c6bc6448510006df6348510006dc6348510006ef6248510036ec624851001fe42148510005fb7048510005f87048510034f47648510007776548510007746548510007b76448510007b46448510007d76348510006f66348510006f46348510007d46348510006d4634851001df7724851001fe77248510007e76248510036f66248510036f46248510007e46248510036e46248510007e73248510007e43248510007f37048510005f47048510007f0704851001ef7604851001ff36048510064fe76941100067f65941100167c6594110006bf64941101bebc6494110006df6394110006dc6394110006ef6294110006ec6294110014ff7654110044fd765411001cfc76541100067f65541100167c6554110006bf64541101b6bc6454110006df6354110006dc6354110006ef6254110006ec6254110005f7715411001df4715411005cfe76901100067f65901100b67c6590110006bf649011000ebc6490110006df6390110006dc6390110006ef6290110006ec629011000cff765011003cfd765011001cfc76501100067f65501100ae7c6550110006bf645011000ebc6450110006df6350110006dc6350110006ef6250110006ec6250110005f7715011001df4715011001cfe76cc1100067f65cc1100a67c65cc110006bf64cc11009ebc64cc110006df63cc110006dc63cc110006ef62cc110006ec62cc11001df671cc110005f571cc110004fe768c1100067f658c1100967c658c110006bf648c11008ebc648c110006df638c110006dc638c110006ef628c110006ec628c110004ff764c110004fd764c11001cfc764c1100057f754c1100457c754c1100067f654c1100867c654c110005bf744c11003dbc744c110006bf644c11007ebc644c110006df634c110006dc634c110005ef724c110005ec724c110006ef624c110006ec624c110005f7714c11001df4714c110004fe760c1100067f650c1100767c650c110006bf640c11006ebc640c110006df630c110006dc630c110006ef620c110006ec620c11001cfe76c811001cfc76c81100067f65c811019e7c65c8110006bf64c8110196bc64c8110006df63c8110006dc63c8110006ef62c8110036ec62c811001df671c8110005f571c8110007e521c81100067f658811018e7c6588110006bf6488110186bc6488110006df6388110006dc6388110006ef6288110036ec6288110007e62188110004fd764811001cfc7648110005bf744811003dbc7448110006bf644811016ebc6448110006df6348110006dc6348110005f7714811001df47148110007e521481100067f65841100567c6584110006bf648411004ebc648
  | 6 => 0xf65549100167c6554910006bf645491022ebc6454910006df6354910006dc6354910006ef6254910036ec6254910034ff7690910004fe7690910004fd7690910034fc76909100067f65909102267c6590910006bf649091000ebc6490910006df6390910006dc6390910006ef6290910036ec629091001df67190910005f57190910004ff7650910004fe7650910004fd7650910004fc76509100067f655091021e7c6550910006bf645091000ebc6450910006df6350910006dc6350910006ef6250910036ec6250910004ff76cc910004fe76cc910004fd76cc910004fc76cc9100067f65cc9102167c65cc910006bf64cc91020ebc64cc910006df63cc910006dc63cc910006ef62cc910036ec62cc910034ff768c910004fe768c910004fd768c910034fc768c9100457e758c9100057d758c9100067f658c9101fe7c658c91003dbe748c910005bd748c910006bf648c9101f6bc648c910006df638c910006dc638c910006ef628c910036ec628c91001df6718c910005f5718c910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c9101ee7c654c910006bf644c9101e6bc644c910006df634c910006dc634c910006ef624c910036ec624c910034ff760c910004fe760c910004fd760c910034fc760c9100067f650c9101d67c650c910006bf640c9101cebc640c910006df630c910006dc630c910006ef620c910036ec620c91001df6710c910005f5710c910014fc76545100067f65545100167c6554510006bf6454510136bc6454510006df6354510006dc6354510006ef6254510006ec6254510005fb7054510005f8705451000cfc76505100067f65505101267c6550510006bf645051000ebc6450510006df6350510006dc6350510006ef6250510006ec6250510005fb7050510005f87050510004fe76cc5100067f65cc51011e7c65cc510006bf64cc510116bc64cc510006df63cc510006dc63cc510006ef62cc510006ec62cc510005fa70cc510005f970cc510004fc764c5100067f654c5100fe7c654c510006bf644c5100f6bc644c510006df634c510006dc634c510006ef624c510006ec624c510005fb704c510005f8704c5100457e75c85100057d75c85100067f65c85102567c65c851003dbe74c8510005bd74c8510006bf64c851024ebc64c8510005de73c8510005dd73c8510006df63c8510006dc63c8510006ef62c8510036ec62c8510005fa70c8510005f970c8510005f6768851001ef67688510004f6768851001f76758851001f75758851000777658851000774658851001fb6748851001fb57488510007b76488510007b4648851001fd6738851001fd57388510007d76388510006f66388510006f46388510007d46388510006d46388510005f57288510007e76288510036f66288510
  | 7 => 0x8910006ec73d8910006ef53d8910006ee53d8910006ed53d8910006ec53d8910006ef43d8910006ee43d8910006ed43d8910006ec43d8910006ef71d891017eee71d8910006ed71d891017eec71d8910006ef51d891017eee51d891017eec51d8910006ef41d891017eee41d891017eec41d891017eee31d891017eec31d891017eef70d8910006ed70d8910006ef50d8910006ec50d8910006ef40d8910006ec40d891017eef10d891017eec10d89100457e75989100057d75989100067f65989100067c659891003dbe7498910005bd7498910006bf6498910006bc6498910005de7398910005dd7398910006df6398910006dc6398910006ef62989100057f75589100457c75589100067f65589100067c6558910005bf745891003dbc7458910006bf6458910006bc6458910005df7358910005dc7358910006df6358910006dc6358910004ff7458910006bf7458910004bf745891000cfe745891000cfc7458910006bc745891000cbc7458910004ff7358910006df7358910004df7358910004fc7358910006dc7358910004dc7358910006f77158910004ff7058910006fb7058910004fe76189100067f65189100067c6518910006bf6418910006bc6418910006df6318910006dc6318910036ee6218910006ed6218910005ee7618910006ee7618910004ee7618910006ef65189100076f65189100066f6518910006ee6518910006ed6518910006ec65189100076c65189100066c6518910006ef6418910007af6418910006af6418910006ee6418910006ed6418910006ec6418910007ac6418910006ac6418910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc6318910007e5711891015feb101891015fe81018910036ef7518910036ee7518910036ed7518910036ec7518910036ef7418910036ee7418910036ed7418910036ec7418910006ef5418910006ee5418910006ed5418910006ec5418910036ef7318910036ee7318910036ed7318910036ec7318910006ef5318910006ee5318910006ed5318910006ec5318910006ef4318910006ee4318910006ed4318910006ec4318910036ef7118910036ee7118910036ec7118910006ef511891015eee511891015eec5118910006ef411891015eee411891015eec411891015eee311891015eec3118910036ef7018910036ed7018910006ef5018910006ec5018910006ef4018910006ec401891015eef1018910006ed101891015eec1018910034ff7694910004fe7694910004fd7694910034fc76949100067f65949100167c6594910006bf6494910236bc6494910006df6394910006dc6394910006ef6294910036ec629491001df67194910005f57194910004ff7654910004fe7654910004fc76549100067
  | 8 => 0x8cfe7018d1006cfc7018d10005de7618d10006de7618d10004de7618d10006df6518d100075f6518d100065f6518d10006de6518d10006dd6518d10006dc6518d100075c6518d100065c6518d10006df6418d100079f6418d100069f6418d10006de6418d10006dd6418d10006dc6418d100079c6418d100069c6418d101a7db1018d101a7d81018d10006df7518d10006de7518d10006dd7518d10006dc7518d10006df7418d10006de7418d10006dd7418d10006dc7418d10006df5418d10006de5418d10006dd5418d10006dc5418d10006df7218d10006de7218d10006dd7218d10006dc7218d10006df5218d10006dc5218d10006df4218d10006dc4218d10006df7118d101a6de7118d10006dd7118d101a6dc7118d10006df5118d101a6de5118d101a6dc5118d10006df4118d101a6de4118d101a6dc4118d101a6de2118d101a6dc2118d101a6df7018d10006dd7018d10006df5018d10006dc5018d10006df4018d10006dc4018d101a6df1018d10006dd1018d101a6dc1018d10004ff7694d10004fe7694d10004fd7694d10004fc7694d100067f6594d100167c6594d10006bf6494d10246bc6494d10006df6394d10006dc6394d100475f5394d10004ff7654d10004fe7654d10004fd7654d10004fc7654d100067f6554d100167c6554d10005bf7454d1003dbc7454d10006bf6454d1023ebc6454d10006df6354d10006dc6354d10004ff7690d10004fe7690d10004fd7690d10004fc7690d100067f6590d1014e7c6590d10006bf6490d1000ebc6490d10006df6390d10006dc6390d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100057f7550d100457c7550d100067f6550d101467c6550d10006bf6450d1000ebc6450d10006df6350d10006dc6350d1003f9c4350d100067f65d89100067c65d8910006bf64d8910006bc64d8910006df63d8910006dc63d8910014fe75d8910004fd75d8910014fc75d891000cfe74d8910004fd74d891000cfc74d8910004fe73d8910004fd73d8910006ef52d8910006ec52d8910006ef42d8910006ec42d891001cfe71d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d8910007e771d891017feb10d891017fe810d8910006ef75d8910006ee75d8910006ed75d8910006ec75d8910006ef74d8910006ee74d8910006ed74d8910006ec74d8910006ef54d8910006ee54d8910006ed54d8910006ec54d8910006ef73d8910006ee73d8910006ed73d
  | 9 => 0xc5455110005df7355110005dc73551100067f65d8d100067c65d8d10006bf64d8d10006bc64d8d10014fe75d8d10004fd75d8d10014fc75d8d1000cfe74d8d10004fd74d8d1000cfc74d8d10006df53d8d10006dc53d8d10006df43d8d10006dc43d8d10034fe72d8d10004fd72d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d101afdb10d8d101afd810d8d10006df75d8d10006de75d8d10006dd75d8d10006dc75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df52d8d10006dc52d8d10006df42d8d10006dc42d8d10006df71d8d101aede71d8d10006dd71d8d101aedc71d8d10006df51d8d101aede51d8d101aedc51d8d10006df41d8d101aede41d8d101aedc41d8d101aede21d8d101aedc21d8d101aedf70d8d10006dd70d8d10006df50d8d10006dc50d8d10006df40d8d10006dc40d8d101aedf10d8d101aedc10d8d100457e7598d100057d7598d100067f6598d100067c6598d1003dbe7498d10005bd7498d10006bf6498d10006bc6498d10006df6398d10005ee7298d10005ed7298d10014fe7598d100067e7598d100147e7598d10004fd7598d100067d7598d100047d7598d10014fc7598d1000cfe7498d10006be7498d1000cbe7498d10004fd7498d10006bd7498d10004bd7498d1000cfc7498d10004fe7398d10004de7398d10034fe7298d10006ee7298d10034ee7298d10004fd7298d10006ed7298d10004ed7298d10004fd7198d10006f57198d10004fd7098d10006f97098d100057f7558d100457c7558d100067f6558d100067c6558d10005bf7458d1003dbc7458d10006bf6458d10006bc6458d10005ef7258d10005ec7258d10004ff7558d100067f7558d100047f7558d10014fe7558d10014fc7558d100067c7558d100147c7558d10004ff7458d10006bf7458d10004bf7458d1000cfe7458d1000cfc7458d10006bc7458d1000cbc7458d10006df7358d10004ff7258d10006ef7258d10004ef7258d10034fc7258d10006ec7258d10034ec7258d10004ff7158d10006f77158d10004f77158d10004ff7058d10006fb7058d10004fe7618d100067f6518d100067c6518d10006bf6418d10006bc6418d10006dd6318d10014fe7518d10004fd7518d10014fc7518d1000cfe7418d10004fd7418d1000cfc7418d10006de7318d10006df5318d10006dc5318d10006df4318d10006dc4318d10034fe7218d10004fd7218d1001cfe7118d1001cfc7118d10
  | 10 => 0x95102767f10d95102767c10d95100467c6559510005bf745951003dbc7459510005df7359510005dc7359510005ef7259510005ec7259510044ff75595100067f7559510004ff7459510006bf7459510004bf745951000cfe745951000cfc7459510006bc745951000cbc7459510004ff7359510006df7359510004df7359510004fc7359510006dc7359510004dc7359510004ff7259510006ef7259510004ef7259510034fc7259510006ec7259510034ec7259510054ff7159510006f77159510064ff7059510006fb70595100057e76195100467e76195100047e76195100067e64195100067c641951026e7f601951026f7b101951026f78101951000cfe76d91100067f65d91100067c65d911003ebe64d9110014fe75d9110004fd75d9110014fc75d9110006bf54d911003ebe54d911003ebc54d9110004fe73d9110004fd73d911003ebf43d911003ebc43d9110034fe72d9110004fd72d911003ebf42d911003ebc42d911001cfe71d911003cfd71d911001cfc71d911003ebf41d911000cfe70d911001cfd70d911000cfc70d911003ebf40d911003dbe76d911000cbe76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110267bb10d9110267b810d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006bc52d9110006bf71d9110266be71d9110006bd71d9110266bc71d9110006bf51d9110266be51d9110266bc51d9110266be31d9110266bc31d9110266be21d9110266bc21d9110266bf70d911003ebe70d9110006bd70d9110006bf50d9110006bc50d9110266bf10d9110266bc10d91100057f75591100457c75591100067f65591100067c655911003ebc6459110005df7359110005dc7359110005ef7259110005ec7259110004ff75591100067f75591100047f7559110014fe7559110014fc75591100067c75591100147c755911003cff7459110006bf7459110004ff7359110006df7359110004df7359110004fc7359110006dc7359110004dc7359110004ff7259110006ef7259110004ef7259110034fc7259110006ec7259110034ec725911004cff7159110006f7715911005cff7059110006fb7059110005be761911003ebe7619110004be7619110006bf65191100073f65191100063f6519110006be6519110006bd6519110006bc65191100073c65191100063c651911025ebf601911025fbb101911025fb81019110004ff7655110004fe7655110004fd7655110004fc76551100067f65551100167c6555110006bf645511000ebc645511003f3
  | 11 => 0x1c5f6720c610006f7620c610006f5620c610007d7320c610007d5320c610005f5700c61001ff2600c6100557e75c86100057d75c861004dbe74c8610005bd74c8610005de73c8610005dd73c8610036ee62c8610006ed62c8610005fa70c8610005f970c86101c77675c86101c77575c86101c7b674c86101c7b574c8610005f673c86101c7d673c8610005d673c86101c7d573c86101c5f473c86101c6f762c86101c7e662c86101c6f562c8610007e562c8610007e732c86101c7e432c86101c7f270c8610005f570c86101c7f170c861001ef660c8610034ff7648610036ee6248610006ed624861001fe42148610005fb7048610005f87048610005f5760861001ef57608610005f6730861001df4730861001fe672086101c6f76208610007e76208610006e762086101c6f562086101c7e46208610005f5700861001ff2600861001cfd76942100167e65942100067d659421001df67194210005f5719421002cff76542100067f65542100167c655421001cfd769021000ebe6490210006bd649021001df67190210005f57190210024ff7650210006bf645021000ebc6450210006df63cc210006dc63cc210007d731cc21001cfd768c210006de638c210006dd638c21001df6718c210005f5718c210007d4318c2100057f754c2100557c754c210005bf744c21004dbc744c210006df634c210006dc634c210005ef724c210005ec724c210005f7714c21001df4714c210007d7314c21001cfd760c210006de630c210006dd630c21001df6710c210005f5710c210007d4310c210036ec62c82101c7e721c821001cfd768821001df67188210005f57188210007e42188210005f576c421001ef576c4210005f673c421001df473c42101c5f672c421001df472c4210006f762c4210006f562c421001ff260c4210014fe76d95100467e65d951000cfe74d9510004fd74d951000cfc74d95100467f54d95100067e54d95100467c54d9510004fe73d9510004fd73d95100467f53d95100467c53d9510034fe72d9510004fd72d95100467f52d95100467c52d951001cfe71d9510044fd71d951001cfc71d95100467f51d951001cfd70d95100467f50d95100457e76d95100147e76d95100067e64d95100067c64d95102777b10d95102777810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067c42d95100067f71d95102767e71d95100067d71d95102767c71d95100067f41d95102767e41d95102767c41d95102767e31d95102767c31d95102767e21d95102767c21d95102767f70d95100467e70d95100067d70d95100067f40d95100067c40d
  | 12 => 0xe7694e10004fd7694e10004fc7694e100067f6594e100167c6594e100575f5394e10004ff7654e10004fe7654e10004fd7654e10004fc7654e10005bf7454e1004dbc7454e10005f77154e1001df47154e10004ff7690e10004fe7690e10004fd7690e10004fc7690e10006bf6490e1000ebc6490e10004ff7650e10004fe7650e10004fd7650e10004fc7650e100057f7550e100557c7550e1004f9c4350e10005f77150e1001df47150e1000cfe74d8a10004fd74d8a1000cfc74d8a10004fe73d8a10004fd73d8a10006fa70d8a10006ef6298a100057f7558a100557c7558a10005bf7458a1004dbc7458a10005df7358a10005dc7358a10004ff7558a100067f7558a100047f7558a10014fe7558a10014fc7558a100067c7558a100147c7558a10004ff7458a10006bf7458a10004bf7458a1000cfe7458a1000cfc7458a10006bc7458a1000cbc7458a10004ff7358a10006df7358a10004df7358a10004fc7358a10006dc7358a10004dc7358a10006ef7258a100557e7518a100057d7518a1004dbe7418a10005bd7418a10005de7318a10005dd7318a10036ee6218a10006ed6218a10034ff7694a10004fe7694a10004fd7694a100067f6594a100167c6594a10004ff7654a10004fd7654a10004fc7654a100167e6554a100067d6554a10005f77154a1001df47154a10034ff7690a10004fe7690a10004fd7690a10006bf6490a1000ebc6490a10004ff7650a10004fe7650a10004fd7650a10004fc7650a1000ebe6450a10006bd6450a10005f77150a1001df47150a10004ff76cca10004fe76cca10004fd76cca10004fc76cca10006de63cca10006dd63cca1001df671cca10005f571cca10034ff768ca10004fe768ca10004fd768ca100557e758ca100057d758ca1004dbe748ca10005bd748ca10006df638ca10006dc638ca1001df6718ca10005f5718ca10004ff764ca10004fe764ca10004fd764ca10004fc764ca10006de634ca10006dd634ca10005f7714ca1001df4714ca10034ff760ca10004fe760ca10004fd760ca10006df630ca10006dc630ca10036ec620ca1001efb1058610014ff76546100167e65546100067d6554610005fb7054610005f8705461000cff765061000ebe6450610006bd645061001fb44150610005fb7050610005f87050610006de63cc610006dd63cc610005fa70cc610005f970cc610006f576cc610006f763cc610007d663cc610006f563cc610007d563cc6101c5f672cc610006f762cc610006f562cc610007d632cc610007d432cc610007f270cc610005f570cc610007f170cc61001ef660cc610006de634c610006dd634c61001fd4314c610005fb704c610005f8704c610005f5760c61001ef5760c61001fd6730c610006f7630c610007d7630c610006f5630c610007d4630c610
  | 13 => 0x431001cfc76543100167e65543100067d6554310005f7715431001df4715431003cfd7690310266bf649031000ebc649031000cff765031001cfc765031000ebe6450310006bd6450310005f7715031001df47150310006de63cc310006dd63cc31001df671cc310005f571cc3101aedf638c3101aedc638c3100057f754c3100657c754c310005bf744c31005dbc744c310006de634c310006dd634c310005ef724c310005ec724c310005f7714c31001df4714c3101a6df630c3101a6dc630c31001df671c8310005f571c8310007e521c83100567e65d961000cfe74d9610004fd74d961000cfc74d96100567f54d9610004fe73d9610004fd73d96100567c53d9610034fe72d9610004fd72d96100567c52d9610006f571d96102767e51d96102767c51d9610006fa70d96100567f50d96100567c65596100067f7559610004ff745961000cfe745961000cfc7459610004ff7359610004fc7359610004ff7259610034fc72596100567f52596100567f515961001cfc70596100567c505961004ebe64d9210014fe75d9210004fd75d9210014fc75d921004ebe54d9210004fe73d9210004fd73d921004ebc43d9210034fe72d9210004fd72d921004ebc42d9210006f571d9210266be41d9210266bc41d9210006fa70d921004ebf40d921004ebc6459210004ff7559210014fe7559210014fc7559210006bf7459210004ff7359210004fc7359210004ff7259210034fc725921004ebf425921004ebf415921001cfc705921004ebc4059210004ff7655210004fe7655210004fd7655210004fc76552100067f65552100167c6555210006bf645521000ebc645521004f3c5455210005df7355210005dc7355210005f7715521001df47155210014fe75d8e10004fd75d8e10014fc75d8e1000cfe74d8e10004fd74d8e1000cfc74d8e10034fe72d8e10004fd72d8e10006f571d8e101aede31d8e101aedc31d8e10006fa70d8e10006df6398e10014fe7598e10004fd7598e10014fc7598e1000cfe7498e10004fd7498e1000cfc7498e10034fe7298e10004fd7298e100057f7558e100557c7558e10005bf7458e1004dbc7458e10005ef7258e10005ec7258e10004ff7558e100067f7558e100047f7558e10014fe7558e10014fc7558e100067c7558e100147c7558e10004ff7458e10006bf7458e10004bf7458e1000cfe7458e1000cfc7458e10006bc7458e1000cbc7458e10006df7358e10004ff7258e10006ef7258e10004ef7258e10034fc7258e10006ec7258e10034ec7258e10006f77158e10006dd6318e10014fe7518e10004fd7518e10014fc7518e1000cfe7418e10004fd7418e1000cfc7418e10006de7318e10034fe7218e10004fd7218e10006f57118e101a6de3118e101a6dc3118e10006fa7018e10004ff7694e10004f
  | 14 => 0x34fc72597100667c525971001cfc715971001e7e515971001e7c51597100667f5059710004ff7559310014fe7559310014fc755931001ebf745931005ebe5459310004ff7359310004fc735931005ebc4359310004ff7259310034fc725931005ebc425931001cfc715931001ebe415931001ebc415931005ebf4059310004ff765531001cfe7655310004fd765531001cfc76553100167e65553100067d655531000ebe6455310006bd645531005f3c5455310005df7355310005dc7355310014fe7598f10004fd7598f10014fc7598f1000cfe7498f10004fd7498f1000cfc7498f1001ede7398f10034fe7298f10004fd7298f1001cfe7198f1001ede3198f1001edc3198f1001ef62198f1001ef41098f10004ff7558f10014fe7558f10014fc7558f10004ff7458f1000cfe7458f1000cfc7458f1001edf7358f10004ff7258f10034fc7258f1001cfc7158f1001ede3158f1001edc3158f10004ff7694f1001cfe7694f10004fd7694f1001cfc7694f100167e6594f100067d6594f100675f5394f10004ff7654f1001cfe7654f10004fd7654f1001cfc7654f10005bf7454f1005dbc7454f10004ff7690f1001cfe7690f10004fd7690f1001cfc7690f1000ebe6490f10006bd6490f10004ff7650f1001cfe7650f10004fd7650f1001cfc7650f100057f7550f100657c7550f1005f9c4350f10004ff7558b10014fe7558b10014fc7558b10004ff7458b1000cfe7458b1000cfc7458b10004ff7358b10004fc7358b1001eef7258b1001eee2158b1001eec2158b10034ff7694b1001cfe7694b10004fd7694b100167e6594b100067d6594b1001df67194b10005f57194b10004ff7654b10004fd7654b1001cfc7654b102867f6554b100167c6554b10034ff7690b1001cfe7690b10004fd7690b1001cfc7690b1000ebe6490b10006bd6490b1001df67190b10005f57190b10004ff7650b10004fd7650b1001cfc7650b1027ebf6450b1000ebc6450b10004ff76ccb1001cfe76ccb10004fd76ccb10206df63ccb10206dc63ccb10036ee62ccb10006ed62ccb10034ff768cb1001cfe768cb10004fd768cb1001cfc768cb100657e758cb100057d758cb1005dbe748cb10005bd748cb10006de638cb10006dd638cb1001df6718cb10005f5718cb10004ff764cb10004fd764cb1001cfc764cb101dedf634cb101dedc634cb10034ff760cb1001cfe760cb10004fd760cb1001cfc760cb10006de630cb10006dd630cb10036ee620cb10006ed620cb1001df6710cb10005f5710cb1001df77648710006f77648710006f6634871001ef4634871001fe7724871001fe76248710036f6624871001ef4624871001fe4624871001ee46248710007e73248710007e43248710005f47048710044fd76943102767f65943100167c6594310014ff765
  | 15 => 0xe745843000cfc7458430004ff7258430034fc72584300757e75184300057d751843006dbe7418430005bd7418430005ee7218430005ed721843001ef66118430006f5611843001cff7694430004fe7694430004fd769443001ef66194430006f56194430004ff7654430004fd7654430004fc76544300167e65544300067d6554430005df7354430005dc735443001ef66154430006f5615443001cff7690430004fe7690430004fd769043001ef66190430006f56190430004ff7650430004fd7650430004fc765043000ebe6450430006bd6450430005df7350430005dc735043001ef66150430006f5615043001cfd76cc430006de63cc43001ef661cc430006f561cc430005fa70cc430005f970cc430004fd768c4300757e758c4300057d758c43006dbe748c430005bd748c430005ee728c430005ed728c430005dd768c4301a6dd768c430004dd768c4301a75e758c4301a75d758c4301a79e748c4301a79d748c43028dde728c4301a7ce728c430005ce728c4301a7cd728c430006dd628c4301a5de718c4301a6dd618c430005dd708c430004ff764c430006de634c43001ef6610c430006f5610c430007d5310c430005fa700c430005f9700c43028dde720c430006dd620c4301a5de710c4301a7d6710c4301a7d6610c4301a6dd610c430007d5610c4301a7da700c430005dd700c4301a7d9700c43001cff7688430004fe7688430004fd76884300757e75884300057d758843006dbe7488430005bd7488430005de7388430005dd738843001ef66188430006f561884301a7d43188430004ff7648430004fd7648430004fc7648430005df7348430005dc734843001ef66148430006f56148430007d4314843001cff7608430004fe7608430004fd76084301a5df73084301a5dc7308430007e5210843000cfe749803008cfd749803000cfc74980301aede31980301aedc319803008cff769003000cfe769003000cfd769003006cfc769003000ebe6490030006bd6490030005de7390030005dd739003008cff76500301a5de71cc030006dd61cc030005dd738c030006de638c030005f9738c030006fa638c030007da638c030007da318c030007d8318c030004ff764c030005bf744c03006dbc744c030005f7714c030005f4714c030005df764c030006df764c030004df764c0300079f744c0300079c744c030007d7714c0301a5dc714c030007d4714c030005d4714c030006dd614c030005df704c030006de604c030005fb764c030006fb764c030004fb764c030007bb744c030007b8744c030005fb734c030007db734c030006fa634c030007da634c030007f3714c030007f0714c03001e7f7559710004ff745971000cfe745971000cfc74597100667f5459710004ff7359710004fc73597100667c5359710004ff7259710
  | 16 => 0xc53001cdc764c5300075f654c5300075c654c5300079f644c5300079c644c530005df724c530007cf624c530296dc624c530007cc624c530006cc624c530007d7714c530007d7614c53001ede614c53001edc614c530007d4614c53001ed4614c530007db704c530005dc704c530007d8704c530004fe760c5300067f650c5300ee7c650c530006bf640c5300e6bc640c530005de730c530006ef620c530006ec620c530006f7610c53001ef4610c530004fe7688530004fd768853001cfc76885300857e75885300057d75885300067f65885300de7c658853007dbe7488530005bd7488530006bf64885300d6bc6488530005de7388530005dd7388530006ef6288530036ec6288530006f7618853001ef46188530007d73188530004ff7648530004fe7648530004fc7648530006bf64485300c6bc6448530005de7348530005dd7348530006f7614853001ef46148530007d73148530004fe7608530004fd760853001cfc7608530006bf64085300bebc6408530005de7308530005dd7308530006f7610853001ef46108530007e5210853009cfe76901300067f65901300b67c6590130006bf649013000ebc6490130006ef6290130006ec6290130006f76190130006f4619013000cff765013007cfd765013000cfc76501300067f65501300ae7c6550130006bf645013000ebc6450130005df7350130005dc7350130006ef6250130006ec6250130006f76150130006f46150130006bf64cc13009ebc64cc130006f761cc130006f461cc130007bb64cc130007b864cc130007f361cc130007f061cc130007db31cc130007d931cc130006bf648c13008ebc648c130006f7618c130006f4618c1300079f648c1300079c648c130005dd718c130007d7618c1301aedc618c130007d4618c130006d4618c130007db608c13006ebe64d9030014fe75d9030004fd75d9030014fc75d903006cfd74d903009cfe73d9030006de73d9030034fe72d9030004fd72d903001cfe71d9030004fd71d903008cfe70d9030006fa70d903000cff765903006ebc6459030004ff7559030014fe7559030014fc7559030006bf745903006ebe545903000cff735903000cfd735903006cfc735903006ebc4359030004ff7259030034fc725903006ebf4259030004ff715903001cfc715903006ebf415903006cfc705903006ebc4059030004ff7655030004fe7655030004fd7655030004fc765503000ebe6455030006bd645503006f3c5455030005df7355030005dc735503000cfe7498c3009cfd7498c3000cfc7498c3009cff7690c3000cfd7690c3000ebe6490c30006bd6490c30005fa7090c30005f97090c3009cff7650c300057f7550c300757c7550c3006f9c4350c30006f76198430004ff7558430014fe7558430014fc7558430004ff745843000cf
  | 17 => 0x67c6518530006bf6418530006bc6418530006ef621853001ef66118530006f56118530005f67618530006f67618530006f76518530007776518530006776518530006f66518530006f56518530006f46518530007746518530006746518530006f76418530007b76418530006b76418530006f66418530006f56418530006f46418530007b46418530006b46418530007d57318530006f76218530007e76218530006e76218530006f66218530006f56218530006f46218530007e46218530006e4621853001ef7751853001ef6751853001ef5751853001ef4751853001ef7741853001ef6741853001ef5741853001ef47418530006f75418530006f65418530006f55418530006f4541853001ef77318530006f75318530006f65318530006f55318530006f45318530006f74318530006f64318530006f54318530006f4431853001ef7721853001ef6721853001ef5721853001ef47218530006f75218530006f45218530006f74218530006f4421853001ef7701853001ef57018530006f75018530006f45018530006f74018530006f44018530006f53018530004fe7694530004fd769453001cfc76945300067f65945300167c6594530006bf649453013ebc6494530005de7394530005dd7394530006ef6294530006ec6294530006f7619453001ef46194530004ff7654530004fe7654530004fc76545300067f65545300167c6554530006bf6454530136bc6454530006ef6254530006ec6254530006f7615453001ef46154530004fe7690530004fd769053001cfc76905300067f659053012e7c6590530006bf649053000ebc6490530005de7390530005dd7390530006ef6290530006ec6290530006f7619053001ef46190530004ff7650530004fe7650530004fc76505300067f65505301267c6550530006bf645053000ebc6450530006ef6250530006ec6250530006f7615053001ef46150530004fe76cc5300067f65cc53011e7c65cc530006bf64cc530116bc64cc530006ef62cc530006ec62cc53001ef461cc530005de76cc530006de76cc530004de76cc5300075f65cc5300075c65cc5300079f64cc5300079c64cc530005dd72cc530007cf62cc53029edc62cc530007cc62cc530006cc62cc530007d761cc53001ede61cc53001edc61cc530007d461cc53001ed461cc530005de70cc5300857e758c5300057d758c5300067f658c53010e7c658c53007dbe748c530005bd748c530006bf648c530106bc648c530005dd738c530005ee728c530005ed728c530006ef628c530006ec628c530006f7618c53001ef4618c530005fa708c530005f9708c53001cfc764c5300067f654c5300fe7c654c530006bf644c5300f6bc644c530006ef624c530006ec624c530006f7614c53001ef4614c530005fb704c530005f8704
  | 18 => 0xc71d9130006bf51d9130006bc51d9130006bf70d913007ebe70d9130006bd70d9130006bf50d9130006bc50d91300057f75591300857c75591300067f655913007ebc6459130005ef7259130005ec7259130005f77159130005f47159130004ff75591300067f75591300047f7559130014fe7559130014fc75591300067c75591300147c755913007cff7459130006bf745913008cff7359130006df7359130004ff7259130006ef7259130004ef7259130034fc7259130006ec7259130034ec7259130004ff7159130006f77159130004f7715913001cfc7159130006f4715913001cf4715913009cff7059130006fb7059130005be761913007ebe7619130004be7619130006bf65191300073f65191300063f6519130006be6519130006bd6519130006bc65191300073c65191300063c6519130004ff7655130004fe7655130004fd7655130004fc7655130006bf645513000ebc645513007f3c5455130005df7355130005dc735513008cfe7690d300067f6590d3014e7c6590d30006bf6490d3000ebc6490d3000cfc7650d300057f7550d300857c7550d300067f6550d301467c6550d30006bf6450d3000ebc6450d3007f9c4350d30005fb7050d30005f87050d300067f65d85300067c65d8530006bf64d8530006bc64d8530014fe75d8530004fd75d8530014fc75d853000cfe74d8530004fd74d853000cfc74d8530034fe72d8530004fd72d8530006f751d8530006f451d8530006f741d8530006f441d8530006f765d85300077765d85300067765d8530006f665d8530006f565d8530006f465d85300077465d85300067465d8530006f764d8530007b764d8530006b764d8530006f664d8530006f564d8530006f464d8530007b464d8530006b464d8530007d773d8530006f762d8530007e762d8530006e762d8530006f775d8530006f675d8530006f575d8530006f475d8530006f774d8530006f674d8530006f574d8530006f474d8530006f754d8530006f654d8530006f554d8530006f454d8530006f773d8530006f753d8530006f653d8530006f553d8530006f453d8530006f743d8530006f643d8530006f543d8530006f443d8530006f772d8530006f672d8530006f572d8530006f472d8530006f752d8530006f452d8530006f742d8530006f442d8530006f770d8530006f570d8530006f750d8530006f450d8530006f740d8530006f440d85300857e75985300057d75985300067f65985300067c659853007dbe7498530005bd7498530006bf6498530006bc6498530005ee7298530005ed7298530006ef6298530006f761985300057f75585300857c75585300067f65585300067c6558530005bf745853007dbc7458530006bf6458530006bc6458530005ef7258530005ec7258530006ef62585300067f6518530
  | 19 => 0xe3008f9c4350e30005fb7050e30005f87050e30006f76198630004ff7558630014fe7558630014fc7558630004ff745863000cfe745863000cfc7458630004ff7258630034fc72586300957e75186300057d751863008dbe7418630005bd7418630005ee7218630005ed721863001ef66118630006f5611863001cff7694630004fe7694630004fd7694630004ff7654630004fd7654630004fc76546300167e65546300067d6554630005df7354630005dc735463001cff7690630004fe7690630004fd7690630004ff7650630004fd7650630004fc765063000ebe6450630006bd6450630005df7350630005dc73506300957e758c6300057d758c63008dbe748c630005bd748c630005ee728c630005ed728c63001ef6618c630006f5618c630005fa708c630005f9708c6301af5e758c6301af5d758c6301af9e748c6301af9d748c6302a5de728c6301afce728c630005ce728c6301afcd728c630006dd628c6301afd6618c6301aedd618c630007d5618c6301afda708c630005dd708c6301afd9708c63001cff764c63001ef6614c630006f5614c630005fb704c630005f8704c63001ef4610c630007d5310c630005dd760c6301aedd760c6302a5de720c630006dd620c6301afd6710c630007d7610c6301aedd610c6301afd4610c630005dd700c63001cff7688630004fe7688630004fd76886300957e75886300057d758863008dbe7488630005bd7488630005de7388630005dd738863001ef66188630006f561886301afd43188630004ff7648630004fd7648630004fc7648630005df7348630005dc734863001ef66148630006f56148630007d4314863001cff7608630004fe7608630004fd76086301addf73086301addc7308630007e5210863000cfd769023000ebe6490230006bd6490230005de7390230005dd739023006cff7650230005dd76cc230006dd76cc2301adde71cc230006dd61cc230007da50cc230007d950cc230005f976cc230006f976cc230007da53cc230007d953cc23000cfe76d913007ebe64d9130014fe75d9130004fd75d9130014fc75d9130006bf54d913007ebe54d913007ebc54d913000cfe73d913007cfd73d913000cfc73d913007ebf43d9130034fe72d9130004fd72d913007ebf42d913007ebc42d913001cfe71d9130004fd71d913007ebf41d913007ebc41d913007cfd70d913007ebf40d913007dbe76d913000cbe76d9130006bf65d91300073f65d91300063f65d9130006be65d9130006bc65d9130006bf75d9130006be75d9130006bd75d9130006bc75d9130006bf73d913007ebe73d9130006bd73d9130006bf53d9130006bc53d9130006bf72d9130006be72d9130006bd72d9130006bc72d9130006bf52d9130006bc52d9130006bf71d9130006be71d9130006bd71d9130006b
  | 20 => 0x5fa7090f30005f97090f3006cff7650f300057f7550f300a57c7550f3009f9c4350f300a57e75d87300057d75d873009dbe74d8730005bd74d8730005ee72d8730005ed72d87300a57e75987300057d759873009dbe7498730005bd7498730005ee7298730005ed7298730006f76198730004ff7558730014fe7558730014fc7558730004ff745873000cfe745873000cfc7458730004ff7258730034fc725873001ef66118730006f5611873001cff7694730004fe7694730004fd76947300167e65947300067d6594730005de7394730005dd7394730004ff7654730004fd7654730004fc76547300067f65547300167c655473001cff7690730004fe7690730004fd769073000ebe6490730006bd6490730005de7390730005dd7390730004ff7650730004fd7650730004fc7650730006bf645073000ebc645073001cfd76cc73001ef661cc730006f561cc730005fa70cc730005f970cc73001cdd76cc730005dd72cc73029ede62cc73001ede61cc730007d661cc730007d561cc73001edc61cc730005de70cc730007da70cc730007d970cc7300a57e758c7300057d758c73009dbe748c730005bd748c730005ee728c730005ed728c730005df764c730006df764c730005df724c730296de624c730007d7714c73001ede614c73001edc614c730005dc704c73001ef6610c730006f5610c730005fa700c730005f9700c73001cff7688730004fe7688730004fd76887300a57e75887300057d758873009dbe7488730005bd7488730005de7388730005dd7388730036ee6288730006ed628873001ef46188730007d73188730004ff7648730004fd7648730004fc7648730005de7348730005dd7348730007d7314873001cff7608730004fe7608730004fd7608730005de7308730005dd730873001ef66108730006f56108730007e5210873007cfd7690330006bf649033000ebc649033000cff765033000ebe6450330006bd6450330005df7350330005dc73503300957e75d92300057d75d923008ebe64d9230014fe75d92300067e75d92300147e75d9230004fd75d92300067d75d92300047d75d9230014fc75d923008ebe54d9230006dd73d923008ebc43d9230034fe72d9230004fd72d923001cfe71d9230004fd71d9230006fa70d923008ebc6459230004ff7559230014fe7559230014fc7559230006bf7459230006bf545923008ebc545923008ebf4359230004ff7259230034fc725923008ebf4259230004ff715923001cfc715923008ebf415923008ebc4059230004ff7655230004fe7655230004fd7655230004fc7655230006bf645523000ebc645523008f3c5455230005df7355230005dc735523007cfd7690e30006bf6490e3000ebc6490e3000cff7650e300057f7550e300957c7550e3000ebe6450e30006bd645
  | 21 => 0xd72d8540006f751d8540006f451d854004ef641d854004ef541d8540006f7619854003df970985400057f75585400ad7c7558540005df7358540005dc7358540005ef7258540005ec725854005dfb70585400ad7e75185400057d751854001ef66118540006f56118540004fe7694540004fd769454001cfc76945400067f65945400167c659454000dbe7494540005bd7494540004ff7654540004fe7654540004fc76545400167e65545400067d655454001cbc7650540006bf6550540006bd6550540006bc6350540005bf72505402bebc625054000dbf715054000fb77150540007b7615054001ebe615054001ebc6150540007b4615054001eb46150540007bb7050540005bc7050540007b8705054000ebf605054000fbb6050540004fe76cc540004fd76cc540004fc76cc540006f761cc54001ef461cc540004fe768c540004fd768c54001cfc768c5400ad7e758c5400057d758c54000dbe748c540005bd748c540006df638c540006dc638c540005ee728c540005ed728c540004ff764c540004fe764c540004fc764c540004fe760c540004fd760c54001cfc760c54000dbe740c540005bd740c540006df630c540006dc630c540006f7610c54001ef4610c540004fe76c8540004fd76c8540034fc76c85400ad7e75c85400057d75c854000dbe74c8540005bd74c8540005de73c8540005dd73c8540006f761c854001ef461c8540004fe7688540004fd768854001cfc76885400ad7e75885400057d758854000dbe7488540005bd7488540005de7388540005dd7388540006ef6288540036ec6288540004ff7648540004fe7648540004fc764854000dbe7448540005bd7448540004fe7608540004fd760854001cfc760854000dbe7408540005bd7408540006ef6208540036ec6208540006f7610854001ef46108540007e521085402b4fe76941400167e65941400af7b509414000cfe76541401b4fd765414000cfc7654140005bf745414000dbc7454140006bf6590140006bd6590140006bc6390140005bd72901402aebc6290140005bd7190140266bc619014000dbe709014000fba709014000ebf609014000fbb609014009ebe64d9330014fe75d9330004fd75d9330014fc75d9330006de73d9330034fe72d9330004fd72d933009ebf42d933001cfe71d9330004fd71d933009ebf41d9330006f970d933009ebc40d933009ebc6459330004ff7559330014fe7559330014fc7559330006bf745933009ebe545933009ebc4359330004ff7259330034fc725933009ebc4259330004ff715933001cfc715933009ebc415933009ebf4059330004ff7655330004fe7655330004fd7655330004fc765533000ebe6455330006bd645533009f3c5455330005df7355330005dc735533000cfd7690f3000ebe6490f30006bd6490f30
  | 22 => 0x9540034fe72d9540004fd72d95400ae7c52d95401bebf42d954001cfe71d9540004fd71d95400ae7c51d95401bebf41d954000cfd70d95400ae7f50d95401bebc40d95400ae7c6559540005df7359540005dc7359540005ef7259540005ec7259540005f77159540005f471595402c5fb70595401b4ff7459540006bf7459540004ff7359540006df7359540004df7359540004fc7359540006dc7359540004dc7359540004ff7159540006f77159540004f7715954001cfc7159540006f4715954001cf471595400ae7f51595401b6bf41595402c4ff7059540006fb70595401b6bc4059540014fe75d8d40004fd75d8d40014fc75d8d40006df53d8d40006dc53d8d4008ede43d8d4008edd43d8d40034fe72d8d40004fd72d8d4001cfe71d8d40004fd71d8d40006df6398d4007df97098d400057f7558d400ad7c7558d40005ef7258d40005ec7258d40005f77158d40005f47158d4009dfb7058d40006dd6318d40014fe7518d40004fd7518d40014fc7518d40006df5318d40006dc5318d4006ede4318d4006edd4318d40034fe7218d40004fd7218d4006ebf4218d4001cfe7118d40004fd7118d4006ebf4118d4006ebc4018d40004fe7694d40004fd7694d40004fc7694d400067f6594d400167c6594d400af5f5394d40004ff7654d40004fe7654d40004fc7654d40005bf7454d4000dbc7454d40014fe75d8940004fd75d8940014fc75d8940004fe73d8940004fd73d8940006ef52d8940006ec52d8940186ee42d8940186ed42d894001cfe71d8940004fd71d8940006ef629894016df970989400057f75589400ad7c7558940005df7358940005dc7358940005f77158940005f47158940195fb70589400ad7e75189400057d7518940036ee6218940006ed6218940004fe7694940004fd7694940034fc76949400067f65949400167c659494000dbe7494940005bd7494940004ff7654940004fe7654940004fc76549400167e6554940034bc7650940006bf6550940006bc635094000dbf725094000faf7250940007af6250940036be6250940036bc6250940007ac6250940036ac6250940005bf715094027ebc6150940007bb7050940005bc7050940007b8705094000ebf605094000fbb6050940004fe76cc940004fd76cc940004fc76cc940006ef62cc940036ec62cc940004fe768c940004fd768c940034fc768c9400ad7e758c9400057d758c94000dbe748c940005bd748c940006df638c940006dc638c940005f6718c940005f5718c940004ff764c940004fe764c940004fc764c940004fe760c940004fd760c940034fc760c94000dbe740c940005bd740c940006df630c940006dc630c940006ef620c940036ec620c940014fe75d8540004fd75d8540014fc75d8540004fe73d8540004fd73d8540034fe72d8540004f
  | 23 => 0x265be7190a402afba7090a40005bd7090a402afb97090a4000ebe6090a4000fba6090a40004ff76cca40004fe76cca40004fd76cca4000dbe74cca40005bd74cca40006de63cca40006dd63cca40034ff768ca40004fe768ca40004fd768ca400b57e758ca400057d758ca4000dbe748ca40005bd748ca40005f6718ca40005f5718ca40004ff764ca40004fd764ca40004fc764ca40005bf744ca4000dbc744ca40006de634ca40006dd634ca40034ff760ca40004fe760ca40004fd760ca402adbf740ca4000dbc740ca40025fa70d8640006f76198640004ff7558640014fe7558640014fc755864003ebe5458640006bd5458640004ff7358640004fc7358640006be435864003ebc4358640004ff7258640034fc7258640006be425864003ebc425864003ef6415864003ef54158640266bc415864003ebf40586400b57e75186400057d7518640005de7318640005dd7318640005ee7218640005ed721864001ef66118640006f5611864004dfa701864001cff7694640004fe7694640004fd769464000dbc7494640004ff7654640004fd7654640004fc76546400167e65546400067d6554640005bf745464000dbc74546400073d5454640265bf7590640005bd7590640005be73906402adbe7290640006bd629064000dbe719064000fb67190640267b66190640266bd6190640007b56190640267ba7090640005bd7090640267b9709064000ebe609064000fba6090640004ff76cc640004fe76cc640004fd76cc64000dbe74cc640005bd74cc640006de63cc640006dd63cc64001cff768c640004fe768c640004fd768c6400b57e758c6400057d758c64000dbe748c640005bd748c640005ee728c640005ed728c640004ff764c640004fd764c640004fc764c640005bf744c64000dbc744c640006de634c640006dd634c64001cff760c640004fe760c640004fd760c640265bf740c64000dbc740c640034ff76c8640004fe76c8640004fd76c86400b57e75c86400057d75c864000dbe74c8640005bd74c8640005de73c8640005dd73c8640036ee62c8640006ed62c864001cff7688640004fe7688640004fd76886400b57e75886400057d758864000dbe7488640005bd7488640005de7388640005dd738864001ef66188640006f56188640004ff7648640004fd7648640004fc7648640005bf744864000dbc7448640036ee6248640006ed624864001ef66148640006f5614864001cff7608640004fe7608640004fd7608640265bf740864000dbc7408640007e52108640014fe769424000cfd769424000dbe7494240005bd74942400073d54942401bfbb4094240014fe76d95400ae7e65d95401bcff74d954000cfe74d95401bcfd74d954000cfc74d95401be7f54d95401be7d54d9540004fe73d9540004fd73d95400ae7c53d
  | 24 => 0xc735802101ef62158021036f52158021006e5215802101efb705802101efb105802101ef4105802101ef810580210b67e65d9640005de73d9640005dd73d96402b5fa70d9640004fe73d9640006de73d9640004de73d9640004fd73d9640006dd73d9640004dd73d964001cfe71d9640004fd71d96402b4fe70d9640006fa70d9640014ff76596400b67c65596400067f75596401b67f54596401b67d5459640004ff7359640004fc73596400b67c5359640004ff7259640034fc72596400b67f5259640004ff715964001cfc71596400b67f515964000cfc70596400b67c50596400b5bf7655240016bf7655240014bf765524000dbf755524000f3f7555240016be65552400b73e65552400163e65552400073d6555240016bc65552400079f7355240005bc73552400079c73552400059c73552400b73f53552402adbc72552400b73f5255240265bc71552400b73f5155240005bf7055240007bb7055240007b8705524000ebe605524000fba60552400b73c50552400b57e75d8e400057d75d8e4006dfa70d8e40006df6398e40014fe7598e40004fd7598e40014fc7598e40006df5398e40006dc5398e4009ede4398e4009edd4398e40034fe7298e40004fd7298e4001cfe7198e40004fd7198e40004ff7558e40014fe7558e40014fc7558e4007ebe5458e40006bd5458e40006df5358e40006dc5358e4007ede4358e4007edd4358e4007ebc4358e40004ff7258e40034fc7258e40004ff7158e4001cfc7158e40006dd6318e4008dfa7018e40004ff7694e40004fe7694e40004fd7694e400167e6594e400067d6594e4000dbc7494e402473e5494e400b75f5394e40004ff7654e40004fd7654e40004fc7654e40005bf7454e4000dbc7454e400073d5454e40005bf7590e40005bd7590e4014ebe6590e4014ebc6590e4000dbe7390e4000f9e7390e400079e6390e40006bd6390e400079d6390e402adbe7290e40265be7190e40007ba7090e40005bd7090e40007b97090e4000ebe6090e4000fba6090e40165fa70d8a40006ef6298a40004ff7558a40014fe7558a40014fc7558a4016ebe5458a40006bd5458a40004ff7358a40004fc7358a40006be4358a4016ebc4358a4016eee4258a4016eed4258a402aebc4258a40004ff7158a4001cfc7158a4016ebc4158a4016ebf4058a400b57e7518a400057d7518a40005de7318a40005dd7318a40036ee6218a40006ed6218a40005f67118a40005f57118a40185fa7018a40034ff7694a40004fe7694a40004fd7694a4000dbc7494a40004ff7654a40004fd7654a40004fc7654a400167e6554a400067d6554a40005bf7454a4000dbc7454a400073d5454a402adbf7590a40005bd7590a40005be7390a4000dbe7290a4000fae7290a402afae6290a402aebd6290a40007ad6290a40
  | 25 => 0xc52101fe7720c521035f6720c52101df4720c52101fe4720c52101ef7620c52101fe7620c521007d7320c521007e7320c521007c7320c521007d5320c521007e4320c521005f5700c52100cfe74d8121004fd74d812100cfc74d8121004fe73d8121004fd73d8121006fb6098121005bf74581210c5bc7458121005df7358121005dc73581210c5be7418121005bd7418121005de7318121005dd7318121006f9601812100cfe7418121006be741812100cbe7418121004fd7418121006bd7418121004bd741812100cfc7418121004fe7318121006de7318121004de7318121004fd7318121006dd7318121004dd7318121006f73118121006f4311812115eee2118121156f42118121004ff7559021014fe7559021014fc755902101cff745902101ebf74590210bebe5459021004ff7359021004fc73590210bebc4359021034fe7259021034fc7259021036be4259021036bc425902101cfe715902101cfc715902101ebe415902101ebc4159021004ff7059021004fc70590210bebf4059021004ff765502101cfe7655021004fd765502101cfc765502100ebe6455021006bd64550210bf3c5455021005df7355021005dc735502100cfe7498c21004fd7498c2100cfc7498c2101cfe7398c2101ede7398c2101cfe7198c2101cfc7198c2101ede3198c2101edc3198c2101ef62198c21036f52198c21004fe7098c21004fd7098c2101ef41098c21004ff7458c2100cfe7458c2100cfc7458c2101cff7358c2101edf7358c2101cfe7158c2101cfc7158c2101ede3158c2101edc3158c21004ff7058c21004fc7058c21004ff7690c2101cfe7690c21004fd7690c2101cfc7690c2100ebe6490c21006bd6490c21004ff7650c2101cfe7650c21004fd7650c2101cfc7650c210057f7550c212d57c7550c210bf9c4350c2101fe7764842101de77648421006e77648421007e774484212cfe67448421007e574484212cfe4744842101fe7644842101fe6644842101fe5644842101fe464484212cfe65448421007e554484212cfe45448421007e77348421007e67348421007e57348421007e4734842101fe7634842101fe66348421006e6634842101fe5634842101fe4634842101ee463484212cfe74348421007e64348421007e543484212cfe44348421007e77048421007e67048421007e57048421007e47048421005e4704842101fe7604842101fe6604842101fe5604842101fe460484212cfe740484212cfe4404842100cfe7498021004fd749802100cfc7498021004fe7398021004fd739802101efa709802101efb109802101ef81098021004ff7458021006bf7458021004bf745802100cfe745802100cfc7458021006bc745802100cbc7458021004ff7358021006df7358021004df7358021004fc7358021006dc7358021004d
  | 26 => 0xcfe745822100cfc7458221004ff7358221004fc735822101cfc715822101eef215822101eed215822101efb705822101efb105822101ef8105822100cfe76d91210c6be64d9121014fe75d9121004fd75d9121014fc75d9121004fe73d9121004fd73d912101cfd72d91210c6bf42d9121034fd71d91210c6bf41d9121004fe70d9121004fd70d91210c6bc40d91210c6bc6459121004ff7559121014fe7559121014fc75591210c4ff7459121006bf74591210c6be5459121004ff7359121004fc73591210c6bc43591210d4ff7259121006ef72591212bebe42591212bebc425912124cff7159121006f7715912127ebe415912127ebc4159121004ff7059121004fc70591210c6bf4059121004ff7655121004fe7655121004fd7655121004fc765512100ebe6455121006bd64551210c73c5455121005df7355121005dc7355121005f7715512101df471551210c5be74d8d21005bd74d8d2100cfe74d8d21006be74d8d2100cbe74d8d21004fd74d8d21006bd74d8d21004bd74d8d2100cfc74d8d21006f571d8d21004fe70d8d21004fd70d8d21006df6398d2100cfe7498d21004fd7498d2100cfc7498d21004fe7398d21004fd7198d21006f57198d21206de3198d21206dc3198d21004fe7098d21004fd7098d21004ff7458d2100cfe7458d2100cfc7458d21006df7358d21004ff7158d21006f77158d211dede3158d211dedc3158d21004ff7058d21004fc7058d21004fe7618d21006dd6318d2100cfe7418d21004fd7418d2100cfc7418d21006de7318d21004fe7018d21004fd7018d21004ff7690d21004fe7690d21004fd7690d21004fc7690d2100ebe6490d21006bd6490d21004ff7650d21004fe7650d21004fd7650d21004fc7650d210057f7550d210cd7c7550d210c79c4350d21005ef7250d21035ec7250d21005f77150d2101df47150d21034fc76545210067f65545210167c6554521005ef7254521035ec725452101fe4215452100cff76505210c4fd7650521034fc7650521006bf645052100ebc6450521005ef7250521035ec725052101fb4415052101fe42150521034fe76cc521006df63cc521006dc63cc521035ee72cc521005ed72cc52101fe421cc521035f676cc521006f676cc521034f676cc52101df673cc521006f763cc521007d763cc521006f563cc521007d463cc521035f672cc521007e672cc521035e672cc521007e572cc521035f472cc52101ef762cc52101fe762cc521007e732cc52129fd632cc52129fd432cc521005f570cc521004ff764c521004fd764c521034fc764c521006df634c521006dc634c521005ef724c521035ec724c52101fd4314c52101fe4214c521005f6760c52101ef6760c521005f6730c52101fd6730c521006f7630c521007d6630c521006f5630c521007d5630
  | 27 => 0xf7258e21296de7258e21006dd7258e21296dc7258e21006df5258e21296de5258e21296dc5258e21006df4258e21296de4258e21296dc4258e2101edf7158e2101ede7158e2101edd7158e2101edc7158e2101ed47158e2101edf5158e2101ede5158e2101edd5158e2101edc5158e2101edf4158e2101ede4158e2101edd4158e2101edc4158e2101edf2158e2101ede2158e2101edd2158e2101edc2158e21006df7058e21006de7058e21006dd7058e21006dc7058e21006df5058e21006dc5058e21006df4058e21006dc4058e21296df2058e21296dc2058e2101edf1058e2101ede1058e2101edd1058e2101edc1058e21004ff7694e2101cfe7694e21004fd7694e2101cfc7694e210167e6594e210067d6594e21246be6494e21006bd6494e21006de6394e21006dd6394e210df5f5394e21004ff7654e2101cfe7654e21004fd7654e2101cfc7654e210167e6554e210067d6554e21005bf7454e210d5bc7454e2123ebe6454e21006bd6454e21006de6354e21006dd6354e21005f77154e2101df47154e21004ff7690e2101cfe7690e21004fd7690e2101cfc7690e2114e7e6590e210067d6590e2100ebe6490e21006bd6490e21006de6390e21006dd6390e21004ff7650e2101cfe7650e21004fd7650e2101cfc7650e210057f7550e210dd7c7550e211467e6550e210067d6550e2100ebe6450e21006bd6450e21006de6350e21006dd6350e210d79c4350e21005f77150e2101df47150e2101eee2158a2101ef42158a2101ee42158a21014ff7654a2101cfc7654a210167e6554a210067d6554a2122ebe6454a21006bd6454a21006de6354a21006dd6354a21005f77154a2101df47154a2100cff7650a2101cfc7650a2121e7e6550a210067d6550a2100ebe6450a21006bd6450a21006de6350a21006dd6350a21005f77150a2101df47150a212167e65cca210067d65cca2120ebe64cca21006bd64cca21006de63cca21006dd63cca2101df671cca21005f571cca21207d431cca211ee7e654ca210067d654ca211e6be644ca21006bd644ca21006de634ca21006dd634ca21005f7714ca2101df4714ca211dfd4314ca2101df576cc621006f576cc62101f7665cc62101f7565cc62101fb664cc62101fb564cc62101fd673cc62101ef763cc62101fd663cc621006f563cc62101fd563cc621006d563cc621035f672cc621035f472cc62129fd632cc62129fd432cc621005f570cc621014fe7598221004fd7598221014fc759822100cfe7498221004fd749822100cfc7498221004fe7398221004fd739822101cfe719822101cf67198221006f7319822101ef431982211c6f7219822101ef4219822101efa709822101ef7109822101efb109822101ef81098221004ff7558221014fe7558221014fc7558221004ff7458221
  | 28 => 0x922101cfc715922101ebe415922101ebc4159221004ff7059221004fc70592210d6bf40592210d6bc4059221006bf7559221006be7559221006bd7559221006bc7559221006bf7359221006be7359221006bd7359221006bc7359221006bf5359221006bc5359221006bf72592212bebe7259221006bd72592212bebc7259221006bf52592212bebe52592212bebc52592212bebe32592212bebc325922101ebf715922101ebe715922101ebd715922101ebc715922101ebf515922101ebe515922101ebd515922101ebc515922101ebf315922101ebe315922101ebd315922101ebc315922101ebf215922101ebe215922101ebd215922101ebc2159221006bf7059221006be7059221006bd7059221006bc7059221006bf5059221006bc50592212bebf20592212bebc205922101ebf105922101ebe105922101ebd105922101ebc1059221004ff765522101cfe7655221004fd765522101cfc76552210167e65552210067d655522100ebe6455221006bd64552210d73c5455221005df7355221005dc7355221005f7715522101df47155221014fe7598e21004fd7598e21014fc7598e2100cfe7498e21004fd7498e2100cfc7498e2101ede7398e21006df5398e21006dc5398e21006df4398e21006dc4398e2101cfe7198e2101ede3198e2101edc3198e2101eef2198e2101eed2198e21004fe7098e21004fd7098e21006df7598e21006de7598e21006dd7598e21006dc7598e21006df7498e21006de7498e21006dd7498e21006dc7498e21006df5498e21006de5498e21006dd5498e21006dc5498e21006df7298e2129ede7298e21006dd7298e2129edc7298e21006df5298e2129ede5298e2129edc5298e21006df4298e2129ede4298e2129edc4298e2101edf7198e2101ede7198e2101edd7198e2101edc7198e2101edf5198e2101ede5198e2101edd5198e2101edc5198e2101edf4198e2101ede4198e2101edd4198e2101edc4198e2101edf2198e2101ecf2198e2101ede2198e2101edd2198e2101ecd2198e2101edc2198e21006df7098e21006de7098e21006dd7098e21006dc7098e21006df5098e21006dc5098e21006df4098e21006dc4098e2129edf2098e2129edc2098e2101edf1098e2101ede1098e2101edd1098e2101edc1098e21004ff7558e21014fe7558e21014fc7558e21004ff7458e2100cfe7458e2100cfc7458e2101edf7358e21006df5358e21006dc5358e21006df4358e21006dc4358e2101cfc7158e2101ef47158e2101cf47158e2101ede3158e2101edc3158e2101ef43158e21004ff7058e21004fc7058e21006df7558e21006de7558e21006dd7558e21006dc7558e21006df7458e21006de7458e21006dd7458e21006dc7458e21006df5458e21006de5458e21006dd5458e21006dc5458e21006d
  | 29 => 0x1df671cc831005f571cc831034dd76cc831036de62cc831207ce62cc831207cd62cc831036dc62cc831207d671cc831205dd71cc831007d571cc831207d661cc831005de70cc831004fd768c8310ed7e758c8310057d758c8310e5be748c831005bd748c8311dddd738c83129ede638c83101df6718c831005f5718c831004ff764c83101df6714c8311dddf764c831006df764c831004df764c831007cf724c831036de624c831036dc624c8311dddf714c8311dfd6714c831007d5714c8311dede614c8311dfd6614c831005dc704c83129ede630c83101df6710c831005f5710c83101df7764c431006f7764c431004f7764c43101df7734c43101fd7734c431006f6634c43101fd6634c431007d6534c431007d5534c431007d6434c431007d5434c431005f7724c431007d7324c431007d5324c431005f4704c431014fe7598031004fd7598031014fc759803100cfe7498031004fd749803100cfc7498031034fe7298031004fd729803101efa709803101efb109803101ef81098031004ff75580310067f75580310047f7558031014fe7558031014fc75580310067c75580310147c7558031004ff7458031006bf7458031004bf745803100cfe745803100cfc7458031006bc745803100cbc7458031004ff7258031006ef7258031004ef7258031034fc7258031006ec7258031034ec7258031006df3258031006dd325803101edf315803101edd315803101ef6215803101efb705803101efb105803101ef4105803101ef8105803101e7f7559621004ff745962100cfe745962100cfc74596210de7f54596210067e54596210de7c5459621004ff7359621004fc73596210de7f53596210de7c53596210de7f525962101cfc715962101e7e515962101e7c5159621004ff7059621004fc70596210de7f50596210de7c50596210067f74596210067e74596210067d74596210067c74596210067f73596210067e73596210067d73596210067c73596210067f43596210067c43596210067f72596212de7e72596210067d72596212de7c72596210067f42596212de7e42596212de7c42596212de7e32596212de7c325962101e7f715962101e7e715962101e7d715962101e7c715962101e7f415962101e7e415962101e7d415962101e7c415962101e7f315962101e7e315962101e7d315962101e7c315962101e7f215962101e7e215962101e7d215962101e7c21596210067f70596210067e70596210067d70596210067c70596210067f40596210067c40596212de7f20596212de7c205962101e7f105962101e7e105962101e7d105962101e7c1059621004ff7559221014fe7559221014fc755922101ebf7459221006bf54592210d6be54592210d6bc5459221004ff7359221004fc73592210d6bf43592210d6bc43592210d6bf425
  | 30 => 0xf76545310fcfd7654531014fc76545310067f65545310167c6554531005df7354531005dc735453101fd4315453100cff76505310f4fd765053100cfc7650531006bf645053100ebc6450531005df7350531005dc735053101fb4415053101fd4315053101dde73cc53101df673cc53101fd763cc531006f762cc531007d632cc531014fe75d8131004fd75d8131014fc75d813100cfe74d8131004fd74d813100cfc74d8131034fe72d8131004fd72d8131006fb60981310057f75581310fd7c7558131005bf74581310f5bc7458131005ef7258131005ec7258131006f96018131014fe7518131004fd7518131014fc751813100cfe7418131004fd741813100cfc7418131034fe7218131004fd7218131006de3218131006f731181311a6de31181311a6dc311813101e7f7559431004ff745943100cfe745943100cfc74594310ee7f54594310ecfc73594310ee7c5359431004ff7259431034fc72594310ee7c525943101cfe715943101cfc715943101e7e515943101e7c5159431004ff7059431004fc70594310ee7f5059431004ff7559031014fe7559031014fc755903101ebf74590310e6be54590310e4fc73590310e6bc4359031004ff7259031034fc72590310e6bc425903101cfe715903101cfc715903101ebe415903101ebc4159031004ff7059031004fc70590310e6bf4059031004ff765503101cfe7655031004fd765503101cfc76550310167e65550310067d655503100ebe6455031006bd64550310e73c5455031005df7355031005dc7355031014fe7598c3111cfd7598c31014fc7598c3100cfe7498c31114fd7498c3100cfc7498c3101ede3198c3101ef63198c3101edc3198c3111cff7694c3101cfe7694c31014fd7694c3101cfc7694c310167e6594c310067d6594c310ef5f5394c3101df67194c31005f57194c3111cff7654c31005bf7454c310e5bc7454c310ef5c5354c31114ff7690c3101cfe7690c3100cfd7690c3101cfc7690c3100ebe6490c31006bd6490c3101df67190c31005f57190c31114ff7650c310057f7550c310ed7c7550c310e79c4350c31004ff7558831014fe7558831014fc7558831004ff745883100cfe745883100cfc745883101eef725883101eee215883101eec2158831004ff7058831004fc7058831034ff769483101cfe7694831004fd76948310167e65948310067d6594831005de7394831005dd739483101df67194831005f57194831004ff7654831004fd765483101cfc76548312867f65548310167c6554831034ff769083101cfe7690831004fd769083100ebe6490831006bd6490831005de7390831005dd739083101df67190831005f57190831004ff7650831004fd765083101cfc765083127ebf645083100ebc6450831034fd76cc831036ee62cc831006ed62cc831
  | 31 => 0x953100cfc74d95310067e54d95310fe7c54d953101cfd73d95310fe7f53d9531034fe72d9531004fd72d95310fe7f52d95310fcfd71d95310fe7f51d9531004fe70d9531004fd70d95310fe7c50d95310fe7c6559531005bf74595310f5bc74595310fcff75595310067f7559531004ff7459531006bf7459531004bf745953100cfe745953100cfc7459531006bc745953100cbc74595310fe7f545953110cff7359531006df73595310fe7c5359531004ff7259531034fc725953111cff7159531006f77159531004ff7059531004fc705953100cfe76d91310f6be64d9131014fe75d9131004fd75d9131014fc75d9131006bf54d91310f6bc54d913101cfd73d91310f6bf43d9131034fe72d9131004fd72d91310f6bf42d91310f4fd71d91310f6bf41d9131004fe70d9131004fd70d91310f6bc40d91310057f75591310fd7c75591310f6bc6459131004ff75591310067f75591310047f7559131014fe7559131014fc75591310067c75591310147c75591310f4ff7459131006bf74591310f6be5459131104ff7359131006df73591310f6bc4359131004ff7259131034fc7259131114ff7159131006f77159131004ff7059131004fc7059131004ff7655131004fe7655131004fd7655131004fc76551310167e65551310067d655513100ebe6455131006bd64551310f73c5455131005df7355131005dc735513110cfe7694d310167e6594d310067d6594d310ff5f5394d3101cfc7654d310067f6554d310167c6554d31005bf7454d310f5bc7454d31005f77154d3101df47154d31104fe7690d3100ebe6490d31006bd6490d3101cfc7650d310057f7550d310fd7c7550d31006bf6450d3100ebc6450d310f79c4350d31005f77150d3101df47150d31014fe75d8931004fd75d8931014fc75d893100cfe74d8931004fd74d893100cfc74d8931206de31d8931206dc31d8931004fe70d8931004fd70d89310fd7e75989310057d75989310f5be7498931005bd7498931006ef6298931036ee6218931006ed6218931004fe7694931004fd7694931034fc7694931004ff7654931004fe7654931004fc76549310067f65549310167c6554931005df7354931005dc7354931004fe7690931004fd7690931034fc7690931004ff7650931004fe7650931004fc7650931006bf645093100ebc6450931005df7350931005dc735093101cfe768c9310fd7e758c9310057d758c9310f5be748c931005bd748c931006ef628c931036ec628c93101df6718c931005f5718c93101cde768c9312975e758c9312975d758c9312979e748c9312979d748c931296df628c931007cf628c931297cc628c93101dde718c931297d6718c93101dd6718c931297d5718c93101ddc718c931005dd708c93101cfc764c931005f7714c93101df4714c931014f
  | 32 => 0x14fc7558a31004ff7458a3100cfe7458a3100cfc7458a3101eef7258a31006ef5258a31006ec5258a31006ef4258a31006ec4258a3101ef43158a3101eee2158a3101eec2158a31004ff7058a31004fc7058a31006ef7558a31006ee7558a31006ed7558a31006ec7558a31006ef7458a31006ee7458a31006ed7458a31006ec7458a31006ef5458a31006ee5458a31006ed5458a31006ec5458a31006ed7358a31006ef5358a31006ee5358a31006ed5358a31006ec5358a31006ef4358a31006ee4358a31006ed4358a31006ec4358a3101eef7158a3101eee7158a3101eec7158a3101eef5158a3101eee5158a3101eed5158a3101eec5158a3101eef4158a3101eee4158a3101eed4158a3101eec4158a3101eef3158a3101eee3158a3101eed3158a3101eec3158a3101ee43158a31006ef7058a31006ee7058a31006ed7058a31006ec7058a31006ef5058a31006ec5058a31006ef4058a31006ec4058a3101eef1058a3101eee1058a3101eed1058a3101eec1058a31034ff7694a3101cfe7694a31004fd7694a310167e6594a310067d6594a31236be6494a31006bd6494a31005de7394a31005dd7394a31036ee6294a31006ed6294a31004ff7654a31004fd7654a3101cfc7654a310167e6554a310067d6554a3122ebe6454a31006bd6454a31036ee6254a31006ed6254a31034ff7690a3101cfe7690a31004fd7690a312267e6590a310067d6590a3100ebe6490a31006bd6490a31005de7390a31005dd7390a31036ee6290a31006ed6290a31004ff7650a31004fd7650a3101cfc7650a3121e7e6550a310067d6550a3100ebe6450a31006bd6450a31036ee6250a31006ed6250a312167e65cca310067d65cca3120ebe64cca31006bd64cca31036ee62cca31205dd76cca31006dd76cca312075e65cca312075d65cca312079e64cca312079d64cca31036de62cca31207ce62cca31036ce62cca31207cd62cca31036dc62cca31205dd71cca31005de70cca31105be748ca31005bd748ca311f6be648ca31006bd648ca3101df6718ca31005f5718ca3101df576cc631006f576cc63101f7665cc63101f7565cc63101fb664cc63101fb564cc63101fd673cc631007d653cc631007d553cc63101fe662cc631006f562cc63101fe562cc631006e562cc631014fe7598231004fd7598231014fc759823100cfe7498231004fd749823100cfc7498231034fe7298231004fd7298231006f7319823101ef4319823101efa709823101efb109823101ef81098231004ff7558231014fe7558231014fc7558231004ff745823100cfe745823100cfc7458231004ff7258231034fc7258231006df325823101edf315823101edd315823101efb705823101efb105823101ef81058231014fe76d95310fe7e65d953100cfe74d9531004fd74d
  | 33 => 0xe215963101e7d215963101e7c21596310067f70596310067e70596310067d70596310067c70596310067f40596310067c405963101e7f105963101e7e105963101e7d105963101e7c1059631004ff7559231014fe7559231014fc755923101ebf7459231006bf5459231106be5459231106bc5459231106bf4359231004ff7259231034fc7259231106bf4259231106bc425923101cfc715923101ebe415923101ebc4159231004ff7059231004fc7059231106bf4059231106bc4059231006bf7559231006be7559231006bd7559231006bc7559231006bf7359231006bd7359231106bc7359231006bf5359231006bc5359231006bf7259231006be7259231006bd7259231006bc7259231006bf5259231006bc525923101ebf715923101ebe715923101ebd715923101ebc715923101ebf515923101ebe515923101ebd515923101ebc515923101ebf315923101ebe315923101ebd315923101ebc315923101ebf215923101ebe215923101ebd215923101ebc2159231006bf7059231006be7059231006bd7059231006bc7059231006bf5059231006bc505923101ebf105923101ebe105923101ebd105923101ebc1059231004ff765523101cfe7655231004fd765523101cfc76552310167e65552310067d655523100ebe6455231006bd64552311073c5455231005df7355231005dc735523101ede3158e310fcfd7694e310167e6594e310067d6594e31246be6494e31006bd6494e3110f5f5394e31014ff7654e3101cfc7654e310167e6554e310067d6554e31005bf7454e31105bc7454e3123ebe6454e31006bd6454e3110f5c5354e31005f77154e3101df47154e310f4fd7690e3114e7e6590e310067d6590e3100ebe6490e31006bd6490e3100cff7650e3101cfc7650e310057f7550e3110d7c7550e311467e6550e310067d6550e3100ebe6450e31006bd6450e311079c4350e31005f77150e3101df47150e31036ef7598a31036ee7598a31036ed7598a31036ec7598a31036ef7498a31036ee7498a31036ed7498a31036ec7498a31006ef5498a31006ee5498a31006ed5498a31006ec5498a31036ef7398a31006ef5398a31006ee5398a31006ed5398a31006ec5398a31006ef4398a31006ee4398a31006ed4398a31006ec4398a3101eef7198a3101eee7198a3101eed7198a3101eec7198a3101eef5198a3101eee5198a3101eed5198a3101eec5198a3101eef4198a3101eee4198a3101eed4198a3101eec4198a3101eef3198a3101ecf3198a3101eee3198a3101eed3198a3101ecd3198a3101eec3198a31036ef7098a31036ee7098a31036ed7098a31036ec7098a31006ef5098a31006ec5098a31006ef4098a31006ec4098a3101eef1098a3101eee1098a3101eed1098a3101eec1098a31004ff7558a31014fe7558a31
  | 34 => 0x9331116bf4259331116bf4159331004ff7059331004fc7059331116bc4059331004ff7655331004fe7655331004fd7655331004fc76553310167e65553310067d655533100ebe6455331006bd64553311173c5455331005df7355331005dc735533101cfd7694f310167e6594f310067d6594f3111f5f5394f3101df67194f31005f57194f310ecff7654f31005bf7454f31115bc7454f3101cfd7690f3100ebe6490f31006bd6490f3101df67190f31005f57190f310e4ff7650f310057f7550f3111d7c7550f311179c4350f31006ef6298b31004ff7558b31014fe7558b31014fc7558b31004ff7458b3100cfe7458b3100cfc7458b311dede3158b311dedc3158b31004ff7058b31004fc7058b3111d7e7518b310057d7518b31115be7418b31005bd7418b31036ee6218b31006ed6218b31034ff7694b31004fe7694b31004fd7694b31036ee6294b31006ed6294b3101df67194b31005f57194b31004ff7654b31004fd7654b31004fc7654b310167e6554b310067d6554b31005df7354b31005dc7354b31036ee6254b31006ed6254b31034ff7690b31004fe7690b31004fd7690b31036ee6290b31006ed6290b3101df67190b31005f57190b31004ff7650b31004fd7650b31004fc7650b3100ebe6450b31006bd6450b31005df7350b31005dc7350b31036ee6250b31006ed6250b3101cfd76ccb3101df671ccb31005f571ccb31014ff76547310167e65547310067d6554731005df7354731005dc735473101fd6315473100cff765073100ebe6450731006bd6450731005df7350731005dc735073111d7e75d83310057d75d8331115be74d8331005bd74d8331005ee72d8331005ed72d8331006fb6098331014fe7598331004fd7598331014fc759833100cfe7498331004fd749833100cfc7498331034fe7298331004fd72983311aede31983311aedc3198331004ff7558331014fe7558331014fc7558331004ff745833100cfe745833100cfc7458331004ff7258331034fc7258331006f9601833101e7f7559631004ff745963100cfe745963100cfc745963110e7f54596310067e545963110e7c545963110e7f5359631004ff7259631034fc725963110e7f525963110e7c525963101cfc715963101e7e515963101e7c5159631004ff7059631004fc705963110e7f505963110e7c50596310067f74596310067e74596310067d74596310067c74596310067f73596310067d735963110e7c73596310067f43596310067c43596310067f72596310067e72596310067d72596310067c72596310067f42596310067c425963101e7f715963101e7e715963101e7d715963101e7c715963101e7f415963101e7e415963101e7d415963101e7c415963101e7f315963101e7e315963101e7d315963101e7c315963101e7f215963101e7
  | 35 => 0xdbc7494d412473e5494d411275f5394d41004ff7654d41004fe7654d41004fc7654d41005bf7454d4100dbc7454d410073d5454d4101cbe7690d41005bf7590d41005bd7590d4114ebe6590d4114ebc6590d4100dbe7390d4100f9e7390d41006bf6390d410079f6390d410079c6390d412bdbe7290d4101dbe7190d41007b67190d4101db67190d41007b57190d4101dbc7190d4100ebf6190d4100fb76190d41005bd7090d41014fe75d8941004fd75d8941014fc75d894101cfd74d89410d6be54d8941006bd54d8941004fe73d8941004fd73d8941006be43d89410d6bc43d89410d6ee42d89410d6ed42d89412bebc42d89412e6be41d89412e6bc41d8941004fe70d8941004fd70d89410d6bf40d89411257e75989410057d7598941005de7398941005dd7398941006ef62989410c5f5719894124df77158941036ee6218941006ed6218941004fe7694941004fd7694941034fc769494100dbc7494941004fe7654941004fc7654941005bf745494100dbc74549410073d545494101cbe76909412bdbf7590941005bd7590941005be739094100dbe729094100fae72909412bebf6290941007af62909412bfac629094101dbe71909412bfb6719094101db671909412bfb5719094101dbc719094100ebf619094100fb76190941005bd7090941014ff765454100cfe7654541134fd765454100cfc76545410067f65545410167c6554541005bf745454100dbc74545410073d545454101fb44154541014fe75d8141004fd75d8141014fc75d814101cfd74d8141004fe73d8141004fd73d8141034fe72d8141004fd72d814105efa40d8141006fb60981410057f75581411257c7558141005df7358141005dc7358141005ef7258141005ec7258141006f96018141014fe7518141004fd7518141014fc751814101cfd7418141026be5418141006bd5418141004fe7318141004fd7318141006be4318141026bc4318141034fe7218141004fd7218141006be4218141026bc421814125ebe411814125ebc4118141026bf4018141026f9401814111e7e65d973100cfe74d9731004fd74d973100cfc74d9731006de73d9731034fe72d9731004fd72d9731006f571d9731004fe70d9731004fd70d973111e7c65597310067f7559731004ff745973100cfe745973100cfc745973111e7f545973101cfc735973111e7c5359731004ff7259731034fc725973111e7f525973111e7f5159731004ff7059731004fc705973111e7c5059731116be64d9331014fe75d9331004fd75d9331014fc75d9331006de73d9331034fe72d9331004fd72d9331006f571d9331004fe70d9331004fd70d9331116bc6459331004ff7559331014fe7559331014fc7559331006bf7459331116be545933101cfc7359331116bc4359331004ff7259331034fc725
  | 36 => 0xc7454e41004ff7558a41014fe7558a41014fc7558a41004ff7358a41004fc7358a4101eef7258a41006ef5258a41006ec5258a410c6ee4258a410c6ed4258a4101cfc7158a4101eee2158a4101eec2158a41004ff7058a41004fc7058a4101cfe7694a41004fd7694a4100dbe7494a41005bd7494a41034bf7650a4127ebf6550a41006bd6550a41006be6350a4100dbf7250a4100faf7250a41036be6250a4127fae6250a41036ae6250a4127fad6250a41036bc6250a4127dbf7150a41007b77150a4127fb47150a4100ebe6150a4100fb66150a41005bc7050a41014fe7598241004fd7598241014fc7598241004fe7398241004fd7398241034fe7298241004fd729824101cfe719824101efa709824104ef9409824101efb109824101ef81098241004ff75582410067f75582410047f7558241014fe7558241014fc75582410067c75582410147c7558241004ff7358241004fc7358241004ff7258241034fc725824103ebf4258241006bd425824101cfc715824101ebf415824101ebd415824101efb705824103efa405824103ebc405824101efb105824101ef81058241014fe76d95411267e65d954101cff74d954101cfd74d954113e7f54d954113e7d54d9541004fe73d9541004fd73d95411267c53d9541034fe72d9541004fd72d95411267f52d954100cfd71d95411267f51d9541004fe70d9541004fd70d95411267c50d95411267c6559541005df7359541005dc73595412edf7715954113cff75595410067f7559541134ff7459541006bf7459541004ff7359541006df7359541004df7359541004fc7359541006dc7359541004dc7359541004ff7259541034fc72595412ecff7159541006f77159541004ff7059541004fc705954101dbc7655141016bc765514101cbc765514100dbf755514100f3f75551410073f6555141016be6555141016bc65551411273c65551410163c65551410079f7355141005bc73551410079c73551410059c73551411273f53551412bdbc72551411273f5255141007b7715514101dbe715514101dbc7155141007b4715514100ebf615514100fb761551411273f5155141005bf70551411273c5055141014fe75d8d41004fd75d8d41014fc75d8d4101cfd74d8d41106be54d8d41006bd54d8d41006df53d8d41006dc53d8d41106de43d8d41106dd43d8d41106bc43d8d41034fe72d8d41004fd72d8d41004fe70d8d41004fd70d8d41006df6398d410f5f57198d410057f7558d411257c7558d41115f77158d41006dd6318d41014fe7518d41004fd7518d41014fc7518d4101cfd7418d41006df5318d41006dc5318d410e6de4318d410e6dd4318d41034fe7218d41004fd7218d41004fe7018d41004fd7018d41004fe7694d41004fd7694d41004fc7694d410067f6594d410167c6594d41
  | 37 => 0x8d51006df4318d51006dc4318d51034fe7218d51004fd7218d51004fe7018d51004fd7018d5101c7e7694d510057d7494d512467e6494d512467c6494d510157e7394d510175e7394d510067f6394d510075f6394d510065f6394d510075c6394d512dd7e7294d5101d7e7194d51007767194d51007757194d5101d7c7194d510167f6194d51017776194d510057d7094d51004fe7690d51004fd7690d51004fc7690d510057f7590d510157c7590d51006bf6490d5100ebc6490d5114f3f5490d51004ff7650d51004fe7650d51004fc7650d510057f7550d510157c7550d510073d5450d511379c4350d5101cfd75d895100cfe74d8951004fd74d895100cfc74d89510de7f54d89510067d54d8951004fe73d8951004fd73d89510067e53d89510de7c53d89510deee52d89512de7c52d89512f67e51d89512f67c51d8951004fe70d8951004fd70d89510de7f50d8951135be7498951005bd7498951005de7398951005dd7398951006ef6298951036ee6218951006ed6218951004fe7690951004fd7690951034fc76909510157c7590951004fe7650951004fc7650951006bf645095100ebc64509510073d545095101cfd75d815100cfe74d8151004fd74d815100cfc74d8151004fe73d8151004fd73d8151034fe72d8151004fd72d8151066fa50d8151006fb6098151005bf7458151135bc7458151005df7358151005dc7358151005ef7258151005ec7258151006f9601815101cfd751815100cfe7418151004fd741815100cfc741815102e7f54181510067d5418151004fe7318151004fd73181510067e531815102e7c5318151034fe7218151004fd721815102e7c521815126e7e511815126e7c511815102e7f501815102ef9501815101e7f75596411367f54596411367d5459641004ff7359641004fc735964112e7c5359641004ff7259641034fc725964112e7c5259641136bf425964101cfe715964101cfc715964101e7e515964101e7c515964101ebf415964101ebd4159641004ff7059641004fc705964112e7f5059641136bc4059641014fe7598e41004fd7598e41014fc7598e4101ede7398e41006df5398e41006dc5398e41116de4398e41116dd4398e41034fe7298e41004fd7298e41116bf4298e4101cfe7198e4101ebf4198e4101ebd4198e4101ede3198e4101edc3198e41004fe7098e41004fd7098e41116bc4098e41004ff7558e41014fe7558e41014fc7558e4101edf7358e41006df5358e41006dc5358e410f6de4358e410f6dd4358e41004ff7258e41034fc7258e4101cfc7158e4101ede3158e4101edc3158e41004ff7058e41004fc7058e41004ff7694e4101cfe7694e41004fd7694e410167e6594e410067d6594e4112f5f5394e41004ff7654e41004fd7654e4101cfc7654e41005bf7454e4100db
  | 38 => 0x4fc70592511267c505925113ebf405925100cfe7498e51004fd7498e5100cfc7498e5101ede7398e5111ede5398e5111edd5398e51006df4398e51006dc4398e51034fe7298e51004fd7298e5111e7f5298e5101cfe7198e5101e7f5198e5101e7d5198e5101ede3198e5101edc3198e51004fe7098e51004fd7098e5111e7c5098e51004ff7458e5100cfe7458e5100cfc7458e5101edf7358e510fede5358e510fedd5358e51006df4358e51006dc4358e51004ff7258e51034fc7258e5101cfc7158e5101ede3158e5101edc3158e51004ff7058e51004fc7058e51004ff7690e5101cfe7690e51004fd7690e5100ebe6490e51006bd6490e51004ff7650e51004fd7650e5101cfc7650e510057f7550e510157c7550e5113f9c4350e51004ff7458a5100cfe7458a5100cfc7458a51004ff7358a51004fc7358a5101eef7258a510ceee5258a51006ef4258a51006ec4258a5101cfc7158a5101eee2158a5101eec2158a51004ff7058a51004fc7058a5101cfe7690a51004fd7690a5100ebe6490a51006bd6490a5100cfe7498251004fd749825100cfc7498251004fe7398251004fd7398251034fe7298251004fd729825101cfe719825101efa7098251056f9509825101efb109825101ef81098251004ff7458251006bf7458251004bf745825100cfe745825100cfc7458251006bc745825100cbc7458251004ff7358251004fc7358251004ff7258251034fc72582510467f525825101cfc715825101e7f515825101e7d515825101efb7058251046fa50582510467c505825101efb105825101ef8105825100cfe76d9151136be64d915101cfd75d9151136be54d915112ebd54d9151004fe73d9151004fd73d9151136bc43d9151034fe72d9151004fd72d9151136bf42d9151014fd71d9151136bf41d9151004fe70d9151004fd70d9151136bc40d9151136bc6459151005df7359151005dc73591512fdf7715915101d7c765515100e7c765515101c7c76551510157f74551510173f74551510073f645515100e7e645515100e7c64551511373c645515100e3c64551510075f73551510057c73551510075c73551510055c73551511373f43551512dd7c72551511373f425515100777715515101d7e715515101d7c71551510077471551510167f61551510177761551511373f41551510057f70551511373c405515101cfd75d8d5100cfe74d8d51004fd74d8d5100cfc74d8d5110e7f54d8d510067d54d8d5110ede53d8d5110edd53d8d5110e7c53d8d51006df43d8d51006dc43d8d51034fe72d8d51004fd72d8d51004fe70d8d51004fd70d8d51006df6398d510fdf57198d51005bf7458d51135bc7458d5111df77158d51006dd6318d5101cfd7518d5100cfe7418d51004fd7418d5100cfc7418d510eede5318d510eedd531
  | 39 => 0xc7655143016bc7655143014bc765514300dbf755514300f3f75551430073f6555143016be6555143016bc65551431473c65551430163c65551430079f7355143005bc73551430079c73551430059c735514300ebf635514300f9f63551431473f53551431473f52551431473f51551431473c5055143304fe7694d432467f6594d430167c6594d4300dbc7494d432473e5494d431475f5394d432479c4394d4300cfe7654d4323cfd7654d4300cfc7654d43005bf7454d4300dbc7454d430073d5454d4323f9c4354d43005bf7590d43005bd7590d430073f6590d4314ebe6590d4314ebc6590d430073c6590d4314e3c6590d4300dbe7390d4300f9e7390d4300d9e7390d4300ebf6390d4300f9f6390d430067f65d89430067c65d894320f9c43d8943014fe75d8943004fd75d8943014fc75d894320ebe54d8943006bd54d8943006be43d894320ebc43d894320eee42d894301cfe71d8943004fd71d8943004fe70d8943004fd70d89431457e75989430057d75989430067f65989430067c65989431f79c4398943006ef6298943005f67198943005f571989430057f75589431457c75589430067f65589430067c65589431e79c43589430067f65189430067c65189431cf9c4318943036ee6218943006ed62189430067f65d85430067c65d85431179c43d8543014fe75d8543004fd75d8543014fc75d8543116be54d8543006bd54d8543006be43d8543116bc43d8543034fe72d8543004fd72d8543116f641d8543004fe70d8543004fd70d85431457e75985430057d75985430067f65985430067c65985431079c4398543005ee7298543005ed7298543006f761985430057f75585431457c75585430067f65585430067c65585430f79c43585430067f65185430067c65185430e79c431854301ef66118543006f561185430067f65d81430067c65d814309f9c43d8143014fe75d8143004fd75d8143014fc75d8143034fe72d8143004fd72d814301cfe71d8143004fd71d814309efa40d81431457e75981430057d75981430067f65981430067c659814308f9c4398143006fb60981430057f75581431457c75581430067f65581430067c655814307f9c4358143005ef7258143005ec7258143005f77158143005f471581430067f65181430067c651814306f9c4318143006f96018143014fe7518143004fd7518143014fc751814306ebe5418143006bd5418143006be431814306ebc4318143034fe7218143004fd721814301cfe7118143004fd711814306ef9401814301ebf745925113ebe5459251126bd5459251004ff7359251004fc735925113ebc4359251004ff7259251034fc72592511267f525925113ebc425925101cfe715925101cfc715925101e7f515925101e7d515925101ebe415925101ebc4159251004ff7059251
  | 40 => 0x9643004fd70d9643246bc40d9643014ff765964314e7c655964300dbc745964314f3f54596430067f755964323e7f545964314ebf545964314e3f545964323e7d545964323ebc545964300cfc735964314e7c535964323ebf4359643004ff7259643034fc725964323ebf4259643004ff715964301cfc715964323ebf4159643004ff7059643004fc705964323ebc4059643014fe7694e4300cfd7694e4300dbe7494e43005bd7494e432473c5494e432479f4394e4314d7e7598a430057d7598a43006ef6298a43004ff7558a43014fe7558a43014fc7558a431e6ee4258a43004ff7158a4301cfc7158a43004ff7058a43004fc7058a43036ee6218a43006ed6218a4314d7e75986430057d7598643006f76198643004ff7558643014fe7558643014fc7558643004ff7258643034fc72586430f6f64158643004ff7058643004fc705864301ef66118643006f56118643006fb6098243014fe7598243004fd7598243014fc7598243034fe7298243004fd729824301cfe7198243004fd719824308ef940982430057f755824314d7c7558243004ff75582430067f75582430047f7558243014fe7558243014fc75582430067c75582430147c7558243004ff7258243034fc725824307ebf4258243004ff715824301cfc715824307ebf415824307efa405824307ebc4058243006f96018243014fe76d95431467e65d95432479c43d9543244ff74d9543244fd74d95432467f54d95432467d54d954300cfd73d95431467f53d9543034fe72d9543004fd72d95431467f52d95431467c52d954301cfe71d9543004fd71d95431467f51d95431467c51d9543004fe70d9543004fd70d95431467f50d95431467c50d95433057e76d95430147e76d95430073f74d95432473c74d95432475f43d95432473c43d95432475c43d95432471c43d95432467f74d95432467e74d95432467d74d95432467c74d95432467f73d95431467e73d95432467d73d95432467f43d95432467e43d95432467c43d95430067f72d95430067e72d95430067d72d95430067c72d95432467f42d95432467e42d95432467d42d95432467c42d95430067f71d95430067e71d95430067d71d95430067c71d95432467f41d95432467e41d95432467d41d95432467c41d95430067f70d95430067e70d95430067d70d95430067c70d95432467f40d95432467e40d95432467d40d95432467c40d95431467c655954330ddf735954323f9c435954323cff7459543006bf745954330cff7359543006df735954330cdf7359543004ff715954301cfc7159543004ff7059543004fc70595432457e76195431467e76195432447e76195433073e74195431473d74195433067f64195433067f63195433065f63195433075f43195433073c43195433075c43195433071c4319543145b
  | 41 => 0x30edd74d8d5430edc74d8d5430ede54d8d5430edc54d8d54006df71d8d54006de71d8d54006dd71d8d54006dc71d8d5432edf51d8d5432ede51d8d5432edd51d8d5432edc51d8d5430edf41d8d5430ede41d8d5430edd41d8d5430edc41d8d54006df70d8d54006de70d8d54006dd70d8d54006dc70d8d5430edf40d8d5430ede40d8d5430edd40d8d5430edc40d8d542473c5498d54006df6398d5423f3c5458d543073c5418d54006dd6318d54014fd7418d54326bd7418d543067e5418d54306bc5418d543063c5418d54306bf4318d54306dd4318d5401cfe7118d54004fd7118d543267f5118d54306bf4118d54004fe7018d54004fd7018d54306bc4018d5430dde7618d54006de7618d543079e7418d543279d7418d543075e5418d543079c5418d543071c5418d543275f5118d543079f4118d543079c4018d54306df7418d54306de7418d543069e7418d54306dd7418d543269d7418d54306dc7418d54306de5418d543065e5418d54306dd5418d54306dc5418d543069c5418d543061c5418d54006df7118d54006de7118d54006dd7118d54006dc7118d54326df5118d543265f5118d54326de5118d54326dd5118d54326dc5118d54306df4118d543069f4118d54306de4118d54306dd4118d54306dc4118d54006df7018d54006de7018d54006dd7018d54006dc7018d54306df4018d54306de4018d54306dd4018d54306dc4018d543069c4018d5401cfe76d85542ef3c54d8554006df63d8554006dc63d855400cfd75d8554014fd74d8554004fe73d8554004fd73d8554034fe72d8554004fd72d85542fef651d85542eef641d8554004fe70d8554004fd70d855413f3c5498554005de7398554005dd7398554006df6398554006dc6398554005ee7298554005ed7298554006f761985541373c5458554005df7358554005dc7358554006df6358554006dc635855431f3c5418554006df6318554006dc631855401ef66118554006f561185542c73c54d8154006df63d8154006dc63d8154014fd74d8154316bd74d8154004fe73d8154004fd73d815401cfe71d8154004fd71d81543167f51d81542c6bf41d81542c6fa40d81542c6bc40d81541bf3c5498154005de7398154005dd7398154006df6398154006dc6398154006fb60981541b73c5458154005df7358154005dc7358154006df6358154006dc6358154005f77158154005f471581542b73c5418154006df6318154006dc6318154006f96018154014fd7418154004fe7318154004fd731815401cfe7118154004fd71181542b6f9401815414e7e65d96432473c54d9643305de73d96432467e54d9643246bc54d96432463c54d9643304fe73d9643006de73d9643304de73d9643246bf43d964301cfe71d9643004fd71d964314e7f51d9643246bf41d9643004fe70d
  | 42 => 0x2000c00100200000000000000400300000000000000000c00000000000000001000400300080000018000000000100000000008000000c00400040000000001001c0000000002000000100040030000000000c0000020001000800300080030008000000000100100000018002000c006000400100000010008000000400500080020000000000000200100000004001000000100000000008003000c0040000008000001b000000000000000014006000000000000010000000001400300100020000000000c0030004002000800000000000020000000400000000010010000000c0000008002000000000000000000000002400000040060000000000c001000000000040000014009000000100000040004000000c001000c0000000005000400000000030004001000000200000010008000000000000180010000000001c000000c002000c0020004009000800300000010004002000000000000000000001000c00100000000004000000400000040010004000000c00a000801b000800000180000004000001000100000030004000001c0010000000000c001001c0010000001000800c00000040000000002000000300010008000000400000000000014003000400100040090008003000800100000000004000000c0010004001000000000040010000001000000100000000000000002000400180000000002000400100000040008000001c0030018000000400a0004001000400100140000000000001000100140000010006001800200000020010000000400600000000008000000c000000000700000000004001000800200000010004000000c0030000000000000200040000000016000000200000080004005000000000040000004001000400000000000008006000000300000030004003000000600140020000000000400100000000014001000800000000030008004000c00000000010004003000400200000000000006000400800000020000000000400100000000000000000800000000010004000000c003000000e0010000000c00000000010018001000800000000040000001000801d00000000008000000000100300000000002000400100080030000001000c000000c00000100000000000000800100000030000002000000000000060004001001800200400000000000000400000000000004000000c00000080030004000003c00100100060000000000000000080000004000000400000000080008002000000100000090010006000000530f3c54d8d54014fd74d8d5430ede43d8d5401cfe71d8d54004fd71d8d54004fe70d8d54004fd70d8d5432f9f74d8d5430f9c74d8d5430f5e54d8d5430f9c54d8d5430f1c54d8d5432f5f51d8d5430f9f41d8d5430f9c40d8d5430edf74d8d5430ede74d8d54
  | 43 => 0x10008000001000000000080000000000000000040080004002001c00400040000020000000800c004000300300070000000001400a00040000000003000000100000010014001000000000000000000004000000400180010004003000c00000040000004001000400800000100004000000400200080000014002000c000001c00100040000008000000400f000000300000010008001001000000000000008003000000000080030000003000400000480010000000001800000040020000000000000d00000010014000003400200080030048000000000000000000008000000c00000040000000000000800100000050000007001400000080010020003002800100000000008002002800a00000000000008000400400100010000000000001300000000008000000c000000000000040000038000000000000300030000001000000000040010004000000000000300020018005000000400040010000000000000000000010014000001000400040040000001000800300040020004000000000000000080004001000c0010004000001000000000000008001000400000000000000000000c00200000010020000000000100180010004000001c000001c000000800100040060028003001000300040020018001000c00100000000000000000000200080000000000001400100000000020000000400200000000000000001400400080010000001000000000000030010000000000000180000004002000400600040000010000001c0000018001001000000000000004003000c004001800200040000000000002000000000000014003002c003000000000000040000006002000000140000004000000000000100020004000000000700000030000002000400500300020004000001c003000000300040010000001000000400040000014003002400100180030014000002000000180000004002001800000000030004000000c006000000000040000008000000000000100020004000000400100080010010000001800100080030000000000000000000010000001000000000280050000001000400200100060008000000c007000000000140040000002000000200000060000005000c007000000100000000000003000c0020004004000000500000040008006001000700000040004000000c001000000000000000004001000000000140000000001000000000000000000003000000000140000004001000000100080050000002001c0000004009000400000000000000006000000700080010000001000c000000000000000030014000001800100000010004003001c00a0000000000000100000010040000001c000000400800000010000000000800300100000000002000400000100000000000001c000001c
  | 44 => 0x6000c003000400c000c000000000000000000000000001c0000008002000800300080000004000001000100040020000001001000100000090008000000800000200000000007000800100040040010000000c00000000000000011000000000000010004003000000000000030004000000000100000010000005002c00200000060000001000800000040030008000000800100140010000000000400000000030014003000c001000000100280030000000000400200000000008000003400000000050000000000c0000008000000000000280040028002000000000280000008000000c001000000600040020000000001800000000010008001000000100040050008000000000200000020024001000c001000000700040030000001000800000000010004001000c00000040010000000002800400040000018000000c00100000030010007000400800000030000000000000200300010000000000000700000040000003001000000000000008000000000600000010008001000c002000800000000000004000000400000000010010001000c0030008000000c0030000000000800000000000000001001c000002000000000110028000000c00200000000004000000c0000000000000400000040000000000000000100000020004000001400000000000030000000000100000000004003000800b0000000000c007002c00100040000000000000400000380000018003000400000080000004001000400800000010004001001c004000000000040000000000000400000100000000000002800600480010000000002400100040000004001003400000040040010002000400000000000000004001000000080000000000000400300000010004000001000000080040004001000000100040010000001000000100080040000003000400100140070008000001400000400040000001000800100080020004000001400000040000010001000000800040060000000001000100140020024001001c003000800000040010000001000400d0000000000000300000000008000000c000000000100000000000000001800200200000000015001c00100000010008001000000100000030000000000c001000c0000030001000c00300080000010000001400000000020004000000800300300010008014000000c0008001000c000000400b00100010000002000000000000020000001000000000000010000000000400100100000000000005c001000000000000000008007000800000000020008000001c0010000003000800300000000000000000400e000000400080000000000000c00100000020000001000c0010000001000c000002800d0008000000c00800000020004003000000300000000004010000c0020004000
  | 45 => 0x600040010004000001c0050000002000400500000000000003000000300040000028003000c00a00100000018001000c00100400010000001001c0010000001000c00100040010000002000800c00000040028004000000100040090010001000c00400100010000002000400200000010000003000c0030004003000c000000800b0004000002c00000000000014002000400200080000044001000c004000c001002c001000400000100030000000001c00000080080004000001800100000070000000000400500080000024001000000000000000000002000c001001000000000050010000000800300140070000013001000000000000004001000400000000050024000000c0020048001000800500000010000000000c000001400800080000018002001c00100000000000006000400200240060000000000400a001800100080000000005000000000000000010006000000000080070000003001c0000004000000c007000000200000000010002001400200080010008007003000900040060008005001000500000050000003000400400000070000002001400000040000000001000000200040010000000000c004000c0050008000000400000000000004000000800100180000014000000c00100140000018000000c0000010000000400000040060000000000800100000000000000000000100100030004009000800100000000004001000800400000000000001001c0030010009000c000000000300000020004000000000100000000000001000000c000000100080010000002001400300000050004000001800000080000004000000c001000400700000010000000000800800140000004000000800b000000100000000008001000000000100000000006000000400000020000002000000000000000020004000000000000030000000000000c0000003000000200140010004002000c0010014000000000000000040014003000000000040000004001002800000040000028001000800000080010000002000000100000000004002000400000000000004007001c000000800100000030000001000400200000000004003000000b000400000280000000001000000100000140004000001400100000070004002000000000000000004002000400000100010000000000000000000000008000000400000080010004000000000200080050018001000000000080000034000000c00100080020004001000c003000400200200020008001000000100000000014000000000500040010000002000000300080070004006001400000000010004001000000100140080004003000000000080050010002001800a001800000040000004000000400e002000700000010000004000c00000080010014000000c000000
  | 46 => 0xf730000e0e9531f2663381dc00037b6cab87f43da2afac06000000000000000fd8000000000000000001b7cb81a1ae0002ddcaf8b21d3a42f820000000000000000000000000000b4e2580000000000024be69499de00005da00000008608000000000000000000000000000000000000007460000b6b80000000000000078a173400046298de7e20000c500d9c7de000000000000000005000000000000040000008000000300040000004000000c003000000000100020008002001800200000000010003000400100080000008000000800000080000004001000400200000020004000000000400140020024003000000300080000000002000400000000080008000001000200040020008009000800200040030008002000000100000010004000000400000100010008001000800a000400000000010000005001400000040000000000000000100080030000000000000b00100000000000000800400100000004001000c00100000010008001000400100000040004001003c000000400100000000008006000000200000000004001000c000000800000040000004005000c00200000010008001000400100040200000001000000000100050000010000400f00000040008000000400400000000000002000000000000010000001000c001000c00600000040008002000400900280000000000002000b000c0000010000001000300040010000000000000300080000008000000400300180000004000000400000140000008000000800800000000000000000c00400000000000003000400500000000004002000000100140010000002000000500040000000000000c00000000010000000000400000180020004000000c0010000002000400500080010004000000c000000000300080010034000000c0010028004000c00100040020018000000000300100000028001001800000180000010003000000000140010004003000c0010008011000000100000000008000000c00000080020000001000400000100000000001001800000000000000001000400000080000008006000400300000000004000000000400080070000002000800000000000000001000000000000000000002001000000000020018000003000300200000008000000400100040010000002000000b000c00100040000004000000400200100000000007000000000040010000003001800200080060010000000000000000070000001000000000080000008001000c0070004000000c000000400100000000000005000400200100020000001000c001000000200000010000002000c00300000000008000000c00100000000008001000400a0000009000000300000010000001000400000080020014000000000000000000004000000000
  | 47 => 0x70400367a09792b0a07e0e06e52c9a00005de000000039b000000000002308000000000000000000000000000000000036c955a0000dc82b0b00000000003278000000000000000000000000030429800000000000000000078e80000000000000000000025ae00000fece10e7c0002b6296c040200007268091b3ebe40c2ae03cfcc0000000c34b2c6bb880000000000a648f247aba9b264c9a460001f2a0000000000000000000000000000000000000000005061f080000000000146017b991e6caac6a000041a0001fdd000000000008bccb0000000000000001d6200000005114000000000057c206ca5f1cb0839ad4c00021948960000506ad1ca4d000049b8000000000000000005ba130400003a40001828b838000000198e0000000000143800000003de000000000009b2800000000000000a986a301ba22a00007678000d7e273e00036f8000000000000005a900004c280000000000bb9824e270ae9cbb79afe0002b4e0a5277c0000000bcdb6d650d49d631e132740f954ca48a4e0c78b2347a108c892f06365408cb05252f4adaf0216daab27200025c40000000743882800002c40002ade000000000008ae0001976976062233f80000000000dfec00000000006e636369b5800000014b63c08a8e00000005700000000000045080000000000d270000806b6344c40e0638a5577b1e0000def00000000000cbf00004c1d88c00016e67cb2d52cdd00001ecebd0d818000c3000000000000b55a09ca852fc4000000018a153ce0180001279774640b4060ab8ce0000000000000000001758000203e0000000000000000000000000000000030a9d014b457700000000000000000081f45a42aa0852ae5b7a43b81a5ebe5a11024ad3fa23e10b359e9c1a000000000017f34c3000021c9e5cb4fb4fa0001e7406e1e8a77e8be67ab088c0f72130000104c5ef22a00000000a6b80000000000ada000000000008af92bc00000008a15d26c959fa672469a400000004b8c000000105883cc000000000027c00000000000532359c000000000000008f5095800796e40001b7000015d66653100df0c3630000a820002cca00000004cc800047d200d0000000000136a00018fe0b310d431f800000000000000000000134ed0f8f260000000000000000000002950000c2c000025c818f40716c900000008430d5c0000000000000000006162b132acb8437e628e80006648000ddac1c330bc0009db18620000000000221300027f627780dc3e3971bb4400000000000000000000000000000000a7080003438c928abaac200000003bab0f6de4845ac8836c200020f80001dc300024f20000000aea00005d28000000085859ba5aa9f6a6f568f000000032309e48d98ab680000000000ccd8000b8e0edeb040000c6f800000032526786a5637
  | 48 => 0xd2ec05cf92780000000000000000032587f09f9200016e00000000000000000007820000becd2b0000a1b04b20f7800009333bccdb283400026be05e9abc000000000033ae00000000002368aa640000000000a8121e2d0380000000c54000363800036a70002048b0700000002d7400000000b085c20001ad67a21294c168000461800000000008e0a26aa6fa3ee9492f8ea7880008594f3605e2cbc83005d29ef08847bf829c8f68000cd2ac38170000099e85cbbd72c972fa16441addc1297e80000002b7c14c8000000197c599400000031f4d858000deadbec0000000ac08000ae48000000016cab8800058814ea0000000bfcc0000000e72000000027c80000000000000180c58f72b030e33fc6cb8072542800000008f28da80005829b3fb4491fa1af099c23bacb10ee946d387294ebd9113c083000000000000000000807871c000000000032d4000135600023e2beb807e4622cce231000000035a40002c9e00015e98940000df8c0003f7800000032d20310000000217e772800048a80009990000ba2c0000000e1467113fedfcc73e1c41ab200008b600000000000000963000050208e68dd80003d98000420000029d00000000cb20001d4a0002a52be143b073e160e00036df000000000000000000000000000000006c46dd2428000000000021a400009730002d4200017461078c428561f460000000000223400000001620000180292b53e000000034487f3749636b9cbb458058c6f2246600000003840000000000068d0000451abf4a3108469c980000001b648df00000001069000262e0508000cd300000002b9400000000001d4c60e80004ad4000c0d000000000001782d8803c8000af001500c88000aefa114d600000000020a0000000000012c7768fb6574c00015da3280000000000337a00000009386732dae33926f4b21e012e6122780dbad898000086800075f400000020d0195a12647117b800008fa2cc000087dc00002800004a6961700031ee000000000000009ea94925fb6fcc00000000000000000289c02e000067180000001a883be00008e58d909b1b6220e79792000000000000000458b3427503160000000b8ac00098ae5e600007fa6302f000001eb700000003b08000117800063f000000026d04de9a56000187adc5853400000008856ab4000127643f1226b4394ae00000000003776000000000000008b41596000000066a2306000248836a00004aa000061080000000000a9c8000cba0000bf0000000030e2c5baa2835480000000000a0a141600015662151e8600000000000000d980000000000024980003d2800000018524e526c2c87c21f10c146a295b0679c2585039da6848ce8d205faf3e40000000d21000000016b60002cb624180000001f8ecf4acea5308000000000020e000032813
  | 49 => 0x4bbaa903bc96505ff00000002a36c4d4c661048000d8415e6a0e109edb067b2b06237ea29e0834902f54b62804400027241489ca8d170dc4b640fe78a362ef3f000000000000000000000000000001c440000000ce2000000000007a72ff95fe259400000000000000514000091188800000000000000000000000000000000000000037c1000000057d8bb84bd8000000275800008100000000766316c0000754b17927cdf56afcba08000dee73b65c78060705800038e80000000000a2a000000034745df08b027888d044a0000000000078394fe258800040d2d78620000057cc0001b280000000000079800049d198300037864a18d2e28601a4000000000000003ee80004bcb33480557dc6fb80000000000000000036d95080000000000000083dc000da880002e9800000000000000000a1e80000b79f42ad515161ff0f62000000093594d200029ed560b52025a0d268eb99c00000de05f280005c400008540000024800042640000000000000000000000000000000c4a00000000000486800044610b82a100000000000889047e3c6b3905c2f55107c147ace596fa00000000e3afa0513400028ec000000288592ec0009d800003a024aa250587e0a92c20dab3530b27e59c0002cd6b7fc00000003380000000862811400028b00000d3e00026a8578a03026a8d225bd061ad61057abba17dadc3805e00021c4000000000000001b5912c910000000004ee000230403b8cba24821ea00027ec000266ade7000000018e3cbea489dec0000000000000000000000000000000000015dfe04c000000370700017c81b200009e19de6000111e00033c40001cfa2071bf8d56a81570d00000000c00000000000017e778423674d72fe00000000000000000000007220000a2f800000015b0402800037680001b719c200000000000000000000000000000000000000000000000000000000000278e88400000001dc0000000000026900002ccc000000070f2d6a0d3a0960002e9a00000005b75c080324000000000000031469ac800000024e6dedd3c2a0282f278a8000000000000000000000000a56400067620f10000b5e6b3291675483ecbee8000a70000000000005c940000000000de8c00000000004df0000000000021f80007e6000003f2ffe00000000000000d5a40005bf4000000000024359da5df8000d321e24de068ca757ac72ac2400000019d20000000000000025d80000003072000000068d40007dc015c00000000003020000000000020d248e800027623de0000000000000000000000001c900000d6282493ce7f6400000000000000000000000000000002fd1ab0000205d00021fd000000040429067721052d08a9e4000000000000009190000000000000000000002628000000079cc000000000006622920000dd21
  | 50 => 0x16aa4a3850400000002569da200023320002e361938d82a348000646000000028e48c5b10a00021380000000000000094b862c000297a12a057ea73161000010591af800000004da47e0000000000000000002f32ed8000000000000000001df10000000000000000000000000000b71800000000000160000000000000000005ac8f140000d3442daa3e000284ccb708acda557d60000000ad980000002e0100012e200000000001ebc0000000dbd14bdac3400063700004bc35dc615800000000000000000c21000000036fbb223528000148426482d480f0000000102700032bfad93769cc302ca00035225a200000000000de5e0548f1eed400000007338000c6b00007b04000b8dc000000247adac6ac6000000000000000000000000000000000000000cda0000000000000000037d7000000000022e50000dd08969ff40001e545959c6ecb92f2a7ee326e916a21f00000003df00006fcb7c20001744566a4cb2d727167aa800054d000000004bd0000000a2b9e6292e00008309a725d40000ddb5a40761e7b000028640000000000000000003a24218000b7a000086676b66322d8e4a2aa0a0000000000000000000000000000000000051f800000000000000000000249e0001e8000035fac52174cdb5000000000000002cc200003642a905280002ae01c28e4cc9528168ba8000499800024b000029623aacc6976cac5a39e12a936887301323af8000c46800000000000000000cb1254200000000b48000d6bb68600000005448000000000000000000002976110a2a4a71000058d80005b08000000308e0002dec745b18e2dc162146982667da0000000000033702201f7c0000000000b5d80002df8000914800091ec00000000000000aac86f54d078f8000000000000000000000000000000000000000000000000000000000005b48000ace0000000000084780001450000afa98d80000000000000055100008d1000000000000002bec00027d86a98598000000000000000c20000dba0361000000000000005a40f1200000004ed8000000077c85e00000a0105a51a000070a80000000000000000000000000000000b70071e0001674a358188750000000019272be223e000245e0002614785000000019ca0000f0e1d9800000000000000000913022c1eb178015088aa000144e0000c08c98aefe41a0000000351e298800086e62b5000000000023201438000507c00000000000000000c8e92a20000000656a6cc00015e876580000001a6400000000000d7600037ff0000000c8b80009661b22476c44a00000005288000000016a72132237cf8000000000000010929d4ae74821b0d806823c20002a8e0d837ea00004bc000101862d8000000000000011080000000000225300037ac00000002e80000000000000025a20000
  | 51 => 0x895200000000000000a050000875d8f200006ba0000000000000000000006bd3575014800000005b87aea59e2d326e800000000001ffa0000000e0216940001b8000027ee000319aafba297000000012d149c0002506b2392464409946835017200022ed4050000000096a10a0ece760c00016e80009d987e23c100000000000d5231d60001c3e10c882e8656c2200000000cc8000000361e000000000000001750000c4d000094eace2000000055ab7a1000000063e00000000aa00000ed800013743feaa102d200005fc8000bd800003f5000000000000001dc20000000c1b800000000000000000000189b0beb232000000098c800031f000025ea3140c426a686b1d0890f0000330247500028e600000000db80000000000000066200013f4000000000000003798e9600022e3000151ec43000000010ac0001ad400016702be8000a3c000000000000000000000000000000000000000000131c00000000000ee6000000000028059258000da531a6d119b16000000010c4000000000042700000000000873800053e80001e5800000001c2870c7ee270183c0000c9c8b0815600032c8799457c21083e43f99e8c00023d835e0c2eaaf351f7750000c74a7a40002267000035600018b2a2180000000f3265626b40f180006264278c0487c42b886b4a0c60e47bc8000483b7890000f34000000088100000000000c8d80003d20000000000000000000000000000000000000000000000a890000b7127f30000ef40001da400035da0001c9a00000000000000b4a1c7a0000000000000000029360000000129a8ab46c000000031d800013fb71a8000de61da0564846c83850711ee928cbabb2ec6dd800000000000000000ba904d80000bc49c000000000000000255c0001e4c00000000002c2aac9153177380000000a9494e1efc000000007c803e0001e46df44000c1d80007510000adf807c41500000002f780000000cf40000000113800000000000fbd5a0800014b238a00037f61ae00000002408dde4000000000097d194800000000000000182aa38cce000000015584eb5c18c2a00000000ed0829000079f800000000004fb2cb200000000000000c6487b1000032e0648000000000000009be0000000296800059e4000000000000000000002ce000000008b1800000000003f2c0000000000cc10000000158800000000001b9e000000000007b83ff11e8af10000000218c0000000327b13c0000000000299b000285c7cd2f10000000057f61c600000000001e2cdda8000000138a3c8a3b8883080084a8000cc280004f300000000000c5c00000fc8f5543f8a8a1b25a58bb580688ab0000836b2e6d561ce00000b022e18e9e0000000000000000000007e70000000000000000000000000000108700000000000000a3b8000c888000
  | 52 => 0x8280000a9600000000000000000004723b104932000000000c4800000001fec00000000000000c57aefc649000070ea7122598000124800000000000000000013c000ac007420000000000059e00000005461ffe3cdc97c5acce8a40f120c000152cc4b242e6ae89b223a015492ba1eb5f34e8c0000f18000189500000001ef113a00000000000c98d9a000060183b647f800000000000002a84000000036a800000000000002ad0af49faa000272a0f0a92c00019a2cf311d80000c01000295607f8000000000000000000000000000000000000006cf1f5eca2173c33894aa3342122ad09464703de050f698140000000a4f1d50a918000a11065210bb45067d80000000000000123c0001bdc00000500000000000208a0000000d82000000000000000000000000000028e00001120a9680000000bf04b0a38b10730263f3ac820bee2b80001b548ac971a79137f019612180001e0c02a80001d38000b2bf7d3d39a74a0a6cb724f5257b000362e52eaeaa5f2c55c00000003968c3a555000085bb7a200000000000000000000000000006f177651f580001cb0000a85aa4895410be5ec000000000009a58000000023c000000056780009058000c31892a00000000000000587800000000000000000000000000000005fb8c500002552000217d0000000795b4a400003ee0001a48242b44e5d0986452f81bc697131800021610ca80005821e690000000000039941900009f0722816c1f0a00015b8b560ad2000000000000008d60000000000052980009229b23000000000021ec00000000000000000000000000000002985dd79d8eaea9e1e5f250ce3e00000b3d000072c8000000000000000009ef40002b5154800000001318000b488000000020e217dbae0000c02d0c2800947a820d388c20000149000000000972a4e236b63a000000000016ae0000000386305eb10000000000000001b049f64000de3800087900000000b1c4ad80001ce000000000000002276a40948c0000946d4b0f64318904eca316647a50000a9f0b16d32aea0d99027b85bc28c00002600000964cf29c5600000002128000000000078c8000000000057b847800000000000000000000014300000000000d1b8b9086da76e0002f028e5000000000000000000708b052dc74efe40dac3698a4a242288cb600022c3000000000000000000000be5c000000000057ae6b6536aa509c1371400016cc00000000000000000000000000000002134000239d000000000000000000000000000045ba16d921510403c1c8500000000ea98a044f902a50d0000769f6463540000000000000000002e585aa23a8c3263e8f9000000004f9158e948b7020002dbe1af435a000353a000000000025260000000000152600013168d30000000000073c000000005d6c43
  | 53 => 0xcc000648ae984c6e05ad10a5daa78000000000000002adce00e00400003780000000ac0c0008b70000000000000016ec9a183ea4cb0000dec93d800031ce0000000062ded4000000000000000000df6c068000d920a2a76752aa0000000ad680000002e8400000000000000d0210770002df4cdc8000bd7c000293800057795c200000000000000a80800000000000000000b7235b49f1400094c93ee000281880598ff4d807aa27e8000a0cd18e6ec91224e90b4ed798b9200000009f880003d5a5d26ef8e1a00000000000000000375759f00000000000a62a27e11227440000000000122ea4aafe600000002bb0000000132a8d880000cd1f6489b40003ad80004680000000378f1e000e6000000000000000000382000335a641164a607931a79b16766d6000000000000000b6eccc0043866e9812f427de38a28302240000d09852a00021bc00000000000000290800000012a48a6e99a14910e46038988a74872bd228d7e7b4ae502a983fc85916cbb3c902c0001dd680d9f05000000000000006ba1ff64640fb000015030000fa2000000097a800068300000000000000000000000005c74000b8080000000000cd0a2c1434302a00008f6306b76000006a400006649de0000000000063f400000021fa0001e3c00019120000b9c86034d200031e0b89110aca0b32a2eb000000029578bc400000000008d91ddc0188000bde400054a0000aee00005bc400000024ea0002b4a16385fc8f20a761e6b53b37510de00000000000000000000000015d84e106aa000000000000000000000057c0000000000000000000000008fc800000036ca72f1e5806ca51c227027ca718c4a69f125a0000000cd9000018080008fd02320002f14c6404c434ab438ae10a706090000768503a24200000001b000000de4000000000000008a98000a8aadfc0000000a16114c000000000027cd4b30000000000000000006b209ee00034cc75580008c09e2e0000000000000000005f85a6a14a9fa33aa64e000000000009d08000cb8c000bad000013f2af0b8856efac1000020b284a59ac456b4e8000701800056a000000017d8582c000df29e68c15a80843caa74b9facfc97593c0a2680000000000cbe602c0000000cfa0000db980000002c0c00000001e980005b200000000000377163c000000000016550001de05040adc4e4589600033ce0da400038d34e0bc8800086f800099f9fce00000000000000bec7138000000000000008bd00000000000b56a5e10000000000000000024630000000bdf0000c7a300400017146d09e5a534c00000026ae9429a1e930b2667e5b308c62337d0000000bbb0000000256c6438d481480000dc907080001c78ba1800004e80000000e5e00001df0002125ccf80000003550ca8adce01740000002aea00000902db000
  | 54 => 0x20975d218a6000000026082220108d38000000000000009ee0000000000000000007b900004ab2b480001cbe2cda3857c400000000000aed80000001a609d69fc3be4824031eac5cb58800000000000000000ba00977cf7926238b52a000000000002a5e0002b1000010502c60000b304c68000000005100009ce00000000d2c00000002508c1e14f00267bd80007030000ca8000000000000000000000000000006d80000000b898000533000000028844bfc00018c9c60439a312dc200000000000000000000007b90001c9e00027e60000000bcf000000000007be80000000000dde800058640000000c9a00000000000000000000068e000020780009e580000002ea87a8a4a8000000000000000000000000000038c332204180000001ae4a1ab1b02bda28f345220268c8000000023000037590000000802f4d4000000000012c585c603a00031f846a0516dd1ae7f5b1020600003c87900000c2025c80000000000000000000000000000d178000aaa931291a99eae0519820000000b4200000000000151800000027e335d000000000000000000404840a553800030898b000000002d8000000000000e280000000000a7c400000000008f19b6c000068489b1ee800023b446a800055d8b1e0002b8800015600003310c0700004e30ccc00000000000000000288a0000c6479c80009458000000000000035c400025f68fa00000000390000000000033ec61b000000000006ef67100b5a9840000000b3b8000dc3000058b800000016b84458000a80c6940001f589ae800000014de000000000000008bd8000000000000018be00025f2adb80000001be400000000000000073000000000008de8386000001a7d38000732883ed471b625ad00000000000000000000030ca73997f000014390002980000282626100000000330248800000000005571f280000000b06835055b80000000000b7f800000027e9000000000000007bab66f86e80471182085417003230307c07e0046a000341200000006d8000000000000001ecb0003502000002e0000f9e0bb322ac410000000000000032c2335af38a278000000353900015f2b0a2b2c00010980001a4ea1c92700000ce6a0c8000000105e00000000000e68000328a00000005601d3a2830000000295eb3c2ad44ee96f68be9ff00bd000000000002fca262b392bf800020c4000000044716485c5a43e78700000000e000000000164000007f00008d5a2730000000b188000431144a31818d6d7bb5c07c527cc4acc00000000000001c5291f9bcc640c0000000000681c000000000095b80000ba000000000000000000c352bca4bd0000000214cdaba0e20000000746c00030500000a11e6e3f21f1853f00450001cf42f6b7803cbb76e31ba0dc83bb09066
  | 55 => 0x61ab110000000d1001e10000000c1a97780002b9093295e74b1188800000000001c5e00000000000000000000000000000000b88dbe771e000000079d8000000000000000000000000000000000000008de2fd81681eb091e271a61d8000000222c78e30ce0fa379a2a4804dc1d2f30cd12d7c00000006f980009f7dd8d000215e000000000000000003078000000054f4000000000000000007482d943b01a2a2e0000000018f09368000c4780000000000000000000000000000000000000000001020000000d9301a7000012e0000000000359800037b4b9e00000000000dbba068000332e0000000261c00000000009e311aea1c0df80000000b84400041084724b40000a44193c3e5f4f4ca0ed6e000326a23bcf6c0000df212182b3066c000000216900024f6cce800053880007f18000e04a05e00000007fa23d2b0c348e37a00000001f3c00000001ab328e662b7e2d4d000069d800000014264361562000199f01c1e2600018368d1c000c5f107400000002fe260000000000000000000000078580000001298a04b36263b80005bfc0002e90000179b4b2c5a800042b800038880002c68000000000008500001c8000009580000000000000000000000000000c4000037900000000dc880001a28000a99a9200000536000000001eb19862b000000000008a0080a000191a00036000b2000000000007ce80000000000d9ca4602c280003719808b4581ae019c000000000041f80009cb1428000273a000000082525880000000000182900014780000000591400000000000000000b24b1a8892ed5c60980001b88000000000088b8000c208000000129ce008000000120a0000000000111a00000001bd8a4443280000000d96000000000000005d66df6000000e9740abab760eca0080000bf19daf0001d76000208402990cc52ae21c00013a866c2e4e0000e600000000000163e00000001ba1ad80000724aeb8000000000064b800002f800000022e60000000dd4c6fccd1b6620968000bc200003528000c0000000002f9a00000000000000000000000000008683196c2d00000001f7200000005c0a4fa00000000000000db880000000000000000000000000000dfe10e9d0a0000000000000000000000000d020000000000328457200000001db645a139ebb800000000000000000000000003fd81aa0000000020c000b13000000022d9c2d8fae23d146baa5b6d2945000000000004ab8079a54926a0001f20000000000021065e50ec500010708114000000000059d5c1c00000007f54a1a48d800000000000001a849bb80007f2800000000000001ffba6c04180000000000000000000000001322002ad143fcb014b1f8000c828000d15869000000007b1534a00012b8bfb8fb200016bd9968000000000000000000000fe200000
  | 56 => 0x42e000000000000000001afc000056800030070000ac88fd8000cca00000000000355800000036540000000b8f9d2a000000000000000000000000000000000001fc0000000349000025c0668cd1e00000000000844000000000011a20000ae475600007ef00000000000c4b85e2417400000000000000000084818e1b7498aa1f14ac00000000000d660000000d3dac16000125200000000001c2e00000000000000000000036e2f70a630022bf2aaa2000165e00000003858000000000062b80000000d3a00022ca3990dbc00000000000000000000000000000000000000369d0002b07000000000000000000000d6dad44089e8715b500000001a68bf0a1c2000000000000000001a6c000059c000000079be1a8d2d13141aa01f6d45b5de000000000025e8455406c00000007bc00000000170d9a80000002b7424c35f4000000031695c4ac296ca00018043fc2f587eb8000adc06968c3f49a3d680000002a6e0001dc53950000000229e00038003308000a26ed1a0001c98000000000000009a0000060028de4ddc2aa826a0d6ce635e40002b8edd555eab8a6f7e195db887a7806ece1a9507710000cd0000046089360002e4100000000001a3000013860000f4400000005509ae04911e4a0000000000000032f210a13d36280000000bce800000000000000000000350a000000039f89d2c3e8000b4780000000000000000054adb5057deeac1328000dfb9aa400c0000000272e36980e04a00afe0000e6e257a1fb000000062e000072b40000001d60000000030d000000026370000592000009c0002c48bb086cd15c00005b61aec53100009c3abdeb99a9f093180b4d30b0ae00027ba000000077a4ca60000000000362c0000000000187b00000005fb00b0000000000000000000e2e0000000000000000002b200000002de000000000000000875d368000000134c00034f20000c8498eec7aca6238757440007a90e6a4c397e4000325ac2990d2561ad8400003767e807840002166000182c0000000c13c00060d00000001d5a0002b0e6f60f16591a8a25c83524829a29ad27a564bca1e903dc1324017217c1c3dbce32e16fe3960be493b9874c196074a37000000000004d4000000014966228a6ccf5268c015332400009b60002270d7edc4c3c02cb001a40000000000c56000042ab458682971c64b0000250011a000065900015e35fa8000a4c02702da00000001354000232d0001fcfa0db71b000187805d709200036a8000009a30380000000000000000000022403fbc00000012e60000000000000000022ce000000000000b2d0c85a200015cf26c0000cef8000289a02e0001fee0000000000000059880000002dde00000009d58000c8b046200006a60000000000000000000000000000000000000008182d8b1b81e41b922
  | 57 => 0x2c04000000088c2f6aa6a8000c1a2b781d42ce89e11f1390cae5c91b9ee53bfd19c0000ea8c89a80200006807b883061b78000b498000c688dc25e828c63a612d414c0000000365c00007d80000000317a38f0000000c031d7b0000000000381aa8794547e2800000006e400015a4800800000013282d75b12a82153e00000000000000000000034a000000000001be19870000000000000000000000000000854400000000009a800000000fade0113d6854c000a8003e600000000002b560000000000373200008ca000375c28b088e8c600000002d60005af80aa509256b40d534a0cfdccb5aaac57405c600035a000000000cf317628d0000123926d00022e9000000089bf7770000000dc4124c6cc00000000000000000000028ec0000692000031e000253c43a0000000000001180000a8000045e800000000000000000000000000000000000f3c00020620b72810cb8800070122b6ce500000000000000287e00000004ae800000000001ceb2f8d618000ddf8653000350e6615336000000083b00000002a86000008800028fc4960000000329a964000047c000055c81d29270000322000047415ffc8e0000d3b9be80000000a51372eda7000000000002af27b974d28b6477a0700001bd41baac1400020b800a2e685738a1cd313264000000000026b8512c00000037d0b852f3421387281bf8bc20000000000009600000000001ed800000004e389f6000000007884bfc5facd49fc8000000000000000000000000424280c00000000000b0400020e3b2880003e080000002df20000000ba76dac545293a0001bf0000234051d0078572abfca3eae208f920ef0000000000262000008ec00000000a78f2a4c99d28000226975b36040000000dce8000de34000158865a00028468538000000042220ac00000000000000000000000000009540000000c4400008bc80000001f5062100000000000000216c55e65ec0000000000147189556270000000000000000021860002f2cb9680009ed2af80000000518a8d890b000090188660001cc600000005d5000006ff3a00000000000000000000000000000c6d000056fb3ee900085a299196edb32e28a90000075900000000e92000168100000000002e3200013d2d0d27fe00017311ec841fab2861800000003610d610002319a260bee00000000002b720000000000000021b000000031cc00023555e08000000000045e00004610b3a00021b200000000001d72000307c4546674000000071b604600000000000000dc06ef000000004314000000000000000000000000000000000000002ac8000000144c79413236548000000000000000000000396000000000000000001d15ddec0000000a7e0001c54000000095d00001a300000001a13000000000008e70001b7e00000000003
  | 58 => 0x800051dc0005a19c4e2ab8000000227b8044000627000000002da00036f7000000000000003b0c0000000000b5280005a95cee0d22a5425d000017c0000000000027e00000000000000000000006460002d4e0003154dd4593a767c000c313744c928000516d9fa00034166770e6200008d40c900003e680000000da4b168000a180000000000000000000001f7ab7280006aa95ef00000003f540000001b72c55c00047800008d14000000000037e800055b000000000000000000000199aca6e2ee24e00000c516b00000000935191000000003a900005c98000173a1df00000006a0b544000000000000007a15bc20001626568c000000000013b00004b5af8a0e100004c5489e0002384c3a224a52e0000b258000df9558438e2ca60002d04000000000014807dda2911f324fd82f0000000000037c22af000381b0528000000208067d1914000069e000000069fa29c47380000000000000298299e3596a581b960002fb400000004032060000000085500000000000000000013f853f000000078080000000000000000042a000000014e6000000092380001730c2c1b98000361800000000000000000000000000000005393036a7f34d08e0400000000000001c2800006fa00000000000000081000000000000001300df800000000000065116c0002fd01ea0000ab30000000158100000000000cca0000000a6f1a54000000074b8180ae71e0b51100003e18000000285e0002ece66000009008000699b5d800000006f400009eb10a600027765e180000000000746b7da6082c66000000000000004fcacd0c38000000004400000000000000065e81d4457a58adc2800000000000002a016b0337068b8000000269400023ccce896a00000000a1a000000000003bc00003a0b478c3737400002dd4caa23424ac95949b780da1e0eff469e57c51c95bb6c87000000004cc0000000000000000025de00000000000c726a05f1c4eab57d4870000dc0000000000009e980000000000000327b2558c2800003a000000007342050b138000c592db80002cd893021969842560ac20452217a45465f8000b9f1dcc0000000858d766d73ad82996358e718454c3e807f3390208cbfca1d615008d58422b60766a65c78000002a680007c1157308ea8488993578b0223ea0000000000295c00000000001ba4000311700016720000000116000000000008670000322b0bc00005100dc0000000000050dc1819e6400072b33206e280008ac1f600fe112a2a300000000000000000000000000002c0e22f800065300002ca94721ae6fea00000000f500004650000000044e990327a0000000d24800000000000000000000000000000000003811bfd800009840006c1b5b000006500000000000000000015d25d68000000000001aab9aa6867e0d9d4000
  | 59 => 0x2075ad8000008b24abe5761d8000000000006b9b7ef00000000000000000200c00019cc000000000026fe5bd400000000000000000000000000000000000000da98259c1995e1c4b40009078bae5f8343a000000000000009120000000000000000000000dee00000008cb8000b824000576800000000008d251e47078000c7e8000000108200029e8000000066ca90e987000024d064898f3022d730000d9f00000001de2c3b00000000000cb3098c0000000dea80009a080001e600000002058000000000007dc91a20445fd16be000000057559285f1b1247c371a4a4501840000ed40000fa8000238683a8000659800000019f00000000000027f00000004ce11d600000000000000797c00021a0000dbb0000000000000007b510f84f213d8000000297900000004b49dee000000000018867160000000363c0002df000000000000000a9da99c0002c1e00085b600036500000000a72a220d0db0ac00000000000000cc03738d2c000000000000000000000148ed06a1924c26f44dd9000000003e23d5f6fa00000000002ec4c6700009c5352ada4ae88a490fb8dda194041c84de000207a6ea0000ba58000000000000000000000dea00000000000000000270a156800000000000000000000000056d0bbcb5400000000000d5580000000000cc600000001fb4bdd015a9288000c8228dd00000003d49fbaa651db447a781d0001b4e0001c0000000000000d0019e8d6494a8000000000026d1e0a00000000000000000285a00000000000bd20000000c43641c00000000003240bc100006a38000000000017d8feb0000000000000000000000000000000243a00013420909af20001a62000157e3bd891400030022f70000da2086e00016b50003292d19108c5218f080000000000230a000204e0000000000000000026c0000227d00000002080c7400000000002a7e000000006b00000350000000000021e800000000000000000000173f00000008699b0a7478292b6c8000b648000000000000000000000b6a00000002468000000000066d2d9600000004012498000303000000006d1a9a60002880a350000590c000000279eb5c8000000000099100005e736790000a50003000076b80000ef0000000295800000003560000bd3367000036e0a100bc8000000000000007230a046f1a4e2cf59e28bb29400bc181b6000093200000000000000000000000000000000000ae780000002da20000000495a03455400000eb80000000f886631f6e4e88000be5126800000001c883e00000e0a0000e7833f00000000000000000000009fc9f0b21400000008190000c718000000000000000000000f3e0000000000001c00000001498e97000000000020fc22180000000da2a5d11170001c48c0a00002100000000278800000000000000478
  | 60 => 0xa85b25a5a806841db1a00000000000000000000000021245ab00003d396d1809ab0cc3f800000000000002604a2080000000000000000000000000000000981aba60000000000000000000001ec0000000000000000004588aaa00000000001d8c01300007d70000000000000000000000000000177a46000000001ebe71f1a5ad6f800058c35e80cea73ca9ab4e4000296a0000000d40141e04d21b43208d8c00000000002b7a3acaae66b70000a3e000005f8000000000000019cede31bda401800000000000000000cfe34020001c0e03313b23e9d6296c8011eaff800021e0ab46e180003abb2b4aae2e900001eec000011296b13ae77f9ac1bd20173a9e380113880004e4133f740b69a000126cc7682027b7b57cd0a0000000000000012e50000000b5b1f020000000000000000024620002dda000066c0000000000000000018b4bdbb11c0001ece0000000000326c2c9a64c0003590c2e00009f43526d99a825000000000000000001bba1cf0006a448d06d6f00000000000d0600002838ce800000005c6356e0000a66af9aaf40000000000000000024e7de280000000000a2640003d319502e780007948000000000000000000001110522772652800000002d06665800016180000000354bea800000000000000000000000058e400083f9b56000124d0000000b9500009f6f73480029d02ff371cce68000b6180004e02782000102800033b800000002c3b04c0001578000000000011cab3200000002e48a238d0a12f9e838b321b7000140a95f9bfcba50000ddd26f00000000953886a156137e257168003540fa00020124465e64e0631318741d795ffb09c0000000032a1365b41ac4874ad182a19fb20000288b6ea4ec7ec03529fe2444000000000000005c300000000000000000000000000002f7600000000003172000000029a000000026506ca1de445f800015c400000022d6a56b47a6820b2c61c000007b00001878000000000000000000000000886a536e024000b3109a000008a6000000057d4000a02400000000000001500d9e374b165927e000000057300007571dac00000005d02c0033da1b0377800000005dc6d4c00000000000001ecc00000000002f8400000006ec4000000000000031e699525b600037176a180000002bb40003248000024a2ac18e284a32108e35dde8bec00059987704569c74304b0325f8800034300000000000d78b6b50002cae000000026630f4000000000000000002f980b0000084e8000000009e00008ce52935ac556875a00021b819aa8fe000000000000000000000000357305000b634582860000000652904047d80000002b4b00000001ddaf666365a730000000deee20b000000000019420000eb0000000012028e253b82e60002b184b2012ade1d6fc2b7b7e899a00007d6b71
  | 61 => 0xa59bf00007140000d58194e00000003eaafa6d5891640002052000217bab6000032b000000000000000000cf985614a7a8cc924848200000000002f2400022590002216924c000000000000015a63ae000000000003f40000aee980a8fb1e4800034a0dbaa7d70000000b098000d2a00000000000cecb058d808ac29f38f7460ae22a000000067922720000000000000000000000000000d8f8916000000000036cd0000b4ab691e6a7b1ae1798d946e600800090600000000000000230e0000efd00027900002ebc000379600025d4c60a37020a8b0600026340f580008dba19a7c59402ddf00009fee198041c000000228a80700000002bb228d44960002d4067580000000000000000000033484120000dfd01be0410a9e53580000000000c9d0a9c3545fd443ba7cba9ac0005dc465c0000e360002c54946000084380008fe0000c63148700009c40000000aa60000b5180008d480006c0b1f00000000aac361800033788939ec80001d7a0001bfa18e0000c48800000000000000410c600000000000000000000000000000000000000003ba0b420000000aaf800000010f8190339e3ca1f62b2a13347b8184ca870eeca0ba24459dc0000000837b4f1e1a00000000002966000206662a800000026dc000000000031f6a6b000094026e0000312a00005020000000000000064327fd42f0000013800000000000000000247000000000006044000000000000000002b8000000031e45fff2b207bb752363833e6bb80000000000000000097fa028ae800004180000000347c0002a69000000035000004f1863a85ad8a4000000000012b70000000000000085d9b5c00006b500026c40e980000000000a6800983a18000c3a80007ff209800002a28e3ae0b02ac0003b2000079e8b2829b9c4600000007980000c4600001e49c32a575db2cf80000000144119080006b08000aa0196800000007ac65100002b460001fa808d8000000000005a000000018c474e1c5c99280005f1c00000000000001be08d64cd80000000000000097e0fe9bac19360002e8e089292e6da991c00022a800015b200000000002aa000000000000000c9396980002ab200000002510000000000000000005da1d9c0000251d9d0000000000000000000000000000000000031620f4800054888120000000000000046d81367aa005725f80008b6044b00000000000000da3000000012e80000000c340000000000000000002ed80005b180005ca95361b040000000000000327fbd081208df4000caa8000a4f80000001cd475200000001e6b3738000000030c9cd96bca554000a58800000000000000000000000015597a2000000034f000066b000000032e04b29752429131e4fd9908716af1a0000000000310651b018dab100937a0a4d800031aa0000000000000077
  | 62 => 0xcd8f5454800000000000000261a0000000000000041e24d2000000000000001f3c000000000000019c8abf8000000000067800000002a427ad968e000086000000000000000e0800000001b2f000160000028ba989a4b000035f047b42588128000612893e8754e4400000000388000000220300000000fc14525c91a020002b26000000000022055640b983a83306000000000000000000000bbe2dd03fb8000000000016d12736268b744f7000022e41ea13a3008b10a07251014ca76a80d600001080000000000354c2802a62929047609400000002b8a8aa8000436454e000000000000009789dd094e7644624a36c3e300009c18582bc70ffd5fd9c7215e2a890001dbc00027a00000000b0d1d94dcb03c09a6142dc4bcedc0ef870400012e10000000465a35ca0b75f24880711cc3a31e97b800082d2a0b5a300007200000000000000037670000b100000000000000046f858400022ad000000000000004548000d3780002ee8fe1889800057b400000000008238772000112479c2a150000000b7bb45200016ea2b380006262c60a140d4472d400000021f0c72119e000000048032d06d2b7fd342063e0580e31a888000000075c3ce05748d3885c00020a200026c80b4358cd71400000009180000000000000000017b400000eb0000000952b7f5000000047729e6000000000013e20000de26d48bc60000000000000000037620000cde0000000000356600019e52f5800000003720000000c464000b94a5a8000168a00028a08e8800060c20be4cf8000172000000000001ea43fed6512085370000df5a8bc00000000000000b7583282d990227f9000000000008688326d2f0fe8000000052140000002953dabe5fc13007936b6896067c8080a86af0e7eb0f46071b1410003206b52000000036f00000f3a0000000cea000094a000000012f7a4a00000000000776d3b028f225400000000001210158225666a80007daab1c906800053c0000000000039080000000000decc000970800000000001de0000000000000000000002f8c00018fb7fc69c867f802c00000000000000000263000000000000ae8c91800000027bf00000004d78000078338ad519fa21d8a274000373c0003356000004a0002d7a21336ff000316800000009378000000000047b898e00004eae078000000000000000000002cbd5f50000000000033c80000001ed00000fb39e503686e6b7c60000488000000085800003b92412785639c3e522ebce3000000000000002db4520a333000000000006a046304b80640000000302ca990ad625b1fde753a77210ac000000281a000000000000000000000522b1509d30000000000000000003c4000000000003dc5cf263e5d88c5e05e8000076a3dd98448921c76d3a8000000000000000001fe20ac000000059637
  | 63 => 0x8d7ab6c00027220000000b2d237100000000001b0c06776320ad9eda2f63294ddb0cf8c56a80409aa60c000099a0000fda7e0b6cbddd742458b00008be27ef00000000001c7092c80000000f9600000000000000423a33e00000000000dec00002380000000000000000022f5762800000000001a24000c4980000000000000000000000004b62dd24259c6299820ae7d1374c00000007a800000000e3c000095d00025e43970b44000338e00000000000000000000094c1b14ae9000000036b2d4c8000a20629900000000000000cae1fc443802cb951b64e0000000100248c0000c060000000000000050cc00000000000741c926a280000000000000000000000000000000611800085200000002a200000000000000015c8000c4c0000cec00002ba800000000000000000504c000c42000000000000000000000000000000000000000a430282c111ee607131149fb4a90000173300012fe50f8994000000044c00000000f6a48f91480000000000000000000000000000000000000035124bcdf4c0000000b8e800000000000000000ad300008ca8000000000043694f40000000ac834ae1839056000000000000000000000dde000000000000000cd2cae402a000000000023d60000000000000000005520000000000000000034be000284e0000000000000000000001ca42183f4a2b4cbc89ca00005c444b800000031605ce2cc012ec000c4cae56499d89e00000006170000000000000000000000000d35ac3c00000000000000000000000017040000000cf1817c08e4000a079dc6087b6c300010a200000000003506a2900000000000000000000032f4000000000014cbd3c2fa8bbd56dc5468000000000093a14480df800096d24ac00018f500032f07640000000000096eb0e433d2b4000000000000446b66986e00026f4000329e00000000000774000152e000000007000a45680436000000000000000000000000000099b800000000000000000abb00002b600008411f0e02f24f02014ff4586a82423f00001d7969900008ba0000000cdb8bbed78212144d800000025960002bd4bd418f4a0f0efca2319be0000dac5c21dd20ad1d6e72d80005c01964aad8000000003a31100000001604a6d80000ae400000000000000276d2333528d740009978d100000000000196a4dda40c87200000000902000000000029a87c27736000000000000000000000233296448b000000000006c8515c63689cc78189ac00007b6000052e8ff1af000000000002b5849818e641f000095798bc00000009d200007c68f5cdd0800076e228cb8300000000000934330200015c3000269200000000002908000000070800006ad00006881697c1208d700022685ea400058d0000000000000000000000f6e00019884c180000001b386
  | 64 => 0x4d02894d080000000308600009dc000128100005669fc52a3709345a7c1d47633aa1f64cc18bb00024fc628941c22900000a5c000000233800000000003690000183e0000000000000000000000001f9a511a37fb978000a6bee3cb4020ba9cd1f222850d3600014067e79e662d02b503ae80000001a9e7be00005e200ac125042a00018225ae80009c600002438000b9d8138000139a00000000001ca000025f04b71443000000000035a20000000b1498d2a50000000000000002616c80902478496a2000000051c1f3000000c3048814600028ea60681867d4902130921ca2b69e780000000845b14ac72a1008029d7e6d00000d45d3da133b2bc963abc68a886cc20d8000516a0de0001cd85a700003e9378b2c814b000000003b10be0d8800006f5ad3400035fe14e0c6a0000a20000000000000000000000ca0003c5c1a0900000000d0333fa000360a00000007d9800059b0d12685008e00008020000000000195489e9ea651f000000000748d527201b4800052c800000000a200000004e218c200010f02ae32be000000000000006a624ce07e800000002a8cf6800002e8000000380dd5c8000000000087c400043000000002582d37000091f000000000003041c648ff8000000219720500000000d46dc1271cc6d8000a7c91ea00002088ef1e420000000000000000006554560000cfd248262a000000000004dd57a80000aa2d18ae5800021de0000000bac800000000000000000000053e000231a0001564000371a4a4a1f221d19e80000000000191600000000002fa419e000006680006d10000616268e84f800026a0000bcba59a0001dd891606bb10b000000000008efa878243000000034fe00021f4000000047f13c32d580002222cf80002156cf600000000000db21c66531b1520d70000000319e9d896020001bfe55f27b5000000091d00000d78000acf8000909a11cc0f0000000000000021dc61a0000000279a10d5a3a0000000000235aacfcda0280800009b00008a75d7400019004ad00000000000c3c0bb000013640000000000379b886103800100001acb7f200023c057524a0a76800000000004db0000000223fdd277d8000167e000332c00000000000cae00000000000c0a000000000003422cfa9f5bf70000b3980000000000000000069b800000000000000000dc550b0cae8000000179f7470000000000000034864098000bd000003a5000019c8152a2589ea6e300005d8708cb9ba0fa4e980006e988d2dbf0000948021c6c200000002480cd7800038980003ce5760903ac5067e00008970000ddc828a0000ad0a02c000000357a000000000022e40000000000000000000004431d3c000000000000000000000000324c000232c00000000000000c6e8c800000000acd00000000
  | 65 => 0xbcea49a15a8c937f1712a1470001cba00000000000000450c000415f2a46adb1b200000000db09780002f20000000000000008468000cbb8000bbb9cb1b66c0001f6c0000000f9cc2f8000bae000046c822e00000007ad0c5c157f3c9d46b3a600004b015400000000000000000000000000000000ab382a6bf5276874006ae000346600000000000000000000000000003cc00000000b24000124800000000000000420db68000000000025a60003244d5aa754cd50000d50800000000000000000be657c40001552a4e00008061cfc000216800000009274000065a3fa3758000000240a5f0a83b8825cb883a13bc943181c00021fe57940842a235aa69a89e48e4d42423f800000018ccbad80000000000000005ad3b00000000000000000000000000001a78b7800001460000000000000027463a38000000369e0000a6a6150000bb1a39100011b80d134a200000001880000d20067c00031747e9000069c34f820180000000000b6719e30002a9c82c0000c1416f299c37ed721913400000000000000000000000011475e5800000004470000000016f4aa42c82e0da6145e9b50fb74e5800000026d87b54000000186aa1480000002a5cafa0000678a422147800000023f000021ef589317a479d622000236ba0b1b34dc2524264a800008f975c38b34b64879a188e24fc2508a7a2b578000d75940c0002f32000000000003c47f21e2200000001470ca87320000bb4221e0048000a4282851c32f1835311ec75c04980d888a3a7f87406a7153865d2140c94088a00000000000000000000000000000001c020208000000000065c0000a930d1aa6382b8b159d78b9cac0245d86db24100003b8800000000000001cd203900000000a31000000000016a700000004e718ec00034981c5800068998d09da8ed69fc0000000050aa3c88626c381f40001ef4069a8e822d0a3600000000000000000222879c59a0000114e00000000000000000249a885d4737ae00000000000000000072700003890000aeb125c35780000000000c1e8b00b2e0e70000244e00012a6583ccaa0000059afc27508e80000281b4ba51bd6282d68000000000095a80000001bb005e45ca00000000000000000000043d0000324133c000000000015e4000000018ab80e03189243bea5c60000000da000000000000000032c18b94123e2eedab929dbb00030a43059c8a516524bb3f8000000080c0000000dcf93ea994a968387a78a0000928399a07800000000002a0cb1c00000002bfa0000000000000000000007f800004aae353000000088eb31c481800011bb55c3d61346000000000000004718f4000006748b8800000009da000114000029f800000000003682a369af8000000000000000002cec00000000000000b0b00007acb0e6000000000000000000a08
  | 66 => 0x52c537ce00000000000e848a0dec70000b326571df4c8f80000000c330001392000000000000000000000000372d0000b52005000000023ca0000000000000000000000000000402000000009700001f840020000000000009f81eb1764000c3ca4c441d9150a33aef600000d734730aa23d77c871a1a920001d97099c6d454418ba3410698becaaf2c3e03748b3f5b2b6c34940d00a5200000001f915a21f6a42f0001e98bfe9ecad42199e3339ade20c2022a98110e00000003158000000000000000000002e6439d0000541800000034824fa174b00000005c3a2ec19a190a0001094000000000000001f80000205a334596860c0ea00006c400000002932c7b000000001f800006100000000c7507ea00036e40000000000000000029ab000170a20e8a0ac3680000001b90c2e80000001f1e65c8000000000000015d7dca9aa83c700000003070dafd0e2d3a00005c8ade24d880364fc02af0001bea52600000000000a5cb67e0000000169800000006664038e7aa1d400000005fa6240000000000000000006e112889fa8000000000000026acc118e200000b5899d98e4000138949528220001c3868f800000037bf0000000000000000000000000000000000080caf680000000de4c00000006700000000000296e0000000803b4a600000000000a7c4118580411375ad7aabda61866e26e3b08a576ef569df800087a1c6c00035144373242ba640000000000000108803480000000000969048a0000000bc78594810b65e1b0d1da000000099b37f70002b2200014f6000030e000000024000000002ac8b8d24c80002a11455ad6800021bf8eb0fa11321ace56eae12b1d13e66ab04084dcb1f2df86584623b7588ec80000000000a256298a67c000c6bb13a00030c80000000000000074100005cc044498e2c466c989f48519ec400008b8464ac4400000000002e6a0000000d318faf00036d00000000000233600000000002508b6600000002b360001c8ea2e063409a1926000000000024ba0001b78000055e44505640b3cc303c180000000000000000000023c4d1a80000000a300002dcc2de981b01d800000036da26b8000b6f000086d4000466a512ba31df20000eaa000176fa9b000000000000000000e01e7707c933c80000fb40001fd6d1500000000be23f91dbe5411d800000ab60000000000000000000d01a88c967f31fd0000303e9988000b82000000035f6a65800000000000000b940001d7c941000000000000002b67cc4961691a629016f19608e480004b39af6000060400003f6bc2800000018ea19b80000000d9e0000e500000876ccf2f5e832936626000000000000b988000562800057f0000000000066f000069d25620000b0864d000000000000000000000212faf08000dea14e0000000074d8000dff8000000
  | 67 => 0xcb6284204a02440000000a05e4700000000aa280001bd00000000000000318a14180000000000c30800076a026ecfc6438db4db1e8dd34681c49cec7e1b0400ae800000028a600000000003088a41000000018130000000000331400000001b4000000020cc000150caca33661d10000cdf320e600400000000008af0e2a2b014670000a720000000a6231a0690abc800000000ed0000000000006700008a0a16200010620ee07c2000000000000000000000000000000019ba20380006ab80005cb00000000118000000000000000002ff8a91325c72bc44c69e85fec7728741d2aaa40002b6aae180008e0f13e0000000000000035a9e0800000000000000ad4800000014c09170baa1f480001bb10238ee97b6a3d8388000084700018c600023503218000a198a4a00000000000000000077e36c0700b4c00000000000ae323a4a24800000000000000000000000000000005e8453abb70000000000098b2eba0898fe02d50000615c000cd62f720000000000176a00000000002c9900000000002a26000000000029ec0000ffe000000067500000000000000071870517a656b8000aceab820001d32311ade6584b54a00000000000f8a000000000000000002a325d88000000072e00017e6cc980000002190cf71a283f0c31c0000000616b3160000000000000039840000c815f818940000001d2c78c16318c540000001a246f280007d500003dc800000000000000a102a5a69c5e9000042e8d927d029b400000000400000d3600002d93540000000086a926900000003d40000000073400000005e40000c70000025b80004ff34708c700000000000000034a3620000bd682eabc5800000000000fd000038c8000000015e000279c00000000000f8f00000004ef8b38000000084b0d7c000000060c8000b280000000000000000000000000d53a9fb01f400000007f29f7000030f00007b00000000000000011ba0000000166ad20237327000012c616ba33d00009fe41ea9a200000004a08000db000004941edc50802908bf12fad5b10840000000af920880339f0088de7c62521772d9080003148000d9ba1e03af000000032290906200000000067b0000095238000000001b3800000000007dd12141cab592000141500008e200028b20002e1e5d926e40f637c0ce916dad4e11d45901ca6ab582c60000ea2c078000000277483d800013e80400000000000358219f97ef000094e00031de20201a30000000000241428580008c9a17000000000002862000000009480000000bb41910000b4bb4767cc800000000000000000000000000036b085e80009b48000000000039b77ec00000000000000000000000000004f28000000000000001a8cf89bf40002f6c0000000000000000000000001cde000135800000000000000000379
  | 68 => 0xd13ad093a13923608da46c200000000000000000000000000008e22da8d54c00000026ec3e987ec0000000000000072b80000000000000000020f000000010750000000cd400000000cd463a00000001d14c980000000255444f400077c000000000000001755000010e000000000000007330000000155ed50501a7f8838c00000003b6958300000009ff00000000000000300a1341d3043070cc50d8794000000000007c800031c2360000000000510000d420000000000238c000000000000000002e310000000dd280002bc800000000004b7800088c80000000000000036b0001b829eee1fcb9eacaa3faa57a00000000000fbe00003cc031d02e0000000b91000000000004ed136e01fc000000000000000000000000b90000000013ac8c4034603b0ec60001ce800000000000000b3e80009f48000a530d700001f4a000267c86200000000ecc55d00000000000000000000035640001b7a3e480000000c1c2249f9400000008e6c00000007142f02d2c0000000cbfc8f0267940eb200000620ae1800013080de8000000199850b2f8845f00000000000000000000004a20000a1d5f7a373b591a1ac0b810c0a3901670b19860000624be3c0000bc35f73e1ea8c17c82e500000f60000000000347260488981a080000000000de7c0002978000000000087000006f78000000000000000009a91caa0000000000000071fa9ce00000000001ecd0000000418c00000000000000000000000000000000000acc00020b600028d081f800000020290000000d6a22960c7646c00000000001e3433900001e70000000000012700000001cea0000000000075682a0bf6852c000426a2f000036120000000b1f04c1dbf9f360a5aaa6000213ca36c0000002da6a6e1aa000019d000026085a1000000000000060ba8000016e00015400000466000198410100000000000a75a2604f04000d72b7eb1f387a20000000000005f0918000a3d00000000000dab47de738816f2d94000000157a0000e46add800097331ea2b9800000000003a6b41c00000000000000d5f800023582bc1e5c0000000000000000000000000564000000000003d0000000000000022942e6800000000000000000a7d8000000301000000004008000000223600017aa0000000dec40000000000000000000000009438a120000b7600000000bf19b800000006fd800053a000000020dfc1388a07a5b4104d6949a4280000be1a25eb2ea1c1bf3854400021f9d2e2e6c0000210d7f0c4c3a70a07b88b06443d800000018380000000365000000013f800033c0000000000002ee0000000000000043090d60000000000013ec2607fe0000000000000000000000000000de5000000000000768414431afbc0000000000000048c079900006e0dae80000000000cfa8000000000000
  | 69 => 0x20d23b30be0dc8dbd80000002d9e17b00000003094de1266600026b00001e7c0000000dd40000446d6421f50484519a6aa8b14a784cbe2f99c322789eded8c63da6fab2306c000016a80002025815ad7e7b5973a0000000b211285be8800000000000000000bf5aa184d48fd66510bfabcf8000000346c8f3895baf7340a00030fc47ca61e000069f00007af1928864d961920522000098935c20001154000000090c573221228c0cb7881ad67a2d100025580002a920001a4c1c6953a000000000012320000000685800000000000001fea9be00004be00004889816a09c8de0000000b7a87c600000000000000c830000b8b80007a38000000000000000003010000000169d0000000b2b000000000000000b0cdfe996c769a2b125280001f94f6000019a4ae6000000001c87f700009d70a91d4623b70ac32902b19aca587294600000000000000650698b1cda95400000000eb09ba64c24dc00000006641d6a761800000000004bae2d40000000000000000000000ec939828f56067c480004f79652103b111ac51bb8a0395a158614ec000000028a0000da12174ddc40001741fd81ad9b32000245600000004cb800021c09d0000363058cafb00000630c1292900003510000000057fa436bb90c584e140ea4a97383cd800000000000000000076080000001d060000000000000000000000000000000000027b000000000000001dcf00000008b9f57405200009b980006380000e0300000002b57000287661cb59a1f75e9ad4fa4f4daccf0a7c32ea6380a5440590000000000000007b4cc780000000000239008600012ea83d2d0c4662fd20000416000000000017e3000000000000000002252aa680004811cb400000008b105ea356a040768c9500000000860482200033c2000013c1edc0000000000000206a9808cfa0c4b7e482c8000af800006a50000000000000000001f98000000000000000000001275840973431e4a7a000000020c800004980000001756c4554420000e567509cc224bafef15b4a3300017cc000000000000002dfc000d71ac760000000806c0008b4b8160190000000000000000000000000d62ae0a000181800036961820dbeaa2364a0000000000283a000106a5e2b5888dc82ce9391bac0000f7edf78b828919f8c863969236280005f84eee841442000000009f10000c890000552a48400000005719066000000000037a05e6a7a800000000000000c9f9798288c000dfe016200023b06704000b1280000002f26df5000000032040000000a522ea20000000da90000000000052f0000000000000000009fd000000000008a1800000000000000000000000000000000002ac0df48000000000000000000002ca4135000000000000002b4900000000000cc84498a460000000973a7c07c18f
  | 70 => 0x9ee0002ae80003810d4455f40002f8900005a80000000000000049e8b3c000262200028541d48000cb3843cbc32aee6180000929839200000000003276000000000027ae000000047200001fd8000000372b38485e4000000000000001e7840cad121672514000000000042e4000000000068400000000000751b53f0000000176000094d0000d9694565f480000001174d7b0000000000012686da0000000a5c004900000008e60000000000000033f09265f7c000000000000000001e5e9b3800096f8a3800000003538000bd88000c4d8000b160000d6e89a20000000dc62361d6e0000000228e000226b22680004bf0000000000000006bf00027d50000e042f7848c00000000000000df9e1f80003273c531a4466b96f8d870d54000073286ec00000030389a2000028789964510000bd1a87fb6d80000000000731000000000005c252bed5fd64c4418000e07162a00037fc000325eb859d3e189800001c56605782b7f36d30b2cbf6c6c8dd5fd2c6100005f400000000000dca02f600000000000000b8b000000000000000000000189d00000000002a1212b000090d22c00000000000000000000005d8e94a0002453cab6cdc000000000024eb6d68000000000000000000001f5600007a4d0b0000000056c0000000c3b8000b930000000213200000003239c0db86a0dd71940000000b2e000000000000002af8000b3490939156266d220f27000197800000000000000000178e030b504c2788e000000000002ec881fc4d6db180000000000d18133511c00000002b3c0000000535400000000000000000000000048d2348000360e000000025300000001d6b000000000031c478d8fc439380000000000000271e3c04000ca180000002c2e27180001a70000474865e00000003e600001d1800000037630000000a1ba26e40800002e10000dbc80000d30c48bf88000000000027200000002b1a0000000c1b00001f28394619a43f8d7c00066980008e98000cba81ce57667be0000000000220600015300000000a0040006b8a06e000000084c4f2c000319400036a09958000422800042b747e0b90000d4d800000000000000000000000000025860000000000000000000002da620ec7f25480b603d000028c85ec8cee000000028deb2a3a22e00155166800d0dfcc4ac000ba2914f000379100027dd90901de14200009f200d8000000033c0000547379900033b453615560000a320002900c0900000d9744a000277a60b8c2684632d100021da22f40000a60000000000000016ce719d52a00000000000000000000074480000000000244000000000002c880000000000c8491ac00000009ed80000428000879b15cc7fae460000000940800000000000000c6c2d4073013e04a400031d0950000000007e8c4580001d30000000217f0
  | 71 => 0x175ebe0ca22092253e00000000000000d078000000000000000000d98912349000000000002972494d4b800089f2a06584436a000000000037ccd8a814c7861bb5ac142be3292646000374e000224282a80000000000000000000000000000000000179e0000000000000000000000000ed27028000000315600032a6db74000ad700006a580004f10000000178c4798182b550000c86800000000000000380de9a6ea885291a06297ba00000002a000007dfa9982258000867b4fc0002e1c00000007fac00000000000001c30000000081d800000029ea0000000000260e00020c613c0b8c9780000432211287600000000000000174e48480003de800095f22fd0001ba0c1886120002fbe1018000000221200015aa4d100008571ac375c40000003142000000000000000000000000000050c5f488cf12ddafd9cfe000091e000000000000000000000000123806d2288afc80000000000c1ac00041f55248208000a5080001bc8000c1080005a78000505000000036c40000000972a64e0001736a7600000001d5400000000000000000000000007a00000a3ea7eb4040001e047fcb2180000000000000000000000000000ba7800000000006ef214904c00000000000000223c00024500000000511dabece70000daf800000000001190000000000031d8000000207c000216a00004680000000000000060aa7d41403652000000019828880002c8d0002ba2a8d0c948faec3a2b2ae704f8142f0002b2e144b66c0000000b0f80001f0400000000000000d180002997cdf800000016a600037be000000000000004701777373160c83c8000d4f134800000000000000b240e520d6045000000000000000000150e00010ec0000000000000062f400000000008f8000035a00008db40000000000000000000000000002fac0002c0628b933a0001b9c6101302ba1644a000000077da60a00023e6bf91baa00000006579c7500000007490000000000019300007ad75d2af3962f0158f0c68700000000000cda0bea4078000000000095e287b00000000000786d132e3000000006ed199c02a07be5338a4888840006353414000334e0002010000212000000007ce0000000000000000c000006b08d18000a8b800012de12e1818000688b6d86a684c2c1500000000000000000000000000a68000b7e815800002740001859739298db29d032000147530d8bca89c478cadc6357a8b0000000000000000000000000225000000017fa3ab000000022e800000000000000dc18000dee0000000000000025b2000000000000000000000000164e7440000c53a97e96e000000031bc20fd9c31d21a0600037b552a000000000000000000000000032f800000000008cbc00051600008c8a184000377095a0ea60000c703580a931f400c89356
  | 72 => 0xb12000342adb383550002592264000000037ba1a38000000000077e0000ba48000000000008d00000000804000000000000000000000801800000021442318ff841e542e793a5560002337000000000033ac0000000c859eee0000000000124a4a108396f0053d00018914f4000015a95755dd80000000000000000000019b60000000a9c2cbe000000045c80005eb8000000058a0001c96000000000000000000000d4f40000e6a0f5000000000031660000000cfcb624000337f0000000128000000000000001d925c4eff0000163b36680004b8019e0090b8e0000000a6e800000000000002c8693e09b8dd200000001dec00000000000000000076e099167800029de000000000008d87288000ca150fa000000092d000067f0000489361a00000000000000000213fd5c000011f14bb0002a6875980007a047580003016000205c5e12c98a242222623ee42bed937bb3d8bfe1c3a20d12d8e6bc61a5a0d9cc0000000000000202a00000000000000a46000002305be7db00000000000000000000000002798df4db700000002aa8000262a6d3000002526f2cbec0009330000000000000000000001c36a772ad20442fdea92aa3c000000000017708932fda11523dc9bd800092da68a0000000000000000000000002dc200022ba0001532ac4b4ce80e1d2299c9b6e00021ed0c0243000022c800002ac00000000002d2ab0280007100000000000000000000000c4e3319b1cc5108500000c3e000077a9908272a8c00000000000dbf6bd600012965f38e480000000924000000000000000aeea6780006a00c030003773aef109f2e293a08a128aa7b08764a308200000061436c81b05b5a91e46d0ca26bab3fed54800000000009a7959c00025661098000000000056b085617d0000000000000000000000000000000000000003c78000c44f819b9ede6daec1810bff34c000000000000000000338035b00000000000000056ea0f80000000066000000000015462900000000251a95c263e293376f0041803000000000000000001ac6c9a1a0000000000538000000291c0001db05fe400000000007369fe3493800015200f800000000000000ba3447a000350c8b6b0de6d780000b880000000000000069a0000000b2703ce808104adeb80000002d2468b0000ca5800000000006940b7b0001aa2000000000000009af2fec3d4cd300000000000000000000000000000aab8000000000091d80003d640000000000d578000bbc8000974c000000000034c80005b8aecc000184e44028564e088262df21d49f0e9f40001b180000000df100004b34dca8c20000000000000035c8000327c000000000000009d7800053500000000000000000000000000bf9fc0b7e125e00000009c22c240000000dcc0000499000005d003800023a8
  | 73 => 0x940400000012e40000000480b37657e845c1380000428c0000000000bee17c3d95a47295ca6a2000000077f00000000bd40000000908263ab598dd80002c6e35c8000000368e0228000b048000ac3c0003c820d8b4da3d00003400ac79421a8ea25768d92ec2bc2ebe1399fda000239a53c800000010eac1835d01241f900001638a2b00000000000000000000025dcbbe8000000000024a723c45a80000000000c1703ca57c4000000187c0001d84000381f00000000001272ab90000000360c0001030000114100028111370176cd70000000000080200003060d6e000000000022e00000000195130dce08000b1a0000b368000000000000029903928000000143c9f92feb48586f0b37ae2a0000228000000000000004f4c00000000001e2281c5f0000055c000000000000000000bfa0fca0002207000378808f400047751703230000000000010925bc2090000452800000016de88e000000000000000000737031ac1a60140002172aa0b2da0001c423d0af1238200000001ad2b31800044ca1ee000343c8320000a0a80000000e0c459800000000004b02b325eb06880002f7b00026daccc8000d11230c000000000016f00000fbc0000000000000000000000000e25000000000035190000000827a7800003096cee800000030a0000255a00000000000000df16366730051a8b7b55450e9a4a8ed80002ec8f5e59aa404d7515dd000043800000005ef8000000039c07a10b40000000a5b1fe6000000000000000002d7000015b60000000000000002bb6760002b7300000000000048000329cb428000850b58356c40004f226185c4800050c8fec67b80009f9c000000076cdb7af526418000c0380008828000de7833683381a29f5a74e1e3a0f076e8000b6809bc00000de48a000000023006a40000cb295ec00000007041c825bba04c0000000be7847400016c00001a04000000000000000002c94bb4b11200000e800000000002728000000000015bc000376600000000000000879542a00000009c0ac323f7c000c2680008714000063174d612172828e620846f1e6768388f91349598abd8000000158c4de0000000000000000000002f4e63940000000000000000000000000002e0400000000000000d4ac0000002ef4000230d0001c940002fc85970e3e0000000000126b000354900003020c6027a000143000000000df01e4c2880000000000000000094b000012ea69a00000000000000000000000000000000000aae81660001b3a3311afa6f116547a480000001cf600000006c9039877a12dab4ca49fdad37827fe30d61bb945cc40a7ca00037dc6d23756cbfaa7ae0280007f5db2c6848000230223500029d400000004f3c000cfda39000007020001c26bba9320aa780000000000000196200004aedd524fe4690000000
  | 74 => 0x36408aac00078809ce0002bcc4708000a618cb400000007cb94040000000b6aae6000000000000fc60002764cda800000018ca000000000035a68bf906ce014cec99230060002de4072893c0000000acc09a4a839be2269826273587680c64000d5a28b4c1f949e00000002e880000000000b4080000000000000087c000082dddf572e0002c645db8f610000686ae0163a000248600000000000676000000000017e81b18000000000000000004ee00000000000000000041bb03aac199e6dfa463c7430d653eb000000000000002bd8000241000032f6da2861c00035768cc05ac7ed8000cada2c7000000000000000001ab8220a42aad7b167000000000000000000000000000000000002bf0000000000000000000000706000000047300000002c8a00000004cb47ae75a244285e4000000000000000007ef81d800027fa729193e0000000bde80009e60000000111227a054ac56400000000008d2985e3e11b6608a8000000000065596149cc0af400000000002f9c0001ba2000000035ea152a5e28932d1989400003fad85000000000000000000632c00
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc5c7598d200400193ee931a4008003271d2634801001e6a38cc690020008de8758d20040011b90eb1a400800317dd563480100062e3aac69002000c9f7458d2004001938e8b1a400800f351c5634801000637baac49002000c6c75589200400195ee8b1240080032b1d1624801000667b9ac49002000ccc7358920040079c8e2b1240080031d99771480100063ab2ee29002000cb664dc5200400196ac9b8a40080033598f71480100066ab1ee29002038ce662dc520040019cac5b8a40080be79a1f214801000572c36429002038ce776c852004001b88e790a40080062fa1176080100347ac0aec100202bce4215d8200400117f0cba040080030f99574080100061eb2ae81002006cae625d0200400117f0eb2040080022f61d64080100061f3aac81002000c3d75590200400796ce2b20400800237e1e63080100046ec3cc61002000c5e7598c20040018baeb3184008003279d263080100064eba4c61002003cd67198c20040011bf0eb1840080023761d63080100062f3aac61002000c5d7558c200400193ce8b184008003275d1630801001e6b38ac61002000c76655c420040018eacab8840080032d99171080100065ab22e21002000cd6635c420040019aac6b88400801b39989710801000672b12e21002000c7785dd910040018e90bbb220080032de1376440100065a426ec8802000cd783dd910040019a907bb2200800339e0b764401000672416ec8802000c7776dd510040018eeec3aa20080032dddb74440100065bbb0e88802000d34751d110040019aeedb9a20080023d61a73440101a4eb41ce6880202a9e6829cd10040019aeec39a200800355dd47344010006aa3a8e68802000d97741cd1004001b28e839a20080d275e1873440101a4eac30e68802034d56651cd1004069aaaca39a20080d36599073440101a6cab20e68802034cd7621cd1004069b8cc439a20080d37158873440101a6e9300e6880202b9e687dc910040019ceedb922008003711cf724401000673bb0e48802000d67751c91004001ac8ea392200800369dd07244010006d23a0e48802000dc7731c91004001b88e639220080ae79e18724401015e73430e4880202b9e5861c910040559cb0c39220080af59994724401015eb2b28e4880202bda6641c91004057b4ac839220080af7198c724401015ee2b18e4880202bde2601c910040551e90eb122008003351cd624401015672392c4880202ace78758910040015cd0eb122008002b921d62440100067243ac488020008e4875891004001cceeab122008003991d5624401000753ba2c48802000ea4745891004001d8ee6b122008003399cd62440100067239ac48802000ec4735891004001988e6b12200800f39dc1624401001f71b82c488020038f68798110040019a8e730220080e3391ca6044010
  | 1 => 0x904b9cc0080021fe1572980100143e42ae530020008bf845ca600400317908b94c00800237e0d72980100046e41ae53002003ce67158a50040018eacab8ca00800339589719401001e7338ac52002000cb5645c640040019cac4b8c800800e3d20576cc01001e7238ac59802000cd576cc73004001d8ac598e60080d6b5205638c01001e7338ac51802035ec43158a30040019aac6b8c600800339589718c0100143e42eec98020018bc84dd930040071b907bb260080023de07764c0100843ec36ea9802000c3e64dd530040010fd0eb2a60080161f21d654c0100061e3a2ca9802003c7471595300401f17b0dba260080030f997744c0100061eb2ee898020008be8759130040091790eb2260080030fdd5644c0100061e3aac89802003cb47159130040018beeb31a6008003171d6634c0100064fba4c69802000c9c7498d30040079a8e331a600800317dd5634c0100062e3aac69802000c9f7458d3004001938e8b1a600800f351c5634c0100063732ee49802000c6d65dc9300400195cc9b9260080032b593724c0100066731ee49802000ccd63dc930040018dcca39260080031b594724c01000657320e49802000cad641c9300400199cc639260080033358c724c0100047743cc498020068ec8798930040018deeb31260080031b1d6624c01000657ba4c49802000cac7498930040079c8e331260080023ba1d624c0100047643ac49802000c6f7558930040018d8eab1260080032bdd1624c010006563a2c49802003ce47158930040018eccbb8a60080031d597714c0100065b326e29802000cb564dc530040019acc7b8a60080033558f714c01000673316e29802000ce562dc5300406b3ad0f98a600800335ddb314c010006e2396629802000ec562cc530040071bb06bb0600800f1d9c5650c01001e5b38ac81802034ad48158c30040079cce2b1060080d3b10c5620c0100063ab2ae21802000cb5645c430040019acc6b88600800339589710c01001c7a40aed900202ace7215db20040079c8e2b1640080bf39087768801001e7338ac510020008f7865c620040013a906b8c40080033958971880100143e42eec90020018bc84dd920040071d905bb240080e23de0776480101743ec36ea9002000c3e64dd520040cd8dcc5baa40080021fa1d654801002c3e43aca9002000c3c7459520040078e8e2b2a40080b62f61b74480100061f32ee89002000c3d65dd120040ab95cc5ba240080022fa1d64480100245e43ac89002000c3f755912004001878eab22400800f2d1c564480100062f32ee69002000c5d65dcd200400193cc9b9a40080032759373480102a667316e69002000c5e651cd20040018baca39a40080032799073480100064eb20e69002051cce621cd20040011bd0f31a40080023721e63480100062fbacc69002000
  | 2 => 0x4405881000572c0880b10200387f8759652040070f90bbb2a40800e3d205765481001c7643ac4a902003ce47158952040018eacbb8aa4080033958b715481001c5fc3ac921020038bc84dd942040071e902bb2840800e2f21d645081001c7643ac4a102003ce471589420400196ac9b8a84080033958b715081001c7b40eed9902003c7671597320400796ce2b26640800e3761e63cc8102056a40ac799020038ef8758b32040079cce2b166408103b10c562cc8100063ab2ae39902000cb5645c732040813a906b8e64080033598d71cc81000672b12e3990200287e855da320400317d08bb4640801a3d605768c8100043fc32eb1902000c3e645d6320400d8dcc4bac64080021fe1d658c8100043ec3acb1902000c3e7459632040078ece2b2c64080022fe19748c8100061f32ae91902000c3d655d2320400d95cc4ba464080022fe1d648c8100045ec3ac91902000c3e75592320400187aeab24640800f2d9c5648c8100062f3acc71902000c5d7598e320400193ce931c6408003275d2638c81001e6b38cc719020038df8758e32040018bceab1c6408003175d5638c8100064f3a2c71902000c9d7458e32040079ace2b1c64080031b9d5628c81000636baac51902000cae7458a320400195ae8b14640800f399c5628c8100063b32ae31902000c75655c6320400196cc8b8c64080032d591718c8100066b31ae31902000cd5635c6320400d9ccc4b8c640800339589718c81001c7a40aec99020038dc8758d32040775a902b1a640800e3b21d624c81001e7238ac4990203bec43158932040019aac7b8a64080033958b714c81001c7a40aec190202ace7215d832040071bb0f318640800f391c5620c81001d6ac1aed9882003ad78758f31040551ef0eb1662080ab399c962cc41000673c3ac59882000ec78358b3104001d8906b16620800f399cd62cc41001f6339ac5988203b9d5878cb31040015ab0d1966208003b158a32cc4100056ac30659882000ec5620cb31040019cac4b8662080031da1576c84100063ac2aed9082000cb6845db210400196b08bb6420800335a0d76c84100066ac1aed9082003ce6825db21040079cb04bb642080ab390c976c841015673902ed90820409d7869cf21040813ab0d39e42081035599673c8410206aab2ce79082040d96649cf2104081b2ac939e420810335d8a73c8410206e3314e7908202acd5629cf2104081b8ac539e42080e33598273c8410206e9304e79082003ae78758b2104055ccceab1642080ab995d562c8410157533a2c5908202aea57458b21040019cce6b1642080abb19cd62c84100066339ac5908202aec57358b21040559c8e6b164208003395db32c841000672b12e1908200087f855ce60040050f90ab9cc0080022fe11739801000c5e422e730020008ef825ce600400d1d
  | 3 => 0xd298200387f8759653040014bf06b2ca60800387d4d6494c1001c6ec3cc72982002a5e8598e53040054bd0ab1ca6080062f2137654c100045fc22eca9820018bc845d953040071e902bb2a60800e1f21d6554c100061e3a2caa9820008bd86dd1530405387ccbba2a6080030f5977454c100045f43ac8a9820008bc87591530400193ee931aa608003271d26354c1001c6e43ac6a982000c9f7458d5304001938e8b1aa6080031d5977154c100066ab1ee2a9820038bf8759243040071bb0f31c860800a1f2177650c100064e21eeca18200087f855d943040050f90abb286080032710d7650c1001c7a40aeca18200087d86dd5430409187cc9baa86080021fa1d6550c100043e43acaa182000e1c4359543040071790eb2286080030fdd56450c100061e3aac8a182000a9c8359143040018beeb31a8608003171d66350c1000d4e424c6a1820038dc8758d43040018beeab1a8608003171d56350c1000d4e422c6a182000cb564dc543040019aac7b8a86080038bd52549881000567c1aa93102000acc835526204001c5aa82a4c40800393d4e539881000557c22a73102000aac8454e620400155d0829cc408002ab610539881000537c2a873102000a6c8550e62040014dd0a21cc4080029b614439881000746a18873102000aae84d42620400155b09a84c4080029ba17409881000536c2e81310200287e85dcd62040010fb0bb9ac4080062fa1373588100045ec26e6b1020038ee87d4962040075cd03a92c408002aba10525881000556c20a4b1020038ee87d0962040075cd03a12c4080029ba14425881000536c2884b102003ae6819d562040015cb033aac40800eb9205755881000557420eab102000aad841d562040075cd033a2c408002b9606745881001d7240ae8b102000a6e851d162040014db0a3a2c4080038bd52545881000567c1aa8b102000acc8355162040015cf02aa2c40800eb9205545881000716aa0a8b102000a6e85dcd62040014db0bb9ac408002aba13735881000556c26e6b102003ae681dcd62040075cd0339ac408103b10c6735881001d7240ae6b10203bec4315cd62040075c90239ac40800eb9a07535881000572c0ea6b102000e4f5394d620400155f08a9ac408002ab211535881000573c0aa6b102003ae48154d620400155d0829ac408002ab610535881001d7340e86b102000ae581d0d62040014df0aa1ac4080029b215435881000573c0a86b102003ae48150d62040014dd0a21ac4080029b614435881000746a1886b10202fce4719c162040014dd0a382c4080029b614705881000557420e0b102000aad841c1620400159d06382c408002b360c705881015e72388e0b102000aae84d41620400155b09a82c40800eb9a04505881000572c08a0b102000a6e85d0162040014db0ba02c40800eb9a0
  | 4 => 0x40400147f0ab9ac8080028f215735901001d5a40ae6b202000a3e851cd640400147b0a39ac808003275cc735901001d5b40ea6b202000ab581d4d640400117d0e29ac8080022f61c535901001d5a40ae4b202000a3e851c9640400147b0a392c80800eada0752590100055ac0ea4b2020008be87149640400117b0e292c8080122fa1f50590100045ec3ea0b202003ab681141640400156b02282c8080030f15376550100061e2a2ecaa020008df835d954040011b906bb2a80800e3d205765501001c3e43acaaa02001a3c8459554040071790eb22a80800a8f21564550100046ec36e6aa02065c5e65dcd54040018bacbb9aa8081872799373550100064eb26e6aa020008dd861cd54040c98bcca39aa8080031759473550103064f320e6aa02000c9d641cd54040cfa38a839aa8080031d59771550100065ab26e2aa020008bf845d6630400317908bacc6080021fe157498c100143e42ae931820038dd8714e630400153d0829cc608002a76105398c1001c6ec38873182000a5e8510e63040014bb0a21cc608003275d04398c100062fbaceb3182000a9f845d6630400153908bacc608002a7a107598c100054ec20eb3182000a5f855d263040014b90aba4c60800297a147498c100052ec28e93182000c9d741d26304001c3ea92a4c60800237e1d5498c100046e43aa93182000e1d5415263040075ad03b94c60800297a167298c100052ec2ce53182000a9e849ca630400153b09394c60800eb5a067298c100054f420a53182000a9d8414a63040014bd0a214c608002976144298c100054f426a13182000a9d84d4263040014bd0ba04c608002976174098c1001c6f43ea6b182000c5f75d4d63040075ad03a9ac608002a7a105358c100054ec20a6b1820038de87d0d63040075ad03a1ac60800297a144358c100052ec2886b182000c5f759d563040075ad033aac608002b56067558c100054fc22eab182000a9c845d563040075a902baac608002a7a107558c100054ec20eab182003ad6819d163040015ab033a2c60800297e157458c100052e42ae8b182003ad4815d163040014bd0a3a2c608002976147458c100064eba0e8b182000e1f5495163040011bf0eaa2c6080023721d5458c100070eaa0a8b182040cd471dc963040014bd0b392c608002976167258c100054f424e4b182000a9d849c963040075ad03392c60800eb52057258c101de6a38ae4b182003ad681d4963040015ab03a92c608002a7a105258c100054ec20a4b182003ad681d0963040015ab03a12c60800297a144258c100052ec2884b182035cd4719c163040699a8e2382c608002a7a135058c100054ec26a0b182003ad68114163040015ab02282c60800297a174058c100052ec2e80b182003ad68110163040015ab02202c60800317d4f7694c100062fa9ae
  | 5 => 0x80032bd93724c11000656326e49822000ccf63dc93044001998c7b9260880be3ba18724c11000637b28e49822000c6c651c9304400195ec839260880032b190724c11000667b18e49822000ccc631c930440011dd0fb1260880be3b21f624c11000637baec49822000c6c75d89304400195ee9b1260880032b1d3624c11017e7238ec498220008ee8718930440018deea31260880031b1d4624c11000657ba0c49822000cac7418930440579c8e231260880031dd97714c1100063a32ee29822000cb764dc53044001968c9b8a60880033518f714c11000673b16e29822000ce462dc530440699ace231e40880033518d71c811003672312e39022003ce4764872044001d88c690e4088002b9a1a21881100076231c4310220008bf845d9204400317908bb2408800237e0d76481100046e41aec902204b8be86dd1204400187ecbba240880030f19774481102ae56316e890220688be87d9120440991790fb2240880030fdd764481100061e3aec8902204ccb471d9120440a31bd0fb1a40880d63721f63481100062fbaec69022000c5c75d8d204400193ee9b1a4088003271d363481101ae6a38ec690220548de8718d20440691b90e31a408800317dd463481100062e3a8c69022000c9f7418d2044001938e831a40880d3351c463481100063bb2ee29022000c7465dc5204400196ec9b8a40880032d19371481100066bb1ee29022000cd463dc520440719c8c5b8a408801ab9219214811001e723b2429022000ec46348520440017c10090a408813b1d9db65841100163b3b0cb082204ccb676d92104400396cec32420880038d19464841101ae6b3b6c70822038ae68298e10440699acec31c208800395d9463841100072a328c70822000e976418e1044001d28c831c20880033518f728411001c7a432e50822000cd4635ca10440719c8c4b942088003b118f628411000733b28c50822000e646518a1044001d4ec83142088003a9190628411000763b18c50822000ec46318a10440719cb0e314208800e1fa1e54594100061fba4a8b2820018be841cd650400117b0839aca080030fdd274594100052fc1ae8b282000a5c835d165040074e902ba2ca080030f5d074594100062fb9ce6b282000a3f845cd650400147908b9aca0800e9d20573594100051f420e6b282000a3d841cd65040074ed03a1aca080029d60743594100043f43886b28200087d8710d65040074e902b92ca080028fa1072594100051ec20e4b282003a7681d0965040014eb03a12ca080021fa1c42594100043ec3884b28200587e87d0165040010fb0fa02ca0800e9da0440594100053ac0880b2820038be87d51640400187eebaa2c80800a1fa1473590100043ec28e6b202000c3f759d5640400153f06baac808002a720d755901001d5a40aeab202000c3d751d56
  | 6 => 0x62f3aec790a2000c5d75d8f214400193ce9b1e4288003275d363c85100046ec38c790a2000c5e7518f21440018baea31e4288003279d063c85100064eba0c790a2000c6e75d8b21440018daebb1642880032b9d362c851000656ba6c590a2000cce73d8b214400199ae7b16428801b3a18a70c85100063bc2ced10a2000c74859da214400196f093b442880032d21276885100066bc1ced10a2000cd4839da21440019cf053b442880031d9db65885100063b3b0cb10a2000cb676d92214400196cec32442880038d19464885100066b3b6c710a20008f58798e214400d5cd0531c4288003359d863885100072bb28c710a2000e546518e2144001d2ec831c4288003a519063885101a56bc38c710a2034ad58718e2144069cacea31c42880d3955d463885101a74b3a0c710a2034e957418e21440019ccedb144288003b118f628851000733b28c510a2000e646518a2144001d4ec83144288003a9190628851000763b18c510a2000ec46318a21440019a8c738442880e33918a70885102773210eca90a204cea421d91214406bd8843b1a42880d3b1084634851001d7340ec490a2000ceb621c12144001c68ca322428801a3da1e63485100056b41cc690a2006ae68298d2144001caeca31a42880039519463485100074bb20c690a2000e946418d2144001d8f0431a4288003b120863485101a66bb90c690a2034ec77218d214400d5cd0db124288003b118f624851000733b28c490a2000e64651892144001d4ec83124288003a9190624851000763b18c490a2000ec46318921440015cd0d992428801b391db32485100076231e6490a2006ae4860c92144001d88c619242880033518c704851015ef1b90e090a204ec7471d9550440699a8e231aa0880af391c462541100063bb2ee2a822000cb464dc550440019a8c7b8aa0880033918b71541102665a38ec8a022034cd47118d40440579c8e231280880031d19771501100066a31ee2a022000ce462dc540440699ace231e60880af399c462cc1100066a31ae39822000ce4625c730440050fd0bbb260880021f617764c11000c5f426ec98220008bd84dd930440011db05bb260880021fe15764c1100143e42aec98220008bf845d9304400317908bb260880023be09764c11026c3f436ea9822000c3c64dd530440010fd0fb2a608813a1f21f654c1100061e3a6ca982204ec7471d95304409717d0dba260880030fd97744c1100061e32ee898220008be87d9130440991790fb2260880030fdd7644c1100061e3aec8982204ccb471d9130440018beebb1a6088003171d7634c1100064fba6c69822000c9c74d8d304406b9a8e3b1a608800317dd4634c1100062e3a8c69822000c9f7418d3044001938e831a60880d3351c4634c11015c77436e49822000c6f65dc930440018d8cbb92608
  | 7 => 0x6c85440624400155f08880c488002ab211101891000567c1a203122000acc83440624400117f08bb4a4880062f21176949100046fc1aed29220008dc835da524400d1d904bb4a48813b1d9c765949101a66b388c72922000c77655c65244001968c8b8ca4880033518d719491003672312e329220018be84dd9524400117b09bb2a48800237a0f76549100046ec1eeca92200687e87d9552440051dd0fb12a4880021fe1576909100143e42aed21220008df835da42440011b906bb4848801a3b20976909102665b38ec92122034cd67118e42440018e8cab8c84880033518d719091003672312e3212200287e85dd942440010fb0bbb2848800237a0f76509100046ec1eeca12200087f855d942440050f90abb2848800237e0d76509100046e41aeca1220008ef825d942440011ef02bb2848801a2fa1f645091000c7743ec4a1220018be84ddb324400117b09bb664880021fe1576cc9100143e42aed99220008bf845db324400317908bb6648801a3761c63cc9100143e42ced19220018bc849da32440071e9033b464880021fe15768c9100143e42aed19220008bf845da324400317908bb464880021f219758c9100061e322eb1922006c6c625d632440010ff0fb2c64880021f61f658c9100061f3a6cb192204ec7671d9632440011790cba464880030fd95748c9100061e32ae91922006cac625d2324400117f0fb2464880022f61f648c9100061f3aec91922000c3d75d92324409996ce3b246488003179d7638c9100062ebaec71922000c9e74d8e324400193ae9b1c64880d7359c7638c9100062f3a8c71922000c5d7518e324400193ce831c6488003275d0638c9101a66b388c71922000c6e75d8a32440018daebb1464880032b9d3628c91000656ba6c5192202fce671d8a32440018eecab8c64880031d195718c9100065bb22e31922000cb4645c632440019a8c6b8c648800339d89718c91003672312e3192200287e85dd932440010fb0bbb264880062fa13764c9100045ec26ec99220008bf845d9324400317908bb2648801a37a1f634c9100043fc2aec192200287c855d8324400117f08bb064880062f211760c9101a66b388c61922000cd4635c4324400d9c8c4b8864880031ed9470545100065db20e0a0a2000cd8639c331440019b6c638262880021f21975c85100061e322eb90a2006c6c625d721440010fb0fb2e42880030f9d365c85100045e432e990a2000c3f655d32144001878caba6428801b2b18974c85100045ec3ec990a2000c3e75d93214400187aebb26428800237a1a73c85100062fb2ce790a2000c5c659cf214400193ec939e42880032719273c851003666314e790a20008dc865cf21440018becab9e42880031719573c85100064fb22e790a2000c9c645cf214400d998c4b9e42880023761f63c85100
  | 8 => 0xebb14c4880031b5d76298910006573a6c53122000cad74d8a624400199ce7b14c488003335cf62989100043f43ecab122000c3c74d9562440010fd0e32ac4880030f1d065589100061fb2ee8b122000c3c65dd1624400117d0fb22c4880030fdd764589100061e3aec8b1220008be87191624400187eea322c4880030f1d464589100062fb2ee6b122000c5c65dcd624400193ec9b9ac4880032719373589100062fb28e6b122000c5c651cd624400193ec839ac4880032719073589100046f43ec6b122000c5f75d8d62440018b8ebb1ac48800327dd363589100064e3a6c6b1220008de8718d62440018beea31ac488003171d463589100064fba0c6b122000c9c7418d624400187eebba2c4880030fdd474589100061e3a8e8b122000c9f74dcd6244001938e9b9ac48800327dd073589100064e3a0e6b122000c7775dc562440018e8ebb8ac4880032ddd371589100065a3a6e2b122000cd773dc562440019a8e7b8ac4880023be1d621891000537c2ac43122000a6c85588624400155f08b10c488002ab211621891000567c1ac43122000acc8358862440018dcedb28c4880023b61e651891000557424ca3122000aad84994624400159d07328c488002b360e651891000477c3aca3122000aaf84594624400155908b28c488002b3e0d65189100056641aca3122000c6e76194624400195cedb20c4880038bd9764189100071632ec831220008ed8799062440014dd0b320c4880029b61664189100056741cc83122000acd8399062440011df0eb20c4880029be1564189100053642ac83122000acf83590624400159906b20c4880032b9d8641891000717b28c83122000e2c65190624400199cedb18c48800393d9763189100072632ec63122000e8f64d8c6244001d18c9b18c4880023b61e63189100053742cc63122000a6d8598c624400155d09318c488002ab612631891000477c3ac63122000a6f8558c62440014d90ab18c488002abe11631891000556422c63122000cce7618c6244001c9eca318c48800393194631891000747b20c63122000e8c6418c6244001ccecab88c48800399195711891000753b22e23122000ea4645c46244001d8ec6b88c488003b118d711891000717aa4a83122000acf83550624400159906aa0c4880038b550541891015d73408a83122000ae5811506244001c9ea7298c488002abe11531891000556422a63122000aae8414c624400155b08298c4880aeb9a04531891000572c08a63122000a6f8550c62440014d90aa18c4880029ba14431891000536c28863122000e8d4310c62440575cd02218c488002b9604431891000557426a03122000aad84d4062440575cd03a80c488002b960750189100053742e803122000a6d85d0062440575cd03a00c488002b9607401891000537c2a203122000a
  | 9 => 0x7690d1000c6ec38c721a200287e85dd943440010fb0bbb2868801a3ba0b7650d1000476c16eca1a200287e859d943440010fb0b3b286880032710e7650d100043fc2aeca1a200287c855d943440011bf06bb286880023be097650d1003476412eca1a20008f7815d943440050f90a3b286880032710c7650d100043f436eaa1a2048c3c64dd543440010fd0fb2a86880021f21f6550d100070e21ecaa1a2000c3f75d914344001878ebb228688002a7a0f6450d1000c6f43ec6a1a2000c5f75d8d43440018b8ebb1a8688006a7a136350d100062fba8c6a1a2000c5c7518d43440035390831a86880021fe1573d89100143e42ae7b1220008bf845cf624400317908b9ec488002aba1052d891000556c20a5b122000a6e8510b62440014db0a216c488002aba1265d891000556c24cbb122000ace83997624400159b0732ec488002abe1165d891000556422cbb122000acf83597624400159906b2ec4880038bd9764d89100071632ec9b122000a6e8599362440014db0b326c488002b3a0e64d891000566c1cc9b122000a6f8559362440014d90ab26c488002b3e0d64d89100056641ac9b122000e2f651936244001c58ca326c48800393d9763d89100072632ec7b122000e8f64d8f6244001d18c9b1ec4880029ba1663d891000536c2cc7b122000aae8498f624400155b0931ec4880029be1563d89100053642ac7b122000aaf8458f624400155908b1ec48800393d9463d891000726328c7b122000e8f6418f6244001d18c831ec488003b118f71d891000557424ebb122000aad849d762440014dd0b3a6c4880029b61674d891000717aa4a9b122000acf83553624400159906aa6c4880038b55054d891000537c2ae7b122000a6c855cf624400155f08b9ec488002ab21173d891000573c0ae7b122000e4f5394f624400155f08a9ec488002ab21153d891000557420a7b122000aad8414f62440014df0aa1ec4880029b21543d89100053742887b122000a6d8510f6244001d1a8621ec4880029be1571d89100053642ae3b122000aaf845c7624400155908b8ec488002b3e0d71d89100056641ae3b122000aae84d43624400155b09a86c4880029ba1740d891000536c2e81b122006c6c625d6624400187ce9b2cc4880030f9d065989100061fb2ae93122000c3c655d2624400d958c4ba4c4880030f9d764989100061ebaec93122000c3e75192624400187aea324c48800317d9673989100062e32ce73122000c9f649ce6244001938c939cc48801b3318a73989101c66bb0ce73122000c5f655ce62440018b8cab9cc48800327d9173989100064e322e73122006ccc625ce62440018bcebb1cc488003175d763989100064f3a6c73122000c9d74d8e62440018bcea31cc488003175d463989100064f3a0c73122000c9d7418e62440018dc
  | 10 => 0x31a2000a9d849cc634400159d05398c688002b360a7318d100054f420a631a2000a9d8414c63440015ab02298c68800297a144318d100052ec288631a2000c9d7410c63440015ab02218c688003179db6518d100046ec3cca31a2000a9e84994634400153b09328c688002b3a0a6518d1000566c14ca31a20008df87594634400153f08b28c688002a72116518d1000567c12ca31a2000acc8259463440018bcec328c688003279db6418d100070fb2ec831a2000e1c65d9063440011bb0f320c68800297a166418d100052ec2cc831a2000ace82990634400159b05320c68800237e1d6418d100052fc2ac831a2000a5c85590634400159f04b20c688002b32096418d100064f3b0c831a2000e1f651906344001c38ca320c68800317dd67518d100054fc22ea31a2000a9c845d4634400153d083a8c688002a76107518d101a56b408ea31a2000ad5811d463440014bf0aba0c688002972157418d100052f428e831a2000a5d851d0634400193ae83a0c6880d2b5a047418d100056ac08e831a2000e1f5495063440011bf0eaa0c6880023721d5418d100070eaa0a831a2034ad68115063440015ab022a0c68800297a167218d100052ec2ce431a2000a9e849c8634400153b09390c688002b56067218d100056ac08e431a2000a9e84148634400153b08290c6880d2b5a045218d100056ac08a431a2000a5e8510863440014bb0a210c6880d2b5a044218d100056ac088431a2000a5f855c063440014b90ab80c688002a7e117018d100054e422e031a2000acf825c0634400159904b80c688002a7a135018d100054ec26a031a2034ad681d4063440015ab03a80c68800297a174018d100052ec2e8031a2034ad681d0063440015ab03a00c68800297e151018d100052e42a2031a2000a9f84440634400153908880c6880062fa137694d100045ec26ed29a20008de83dda534400d1dd05bb4a6880023b60b7694d100062fa9ced29a20008bf845da534400317908bb4a6880023be097694d1003476412ed29a2000c5f531da53440014bb07b2ca68800387d4f6494d100152e42ec729a20028dd8718e53440054bd0a31ca6880062fa137654d100045ec26eca9a20068ee82dd953440011db05bb2a6880062fa127654d100045ec24eca9a20008bf845d9534400317908bb2a68800237e0d7654d1000477c12eca9a20068ec825d953440011ef02bb2a6880062f2107654d100061e3a6caa9a20008be86dd1534400187ecbba2a6880a70f1977454d100045f43ec8a9a20008bc87d9153440051bd0fb1aa68800327dd36354d100064e3a6c6a9a2000c9f7418d5344001938e831aa68800a1fa177690d100043ec2eed21a20008de83dda434400d1dd05bb486880023b60b7690d100043fc2aed21a200287c855da43440011df04bb4868801a3b209
  | 11 => 0x4400153b0932ec688002b3a0a65d8d1000566c14cbb1a2000a9f84597634400153908b2ec688002b3e0965d8d1000566412cbb1a2000e1f65d936344001c38cbb26c68800297a1664d8d100052ec2cc9b1a2000ace82993634400159b05326c68800297e1564d8d100052e42ac9b1a2000acf82593634400159904b26c68800387d9464d8d100070e328c9b1a2000a9e84dd7634400153b09baec688002a7a1275d8d100054ec24ebb1a2000c5d751d763440014bd0bba6c6880029761774d8d100052f42ce9b1a2000a5d859d3634400193ee93a6c68800387d5254d8d100046fc3aa9b1a20008dc875536344001c3aa82a6c68800297a1472d8d100052ec28e5b1a2000a9e841cb634400153b08396c688002b560472d8d100054f420a5b1a2000a9d8414b63440014bd0a216c6880029761442d8d100054f426a1b1a2000a9d84d4363440014bd0ba06c6880029761740d8d100061f3a6cb31a2000c3e74196634400187ecaba4c6880030f1957498d100061f3aec931a2000c3d75d92634400187cea324c6880030f5d46498d100062f3aec731a2000c5d75d8e634400193ce9b1cc688003275d36398d1000637b2ce531a2000c6c659ca634400195ec9394c6880032b1927298d1000667b1ce531a2000c6f655ca63440018d8cab94c6880032bd917298d1000656322e531a2000ccf635ca634400187ceb3a4c6880030f5d67498d100061f3aae931a2000c3d755d263440018dceb394c6880031b5d67298d10006573a4e531a2000cad749ca63440018dceab94c6880031b5d57298d10006573a2e531a2000cad745ca63440019cce4b8cc6880021fa1f6558d100061e3a6cab1a200087e871956344001878e832ac6880030fd977458d100061e32ee8b1a20008be87d91634400187eebb22c6880030f1d76458d100045f438c8b1a2000c3f751916344001878ea322c6880031bd977258d100063632ee4b1a2000caf64dc96344001958c9b92c6880031bd947258d1000636328e4b1a2000caf641c96344001958c8392c6880030fdd77458d100061e3aee8b1a2000c3f751d16344001878ea3a2c68800317dd77358d100062e3aee6b1a2000c9f74dcd6344001938e9b9ac6880031bdd77258d10006363aee4b1a2000caf74dc96344001958e9b92c68800333dcf7258d1000637ba8e4b1a2000c6c751c9634400195ee8392c6880032b1d07258d1000667b98e4b1a2000c7775dc563440018e8ebb8ac6880032ddd37158d100065a3a6e2b1a2000ce772dc563440019c8e5b8ac68800237e1d6318d100052fc2ac631a2000a5c8558c634400153f08b18c688002a72116318d1000567c12c631a2000acc8258c634400117f08ba8c6880062f2117518d100043fc2ae831a200287c855d063440014bd0b398c688002976167318d100054f424e6
  | 12 => 0x3271d373595100062fba8e6b2a2000c9f741cd6544001938e839aca880031bdd7725951000657ba6e4b2a2000cac74dc9654400199ee7b92ca88003331cf725951000637ba8e4b2a2000caf741c96544001958e8392ca8800333dcc725951000666398e4b2a2000cb474dc565440019a8e7b8aca88003391cb71595100052f41cc832a2000a5d8399065440014dd05320ca880029b60a64195100061ebaea9b22200287e859cf64440010fb0b39ec888002a7a0e65d91100054ec1ccbb222000aae82997644400155b0532ec888002a7e0d65d91100054e41acbb222000aaf82597644400155904b2ec888002a7a0f75d91100054ec1eebb222000c3f759d7644400187aea3aec8880028fa1773d91100051ec2ee7b222000a3e859cf644400147b0b39ec88800327dce73d91100045f438a7b2220008bd8714f644400147d0b396c8880028f61672d91100055ac08e5b2220008be8714b644400117b0e296c8880028fe1570d91100051e42ae1b22204c8be87d43644400117b0fa86c8880030f19375591100043f43ecab22200087e8719564440018becbb9ac8880031719773591100064e326e6b222000c5f651cd64440018b8ca39ac88800327190735911000637b2ee4b222000c6c65dc96444001958c9b92c8880031bd94725911000636328e4b222000cac641c964440050fd0fbaac8880030fdd774591100061e3aee8b222000c5f75dcd64440018b8ebb9ac88800327dd373591100062fba8e6b222000c5c751cd644400193ee839ac8880031bdd77259110006363aee4b222000caf74dc9644400199ee7b92c888003331cf725911000637ba8e4b222000c6c751c9644400195ee8392c88800333dcc725911000666398e4b222000c7475dc564440019a8e7b8ac888003391cb71591100061f3b6ca32220008bd87994644400147d0b328c888002a7a0e65191100054ec1cca3222000aae82994644400155b05328c8880022fe1d65191100054fc1aca3222000a9c83594644400155f04b28c888002ab20965191100051f430ca3222000c3e7619464440011bd07bb2a8880023760f765511003477416ecaa220008ed82dd95444001878a93b2a88800237a0e76551100046ec1cecaa2200087f855d9544400117f08bb2a88800237e0d76551100046e41aecaa220008ef825d9544400d1d904bb2a8880023de0576551100061e2a0ecaa2200187e87d95544400347d09b2aa88800a2fa1f64551100151f42ec8aa220008de86dcd54440018becbb9aa8881971719773551100064fb26e6aa22061c9c64dcd54440011bd0c39aa88800317d9473551103262e328e6aa22000c9f641cd54440c1938c839aa8881a74715073551100062ebaea7b1a2000a9e8414f634400153b0829ec68800297a1443d8d100052ec2887b1a2000a9e8499763
  | 13 => 0x61fba8e8b142000c3c751d162840018beebb9ac508003171d77358a100064fba6e6b142000c9c74dcd62840019ad03b9ac508003356077358a100062fba8e6b142000c5c751cd628400193ee839ac508003271d07358a100066639ee4b1420008ef87588628400159906b10c5080022fe117694a1000c5e422ed29420008bf845d9528400317908bb2a50800237e0d7654a100046e41aeca94200087f855da42840050f90abb485080021fe157650a100143e42aeca1420008df835d942840011b906bb2850801aab2096450a100143f42eed994200087d85ddb328400317d09bb665080022f61376cca1003566412c79942035cd671d8e32840699ace231c650801a3de19718ca100043fc2aec994200287c855d9328400117f08bb265080062f211764ca100046f43cc69942006acc8258d32840010ff0abb0650800a1f215760ca100045fc22ec19420018bc845d832840011bb0fb1865080d637e1d63cc61029d66412c798c2000ae78258f318400178904b1e63080e3399cb62cc6100056bc1ac598c2000ad5868cb31840015ab0c19663080d237a1e634c61029566412c698c20389e4825d831840011eb0fb1863080027561f630c6101a5e9406c618c2000ae78258c318406b7a50031863080e23de1d620c61000763b166418c20009d7874c831840713c904b8063080be3be1d62c86100056641ac590c202fde0219c321840719aec539e43080e33558a73c8610005e241ac590c202a8f7865c3218400159906b1243080027520d7608610004f2c3ec410c202bbe280d88218405f5cb0fb1043080033961f62086100067339ec410c202fce473d882184001dc501b1043080027520d700861000673b12e010c200387e87d95508400717d0fb228108152b3209638c2100046f438c69842034cd47118d308400199ec639261080033318c724c210004eb43e629842000dc472cc530840011bf0eb186108146b3209630c210004ea41ae310420009d4835db10840713c904bb621080bf391cb62c42101c47bc3ac58842038ce67258b108400187ae92a6ca880062fa1273d95100045ec24e7b2a2000a5e8399365440014bb07326ca880029ba0a64d951000536c14c9b2a2000a5e83dd365440014bb07ba6ca880030fdd274d95100061eba0e9b2a2000a3e84dcf654400147b09b9eca880028fa1273d95100051ec24e7b2a2000c5d731cf65440010fd0e21eca880021f61c43d95100051f424e5b2a2000a3d849cb65440014eb02396ca880021fa1c42d95100043ec3885b2a2000a3f845c3654400147908b86ca8813a1fa1f40d95100043ec3e81b2a2000c3c65dd165440018b8cbb9aca880031719473595100063632ee4b2a2000c6c651c9654400317d0fba2ca880030fdd774595100061fba8e8b2a2000c5f75dcd654400193ee9b9aca88
  | 14 => 0x574586210c0019ace6b0c42180062fa1076484300045ec20ec90860008dd86dcd210c00d5c904b0a4218003b1588314843001e73bb2421086000ce576484210c069b88e690842180032759273900301a46fc3ac39806034cd671587300c0011bb0f31c60180023e61e638c030005e5414631806000c9f76dd1300c00193eec3a26018003471d4744c0300066bbb6e29806000cd7761c5300c001aaeea38a6018003551d4714c030006cbba0e29806000d94741c5300c001b8ee438a6018003711c8714c0301a66ac30e298060348dc87585300c001998e4b0a60180d3351c5614c0300065dbb6e89806000cbb761d1300c0019e6edb8a60180033cdd8714c030006e9b98e298060008df835d954c40011b906bb2a98800e1f21d655531000d1e422caaa620038bc8759154c40054790ab22a9881931799473553100062eb28e6aa62060c9e641cd54c400193ac839aa9881af47150735531001c3fc3acb29e2000a5f8359653c400117f08bb2a7880062f2117654f1001c5fc3ac921e200087f855d943c40050f90abb2878800a1fa177358b100043ec2ee6b1620018be84dcd62c400117b09b9ac58801a1f6177654b1001e5b38ac921620068bd84dd942c400d1b906bb665880ee3761e638cb1001e6b38cc71962003cd67158e32c400d1bb07bb2658810237e1d630cb101547bc32e21962000ad683dd921c400d5cd0531a438800eb9a1b32487102076231e6490e2003ae4860c921c4001d8cc619243880af39188704871001e5a38ac8a0620348df8758f30c406b1bd0f31a618800f351c6634c31001e6a38ac69862000cce631c930c400199ac6392618800237a0e76552100046ec1cecaa420008df835d954840011b906bb2a9080023be09765521003476412ecaa4200187e87d95548400347d09b2aa90800a2fa1f64552100151f42ec8aa42000c5f651cd54840c98b8ca39aa90800327d9073552103064e320e6aa4206ad1c541cd548400187eebba2c7080030f1d77458e100061fba8e8b1c2000c3c751d163840018deebb92c7080031b1d77258e1000657ba6e4b1c2000cac74dc963840018deea392c7080031b1d47258e1000657ba0e4b1c2000cac741c9638400199ee6392c7080031ddd77158e100063a3aee2b1c2000cb774dc56384001968e9b8ac70800339dcb7158e1000672396e2b1c20008df8758c638400159904b18c7080022fe117694e1000c5e422ed29c2000a5d83d96538400317d093b2a7080022f6127654e100045fc22eca9c20018bc845d953840011df04bb2a70801a3b2097654e100043fc2aed21c200287c855da43840050fd0b3b287080021f6167650e100043fc2aeca1c200287c855d943840011df04bb2870801a3b2097650e100045fc22e7b1420018bc845cf628400187eebba2c5080030f1d77458a1000
  | 15 => 0x8bb4429800e3d20576885300043e432eb10a6000c3c645d6214c0b78d8c4bac429800f1d18575885300043fc3ecb10a600087d87d96214c00187ce9b2c42980022f21974885300061fb2ae910a6000c3c655d2214c0af958c4ba4429800f2d18574885300045fc3ec910a60008bd87d92214c00187cebb2442980030f5d764885300062fb2ce710a6000c5c659ce214c00193ec939c429800327192738853029e66314e710a6003cd4619ce214c0018becab9c42980031719573885300064fb22e710a6000c9c645ce214c0a5998c4b9c429800f351857388530006373aec510a6000c6d75d8a214c00195ce9b1442980032b5d362885300066739ec510a6000c7675d86214c0018eaebb0c42980032d9d361885300065aba6c310a6000cd673d86214c0019aae7b0c42980d6b5a1b31885300066b3b66310a6053ec462cc6214c00317d09bb242980022f61376485300046f434e690a6040cd4619cd214c0779a8c2b9a429800276201734853003573416c290a6000ad686cc5214c0019a8ed98a429814fb118b31485300045fc22ec10a60018bc845d8214c06b1bd0d398429800f35186730853001e6a30ae610a6000ae686484214c0015c90c9084298003399d9210853001e723b24210a6000ea764484214c0b3d48c89084298003719cd21085300062e32ee6a026000c5c651cd404c00193ec839a809800333dcc625013000666398c4a026000cd773185404c0019a8e630a809803f279db648c13000e4f3b0c91826000e1c65192304c06b1b90cb8c60980d735185718c1300072bb28c31826000e5465186304c001d2ec830c6098003a5190618c13000763b10c31826000ec462186304c06b9ab0e30c6098003355c8618c1300072db2ec118260008de839d9540c0c31bf06bb2a81800e3da0476550300047ac08ecaa060028bc87591540c0054790ab22a8180023761873550303064f320e6aa06000c9d641cd540c0d9a38a839aa81800f1d985751843001e5b30ae83086003ce6615c8610c0011ef0eb08c2180031d5d561184300065aba2c23086000ce572584610c0071ed033b4a2180022fe11765443000c5e422eca8860018be841d9510c00117b083b2a21801a3ba08765443000476c10eca886000c5d651cd510c0051e90eb0aa21800e3da0676904300043fc2aeca08600287c855d9410c0050fd0a3b282180021f614765043003477410eca0860008ed821d9410c00193ac839a82180063d21d61504301a6e218ae51886051ccd869ca310c06999ec339462180d333586728c4301ae67304e518860518df8758a310c0a399ce4b14621800237e1d620c43028e67392c418860519cc825c0310c069ba020b80621800e3da06768843001c6ec1aed1086003c76615d6210c00796cc2ba442180d27520573884300063abaac31086000cb
  | 16 => 0x185300053bc2a6030a6000a74854c0614c00156f08980c298002ad211301853000573c126030a6000ae4824c0614c00117f08bb4a2980062f211769453000477c12ed28a60068ec825da514c0071e902bb4a29800317d9673945300064e324e728a6003cd4619ce514c0018becab9ca29800327191739453001e6a30ae728a6000cce7318a514c00199ae6314a2980062fa1376545300045ec26eca8a60068ee82dd9514c0011db05bb2a29800a3da1f61545300043fc2aed20a600287c855da414c0011df04bb4829801a3b209769053001c7a40aed20a6000c5c659ce414c00193ec939c829800f3518673905300062e32ae720a6003cd4615ce414c00199ce63148298003335cc62905300143f42eeca0a600087d85dd9414c00d1dd05bb282980023b60b765053000c7b43ec2a0a6000cd7819db314c0018bcedb2e6298003179d865cc5300064f3b6c998a6000c9e76193314c001c38ca326629814e3721972cc53029e66312e598a603bcd4615cb314c00199cedb166298003339d862cc53000727b28c598a6000e4c6518b314c001d1ec83166298003a319062cc53029e66c38c598a6053ec68118b314c0a7d8b023166298003359db61cc53000762316c398a6000e5765187314c001ca8ca30e6298003a5d9061cc5300074a320c398a6000ec762187314c001d88c430e62980033318a70cc5301ae6a30ce198a600087c865d6314c001878c8bac629800f1d185758c5300043ec3ecb18a6000c3e74d96314c0011790cba462980030fd95748c5300061e32ae918a6003cb4615d2314c00117b0fb2462980030f9d7648c5300061ebaec918a60008ee869ca314c0018decb39462980031b196728c53000657b24e518a6000cac649ca314c0079c8c339462980023b219728c53000637b2ae518a6000c6c655ca314c00195ec8b9462980032b191728c53001e7230ae518a60008ed87d8a314c0018dcebb1462980031b5d7628c530006573a6c518a6000cad74d8a314c0011db0e31462980031b9d4628c53000636ba8c518a6000cae7418a314c00195ae831462980031d9d7618c5300063abaec318a6000cb674d86314c00196ae9b0c6298003399cb618c53000672b96c318a6003cf0619c2314c0019e6c2382629800387194644c5300046f436e498a6052ccc62dc9314c0819a8c3b92629800393d94624c53000726328c498a6000e8f64189314c001d18c8312629814b33a1c624c5300056b436e298a6000ec462dc5314c0075ad0db0a6298003b118b614c5300072bb28c298a6000e5465185314c001d2ec830a6298003a5190614c53000763b10c298a6000ec462185314c001998c4382629800374dc4704c5300143e42ced10a60018bc849da214c0071b9073b442980021fe1576885300143e42aed10a60008bf845da214c0031790
  | 17 => 0xa6000c3e75192614c00187aea324c2980031bd9672985300063632ce530a6000caf649ca614c001958c9394c2980d733d8e729853001e7230ce530a6000c6f655ca614c0018d8cab94c2980032bd91729853000656322e530a6003ce4615ca614c0018dcebb14c2980031b5d76298530006573a6c530a6000cad74d8a614c0018ecebb0cc2980031d5d761985300065b3a6c330a6000cb574d86614c0019cce5b0cc298003395cb61985300043f43ecab0a6000c3c74d95614c0010fd0e32ac2980030f1d065585300061fb2ee8b0a6000c3c65dd1614c00117d0fb22c2980030fdd764585300061e3aec8b0a60008be87191614c00187eea322c2980030f1d4645853000637b2ee4b0a6000c6c65dc9614c00195ec9b92c2980032b193725853000637b28e4b0a6000c6c651c9614c00195ec8392c2980032b190725853000637baec4b0a6000c6c75d89614c00195ee9b12c2980032b1d362585300047bc3ac230a6000a7785584614c0014e90ab08c298002ade1161185300055a422c230a6000ae782584614c0015c904b08c2980031d9db65185300047ac3cca30a6000ab684994614c00156b09328c298002b9a0a651853000572c14ca30a60008f787594614c00156f08b28c298002ad211651853000573c12ca30a6000ae482594614c0018ecec328c2980032d9db64185300071bb2ec830a6000e3465d90614c0011eb0f320c2980029da1664185300053ac2cc830a6000ae682990614c0015cb05320c2980023de1d64185300053bc2ac830a6000a7485590614c0015cf04b20c298002b920964185300065b3b0c830a6000e3765190614c001c68ca320c29800395d9573185300072a32ae630a6000e97645cc614c001d28c8b98c298003399db621853000733b2ec430a6000e6465d88614c001d4ec9b10c298003a9193621853000763c1ec430a6000ec573d88614c0011eb0f310c2980029da1662185300053ac2cc430a6000ab684988614c00156b09310c2980023de1d62185300053bc2ac430a6000a7485588614c00156f08b10c298002ad211621853000753b20c430a6000ea464188614c001d8ae6310c2980038dd5254185300056bc1aa830a6000ad483550614c001c6aa82a0c298002b5a0c54185300056ac18a830a6000e575394c614c00156f08a98c298002ad21153185300055b420a630a6000ab58414c614c001caaa6298c2980029de1543185300053a42a8630a6000a768510c614c0014eb0a218c298003a550c43185300055b420a430a6000ab584148614c0015ad06290c298002b560c52185300053b4288430a6000a7585108614c0015ad06210c298002b560c42185300055b426a030a6000ab584d40614c0015ad07a80c298002b560f50185300053b42e8030a6000a7585d00614c0015ad07a00c298002b560f4
  | 18 => 0xc0018b8ebb9ac8980031bdd77259130006363aee4b226000caf74dc9644c0018deea392c8980031b1d4725913000657ba0e4b226000ccf731c9644c0018eeebb8ac8980031d1d771591300065bba6e2b226000ce772dc5644c0019c8e5b8ac8980031ddd471591300063a3a8e2b226000cb7741c5644c0019aee638ac89800339dc8715913000672390e2b226000c3e76d94644c00117b0f328c8980028fa16651913000557414ca3226000aad82994644c00156d03328c898002ad60665191300045fc3aca3226000aaf82594644c00155904b28c898002ade0565191300055a40aca3226000c3e76194644c0071ed03bb2a8980023d60776551300061e2a4ecaa260008bf845d9544c0011bf06bb2a8980023de05765513001c7a40aecaa26000c3c541d9544c0c11b9063b2a89800a2fa1f64551300151f42ec8aa260008de86dcd544c0018becbb9aa8981872719373551300064fb20e6aa26060c9c641cd544c0dba38a839aa8980021fa1b7550d302461e326eaa1a606087e87d95434c0910f90fb2a86980038710f6550d300061fbaec8a1a6000c3c75d91434c00353d07b2286980032ed907050d300043fc2ae5b0a600287c855cb614c00117f08b96c2980062f21172d85300055b420a3b0a6000ab584147614c0014ed0a20ec2980029d61441d85300055b424cbb0a6000ab584997614c0015cd0532ec298002b960a65d85300055bc22cbb0a6000ab484597614c0015cf04b2ec298002b920965d85300071bb2ec9b0a6000e3465d93614c0014ed0b326c2980029d61664d853000573414c9b0a6000ae582993614c0014ef0ab26c2980029d21564d853000573c12c9b0a6000ae482593614c001c6eca326c2980038d19464d853000753b26c5b0a6000ea464d8b614c00156d093aec298002ad61275d85300053b42ce9b0a6000a75859d3614c001c6ea92a6c298002b5e0d54d85300056a41aa9b0a6000e3554153614c001caea729ec298002ade1153d85300055a422a7b0a6000ab68414f614c00156b0829ec2980029de1543d85300053a42a87b0a6000a768510f614c0014eb0a21ec298003a550c43d853000673b94e5b0a6000a77855cb614c0014e90ab96c298002ade1172d85300055a422e5b0a6000ad7835cb614c0014ed0a396c2980029d61472d85300055b420e5b0a6000ab5841cb614c0015ab06396c298002ada1052d85300055ac20a5b0a6000a768510b614c0014eb0a216c2980029da1770d85300053ac2ee1b0a6000ab684dc3614c00156b09b86c298002b9a0b70d853000572c16e1b0a6000ab684d43614c00156b09a86c2980029da1740d85300053ac2e81b0a6003c74615d6614c00187ce9b2cc2980030f9d065985300061fb2ae930a6000c3c655d2614c007968c2ba4c2980030f9d764985300061ebaec93
  | 19 => 0xa2fe1d65901400054e41acb2028055aac82596405009956902b2c80a00062f21972901402ae56312e520280018bc865c64050099968c2b8c80a000e3da0676553300047ac0cecaa660028bc8759154cc0054790ab22a9981832799073553300064eb20e6aa6606fd1c541cd54cc06999cc7394c39800f39185729873000573416c330e6000ce572d8661cc0050fd0bb92c3980021f617725873000c5f426e4b0e60008bd84dc961cc0011ef0eb08c3980062fa1276947300045ec24ed28e600387e87d9551cc0050fd0b3b483980021f61676907300064eb24e720e60038be87d9141cc00756d03b22839800237e1972cc73029e67312e598e6000bc58298731cc0a51bb0db92639814b3398b724c73001c7a40aed10e6053cce629ce21cc00199ce6b144398003355db318873029f633166310e60018be84dd921cc00117b09bb2439800335ddb314873000c5f424ec10e60008bd849d821cc0691bf0cb984398002b9e19210873000572c324210e6000ce67648421cc001b8ce690843980032759073503300143fc3aebb246000c5e755cf648c00147d0bba2c9180030fdd754592300061e2a6ecaa460008bd849d9548c001878a8bb2a91800a2fa1f64552300151f42ec8aa46000c9f641cd548c0c1938c839aa9181bb47150735523014d1f42ec921c6000c3c75591438c0079ccc2b90c3180d7710c572186300047bc3ac230c6000ce572584618c0018bacbb9aa31800ead205645063001e7330ae518c6035dc4315ca318c0019cae4b0c63180d7740c6708c6302a667434e518c6054ccd869ca318c06b99ec339463180d733586728c6300046fc3ac518c6054cce7258a318c0a91bf0eb106318153339c9620c630004eac3ec218c6000bd280d84318c0a939904b80631800e3da0676886300066ab9ac310c60018be841d9218c00117b083b2431801ab9209614863000762b106290c6003ce776484218c0019caec90843180d7711cd21086301ac6fc3ac39846035cd671587308c00187aebaa6c898002aba0a65d913000556c14cbb226000ab681997644c00156b0332ec898002a760f75d91300061fbacebb226000c3d751d7644c00147d0bb9ec8980028f61773d91300070f29ea7b2260008be8714f644c01f17b0e29ec8980028fa1672d91300051ec2ce5b226000a9d831cb644c00117d0e296c8980022f61c52d91300051f42ce3b226000a3d859c7644c00153b0638ec8980022fa1c51d91300045ec38a3b226000a3f855c3644c0014790ab86c8980022fa1f50d91300045ec3ea1b226000e3a50d43644c001878c9baac8980031bd97725913000656326e4b226000c6f651c9644c001958c8392c8980031dd9771591300065a326e2b226000c77651c5644c001968c838ac89800a1fa1f75591300061fbaee8b226000c3c75dd1644
  | 20 => 0x3f42ced98c800087d859db319000193ae931e632000eb5205634c64001c77414ed90c8000cad7458b21900071ed033b443200032d5d161886400143f428ec90c800087d851d921900011bd063b243200023760c764864001d7240ac490c8006ae48258521900079ceec9084320003395d921086400061eb2ae92848002a3f86552509000387aecaa4a120002c720d54942400059dc02a928480018be849cf65500018b8ca39acaa00031b19472595400063a328e2b2a8000c9f741cd65500018bea239acaa000327d0473595400064e200e6b2a8000cd773dc565500019a8e7b8acaa000339dcb71595400063bba8e2b2a8000cb7741c565500019aee638acaa0003351cc715954000673b90e2b2a8000ce4721c565500018baeba9ec6a0002a761053d8d400046fc3ac631a8000a5c8558c635000159904b18c6a0002b52056318d400054ec20a631a8000a5d83d965350003179083b2a6a00021fe1573d89400143e42ae7b1280008f7815cf62500071e902b9ec4a0002ab61052d89400043fc2ae3b12800287c855c762500011bf06b8ec4a00023720d71d89402ae1fb22ea31280008ef8758862500014d90ab10c4a0002b320d62189400057240ac43128000c3f655d2525000d55d0db1284a00022fa1b715094027e5a30ee2a1280308be861c1425000d179093b464a0003179d7638c9400062f3a8c71928000c9d7418e32500019aec738c64a00033518e718c9400043fc2aec192800287c855d832500011ef02bb064a000e3d205760c94003656312e81928000c9d7418c32500010ff0ab9ec2a000a1f21573d854000477c12e7b0a80068ec825cf61500010ff0ab96c2a000a1f21572d85400046fc1ae5b0a80008dc835cb615000156b0828ec2a01330fd9175185400047bc3ac230a8000a748558461500015a906b08c2a0002b920961185400061fb2ae928a800387c8759551500014b906b2aa2a016e9b209655454001d3a40acaa8a80038bc87595415000153906b2a82a015eab209655054001d5a40acaa0a80008be86dc941500af958c5b9282a000eada1b615054004c5f430e0a0a80038bc849da31500018bcebb1c62a0003179d4638c5400064eba0c718a8000ccf639ca3150001998c739462a00021fe15760c5400143e42aec18a80008ef825d8315000d1d904bb062a000f2d185740c5400064eba0c618a80068bc849db215009f968c2ba642a01033518673c85400063b3aec390a8000cd673d872150007179093b442a015f2b189748854029e66314e710a8000c6e75d8a215000199ce7b1442a000a1fa1476485400043ec28ec90a80009b8805d121500010ff0abb042a000a1f21576085400046fc1aec10a80008dc835d8215000d958c4ba042a000f2d1857408540005734324210a8000ae486484215000187ecbba2a0a00
  | 21 => 0x841c1210840174b083824210802f1a0c7048421005e2c18e0908422b9e7861c121084573cb0c3824210803396187048421006d3420e09084200da5841c12108401b8d0638242108037160c704842100673318e0908422bce4631c12108457bc4c038242108af7858070484210045fc22e730042018bc845ce600840317d0fba2c0108030fdd774580212ae56396e8b00424ccb471dd1600840187eea3a2c0108030f1d4745802134656390e8b00424bcb4711d1600840193ee9b9ac010803271d373580211ae6a38ee6b004200c9f741cd6008401938e839ac0108d3351c473580211a66b108e6b004251cd5211cd60084699a82039ac01080339e1d21580210057243a42b004200ce4874856008401d4ee890ac010803a91d1215802100763b9a42b004200ce4734856008401d88e690ac010803311cd215802100771c0242b004200ae4804856008401dc10090ac010802b8201215802101f71b8242b004200c5e659cf65900014bd07baacb2000a8fe19655524032e4fbb6e6aa48065e1e65dcd54900c987cca39aa92019327dd873552403068fba8e6aa48064e1e651cd54900e193d0c39aa9200032761873552403868f428e6aa48060d1d851cd54900c993cca39aa9201c34799473552403260f328e6aa48000d1d651cd54900c9938ca39aa9201c347d4873552403868fa88e6aa48060c9e601cd54900c1b34c039aa9201c34714073552401b45ec36e0aa48000d98731c154900014bd0bb1cc720002a76105398e403245e43aa8b1c8002c3e75551639000153906aa2c72000317dd75358e400054ec26a6b1c8000e1d54d4d639000153b0829ac7201b7879505358e400046fc3ac631c8000a5f8359653900032790eaa2a7200030fdd95454e400058e41aa8a9c8029c3e65dd643900c133d07bac87200462fe1d6390e4009c5fc32e121c800093f855c2439000587ceaaa2c520002a720d5458a400143f42ee6b14800087d85dcd629000193887b9ac5200023be1d6218a4003673312e23148000ce5625c4629000187acbba2a5200064f21d5454a400151fc32a8a948000c3f76551529000163906aa2a5201a22fe197090a400049fc2ae1214800287e85ddb32900010fb0bbb6652000e3da0776cca400047ac0eed994800287e859db32900010fb0b3b66520003275d263cca4003566412c69948002c3e75551619000153906aa2c32000a1fa1773586400043ec2ee6b0c8000c9c43dcd619000117d0f212c320132ada06425864001e7330ae430c80008f78758461900019cae4b08c3200030f597745464000c9e43aa8a8c8002a3f86551519000187eecaa2a320002c720d54546400045fc3ac520c8055cae7258a419009717f0cb8483200024fe1570906400143f42eed98c800087d85ddb319000d1dd05bb663200023b60b76cc640014
  | 22 => 0xb1e65108031d59571cca210065ab22e399442069d4835c732884019acc6b8e651081ab5205634ca210066ab1ee29944203ad5835db31884075af0eb1e631080f35e1d63cc6210043fc2ae7304420287c855ce608840117f08b9cc1108062f21173982210043fc2ae1b22420287c855c364484011bd073b2a8908023760e76551210046fc1aecaa242008dc835d954484011f700bb2a8908023e20176551210145e43ac8aa24202a3c8559154484c193cc839aa89080327590735512139e8e2a0e6aa242068f686dc5544840d3cd05b8aa8908030f9d674d8d210061f3aae9b1a4200c3d755d363484018eceab8ec6908031d5d571d8d210065b3a2e3b1a4200cb5745c763484019cae4b8ec6908062fa127618d210046fc3ac631a42008bf845c0634840317908b80c69080a1fa167690d210043ec2ced21a420287e859d943484010fb0b3b286908022f6127650d210043fc2aeca1a420287c855d943484011f700bb286908023e2017650d2101c77436e4a1a42039e681dc9434840d1ed0db8a869081a79a0b7150d211dc6ec3ec798a42039e587ccb314840d9cced9966290803b1d8f32cc5211547a432e198a42408de8718d314840d3cd0539862908eef160a630c5210047bc3ac618a42009d78758c314848178f04b18629081a7561f320c52101d734366418a4206dc687cc8314840db8b0f9906290903b1a1b320c52100762c366418a4200dc676cc83148481d8ced990629094e75e1d320c521036e23926418a4253dc6730c8314840d3c904b80629080371cc9700c5210047dc3ac03024200c3e759d0604840187ceaba0c0908030f5d574181210064f3a4e63024200c9d749cc604840193ce8b98c090803275d173181210066bc0ae63024200cd4815cc60484019aae7988c0908aab9a0b3118121007639906230242008df835d954084011b906bb2a81080e2f21d64550210151e42ac8aa04260c9e641cd540840193ac839aa8109cb47150735502101c5fc3ac9218420087f855d943084050f90abb2861080f39a1f764842100753426ec9084200ea584dd921084015cd07bb24210803b1a0f76484210056341eec9084200ec583dd921084015cb01bb24210802b9e19744842100573c32a89084203ae48655121084b3e48a8aa24210802f1e0d5448421005e241aa89084259ba684dcd210840174b09b9a4210802b961a73484212076231ce69084200ae7865cd2108477d88c6b9a4210802b9a1e63484210057243cc69084203ae68398d2108407d8d0731a4210803b1dce63484210076239cc69084200ae58098d21084015cf0ca1a421080eb92194348421005b3c2a869084271b648550d21084b3f0886a1a4210802b961a704842100573c32e09084200ba7845c121084b374908b824210802f1e0d7048421005e241ae09084259ba6
  | 23 => 0x98e2129d67410eb31c4200acd821d663884014bf0aba4c710802972157498e210052f428e931c4200a5d851d2638840193ae83a4c71094eb3a087498e2100566c10e931c4200e1f5495263884011bf0eaa4c7108023721d5498e210070eaa0a931c4253ace82152638840159b042a4c710802b360b7098e210052fc2ae131c4200a5c855c2638840153f08b84c710802a72117098e2100567c12e131c4203ad4815c263884075ad02384c710802a7a135098e210054ec26a131c4253ace82d42638840159b05a84c71080297a174098e210052ec2e8131c4253ace82d02638840159b05a04c71080e37a1f5358e210062fbaea6b1c4203ad681d4d638840153d0829ac710802a76105358e2101c6f43e86b1c4203ad681d0d63884014bd0a21ac710802976144358e210062fbaceab1c4203ad6819d563884015ab033aac710802a7e117558e210054e422eab1c4203ad4815d5638840153d083aac710802a76107558e2101d6b40ce8b1c4200ad5819d163884014bf0aba2c710802972157458e2101d6a40ae8b1c4200a5e851d163884014bb0a3a2c710803275d07458e210070faa4a8b1c42008df8755163884011b90eaa2c710803875505458e212066a38ee4b1c423bcd4715c963884075ad03a92c710802b56075258e2101d6b40e84b1c4200ad581d0963884075ad03382c71080297e157058e210052e42ae0b1c4200a9f845c1638840153908b82c710802b3e097058e2101d6a40ae0b1c4234cd4711c1638840153d09a82c710802a76135058e2101d6b408a0b1c4200ad58114163884014bd0ba02c710802976174058e2101d6b40880b1c4200ad58110163884018bea7bb4a71080317d4d7694e2101c3fc3acb29c4200a5f835965388401c3ea6b24a71080e3761e6394e210152f42cc729c4202a5e8558e538840317909bb2a7108022fe117654e2100c5e422eca9c42038f4815d953884070f90eb2aa7108030f1d16554e210045ec36e8a9c4229c3e65dd1538840187acbba2a7108022fa1d6454e210045e43ac8a9c4200c9f7498d5388401938e931aa71080e3721d6354e210064fba2c6a9c4200c9c7458d53884018eacbb8aa7108033558f7154e2101c5fc3ac921c42038dd8798e43884050f90bbb287108032710f7650e210043fc2aeca1c420287c855d9438840193886bb2871080e3d2057650e210043ec36eaa1c4248c3e64dd543884010fd0eb2a87108021f21d6550e210070e21acaa1c42038bc87591438840187eeab2287108030f1d56450e210054e41ac8a1c4200c5f7598d43884018b8eb31a8710806a72126350e2101c6e43ac6a1c4200c5f7558d43884018b8eab1a8710806a72116350e210065ab26e2a1c4200cd563dc543884018eacbb8aa5108032d5937150a2101e3b38acb9944203cb671593328840d5a902
  | 24 => 0x6200cd77694d310c4019aeeca9a6218802e5e11534c431005abc2a869886200ad7864c9310c401b8ee499262188021fe1572980310143e42ae530062008bf845ca600c40317908b94c01880a1fa1f75580312763a38eeab00624dc74711d5600c40317d0fba2c0188030fdd774580310061e3aee8b00624ccb471dd1600c40187eea3a2c0188030f1d4745803125e5a388e8b006200c6f75dc9600c4018d8ebb92c0188032bdd37258031006563a6e4b00622fce471dc9600c4018deea392c0188031b1d4725803100657ba0e4b006200cac741c9600c4579c8e2392c01895237a1f32580310366639664b006206ccc724c9600c4070fd0f2a2cb108030fdd2545962100c5f420e6b2c42008bd841cd658840317d09b82cb108022f61370596210061fba4e8b2c4200a5f835d165884014b906ba2cb1080e9d20574596210061eba0e8b2c4200c5f739cd658840147f08b9acb108028f211735962101d3a40ae6b2c4200a3e841cd658840147b0839acb1080e9da0743596210053ac0e86b2c420087e8710d65884010fb0e21acb1080e9da0742596210053ac0e84b2c4200a3e84dc1658840147b09b82cb1080e9da06705962100537c12e0b2c420087e87d0165884010fb0fa02cb1080e9da0440596210053ac0880b2c42038be87d51648840187eebaa2c91080a1fa1473592210043ec28e6b24420287e85dc164884010fb0bb82c9108030fdd675592210054fc1aeab244200a9c835d5648840756902baac9108030f5d475592210051fc2ae6b244200a3c855cd648840756902b9ac9108028fa1473592210051ec28e6b244200c9d731cd648840756d03a9ac910802ad60753592210045f438a6b2442008bd8714d648840756d03a92c910802ad60752592210051f42ee0b244200a3d85dc1648840756d03382c910802abe0970592210045f43ea0b2442008bd87d41648840756d02282c910802ad60450592210061e2a6ecaa44200c3c545d954884011bf06bb2a9108023720d765522101c7a40aecaa4420387c87595548840347908b2aa91080e2f21d64552210151e42ac8aa442008dd86dcd54884cb8bccbb9aa91080317597735522130e4f326e6aa44200c9d64dcd54884011bb0c39aa9109931799473552210062eb28e6aa44260c9e641cd548840193ac839aa9109d34715073552210063ab2ee2aa44200cb564dc5548840117f08bacc7108062f2117598e210043fc2ae931c420287c855d263884071bb0e29cc710802a7a105398e210054ec20a731c4200acd8214e63884071bb0e21cc71080297a144398e210052ec288731c4200c9d7410e638840159b0421cc7108021fe157098e210143e42ae131c42008bf845c2638840317908b84c71080317dd67598e210054fc22eb31c4200a9c845d6638840153d083acc710802a761075
  | 25 => 0x40155d0829ac518802ab6105358a3101d7340e86b146200ae581d0d628c4014df0aa1ac5188029b2154358a3100573c0a86b146203ae48150d628c4014dd0a21ac5188029b6144358a3100746a1886b146200a6f855c1628c4014d90ab82c518802abe117058a3100556422e0b146200acf835c1628c4075c902b82c5188029ba147058a3100536c28e0b146200aae841c1628c40155b08382c518802b360c7058a3101d73408e0b146200aae84d41628c40155b09a82c51880eb9a045058a3100572c08a0b146200a6e85d01628c4014db0ba02c51880eb9a044058a3100572c0880b146200c5d659ce528c40193cc939ca51881b3398a7394a310062eb2ae72946200c9e645ce528c40d99cc4b9ca51880e3b21d6254a310062f32ce72146200c9d649ce428c40d99cc539c8518803179957390a3103667312e721462038ec87589428c4a999cc538665188022fe19748ca310061f32ae91946200c3d655d2328c40d95cc4ba465188022fe1d648ca310061f3aac91946200c3d75592328c40796ce2b2465188031d995718ca310063ab2ae31946200cb6645c6328c40196ac8b8c651881b39989718ca3101f6339ac598c620087f855ca608c4050f90ab94c1188022fe11729823100c5e422e53046200c3d74953654c40117f08b86ca988062f21170d953100c5f43ee8b2a6200c3f751d1654c401938e9b9aca988030f5d754d91310043fc2ae1b22620287c855c3644c4050fd0fbaac8988030f1d774591310062e3aee6b226200c3c549d9544c4010ff0abb2a8988022fe1176551310046fc1aecaa26200c3c541d9544c4030f90eb2aa8988068f21165551310145e43ac8aa26202a3c85591544c4071bd0db9aa89880e75a0773551313262f328e6aa26200c5d651cd544c4c193cc839aa8988032759073551313b68e2a0e6aa2620387f87596534c49147908b2ca69888697e0d6594d310061e3a6caa9a62038bf87592434c4534790ab2486988030f1d76450d3100477c3ac43126200c5f65dcd524c4073ad03b9aa49881aaba0b645093101ceb40ee6a126200ce7625c6324c40d9c8c4b8c649894b710c9718c9311a46e432e11926200c5f65dcd514c401d8ec519662988023ee1d60181310046ec3c643026234ad6818c8604c4070f90eb2aa8188068f211655503101c5e43ac8aa06202a3c85591540c4011bb0c39aa8189931799473550310062eb28e6aa06260c9e641cd540c40193ac839aa8189d7471507355031004eac08e6aa06202a5f83596530c40796ce2b24861880a1fa1470588310043ec28e0b1062018be841c1620c40117b08382c41881a1f617765483101e5b38ac92106200c9d649ce420c40d17b09bb2841880f399c562cc8310046ec34e1990623bcd681dd9320c4779ac43bb26418802b5e19714c8310066bbb2e299
  | 26 => 0xe1fa1e54596310061fba4a8b2c62018be84dc1658c40117b09b82cb188030fdd274596310052fc1ae8b2c6200c3d741d1658c40147f08b9acb188028f211735963101d3b40e86b2c6200a7581d0d658c4430fd0e21acb188021f61c43596310052ec1ce4b2c6200a3e841c9658c40147b08392cb1880e9da0742596310053ac0e84b2c620087e87109658c4010fb0e212cb188028fa1370596310051ec26e0b2c6200a5f835c1658c4010fd0fa02cb188021f61f405963101d3b40880b2c6200a7581101658c40717d0faa2c9188030fdd754592310143f42ee0b24620087d85dc1648c40187eeb3aac918802a7e0d75592310061eba8eab246200a3f855cd648c4014790ab9ac91880eada0753592310055ac0ea6b2462208be8714d648c40117b0e29ac918802a760e72592310051f428e4b246200a3d851c9648c40756d03a92c918802ad60752592310045f438a4b2462008bd87149648c40147d0bb82c9188028f61770592310054fc1ae0b2462008be87d41648c40117b0fa82c91880eada0450592310055ac08a0b246200c3c54dd9548c401878a8bb2a91880e1f21d655523100d1e422caaa462038bc87591548c4054790ab22a9189971799773552310062eb2ee6aa46261c9e64dcd548c4c98bcca39aa9188031759473552313064f320e6aa46200c9d641cd548c4efa38a839aa91880387d4d6494e310061e3a2caa9c62008bd86dd1538c45387ccbba2a7188030f5977454e3114c5f43ac8a9c62648bc87591538c4018eacbb8aa7188021f61b7550e312461f326eaa1c624887e87595438c4c10f90eb2a87188038710d6550e310061fbaac8a1c6200c3c75591438c40196ac9b8a87188038bd525498a3100567c1aa93146200acc83552628c401c5aa82a4c518802b3a0c5498a3100566c18a93146200e4f5394e628c40155f08a9cc518802ab2115398a3100557420a73146200aad8414e628c401c9aa629cc5188029be154398a310053642a873146200a6e8510e628c4014db0a21cc518803a350c4398a3100557426a13146200aad84d42628c40159d07a84c518802b360f5098a310053742e813146200a6d85d02628c40159d07a04c518802b360f4098a3101d7340ea4b146200aae84149628c40155b08292c51880eb9a074258a310053742884b146200a6d85109628c4050fd0a382c5188021f6147058a3100c5f420e0b1462008bd841c1628c4075cd033aac518802b96067558a3100557420eab146200aad841d5628c4075cd033a2c518802b96067458a3100537428e8b146200a6d851d1628c401c5ea92a2c518802b3e0d5458a310056641aa8b146200e2d54151628c477d8862b9ac51880eb9a075358a3100572c0ea6b146200e4f5394d628c40155f08a9ac518802ab2115358a3100573c0aa6b146203ae48154d628c
  | 27 => 0xe42ae730482008ef825ce609040d1d904b9cc1208021fe1572982410143e42ae530482008df835ca60904011b906b94c12080a1fa1f75582410061fa16eab04824ec3f41dd5609049d87a83baac1208030f10375582413445e43a84b048200c3f75509609040317908b86caa08031719473595410062fba8e6b2a8200c9f741cd655040547d0db2aa8a0997271db735514132f0e32ee6aa28264c3c651cd54504c9938ec39aa8a098347dd473551413270e328e6aa28200c9e861cd54504f393b0c39aa8a09e747a1473551413068ec28e6aa28200d1f651cd54504c993cca39aa8a09932719473551413ce8e328e6aa28264c1c651cd54504f3a3ea439aa8a098327d847355141306cbb08e6aa28279d1f511cd54504f3a38a039aa8a0803651cf7155141006cbb98e2aa2824b8be86dc154504c917f0eaa6c6a080b0f1d554d8d410054e41aa9b1a8200c5d75d4f635040153b09a9ec6a08038755353d8d410056ac0ea7b1a8200a9d8414f63504efc3ca829ec6a080237e1d6318d410052e42ac631a8200a9d8414c63504010ff0ab80c6a080a1f2157018d4100477c12e031a82068ec825c063504014bb07b2ca6a080e6da077454d4100c9e43aa8a9a8200c3c76551535040163906aa2a6a080e2fa1b7590d4114e1e32eeb21a826099e83dd6435040736d03bac86a087a2f61f6390d4101cdbc3ae321a824b8bc865c2435040127f0ab8486a080b0f1d554d89410054e41aa9b12820087f855cf62504050f90ab9ec4a08032710d73d894100477c3ac431282038bd849da525040187ecbba2a4a080e6da0774549410151e432a8a928200c3c76551525040163906aa2a4a092e2f21970909410049fc2ae12128200c3f65dd151504072790eaa2a2a080e8f219545454100e1e3b2a8a8a8200b1c83551515040766902aa2a2a08023ee1d60181410161e3aaa83028200a9c8355060504010ff0ab98c0a080a1f21573181410064e21ae630282008bd87908605040317d09b82cb988022f61370597310143f42ee0b26620087d85dc164cc40d1dd043b2a9988023b608765533100c3e43acaaa66201a3c8459554cc4051790eb22a99880a8f215645533101c6ec30e6aa66264c5e651cd54cc4018baca39aa9989832799073553310064eb20e6aa66278d1c541cd54cc4018eacab8ca79881b1b9897518b3103657312e831662008ef8758862cc4018daeab10c5988032b5d16218b3103477414ed2966206ce6625c652cc40117f08bb2a5988062f2117654b3100c5f420eca9662008bd841d952cc4018baca39aa59880a3b21d6254b3103477414ed2166206ce6625c642cc4010ff0abb2859880a1f2157650b310143f428eca16620087d851d942cc40193ac839a85988063b21d6250b310062eb28e6a8e6200c9d641cd41cc4011f70eb00c19880
  | 28 => 0x71956050cdd8bee632ac0a19b78710c655814300637b2ee4b028600c6c65dc96050c01b1887b92c0a18031bd94725814300636328e4b028600d8c431c96050c018eecbb8ac0a18031d1977158143006ca21ee2b028600c77651c56050c018e8ca38ac0a18036510c71581433670e218ca30286008fb875806050c05878eaaa0c0a1802a720d54181430043fc2ae4302860287c855c86050c010ff0ab88c0a180a1f21571181430064eba08731ca203ad681d0d63944014bb0a21ac7288032710f7650e510064e21aeca1ca20097581dd5439440317d09b9ac5288022f6137358a5101d7340e84b14a200a6d85109629440317d08382c5288022f6107058a510046f418e0b14a2008dd831c1629440187aeab2485288022fe11739825100c5e422e7304a2008ef825ce609440d1d904b9cc1288022fe11729825100c5e422e5304a2008df835ca60944011b906b94c1288062fa1f74582510061fa96e8b04a24cc3f51dd1609449987aa3ba2c1288030f14374582510064e320e6b22a201a3e86d9154544c38b8edb9aa8a89878719373551513061e320e6aa2a260c5c761cd54544c9a3ee839aa8a89838719073551510062f430e6aa2a27bc5d861cd54544f7a3d0839aa8a89934761073551510068fb20e6aa2a260c5e641cd54544c18b8c839aa8a89ef4719073551513060e320e6aa2a27bd1f421cd54544c98bec239aa8a899355d8473551513de8fa08e6aa2a27bd1c401cd5454401aa8e7b8aa8a880355dcc715515126c3f436e0aa2a26087f875536354403878e8aa6c6a88029720d54d8d510052ec2e87b1aa200e1d54d0f63544014bb0a21ec6a89eb87d5043d8d510046fc3ac631aa200a9c8458c63544014bb0a218c6a8803275d04318d510045fc22e031aa2018bc845c063544011df04b80c6a881a3b2097018d510fc3ec3ec729aa21fa5d87d8e53544018bb0fb1ca6a89361f2197094d510049fc22e129aa20387e86dd64354491878c9bac86a899257a0f7590d5101cbb40eeb21aa200c9c439d94354401938863b286a880a4f21d5450d510061e3b2a8a1aa200b1c835514354403878e8aa6c4a88029720d54d89510045fc22e7b12a2018bc845cf62544018b8a6b9ec4a88023be1d621895101c3ec2ced212a200c3f75d91425440d55d05b2284a88068f21954509510061e3b2a8a12a200b1c8355142544011f70eb00c0a88070f1d154181510052e41aa8302a2008bf845cc605440317908b98c0a88031714d73181510054ec20a731c8200c5f75d4d63904075ad03a9ac720802a76105358e410052fc1acb29c820287e85dcd62904010fb0bb9ac52080eb9a075258a4100556c20a4b14820287e851c162904010fb0a382c52080237a0c7058a410046ec18e0b148200c3d655d2529040117b0c38285208021fe1573982410143
  | 29 => 0x1ec0aa2238715063d81540068e2a4e7302a800d1c545ce605510f93ae831cc0aa21b8715063981540068e2a6e6b02a800d1c541cd60550011bd0fb1ac0aa00237a1c63581543864fba0c6b02a885e1c5418d6055001a68a9b8ac0aa00335d8f71581540066a31ee2b02a800d34541c560550019aec638ac0aa0033518c71581544270e2a0c6302a8008fb8758060550011bf06b88c0aa0023720d711815441f0e2a4e7b2c8600c7a505c36590c91878e9baacb21a0a97a0f75596430061eb2ae929c86008ef875886290c011ef0eb08c32180a1fa1f75582430061fa16eab048600c3f41dd56090c0187881baac1218023ee1d601824300637292e5b2a8600c7a505c36550c9147d09396caa18028f61272d954300636b90e5b2a8648a3e849c76550c0147b0938ecaa18031d5c471d95430051fc22e1b2a8648a3c845c36550c018f2e0386caa1a0717dd773595430151f436caaa28628c3c76d955450ccb938edb9aa8a19978719773551432445f430e6aa28660c3c651cd5450cc193ec639aa8a1983271d873551433068fba8e6aa28660e1c651cd5450c9133d0c39aa8a180327a1873551434068f428e6aa28660d1d851cd5450c01a3eca39aa8a19932799473551433064e328e6aa28660d1c651cd5450cc1838ca39aa8a1a0347d4873551434068fa88e6aa28680d1c501cd5450c0187ecbba2a6a18a70f1977454d430151e432a8a9a8601c3c765515350c0163906aa2a6a180a2fa1b7590d4314e1e32eeb21a866099e83dd64350c031790cbac86a18a70f1957590d433051f436cb21a8648d1e73d964350c91c3ec7b2c86a1983479cc6590d433ff0e218cbb128602c3c755536250c0153906aa6c4a18021fe1571d89430143e42ae3b12860287e859c36250c010fb0b386c4a18034710d75989433ee2eb98cb312867ee1c431966250c018eecb38cc4a18031d1967198943006ca21ce33128600c77655c66250c018e8cab8cc4a18036510d719894300673b12e33128606ce4625c66250c01a3887baac4a18021fa1f65589430043f438cab12867ec5f731956250cfbc388632ac4a19f38710c651894300477c3ac43128678e1c431976150c05878eaaa6c2a1802a720d54d85430043fc2ae5b0a860287c855cb6150c050fd0b386c2a18021f61670d85430068e21aeb30a8676c5d731966150cefc388632cc2a18031bd9672985430063632ce530a8600d8c439ca6150c018decab94c2a18031b1957298543006c621ae530a8603ce4615ca6150c019cae5b0cc2a18034710f75585430043f43ecab0a860087e871956150cef8bee632ac2a19db8710c65585433af0e218ca30a86008f7875846150cdfc388632ec0a18034710d759814336e2eb98cb302866ee1c431966050c910f90dbaac0a18034710f75581430043f43ecab02860087e8
  | 30 => 0x4000800003a00b002000800000802b800801c00000000040120030048008000008000001400c0030000000000006002000000200d000802c05e0130008000000007004001001e0050008018016002009001c002008003000402c00000080040020060000008004004001800000600a0010000022000001000000200000a000001200100c005400a007009801c01000400000780080020360038000002002001c00a001001000000a000000800801000a0000008016000000801c008008001000c0020000020004004005004800402200400b000000a0010018010006003006006400200300000300160010018000000006000807800400000080a4004001000000000c00200200080000030008070006001002800c01600500000240020020000040000002001000403800b000800c00000100d80000000070000004006004000005c0040280010000004004000004000200b001800c0000050008000004001000800800600000380140060000010000002000000001c0100020000010000002001001800200500b0004006003000001000000000000380360010058000002000002001800400a00380000020130008004004002003001400000600a800c004000002000000c00100100080120090038008000012005800400200200700200000000000098000003005001c006003001801400200100b803800c00a0000000010011000000007600100a80335dc671d8d5430d2ec28e3b1aa865a9d841c7635500159d0438ec6aa002b360871d8d5432d4ec26e1b1aa800ad681dc363550015ab03b86c6aa00237e1d6318d544754fc22c631aa882e1c5458c63550011ef02b80c6aa00e3d2057018d5446f0e2a4ec31aa860a5d85dc463550c953b09b88c6aa003871537118d5400567416e231aa800acd82dc463550f74bb0b388c6aa1e6a76127118d540070e2a4e231aa800ace829c4635500159b05388c6aa003871517118d543052ec28e231aa864a9d841c46355001c38a8388c6aa003355c47118d543254ec26e031aa800e1c54dc06355001c38a9380c6aa1c2a7e117018d540070e2a2e031aa800ad7815c063550015a902b80c6aa192a76107018d540070e2a0e031aa800ad6811c063550015ab02380c6aa2338715063d85540046fc1ae5b0aa8008dc835cb61550011bd07386c2aa0023760e70d85540068e2a4e730aa800d1c545ce61550f78baea31cc2aa1e7275d0639855445f0e2a0c730aa800d2c549ca615500199ec7394c2aa0033318e7298554006962a2e530aa800ccf635ca6155001998c6b94c2aa00f39185729855400672b96c330aa800d1c54dcd6155001a38a839ac2aa00237a1f63585540046f438c6b0aa88bc5f7518d615511593ee831ac2aa1ef87150635855444f0e2a0c630aa8008f7875846155001cb4a1b
  | 31 => 0x5001c0100010068000032001000000c000004000001400200b000801c00400200181c400a001000003c00c0000010008002001000000c00c00000000080020020018020022006000001c00c0080060008014001000000000001e0000044000017000801c00e000002800400000c000803800401200000280240010020104000000008001403600e001000400201300f800400000d000003000201b000000800200000680b80160010028024006024010000003e02d0020000004005001800403000800d001000e004002000000e002000804400400400000000020160000000000013000000001c00100280040040000000000006001000001000e00400000000040060000004000000001000800000000100000080000038000012005005005000200000580100000000008000006001003800c00600000b0000000000000000000c00000a003000c00100180080120020010008000002010004c00400d00000000020000050000006001015000400801302b808400600800600180040010038004000000000000400000100280140020000020004000002000800001000000180180020020000008000005000801000a002000002401e00200200000000240000004008006000001c02a00000280140020000000018006005009804000a0010030008000001000003400200c01880480080010018000004000000800002800c004800000a001002000800c000000001000000a001000800200200c000400200d000000c008001000000c01a011009800000000700000140020090028008000026000000c00e00b000000000000d009000c00200401a000000200000000000000040000010014017003800000800000000440080120030008008000001000000600000080380020010078018008006000801c0000010038018000002002000c00e006000000c008003005000005e000000000800807e00000080000000038010006003001001402a0050030008006000003000405a00400b8000000005000000401c0060000014002007000001000600000500080080010000004006008009802801e000000800005e00100500240020010008000004000001800000200000200080000190030000004002004801001200f000002800000d000000c00200201080040300090020000008004000000000000f000807800200c0020010006002000001c00200900000180060000018008002000004000801e000007801c03e0000030000000001001800802000000300040040000000000006001001000000800b001001407200100b006800400600180340000040010018004008002000000c00700280340040060000010000010000007c000001000000400201f002800801800300300780020000050000002002001000c002000042000400200100200
  | 32 => 0x26c00007580d8a8e6bd38000ad79d2cde910a64a80000bf53bcccc332e498c805cbd529e06f5000000021d2a7e8000012005001800000a000001802400000c00300040000120000000048002000800001000b00080b40020160020000000003005802800000d000800000a002018801800c00400080000020000008008002024005802c006003005800000400800a8000002000000800c00c009000804400000a0030000000002005003000000000300000000000000024006001002804800200100680240160120000030018001001000001000000080080160010008000000000000800000000500d002c00200200300000040020030020002010000002802800300100280060000000008006001000001400000000600040060050018004000000000000800c01300b800c0380000018000000004004800c00000d000000800000100100000000200068030004006002000000800e0058020000001003001001a0100000024006005005004800e000009001400a000005000c002000004800400400200080040020000008030000001000001403400400e804c008016000000000400100500080060030008000018000000002c000011003800403c008000000c0000020080030000001004000001a01100d802401400700300140000060008000022001000005002a00300000000000010008008004002002008400200a0120038008000001801c000008001000c0000050080014016000000801c000001004802000c0000000000004000009002000400a0000000006000001800401e00000180580000010000000014009000801c0080070008008000006000000000c001000000400000100080000020000010008014011000801c0240010008014002000000000c00400b004800c030007001800c002002002800800c0000018000000001015000800600700000b0000011004000c01a00100b80400060010030004004000001001c00c00000080280040010000008004007000006400200100580c00000090010024004000004001c01e0010010000008001000006c006005002800400a007003001000e001000800000e00300500100000030000058014006001001c00601f00f003c000006000001801a000000800400200000180480020060038000000000000002c00200100300000000050048000006005000009801000000b8000002004000000002002800a8004006006001802400800300180000080170000020006000004801403c00100380c400400800100000000020008008010003004801c0000030098064000000002000402e00e00000040160080098000002000000001c016000005000004201500080040060070048014000000000801c00401900500000460080000008006000000000c002002006000000a00b00180680260
  | 33 => 0xcff260c0003b2035c92250210556a8c38f82b100008582d1e46b2b787d3278416527944703c883f18000b661bf85023928dd3000000017a4b4a20d05f1240e00038980000228c2d00580792028badbb4c82f8000eb300003632fc4acc206800000000001ac4000000089c226832b00000000e400003f24000181c000325c36d07dc00014040003a907c432843ae0000be7000000011b068d3de89b400000000000000000088830a07080ef4ff7079cce60d00b52c1ae2aa00000518000fe62e14f8736e05120000c51287008314c02c400000002eacc3d3186000327c0c231f800041c00123ed4242205cd883f3828a3df89473c90c382ea400033589773244c47bc4c6260298fed12ec00036500002714cbc1b9842933c811a8a884e82a9c0243ac82d733843c9000000018d8d5106e813a4130e0e1674c1a800000000007f234f81eb29725f838b8832406073416b0a2a979cb8b304c7c2000009a21ae1a829980002d5000020027130b14cd80001044000000016647ef000102c14bc000235c34a0000a9231ce3fd1c089a20000bbe1b3c072150caae00006ab3c8c0002a8c0000000bce0000414077406503c4af139e41ae000088c0000000069837a000090c3f880000000df436cad1426b031f0eb400000004a400009092ddcd061f462b90ad45c527dad8b0358c451ddc0002378457000000016ec4163e18b6c11840000000fff1d2000000007780000b4b3fd8c600ce0f1400001a51b4001400000001412de30000000000005d80000000000000000095733e43fc178c0311b389240000ede0000dea1254b7e35fc1be0000ac709e837c12e8da3000093a11a45703614000104c13e2f9807a25140001cd800032b0bcd80010200000d160000000215400012400000000e6b00009713b7e66836f05151c1477014ac4562b382cf29f494d0e42000000000000000000000000000000032a400000000002cac0000000551313003000007653dd40002de8000000107939e0000273000035690322b440001afca3827c40000000f20000094817540001dccb901c6cc52b84ced2368449618c07330c6a0003e8800000000000fe400000004934206000000002f0000d2b324800025ac8073f0492707d8a150000e0325a6e192e54bca10100df120841535889180a7caa1230e182078a97a221411c325e7861270c0800006923d1c2821ed400040c0adb0aa01da216ec34877a80607305a60000452259800000000000ba040300000002340c8716e40a8000000020a4bff1cbc0000000000000041d06d8c050000cf01f3885b25ae018000005d0000aa4305800000000000378000317cd5901a00000000ace8b0c0c92b481a79d5e1c512803f125a507fb780c7c1a3cbf29c0c8860000f58000000009709fe002805f264c0a22b2000000006bc3ae0d831
  | 34 => 0xbc1000012d2b580002d88fdd222860f0000f4b278cc183d4800000000000000d91275c728175d00900007af3f30f843d0800002a80002c309ef800079f2c7a000137800028ac9a91d90c190000fbc0bc6dac2f8c75126b4d6700008b221fa6f930e25fe33d83d3411c3a118ccabb29ac6b00f840001af875a0ca0dc619dc0001870b2331d4c812ac09db04fcba70000a87098f04a3ab43fb41e04ca3d900032710b9b0000e472ed40000000000258cf8f35e0b042eb8a01000060100000000000bb1326400000009210000000000011580000000000d500c70000359800004780000000d4c08d8000000103d27a4bbba8664551a707270b2c9a8000036489c4fe416840000af0aa61b0c803ad34ce4851482610346e12f424ae2f4907633c48cf19747011c70c850844327000000017201501768bdf0a9050f1a84b510000f190f7c0003afc00f38f016a37087aa242800006b6000065effa0f2800000000002f780cd28240ad94d80000944de200006e327d81ed0c0104f00000002370f561d7c000197c73100008030000ef542140a73cf8cfe310095f865600037fc0003a00d34000000030500002f4ae0a3d44fbf086ca8e00802b30d6830f3d648041d54000000060a000000000000001040c5200007f523ecb1e00003a03b7c0003e5c3d12036f150000e940000b6b00000002b2cd46000000019548f600000001990f493758c0d39c8ebd0c907961498b3b25ec00000008d127b20000000f503184b060000bd32c3c00000000003f680002c163c82134b1c09b4000047c31b000000000002882f46b720000c1f000070732e89b92c580001e644b60000a24984409c00000000000f6500009df109400006ccc338000128000000030da665000000000008cc0000be6b09e0001cc8000000000028a22be8f407db80005ea213e00021c09d5000000000007494106c3b929496433a800038500002d141b9033e4b1b67ce8324ce8b400000000000e860000c298000f801f2860c00001e200000000000b40363495c16a0bac0000000085c5ab0000abe0c202622bf00000000b4731666ed2930c6424cc0dc0000ac400000000000ae300000003b6009d0000b6d2b180001e2815b06b2744000281c8e8c678000094a3f1cdee2b3c74c000000001ee3b5169c2253d8832303f285880006a20abcea605b0d400ae8b920000a032a20e700000000000075900000000000af42e0cc22928800000000000000b4e80000002ee23191920bfe036c00041ac00019b4dbbaaba5143a44e3f000015a1abc6d6316c16b0000901b1cc000152c6f61a9c3ea3f14f6e00007c800002db318303b80a88b6000063b1ed80da17b8df60598f3a2250baf00002c900002793084e9a2b4c0003a600b10f3000021f000030c4ca400000000cb454435f0cd30000503a0fc
  | 35 => 0x8530fb40001ba08c633045b40b641f915ecc5900002e21a1471a2046000111431d275800000000000000e610000000390d03595904d7000055a0000f6b241c0000000000000000000003ba1e98000000015b80000000000f0c36bcc459784a078000391267ce2833a0c6a00008ce1b1444733e882e1a509b223fd0582000f1e05ec35200fcd1f3e90e4b221c260420e4710000a931bdc59b2d0a4f014300003066acf82ec00000000000808cc40000d6b00000000000043000000000000003075061a0500000000dda3f50808000000026fc4374078b860b78424acb4bc226747a5063ce293a1099b07044d6032c3cf2e7c840258428018602ca19cc7a931b10041efcde7407059019e85a202eabd4166027330dc1a32dec824ae9a1021c7c460181000031ec41b0c84d350e9838a3cc81590c1275b044856727c2d7e1fce000269c0f81e70bad28c60000000ef22b7449705d464700002970000d0300000003446b8a2664699000000000002f100004fb152902a0d905f90000d0539b4441000076e2d68351060ce370000000213a14c235408735cc0000ed000000000000148f5d00000001d988200000000045c000000105a2c746a312fc06029947ee23b06791ef8fdc1e8455f07349b7107066e1c189f880006583296d5d10803db13700000000dfe22b438314d0f4f3894e5800001053ce000010b6e7d00007e40200337017864600000000000adf06accad3ca10563cbc0002c5000006d016a8314000016ccef2f1837413e8e5c93d83d411a00001dd60000000cc02c48000165024924b879141f60001b282b03c143b3240809612f0accb5dceb518900000000cab000000001200002e9057e1198000000098c00010673a489fa0000ebb015c48d00000000000e890d1c000341ccb000005e80e48f1c3ac4bec00003821ce41720e9447620ac0540d86c711a760c427ac00027b8ea8000000014b002729d44ef1e08007325064e17006f138b014840d2c4c92da21f1f7812a02545f5158c4b30d62ef19880fe3189c1fe0a64e761d184d03368b79400cf4c099c76a0ddaa32938814d80000000eacf012600bc8074c569000000000007e803e83ac256a0003bb4094000062327b0000357081c05624a103ccca704bce31060000021d02bd30ec62c41cc42e25fa0002ca87ab2ae8784087025522a06830ca4892375082c0998be910689fc08d0fd3239037e22ec23a20a0cb63e046db2060d173a64dec2810feb03c085eb0968231f3018b0c44e2b34b061f0c2c00029740000000000203c12e0e7061500000b3b5585be265872c1084000220c8f438f400018503aa22608b6874400000006ee1612000000000005d000008cc00037b4c058cc8853b4a0d6f14b8a8300244cb03e47dc98ac5f322e48b30a1c8840000a27c02200006a85ff0000a8f
  | 36 => 0x82d383bf3860f0b20d8000000083700003700f8028e17d84270d3d0402350000401c6f236d035c000000034600002a9400001980001344c2a00000c3394c000000037b2f80bf303740002634e902858c720000ca81a790240000bb810cc0000000f2e26ac64524f056a26f480d225c000400000009480002e1f02605103133b74a8a09c03571422882333418aa9a800000001c7055e00000000003966000353c0003c2800011e800026403b20000000063487380b00000000387000000000002fc3b08000000087dbea49de00000002d3c4cf294476b0000c4d18a800000003b60000cbb0000c800000fe0000040c202c35e2c687612e1d06100002d10e04eb93bf845127a01e1262400014e81ea0000aaca2880000000071a68400022d48463714cb7352400023c4de623a867e33706bb28dc35b21a858a207e36905125241ed06872ee4312133852340e4fee1268a240550000227804718d043c1e3452917e81a241a2c5a2c6cac107a42dcc0d81d038e0dba18fc7942c08fd91f4034d1888e203e584e434908e6360098a2da82d22a6cf292c5c84411380b33a04675245c317345457702381f42d90209334492b16bcf9219848390f106c80fbcf0e0d0c00e343ced63dfc81f3158625241105d38c8000369901a25f415311c800034242f00000c5300000002400fde0000204107c000187800000000000b3400000000000ea4e300000000065a6fc01240003eb4c2911680f61e7800037c834530287e1000084502ca00000009f509f0c7f2db834b0000b97000072403f04493d541d912bd05b0000134330844402dc46e2ad0bef1a6257840207421ecc6893f7c07c0000000000086013c400000000000000c4180000001654909aadcea500000000000c2200000001524738372417e0000d642568b070000000294cc8b1bf2000000004b28b8b5d1188b5503b000041a40003b387620e642e90428000093c00000005660160221000093f31181962128a2fb44400005c41c301710280f00d7b1ec80ee000078325bc87f0000000093485e222e8e20be4d721380b63054422a132487b38bc30e02d805a2f7eeee044cf2112de4ee22f46d52f409b3039cab90e88f730f4803a3604d0424f874100000003a700001d74acd15cd005380026e120c77f00b897e250424819683662bc8e10171c43a389c426153810b3e602e30155066a5480000000000420033026c05ec3314ad8209e8c28660dbd31b800034d8df00c98000040cbeb0850ff51e9c00028e400000000532820000311021a02803d80b0042212cae8d289cd9e0000135000104d00c800000000000000851000079313b411d32d40000000a7b9b500000bb6cee3ec000026180003ef8d0d02f00000000000332c00015c4000000027b2312c3e31780000000b1806b0af740fc481377c285063
  | 37 => 0x4893180055b1c2c6b507247bd2aaedbb326c84b1cc0e932a4003c02e83043d6889b33dc55241780002ae012c0488a2a3fc8bcebf2885fc1f0bd9ad942453274ef73fa88e800008c92d583550b4cbee0000bf60a54ffd2c54038000082a065458b064489912e2dcd001804d3278a3094889f0375ce413e7400000f433f117051d40e26132a6103e347021d272c0f42f74f6334fc7f03e24130319c240000095f1b9cc0612c4ab53660714297c0001ba4b49b4dc77621ac7a40fc00d4000011600000000000000000035900000001584000000069834c01c03e6455510ec9f81face7101180001ef0000008cedc19f4868983905300000000000f6c000000000005db24bc29c0d240372af50452d40b363b80dde0000000310c40b0a5000022040002f1c0000000e7f0000000000000027900001cf250a00000000f78000076c0c10000503186ca9600002c12c380640000000307800008187bb3bb08f933902ef31dc0000000df80a4c14200000000000b7f1f74f6a18f090d00000001494000122000023f8000318cd1a00000f21ae036502c8e7a32be9f7a7cc00000008a400008df00100003dc00000000bbb01dc00000007fb00000002b8400027fc0000dc8e1c2aa000010c4ec3388877200008421b68000000000000000003fa000032200000df2a7e000031a3380da70f740000000ee1242c8412a1000000000000000000163c0002f444d523209a52b949cf13a400027dc3c500007292cbc1f1000000023744ec1cf0bed32fc77e1b103e701d867100000000e540ea000020d20c41d821e600038744c73e0807dbe383163ba8c23a5c85391f98b9334cce62141600001a40003f4876c28ba0002238f1024d896d3aa8b5b0b840752cc8a354150dc0199c5c23e50d132c4c5a423ee95d1944d991824a552ef6015217072529ecab22abc47524f41363c9cbf20394863b330d4d17800d739f83c31134f0d06c09e023cc1a441810132ff400016cc0003848bcf8000b5e94f4def0ab82313fb09dd06764c511909ef1fc418430d800012b007ca1da00009fc00001fc0002ec03608000000063e29d193c0002e74ee9000106d05548208000d7d05e81231988f4000a048f33cc0a9b69419310b0760227c000244800000007d23fcc056800000040dee3519400003b6cb570000290000000031b400000002e700004bca3c82003388e870f04fa830000000000e3b2dbcd6e21f8d0b0000ce319b0e5000000000000a31050c78e19643011f1aa293b400d038a886d800039b0e140000000c950000db03cdc00000000002044ff81a380000484000000000026380001214000000091c2244eb417707cb01ea227253c28f000048e1f881d400005000000fb31fe49fb329818e146c967af9e3bb0000000288c00007f0e7b2b2800042107a00000b891e7450
  | 38 => 0x2c7163428100010222da000039d0d6830c8000000032037cc4113854c422ff04c6203b04300001571444000000071e32340d200000000d8808b04365a00904a00161c7f7171000002b490e0000000069cd5b3af0a6200001640fe8c98000000032cc000317a00041900001b34a3034560001be8c8a13640000000000096c8d6000000008c898b00000000000000000070e2610f8d0000c5c08d505c0bec8f73b2c07b17c8c3412f4d4400000003b049aa3dc80000000000021004a0e4b01229f6be134e49383a7400000004541c9800000008a50fd46930000d192164ad9000048600004b7385c0004194547167c74e2882f2d3a384db3ed85ca000076d29dc81e1b7433b38308db0300e6c286c0ce2e942a61bac8611da06d92b0c8b02bec6d21060ba806f0ee530d44b43e984300000b822474aad865cb59164896c0602cfd072c5171c54000365cca32de0f000940769260a07fb0085413e2cfb9376cd8a8000fcf3a88c62038863e231c9e601921ee32f806db680e46418cccf06b4c1c2a546032e444a92fe842e8ce82f5004c5d614100cc2a642393e8cb8e1d145df04a410d234c97816dcc763ccc63500007e5354c70a00001bd2b4261700010371e68000284c00006521920cf023f1d4c6d1110800022f00002ea801b2bb80e126e8f4138e4a342be038940d01b21c6050e28b0c58000022424d09af1d48d382468fc32cf48c88000000000000030ba000000000036428b700008ab1028e7730485910de00003420d4b0a94000127857a24980e0098c8632edc00015505de2c88a050000a0e35280002864bedb0ac36c2a720000000ae000009d2257601a40a43a70000bcf1b085b10000f3b3da0000386c0003c48537000000000001470000847000031826e00000000c1f8000d600188dfc0cd8bc0373c1461e6e2050ddc3f70994d27000001918c462f00000000b980a3077c5ad09d44b01e04ea000000003eec000104800000006a808f807029a0528000106e26d45352e5000000000000000d9b410853c35946b600342440000baa800000000000000000e5a2c4045d21c45862f6c0000000ef61cd41ae91f8c8c2b549fd260e0001fe8db7000086d3d149d823145650dac230092806a027800000004f72a5094b1ff8a7031e4f4300000001e6a5c640ec0002e30bf000009063a780002328edbbe140000f2c2bf18b40001b700000cd253e3e28e332cd69ae2df01b8342806c08409c10000c9a39740002148a91225456033e1083049050636e453b254cbdc395900c28d8f6d00300882e3c000287ab6737407ad37e866a33206de304e0972c0c5450000c9c075c00000007a34154aed242074a2006c54246cf9b1bf60000000b0005040000000dc70000000133497f80005ef000004e248cff012e653318689853b10abf1ff023d02
  | 39 => 0x5860002c4400000b400008acca01e603a40e68000276498f16c81882e800002c9800023bc0000ce4a4e000000000006b41b0410fb4a410900000000000eb70be0a0f42040003994000204863210aae0f000000012001b7403c0000d744341c40131378506280000000000e9f0cf823b36cc5cf01aeae936902ee03283f8858c3b90000a20210cf441980a820a6c45836749c036d8d3d0a4449d34e82f71a102f89e40c93130ca692a5c72b23a469a02d0d8e3198afe227477107a00000000de507e03ce0a10000000000015fc00019c07ff88385740a783ee1d000000088965a6f08133f6c00020f80002ed80003288e1f00000002f6843e4074c75a34904829489be12a88673dd0a3b000013d30e8716093844b2284f3d1dd00fd9d12ca531245b000005aa15b8000306c0000d505ba1f147ec00000001348696097c57d3f9473e3d6e87700007092d0606f0578af512ea6492fa000025a20001be0000000054641447c33b549650000e5f2be49b60000a3e000000024a075719bc40705d896a303856234a8fcd166a8892c062922e84c683ea8ab62d24cfc280a32234380002450a2d090cdad1b80913361c3101fa85eb3bfc1791dd2f6002fc0000000000000059a18f40000000bb580005e512c88e710d426f0574d9a084892c00000000ab01bb00000000d4ca3f41180000000000078c0003970c820130bc500004a7000000b000017f068057c000003b3ee09033bc400035e4ad72aacd86053d0253b003f2841c15c2b98b2522f2a7401b85d9388cda23f0830900007971c34ec639f00b91f503482cc05422c9c00000000000000d5825602da3b9865b3bc00ac05004e715d4000117cb2904cea2200005bf286893b00002681fd000040b8ff427209a434c40001ea08c3240495e0000000000064c00009a02c28f1f4034c8605c0ee240c402b1e24a9f3b8cc2f1ab50231cf6f5e0364f2180002611fa40000db87cf0d18a543dc477c311ca412c144023378cd4256e45e000000000008903af80003fe400015d80002a0095900001dc0000c4a044a7fd300cd89b54838e0f3446d37e411b000074d09dc54040e0237350c000204048c207409900000002cd0fd72168eba23946ef18dcb978000f1a35b0000209ca4320e8a1e0360a9c0000e48000000000010350fa000039343e9256c000000000000000000000b9e3c0c0000000596000082f0000104800000000000363f203e52c86c8a8000896000029832c45132a1433325e4b332d0c6a921520000f6472d4220aa024de8e335c052d1440a441614876052c7d91e200003ddc5182c242f3bd34d4e21cce49208448b40f0ee8067446730fcd020000654000069f22c40000000b6135784a621f45b515b400007289c629e80000cc48500000f460ac8b733cd4ac900009951f60bbc01aca5701c20
  | 40 => 0x74300000000000289220000029841060000737953035601c4c3301049c341c8bb3290851913a8c17848019a19102692c7c4922414cb20e3411522065790000dd90dbc4dd18e000029cc0000b70000019c0000000bfb032000025f07b82b000000000672325875400002f400007d631463750000000000011086fc3b1370c2e410245cb2f643e4004494e0000e11026000023b809f108cdc2c018e9b000045907ecc65082cb882bd89da23c00003ff0238067a00015740002ce46192f0c54f2d3045321a000020d48a30e000c7313d0113d384082e8c0003980f071edcc12a1e8000000093914e038c000096aa9b0b858000ecc22bc0630000dbe066cf2a0b404872738968000098801b43c221e4a2d80e4e4c0ec09dc0bccaaa04440c60b185073f445dd2f6000020e00be0f5caeb02b883d3ec4b520078cae3fbc0002dd039724a800800006cc3b5c000110c4ad1884c3000000000000ddd21a4c0f0794eac000017326488c027344c228081c823d4de8154cd1e34301620c2829a0000e0b1b605e4000000032d0000000000004f0951b1a4e442b086f32f8816f41f82c227b41ce2b9c7790d1058c1018aa211e42d80d80e681b24000062e2209874fcb05527633a5c9b11acc0000a1a00012e400037300002ce8d93220270c0a34e8c0f580002a3400000003a80a582ed000009100005a900005c11b2d041000104e143490080743e60000d003340a2807b0bcc28508c12e350118cb016934ecb990000000000107b1228dfb39642ce37603f08000c5d30b0189339c8bf16105c92ee824b38d80a53a2c1391ca8f9f2508ae228c80ed1608f2c11e002941c4b3f8000d902c900003814d63000055e284009024c8000164c56800003f408604f933a46a604528e125c000009c880116200000e7c22803f800036286ba1e2c30c2d2ad82000085f00000001394d3208aa00005390524164b3e023c0000b74259042239419ec73f2958fa01320034000053f1750421b0105723c10d7431d00eb0000cd93f600e8085418131f62a337387ac3a5832f36102471004000308097f08642cc0000ada0000e2d0e1078018a46a4202600000000780aec00025b80001b1c0000000a0d0000a3a0000a7200003793b64b3800008090e78c4e11d046f02a2d5f07fc00000000001f1c85d4008a470398f4a421c000323859e2cdcf781b00a591fd8c102b90325323c7d5000000000000000000c41130000037c4000274c46a00000000858eca000082d1c64000000044c1d1cc6f389019c06d46ac04e07501c8032e2920e552158b0b1adc7b13cf06f035848fd206400000000001250b4880000002e58718b7f40002d0e8ac000084f29809490000812800000033d00000000000316220839a47e73be019400009440000aac0000c4b0000aea09f44e109a83be0000a122
  | 41 => 0x39507ed00000000000b5c0bfefba024d0190000f3f26040002a7af9531f501f296031c995cfff800000004304df00005480f544f8148482220f08a00000126c124e0833546b20000c55373247c0e58afa21940001ae4000168d00e10d88ae141ead41908daa03542fe3eacbf180000ff378ea4600000003df09111fe069eafe01f20b204a30000a9a39d465600005bd10789f929281f534b8c900000a8b80005971e1c24600004c12588000305c6e202bcbe5245814d03d400011dcaf02efc0000da05fd3de4c2736480000000000184820124885cc34800003c98fa500004d316e0000034c0a422989d004acef43748ecd0040e513c245582d780000000000255e00035d8a4b07cce4f0000000000000000003b7163800023e8f8319042d60000bbd000041707982560ad04428000000000044a3e302fa18344fe38e88333ed00003bf400000003341bb01000000a4d1a3058900001fd3d8412533d4b5f01be00025c600038340003ebcf3014684f41e306950000e451c5c00000008ba259c8f82aa4a9e3b24b468bb0dcb240a3671a0407d1a20e4022a8d2f03bcc3c3f584ff067c39d30e4da90ca87952bea0e902345d029f0a173978b75095c1e040405d805b8b409f7cd470cde000000075e00005ae0000f1d0001001000000000004ab1b4c1900ae0e64245408c13ac854209492501140b509e000017d0acb8bbe00012d269d000068b3c600fd27a80001cb80003abc000000006113cc6063374974173800009749372ed07ba1bf400000000001424da810e46020ad86a510fc0e40b8095005a03980001015b440a3c25542eb24b4c7810acbea1de81fa1480116800000000000002192e8f00002219d70000346c1042364d2600006050000959a9c40bd00008ed2d4c6f424785d32cd4c5b9cec20a000000032a864a24d467f397e000000000000007562cf0a3d0dd84052bccecf2a04f489120d231bec0001600f06007c95139b884e038cc571934cc73098cce07c0f9e222c06c88feaff18203061194d413b1c86424c0ddc00001562cb000006140000000000308600000001cf41a800037040002a2c00025d8bb2260840f00003bc0000000415c4380000000298c81620384403e84a0a21241a11d9c00004507c921ba0001b9001c200a0ac9d3c000000000031f200000000000000a5000000000000a0c0000000000000007100003004d483cc4000233400029bcc0917b4b283eb830bc05c81508b0b9a0108000000000019f0f7d21c87b9049ca3324b2956bd505274058559173413b1c88e4e1f6cac51570a999e48bcd2bb042f1478bee884ccdf29fc1af3be80a1375494621b80000d4022e282c6bd0110b0816f070f420800041d482436540000000000000000000004002bb63c61ab89bb0524bd7021456f0000aeeba200000000
  | 42 => 0xe340000bc93c6c085b6ac004a360ea7000000038180000000c6b0a800a92d189540d042d4190c0000000df50000d3c3d7cb602e04f9c139816036d481b25ccc153e4468a16043c70000a6d00000002d04d6a000000000003f218e4ffe35b6f3900004d803dc9f2355c000000025a2fd03af000000041920000990e012a6a4f220140fb3658eeb194c00007480251b18335000083025300000a18dc82f270659260848394800040cc37f38781102884b703c3cc842fe40b83d980ab23802220ba8997088102b2968b58052800032bc1320dcc79b2da4fbd0c34cbd0000ea3000007e0fe6a2f0000ad02dc433d0001050367027601faf3638842261dd400008bcc501b5c000000077d22e0ef90000bc8861c00000007e0179800010c903a04cc49f320cc482cc43150000e9500005f0000100a000028c194868612f8e630ab4cca05e0610141400000002233aacd7a3dbca9d3bec2a1077811a01d03da218800000ccf482af06741ba85d213f4a18008463a34749e73ec80590000a05b4843e2339400006a600000000001cdc75840b28c1c1f400000007850000c63a4a417c1c44a403a087dc3bbc000000107400008780fd860b21de9204050be4270865c2fdc000299c000000000000000000e3c1081f18c0c0000b0139ccf903d5ce5b061807335c45c30000c253c20bd6081c0000c50f2b363000000000001f04000000028b1f8c0000bdac7a3a28e4238585f718584730008eb0116c83b13f05d1053ecd735a4d250000e0930b8db141a0efc00000000000000246484c281c000402c0000f702580464000000069b1558a038000aef3b44dd1000102d2582cfb3d6ccdb0dc4000406c000080c19e0000de40000f762e1050b000000000000000000a7919d84b5b7ac80580005fb141b07741bc0400000ba200000002e0099e14c8000000065e31c00001a4410e00000000c1ce8514588b1a43c7b03b9c118057c0000000875049800020082540c0816d296cf170628cdfad10dae138d06228b20002874b2e35b41771f00a861f44ced16d899a34042be0e4c19cb6250150000450309a21e261c4f522f8b9c10b2b3f3068e57250043d203228319ac9ca3dec2d50fb06ff2e98b19287e4281038a26268c34e19981672d20f930e2051f2df4ffb0df4531399c7f3420a66312e038b0aac25e1a40ed41264c89269852a3554f9a2c34079954091f0fac76f0000d2d3fa45572650000000000021b0000291400000002f221bcbdeb318d122234852bd4c69730904460c663051c7478f026c9d4297047d021826c41e84843eb01d50000b20229c15216704cc0000b839c8c2ff0718fc41decf161f68f3441f2000000000000000001ffc00000000002616a1f00000003c946690000000000107f113c2b723ace6a1a8094300000000000000258e68206c4000
  | 43 => 0x560c0c8f580000002d163b8094c051308c8a92b70ee40b94d750d608c40d842f602f699c42189c926440000fe02df2744491215c0000000000000000002c04d400f81a909305fc00000000000c37b7dccb80ffcc718000fc61c841c22030000000106c2ba093100000001c480003e9c35f00001a88a9cbd5a7d07ae1b7d0662c0a10f203e00015b0e662660fb733b00502ab422904dca11000051c00000000ff80000000000000000011ec27e0da88c2192c20c2f10d2225581e428180cf00005a53f40c110bf43f3000104b000042d0000b210000c54bb68a64022404f07bc00012d4fc01aa8dbf0664d4233ac2741090db228948fc2dd8c0b1310f6709acd542f2c88f1064dc4040442a083cfd518b8960381c0d7ad080001ce800500000003c445e200d40001534cc92e603862f5200000007a2000000000000003f848cb40bc00000000000248000363c08dbda400000005830208c358004000000000000006e5118c3420f8c0000000d45000000024400003a840003ad8975190023c0000a491f5cea908b4e6f3f9c00029b8aaa8000e1a00000000000afd271ca049c004da3810ab13728ab30c78a762788f880aa4ec51c1015811fc73d219856b0001027301aa892368581bab817d0344a5e0d306280000c071a0000000007cd0584026000105f0000cd23d700003fc40003c08e023092a4f000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xc181e8710f6550d3030607a0c75d91434c0012379855054d85300058524d54153614c0016149550c43d85300048de6154150614c0016149355054185300068555183150614c0012579854c5318530005852515314c614c001a158454c5318530005852554310c614c001a158550c431853000534a5b711c1314c06b4c6969cd21085300063121a73484214c0c941c95590735503030507251651cd54c40c941c95590735531030507a53651cd54840c941e95d9073552100053124d87d8821840018e187a0362086100063120f625c0218400141e93dd274d95100040fe61741d3654400141e93dd675d91100040fe61751d7644400141e95dce73d91100040f660549d9544400181c54a0e76551100040fa60541d9544400143591150765511000607152861cd54440c141e94d94735511032507a57641cd544400141e95dd274d8d1000487e6154153634400141f9755054d8d10325072557410c634400141c955d07418d1000487e6154150634400141c975505418d10006855518115063440c981e8510e7650d1032607214431d9434400181e8710f6550d10006071d683d9143440c181e841d76350d10306072107518d434400122f9855054d89100058324d54153624400160c9550c43d89100048be6154150624400160c9355054189100068955181150624400160c9550c43189100063120f829da21440574e290e0a76885101a53125c6348520440578e0762012148110006b018c80485204400103f985d074594100050724d741d1650400103f985d475590100050724d751d5640400141c955cc73590100040fa6054dd9540400103e98151765501000607150835d9540400181c54618735501030507251651cd54040c941c955907355010325072557410e630400141c955d07498c1000487e6154152630400141c975505498c1000507255741d1630400121f985505458c100050725d5415163040c981c8510f7650c1032607214435d9430400181c8710d6550c10006071d48359143040c181c841d66350c10306072107558d430400122f9855054988100058324d54152620400160c9550c43988100048be6154151620400160c935505458810005832554310d62040818c48358971cc8101dd3165f8358b31040778c58758a32cc4102063160a835db21040014c49758b314c0101ae31a1d62cc530040018c483589718801017c39a5d86c8520040018c5861cf21480100063120f82dd910040570e697a1d62440100061921f755891004001864871d562440100062921f7458910040018a4871d16244010007091d47458910040018c487dcd624401015439a627358910040694c6939cd624401000631a1c7358910040018c4871cd624401000711dd4735891004001c44751cd624401000721dd0735891004001c84741cd6244010
  | 1 => 0x130507251651cd54cc4c941c9559073553310040fe61741d1658c40103f985d475592310040fa6054dd9548c40141d9315376552310040fa60545d9548c4c141c94594735523132507255641cd548c4c181c8710d6550e310048be6154152628c40160c935505498a310068355183152628c40124f9854c5398a31005832515314e628c401a0d8454c5398a31005832554310e628c401a0d8550c4398a310048be6154151628c40160c935505458a31005832554310d628c40103d9815276551310040f660541d9544c4c141c94594735513132507255641cd544c4c141c94594735503132507255641cd540c4018c786dc9324c4310040fe61741d1658840141c935d074596210040fe61751d5648840141c935d4755922100507255731cd648840103e9815376552210050b64854dd9548840103e98151765522100607150835d9548840181c54618735522130507251651cd54884c941c955907355221325072557410e638840141c955d07498e2100487e6154152638840141c975505498e210068355182152638840141c955d07458e2100487e6154151638840141c975505458e213260721443dd943884c981c8510d7650e210060721c43595438840181c7520d6450e21306072107598d43884c181c841d56350e2132507255641cd54484014c79761b320c5212a471a63325c031484c941c95590735502100689a1684dd92108401a8684a0f7648421006a161283dd92108521b045420d5448421204b1a4c8798d21084772c598dce6348421004b124d869c121084018a586a10704842100629619841c121084019258561070484210063161a831c121084018c58660c704842100661611831c121084014c693e1d21580210062921f7448560084018a4871d12158021007091d47448560084018c487dcd21580210063121c734856008401c87741cd2158021007211d07348560084018c473201215802117cb8a5c8048560084018e2972012158021006a8a50804856008401aa1942012158021006a8dd0804856008401aa0742012158021006b0a4c804856008401ac1932012158021006b0dcc804856008401ac073201215802132507e59651cd54900c981e7520d5458e4047c87e6154d4d63900c941c975535358e4000607dd88355153900c981e7520d5458a400050765443dcd62900c981e8510f7358a4000607dd88355152900c981e7520d54586400050765443dcd61900c981e8510f735864000607dd88355151900c181d7620d549424032507255641cd54cc0698c6835cb619873000439a627648421cc0018c7869cd21087300040f66054dd9548c00103e98151765523032507a57641cd548c00103f985d475d91300040f660549d9544c00103e9815076551300050764c541d9544c0c181c83150765513032507a57641cd544c
  | 2 => 0x580000485129979caa08e2000e40b880000004793e688140c26c8c96c594005780055a120602963a76748ae4a94c858256b184192281f2465d24a7f9322c88a241ae0f87e520f28996a1ea54958c01b05a3f97c07a0887a521b950001cc3b8fc0016825a0c860a4791343b1bc575be650c812a44560ea4112200030020100c000411828120600000140101000002a0700802050b85c0000000100a020081c061e118000e00000040e01028640601020000800090240601010880e0702000000a000182a01000080203028080a100c81c00130401400100000808060003008010d014000401800080800018460000808060e01000040001810121230487e6054dc4635500121d981537118d540058564454dc46355001a0c54a0b7118d540068315182dc463550c121f981527118d5400487660549c4635500141d971527118d5400683152829c46355001a0c5460a7118d5430487e60545c4635500121d981517118d5430487e60541c4635500121d981507118d540050765c541c46355001615911507118d5400705151711c463550c121f981537018d540048766054dc0635500141d971537018d5400487a60549c063550c121c981527018d5400487a60545c063550c121c981517018d540050765c545c06355001a1454e057018d5400685150815c063550c121f981507018d5400487660541c06355001a1454a047018d5400685151811c0635500141e96152739855400507a58545ce615500142e96152729855400703150639ca615500142e96151729855400703150635ca615500141e96153735855400507a58541cd615500141e96152739815400507a58545ce605500141e96153735815400507a58541cd60550014369615371581540070515063dc5605500143696150715815400705150631c5605509103c985957494e4330507256861cd5450cc141e96d947355143306071d8835515350cc981c7520d54d894300705194439c66250c01c146510d7198943326071d4835536150c01c0c6510e729854300703194435ca6150c01c0c6510f725814300703194431c96050c01c146510f715814300705194431c56050cc981c7520d541814330507a5b641cd54544c181c7420d54d8d5149487e6154d0f63544c141f9755343d8d51006071d88355143544c181c7420d54d895100507650535cf62544c181c8414d73d8951006071d88355142544c181c7420d541815100507650535cc60544c181c8414d731815132507a5b651cd54504c981c7520d54d8d4148c87e6154d4f63504c941f9755353d8d410068555181d4f635040181c7620d5454d41326071d483553625040141d9510d73d894132607214435cf625040181c7620d5454941306071d88355151504c981c7520d541814100507654435cc60504c981c8510d731814
  | 3 => 0x681ec2484c3d800770a658a5c00002001a459a040000c4b000382480020600136960000d9d41c8000d18a001c44808e53c006480021a2e23147000c23721a278167e8563d0de52986408088c01c01878000662d000591de500001be22001186a800328004e610001ce4400a4ba6e0025a0e800040005715a5e03c50db24c1722a0e65460e989982fa6a789f047000000000680042098000007c9246700099821939886c000451ba828241390e80000809e0121c87b832000001a0008d0000006a000007e00034996001f614000000000022060106000004dc007605e000008d8000012d42800002500a9540009a000007a800171285062a1d0da11000510fa0e224499b62822c449901d870990003400003860001b85c0125b800001da000000000008000400004e000000002a97a001d0108a2a0251271763e0cc758829f272211165092b9e8b84bcac2c02c000d6630007180000046469b4000f0251e84f152360000024c000542d8009a0620000056e38925f4678001490c000ce9c247000005824f539c06097e6a0007082666a408fa3a698e8518284ea782f21c102608f0c631000352427f0007980008a7e00000000889d0ba00000
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x86a9078092858400070001a4983200003c89a228d02300000050038000d08210014c110bd43222a6e231aa800a8168454a0b7118d5400501b4e2a505388c6aa002415a9151711c4635500140ad38a840ae031aa8608072a19414d73d895130403950ca0a6b98c0a8992817a755181d4f63504c900e5432a21ae7b1282648072a19510d731814130403950c98a9bb2a91880220ca96154310e628c40140653aa8c10a931c4200e081d474201215802100650328c990090ac010803880741cc8048560084c900fd432a21ee6b148064807ea19510f735864030403950c98a83b2a898002214a96154310c614c00140a53aa8c08a831a2000a8128d546045418910
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x5
  | 2 => 0x6
  | 3 => 0x2
  | 4 => 0x4d
  | 5 => 0x4e
  | 6 => 0x3
  | 7 => 0x94d
  | 8 => 0x94e
  | 9 => 0x124d
  | 10 => 0x124e
  | 11 => 0x138d
  | 12 => 0x138e
  | 13 => 0xcd
  | 14 => 0xce
  | 15 => 0x9cd
  | 16 => 0x9ce
  | 17 => 0x12cd
  | 18 => 0x12ce
  | 19 => 0x168d
  | 20 => 0x168e
  | 21 => 0xa0e
  | 22 => 0x130e
  | 23 => 0x20d
  | 24 => 0xb0d
  | 25 => 0xb0e
  | 26 => 0x140d
  | 27 => 0x140e
  | 28 => 0x24d
  | 29 => 0x24e
  | 30 => 0xb4d
  | 31 => 0xb4e
  | 32 => 0x144d
  | 33 => 0x144e
  | 34 => 0x16cd
  | 35 => 0x16ce
  | 36 => 0xb8e
  | 37 => 0x148e
  | 38 => 0xbcd
  | 39 => 0x14cd
  | 40 => 0xe8e
  | 41 => 0x178e
  | 42 => 0x4b
  | 43 => 0x8a
  | 44 => 0x8d
  | 45 => 0x98d
  | 46 => 0x98e
  | 47 => 0x128a
  | 48 => 0x128d
  | 49 => 0x128e
  | 50 => 0x150d
  | 51 => 0x150e
  | 52 => 0xca
  | 53 => 0x12ca
  | 54 => 0xa4d
  | 55 => 0x134d
  | 56 => 0x124b
  | 57 => 0x3cd
  | 58 => 0x3ce
  | 59 => 0xcca
  | 60 => 0xccd
  | 61 => 0xcce
  | 62 => 0x15cd
  | 63 => 0x15ce
  | 64 => 0x170a
  | 65 => 0x170d
  | 66 => 0x170e
  | 67 => 0xd0e
  | 68 => 0x160e
  | 69 => 0xd4d
  | 70 => 0x164d
  | 71 => 0xecd
  | 72 => 0x17cd
  | 73 => 0x154d
  | 74 => 0x154e
  | 75 => 0x10a
  | 76 => 0x130a
  | 77 => 0x14a
  | 78 => 0x134a
  | 79 => 0xd0a
  | 80 => 0xd4a
  | 81 => 0xcb
  | 82 => 0xb4b
  | 83 => 0x16cb
  | 84 => 0x12cb
  | 85 => 0x130b
  | 86 => 0x14d
  | 87 => 0xb8b
  | 88 => 0x198d
  | 89 => 0xb0215
  | 90 => 0x20e
  | 91 => 0xbcb
  | 92 => 0x188a
  | 93 => 0x19cd
  | 94 => 0x1a0a
  | 95 => 0x184e
  | 96 => 0x5cd
  | 97 => 0x1a4d
  | 98 => 0x180e
  | 99 => 0x2cd
  | 100 => 0x58e
  | 101 => 0x18ce
  | 102 => 0x134b
  | 103 => 0x5c055
  | 104 => 0x10b
  | 105 => 0x5c955
  | 106 => 0x5d255
  | 107 => 0x5d395
  | 108 => 0x5c0d5
  | 109 => 0x5c9d5
  | 110 => 0x5d2d5
  | 111 => 0x5d695
  | 112 => 0x59316
  | 113 => 0xb0216
  | 114 => 0x5c215
  | 115 => 0x5cb15
  | 116 => 0x5d415
  | 117 => 0x5c255
  | 118 => 0x5cb55
  | 119 => 0x5d455
  | 120 => 0x5d6d5
  | 121 => 0x58b96
  | 122 => 0x59456
  | 123 => 0x5cbd5
  | 124 => 0x5c3d5
  | 125 => 0x5ccd5
  | 126 => 0x5d5d5
  | 127 => 0x5d715
  | 128 => 0x58e96
  | 129 => 0x1a57d5
  | 130 => 0xec5d5
  | 131 => 0x5d7d5
  | 132 => 0x5c155
  | 133 => 0x5ca55
  | 134 => 0x5d355
  | 135 => 0x58a16
  | 136 => 0x5d995
  | 137 => 0x5c2d5
  | 138 => 0x59496
  | 139 => 0x5d4d5
  | 140 => 0x5d9d5
  | 141 => 0x1a45d5
  | 142 => 0x59796
  | 143 => 0x9c5d5
  | 144 => 0x5cb021d
  | 145 => 0x1445d5
  | 146 => 0x144596
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 34
  | 7 => 1648
  | 6 => 7185
  | 5 => 4233
  | 4 => 322
  | 3 => 22
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
  | 9 => packedAt gbK9 (16+((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 2)*1) 1
  | 8 => packedAt gbK8 (1024+((h/20+packedAt gbK8 (884+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (69436+((h/705+packedAt gbK7 (60976+(h % 705)*12) 12) % 2795)*12) 12
  | 6 => packedAt gbK6 (383800+((h/2780+packedAt gbK6 (344880+(h % 2780)*14) 14) % 16121)*14) 14
  | 5 => packedAt gbK5 (269975+((h/1556+packedAt gbK5 (249747+(h % 1556)*13) 13) % 6165)*14) 14
  | 4 => packedAt gbK4 (23566+((h/114+packedAt gbK4 (22540+(h % 114)*9) 9) % 454)*10) 10
  | 3 => packedAt gbK3 (1830+((h/8+packedAt gbK3 (1782+(h % 8)*6) 6) % 37)*6) 6
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffff007fffffffffffffffffc7fc3ff0fffff
  | 1 => 0xf03ffff81f81f03ff03ffc03ffaa3d13f44e73
  | 2 => 0xffc0ffffe001ffc0ffc0fffc03cc3e1cf8739c
  | 3 => 0xfffffffe0000ffff000003f03fe0ff83e0
  | 4 => 0xffffffffffff0000000003ffc000fffc00
  | 5 => 0xffff0000000000000000000003ffffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x20410000a2822041204105515000c0650194a5
  | 1 => 0x523a76581511523a523ae80aa9aa1d12744a52
  | 2 => 0x9e88baad40219e889e88f2a80acc2e18b86318
  | 3 => 0x410dd3679f40410ef3c2030337037a0de83e0
  | 4 => 0x820efc79e79ef3c041040c0c3ff4000ef7c00
  | 5 => 0xef3c0e04104108200820830303ffbbdf000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeaaaeaa8eaa8a8a8eaaaeaa8eaa8a8a8eaaaeaa8eaa8a8a8eaaaeaa8eaa8a8a8eaaaeaa8eaa8a8a8eaaaeaa8eaa8a8a8eaaaeaa8eaa8a8a8eaaaeaa8eaa8a8a8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37367
namespace PEqualNP.Outside.L_meta_37367
open PEqualNP.Outside.L_meta_37367.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 1 := bs0_3_0
theorem alls0 : ∀ k ≤ 3, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 3 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 14 := bs1_4_0
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
theorem bs2_3_0 : Interval s2Atlas 3 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 3 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 14 := bs2_4_0
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
theorem bs3_3_0 : Interval s3Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 1 := bs3_3_0
theorem alls3 : ∀ k ≤ 3, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_32 : Interval s4Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_64 : Interval s4Atlas 3 64 4 := block_range (n:=4) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 68 := (concat bs4_3_0 (concat bs4_3_32 bs4_3_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_32 : Interval s4Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_64 : Interval s4Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_96 : Interval s4Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_128 : Interval s4Atlas 4 128 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 129 := (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 (concat bs4_4_96 bs4_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 13 := block_range (n:=13) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 45 := (concat bs4_5_0 bs4_5_32)
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
theorem bs5_3_0 : Interval s5Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_32 : Interval s5Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_64 : Interval s5Atlas 3 64 4 := block_range (n:=4) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 68 := (concat bs5_3_0 (concat bs5_3_32 bs5_3_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_32 : Interval s5Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_64 : Interval s5Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_96 : Interval s5Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_128 : Interval s5Atlas 4 128 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 129 := (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 (concat bs5_4_96 bs5_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 13 := block_range (n:=13) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 45 := (concat bs5_5_0 bs5_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 1 := bs5_6_0
theorem alls5 : ∀ k ≤ 6, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
  · exact alls5_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 22 := block_range (n:=22) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 22 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_64 : Interval gbAtlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_96 : Interval gbAtlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_128 : Interval gbAtlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_160 : Interval gbAtlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_192 : Interval gbAtlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_224 : Interval gbAtlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_256 : Interval gbAtlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_288 : Interval gbAtlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_320 : Interval gbAtlas 4 320 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 322 := (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 (concat bgb_4_96 bgb_4_128))) (concat (concat bgb_4_160 (concat bgb_4_192 bgb_4_224)) (concat bgb_4_256 (concat bgb_4_288 bgb_4_320))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_0 : Interval gbAtlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_32 : Interval gbAtlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_64 : Interval gbAtlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_96 : Interval gbAtlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_128 : Interval gbAtlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_160 : Interval gbAtlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_192 : Interval gbAtlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_224 : Interval gbAtlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_256 : Interval gbAtlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_288 : Interval gbAtlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_320 : Interval gbAtlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_352 : Interval gbAtlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_384 : Interval gbAtlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_416 : Interval gbAtlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_448 : Interval gbAtlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_480 : Interval gbAtlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_512 : Interval gbAtlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_544 : Interval gbAtlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_576 : Interval gbAtlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_608 : Interval gbAtlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_640 : Interval gbAtlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_672 : Interval gbAtlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_704 : Interval gbAtlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_736 : Interval gbAtlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_768 : Interval gbAtlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_800 : Interval gbAtlas 5 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_832 : Interval gbAtlas 5 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_864 : Interval gbAtlas 5 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_896 : Interval gbAtlas 5 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_928 : Interval gbAtlas 5 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_960 : Interval gbAtlas 5 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_992 : Interval gbAtlas 5 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1024 : Interval gbAtlas 5 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1056 : Interval gbAtlas 5 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1088 : Interval gbAtlas 5 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1120 : Interval gbAtlas 5 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1152 : Interval gbAtlas 5 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1184 : Interval gbAtlas 5 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1216 : Interval gbAtlas 5 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1248 : Interval gbAtlas 5 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1280 : Interval gbAtlas 5 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1312 : Interval gbAtlas 5 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1344 : Interval gbAtlas 5 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1376 : Interval gbAtlas 5 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1408 : Interval gbAtlas 5 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1440 : Interval gbAtlas 5 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1472 : Interval gbAtlas 5 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1504 : Interval gbAtlas 5 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1536 : Interval gbAtlas 5 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1568 : Interval gbAtlas 5 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1600 : Interval gbAtlas 5 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1632 : Interval gbAtlas 5 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1664 : Interval gbAtlas 5 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1696 : Interval gbAtlas 5 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1728 : Interval gbAtlas 5 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1760 : Interval gbAtlas 5 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1792 : Interval gbAtlas 5 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1824 : Interval gbAtlas 5 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1856 : Interval gbAtlas 5 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1888 : Interval gbAtlas 5 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1920 : Interval gbAtlas 5 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1952 : Interval gbAtlas 5 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1984 : Interval gbAtlas 5 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2016 : Interval gbAtlas 5 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2048 : Interval gbAtlas 5 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2080 : Interval gbAtlas 5 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2112 : Interval gbAtlas 5 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2144 : Interval gbAtlas 5 2144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2176 : Interval gbAtlas 5 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2208 : Interval gbAtlas 5 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2240 : Interval gbAtlas 5 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2272 : Interval gbAtlas 5 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2304 : Interval gbAtlas 5 2304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2336 : Interval gbAtlas 5 2336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2368 : Interval gbAtlas 5 2368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2400 : Interval gbAtlas 5 2400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2432 : Interval gbAtlas 5 2432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2464 : Interval gbAtlas 5 2464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2496 : Interval gbAtlas 5 2496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2528 : Interval gbAtlas 5 2528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2560 : Interval gbAtlas 5 2560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2592 : Interval gbAtlas 5 2592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2624 : Interval gbAtlas 5 2624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2656 : Interval gbAtlas 5 2656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2688 : Interval gbAtlas 5 2688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2720 : Interval gbAtlas 5 2720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2752 : Interval gbAtlas 5 2752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2784 : Interval gbAtlas 5 2784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2816 : Interval gbAtlas 5 2816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2848 : Interval gbAtlas 5 2848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2880 : Interval gbAtlas 5 2880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2912 : Interval gbAtlas 5 2912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2944 : Interval gbAtlas 5 2944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2976 : Interval gbAtlas 5 2976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3008 : Interval gbAtlas 5 3008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3040 : Interval gbAtlas 5 3040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3072 : Interval gbAtlas 5 3072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3104 : Interval gbAtlas 5 3104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3136 : Interval gbAtlas 5 3136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3168 : Interval gbAtlas 5 3168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3200 : Interval gbAtlas 5 3200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3232 : Interval gbAtlas 5 3232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3264 : Interval gbAtlas 5 3264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3296 : Interval gbAtlas 5 3296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3328 : Interval gbAtlas 5 3328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3360 : Interval gbAtlas 5 3360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3392 : Interval gbAtlas 5 3392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3424 : Interval gbAtlas 5 3424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3456 : Interval gbAtlas 5 3456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3488 : Interval gbAtlas 5 3488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3520 : Interval gbAtlas 5 3520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3552 : Interval gbAtlas 5 3552 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3584 : Interval gbAtlas 5 3584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3616 : Interval gbAtlas 5 3616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3648 : Interval gbAtlas 5 3648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3680 : Interval gbAtlas 5 3680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3712 : Interval gbAtlas 5 3712 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3744 : Interval gbAtlas 5 3744 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3776 : Interval gbAtlas 5 3776 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3808 : Interval gbAtlas 5 3808 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3840 : Interval gbAtlas 5 3840 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3872 : Interval gbAtlas 5 3872 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3904 : Interval gbAtlas 5 3904 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3936 : Interval gbAtlas 5 3936 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3968 : Interval gbAtlas 5 3968 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4000 : Interval gbAtlas 5 4000 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4032 : Interval gbAtlas 5 4032 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4064 : Interval gbAtlas 5 4064 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4096 : Interval gbAtlas 5 4096 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4128 : Interval gbAtlas 5 4128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4160 : Interval gbAtlas 5 4160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4192 : Interval gbAtlas 5 4192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4224 : Interval gbAtlas 5 4224 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 4233 := (concat (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 bgb_5_224))) (concat (concat (concat bgb_5_256 bgb_5_288) (concat bgb_5_320 bgb_5_352)) (concat (concat bgb_5_384 bgb_5_416) (concat bgb_5_448 bgb_5_480)))) (concat (concat (concat (concat bgb_5_512 bgb_5_544) (concat bgb_5_576 bgb_5_608)) (concat (concat bgb_5_640 bgb_5_672) (concat bgb_5_704 bgb_5_736))) (concat (concat (concat bgb_5_768 bgb_5_800) (concat bgb_5_832 bgb_5_864)) (concat (concat bgb_5_896 bgb_5_928) (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)))))) (concat (concat (concat (concat (concat bgb_5_1056 bgb_5_1088) (concat bgb_5_1120 bgb_5_1152)) (concat (concat bgb_5_1184 bgb_5_1216) (concat bgb_5_1248 bgb_5_1280))) (concat (concat (concat bgb_5_1312 bgb_5_1344) (concat bgb_5_1376 bgb_5_1408)) (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 bgb_5_1536)))) (concat (concat (concat (concat bgb_5_1568 bgb_5_1600) (concat bgb_5_1632 bgb_5_1664)) (concat (concat bgb_5_1696 bgb_5_1728) (concat bgb_5_1760 bgb_5_1792))) (concat (concat (concat bgb_5_1824 bgb_5_1856) (concat bgb_5_1888 bgb_5_1920)) (concat (concat bgb_5_1952 bgb_5_1984) (concat bgb_5_2016 (concat bgb_5_2048 bgb_5_2080))))))) (concat (concat (concat (concat (concat (concat bgb_5_2112 bgb_5_2144) (concat bgb_5_2176 bgb_5_2208)) (concat (concat bgb_5_2240 bgb_5_2272) (concat bgb_5_2304 bgb_5_2336))) (concat (concat (concat bgb_5_2368 bgb_5_2400) (concat bgb_5_2432 bgb_5_2464)) (concat (concat bgb_5_2496 bgb_5_2528) (concat bgb_5_2560 bgb_5_2592)))) (concat (concat (concat (concat bgb_5_2624 bgb_5_2656) (concat bgb_5_2688 bgb_5_2720)) (concat (concat bgb_5_2752 bgb_5_2784) (concat bgb_5_2816 bgb_5_2848))) (concat (concat (concat bgb_5_2880 bgb_5_2912) (concat bgb_5_2944 bgb_5_2976)) (concat (concat bgb_5_3008 bgb_5_3040) (concat bgb_5_3072 (concat bgb_5_3104 bgb_5_3136)))))) (concat (concat (concat (concat (concat bgb_5_3168 bgb_5_3200) (concat bgb_5_3232 bgb_5_3264)) (concat (concat bgb_5_3296 bgb_5_3328) (concat bgb_5_3360 bgb_5_3392))) (concat (concat (concat bgb_5_3424 bgb_5_3456) (concat bgb_5_3488 bgb_5_3520)) (concat (concat bgb_5_3552 bgb_5_3584) (concat bgb_5_3616 (concat bgb_5_3648 bgb_5_3680))))) (concat (concat (concat (concat bgb_5_3712 bgb_5_3744) (concat bgb_5_3776 bgb_5_3808)) (concat (concat bgb_5_3840 bgb_5_3872) (concat bgb_5_3904 bgb_5_3936))) (concat (concat (concat bgb_5_3968 bgb_5_4000) (concat bgb_5_4032 bgb_5_4064)) (concat (concat bgb_5_4096 bgb_5_4128) (concat bgb_5_4160 (concat bgb_5_4192 bgb_5_4224))))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_0 : Interval gbAtlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_32 : Interval gbAtlas 6 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_64 : Interval gbAtlas 6 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_96 : Interval gbAtlas 6 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_128 : Interval gbAtlas 6 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_160 : Interval gbAtlas 6 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_192 : Interval gbAtlas 6 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_224 : Interval gbAtlas 6 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_256 : Interval gbAtlas 6 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_288 : Interval gbAtlas 6 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_320 : Interval gbAtlas 6 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_352 : Interval gbAtlas 6 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_384 : Interval gbAtlas 6 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_416 : Interval gbAtlas 6 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_448 : Interval gbAtlas 6 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_480 : Interval gbAtlas 6 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_512 : Interval gbAtlas 6 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_544 : Interval gbAtlas 6 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_576 : Interval gbAtlas 6 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_608 : Interval gbAtlas 6 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_640 : Interval gbAtlas 6 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_672 : Interval gbAtlas 6 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_704 : Interval gbAtlas 6 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_736 : Interval gbAtlas 6 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_768 : Interval gbAtlas 6 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_800 : Interval gbAtlas 6 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_832 : Interval gbAtlas 6 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_864 : Interval gbAtlas 6 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_896 : Interval gbAtlas 6 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_928 : Interval gbAtlas 6 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_960 : Interval gbAtlas 6 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_992 : Interval gbAtlas 6 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1024 : Interval gbAtlas 6 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1056 : Interval gbAtlas 6 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1088 : Interval gbAtlas 6 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1120 : Interval gbAtlas 6 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1152 : Interval gbAtlas 6 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1184 : Interval gbAtlas 6 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1216 : Interval gbAtlas 6 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1248 : Interval gbAtlas 6 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1280 : Interval gbAtlas 6 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1312 : Interval gbAtlas 6 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1344 : Interval gbAtlas 6 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1376 : Interval gbAtlas 6 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1408 : Interval gbAtlas 6 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1440 : Interval gbAtlas 6 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1472 : Interval gbAtlas 6 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1504 : Interval gbAtlas 6 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1536 : Interval gbAtlas 6 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1568 : Interval gbAtlas 6 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1600 : Interval gbAtlas 6 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1632 : Interval gbAtlas 6 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1664 : Interval gbAtlas 6 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1696 : Interval gbAtlas 6 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1728 : Interval gbAtlas 6 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1760 : Interval gbAtlas 6 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1792 : Interval gbAtlas 6 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1824 : Interval gbAtlas 6 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1856 : Interval gbAtlas 6 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1888 : Interval gbAtlas 6 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1920 : Interval gbAtlas 6 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1952 : Interval gbAtlas 6 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1984 : Interval gbAtlas 6 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2016 : Interval gbAtlas 6 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2048 : Interval gbAtlas 6 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2080 : Interval gbAtlas 6 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2112 : Interval gbAtlas 6 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2144 : Interval gbAtlas 6 2144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2176 : Interval gbAtlas 6 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2208 : Interval gbAtlas 6 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2240 : Interval gbAtlas 6 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2272 : Interval gbAtlas 6 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2304 : Interval gbAtlas 6 2304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2336 : Interval gbAtlas 6 2336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2368 : Interval gbAtlas 6 2368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2400 : Interval gbAtlas 6 2400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2432 : Interval gbAtlas 6 2432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2464 : Interval gbAtlas 6 2464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2496 : Interval gbAtlas 6 2496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2528 : Interval gbAtlas 6 2528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2560 : Interval gbAtlas 6 2560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2592 : Interval gbAtlas 6 2592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2624 : Interval gbAtlas 6 2624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2656 : Interval gbAtlas 6 2656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2688 : Interval gbAtlas 6 2688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2720 : Interval gbAtlas 6 2720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2752 : Interval gbAtlas 6 2752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2784 : Interval gbAtlas 6 2784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2816 : Interval gbAtlas 6 2816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2848 : Interval gbAtlas 6 2848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2880 : Interval gbAtlas 6 2880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2912 : Interval gbAtlas 6 2912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2944 : Interval gbAtlas 6 2944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2976 : Interval gbAtlas 6 2976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3008 : Interval gbAtlas 6 3008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3040 : Interval gbAtlas 6 3040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3072 : Interval gbAtlas 6 3072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3104 : Interval gbAtlas 6 3104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3136 : Interval gbAtlas 6 3136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3168 : Interval gbAtlas 6 3168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3200 : Interval gbAtlas 6 3200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3232 : Interval gbAtlas 6 3232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3264 : Interval gbAtlas 6 3264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3296 : Interval gbAtlas 6 3296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3328 : Interval gbAtlas 6 3328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3360 : Interval gbAtlas 6 3360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3392 : Interval gbAtlas 6 3392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3424 : Interval gbAtlas 6 3424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3456 : Interval gbAtlas 6 3456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3488 : Interval gbAtlas 6 3488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3520 : Interval gbAtlas 6 3520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3552 : Interval gbAtlas 6 3552 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3584 : Interval gbAtlas 6 3584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3616 : Interval gbAtlas 6 3616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3648 : Interval gbAtlas 6 3648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3680 : Interval gbAtlas 6 3680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3712 : Interval gbAtlas 6 3712 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3744 : Interval gbAtlas 6 3744 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3776 : Interval gbAtlas 6 3776 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3808 : Interval gbAtlas 6 3808 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3840 : Interval gbAtlas 6 3840 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3872 : Interval gbAtlas 6 3872 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3904 : Interval gbAtlas 6 3904 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3936 : Interval gbAtlas 6 3936 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3968 : Interval gbAtlas 6 3968 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4000 : Interval gbAtlas 6 4000 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4032 : Interval gbAtlas 6 4032 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4064 : Interval gbAtlas 6 4064 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4096 : Interval gbAtlas 6 4096 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4128 : Interval gbAtlas 6 4128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4160 : Interval gbAtlas 6 4160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4192 : Interval gbAtlas 6 4192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4224 : Interval gbAtlas 6 4224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4256 : Interval gbAtlas 6 4256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4288 : Interval gbAtlas 6 4288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4320 : Interval gbAtlas 6 4320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4352 : Interval gbAtlas 6 4352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4384 : Interval gbAtlas 6 4384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4416 : Interval gbAtlas 6 4416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4448 : Interval gbAtlas 6 4448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4480 : Interval gbAtlas 6 4480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4512 : Interval gbAtlas 6 4512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4544 : Interval gbAtlas 6 4544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4576 : Interval gbAtlas 6 4576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4608 : Interval gbAtlas 6 4608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4640 : Interval gbAtlas 6 4640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4672 : Interval gbAtlas 6 4672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4704 : Interval gbAtlas 6 4704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4736 : Interval gbAtlas 6 4736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4768 : Interval gbAtlas 6 4768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4800 : Interval gbAtlas 6 4800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4832 : Interval gbAtlas 6 4832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4864 : Interval gbAtlas 6 4864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4896 : Interval gbAtlas 6 4896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4928 : Interval gbAtlas 6 4928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4960 : Interval gbAtlas 6 4960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4992 : Interval gbAtlas 6 4992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5024 : Interval gbAtlas 6 5024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5056 : Interval gbAtlas 6 5056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5088 : Interval gbAtlas 6 5088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5120 : Interval gbAtlas 6 5120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5152 : Interval gbAtlas 6 5152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5184 : Interval gbAtlas 6 5184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5216 : Interval gbAtlas 6 5216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5248 : Interval gbAtlas 6 5248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5280 : Interval gbAtlas 6 5280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5312 : Interval gbAtlas 6 5312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5344 : Interval gbAtlas 6 5344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5376 : Interval gbAtlas 6 5376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5408 : Interval gbAtlas 6 5408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5440 : Interval gbAtlas 6 5440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5472 : Interval gbAtlas 6 5472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5504 : Interval gbAtlas 6 5504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5536 : Interval gbAtlas 6 5536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5568 : Interval gbAtlas 6 5568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5600 : Interval gbAtlas 6 5600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5632 : Interval gbAtlas 6 5632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5664 : Interval gbAtlas 6 5664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5696 : Interval gbAtlas 6 5696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5728 : Interval gbAtlas 6 5728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5760 : Interval gbAtlas 6 5760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5792 : Interval gbAtlas 6 5792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5824 : Interval gbAtlas 6 5824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5856 : Interval gbAtlas 6 5856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5888 : Interval gbAtlas 6 5888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5920 : Interval gbAtlas 6 5920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5952 : Interval gbAtlas 6 5952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5984 : Interval gbAtlas 6 5984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6016 : Interval gbAtlas 6 6016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6048 : Interval gbAtlas 6 6048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6080 : Interval gbAtlas 6 6080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6112 : Interval gbAtlas 6 6112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6144 : Interval gbAtlas 6 6144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6176 : Interval gbAtlas 6 6176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6208 : Interval gbAtlas 6 6208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6240 : Interval gbAtlas 6 6240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6272 : Interval gbAtlas 6 6272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6304 : Interval gbAtlas 6 6304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6336 : Interval gbAtlas 6 6336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6368 : Interval gbAtlas 6 6368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6400 : Interval gbAtlas 6 6400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6432 : Interval gbAtlas 6 6432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6464 : Interval gbAtlas 6 6464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6496 : Interval gbAtlas 6 6496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6528 : Interval gbAtlas 6 6528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6560 : Interval gbAtlas 6 6560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6592 : Interval gbAtlas 6 6592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6624 : Interval gbAtlas 6 6624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6656 : Interval gbAtlas 6 6656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6688 : Interval gbAtlas 6 6688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6720 : Interval gbAtlas 6 6720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6752 : Interval gbAtlas 6 6752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6784 : Interval gbAtlas 6 6784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6816 : Interval gbAtlas 6 6816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6848 : Interval gbAtlas 6 6848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6880 : Interval gbAtlas 6 6880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6912 : Interval gbAtlas 6 6912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6944 : Interval gbAtlas 6 6944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6976 : Interval gbAtlas 6 6976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7008 : Interval gbAtlas 6 7008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7040 : Interval gbAtlas 6 7040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7072 : Interval gbAtlas 6 7072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7104 : Interval gbAtlas 6 7104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7136 : Interval gbAtlas 6 7136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7168 : Interval gbAtlas 6 7168 17 := block_range (n:=17) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 7185 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)) (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 bgb_6_416)))) (concat (concat (concat bgb_6_448 (concat bgb_6_480 bgb_6_512)) (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640))) (concat (concat bgb_6_672 (concat bgb_6_704 bgb_6_736)) (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 bgb_6_864))))) (concat (concat (concat (concat bgb_6_896 (concat bgb_6_928 bgb_6_960)) (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 bgb_6_1088))) (concat (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184)) (concat (concat bgb_6_1216 bgb_6_1248) (concat bgb_6_1280 bgb_6_1312)))) (concat (concat (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408)) (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 bgb_6_1536))) (concat (concat bgb_6_1568 (concat bgb_6_1600 bgb_6_1632)) (concat (concat bgb_6_1664 bgb_6_1696) (concat bgb_6_1728 bgb_6_1760)))))) (concat (concat (concat (concat (concat bgb_6_1792 (concat bgb_6_1824 bgb_6_1856)) (concat (concat bgb_6_1888 bgb_6_1920) (concat bgb_6_1952 bgb_6_1984))) (concat (concat bgb_6_2016 (concat bgb_6_2048 bgb_6_2080)) (concat (concat bgb_6_2112 bgb_6_2144) (concat bgb_6_2176 bgb_6_2208)))) (concat (concat (concat bgb_6_2240 (concat bgb_6_2272 bgb_6_2304)) (concat (concat bgb_6_2336 bgb_6_2368) (concat bgb_6_2400 bgb_6_2432))) (concat (concat bgb_6_2464 (concat bgb_6_2496 bgb_6_2528)) (concat (concat bgb_6_2560 bgb_6_2592) (concat bgb_6_2624 bgb_6_2656))))) (concat (concat (concat (concat bgb_6_2688 (concat bgb_6_2720 bgb_6_2752)) (concat (concat bgb_6_2784 bgb_6_2816) (concat bgb_6_2848 bgb_6_2880))) (concat (concat bgb_6_2912 (concat bgb_6_2944 bgb_6_2976)) (concat (concat bgb_6_3008 bgb_6_3040) (concat bgb_6_3072 bgb_6_3104)))) (concat (concat (concat bgb_6_3136 (concat bgb_6_3168 bgb_6_3200)) (concat (concat bgb_6_3232 bgb_6_3264) (concat bgb_6_3296 bgb_6_3328))) (concat (concat bgb_6_3360 (concat bgb_6_3392 bgb_6_3424)) (concat (concat bgb_6_3456 bgb_6_3488) (concat bgb_6_3520 bgb_6_3552))))))) (concat (concat (concat (concat (concat (concat bgb_6_3584 (concat bgb_6_3616 bgb_6_3648)) (concat (concat bgb_6_3680 bgb_6_3712) (concat bgb_6_3744 bgb_6_3776))) (concat (concat bgb_6_3808 (concat bgb_6_3840 bgb_6_3872)) (concat (concat bgb_6_3904 bgb_6_3936) (concat bgb_6_3968 bgb_6_4000)))) (concat (concat (concat bgb_6_4032 (concat bgb_6_4064 bgb_6_4096)) (concat (concat bgb_6_4128 bgb_6_4160) (concat bgb_6_4192 bgb_6_4224))) (concat (concat bgb_6_4256 (concat bgb_6_4288 bgb_6_4320)) (concat (concat bgb_6_4352 bgb_6_4384) (concat bgb_6_4416 bgb_6_4448))))) (concat (concat (concat (concat bgb_6_4480 (concat bgb_6_4512 bgb_6_4544)) (concat (concat bgb_6_4576 bgb_6_4608) (concat bgb_6_4640 bgb_6_4672))) (concat (concat bgb_6_4704 (concat bgb_6_4736 bgb_6_4768)) (concat (concat bgb_6_4800 bgb_6_4832) (concat bgb_6_4864 bgb_6_4896)))) (concat (concat (concat bgb_6_4928 (concat bgb_6_4960 bgb_6_4992)) (concat (concat bgb_6_5024 bgb_6_5056) (concat bgb_6_5088 bgb_6_5120))) (concat (concat bgb_6_5152 (concat bgb_6_5184 bgb_6_5216)) (concat (concat bgb_6_5248 bgb_6_5280) (concat bgb_6_5312 bgb_6_5344)))))) (concat (concat (concat (concat (concat bgb_6_5376 (concat bgb_6_5408 bgb_6_5440)) (concat (concat bgb_6_5472 bgb_6_5504) (concat bgb_6_5536 bgb_6_5568))) (concat (concat bgb_6_5600 (concat bgb_6_5632 bgb_6_5664)) (concat (concat bgb_6_5696 bgb_6_5728) (concat bgb_6_5760 bgb_6_5792)))) (concat (concat (concat bgb_6_5824 (concat bgb_6_5856 bgb_6_5888)) (concat (concat bgb_6_5920 bgb_6_5952) (concat bgb_6_5984 bgb_6_6016))) (concat (concat bgb_6_6048 (concat bgb_6_6080 bgb_6_6112)) (concat (concat bgb_6_6144 bgb_6_6176) (concat bgb_6_6208 bgb_6_6240))))) (concat (concat (concat (concat bgb_6_6272 (concat bgb_6_6304 bgb_6_6336)) (concat (concat bgb_6_6368 bgb_6_6400) (concat bgb_6_6432 bgb_6_6464))) (concat (concat bgb_6_6496 (concat bgb_6_6528 bgb_6_6560)) (concat (concat bgb_6_6592 bgb_6_6624) (concat bgb_6_6656 bgb_6_6688)))) (concat (concat (concat bgb_6_6720 (concat bgb_6_6752 bgb_6_6784)) (concat (concat bgb_6_6816 bgb_6_6848) (concat bgb_6_6880 bgb_6_6912))) (concat (concat (concat bgb_6_6944 bgb_6_6976) (concat bgb_6_7008 bgb_6_7040)) (concat (concat bgb_6_7072 bgb_6_7104) (concat bgb_6_7136 bgb_6_7168))))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_32 : Interval gbAtlas 7 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_64 : Interval gbAtlas 7 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_96 : Interval gbAtlas 7 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_128 : Interval gbAtlas 7 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_160 : Interval gbAtlas 7 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_192 : Interval gbAtlas 7 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_224 : Interval gbAtlas 7 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_256 : Interval gbAtlas 7 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_288 : Interval gbAtlas 7 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_320 : Interval gbAtlas 7 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_352 : Interval gbAtlas 7 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_384 : Interval gbAtlas 7 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_416 : Interval gbAtlas 7 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_448 : Interval gbAtlas 7 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_480 : Interval gbAtlas 7 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_512 : Interval gbAtlas 7 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_544 : Interval gbAtlas 7 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_576 : Interval gbAtlas 7 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_608 : Interval gbAtlas 7 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_640 : Interval gbAtlas 7 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_672 : Interval gbAtlas 7 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_704 : Interval gbAtlas 7 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_736 : Interval gbAtlas 7 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_768 : Interval gbAtlas 7 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_800 : Interval gbAtlas 7 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_832 : Interval gbAtlas 7 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_864 : Interval gbAtlas 7 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_896 : Interval gbAtlas 7 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_928 : Interval gbAtlas 7 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_960 : Interval gbAtlas 7 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_992 : Interval gbAtlas 7 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1024 : Interval gbAtlas 7 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1056 : Interval gbAtlas 7 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1088 : Interval gbAtlas 7 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1120 : Interval gbAtlas 7 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1152 : Interval gbAtlas 7 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1184 : Interval gbAtlas 7 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1216 : Interval gbAtlas 7 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1248 : Interval gbAtlas 7 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1280 : Interval gbAtlas 7 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1312 : Interval gbAtlas 7 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1344 : Interval gbAtlas 7 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1376 : Interval gbAtlas 7 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1408 : Interval gbAtlas 7 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1440 : Interval gbAtlas 7 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1472 : Interval gbAtlas 7 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1504 : Interval gbAtlas 7 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1536 : Interval gbAtlas 7 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1568 : Interval gbAtlas 7 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1600 : Interval gbAtlas 7 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1632 : Interval gbAtlas 7 1632 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1648 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat bgb_7_96 (concat bgb_7_128 bgb_7_160))) (concat (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)) (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 bgb_7_384)))) (concat (concat (concat bgb_7_416 (concat bgb_7_448 bgb_7_480)) (concat bgb_7_512 (concat bgb_7_544 bgb_7_576))) (concat (concat bgb_7_608 (concat bgb_7_640 bgb_7_672)) (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 bgb_7_800))))) (concat (concat (concat (concat bgb_7_832 (concat bgb_7_864 bgb_7_896)) (concat bgb_7_928 (concat bgb_7_960 bgb_7_992))) (concat (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088)) (concat (concat bgb_7_1120 bgb_7_1152) (concat bgb_7_1184 bgb_7_1216)))) (concat (concat (concat bgb_7_1248 (concat bgb_7_1280 bgb_7_1312)) (concat bgb_7_1344 (concat bgb_7_1376 bgb_7_1408))) (concat (concat bgb_7_1440 (concat bgb_7_1472 bgb_7_1504)) (concat (concat bgb_7_1536 bgb_7_1568) (concat bgb_7_1600 bgb_7_1632))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 34 := (concat bgb_8_0 bgb_8_32)
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 4 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 28, 30),(inputs.getD 2 zero, 26, 30),(inputs.getD 3 zero, 22, 30),(inputs.getD 4 zero, 14, 30),(inputs.getD 5 zero, 14, 46)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 4 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 33, 49),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 33, 41),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeaaaeaa8eaa8a8a8eaaaeaa8eaa8a8a8eaaaeaa8eaa8a8a8eaaaeaa8eaa8a8a8eaaaeaa8eaa8a8a8eaaaeaa8eaa8a8a8eaaaeaa8eaa8a8a8eaaaeaa8eaa8a8a8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (3937069736 * 2 ^ 32 + 3936921768) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37367.Model.Repr at out
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

def mono : List Gate := [⟨.and,[4,5]⟩,⟨.or,[2,6]⟩,⟨.and,[0,7]⟩,⟨.or,[4,5]⟩,⟨.and,[1,2]⟩,⟨.and,[3,9]⟩,⟨.or,[8,11]⟩,⟨.or,[0,10]⟩,⟨.and,[12,13]⟩,⟨.and,[0,1]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3937069736 * 2 ^ 32 + 3936921768) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3937069736 * 2 ^ 32 + 3936921768) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37367

open PEqualNP.Outside.L_meta_37367 in
theorem PEqualNP.Outside.L_meta_37367 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3937069736 * 2 ^ 32 + 3936921768) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3937069736 * 2 ^ 32 + 3936921768) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
