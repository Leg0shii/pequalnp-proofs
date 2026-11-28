import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37101.Model
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


end PEqualNP.Outside.L_meta_37101.Model

namespace PEqualNP.Outside.L_meta_37101
open PEqualNP.Outside.L_meta_37101.Model
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

def SBf (j : Nat) : Nat := [5, 7, 5, 6, 6, 8].getD j 0

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

end PEqualNP.Outside.L_meta_37101

namespace PEqualNP.Outside.L_meta_37101
open PEqualNP.Outside.L_meta_37101.Model
def s0K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x40628a042f195c32bc6370c6f985d30
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0xd1000096418ca390a318c424c2510530
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (i*4) 4
  | 3 => packedAt s0K3 (i*15) 15
  | 2 => packedAt s0K2 (i*26) 26
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (5+((h/1+packedAt s0K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s0K3 (96+((h/2+packedAt s0K3 (90+(h % 2)*3) 3) % 8)*4) 4
  | 2 => packedAt s0K2 (107+((h/1+packedAt s0K2 (104+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffdff3ffff1ffff1ff
  | 2 => 0xffffffffffffffffffffffedfc7f3fe3f0fe73
  | 3 => 0x76ff8fcffc7f0f9c
  | 4 => 0x78fff00fff800fe0
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffa0180202049440a5
  | 2 => 0x122324452122a652
  | 3 => 0x9416819484a2b18
  | 4 => 0x78a4eae920ccde0
  | _ => 0
def s0Atlas : Atlas := ⟨4,rawDecor 30 s0Pos s0Neg, 0xfcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37101
namespace PEqualNP.Outside.L_meta_37101
open PEqualNP.Outside.L_meta_37101.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x195a016000078ea640a0a803e389a9421c108445808a2e4159a0000c23180000f000128b1a002090c709244ea829b280c8953c004c1000c02c0146042ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31de31fd31fc31dc31ff21fe21ee21fd21fc21ec21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x490624002e221400006a7200006e5b25424f273900450b4d00031d093b54351f6521122a07576c2d3123081b2c00000000361c603e002851406f4317640f480c520070200011623456005e1e5971192602154c470038675f7400186600584e6d4a2f6101040e3d3a4133304b63503f05556816696b133c00105d0d29375c4600322b001a0073440000535a0a00020001878303810984808d0085050500000002018000800483871d81008380060200860c01965b94b43b6a96877651d0eeaa3a1d794f42aea9e857651d0aeaa3a15dd4532ba28a65cd320cabca7a0d754f41b7296836d52d06bea6a0d714d41b7a92836c52506f6a0a0de14141b7296636d52cc6bca318dbd4931b6292633e540c67aa818e795031ceaa0635e510c7aca218f590431eaa08635e53c86baa790f50c721b728c43ce31887986310d7d4d21ae29a433e540867aa810f50c421d72a043ad54086dca210f994421f320843e541087ce6210f38c421e618843e431087886210e78c640ce18c81ae219035843204f94240af298815d53102dca4205b54840bb2888175511033ca6206754c40d729081ad521036ca2206d54440cf188819c311035c42206b084409f28081ba501027ca9984f553309faa2613c544c2dea4985b14930bba8a6174514c2dca4185b548309f2a6413d54c827ea8904f15120afa9a415c53482eea2905d14520af298415d530827ca9884f55310dc206215e53842baa7085b94a10b6a9421d431843c843084fd51109e2a2215f53442b8a6885bd4910b629221d431043c842086e10010
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x2c08c11242a5801ae70a92622850000001800e00069e8a04a00004ca2b1185320cac46250431b4181410c715540c421b118d41086e06050421b198631086a5640c421e19903108785640c421e19503108785540c421e10c421903155354440c9549511021d650c4408b5942110384310844099185520c2546154c20d194831843465308610e40c440043a02110010
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x60200020000a0aeb3206210c85769503108682ba86210881815943108440
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
  | 6 => packedAt s1K6 (6+((h/1+packedAt s1K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s1K5 (826+((h/15+packedAt s1K5 (736+(h % 15)*6) 6) % 56)*7) 7
  | 4 => packedAt s1K4 (3471+((h/39+packedAt s1K4 (3159+(h % 39)*8) 8) % 141)*8) 8
  | 3 => packedAt s1K3 (952+((h/8+packedAt s1K3 (912+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s1K2 (200+((h/1+packedAt s1K2 (196+(h % 1)*4) 4) % 15)*3) 3
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
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaaf0a0a000faaaaaaaf0a0a000faaaaaaaf0a0a000faaaaaaaf0a0a000faaaaaaaf0a0a000faaaaaaaf0a0a000faaaaaaaf0a0a000faaaaaaaf0a0a000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37101
namespace PEqualNP.Outside.L_meta_37101
open PEqualNP.Outside.L_meta_37101.Model
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
  | 4 => packedAt s2K4 (6+((h/1+packedAt s2K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x1fffffe03ff81c1ffffe0fffff81ff007cfe7c
  | 1 => 0xe07e07ffffffffe0f81ff0780fffffff9333ff
  | 3 => 0xff8007ffc1ffffff001fff800ffe0fffe3c38f
  | 4 => 0x7fffe001fffffe000000ffff001fc03f0
  | 5 => 0xfffff80000001ffffffffffff0000001fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xc30c40238410a40318a60288e390990c24563c
  | 1 => 0x49108a4490a208a06a0a905124a322549130d5
  | 3 => 0x842554890d44954d04952b0249548ca962c30a
  | 4 => 0x1659e7122876de76b6c18a448e79c831fc03e0
  | 5 => 0x1861861c31871b98c719cc67006100c1dba800
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 59 s2Pos s2Neg, 0xeeaaeeaacc88cc00eeaaeeaacc88cc00eeaaeeaacc88cc00eeaaeeaacc88cc00eeaaeeaacc88cc00eeaaeeaacc88cc00eeaaeeaacc88cc00eeaaeeaacc88cc00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37101
namespace PEqualNP.Outside.L_meta_37101
open PEqualNP.Outside.L_meta_37101.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x62008a00420de43dd43be40bc40de30dc30
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x82b0a0a1e610030
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 6
  | 3 => 2
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (i*5) 5
  | 4 => packedAt s3K4 (i*16) 16
  | 3 => packedAt s3K3 (i*27) 27
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (6+((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s3K4 (104+((h/2+packedAt s3K4 (96+(h % 2)*4) 4) % 9)*4) 4
  | 3 => packedAt s3K3 (56+((h/1+packedAt s3K3 (54+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x7fffff01fffe0c1ffffc1ffffe0ffe00f3f3fc
  | 1 => 0x81f83ffe0fffffe0f83fe1e03ff0ffff4ccc7f
  | 2 => 0xfe003ffff07fffff003ffe003fff0fff8f0f8f
  | 4 => 0x3fffff800fffffc000003ffff003f00ff0
  | 5 => 0xffffc00000000fffffffffffc0000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xc30011c21041003184c02238e0112181151bc
  | 1 => 0x24425224642884a06a1521449290a4a944c455
  | 2 => 0x1094a4488351094d042a5409252a09528b0a8a
  | 4 => 0x596738914a1dae76b683111239ccc063f00f60
  | 5 => 0x618630e18c61cf98c733999c01888183eea000
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeaeaeaeae8e8c0c0eaeaeaeae8e8c0c0eaeaeaeae8e8c0c0eaeaeaeae8e8c0c0eaeaeaeae8e8c0c0eaeaeaeae8e8c0c0eaeaeaeae8e8c0c0eaeaeaeae8e8c0c0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37101
namespace PEqualNP.Outside.L_meta_37101
open PEqualNP.Outside.L_meta_37101.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x80be40bc40
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
  | 5 => packedAt s4K5 (6+((h/1+packedAt s4K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s4K4 (34+((h/1+packedAt s4K4 (32+(h % 1)*2) 2) % 3)*2) 2
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
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xeeeaeeeaecc0ecc0eeeaeeeaecc0ecc0eeeaeeeaecc0ecc0eeeaeeeaecc0ecc0eeeaeeeaecc0ecc0eeeaeeeaecc0ecc0eeeaeeeaecc0ecc0eeeaeeeaecc0ecc0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37101
namespace PEqualNP.Outside.L_meta_37101
open PEqualNP.Outside.L_meta_37101.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xa43ee32487da6490fdc8521f710a437f50487f6a090ded4121be28243f850486f0a090dfd5021bf2a043be540867ca810df55021deaa0433d54086f8a810dfd4c21bf29843de53086bca610df54c21eea98435d53086f8a610df94821bf28843ef21087ec4210fb48421fa908437e50087f4a010de94021bea8043f950086f2a010df94f40bea9e81bf43d037a87a05f94b40bea96817e51d02faa3a05f55240bf29c817d539037c87206f10e40bf294817d529037c85206f10a40bf28c817d519037e83206f50640bf28481bf40903f681205fd4d40be29a81bf435037a86a05fd4940be292817f51502f8a2a07ed0140df202817e54102fca6207794c40af298817d53103baa6205754c40df21881bc43102fca4205f54840df21081bc42102fca2205f54440dfa0881bd41102fca0206fd0040fd20081bd40103f280206e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30bf28e617d51cc3f681987e10330bfaa4617e548c2faa9185f15230bea9c617e528c2faa5185f94630bea8c617e508c3f481187e50230ef98461fb308c2fea8986fd51309faa2617e544c2faa8985f15130de2a2613c544c3bc86987750d30bfa92617c524c2fea2985f14530fd20261f9404c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf298617e520c2faa4185f94430bea88617e500c3f680187e10030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c83f681907e10320fd18641f930c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5105f94620bea8c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a417e53482faa6905f14d20bfa8a417c51483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20bf290417e51082faa2105f94020fda0041f840083f460107e4c020f790041fa20083da40107e48020bfaa6217e54c437ca9884f95310beaa621bd54c427aa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fd90621f820c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fda0421f840843f461087e4c210fd10421f920843ee21087ec4210bfaa2217e54442faa8885f15110bfa9a217e53442faa6885f14d10bfa92217e52442faa4885f14910fda0221f840443f460887e4c110fd10221f920443f620887d84110bfaa0217e54042faa8085f15010bfa98217e53042faa6085f14c10bfa90217e52042faa4085f14810bf288217e50043f640087e08010fb88021fa10043ea20087e44010
  | 1 => 0x601800018060000000002000000000600804005f94b43bea96877e51d0efaa3a1df94343bea86877d5490efca721efd0e43efa1c877e5290efaa521df94643bea8c877e5090efaa121f7d0d43df21a877f5250ef8a4a1dfd4543be28a877f5050ff6a0a1ded4143be28287f85050ef0a0a1df95043bf29887bf4310fbc8621ef50c43eea18877e5210efaa421df94443bea88877e5010ff4a021de94043bea8087f95010ef2a021df94f42bea9e857e51d0afaa3a15f94342bea86857d5490afca7215f54e42dfa1c85bd4390afca5216fd0a42f7a14857e5190afaa3215f94242bea84857f5350af8a6a17bd0942df212857f5150af8a2a15fd4142fda82857b5050af8a0a17e14142bc282857e5410afca6215f54c42dfa1885bd4310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0215fd5332bf2a665be54cca7ca9995f55332deaa6653d54ccaf8a9995f94732bea8e657e50ccbf4a1995e94332bea8665f950ccaf2a1995fd5232bf2a4657d548caf8a9195f54e32bf29465df328cbde65195f94632bea8c657e508cafaa1195fd5132bf2a2657d544caf8a8997bcc932ef192657f514caf8a2995fd4132be282657f540cafca8195f55032be2a0657e530cafca41977cc832f719065dd320cbda64195f94432bea88657e500cafaa0195f94f41bea9e83bf43d077a87a0df94b41bea9683bf42d077a85a0df94341bea86837d54906fca720df54e41bf294837d529077c8520ef10a41bf28c83bf41907ee8320df94241fd284837a50906faa120fe54241bca84837f53506f8a6a0efd0d41dea1a837f52506f8a4a0efd0941dea1283f7415077c82a0dfd4141be282837e54106fca620df54c41bf290837d521077c8420ef10841bf28883bf41107ec8220ef50441faa08837e50106faa020dfd5331bf2a6637d54cc6f8a998df94b31bea9663df32cc7ba6598df94331bea86637f548c6fca918df55231be2a4637d538c6fca518df54a31ef19463dc328c6fca318f7cc631fb98c637e508c6faa118dfd5131bf2a2637d544c6f8a898dfd4931be29263df324c7ba6498fdcc531ef18a637f504c6f8a098dfd5031bf2a063be540c67ca818df55031deaa0633d540c6f8a818df94c31bf29063ee520c6dca418df54831f6a90636d520c7bc6418f70c831bf28863df310c7ec6218f74c431fa988637e500c7f4a018de94031bea8063f9500c6f2a018dfd5321bf2a6437d54c86f8a990dfd4f21bf29e437d53c86f8a790fb8cb21f6996437e50c86faa190dfd5221bf2a4437d54886f8a910dfd4e21bf29c437d53886f8a710df54a21bf28c43ef21887ee4310df94221bea84437f544877ea890cfd5121bf2a2437d54486f8a890ef151219e2a2437f53487bea690d7d4d21bf29a437d53486f8a690f714d21ae29
  | 2 => 0x14e2ec000d40000001fce418f13c7a51400038456d120000003f40d8002280006aa26282778c70e518e0000002c25403400000378000000000004ec0008f0006a85d195034000001fa0000000002f2a0220000000004681c90f0005c80000001000906000412001259511c610c00000000000170cb000000000003aa69cb096c3ae370ba024000000f5800288000000000000008d98a1e84dc760a23942e0198ae356000000cc000000000000000009308d3a6334fa06025c3b43204c000148e1800000000fb80039a59c6197f08a388000002a80000988a0f64641d0001ae000a416f38e524ac99e470000a90003fe40c7c81d4a642c41a170004a11a0ad0003e80005c0000003e00049e0000000048e000000b12e60000000007e001290001c024c330003e64902300b04c298000b50dc000000003260ec5410a2f8000091fe1420001b0dd49a0d000000000000741040f29300000033e000558e90d43fc0000021004091000322000c49df000000000001344f8268d13a47b80b80010480cdc979000000001120000000000035e500000000006c9040b9000214cb8001225a8d494224e1ccc105300a3dc1594326a308a9892222000f791d0000000010e368210848002e02bc4c800190000001132661ac001cc0006d4df8e40000000006100088800000000000c201f07a000880004627c4cd8002560009098c34c2f465187000000ac00013a000001863b84fd0090d14e000000002ee0002f800000218001bd434000c180020c89c0000c472740be8001e2774118900001090ea2e302480b41e30004040020b17c000000000ee0000000000079c4a93d0a034c002103f06f86a00000000000180000000000000001d8929b71ec534f0000000250b2a1e1ea8b0dc0da2bc2b0b1130332714709db340431242182c812400000000000d10002c0918d9800000000000000005684c0003ca8380000029e1f4000ce0b2000afa2b0008a4000000005290f8210000000006f0000000009b3f8000001e612c25c001ec47c0003680000000000000000660000000000000001c0e8000038000002310c844000000000ee0007900000001e7444e2133f6058b580001a00008008000080000000028000180000802038100180003800010040080a00002050000680a030060100002032008180200c028020080202000008040180a00008008000280004000000020200a04804010040401e07804000000100000804008020400400802028040000000004018000000a038060280404806008080380605000020020000a008020003e008000080000000028240000006000000040100e01800018000000601800018000c000020000000c018020100200000008000000401002030020580203006018000080202000028020000a0000000006008000080401800008
  | 3 => 0x25a4d8001392380007d8000006b1020a00009385819d0628fc240d80000011d02a000000000621fc000000d209c2ec0021b0005b4000001800000015c36c6584084a000001280062680005f8720008d46f0003b28f10b1630a2200001ce392894100001cc8840000044078902800000178001f50000011b1e83fa0c12b9921527a8e00df000904049d4494769088001e6760dd8002f47e4781ba0fc1e00013a46e81c0000016e0440003c2e233c208b3182924360000000000000000000000040000000d80000008002a9f0454324002420e0954ca2150000000023209e4c4000000000001f12c0008f49c185000238791c40000941a863278340001573820003a80018c358758004b00001399c000598000f840c19d178004466c52a000000000001ad0004bd068d935c72c5b1463161c42d21414841c0500023e45d1980000000000000000000b7100000001228541b65d4bc0222522240000041e000000000006840000010e0e00005700000000118246000cd02913e871288000001940000028e0100c8000001a0aa9883e4000000000001591d8000b622d011cf264050f6a300d2054c6a562ac9100197e480515218a5000000a600005a0008f11606e784d181e154000000000b00003d0001ce000d28c50002f0140010002d0000002040005900e000414b48000003bc000003ac3f0bd80045a3a8fb0c408e174519c64145750919029612c8a81806469000
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x6530871e5494c21c7552530871e5454c21c7551530863e6414c218f590530865e6314c219b988530867a6014c219e580530874d53c84219bd95210874d53484219dd95210873a5494021ce552500875a5394021d654e500873a5454021ce551500875a5354021d654d50086b86050f40ae580439023e65d0d40ae18143503586054c408f596431031d5390c40c754c43102b96010c40c754e421031d5310840ae580421031d53d0440ae583411031d5350440c754f40102b96490040d654e401023f6550040c754d401027b6550040d654d40102bb6550040ced9540102b86350040e694d40103395350040e654d40103195350040ae18940102bb61500409b98b54cc26d62d5330b618143cc39943d0330ced5040cc2d96310330e690c40cc23f6454a308f191528c23e64946308f592518c33854502308f992544c27b60551308f994544c31d6315130ce580544c31c5490d3097195434c27a6590130ce152404c39a43901309e195404c3385450130e650d404c33854cc1308f596540c33860550308f990540c25e63150309e980540c27965d0030ce553400c2796510030ce550400c2d96310030c7553300c339548c03097d95300c31d544c0309ed95300c2b8644c030ce551300c25e63d53209758f54c823e64d4f208f59353c823e6494f208f59253c833b5410320b658c40c82b8644c320d694d30c825e63152209758c548823e6414e208f590538823e64946208f592518823e64951209ed81544823e65151208f992534823d6494d209e582534823f6454d208f19153482776154d209d185534833854c81209798c540825d63150209d984540827561150208f990530823d6414c209d98453082756114c209e59440083395410020b658c4008279658c020ae191300826f65480209ed9520082b864480208f99353c423d64d4f108f99053c423d6414f109b98853c426d6214f108f99352c423d64d4b108f99052c423d6414b109798c52c425d6314b10ce95320c433a54083109798c548425d63152108f990538423d6414e108f993528423d64d4a109798f528425d63d4a10ce55040842d96310210ae19130842b86448210ae993108425f63551109718d544426f62551109b189544423f6454d108f191534426f6254d109b189534423e6414d108f590534423f64549108f191524425f63549109718d524427b60549109e99740443395410110b658c4044278654c110ae1913044358534c1109e99620442786548110ae19120442ba64c41109e983540425e63150109758c540426e62150109b588540423e6414c108f590530426e6214c109b588530427a6014c108fd91520423c64548108f990520423d64148109798c520425d63148109e980520423e64944108f592510427965c80109e594200427965840109dd95100427b6544010
  | 1 => 0x316000000100100007010030003a00c030140501000000140040300001004020100201c0a0000200003000000000b01c0101c000000300002030020000100000010010040100001000030000b01c0000800010000000101801000000040a004040040100c00010000080000002008000000200400000010000500400008000000100803004020000b0000400801000010000000801014000100100c0700000000000100100c059ed8152d0e786054b439e98251d0e796094743ce90c5050e3f6550c43ae1814310e5f6550c43ced0d5010f5a4354043ce50d5010f5943540439e98251d0a7960947429e9825390a796094e42c794d4390ab86050e42ce9085050ab86050c428fd954210ab860508429bd954210a7a60d53329e58354cca7a60153329e58054ccb3a5494332ce55250ccb3a5454332ce55150cca7a60d52329e583548ca7761551329d185544ca7b60551329e181544ca3e64145328f590514ca7a60145329e580514ca7b60550329e181540ca7661150329d584540ca7a60150329e580540ca3e6494c328f592530ca5f654c8329bd95320ca3f64540328f191500cab86050f41ae18142d073a4294241ce10a509073b41942419e98053506796014d41c714d43506b86050d418f99742506b86050941ae982415067b60548419e181521063d65908418fd95411067765504419ed8154cc67860553319e98054cc67960153318fd9150cc63c64543319e983548c67960d52318fd91528c63c6454a319ed81528c6786054a319bd89544c66c62551319ed81544c678605513197997324c66e62d50319b58b540c67a60d50319e583540c63d65950318f990540c66e62150319b588540c67a60150319e580540c72e5494831cb552520c72e5454831cb551520c65d658c831d354a320c74d520c831d354b310c65f654c431d3549310c677654c431ce952500c7395494031da94a500c7695294031ce951500c7395454031da949500c76952540319ed8154c867860553218f99253c863d6494f219e98253c86796094f218fd9150c863c64543219e983548867960d52218f990538863d6414e219e98053886796014e218f992544865e63951219758e544867a60951219e582544865f63551219718d544867b60551219e181544863e6515121c7d53534871c54d4d218f992534863d6494d219798e534867a6094d219e582534863f6454d218f191534867b6054d219e181534865e6514d21c7d50534871c5414d21d3588534874c538c9219b19532486e4614c921ced53504873854d4121d6d4f504875853d4121ced5050487385414121d6d4c504875853141219798f540865d63d50219e983540867960d50218f596540863e64150219798c540865d63150219e980540867960150218f993530863d64d4c219e983530867960d4c219759
  | 2 => 0x1ea0025c8fa12000e20000c4c000000000000014800001b2ab9fab79b869886b412ab52ac6a2dc1b92eba28451ac876a6613000000e6610da298d4141566680000000000124e800000000000000000300006d0004714800000001103d000000002522a3b8000f2920000000000000000010ea792800312271008c88c000b20020c570006b00000180000000000049000002100016e001ba7b000001aa00000180fa000cc48068000000013e002fa000007b8000000000000000001cab400000000000010800000078005f20a1f0003d80029000000f22da62af97a178009409627978b8000000000000000000000000000000058a30005d1d6000000012200000000000e00000000c40002e800001cc0011ac09640001890000000008b8000000e000000a0008d0000000000000000004d21e000000006c4b0d601800152047c07ac5000000000000000000720000a9fc000000024a00230b60301f8ec3e09846000002d2241f60000000000001420003a000dc003080022295800000fe0200000000000ea000000980055000b3944002fe220041700000000a9800781b60025a00000000006780007168001bc7280038272b8a487180050000a38100017e821d23f10ab584e1d000001360023a129dc00000b100000286000007600a000005c000bb0009a80000000961260000079950210b00c85a000b8002260000047ac60da6400106001f20021c838000000000162a693c3920000000919025611232914882f0200009e276312b2002f8001b00014e4e0009d08aa5000000000018a73882a2800002a800000000000b2c2002bc0018e002b60000053190980c294856c295a78a8000a6cc18342f078459941884200236088700000000152000001d8001223c85066002cabca7011aea2f8c677800ae8000000000000000b4000d2000002b9ae0000086290c02884cac023a828e24c630aa411f85a800288407026e002fc082e4a58e87089a00000662f40000000000ac0000000000000001be001e8001f400000248009f9c4000a80015e0000000192000000000000000c1000000009e960000005d800190001aa9890824658d8431a486800688a0ae2da0019c0000000000682240000000000c38ac8b0000000000000a880000228001d400000bb800002e60003e000d00029c3780000000000000000000000002a4000000024e000009a01a7f80000044740009f14a05000002440000000000a8000000000000032000338000000000182000000580000000001e40000081a02620000025eaa800c31863c000002165b254b3172002f60b966000000
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x2808001c400db4ab03b2b8888058469400c912026600b1e00a8060031402401c6143a32e129a872161a531814390a8cb80a6a1a838614c6050d41c32a6b00842061953583411030c3b2a6a00818654c6250040c32a7b0a802052a72d5040cc30daa2c620661265da4310330c32c6b00a89861a6590e404c28c3aa86a0261865516310030870ecaa2601851a73d5040c830daa2c620641465d2534c320c30c929a61906195458c400830caa2c620421461cd5410110a50e4aa080886195458c404428cba0a69822186190534c110
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x60a0a0a82d51631033081987192534c320a0882551631011081987190534c110
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 601
  | 4 => 396
  | 3 => 28
  | 2 => 4
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
  | 7 => packedAt s5K7 (6+((h/1+packedAt s5K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s5K6 (718+((h/13+packedAt s5K6 (640+(h % 13)*6) 6) % 49)*7) 7
  | 5 => packedAt s5K5 (18227+((h/200+packedAt s5K5 (16227+(h % 200)*10) 10) % 960)*11) 11
  | 4 => packedAt s5K4 (16368+((h/132+packedAt s5K4 (15048+(h % 132)*10) 10) % 764)*10) 10
  | 3 => packedAt s5K3 (1426+((h/9+packedAt s5K3 (1372+(h % 9)*6) 6) % 37)*6) 6
  | 2 => packedAt s5K2 (243+((h/1+packedAt s5K2 (240+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xc0ffff01ffc3f10fc3e1f1ffe3fc0e0443f7cc
  | 1 => 0xff03fffe0ffffff003fffe1ffc3ffff87c78ff
  | 2 => 0xfffc1ffff003fffffc01ffe1ffc00fff8f8f0f
  | 3 => 0x1ffffffc01fffffe0001fffff007f00ff0
  | 4 => 0xffffe000000001fffffffffe00000007fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x5618d11c62a4a302e0f07132e264623441b3cc
  | 1 => 0x82480224240100200122920424092490145055
  | 2 => 0xc214448818a405544012441488089618a8d0a
  | 3 => 0x28b2989109206599aa5401119332c046e00ea0
  | 4 => 0x30c310e1ce3389ee3399c998022301877f6000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfce8ecc0fce8ecc0fce8ecc0fce8ecc0fce8ecc0fce8ecc0fce8ecc0fce8ecc0fce8ecc0fce8ecc0fce8ecc0fce8ecc0fce8ecc0fce8ecc0fce8ecc0fce8ecc0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37101
namespace PEqualNP.Outside.L_meta_37101
open PEqualNP.Outside.L_meta_37101.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x11254f028d403179f0001c0074d4e000089880128dc8a1e040005cb00287a183b06e21a363a915844c845bb0600db22e949ad2c9ca186644c900068f002a380005264181051004000000c48010087003c4c180017fd5005fe54017f55005fc54017fd4c05fe53017f54c05fc53007fd0c01fe43007f50c01fc43017fd4805fe52017f54805fc52007fd0801fe42007f50801fc42007fcc801fe32007f4c801fc32017fd4403fe51017f54403fc51007fd0403fe41007f50403fc41007fcc403fe31007f4c403fc31007fc8403fe21007f48403fc21017fd4005fe50005f94005fd50017f140057c50007fd0001fe40007f50001fc40007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc2000ffc4001fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x804000ff4c020037f86010027ff2008001f79004006ff88020007f44010003fd2008001f69004000fe48020047fe201001bfc100800dffb2c2007bfd961003ffccb0800afe658400ffeb2c2007bf59610037f8cb0800afc658400dffb242000bfd9210007fcc908016fe6484001feb242000bf59210037f8c908016fc648400fffaa42007ff9521003ffaa90801ffc548400dffb1c2000bfd8e10007fcc708012fe6384001feb1c2000bf58e10037f8c708012fc638400fffa9c2007ff94e1003ffaa70801ffc5384001ffa1c2000ff90e10007fa8708003fc438400dffb142000bfd8a10007fcc508002fe6284001feb142000bf58a10037f8c508002fc628400fffa942007ff94a1003ffaa50801ffc5284001ffa142000ff90a10007fa8508003fc4284001ff9942000ff8ca10007fa6508003fc32840037eb0c2001ffd461000ffca308007fd5184003fe28c2001ffd061000ffc8308007fd4184003fe20c2001ffcc61000ffc6308007fd3184003fe18c2001ffc861000ffc4308007fd2184003fe10c2001bf9821003ffea10801bfe508400dbf2842007ff54210037f8a10801b7c5084001ffa042006ff90210007fa810801bfc4084001ff9842006ff8c210007f46108003fd3084001fc9842006ff0c210007fe410801bfe2084001fd1042000ff48210007f2410801bfc2084003ff8842001fdc421000ff6210801bfc1084003fc0842003ffd951001dfeca880037f65440013fb2a2003ff99510015fcca8800ffd65440077eb2a2003ff19510015f8ca8800f7c65440053e32a2000ffd9110005fec888003fe644400b7f3222000ff59110005fac888003fc644400b7e3222003ffd511001ffca88800ffd5444007fe2a22000ffd8d10005fec688003fe63440097f31a2000ff58d10005fac688003fc63440097e31a2003ffd4d1001ffca68800ffd5344007fe29a2000ffd0d10007fc8688003fd4344001fe21a2000ffd8910005fec488003fe62440017f3122000ff58910005fac488003fc62440017e3122003ffd491001ffca48800ffd5244007fe2922000ffd0910007fc8488003fd4244001fe2122000ffcc910007fc6488003fd3244001fe1922001bfd851000ffea288007fe5144003fb28a2001ff5451001feaa288007fc5144003ffa0a2001ff9051000ffa8288007fc4144003ff98a2001ff8c51000ffa6288007fc3144003ff90a2001ff8851000ffa4288007fc21440037fb022003ffd411001ffca0880037e5044007fea822003ff1411001ef8a088003ff4044001ff2022000ff50110007f88088003ff3044001ff1822000fe8c110007fa6088003f93044001fe1822000ffc8110007fc4088003fa2044001fe9022000fe48110007f84088007ff1044003fd8822001ff84110007ec2088007fc1044003fa0822001fe04110
  | 1 => 0xfff518801fff28c400bff5462007ff8a310003ff418801fff20c4000ff5062007ff88310003ff318801fff18c4000ff4c62007ff86310003ff218801fff10c4000ff4862007ff8431002afe6088017ffa844006ff94220036fca11002ffd508800dfe2844006df14220007fe811001bfe4088001fea044006ff10220007fe611001bfe3088001fe9844006ff0c220007fe4110003ef2088001fd904400fffc4220037f8211003bff654801d7fb2a4000dfd9520004feca9003bfe65480057f32a400eff59520075faca9003bfc65480057e32a400edf19520014f8ca90003ff64480017fb224000efd91200057ec890003fe644800b7f3224000ff59120005fac890003fc644800b7e3224000ef1912000578c89003bff544801dff2a2400eff55120077f8a890003ff63480017fb1a4000ff98d20025fcc690003fd63480017eb1a4000ff18d20025f8c69003bff534801dff29a400eff54d20077f8a690003ff4348001ff21a4000ff50d20007f8869003bff524801dff292400efb94920077faa49003bed524801dfe2924000ffd0920007fc8490003fd4248001fe2124000ffcc920007fc6490003fd3248001fe1924000ffd8520005fec290037fe61480037f30a4000ff5852006ff8c290006fc614801dffa8a400dff94520077faa290037fc5148001ffa0a400dff90520007fa8290037fc4148001ff98a400dff8c520007fa6290037fc3148001ff90a400dff88520007fa4290037fc214801dffa82400eff94120006fca09003bfd504801dfe282400edf14120007fe8090003fe4048001fea024000ff10120007fe6090003fe3048001fe9824000ff0c120007fe4090003fb2048001ff1024000fb8812006ffe2090037fc104800dffb28400abfd9420057fcca1000afe6508015feb28400abf59420037f8ca1000afc650800dffb204000bfd9020007fcc810016fe6408001feb204000bf59020037f8c810016fc6408015ffaa0400aff95020057faa81002bfc540800dffb184000bfd8c20007fcc610012fe6308001feb184000bf58c20037f8c610012fc6308015ffa98400aff94c20057faa61002bfc5308001ffa184000ff90c20007fa8610003fc43080197f310400affd482004ffca41002bfd5208013fe2904000ffd082004ffc8410003fd4208013fe2104000ffcc82004ffc6410003fd3208013fe1904006ffd8420047fcc210006fe6108001feb084000bf58420037f8c210006fc6108015ffa884008ff94420057faa210023fc5108001ffa084008ff90420007fa8210023fc4108001ff9884008ff8c420007fa6210023fc3108013ff9084008ff88420007fa4210027fc21080177f300400affd4020037fca01001b7e5008015fea804006ff14020036f8a010003ff400800dff2004000ff50020037f88010003ff300800dff1
  | 2 => 0x30097faa81804bfc540c0097f3186004ffd4c30027fca618013fd530c009fe2986004ffd0c30027fc8618013fd430c009fe2186006ffd8830027fcc418002fe620c009feb106000bf58830037f8c41804bff520c025ff2906012ff54830097f8a418003ff420c001ff2106000ff50830007f88418013ff320c009ff1906004ff4c830027f8641801bff610c009ff3086001bf98430027fac218002fd610c00dfe3086001bf18430097fea218047fe510c025fea886011ff14430007fe8218047fe410c001fea086011ff10430027fe6218013fe310c009fe9886004ff0c430007fe4218047fe210c001fe9086011ff0843009dfcc01804bff500c00dff2806006df94030097faa01801bfc500c00dbe2806000ffd0030037fc8018003fd400c00dfe2006004ffcc030027be601801bfe300c009fd1806004ff4c030007ba6018013f9300c023ff8806006ff0403004ffecb90032ff65c8019ff32e4002bf99720066fccb9000a7e65c8019feb2e400cbf59720006facb900027d65c8013fe32e4002bf1972004ffec990002ff64c8001ff3264005bf99320007fac990002fd64c8013fe3264005bf19320067fea990033fe54c8019feaa6400cff1532004ffec790002ff63c8001ff31e4004bf98f20007fac790002fd63c8013fe31e4004bf18f20067fea790033fe53c8019fea9e400cff14f20007fe8790003fe43c8001fea1e4000ff10f20067fea590027fe52c8019f7296400cff54b20067daa590027fc52c8001ffa164009ff90b20007fa8590027fc42c8001ff9964009ff8cb20007fa6590027fc32c8013ffb0e4010ff9872000dfcc390003fd61c80017eb0e4009ff1872000df8c390033ff51c8021ff28e400cff54720087f8a390003ff41c8021ff20e4000ff50720087f88390003ff31c8021ff18e4000ff4c720087f86390027ff21c8021ff10e4000ff4872004ff84390033ff50c8019ff2864000df94320067faa190033fc50c8019be2864000ffd0320007fc8190003fd40c8001fe2064000ffcc320007fc6190003fd30c8001fe1864010ffc4320087f8219001bff65880177fb2c400bff99620015fccb1002ffd65880177eb2c4006ff19620015f8cb1001bff64880017fb244000ff9922002dfcc910003fd64880017eb244006ff1922002df8c91002fff5488017ff2a4400bff5522005ff8a91001bff63880017fb1c4000ff98e20025fcc710003fd63880017eb1c4006ff18e20025f8c71002fff5388017ff29c400bff54e2005ff8a710003ff4388001ff21c4000ff50e20007f8871003afd6288017ffa94400bff94a2005ffaa51002ffc5288001ffa144000ff90a20007fa8510003fc4288001ff9944000ff8ca20007fa6510003fc328800dffb0c400fff9862000dfcc310003fd61880017eb0c4006ff1862000df8c31002
  | 3 => 0xe18e6000ffc87300bffc4398003fd21cc02ffe10e6018ffd43300c7fca1980037e50cc031fea866018ff143300c6f8a198003ff40cc001ff2066000ff50330007f8819805fff10cc02ffe0866006ffd963009dfecb1804ffe658c0057f32c6013ff5963009dfacb1801bfc658c0057e32c6006ffd9230005fec918003fe648c00b7f3246000ff59230005fac91801bfc648c00b7e3246013ffd523009ffca91804ffd548c027fe2a46015bf58e3009ffea718013fe538c027fea9c6004ff14e30007fe8718013fe438c001fea1c6004ff10e30037fec518003fe628c0017f3146000ff58a30005fac51801bfc628c027ffa946013ff94a3009ffaa51804ffc528c001ffa146000ff90a30007fa8518003fc428c009ff9946000ff8ca30007fa6518013fc328c00dffb0c6016ff9863000dfcc318003fd618c0017eb0c6006ff1863000df8c31804fff518c02dff28c6013ff546300b7f8a318003ff418c02dff20c6000ff506300b7f88318013ff318c02dff18c6000ff4c630027f86318003ff218c02dff10c6000ff486300b7f84318012fe608c027ffa846006ff94230036fca11804ffd508c00dfe2846006df14230007fe811801bfe408c001fea046006ff10230027fe6118003df308c009fd9846016ffc4230037f82118057ff654c02b7fb2a6000dfd9530004feca98057fe654c0057f32a6015ff595300adfaca98057fc654c0057e32a6015df19530014f8ca98003ff644c0017fb226000efd91300057ec898003fe644c00b7f3226000ff59130005fac898003fc644c00b7e3226000ef1913000578c898057ff544c02bff2a26015ff551300aff8a898057ff534c009ff29a6015f794d300affaa698057dd534c009fe29a6000ffd0d30027fc8698003de434c001fea1a6000f750d30027f88698003ff624c0017fb126000ff98930007fac498003fc624c0017e3126015ffd49300affca498057fd524c02bfe2926000ffd0930007fc8498003fd424c001fe2126004ffcc930007fc6498003fd324c009fe1926000ffd8530005fec298053fe614c0037f30a6000ff585300a7f8c298006fc614c02bffa8a6014ff945300affaa298053fc514c001ffa0a6014ff90530007fa8298053fc414c009ff98a6014ff8c530007fa6298013fc314c001ff90a6014ff88530007fa4298053fc214c02bffa826015ff94130006fca098057fd504c02bfe2826015df14130007fe8098003fe404c001fea026000ff10130027fe6098013fb304c001ff1826000f78c1300a7fe2098053fc104c00dffb286004bfd9430027fcca1800afe650c009feb286012bf59430037f8ca18012fc650c00dffb206004bfd9030027fcc818016fe640c009df3206000af99030027fac818002fd640c009deb206000af59030037f8c818012fc640c025ffaa06012ff950
  | 4 => 0x3bd435000bfe21a8000ffd8940005fec4a0003fe6250001feb128000ff18940005f8c4a0077ff525003bff292801dff549400eff8a4a0017ff4250001ff2128000ff5094002ff884a0003ff3250001ff1928000ff4c940007f864a0003ff61500017fb0a801cff9854000dfcc2a0003fd6150039fe30a8001bf185400effea2a0073fe515003bfea8a801cff1454002ffe82a0073fe4150001fea0a8005ff10540007fe62a0073fe3150001fe98a801cff0c540007fe42a0073fe2150001fe90a801cff085400effea0a0077fe5050001bf282801dff541400eff8a0a00777c505000bffa028005fed0140007fc80a0003be4050039ff882801cff04140037feca20016ff651000bff3288002bf9944002ffaca2006afd651000dfe3288005bf1944002dfcc820017ff541000bff2a08005ff5504002ff8a82001bff631000bff3188004bf98c4002fbcc620002de631000bfeb188000bf58c4002fbac620002dd631000dfe318801affd4c400d7fca62006bfd5310035fe2988005ffd0c4002ffc8620003be431000bfea188005ff10c4002f78862001bff621000bff3108000bf9884002ffac420002fd621000dfe310801affd48400d7fca42006bfd5210035fe2908005ffd084002ffc8420003be421000bfea108005ff1084002f788420003ff3210001ff1908000ff4c840007f8642001bff611000bff3088001bf9844002ffac220002fd611000dfe3088001bf184400d7fea220067fe5110035fea888019ff1444002ffe8220017bf411000bff2088005ff504400077a8220017fc4110001ff9888019ff8c440007fa6220067fc3110001ff9088019ff88440007fa4220067fc21100377f300801affd4040037fca02001b7e5010035fea808006ff14040036f8a020017ff401000bdfa008006ff9004002ff48020017fd4010001dea008005fe500400cffe202001bfc1010009ffb2e6004bfd9730027fccb9800afe65cc009bf32e60029f99730027facb98062fd65cc009beb2e60009f59730027f8cb98012fc65cc009ffb266004bfd9330027fcc998016fe64cc009feb266000bf59330027f8c998012fc64cc031ffaa66018ff953300c7faa998063fc54cc009ffa9e6004ff94f30027bca798013fd53cc031eea9e6004ff14f30027fe8798013fe43cc009ef21e6004ff50f30007ba8798013fc43cc009ffb166004ff98b30005fcc598013fd62cc0017eb166004ff18b300c7fea598063fe52cc031fea966018ff14b30007fe8598003fe42cc001fea166000ff10b30027fe6598013fe32cc009fe9966004ff0cb30027fec398013fe61cc0037f30e6004ff58730005fac398013fc61cc0037e30e6018ffd47300bffca398063fd51cc02ffe28e6000ffd07300bffc8398003fd41cc02ffe20e6004ffcc730027fc6398013fd31cc009f
  | 5 => 0x865010efcc3280037d619400dbe30ca000dfd065010efc83280037d4194043be20ca000dfcc65010efc63280037d3194043be18ca000dfc865010efc43280037d2194043be10ca006df98250014fcc12800b7a6094043bf884a006df0425002ffecba0016ff65d000bff32e8002bf9974002efccba000a7e65d000bfeb2e8020bf5974002efacba00027d65d000bfe32e8005bf1974002ffea9a0017fe54d000bdf2a68005ff553401077aa9a0017fc54d000bffb1e8005ff98f40025fcc7a0017fd63d00017eb1e8005ff18f40107fea7a0083fe53d0041fea9e8020ff14f4002ffe87a0017bf43d000bff21e8005ff50f400077a87a0017fc43d000bffb168005ff98b40005fcc5a0017fd62d00017eb168005ff18b40107fea5a0083fe52d0041fea968020ff14b4002ffe85a0017fe42d000bfea168005ff10b40007fe65a0003fe32d0001fe9968000ff0cb4002ffec3a0017fe61d00037f30e8005ff58740005fac3a0017fc61d00037e30e8020ffd47400fffca3a0083fd51d003ffe28e8005ffd074002ffc83a0017fd41d000bfe20e8000ffcc7400fffc63a0003fd31d003ffe18e8000ffc87400fffc43a0003fd21d003ffe10e8020ffd4340107fca1a00037e50d0041fea868020ff14340106f8a1a007fff10d003ffe0868006ffd96400ddfecb2006ffe65900057f32c801bff596400ddfacb2001bfc65900057e32c801dbf592400dffea920017fe5490037feaa48005ff15240037fec720003fe63900097f31c8000ff58e40005fac72001bfc6390037ffa9c801bff94e400dffaa72006ffc539000bffa1c8000ff90e400077c8720003fd439000bfe21c8000ef10e40037fec520003fe62900017f3148000ff58a40005fac52001bfc6290037ffa94801bff94a400dffaa52006ffc529000bffa148000ff90a400077c8520003fd429000bfe2148000ef10a40007fe6520003fe3290001fe9948000ff0ca40037fec32007bfe61900037f30c8000ff58640005fac32001bfc61900037e30c801bffd46400f7fca32006ffd519003dfe28c8005ffd06400077e832007bfe4190001fea0c8000ef5064002ff88320003ff319003dff18c8000ff4c6400f7f86320003ff219003dff10c8000ff486400f7f84320016fe6090037ffa848006ff94240036fca12006ffd509000dfe2848006df1424002ffe8120003bf409000bfda04801effc4240037f82120077ff655003b7fb2a8000dfd9540004fecaa0077fe65500057f32a801dff595400edfacaa0077fc65500057e32a801ddf19540014f8caa0077ff545000bff2a2801def951400effaa8a0077bd545000bfe2a28000ffd8d40005fec6a0003fe6350001feb1a8000ff18d40025f8c6a0077ff535003bff29a801dff54d400eff8a6a0017ff4350001dfa1a8000ff90d40007fa86a0
  | 6 => 0x3fe20a6201ffcc531027ee6298807fe314c403ef18a6201ff0c53100fb86298807f4314c403ff10a6201ff08531007fec098802ff604c401ff3026200ff58131007f8c098802fc604c449ffa826224ff94131127faa098893fc504c449be2826201ffc413100ff82098827ff65c84477fb2e4223ff99721015fccb9088ffd65c84477eb2e4209ff19721015f8cb90827ff64c84017fb264200ff9932102dfcc990803fd64c84017eb264209ff1932102df8c99088fff54c8447ff2a64223ff5532111ff8a990827ff63c84017fb1e4200ff98f21025fcc790803fd63c84017eb1e4209ff18f21025f8c79088fff53c8447ff29e4223ff54f2111ff8a790803ff43c8401ff21e4200ff50f21007f88790806fe62c8447ffa964209ff94b2111ffaa590827fc52c8401ffa164209ff90b21007fa8590827fc42c8401ff9964209ff8cb21007dc6590803fd32c8401f69964209ff0cb2100dfac390807ff51c8403ff28e4201ff5472100ff8a390807ff41c8403ff20e4201ff5072100ff88390807ff31c8403ff18e4201ff4c72100ff86390807fe21c8403f710e4201fd8872100ff84390807ec21c8413ffb064200ff98321005fcc190803fd60c84017eb064209ff1832111ffea19088ffe50c8447fea864223ff1432111ef8a190807ff10c8403fe0864222ffd9521115feca9088bfe65484057f32a4222ff59521115faca9088bfc65484057e32a4200ffd9121005fec890803bf64484015fb224200ff9912102dfcc890803fd64484017eb224200ff1912102df8c890803bc64484015e3224222ffd5121117fca89088bfd5448445fe2a24200ffd8d21005fec690803df63484016fb1a4200ff98d21025fcc690803fd63484017eb1a4200ff18d21025f8c690803dc63484016e31a4222ffd4d21117fca69088bfd5348445fe29a4200ffd0d21007fc8690803fd4348401fe21a4201bfd8921117fea49088bfe5248445fea924222ff14921007fe8490803fe4248401fea124200ff10921007fe6490803fe3248401f71924200ff4c921007da6490803fc32484037fb0a4201ffd452100ffca290807fd5148403fe28a4201ffd052100ffc8290807fd4148403fe20a4201ffcc52100ffc6290807fd3148403fe18a4201ffc8521007ee4290807fe2148403f710a4201ff0852100fd84290807f42148401ffb024200bfd8121007fcc090803fd6048401fe3024200bf18121117fea09088bfe5048445fea824222ff14121116f8a090807ff1048403fe0824206dfd9250006fcc9280037d649400dbe324a006dfd8e50006fcc7280037d639400dbe31ca000dfd0e50006fc87280037d4394001be21ca006dfd8a50006fcc5280037d629400dbe314a000dfd0a50006fc85280037d4294001be214a000dfcca50006fc65280037d3294001be194a006dfd
  | 7 => 0xa089ffe50d044ffea868227ff1434113ef8a1a0807ff10d0403fe0868226ffd9541135fecaa089bfe65504057f32a8226ff59541135facaa089bfc65504057e32a8201bfd9141137fea8a0817fe545044ddf2a28226ff551411377aa8a0817fc5450401ffb1a8200bfd8d41007fcc6a0803fd6350401fe31a8204bf18d41137fea6a089bfe535044dfea9a8226ff14d4102ffe86a0803bf4350401ff21a8200ff50d410077a86a0817fc4350401ffb128200bfd8941007fcc4a0803fd6250401fe3128200bf18941137fea4a089bfe525044dfea928226ff1494102ffe84a0803bf4250401ff2128200ff509410077a84a0817fc4250401ff9928200ff8c941007fa64a0803fc32504037fb0a8201ffd454100ffca2a0807fd5150403fe28a8201ffd054102fee82a0807fe4150403df20a8201ff1054100f7882a0807f44150403ff18a8201ff0c54100ffc42a0807fc2150401ffb028200bfd8141007fcc0a0803fd6050401fe3028200bf18141137fea0a089bfe505044dfea828226ff14141136f8a0a0807ff1050403fe0828204ffd9731025fecb98813fe65cc4057f32e6204ff5973112dfacb98813fc65cc4097e32e6204ffd9331025fec998813fe64cc40b7f3266204ff59331005fac998813fc64cc4097e3266225ffd533112ffca998897fd54cc44bfe2a66201bf98f31027fea798813fe53cc409fea9e6204ff14f31027fe8798813fe43cc409fea1e6204ff10f31027fec598813fe62cc4017f3166204ff58b31005fac598813fc62cc44bffa966225ff94b3112ffaa598897fc52cc401ffa166200ff90b31007fa8598803fc42cc409ff9966204f7ccb31027fc6598813fd32cc401ee9966204ff0cb3100dfac398807ff51cc403ff28e6201ff5473100ff8a398807ff41cc403ff20e6201ff5073100ff88398807fe31cc403ef18e6201fd8c73100ff86398807dc31cc403ff10e6201ff08731027fec198813fe60cc4017f3066204ff58331005fac198813fc60cc44bffa866225ff9433112ffaa198897fc50cc44bbe2866201ffc433100ff82198893ff654c4497fb2a6224ff99531015fcca98893fd654c4497eb2a6224ff19531015f8ca98803ff644c4017fb226200ff9913102dfcc898803fd644c4017eb226200ff1913102df8c898893ff544c449ff2a26224ff55131127f8a898806ff634c449ffa9a6204ff94d31127faa698813fc534c401ffa1a6204ff90d31007fa8698813fc434c401ffb126200bfd8931007fcc498803fd624c401fe3126200bf18931127fea498893fe524c449fea926224ff14931007fe8498803fe424c401fea126200ff10931027fe6498803df324c401ff1926200ff4c931007ba6498813fc324c4037fb0a6201ffd453100ffca298807fd514c403fe28a6201ffd053100ffc8298807fd414c40
  | 8 => 0xfd9532167fcca9900afe654c859feb2a642cbf59532167f8ca9900afc654c801ffb226400bfd9132007fcc899016fe644c801feb226400bf59132007f8c899016fc644c859ffaa2642cff95132167faa8990b3fc544c859ffa9a6404ff94d32167faa699013fc534c801ffa1a6404ff90d32007fa8699013fc434c859ffa92642cff94932167faa4990b3fc524c801ffa126400ff90932007fa8499003fc424c809ff9926404fbcc932007fc6499003de324c801ffb0a6400bfd853215ffcc299006fe614c801feb0a642bff1853200df8c2990b3ff514c857ff28a642cff5453215ff8a2990affe414c857fe20a642bff8c532027f862990affe214c857fe10a6400ffd8132005fec099003fe604c801feb026400ff18132005f8c0990b3ff504c859ff282642cff54132167f8a0990b37c504c857ff882642bff0413204ffeca19012ff650c809ff3286402bf99432026fcca1900a7e650c809feb286429bf59432026faca190027d650c813fe3286404bf1943204ffec819012ff640c809ff3206405bf99032027fac819002fd640c813fe3206404bf1903214ffea8190a7fe540c853feaa06429ff15032025fcc619013ff530c809ff2986404ff54c32027f8a619013ff430c809ff2186404ff50c32027f886190aafe620c853ffa906409ff9483214ffaa419027fc520c801ffa106409ff90832007fa8419027fc420c809ff9906404f7cc83204ffc6419013ee320c809fe9906400f74c832027da6419027ff610c809ff3086401bf98432027fac219002fd610c813fe3086401bf1843214ffea2190a3fe510c853fea886428ff14432147fc82190a3fc410c809ff1886428f78c432027f86219013dc310c851ff1086409ff0843204ffec019013fe600c8017f3006404ff58032005fac019027fc600c853ffa806429ff9403214ffaa0190a7fc500c853be2806428ffc4032147f82019017ff65d040b7fb2e8205ff99741015fccba0817fd65d044f7eb2e8205ff1974102df8cba0806fe64d040bffaa68205ff9534102f7ca9a0817fd54d044fdeaa68205ff1534102ffec7a0817fe63d04097f31e8205ff58f41005fac7a0817fc63d044fffa9e8227ff94f4113ffaa7a089ffc53d040bffa1e8205efd0f4102ffc87a0817fd43d0401dea1e8205ff10f4102ffec5a0817fe62d04017f3168205ff58b41005fac5a0817fc62d044fffa968227ff94b4113ffaa5a089ffc52d040bffa168205efd0b4102ffc85a0817fd42d0401dea168205ff10b41007fe65a0803fe32d0401fe9968200ff0cb4100dfac3a0807ff51d0403ff28e8201ff5474100ff8a3a0807fe41d0403df20e8201fd9074100ff883a0807bc41d0403ff18e8201ff0c74100ffc43a0807fc21d040bffb068205ff98341005fcc1a0817fd60d04017eb068205ff1834113ffea1
  | 9 => 0x80bff3288402bf9944202efcca2100a7e651080bfeb288431bf5944202efaca210027d6510813fe3288405bf1944202dfcc821017ff541080bff2a08405ef9504202ffaa8210c7bd541080bfe2a08409ffd8c4202ffcc621012fe631080bfeb188400bf58c4204ff8c6210c7ff5310863ff2988431ff54c4218ff8a621017ff431080bdfa188405ff90c4202ffa8621003bd431080bfe2188432bf9884218ffea421027fe5210863fea908409ff1484202ffe8421017bf4210813ff2108405fb9084202ffa8421003bd421080bf6a108409ffd844202ffcc221006fe611080bfeb088400bf5844204ff8c221006fc6110863ffa888430ff9444218ffaa2210c3fc511080bff2088430ef9044202ff88221017bc4110861ff1888430ff0c442187fc4221027fc2110813ffb008405ff98042005fcc021017fd60108017eb008409ff1804218ffea0210c7fe5010863fea808431ff1404218ef8a0210c3ff1010861fe0808404ffd9732025fecb99013fe65cc8057f32e6404ff5973217dfacb99013fc65cc8097e32e6404ffd9332025fec999013fe64cc80b7f3266404ef993320057cc999013fd64cc8017eb266404ef593320057ac999013fc64cc8097e326642fffd533217ffca9990bffd54cc85ffe2a66404ffd4f32027fca799013fd53cc809fe29e6404ffd0f32027fc8799013fd43cc809fe21e642fffd4b3217ffca5990bffd52cc85ffe2966400ffd0b32007fc8599003fd42cc801fe2166404ffd8732027fcc399006fe61cc809feb0e6400bf58732027f8c399006fc61cc85fffa8e642eff9473217ffaa3990bbfc51cc85dff20e642eff10732027fc6399013fc31cc85dff10e642eff08732027fec199013fe60cc8017f3066404ff58332005fac199013fc60cc85fffa86642fff9433217ffaa1990bffc50cc85fbe286642effc4332177f82199027ff658c8557fb2c642aff99632015fccb190abfd658c8557eb2c6409ff19632015f8cb19027ff648c8017fb246400ff9923202dfcc919003fd648c8017eb246409ff1923202df8c9190abff548c855ff2a4642aff55232157f8a9190b2fd638c855ffa9c6404ff94e32157faa719013fc538c801ffa1c6404ff90e32007fa8719013fc438c8097f314642affd4a3204ffca5190abfd528c813fe2946400ffd0a3204ffc8519003fd428c813fe2146404ffcca32007be6519013ef328c813ffb0c642dff9863200dfcc319003fd618c8017eb0c6409ff1863200df8c3190abff518c85bff28c642aff5463216ff8a3190b7fe418c85bfe20c642dff8c63216fbc6319013fc318c85bee18c642dff8863204ff84319027ff608c801ff3046400bf98232007fac119002fd608c813fe304642affd4232157fca1190abfd508c855fe284642adf1423216ffe21190b7fc108c859ffb2a642cb
  | 10 => 0xc221806fc6110c73ffa888638ff944431cffaa2218e3fc5110c0bff2088605ff10443027fc6221813fc3110c71ff1088638ff08443027fec021813fe6010c017f3008604ff58043005fac021813fc6010c73ffa808639ff940431cffaa0218e7fc5010c73be2808638ffc40431c7f82021817ff65d080b7fb2e8405ff99742015fccba1017fd65d086f7eb2e8405ff1974202df8cba1017ff54d080bff2a68405ff5534202ff8a9a1017ff63d080bff31e8404bf98f4202ffac7a1002fd63d080bfe31e8437ffd4f421bffca7a10dffd53d086ffe29e8405ffd0f4202ffc87a1017fd43d080bfe21e8437ffd4b421bffca5a10dffd52d086ffe2968405ffd874202ffcc3a1006fe61d080bfeb0e8400bf5874202ff8c3a1006fc61d086fffa8e8436ff947421bffaa3a10dbfc51d080bff20e8405ff107421b7fc63a10dbfc31d086dff10e8436ff0874202ffec1a1017fe60d08017f3068405ff58342005fac1a1017fc60d086fffa868437ff943421bffaa1a10dffc50d086fbe2868436ffc43421b7f821a1027ff65908657fb2c8432ff99642015fccb210cbfd65908657eb2c8409ff19642015f8cb210d2fd6490865ffaa48405ff952421977ca9210cbfd5490865deaa48405ff1524204ffec721003fe63908097f31c8400ff58e42005fac721027fc6390865ffa9c8432ff94e42197faa7210cbfc539080bffa1c8400efd0e42007fc8721003fd4390801dea1c8405ff10e4202dfcc5210cbff5290813ff2948432ff54a4204ff8a521017ff4290801dfa148405fbd0a4204ffec3210d7fe61908037f30c8400ff58642005fac321027fc61908037e30c8432ffd46421affca3210cbfd519086bfe28c8435ff906421af7c8321017fc419086bde20c8435ff8c6421aff863210d7fe2190813fe10c8409ffd8242007fcc121002fe6090801feb048400bf5824204ff8c1210cbff5090865ff2848432ff54242197f8a1210cb7c509086bff8848435ff042421a7fecaa10d2ff6550869ff32a8402bf995421a7facaa10d2fd6550869fe32a8402bf195421a7fea8a1017fe5450869feaa28405ff15142007fec6a1002ff6350801ff31a8400ff58d42007f8c6a1012fc6350869ffa9a8434ff94d421a7faa6a10d3fc535080bffa1a8400ff90d42007fa86a1017fc4350869ffa928434ff949421a7faa4a10d3fc525080bffa128405fbd0942007fc84a1003be4250801ffb0a8400bfd854219ffcc2a1006fe6150801feb0a8433ff1854200df8c2a10d3ff5150867ff28a8434ff5454219ff8a2a10cffe415080bfe20a8433ff8c54219ff862a10cffe2150867fe10a8400ffd8142005fec0a1003fe6050801feb028400ff18142005f8c0a10d3ff5050869ff2828434ff541421a7f8a0a10d37c5050867ff8828433ff0414204ffeca21016ff6510
  | 11 => 0x5ffd974302dfecba1817fe65d0c057f32e8605ff597431fdfacba1817fc65d0c0b7e32e8605ffd534302ffca9a1817fd54d0c0bfe2a6863fffd4f43027fca7a18fffd53d0c09fe29e8605ffd8b4302ffcc5a1802fe62d0c0bfeb168600bf58b4302ff8c5a18ffff52d0c7fff296863fff54b431fff8a5a1817ff61d0c0bff30e8601bf9874302ffac3a1802fd61d0c0bfe30e8601bf187431fffea3a18fbfe51d0c7ffea8e863eff1474302ffc83a1817fc41d0c7dff18e8604ff0c7431f7fc43a18fbfc21d0c0bffb068605ff98343005fcc1a1817fd60d0c017eb068605ff183431fffea1a18fffe50d0c7ffea86863fff143431fef8a1a18fbff10d0c7dfe0868604ffd9643025fecb21813fe6590c057f32c8604ff596431edfacb21813fc6590c097e32c863bbf592431effea921817fe5490c7bdf2a4863dff552431ef7aa921817fc5490c097f31c8604ffd4e43027fca721813fd5390c09fe29c8604ffd0e430277e8721817df4390c09ffb148604ff98a43005fcc521813fd6290c017eb148604ff18a431effea5218f7fe5290c7bfea94863dff14a43027fec321813fe6190c037f30c8604ff58643005fac321813fc6190c037e30c863dffd46431e7fca3218f7fd5190c79fe28c863cff9064302ff88321813fe3190c09fe18c863cff886431e7f84321813ff6090c09ff3048600bf98243027fac121802fd6090c09fe304863dffd42431effca1218f7fd5090c7bfe284863ddf142431e7fe21218f3fc1090c77ffb2a863bbfd95431dffccaa180afe6550c77feb2a863bbf595431dff8caa180afc6550c77ffaa28605ff951431dffaa8a1817fc5450c77ffa9a8604ff94d431dffaa6a1813fc5350c0bffa1a8605f7d0d43027fc86a1813be4350c01ffb128600bfd8943007fcc4a1803fd6250c01fe3128600bf189431dffea4a18effe5250c77fea92863bff14943007fec2a1802ff6150c75ff30a8601bf98543007fac2a18ebfc6150c037e30a863bffd45431d7fca2a18effd5150c75fe28a863aff9054302ff882a18ebfe3150c09fe18a863aff885431d7f842a1803ff6050c017fb028600ff98143007fac0a1803fc6050c017e302863bffd41431dffca0a18effd5050c77fe282863bdf141431d7fe20a18ebfc1050c09ffb288604bfd9443027fcca2180afe6510c09feb288639bf59443027f8ca21812fc6510c0b7f3208605ffd504302ffca821817be5410c0bfeaa08639ef5504302ff8a821812fe6310c09ffa988604ff94c43027faa621813fc5310c09ffa188604efd0c43027fc8621813de4310c09fea188604ef50c4302fba8621813ff6210c09ff3108600bf98843027fac421802fd6210c09fe3108639ffd48431cffca4218e7fd5210c73fe2908604ffd8443027fcc221806fe6110c09feb088600bf58443027f8
  | 12 => 0x400000001c00e00000600000600000000c00a02800201c00c00000003c00201400c00201000200600400600400800000200201200c01400003a01e04400001e00200000400a00000001802a00001201a00000201a00601000400000801400601c00000401600000400000200600400000800a00200000200c00200005200600a00000e00401e00600200000000a00200400201000400000400201a00202800000000600200600000000200800400201a00e02e00200600000200200000600c00000400601600001c00000e00a01402400200600000c00600200201200000602800800a00800a01800001200600000e00800004a00200000a01202800001400000001800000c00c00000601000601a00000400600000000000000401c02c00e00200c00002001202e01400400600200000000200a00600801200000000002a00002000200200e00000000800401800800200000600400000e00c00000000001c00400800800e01000200000400400000000000002e06c00000000004a00201806802200000000001c00000200000a00202400200e01200000a00201c00000400002200800402200400c00202000000400400c00000400000000000000600000000000e00401200201000000e01600000200200400a00c00001800000000002800600000a01002800002a01400000000200000200c00203400000000000c00001201000c00802600000000a00600400a00000000200c00c00a00000000000000400400000202e00202e00000400600400204200000000e00600201400000800200000801800000000000200600a00200600400000000400401402000202400001800000000201800000c00400c00002e01800e00c00000400203202000800400401400c01c01200800000000201402c00000000200402400400402800200402000a00000200001a00e04603c00602000002a01800601400200200200201c00000201202400000201000c00800000400c00800a00001001200600800401400400600402c00000000800802401400000000400400200000800002003a00c00200000002601401200000a00000000e00000c00a02a00402400c00000600001401200000000001c00600a00601c00e02401201800400000000000400400400e01200801c00000400800c00200400400200c00000000000000202c00000200000200400000000001600800000401a00000002000e00001400000000000000000800200a00400000200000000200002600000000401000000000000000000000400c0dc00000a00e00800000000000200c00000600200800201800404401600600000201800003200400600400c00c00200400400600000000e00401000400c01400401400800000800400a04200000200400000e00002a00400000600a0020
  | 13 => 0x7644368000592000000000046600000000008be00036400000001c60000000b9600000004dc1a60000000cb0000000000000001a06d51800005c09c722a02fc91a2792eb04c4f6c44050083b0f0c0000be800077e48c5039b7800023401115c0ff62260001188a2a0002a117754342524f28d8cef096c2aa0df44809ec40619209ee5010c00794df475a32a8df011849f035000094a424407a728d6c9790db06dc7a01543e107dc16e000000046c00000049b80002060000001cc80000000000d4c8ba00030da3ecaca39329a000000000028b03889c683f00018b8ac8000000000102c0000000000e900000000000e001cd2e28000f600003e380014ba6ad0000000fae466055999caee2cd3c410e07d27f60688b3c0002bc3560000000000000000078c32d262800143600027d1360c3c4d100000d00920c21cc0988ec29ee0000000a6e9180002044d7e8a83de8000000000475924000000000011f000029e1620000b307a12638b7800000010c80000003e33dca8a40000002c0a11486a00000000000008c90c8168117248500008f400000000000007008cf1b780dc0000004aa28e8000a1f178076400000000000000dc0003a6928cb2800000006e83c817c1419f100003440d420413b284827c000000000000000000003771c8800000000011c0000ad00002a7028450e0002da09500001fd3cc07e829218304886c4d609fe3bf0e545845784dd2064ffa1cb2329d2c15e01d2349ce0da200031792b000000000021ec60c69a39113907465750f700ac26055f281945c0000001d8896c6a475109680000005d034f0001114557000120cc7817a00000008a40000001d14ebe00000000004dc90700000001de00035289604366bd000039864411421b20482cc35604f03907a63751150128e0c6a133a22ed3a04ab00000003388ee2909ee000011a3061d8800000000017a0e32a1e10b06bd47843d1d78aa906a1ff466a5b8c542654268f208266040f40f5c00000e00e00000400600000001200400000802c00001a01001000e00203a00800600000000000c00800c01600401800000000200000000600000800400a00000000600e00000001001401e00a00a01000800000800800c00400001e0220120020000000a600800200003400205600002600e00200201203402600000200800000400000400000800000800402800000201e02200200003001600e03001200000800001a00a00400c00000c00400c00800e00000e00400000401a00c00c00600400001001000804400202201004000001800000000400000404600200000000800200600400401001600400002400400400600601001c00002a01002a00e01200600400c00000200600000400601e00800400000003802000400200000400a00400000602601e00001201400e00000002
  | 14 => 0x245c0c41e32271f4800084c25f000115400034411105981f822b000000020d3a82954fbe82002d90513c66ae2258fa929265041c9c094563a831c19a40000000f6137400019b33e0a500000004cd10054684dc319000020e1ed24780000002ee00005d04080c743105a400046f03f82f83c27f40000000c8a6004ea9a80104000000000000000000000000007a710d00009e698d2c797dc00037f3d8a340bdc51c0001018be620c09d17892203ef3c6a3d4cd83b014419440002483b700000001b94b312700005db2d58c78c826ba29c187d1586da14f9835350a140001a9ca523a14aba4c800062b2b3800068022529f16bc14c86c516826d3b868000001413620000001b1c3ce00200023600000000000000e940b0000000149c32f357800000000000006591be1e90348eb860a2f41a380e0d801130018000fa67e23e78210eee48b420000004c91d3bd80000005ce000262113a4b62700118d0c4cf00002e54b000000014d400000000011a000061c000217000088d00012f53366f90000b04cfa0000000000e242515259f709e27f2201271400000026100006b000000017a8000000060a464d0e00026b9b54a8226645e00000003a73b58d700000003ea0000a741d83278cd4be24823080000c2298300014b02f67c84f303c547a03508700003c084606f83a800000018080000000002de8000e3800009e80000000000a00dd000000000016388d66e84f986140000004da000126a7da2248f1519027d4bc1db412c9294938aac4866231e71dc035c3fc10fa9804b88a51ea9544cf090132a062c9aa6d8000221000002a14e000000055c00000003e422b0149b811bc000000000000000000000006a20000000000b8800000000000008140af295c00000018c000062a000000000000000000016f0000000410a1d000000001e01dc0004ba16800002da13645e800000078c1571eb10f2592000000145000000014b45b8000000050818094d000000000085f000000000000046b0e6547c9f54749e38000a0a000273058ca4000000000007d508aa8c4bf8337342a368c282e952811cc0007ec00000010f400047b1fe8000514000000012e464153800000000000000006ca94a42713ac2fc34a33fa6740005000002898664730250a22490e000261a02cc1415618d00005a64042571884a4e6eb00000013041bd38806a8c767ef067865c0365eb017a2005b24f91c7a50431c8601bc991800034200020b4e784a610c11c80005490000e700008b302e1c153800000000000392000277251c7cc6c40d99e051c61532b99ccc0000001aa0ee93d284b012074143a7182b0800000003a0001a54b1200032123752d257a230985493a79d134908943247e2e908dc000260180182061c70a52b1d745262ca4c91d1871825e29280000006bb4498000d50
  | 15 => 0x886334694fc21e96b428981c77c64750ba4380000004b50ac51609ed2fd84ec7fa6c20a825f09484fb14480002527e640d8b980d86df49e1f84da803233c93047e05fe4a89690cda13532d8f5948a99000000005f08052a80e4932a8d1414937d0309bb18b20346aa71e3f380004d00470a3800000056900008fc0000002970a88c6c0000e6041416c05a00c946000000000000012b400000005740000000308b48f381f1189a08c6520000a78000aec3e4000027ce3642718500000008364da80002f24e20ef00000000000cf1f0000000033502a8b2219a3b0239c16215848023b510a3ec00021980006be30d1c8c00005819000009760f600005a0000612000034000000000000001ea0002d324e000078a00000000000000000000000336000000139600022a8000c6e8f825c000000032848601cc2b40000001c500005b613f12e546a10c32fa5f888e1771ee256000040c0ee1bc87b68004110a44e769f032f0bcd44200037200b141e9dd4070ae0000a0e0668ad40000001040000a1800000000004000004c6000000022e000000000095c000013c3fc7801f70fd0fd067140312f01106353d511705c45c8140a84c00000003d91e0db20000000a7449e000000000083e0002c300009a88c100023dc000000000000000089b07e000141072a28ca76074c0fa16b00304ec88e51025646d640500000006d061300010c8000000065a5c85d600048f000030200000000001f21df02b894c1ce0000d200009323b5094000034200041e8000000000000091c57458d2a5858914c0000001e5800092b000193046210a21483c000002e1451a5c960a243699c747f47350bb05b85f86dd3b625d0cc43df4c08f2d1989701c49b5887e90f0380000e8800000000008f493000020cc86200020aa6bc00039e000000127a2f6149095c386a492b627f000007400000000003d400000000000000002458cde33b1b6a5eccb43f20e8a6280006ec4de1f286964bf00000003320000000000000a0617f880861a0003aa95ec0001a6052000000000000029700000db3cf1ac54061004e893245586b349503b8000334494153475203e0001d94fe04ef203a4085966343291f747f67373a121680f800036487880000002f017fcdae7f744f000049a96326c99c93520001469a644c8890135a19c4b200000013f048a00024700005f43d2000000000097a32b96200005b800000000002222c814900000000000000bb200000016a0b2e83e0000158bec3ab000000000021300000003ec53c0001dbc0000001bf1b98fd400052d000000093a0001d30db659f0dc1fb45340000000e5c00000000000005eaa110000000de60bd00000011860002760000000000010800000000008200012e68dc0fd8648b265660001d603260000891bbc00069d0001d24da02ce298
  | 16 => 0x40238e0808548d01a00001a23f21a24f865b005a1ce935a37b07b8b1c00008300011c518422d279057009000000000009000000da8000000000000000113e19f345a31508451b4418ce00009042100318f6a89100224d893064340d0f74cd04c018b947d2ee3724290000ac66fb4a292252fe000330000000093450c28cc0000080000e200000000d6000136600000000013883b43a383686f481c0001a7c0000000000b84d5407900000000000002839c34000000347a4fc0001c200000000001204a7158800000000017c800006b0da00000000002e4800137c00005684d03f256a3ff273515c77d33a975cb18000114082840644d509143524441123501780207c60001c4c0008a200028bd33c41d1989cad0e200007c09410bc9a33419ac800000000000000b25521dc80000007c503a88551c242a32000000000bb2a310647ec0003a7a6505047bc27a17304d80b81f08bec6bc6d2000047000000000021a4f4008713ba4f91022a014700013003de330961c00000000026f40000000a0852c46a0003781e151949eb0a19a4cffe24137f11042e26ea0f80b68f9800000010f800000002a000000081f3c9291d35850a4019f6c0004212659688b6a622171814825e3bd14580005d800000000007d60000001a700009f838f9c2c0006f5000000031a81300009fc000000000002400022f000000014432424f00000008681d5155800050800000004944b10000c6c0007a31a701e8000000000000138c0000000c6423e00041a12a871a0002ec22e80765c713780009d200000000000000003fc25550482700001f640000a91ed0e7c0004fd52fa8ec0221c741d279c5f23083e717b0000000040142c000060076a7683a45714740ab499a8c017f24ec3d668e37a0000fa27bb341043534241024b024caf835a4c8832400060100001f4000000000174c83c0000001d6c50c8e52dd2428b0800052180011f41c00331ae00000763131d992248022d9903800014500014bc0007e50bf96b4d963d1418800083050f0000000000000000189411464e402222c000000477800000000000000000000003b980000003e0000000000073e4298000314000049026800092c0000000b3c0003bb0a6c70c0003f587d05d03112fc9140ef40004479ef895e0423221f805c80ce41321f4c6642d1f28d880005041b015ac40a0000001c0d1b24de0001d4cbbc0002128c740004590001c68c1200048193842ca27321180000000003710984000000000000018a00000000000008381a1a558dda00009c80000000001a300000000d2000252c736000000000111803d4ed84b8000000000015402e21c47e903400026a40080500000000000a10e0e61800016581f62df0fe14c82105da2370a9027c7b443a83f470e18f3c39e401e485528723880001d719f10f0c5
  | 17 => 0x465fd000000000084900015b800062710721c11aa000000000000000026900000000000000000000000390981800000000027d877875739429509d000000000000c606f11383fc5601703531ad0a2679352f0000e1000013e1a48dec3fe000000000059a000000000015726d291134c71509598a12c092300020b80000b50000a3c0009f90000000000993000090920c00037e94ec0000d612f800000092600000280005a5033800042801c00000000009df00012a400044200021049cc9a522b800115e8150ba994c69a3120000000a8a6f8310030c70858300000002163332e68a8400000043216ec58600008c1dc82782f139685342d69870a30a645765d40dfa56c8d873d4dc80000604942888ae4000212000000000000000003644026ee06e92200009201f9a2c40000001d6911512e8ea4c599c007248424a8f00f4a98f47300005fa8a90001aac8f6603022003cf924b42ce8c1cf643264db11e41986e118fa8a84128b61b700010763a450a8890a863481bb17290e4314138983c00091b00014ac814385000205c0000000000db146e6a9000000000000002e80007040000d80000000000000069c00000039301c402a3b70ea9ea0abc000000069400000000000000002490000000b7e0004181488fdc000027022cafe00049095303788444898048ed2028065085cc2c0004d107d49da9ab47605c8a624673fc96f8d2260e00000000000002952574000736497881c0166ce4f913fc6c80001590c10b2a69822c0000c7429820ba6b800001f00000005d40fe1ca2500ba281d3c18000c7e2bd04e014c00023600000000001912490144a0a0e0000000124a031000168c23c0810952548000827404a6fc4e40e3345009d2ce986119000149a0000e0800000063e1a78000000000000000039c00000000000005533d98100a340000000000d1847d000000000000042c8000000a271e38e7514073f2078dc0d026494cf9e2c000a16217914400096d2848f093e81732140000fc60000001964eea98e47f0874000000305a1fd1e42dd43584093904e700006a4000460000000000022c08800010868870001b94b841dd43b16a84c675400000000001840001a400bea5b0001b0d21054f00000000008ff51280000000e52e792882662e52ce1998d361484a11eb87d02f74539e44dc66292dc979c23a67639c9bdd3ee4a815b08800ca70938b0d5d38285441423507fe9971c816c8cf42a52fa2680fac6b7090a6a901428c159992cc3a96432b24912de1951e48b206b63f716894d83942974848c252a006447c9418bde8560eda8b11563b305e24445aa19d18818b4bb86ca2a015d082c9cf2d61af096e15f529a1f08b49050208c84b0a2bf437125c27e48a1338da4c48a593af151d298a0234219dc5469a401b10484786942db9fcc4f44390c
  | 18 => 0x17d42a22803c785489664082ea83710a03811db045d37099843b8ce8988211000000037600044c22dc0005a92ac8e880000003c10a407e200051c0938f823f8000000083666e4c480007ea000527800056809938605a80000e100021e00002c515f09e00002e74250751164000000000000000000000000000002fc0d648da32a40401e014e0f421d837865657e0001070bcc47627b0234a3a000000231048c1be2b68000682000000229046076829c8f10f3660523f92b490c52300000001b03bb00002b12be6cd4d8000000075649890c000000041791181d677438700013bc4531b380000003d94be8dc4734378092997508e15500012440003033c200190645602e02840040865469065020212707986804aa1b20e797b435614451120f0c3298506a82e8b145333939560bc272f3e69ff13d435f5288d84af23cf26b08e4000664267000000009d3d49e540005020008000d8a0000c4a16c998a0d387a2552a67631f3a3d0e807af179000118e14c0b39a888866c632e0f613f60001a288180000b200000011c000028f000000003349980013ae0002cd800000091500000000007a4000000065c24c0000c7002c0004d900000005e500000003cc000000091096a0000000000000000000000136e0000000000b5c5551119068e4800000000008680a000023c02449d23d31b9d2c44331d2a5d864a8d7000129c67e0001a817042704c60000000ef200008b000008614a4440ec93c20002f4a28c3ac89600000008ea000000000000000005411291b600022da1740007a22640a1400000052080000000002c028c80000000000f34000000511a4711a67970001c0400000000000000009430000000f3e0000001fa4ed489206427f409a0005291b3c0002563e8000052a6dc1579cc4c0489a38b8c8c0009c22681c94ab6000396251800081e49680013d00003d6800020c0e91982810dd2000502a9191681f3059a15c0000000ed261112800045f8b000000004d384454160002e180000005262c10490ef800052118c041686f0b017e8b1642611093f800051223a1fd47da437000148119c16f3358498dfe8b54720465332481114835106e0723f89ca48000004b090e889800033d8e585ae5e40000d9946c0000c30000c724f00000000e9c9e0000000123e42e011800000003f41500000344481b981f83302b739000000960180c600000001634f202b89ca944062126867279a2a502401124700d68000f120000000000ab40000000d300000000001bf12ea9c310f0ee0c7a77f23ba7bd2bc15950009d000090d39a1178000000000000000084f2880e28f286961e09eacfbc8991540da8e820000000a586180002d0883d0d400043f09751e633c26d8000d4625a0f780000009fa2058710000000007221941242c0000000c2e00000000003
  | 19 => 0xf285b053d294100ccfc55d463267000e1780c39d48c9427b00000000001ea00010240002ed3cca758e5c30248a0254b3274300009b40008730ada92800000004a0000f7400000027fcd483e2022a0b00007bf11d8fe4be0a4c0000000936000016a3c521600000f00952720130000c2c2644b2000000141800042c0000f9696836082950c22db2a216c400038b000000000023e000000104a00000013287400004e99f6000016432c000000000000005380000000000000000000000000038a27510805b09a6000231892c3a62a60000c3cde24a000028b83049e2000035d15a8be2b78e3855294f00013d500e0001e18d740000000740000afa0004a40e0c0009ce3aca3f0c62a3f2f180000000002d39ad40009d421593a91966650002724ece7b700025c40007111938cf49268b84970720000098366001489e3494cb058400057200000013e20000000eb0000a39000292000008600019cc2585df1e619345de00000000010560003b88001438000000000000004c44e08e80000003ae00005a8000441228400066335c80002120002e300012ca548091800000008f000000000000005180000000000
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xd6410110005de7310110005dd731011003778501011000cfe76cc11000cfc76cc11001d7e75cc1100057d75cc1100067f65cc1100c67c65cc110006df63cc110026dc63cc11000df671cc110005f571cc11008cfe768c1100067f658c11009e7c658c1100377a508c11003778508c11008dfa768c110006fa768c1100077b658c11022f78658c1100a5f9738c110026fa638c110026f8638c110005f9728c11000dfa718c11000df8718c110036fb618c1100b7f2518c11022ff1518c110024ff764c11000cfe764c1100a4fd764c11000cfc764c1100057f754c11001d7c754c1100067f654c1100ae7c654c110005bf744c110005bc744c110006df634c110026dc634c110005f7714c11000df4714c1100077a504c11022778504c11000df8764c110026f8764c11000cf8764c1100077b754c11022778754c1100077b654c11022778654c110007bb744c110007b8744c110007db734c110007db634c110026fa634c110026f8634c110007d8634c110227da534c110227d9534c110007da434c110007d9434c110005fb724c110007f3714c11000dfa714c11000df8714c1100a7f0714c1100a6fb614c1100a7f2514c110227f1514c1100b4fe760c1100067f650c1100967c650c110005be740c110005bd740c1100b5fa700c11000cfe76c811000cfc76c811001d7e75c81100057d75c81100067f65c81100667c65c8110006ef62c811004eec62c811000df671c8110005f571c8110044fe76881100067f658811005e7c65881100377a5088110037785088110045fa7688110006fa76881100077b658811021f786588110005fb7388110005f9738811006df9728811004efa628811004ef8628811000dfa718811000df87188110036fb618811007ff2518811021ff1518811004cff764811000cfe764811006cfd764811000cfc76481100057f754811001d7c75481100067f65481100767c6548110005bf7448110005bc7448110006ef6248110006ec6248110005f7714811000df471481100077a504811021778504811000df8764811006ef8764811000cf876481100077b75481102177875481100077b6548110217786548110007bb7448110007b87448110005fb7348110005f97348110007eb7248110007eb624811004efa624811004ef86248110007e86248110217ea5248110217e95248110007f3714811000dfa714811000df8714811006ff0714811006efb614811006ff25148110217f1514811007cfe76081100067f65081100567c650811007dfa700811000df67684110036f6768411000cf67684110035f7758411020df57584110007776584110207746584110035f67084110037f27084110036f7608411000ff36084110037765084110037745084110037f23084110007f13084110037f22084110007f12084110
  | 1 => 0x8910024dc7358910006ef725891006cff7158910006f77158910084ff7058910006fb70589100067c505891007cfe76189100067f65189100067c6518910006ed621891004cff7518910014fe7518910004fd751891004cfc751891002cfe7418910004fd7418910024fe7318910004fd731891004eee7218910034ff711891000cfe7118910044fd711891000cfc711891004eef2118910046ed2118910034fe701891004ef97018910034fc70189100067c501891002cff76d0910004fe76d0910004fd76d091002cfc76d09100067f65d09101be7c65d0910006ef62d0910006ec62d091004cff7690910004fe7690910004fd769091004cfc76909100067f65909101967c6590910006bf649091002ebc6490910005fa7090910005f97090910004ff7650910004fe7650910004fd7650910004fc76509100067f65509101a67c655091004cff7610910004fe7610910004fd761091004cfc761091001d7e75109100057d75109100067f651091018e7c6510910006bf641091002ebc6410910006ef621091004eec621091000df67110910005f57110910005fa7010910005f97010910024ff76cc910004fe76cc910004fd76cc910024fc76cc9100067f65cc91017e7c65cc910005be74cc910005bd74cc910006ef62cc910006ec62cc910005fa70cc910005f970cc91004cff768c910004fe768c910004fd768c91004cfc768c9100067f658c9101567c658c910006df638c910026dc638c910005fa708c910005f9708c910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c9101667c654c91004cff760c910004fe760c910004fd760c91004cfc760c91001d7e750c9100057d750c9100067f650c91014e7c650c910006df630c910026dc630c910006ef620c91004eec620c91000df6710c910005f5710c910005fa700c910005f9700c91024d7e76941100367e769411024c7e76941100067f64941102467e64941100067d64941102467c64941100067f639411023e7e63941100067d639411023e7c63941100067f62941100067e62941100067d62941100067c62941100377771941100377471941100367f61941100357e70941100377a70941100367f609411010f7b109411003774109411003778109411000cfe76d011000cfc76d011001d7e75d01100057d75d01100067f65d01101067c65d0110006bf64d011002ebc64d011000df671d0110005f571d01102377850d01100ccfe76901100067f65901100de7c659011002ebe6490110006bd649011002cff765011000cfe76501100e4fd765011000cfc76501100057f755011001d7c75501100067f65501100ee7c6550110006bf645011002ebc6450110005f7715011000df471501100f4fe76101100067f65101100d67c651011002ebe6410110006b
  | 2 => 0x14fe75d8d10004fd75d8d10014fc75d8d1002cfe74d8d10004fd74d8d1004cfe72d8d10004fd72d8d10034ff71d8d1000cfe71d8d100b4fd71d8d1000cfc71d8d100b6df31d8d100b6dd31d8d10034fe70d8d10034fc70d8d100067c50d8d1001d7e7598d100057d7598d100067f6598d100067c6598d10006df6398d100a5f97098d100057f7558d1001d7c7558d100067f6558d100067c6558d10005bf7458d10005bc7458d10005ef7258d10005ec7258d100bdfb7058d10004ff7558d100067f7558d100047f7558d10014fe7558d10004fd7558d10014fc7558d100067c7558d100147c7558d10004ff7458d10006bf7458d10004bf7458d1002cfc7458d10006bc7458d1002cbc7458d10006df7358d10004ff7258d10006ef7258d10004ef7258d1004cfc7258d10006ec7258d10004ec7258d100a4ff7158d10006f77158d100bcff7058d10006fb7058d100067c5058d100b4fe7618d100067f6518d100067c6518d10005be7418d10005bd7418d10026de6318d10006dd6318d1002cff76d0d10004fe76d0d10004fd76d0d1002cfc76d0d100067f65d0d101fe7c65d0d1002ebe64d0d10006bd64d0d10006df63d0d10026dc63d0d10024ff7690d10004fe7690d10004fd7690d10024fc7690d100067f6590d101ee7c6590d10006bf6490d1002ebc6490d10005fa7090d10005f97090d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100067f6550d101de7c6550d1002ebe6450d10006bd6450d10024ff7610d10004fe7610d10004fd7610d10024fc7610d100067f6510d101ce7c6510d10006bf6410d1002ebc6410d10006df6310d10026dc6310d10005fa7010d10005f97010d100067f65d89100067c65d8910004ff75d8910014fe75d8910004fd75d8910014fc75d891002cfe74d8910004fd74d8910024fe73d8910004fd73d8910034ff71d891007cfd71d891007eef21d891007eed21d89100067c50d891001d7e75989100057d75989100067f65989100067c6598910006ef629891006df9709891004cff7598910014fe759891004e7e75989100147e7598910004fd759891004e7d75989100047d759891004cfc759891002cfe7498910004fd7498910024fe7398910004fd739891004cfe7298910084fd719891004ef5719891006cfd709891004ef970989100067c50989100057f755891001d7c75589100067f65589100067c6558910005bf7458910005bc7458910005df7358910005dc7358910085fb7058910004ff75589100067f75589100047f7558910014fe7558910004fd7558910014fc75589100067c75589100147c7558910004ff7458910006bf7458910004bf745891002cfc7458910006bc745891002cbc7458910004ff7358910006df7358910004df7358910024fc7358910006dc735
  | 3 => 0xb754c21025f78754c210007bb744c210007b8744c210037db734c210026fa634c210026f8634c21025fda534c21025fd9534c210007da434c210007d9434c210005fb724c21000dfa714c21000df8714c21006cfd76c821003d7e75c82100057d75c8210035f97688210036f9768821000cf97688210035fb7388210005f9738821004efa6288210037ea6288210037e96288210036f8628821000dfa7188210037f27188210037f17188210035f87188210084ff76482100057f754821003d7c7548210005bf7448210005bc74482100377a5048210037785048210085fb7648210006fb76482100077b7548210257787548210007bb7448210007b87448210005fb7348210005f97348210037eb724821004efa624821004ef86248210257ea5248210257e9524821000dfa714821000df8714821024d7e76d951001e7e76d95100147e76d95100077771d951010f7471d95100357c70d951010f7b10d951010f7410d951010f7810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f72d95100067e72d95100067d72d95100067c72d951010e7f71d951010e7e71d951010e7d71d951010e7c71d951010e7f41d951010e7e41d951010e7d41d951010e7c41d951010e7f31d951010e7e31d951010e7d31d951010e7c31d951010e7f21d951010e7e21d951010e7d21d951010e7c21d951010e7f70d951001e7e70d95100347e70d951010e7d70d951010e7c70d95100347c70d951010e7f10d951010e7e10d951010e7d10d951010e7c10d951002cfe76d91100067f65d91100067c65d9110004ff75d9110014fe75d9110004fd75d9110014fc75d9110024fe73d9110004fd73d911004cfe72d9110004fd72d9110034ff71d911000cfe71d91100f4fd71d911000cfc71d91100f6bf41d91100f6bd41d9110034fe70d9110034fc70d91100067c50d911001d7e75991100057d75991100067f65991100067c6599110006bf64991100e5f970991100057f755911001d7c75591100067f65591100067c6559110005df7359110005dc7359110005ef7259110005ec72591100fdfb7059110004ff75591100067f75591100047f7559110014fe7559110004fd7559110014fc75591100067c75591100147c7559110006bf7459110006be5459110006bd5459110004ff7359110006df7359110004df7359110024fc7359110006dc7359110024dc7359110004ff7259110006ef7259110004ef725911004cfc7259110006ec7259110004ec72591100e4ff7159110006f771591100fcff7059110006fb70591100067c50591100f4fe76191100067f65191100067c651911002ebe6419110006bd6419110024fe76d8d100067f65d8d100067c65d8d10004ff75d8d10
  | 4 => 0x8a1002cfe74d8a10036be74d8a1002cbe74d8a10004fd74d8a10036bd74d8a10004bd74d8a10024fe73d8a10036de73d8a10024de73d8a10004fd73d8a10036dd73d8a10004dd73d8a10036f571d8a10034fe70d8a10036fa70d8a100367e50d8a100367c50d8a1006cfd7698a1003d7e7598a100057d7598a10036ef6298a1004cff7598a10014fe7598a1004e7e7598a100147e7598a10004fd7598a1004e7d7598a100047d7598a1004cfc7598a1002cfe7498a10004fd7498a10024fe7398a10004fd7398a1004eee5298a10006ed5298a1004eef2198a10086ed2198a10034fe7098a1004efa7098a10034fc7098a100367e5098a100367c5098a10036ee2098a10036ec2098a10036ec6258a10004ff7558a10014fe7558a10004fd7558a10014fc7558a10004ff7458a1002cfc7458a10004ff7358a10024fc7358a10036ef7258a10006ee5258a10006ed5258a1006eef2158a1006eed2158a1004cff7058a10034fe7058a1006cfd7058a10034fc7058a100367e5058a100367c5058a10036ee2058a10036ec2058a10034ff7518a10014fe7518a10004fd7518a10034fc7518a1002cfe7418a10004fd7418a10024fe7318a10004fd7318a1004cfe7218a10036ee7218a10036f57118a10034fe7018a10036fa7018a100367e5018a100367c5018a1002cff76d0a10034fe76d0a10004fd76d0a10034fc76d0a1004cff7690a10034fe7690a10004fd7690a10034fc7690a1002ebe6490a10006bd6490a10035fa7090a10005f97090a10004ff7650a10034fe7650a10004fd7650a10034fc7650a1004cff7610a10034fe7610a10004fd7610a10034fc7610a1003d7e7510a100057d7510a1002ebe6410a10006bd6410a10035fa7010a10005f97010a10024ff76cca10034fe76cca10004fd76cca10034fc76cca10005be74cca10005bd74cca10035fa70cca10005f970cca1004cff768ca10034fe768ca10004fd768ca10034fc768ca10026de638ca10006dd638ca10035fa708ca10005f9708ca10004ff764ca10034fe764ca10004fd764ca10034fc764ca10005f7714ca1000df4714ca1004cff760ca10034fe760ca10004fd760ca10034fc760ca1003d7e750ca100057d750ca10026de630ca10006dd630ca10035fa700ca10005f9700ca100e4fd76d021003d7e75d02100057d75d02100377850d02100fcff76502100057f755021003d7c75502100a4fd76cc21003d7e75cc2100057d75cc210035f9768c210036f9768c21000cf9768c210026fa638c210037da638c210037d9638c210036f8638c210005f9728c21000dfa718c210037f2718c210037f1718c210035f8718c2100bcff764c2100057f754c21003d7c754c210005bf744c210005bc744c2100377a504c21003778504c2100bdfb764c210006fb764c2100077
  | 5 => 0x377850d0020004ff76500200057f75500200557c7550020004fd76cc0200557e75cc0200057d75cc020004ff764c0200057f754c0200557c754c020005bf744c020005bc744c02003778504c02004f6e75c802004f6d75c8020036ef65c802026eed65c8020035ed70c8020036ee60c80200376e50c80200376c50c802004df9728802004efa6288020037ea6288020006f96188020004ff76480200057f75480200557c7548020005bf7448020005bc74480200377a5048020037785048020035ef7648020006ef7648020004ef76480200076f75480202676c7548020036ef6548020266ed6548020007af7448020007ac7448020035ef7048020036ee60480200376e50480200376c504802004dfb7648020006fb7648020004fb76480200077b7548020267787548020007bb7448020007b87448020035fb7248020037eb724802004efa624802004fea6248020006f96148020034ff75d9210014fe75d9210004fd75d9210034fc75d9210024fe73d9210004fd73d921004cfe72d9210004fd72d9210036f571d9210034fe70d9210036fa70d92100367e50d92100367c50d92100e4fd769921003d7e75992100057d7599210036bf6499210036bc649921002cff7659210036bc6459210004ff7559210014fe7559210004fd7559210014fc7559210036bf7459210006be5459210006bd5459210004ff7359210024fc7359210004ff725921004cfc72592100e6bf41592100e6bd415921002cff7059210034fe705921002cfd7059210034fc70592100367e50592100367c5059210036be4059210036bc4059210034ff75d8e10014fe75d8e10004fd75d8e10034fc75d8e1002cfe74d8e10004fd74d8e1004cfe72d8e10004fd72d8e10036f571d8e10034fe70d8e10036fa70d8e100367e50d8e100367c50d8e100a4fd7698e1003d7e7598e100057d7598e10036df6398e10036dc6398e10024ff7658e10036dc6358e10004ff7558e10014fe7558e10004fd7558e10014fc7558e10004ff7458e1002cfc7458e10036df7358e10006de5358e10006dd5358e10004ff7258e1004cfc7258e100a6df3158e100a6dd3158e10024ff7058e10034fe7058e10024fd7058e10034fc7058e100367e5058e100367c5058e10036de3058e10036dc3058e1002cff76d0e10034fe76d0e10004fd76d0e10034fc76d0e1002ebe64d0e10006bd64d0e10024ff7690e10034fe7690e10004fd7690e10034fc7690e10026de6390e10006dd6390e10035fa7090e10005f97090e10004ff7650e10034fe7650e10004fd7650e10034fc7650e1002ebe6450e10006bd6450e10026de6350e10006dd6350e10024ff7610e10034fe7610e10004fd7610e10034fc7610e10035fa7010e10005f97010e10034ff75d8a10014fe75d8a10004fd75d8a10034fc75d
  | 6 => 0xc71d9020034fe70d9020036fa70d90200367e50d90200367c50d9020004fd7699020036bf6499020036bc649902002cff7659020036bc6459020004ff7559020014fe7559020004fd7559020014fc7559020034ff7459020036bf7459020006be5459020006bd5459020004ff7359020024fc735902002cff725902004cfe725902002cfd725902004cfc725902004ebe425902004ebc4259020004ff715902000cfe715902000cfc7159020034fe7059020034fc70590200367e50590200367c5059020036be4059020036bc4059020034ff75d8c20014fe75d8c20004fd75d8c20034fc75d8c2002cfe74d8c20004fd74d8c2004cfe72d8c20036ee72d8c2000cfe71d8c20004fd71d8c20034fc71d8c20034fe70d8c20036fa70d8c200367e50d8c200367c50d8c20004fd7698c20036df6398c20036dc6398c20024ff7658c20036dc6358c20004ff7558c20014fe7558c20004fd7558c20014fc7558c20004ff7458c2002cfc7458c20034ff7358c20036df7358c20006de5358c20006dd5358c20024ff7258c2004cfe7258c20024fd7258c2004cfc7258c2004ede3258c2004edc3258c20004ff7158c2000cfe7158c2000cfc7158c20034fe7058c20034fc7058c200367e5058c200367c5058c20036de3058c20036dc3058c2002cff76d0c20034fe76d0c20004fd76d0c20034fc76d0c2002ebe64d0c20006bd64d0c20024ff7690c20034fe7690c20004fd7690c20034fc7690c20026de6390c20006dd6390c2004dee7290c20005ed7290c20004ff7650c20034fe7650c20004fd7650c20034fc7650c2002ebe6450c20006bd6450c20026de6350c20006dd6350c20024ff7610c20034fe7610c20004fd7610c20034fc7610c20004fd76d0820004ff7650820004fd76cc820005be74cc820005bd74cc820004ff764c82004fcc324c82000cff7658420036f46158420004ff7558420014fe7558420004fd7558420014fc7558420004ff745842002cfc7458420004ff7358420024fc735842000cfd7258420046f65158420006f55158420046f64158420046f6315842004ef7215842004ef4215842000cff70584200367e50584200367c5058420036f61058420036f4105842002cff76d0420034fe76d0420004fd76d042002ebe64d0420006bd64d0420004ff7650420004fd7650420034fc765042002ebe6450420006bd6450420005ef725042004dec725042000ef66150420006f56150420024ff76cc420034fe76cc420004fd76cc420026de63cc420006dd63cc420004ff764c420004fd764c420034fc764c420026de634c420006dd634c420005ef724c42004dec724c42000ef6614c420006f5614c420084ff7648420005bf7448420005bc7448420005df7348420005dc7348420004fd76d00200557e75d00200057d75d0020
  | 7 => 0xc5200067f65cc52012e7c65cc520006bf64cc520006bc64cc520006f761cc52000ef461cc520004ff764c520004fe764c520004fc764c5200067f654c5201267c654c520006bf644c520006bc644c52007cfe76c85200067f65c852011e7c65c8520006bf64c8520006bc64c852000cfc76485200067f65485201167c6548520005bf7448520005bc7448520006bf6448520006bc6448520005df7348520005dc7348520006f7614852000ef4614852006fe42148520005fb7048520005f870485200057e76941200367e76941200647e76941200067f64941200073f64941200063f64941202467e64941200067d64941202467c64941200073c64941200063c64941200067f639412023e7e63941200067d639412023e7c63941200376f72941200376c72941200367f62941200067f619412010e7e619412010e7c61941200357e70941200377a70941200367f6094120004fe76d012004cfc76d01200757e75d01200057d75d01200067f65d01201067c65d0120006bf64d012002ebc64d0120005ee72d0120005ed72d0120004fe76901200067f65901200de7c6590120006bf649012002ebc649012002cff7650120004fd765012002cfc76501200057f75501200757c75501200067f65501200ee7c6550120006bf645012002ebc6450120005ef7250120005ec7250120004fe76101200067f65101200d67c6510120006bf641012002ebc6410120005de7310120005dd7310120007b94010120004fe76cc12004cfc76cc1200757e75cc1200057d75cc1200067f65cc1200c67c65cc120006bf64cc120006bc64cc120006df63cc120026dc63cc120005ee72cc120005ed72cc120004fe768c1200067f658c12009e7c658c120006bf648c120006bc648c120024ff764c120004fd764c120024fc764c1200057f754c1200757c754c1200067f654c1200ae7c654c120005bf744c120005bc744c120006bf644c120006bc644c120006df634c120026dc634c120005ef724c120005ec724c120004fe760c1200067f650c1200967c650c120005be740c120005bd740c120006bf640c120006bc640c120007d9300c1200757e75c81200057d75c81200067f65c81200667c65c8120006bf64c8120006bc64c81200077a50c81202877850c812004f7a75c812004f7975c81200077b65c81202877865c8120007bb64c8120007b864c812004fea52c8120287e952c8120005f971c81200067f658812005e7c6588120006bf6488120006bc6488120035ef758812027ded75881200076f65881202776c6588120007af6488120007ac6488120007eb60881200376e50881200376c5088120034ff75d9020014fe75d9020004fd75d9020034fc75d9020024fe73d9020004fd73d902004cfe72d9020036ee72d902000cfe71d9020004fd71d9020034f
  | 8 => 0x14fc7558d200067c7558d200147c7558d20004ff7458d20006bf7458d20004bf7458d2002cfc7458d20006bc7458d2002cbc7458d20006df7358d20004ff7258d20006ef7258d20004ff7158d20006f77158d20004f77158d2000cfe7158d2000cfc7158d20006f47158d2000cf47158d20004ff7058d20006fb7058d200067c5058d20004fe7618d200067f6518d200067c6518d20006bf6418d20006bc6418d20026de6318d20006dd6318d2002cff76d0d20004fe76d0d20004fd76d0d2002cfc76d0d200067f65d0d201fe7c65d0d20006bf64d0d2002ebc64d0d20024ff7690d20004fe7690d20004fd7690d20024fc7690d200067f6590d201ee7c6590d20006bf6490d2002ebc6490d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200067f6550d201de7c6550d20006bf6450d2002ebc6450d20024ff7610d20004fe7610d20004fd7610d20024fc7610d200067f6510d201ce7c6510d20006bf6410d2002ebc6410d20005fa7010d20005f97010d20004fe76d0920034fc76d09200067f65d09201be7c65d0920006bf64d092002ebc64d0920005fa70d0920005f970d0920004fe76909200067f65909201967c6590920006bf649092002ebc649092002cfc76509200067f65509201a67c6550920006bf645092002ebc6450920005fb7050920005f87050920004fe76109200757e75109200057d75109200067f651092018e7c6510920006bf641092002ebc6410920004fe76cc920034fc76cc9200067f65cc92017e7c65cc920005be74cc920005bd74cc920006bf64cc920006bc64cc920006df63cc920026dc63cc920005fa70cc920005f970cc920004fe768c9200067f658c9201567c658c920006bf648c920006bc648c920024fc764c9200067f654c9201667c654c920006bf644c920006bc644c920006df634c920026dc634c920005fb704c920005f8704c920004fe760c9200757e750c9200057d750c9200067f650c92014e7c650c920006bf640c920006bc640c92000cfe76d85200067f65d85200067c65d8520006bf64d8520006bc64d852006ef661d8520004ff75d8520014fe75d8520004fd75d8520014fc75d852002cfe74d8520004fd74d8520024fe73d8520004fd73d852000cfc72d852006ef431d852006ef621d8520034fe70d85200067c50d852006ef710d85200057f75585200757c75585200067f65585200067c6558520005bf7458520005bc7458520006bf6458520006bc6458520005df7358520005dc735852006ef46158520004fe76d0520004fd76d052002cfc76d05200067f65d052013e7c65d0520006bf64d052002ebc64d0520004ff7650520004fe7650520004fc76505200067f65505201367c6550520006bf645052002ebc6450520004fe76cc520004fd76cc520024fc76c
  | 9 => 0xf75d9120006be75d9120006bd75d9120006bc75d9120006bf73d9120006be73d9120006bd73d9120006bc73d9120006bf53d9120006be53d9120006bd53d9120006bc53d9120006bf72d9120006bd72d9120006bf52d9120006be52d9120006bd52d9120006bc52d9120006bf71d9120006be71d9120006bd71d9120006bc71d9120006bf51d9120006be51d9120006bd51d9120006bc51d9120006be31d9120006bc31d9120006be21d9120006bc21d9120006bf70d9120006bd70d9120006bf50d9120006be50d9120006bd50d9120006bc50d91200063c50d9120006bf10d9120006bc10d91200757e75991200057d75991200067f65991200067c6599120006bf64991200057f75591200757c75591200067f65591200067c6559120004ff75591200067f75591200047f7559120014fe7559120004fd7559120014fc75591200067c75591200147c7559120006bf7459120004ff7359120024fc7359120004ff7259120006ef7259120004ff715912000cfe715912000cfc7159120004ff7059120006fb70591200067c5059120004fe76191200067f65191200067c651912002ebe6419120006bd6419120005be7619120006be7619120004be7619120006bf65191200073f65191200063f6519120006be6519120006bd6519120006bc65191200073c65191200063c6519120007ae5219120007ad5219120006be6119120006bc61191200073c501912002ebf751912002ebe751912002ebd751912002ebc751912002ebf731912002ebe731912002ebd731912002ebc7319120006bf5319120006be5319120006bd5319120006bc531912002ebf721912002ebd7219120006bf5219120006be5219120006bd5219120006bc521912002ebf711912002ebe711912002ebd711912002ebc7119120006bf5119120006be5119120006bd5119120006bc5119120006be3119120006bc3119120006be2119120006bc211912002ebf701912002ebd7019120006bf5019120006be5019120006bd5019120006bc50191200063c5019120006bd2019120006bf1019120006bc1019120024fe76d8d200067f65d8d200067c65d8d20006bf64d8d20006bc64d8d20004ff75d8d20014fe75d8d20004fd75d8d20014fc75d8d2002cfe74d8d20004fd74d8d2004cfe72d8d2004cfc72d8d2000cfe71d8d20004fd71d8d2000cfc71d8d20006de31d8d20006dc31d8d200067c50d8d200757e7598d200057d7598d200067f6598d200067c6598d20005be7498d20005bd7498d20006bf6498d20006bc6498d20006df6398d200057f7558d200757c7558d200067f6558d200067c6558d20005bf7458d20005bc7458d20006bf6458d20006bc6458d20005f77158d2006df47158d20004ff7558d200067f7558d200047f7558d20014fe7558d20004fd7558d20
  | 10 => 0xa200057d7510a20006bf6410a2002ebc6410a20005be74cca20005bd74cca20026de63cca20006dd63cca20035fa70cca20005f970cca20024ff764ca20026de634ca20006dd634ca20005fb704ca20035f8704ca2005d7e750ca200057d750ca20007cd320ca2000cff7658620036f46158620004ff7558620014fe7558620004fd7558620014fc7558620004ff745862002cfc7458620004ff7358620024fc735862007ef65158620006f5515862007ef621586200367e50586200367c5058620036f61058620036f4105862002cff76d0620034fe76d0620004fd76d0620006bf64d062002ebc64d0620004ff7650620004fd7650620034fc7650620006bf645062002ebc6450620005ef7250620005ec7250620024ff76cc620034fe76cc620004fd76cc620004ff764c620004fd764c620034fc764c620005ef724c620005ec724c62006cfd76c862000cff7648620005bf7448620005bc7448620005df7348620005dc734862000ef66148620006f56148620005fb7048620035f8704862005d7e75d02200057d75d02200057f755022005d7c7550220037b8405022005d7e75cc2200057d75cc2200057f754c22005d7c754c220005bf744c220005bc744c220037d8304c22005d7e75c82200057d75c82200377a50c82200377850c8220035ed76c8220006ed76c822028f6e75c82200076d75c8220036ef65c822028eed65c82200376e50c8220037ea50c82200376a50c822028fe950c82200376c50c8220005f976c822004ef976c822004f7a75c822004f7975c822004fea52c822028fe952c8220005f971c82200757e76d95200767e76d95200147e76d95200076f72d95200776c72d95200067e61d95200067c61d95200357c70d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200067e73d95200067d73d95200067c73d95200067f72d95200767e72d95200767d72d95200767c72d95200067f71d95200067e71d95200067d71d95200067c71d95200067e41d95200067c41d95200067e31d95200067c31d95200067e21d95200067c21d95200067f70d95200767e70d95200767d70d95200767c70d95200767d20d95200067f10d95200067c10d952002cfe76d91200067f65d91200067c65d9120004ff75d9120014fe75d9120004fd75d9120014fc75d9120006bf54d9120006be54d9120006bd54d9120006bc54d9120024fe73d9120004fd73d912004cfe72d912004cfc72d912000cfe71d9120004fd71d912000cfc71d9120006be41d9120006bc41d91200067c50d912002cbe76d9120006bf65d91200073f65d91200063f65d9120006be65d9120006bd65d9120006bc65d91200073c65d91200063c65d9120007ae52d9120007ad52d9120006be61d9120006bc61d91200073c50d9120006b
  | 11 => 0x57d75d03201067e65d03200067d65d032002ebe64d0320006bd64d032004dee72d0320005ed72d032029f7850d03200de7e65903200067d6590320006bf649032002ebc649032002cff76503200057f75503200657c75503200ee7e65503200067d655032002ebe6450320006bd6450320005ef725032004dec72503200d67e65103200067d6510320006bf641032002ebc6410320005de7310320005dd73103200377850103200657e75cc3200057d75cc3200c67e65cc3200067d65cc320026de63cc320006dd63cc32004dee72cc320005ed72cc32009e7e658c3200067d658c32003778508c320024ff764c3200057f754c3200657c754c3200ae7e654c3200067d654c320005bf744c320005bc744c320026de634c320006dd634c320005ef724c32004dec724c32029778504c3200967e650c3200067d650c320005be740c320005bd740c320034ff75d9220014fe75d9220004fd75d9220034fc75d9220024fe73d9220004fd73d9220036ed72d922000cfe71d9220004fd71d9220034fc71d9220036fa70d92200367e50d92200367c50d9220004fd769922005d7e75992200057d7599220036bf6499220036bc649922002cff7659220036bc6459220004ff7559220014fe7559220004fd7559220014fc7559220036bf7459220006be5459220006bd5459220004ff7359220024fc7359220004ff715922000cfe715922000cfc7159220006be4159220006bc41592200367e50592200367c5059220036be4059220036bc4059220034ff75d8e20014fe75d8e20004fd75d8e20034fc75d8e2002cfe74d8e20004fd74d8e20036ed72d8e2000cfe71d8e20004fd71d8e20034fc71d8e20036fa70d8e200367e50d8e200367c50d8e20004fd7698e2005d7e7598e200057d7598e20036df6398e20036dc6398e20024ff7658e20036dc6358e20004ff7558e20014fe7558e20004fd7558e20014fc7558e20004ff7458e2002cfc7458e20036df7358e20006de5358e20006dd5358e20004ff7158e2000cfe7158e2000cfc7158e20006de3158e20006dc3158e200367e5058e200367c5058e20036de3058e20036dc3058e2002cff76d0e20034fe76d0e20004fd76d0e20034fc76d0e2002ebe64d0e20006bd64d0e20024ff7690e20034fe7690e20004fd7690e20034fc7690e20026de6390e20006dd6390e20005ee7290e20005ed7290e20004ff7650e20034fe7650e20004fd7650e20034fc7650e2002ebe6450e20006bd6450e20026de6350e20006dd6350e20024ff7610e20034fe7610e20004fd7610e20034fc7610e20035fa7010e20005f97010e2002ebe64d0a20006bd64d0a20035fa70d0a20005f970d0a20006bf6490a2002ebc6490a2002cff7650a2002ebe6450a20006bd6450a20005fb7050a20035f87050a2005d7e751
  | 12 => 0xf7459320004ff7359320024fc735932004ebe425932004ebc4259320004ff715932000cfe715932000cfc71593200067c505932004cff75d8f20014fe75d8f2004e7e75d8f200147e75d8f20004fd75d8f2004e7d75d8f200047d75d8f2004cfc75d8f2002cfe74d8f2004ebe74d8f2002cbe74d8f20004fd74d8f2004ebd74d8f20004bd74d8f2004eee72d8f2000cfe71d8f20004fd71d8f2000cfc71d8f2004ef970d8f200067c50d8f20004fd7698f200067e6598f200067d6598f20005be7498f20005bd7498f2004edf6398f2004edc6398f20024ff7658f200067e6558f200067d6558f2004edc6358f20004ff7558f20014fe7558f20004fd7558f20014fc7558f20004ff7458f2002cfc7458f2004edf7358f2004ede3258f2004edc3258f20004ff7158f2000cfe7158f2000cfc7158f200067c5058f2002cff76d0f2004cfe76d0f20004fd76d0f2004cfc76d0f201fe7e65d0f200067d65d0f20006bf64d0f2002ebc64d0f20026de63d0f20006dd63d0f20024ff7690f2004cfe7690f20004fd7690f2004cfc7690f201ee7e6590f200067d6590f2002ebe6490f20006bd6490f20004ff7650f2004cfe7650f20004fd7650f2004cfc7650f201de7e6550f200067d6550f20006bf6450f2002ebc6450f20024ff7610f2004cfe7610f20004fd7610f2004cfc7610f201ce7e6510f200067d6510f2002ebe6410f20006bd6410f20026de6310f20006dd6310f201be7e65d0b200067d65d0b201a67e6550b200067d6550b2017e7e65ccb200067d65ccb20005be74ccb20005bd74ccb201667e654cb200067d654cb2000cff76587200067e65587200067d655872004ef46158720004ff7558720014fe7558720004fd7558720014fc7558720004ff745872002cfc7458720004ff7358720024fc735872004ef7215872004ef421587200067c5058720086f7105872002cff76d072004cfe76d0720004fd76d072013e7e65d07200067d65d072002ebe64d0720006bd64d0720004ff7650720004fd765072004cfc76507201367e65507200067d655072002ebe6450720006bd6450720024ff76cc72004cfe76cc720004fd76cc72012e7e65cc7200067d65cc720026de63cc720006dd63cc720004ff764c720004fd764c72004cfc764c7201267e654c7200067d654c720026de634c720006dd634c720044ff76487201167e65487200067d6548720005bf7448720005bc7448720005df7348720005dc734872004fe421487200057d76943200367d76943200747d76943200067f64943202467e64943200067d64943202467c64943200067f639432023e7e63943200067d639432023e7c63943200376f72943200376c72943200367e629432010e7e61943200067d619432010e7c61943200357e70943200377a70943200657e75d0320
  | 13 => 0x830006bd6410830004ff7558430014fe7558430004fd7558430014fc7558430004ff745843002cfc745843000cfd7358430004ff725843004cfc7258430034ff7158430036f7715843008ef65158430006f55158430026f73158430026f4315843008ef621584300367e50584300367c5058430026fa3058430026f93058430036f61058430036f4105843002cff76d0430034fe76d0430004fd76d043002ebe64d0430006bd64d0430004ff7650430004fd7650430034fc765043002ebe6450430006bd6450430005df7350430025dc735043004cff76c8430034fe76c8430004fd76c8430006be64c8430006bd64c843004eee62c8430006ed62c8430004ff7648430004fd7648430034fc7648430005bf7448430005bc7448430006be6448430006bd6448430005df7348430025dc7348430006ee6248430006ed624843000ef66148430006f56148430004fd76d00300957e75d00300057d75d003002ebe64d0030006bd64d00300377850d0030004ff76500300057f75500300957c755003002ebe6450030006bd6450030035df764c030006df764c030004df764c0300075f754c0302a75c754c030036df654c0302a6dd654c0300079f744c0300079c744c030036df644c0300379e644c030006dd644c0300379d644c0300069d644c030035df704c030027db704c030036de604c030037da604c0300375e504c0300375c504c030037da404c030007d9404c03004d7f76597200667f76597200147f765972004e7f645972004e7c645972004e7f635972004e7c635972004f6e72597200676d725972004e7f61597200067e615972004e7c61597200067f74597200067e74597200067d74597200067c74597200067f73597200067e73597200067d73597200067c73597200667f725972004e7e72597200667d725972004e7c725972004e7e425972004e7c425972004e7e325972004e7c32597200067f71597200067e71597200067d71597200067c71597200067e41597200067c41597200067e31597200067c315972004e7f21597200067e215972004e7c21597200667f70597200667e70597200067d70597200667c705972004e7f205972004e7c20597200067f10597200067c105972004cff75d9320014fe75d932004e7e75d93200147e75d9320004fd75d932004e7d75d93200047d75d932004cfc75d9320006be54d9320006bd54d9320024fe73d932004ede73d9320024de73d9320004fd73d932004edd73d9320004dd73d932004eee72d932000cfe71d9320004fd71d932000cfc71d932004ef970d93200067c50d9320004fd76993200067e65993200067d659932004ebf649932004ebc649932002cff76593200067e65593200067d655932004ebc6459320004ff7559320014fe7559320004fd7559320014fc755932004eb
  | 14 => 0x6bd5199030006bc5199030026bf3199030026be3199030026bd3199030026bc3199030006be2199030006bc2199030036be7099030036bc7099030006bf5099030036be50990300363e5099030006bd5099030036bc50990300363c5099030026bf3099030036be3099030026bd3099030036bc3099030036be2099030036bc2099030006bf1099030036be1099030036bc1099030004ff7559030014fe7559030004fd7559030014fc7559030034ff7459030036bf7459030006bf5459030006be5459030006bd5459030006bc5459030024ff7359030024fe7359030024fd7359030024fc7359030026be4359030026bc4359030004ff725903004cfc7259030004ff715903000cfe715903000cfc7159030006be4159030006bc4159030034fe7059030034fc70590300367e50590300367c5059030036be4059030036bc4059030026df3059030006bf7559030006be7559030006bd7559030006bc7559030026bf7359030026be7359030026bd7359030026bc7359030026bf5359030026be5359030026bd5359030026bc5359030006bf7259030006be7259030006bd7259030006bc7259030006bf5259030006be5259030006bd5259030006bc5259030026bf3259030026be3259030026bd3259030026bc3259030006bf7159030006be7159030006bd7159030006bc7159030006bf5159030006be5159030006bd5159030006bc5159030026bf3159030026be3159030026bd3159030026bc3159030006be2159030006bc2159030036be7059030036bc7059030006bf5059030036be50590300363e5059030006bd5059030036bc50590300363c5059030026bf30590300269f3059030036be3059030026bd3059030036bc3059030036be2059030036bc2059030006bf1059030036be1059030036bc105903004cff7598830014fe7598830004fd759883004cfc759883002cfe7498830004fd7498830034fe7298830036ee729883004eee5298830006ed5298830026ef329883004eec329883000cfe7198830004fd719883000cfc71988300367e50988300367c5098830036ee2098830036ec2098830004ff7558830014fe7558830004fd7558830014fc7558830004ff745883002cfc7458830036ef7258830006ee5258830006ed5258830026ef3258830026ec3258830004ff715883000cfe715883000cfc71588300367e50588300367c5058830036ee2058830036ec205883002cff76d0830034fe76d0830004fd76d083002ebe64d0830006bd64d083004cff7690830034fe7690830004fd769083002ebe6490830006bd6490830025de7390830005dd7390830004ff7650830004fd7650830034fc765083002ebe6450830006bd645083004cff7610830034fe7610830004fd76108300957e75108300057d751083002ebe641
  | 15 => 0xf65585300067c6558530005bf7458530005bc7458530006bf6458530006bc6458530005ef7258530005ec72585300a6f46158530004fe76d0530004fd76d053002cfc76d05300067f65d053013e7c65d0530006bf64d053002ebc64d0530025de73d0530005dd73d05300079d43d0530004ff7650530004fe7650530004fc76505300067f65505301367c6550530006bf645053002ebc64505300079d435053000cfc764c5300067f654c5301267c654c530006bf644c530006bc644c530006f7614c53000ef4614c530005fb704c530005f8704c530004fe76c8530004fd76c853004cfc76c85300067f65c853011e7c65c8530006bf64c8530006bc64c8530006f761c853000ef461c8530004ff7648530004fe7648530004fc76485300067f65485301167c6548530005bf7448530005bc7448530006bf6448530006bc6448530005df7348530025dc73485300057e76941300367e76941300c47e76941300067f64941300073f64941300063f64941302467e64941300067d64941302467c64941300073c64941300063c64941300375f73941300375c73941300367f63941300075e43941300075d43941300067f62941300067c62941300067f619413010e7e619413010e7c61941300357e70941300377a70941300367f609413023f7b3094130037783094130024fe76d0130024fc76d01300ad7e75d01300057d75d01300067f65d01301067c65d0130006bf64d013002ebc64d0130025de73d0130005dd73d01300079d43d0130004fe76901300067f65901300de7c6590130006bf649013002ebc64901300079e439013003778509013002cff7650130004fd7650130024fc76501300057f75501300ad7c75501300067f65501300ee7c6550130006bf645013002ebc6450130005df7350130025dc73501300079d43501302bf785050130004fe76101300067f65101300d67c6510130006bf641013002ebc6410130025de7310130005dd73101300079e4310130007b940101300067f658c13009e7c658c130006bf648c130006bc648c130025fa708c130026fb608c130035df758c1302b5dd758c1300075f658c1302af5c658c130035df748c130005dd748c1300079f648c1300079c648c130035de708c130036df608c130027db608c1300375e508c1300375c508c13002ebf759903002ebe759903002ebd759903002ebc7599030026bf7399030026be7399030026bd7399030026bc7399030026bf5399030026be5399030026bd5399030026bc539903002ebf729903002ebe729903002ebd729903002ebc7299030006bf5299030006be5299030006bd5299030006bc5299030026bf3299030026be3299030026bd3299030026bc329903002ebf719903002ebe719903002ebd719903002ebc7199030006bf5199030006be5199030
  | 16 => 0xd300075f6590d302d75c6590d302cddd7490d300079f6490d3002ede6490d3002edc6490d300079c6490d3002e9c6490d302d79e5490d302d79d5490d30035de7090d30026df6090d30027db6090d302d75c5090d3002cfc7650d300067f6550d301de7c6550d30006bf6450d3002ebc6450d300279c4350d30005fb7050d30005f87050d30027d83050d3002edc7650d3002cdc7650d302cddf7550d302cddd7550d300075f6550d302c75c6550d30025df7450d300279f7450d300079f6450d3002ede6450d3002edc6450d300079c6450d30007db7050d30035dc7050d30007d87050d30026df6050d30027db6050d302c75c5050d300067f65d89300067c65d8930006bf64d8930006bc64d8930004ff75d8930014fe75d8930004fd75d8930014fc75d893002cfe74d8930004fd74d893000cfe71d8930004fd71d893000cfc71d8930006ee21d8930006ec21d89300067c50d89300ad7e75989300057d75989300067f65989300067c6598930005be7498930005bd7498930006bf6498930006bc6498930006ef62989300057f75589300ad7c75589300067f65589300067c6558930005bf7458930005bc7458930006bf6458930006bc6458930005f771589300a5f471589300067f65189300067c6518930006bf6418930006bc6418930006ed621893004cff7518930014fe7518930004fd751893004cfc751893002cfe7418930004fd741893000cfe7118930004fd711893000cfc7118930006ee211893004eec21189300067c5018930004fe76d0930004fd76d093002cfc76d09300067f65d09301be7c65d0930006bf64d093002ebc64d0930025de73d0930005dd73d0930004fe7690930004fd769093004cfc76909300067f65909301967c6590930006bf649093002ebc64909300079d4390930004ff7650930004fe7650930004fc76509300067f65509301a67c6550930006bf645093002ebc6450930004fe7610930004fd761093004cfc76109300ad7e75109300057d75109300067f651093018e7c6510930006bf641093002ebc6410930025de7310930005dd73109300079d4310930005fa7010930005f970109300067f658c9301567c658c930006bf648c930006bc648c930006ef628c93004eec628c930005fa708c930005f9708c9300067f654c9301667c654c930006bf644c930006bc644c930006ef624c930006ec624c930005fb704c930005f8704c930027d8304c93000cfe76d85300067f65d85300067c65d8530006bf64d8530006bc64d85300a6f661d8530004ff75d8530014fe75d8530004fd75d8530014fc75d853002cfe74d8530004fd74d853000cfc73d853004cfe72d8530004fd72d85300a6f631d85300a6f421d8530024fd70d85300067c50d85300a6f710d85300057f75585300ad7c75585300067
  | 17 => 0x6be65d9130006bd65d9130006bc65d91300073c65d91300063c65d91300079f73d91300079e53d91300079d53d9130006be61d9130006bc61d91300073c50d91302efbb30d91302efb830d9130006bf75d9130006be75d9130006bd75d9130006bc75d9130006bf73d91302eebe73d9130006bd73d91302eebc73d9130006bf53d91302eebe53d9130006bd53d91302eebc53d9130006bf72d9130006be72d9130006bd72d9130006bc72d9130006bf52d9130006be52d9130006bd52d9130006bc52d91302eebf32d91302eebc32d9130006bf71d9130006be71d9130006bd71d9130006bc71d9130006bf51d9130006be51d9130006bd51d9130006bc51d91302eebf31d9130006be31d91302eebc31d9130006be21d9130006bc21d91302eebf70d9130006bd70d9130006bf50d9130006be50d9130006bd50d9130006bc50d91300063c50d91302eebf30d91302eebc30d9130006bf10d9130006bc10d91300ad7e75991300057d75991300067f65991300067c6599130006bf64991300057f75591300ad7c75591300067f65591300067c6559130004ff75591300067f75591300047f7559130014fe7559130004fd7559130014fc75591300067c75591300147c7559130006bf7459130004ff7359130006df7359130004ff725913004cfc7259130004ff715913000cfe715913000cfc7159130004ff7059130006fb70591300067c5059130004fe76191300067f65191300067c651913002ebe6419130006bd6419130005be7619130006be7619130004be7619130006bf65191300073f65191300063f6519130006be6519130006bd6519130006bc65191300073c65191300063c65191300079d73191300079e53191300079d5319130006be6119130006bc61191300073c50191302e7bb30191302e7b8301913002ebf751913002ebe751913002ebd751913002ebc751913002ebf731913002ebe731913002ebd731913002e9d731913002ebc7319130006bf53191302e6be5319130006bd53191302e6bc531913002ebf721913002ebe721913002ebd721913002ebc7219130006bf5219130006be5219130006bd5219130006bc52191302e6bf32191302e6bc321913002ebf711913002ebe711913002ebd711913002ebc7119130006bf5119130006be5119130006bd5119130006bc51191302e6bf3119130006be31191302e6bc3119130006be2119130006bc211913002ebf701913002ebd7019130006bf5019130006be5019130006bd5019130006bc50191300063c50191302e6bf3019130006bd30191302e6bc3019130006bf1019130006bc1019130004fe76d0d30034fc76d0d300067f65d0d301fe7c65d0d30006bf64d0d3002ebc64d0d30005fa70d0d30005f970d0d30005de7690d30026de7690d30025df7590d302dddd759
  | 18 => 0xf76d0a30034fe76d0a30004fd76d0a3004cff7690a30034fe7690a30004fd7690a30006bf6490a3002ebc6490a30025de7390a30005dd7390a30004ff7650a30004fd7650a30034fc7650a3004cff7610a30034fe7610a30004fd7610a3009d7e7510a300057d7510a30006bf6410a3002ebc6410a30035fa7010a30005f97010a3004eee628ca30006ed628ca30035fa708ca30005f9708ca30006ee624ca30006ed624ca30027cc324ca30005fb704ca30035f8704ca3000cff7658630036f46158630004ff7558630014fe7558630004fd7558630014fc7558630004ff745863002cfc7458630004ff725863004cfc72586300b6f65158630006f551586300b6f63158630034fc70586300367e50586300367c5058630036f61058630036f4105863002cff76d0630034fe76d0630004fd76d0630006bf64d063002ebc64d0630004ff7650630004fd7650630034fc7650630006bf645063002ebc6450630005df7350630025dc735063000cff764c63000ef6614c630006f5614c630005fb704c630035f8704c63004cff76c8630034fe76c8630004fd76c8630004ff7648630004fd7648630034fc7648630005bf7448630005bc7448630005df7348630025dc734863009d7e75d02300057d75d0230036bf64d0230036bc64d02300057f755023009d7c7550230036bf6450230036bc6450230037785050230037b84050230035dd76cc230026dd76cc2300275e75cc2300275d75cc230036df65cc2302f6dd65cc230036df64cc230006dd64cc230037da60cc2300375e50cc230037da50cc2300375a50cc2302f7d950cc2300375c50cc2300ad7e76d95300ae7e76d95300147e76d95300075f73d95300af5c73d95300067e61d95300067c61d95300357c70d953023f7b30d953023f7830d95300067f74d95300067e74d95300067d74d95300067c74d95300067f73d953023e7e73d95300ae7d73d953023e7c73d953023e7e43d953023e7c43d95300067f72d95300067e72d95300067d72d95300067c72d953023e7f32d953023e7c32d95300067f71d95300067e71d95300067d71d95300067c71d95300067e41d95300067c41d953023e7f31d95300067e31d953023e7c31d95300067e21d95300067c21d953023e7f70d95300ae7e70d95300ae7d70d95300ae7c70d953023e7f30d95300ae7d30d953023e7c30d95300067f10d95300067c10d953002cfe76d91300067f65d91300067c65d9130004ff75d9130014fe75d9130004fd75d9130014fc75d9130006bf54d9130006be54d9130006bd54d9130006bc54d9130024fe73d9130024fc73d913004cfe72d9130004fd72d913000cfe71d9130004fd71d913000cfc71d9130006be41d9130006bc41d91300067c50d913002cbe76d9130006bf65d91300073f65d91300063f65d9130
  | 19 => 0x7301367e65507300067d655073002ebe6450730006bd64507300079d435073004cff76c8730024fe76c8730004fd76c873011e7e65c87300067d65c873004eee62c8730006ed62c8730004ff7648730004fd7648730024fc76487301167e65487300067d6548730005bf7448730005bc7448730005df7348730025dc7348730006ee6248730006ed624873023d7d76943300367d76943300ac7d769433023e7f64943302467e64943300067d649433023e7c64943300375f73943300375c73943300367e639433023f5e43943300075d43943300067e62943300067d629433010e7e61943300067d619433010e7c61943300357e70943300377a70943300377a30943300375c30943300c57e75d03300057d75d03301067e65d03300067d65d033002ebe64d0330006bd64d0330025de73d0330005dd73d03300079d43d03302ff7850d03300de7e65903300067d65903302eebf649033002ebc6490330035dc73903302ef9e439033002cff76503300057f75503300c57c75503300ee7e65503300067d655033002ebe6450330006bd6450330005df7350330025dc73503300079d43503300d67e65103300067d65103302e6bf641033002ebc6410330025de7310330005dd73103302e79e4310330037785010330034ff75d9230014fe75d9230004fd75d9230034fc75d9230036dd73d92302eebe43d92302eebc43d923004cfe72d9230004fd72d923000cfe71d9230004fd71d9230034fc71d9230036fa70d92300367e50d92300367c50d9230004fd7699230036bf6499230036bc649923002cff7659230036bc6459230004ff7559230014fe7559230004fd7559230014fc7559230036bf7459230006be5459230006bd5459230004ff725923004cfc7259230004ff715923000cfe715923000cfc7159230034fc70592300367e50592300367c5059230036be4059230036bc405923002ebe64d0e30006bd64d0e30035fa70d0e30005f970d0e3002cff7650e3002ebe6450e30006bd6450e30005fb7050e30035f87050e3009d7e7598a300057d7598a30036ef6298a3004cff7598a30014fe7598a3004e7e7598a300147e7598a30004fd7598a3004e7d7598a300047d7598a3004cfc7598a3002cfe7498a30004fd7498a3004eee5298a30006ed5298a3000cfe7198a30004fd7198a3000cfc7198a30034fe7098a300367e5098a300367c5098a30036ee2098a30036ec2098a30005bf7458a30005bc7458a30036ec6258a30004ff7558a30014fe7558a30004fd7558a30014fc7558a30004ff7458a30006bf7458a30004bf7458a3002cfc7458a30006bc7458a3002cbc7458a30006ee5258a30006ed5258a30004ff7158a3000cfe7158a3000cfc7158a30034fc7058a300367e5058a300367c5058a30036ee2058a30036ec2058a3002cf
  | 20 => 0x69d6350040005bc7250040005bf7150040035bf705004002fbb7050040036be6050040037ba6050040317bb50500400373e50500400373c5050040037b850500400373850500400067f74597300067e74597300067d74597300067c74597300267f73597300267e73597300267d73597300267c73597300267f43597300267e43597300267d43597300267c43597300067f72597300067e72597300067d72597300067c72597300267f32597300267e32597300267d32597300267c32597300067f71597300067e71597300067d71597300067c71597300067e41597300067c41597300267f31597300267e31597300267d31597300267c31597300067e21597300067c21597300c67f70597300c67e70597300067d70597300c67c70597300267f30597300267e30597300267d30597300267c30597300067f10597300067c1059730004ff7559330014fe7559330004fd7559330014fc7559330026bf7459330024fc7359330026be4359330026bc4359330004ff725933004cfc7259330004ff715933000cfe715933000cfc71593300067c5059330025df7650f30006df7650f3030ddf7550f3030ddd7550f300275e6550f300275d6550f300279f7450f300279f6450f3002ede6450f30026dc6450f300279c6450f30035dc7050f303075c5050f3004cff7598b30014fe7598b30004fd7598b3004cfc7598b3002cfe7498b30004fd7498b3004eee7298b30026ef3298b3004eec3298b3000cfe7198b30004fd7198b3000cfc7198b300067c5098b30004ff7558b30014fe7558b30004fd7558b30014fc7558b30004ff7458b3002cfc7458b30026ef7258b30026ef3258b30026ec3258b30004ff7158b3000cfe7158b3000cfc7158b300067c5058b3002cff76d0b30024fe76d0b30004fd76d0b301be7e65d0b300067d65d0b30025de73d0b30005dd73d0b30006ee62d0b30006ed62d0b3004cff7690b30024fe7690b30004fd7690b301967e6590b300067d6590b3002ebe6490b30006bd6490b300079d4390b30004ff7650b30004fd7650b30024fc7650b301a67e6550b300067d6550b3004cff7610b30024fe7610b30004fd7610b300c57e7510b300057d7510b3018e7e6510b300067d6510b3002ebe6410b30006bd6410b30025de7310b30005dd7310b300079d4310b3004eee6210b30006ed6210b30004ff7558730014fe7558730004fd7558730014fc7558730004ff745873002cfc7458730004ff725873004cfc7258730026f77158730026f73158730026f431587300067c5058730026fa3058730026f930587300bef7105873002cff76d0730024fe76d0730004fd76d073013e7e65d07300067d65d073002ebe64d0730006bd64d0730025de73d0730005dd73d07300079d43d0730004ff7650730004fd7650730024fc765
  | 21 => 0xd7398840034fe7298840036ee729884004eee5298840006ed529884002eef429884004eec429884000cfe7198840004fd719884000cfc71988400367e50988400367c5098840036ee2098840036ec2098840004ff7558840014fe7558840004fd7558840014fc7558840004ff7358840024fc7358840036ef7258840006ee5258840006ed525884002eef425884002ebc425884002eec4258840004ff715884000cfe715884000cfc715884002ebf41588400367e50588400367c5058840036ee2058840036ec205884002dbd7690840006bd769084002ebf659084033ebd65908402e5be739084002f9e6390840006bd639084002f9d63908400069d639084002dbe729084002fae7290840006bd6290840005bd71908401aebe619084002ebc6190840005bd7090840336be609084002fba609084032f3e509084032f3c5090840024ff76cc840034fe76cc840004fd76cc84002dbe74cc840005bd74cc840026de63cc840006dd63cc84004cff768c840034fe768c840004fd768c84002dbe748c840005bd748c840026de638c840006dd638c840004ff764c840004fd764c840034fc764c840005bf744c84002dbc744c840026de634c840006dd634c84004cff760c840034fe760c840004fd760c8400d57e750c8400057d750c8402e5bf740c84002dbc740c840026de630c840006dd630c840004ff7558440014fe7558440004fd7558440014fc755844000cfd7458440004ff7358440024fc7358440004ff725844004cfc7258440034ff7158440036f771584400cef65158440006f5515844002ef7415844002ef441584400cef621584400367e50584400367c5058440036f61058440036f4105844002dbf76504400febf765044002ebf6550440326bd65504402e5bc735044002f9e6350440006bd635044002f9d63504400069d6350440005bc7250440006bd625044002dbf715044002fb7715044000ebe615044000ebc6150440005bf70504400f6be605044002fba605044031f3e505044031f3c5050440024ff76cc440034fe76cc440004fd76cc4402e5bf74cc44002dbc74cc440026de63cc440006dd63cc440004ff764c440004fd764c440034fc764c440005bf744c44002dbc744c440026de634c440006dd634c44004cff76c8440034fe76c8440004fd76c8440005bf74c844002dbc74c8440006de63c8440006dd63c844004eee62c8440006ed62c8440004ff7648440004fd7648440034fc7648440005bf744844002dbc7448440005df7348440005dc7348440006de6348440006dd6348440006ee6248440006ed624844000ef66148440006f56148440035bf7650040006bf7650040004bf76500400073f75500403173c7550040036bf6550040316bd65500402e5bc73500400379e6350040006bd63500400379d6350040
  | 22 => 0x140006bc6290140006bf6190140035be7090140036bf609014002fbb60901400373e50901400373c5090140026df7598c40026de7598c40026dd7598c40026dc7598c40026df7498c40026de7498c40026dd7498c40026dc7498c4002edf5498c4002ede5498c4002edd5498c4002edc5498c40026df7298c40026de7298c40026dd7298c40026dc7298c40006df5298c40006de5298c40006dd5298c40006dc5298c4002edf4298c4002ede4298c4002edd4298c4002edc4298c40026df7198c40026de7198c40026dd7198c40026dc7198c40006df5198c40006de5198c40006dd5198c40006dc5198c4002edf4198c4002ede4198c4002edd4198c4002edc4198c40006de2198c40006dc2198c40036de7098c40036dc7098c40006df5098c40036de5098c400365e5098c40006dd5098c40036dc5098c400365c5098c4002edf4098c40036de4098c4002edd4098c40036dc4098c40036de2098c40036dc2098c40006df1098c40036de1098c40036dc1098c40004ff7558c40014fe7558c40004fd7558c40014fc7558c40036df7358c40006df5358c40006de5358c40006dd5358c40006dc5358c4002edf4358c4002ebc4358c4002edc4358c4002e9c4358c40004ff7258c4004cfc7258c4002ebc4258c40004ff7158c4000cfe7158c4000cfc7158c4002ebf4158c40006de3158c40006dc3158c400367e5058c400367c5058c4002ebf4058c40036de3058c40036dc3058c40006df7558c40006de7558c40006dd7558c40006dc7558c4002edf7458c4002ede7458c4002edc7458c4002edf5458c4002ede5458c4002edd5458c4002edc5458c40006df7258c40006de7258c40006dd7258c40006dc7258c40006df5258c40006de5258c40006dd5258c40006dc5258c4002edf4258c4002ede4258c4002edd4258c4002edc4258c4002e9c4258c40006df7158c40006de7158c40006dd7158c40006dc7158c40006df5158c40006de5158c40006dd5158c40006dc5158c4002edf4158c4002e9f4158c4002ede4158c4002edd4158c4002edc4158c40006de2158c40006dc2158c40036de7058c40036dc7058c40006df5058c40036de5058c400365e5058c40006dd5058c40036dc5058c400365c5058c4002edf4058c4002e9f4058c40036de4058c4002edd4058c40036dc4058c40036de2058c40036dc2058c40006df1058c40036de1058c40036dc1058c4002dbd7690c402e6bd7690c40004bd7690c4002ebf6590c4034ebd6590c4002dbe7390c4002f9e7390c4002ebf6390c4002f9e6390c402e6bd6390c4002f9d6390c400069d6390c40005be7290c40005bd7190c40005bd7090c402eebe6090c4002fba6090c403473e5090c403473c5090c4004cff7598840014fe7598840004fd759884004cfc7598840024fe7398840004f
  | 23 => 0x57d75989400067f65989400067c6598940005de7398940005dd7398940006ef62989400057f75589400ed7c75589400067f65589400067c65589400067f65189400067c6518940006ed621894004cff7518940014fe7518940004fd751894004cfc7518940006be5418940006bd5418940024fe7318940004fd7318940006bf4318940006bd431894000cfe7118940004fd711894000cfc7118940006ee211894004eec21189400067c50189400067f65909401967c6590940006ef629094004eec6290940005fa7090940005f970909400067f65509401a67c6550940006ef6250940006ec6250940005fb7050940005f8705094002fb84050940004fe76cc940004fd76cc940024fc76cc9400067f65cc94017e7c65cc94002dbe74cc940005bd74cc940006df63cc940026dc63cc940004fe768c940004fd768c94004cfc768c9400067f658c9401567c658c940006ef628c94004eec628c940004ff764c940004fe764c940004fc764c9400067f654c9401667c654c940006df634c940026dc634c940006ef624c940006ec624c940004fe760c940004fd760c94004cfc760c9400ed7e750c9400057d750c9400067f650c94014e7c650c94002dbe740c940005bd740c940005fa700c940005f9700c94000cfe76d85400067f65d85400067c65d85400e6f661d8540004ff75d8540014fe75d8540004fd75d8540014fc75d854000cfc74d8540006be54d8540006bd54d8540024fe73d8540004fd73d8540006bf43d8540006bd43d854004cfe72d8540004fd72d85400e6f641d854002cfd70d85400067c50d85400e6f710d85400057f75585400ed7c75585400067f65585400067c6558540005df7358540005dc7358540005ef7258540005ec72585400e6f4615854000cfc76505400067f65505401367c6550540006f7615054000ef46150540005fb7050540005f87050540004fe76cc540004fd76cc540024fc76cc5400067f65cc54012e7c65cc54002dbe74cc540005bd74cc540004ff764c540004fe764c540004fc764c5400067f654c5401267c654c540004fe76c8540004fd76c854004cfc76c85400067f65c854011e7c65c8540004ff7648540004fe7648540004fc76485400067f65485401167c6548540005bf744854002dbc7448540005df7348540005dc73485400057e76941400367e76941401047e76941400373f74941400373c74941400367f64941400067f639414023e7c63941400073f43941400073d43941400067f62941400067c62941400067f619414010e7e619414010e7c61941400357e70941400377a70941400367f60941402477b40941400377840941400067f65901400de7c659014002dfa709014002efb6090140035bf759014035dbd75901400073f65901403573c6590140005bd73901402eebc639
  | 24 => 0xf74cc64002dbc74cc640004ff764c640004fd764c640034fc764c640005bf744c64002dbc744c64004cff76c8640034fe76c8640004fd76c8640005bf74c864002dbc74c8640004ff7648640004fd7648640034fc7648640005bf744864002dbc7448640005df7348640005dc7348640035bd76d024002ebd76d024002f3e75d024002f3d75d0240036bf65d0240386bd65d02402edbe73d0240006bd63d0240005be72d0240005bd71d0240037ba60d02400373e50d0240037ba50d02400373a50d0240387b950d02400373c50d02400ed7e76d95400ee7e76d95400147e76d95400073f74d95400ef3c74d95400067e61d95400067c61d95400357c70d95402477b40d95402477840d95400067f74d95402467e74d95400ee7d74d95402467c74d95400067f73d95400067e73d95400067d73d95400067c73d95402467f43d95402467c43d95400067f72d95400067e72d95400067d72d95400067c72d95402467f42d95402467c42d95400067f71d95400067e71d95400067d71d95400067c71d95402467f41d95400067e41d95402467c41d95400067e31d95400067c31d95400067e21d95400067c21d95402467f70d95400ee7e70d95400ee7d70d95400ee7c70d95402467f40d95400ee7d40d95402467c40d95400067f10d95400067c10d95400067f65d8d400067c65d8d40004ff75d8d40014fe75d8d40004fd75d8d40014fc75d8d4004cfe72d8d40004fd72d8d4000cfe71d8d40004fd71d8d4000cfc71d8d40006de31d8d40006dc31d8d400067c50d8d400ed7e7598d400057d7598d400067f6598d400067c6598d40006df6398d40005ee7298d40005ed7298d400057f7558d400ed7c7558d400067f6558d400067c6558d400067f6518d400067c6518d40026de6318d40006dd6318d40005be76d0d4002ebe76d0d40004be76d0d4002dbf75d0d4037dbd75d0d400073f65d0d403773c65d0d40026be63d0d40026bc63d0d40035be70d0d4002ebf60d0d4002fbb60d0d403773c50d0d400067f6590d401ee7c6590d4036dbd7490d40006df6390d40026dc6390d40005fa7090d40005f97090d40024fc7650d400067f6550d401de7c6550d40006df6350d40026dc6350d4002f9c4350d40005fb7050d40005f87050d4002fb84050d40024bc7650d4036dbf7550d4036dbd7550d400073f6550d403673c6550d4002dbf7350d4002f9f7350d400079f6350d40026be6350d40026bc6350d400079c6350d40007bb7050d40035bc7050d40007b87050d4002ebf6050d4002fbb6050d403673c5050d400067f65d89400067c65d8940004ff75d8940014fe75d8940004fd75d8940014fc75d8940024fe73d8940004fd73d894000cfe71d8940004fd71d894000cfc71d8940006ee21d8940006ec21d89400067c50d89400ed7e7598940
  | 25 => 0xe4002fba6010e403b73e5010e403b73c5010e400dd7e7598a400057d7598a40036ef6298a4004cff7598a40014fe7598a4004e7e7598a400147e7598a40004fd7598a4004e7d7598a400047d7598a4004cfc7598a40024fe7398a40004fd7398a4004eee5298a40006ed5298a4000cfe7198a40004fd7198a4000cfc7198a40034fe7098a400367e5098a400367c5098a40036ee2098a40036ec2098a40036ec6258a40004ff7558a40014fe7558a40004fd7558a40014fc7558a40004ff7358a40024fc7358a40006ee5258a40006ed5258a40004ff7158a4000cfe7158a4000cfc7158a40034fc7058a400367e5058a400367c5058a40036ee2058a40036ec2058a4004eee6290a40006ed6290a40035fa7090a40005f97090a40336bf6590a40336bd6590a402edbe7390a40006bd6390a4002dbe7290a40007ae6290a40006bd6290a40007ad6290a40005bd7190a401aebe6190a401aebc6190a40007ba7090a40005bd7090a40007b97090a4002ebe6090a4032f3e5090a4032f3c5090a40006ee6250a40006ed6250a40005fb7050a40035f87050a40005bd7610a4002ebd7610a4002f3e7510a4002f3d7510a403aebf6510a403aebd6510a402edbe7310a40006bd6310a4002fae7210a40006bd6210a40005bd7110a40186be6110a40186bc6110a40005bd7010a4002fba6010a403a73e5010a403a73c5010a40024ff76cca40034fe76cca40004fd76cca4002dbe74cca40005bd74cca4004cff768ca40034fe768ca40004fd768ca4002dbe748ca40005bd748ca40004ff764ca40004fd764ca40034fc764ca40005bf744ca4002dbc744ca4004cff760ca40034fe760ca40004fd760ca400dd7e750ca400057d750ca402edbf740ca4002dbc740ca40035fa700ca40005f9700ca4000cff7658640036f46158640004ff7558640014fe7558640004fd7558640014fc7558640004ff7358640024fc7358640004ff725864004cfc72586400f6f65158640006f551586400f6f64158640034fc70586400367e50586400367c5058640036f61058640036f41058640005bd76d064002ebd76d064039ebf65d064039ebd65d06402edbe73d0640006bd63d0640005be72d0640006bd62d064000ebe61d064000ebc61d0640005bd70d064002fba60d06403973e50d06403973c50d064000cff765064000ef66150640006f56150640005fb7050640035f870506400f5bf765064000ebf765064000cbf765064038ebf655064038ebd65506402edbc7350640006bd6350640005bc7250640006bd625064002dbf715064002fb7715064000ebe61506400f7b66150640007b5615064000ebc6150640005bf7050640007bb7050640007b8705064002ebe605064031f3e505064031f3c5050640024ff76cc640034fe76cc640004fd76cc6402edb
  | 26 => 0x4cff7598b40014fe7598b40004fd7598b4004cfc7598b4002ebe5498b40006bd5498b40024fe7398b40004fd7398b4002ebf4398b40006bd4398b4004eee7298b4002eef4298b4004eec4298b4000cfe7198b40004fd7198b4000cfc7198b400067c5098b4002ebc4098b40004ff7558b40014fe7558b40004fd7558b40014fc7558b40004ff7358b40024fc7358b4002eef7258b4002eef4258b4002eec4258b40004ff7158b4000cfe7158b4000cfc7158b400067c5058b40024ff76ccb4002cfe76ccb40004fd76ccb4017e7e65ccb400067d65ccb4002dbe74ccb40005bd74ccb4004cff768cb4002cfe768cb40004fd768cb401567e658cb400067d658cb40004ff764cb40004fd764cb4002cfc764cb401667e654cb400067d654cb4004cff760cb4002cfe760cb40004fd760cb401057e750cb400057d750cb4014e7e650cb400067d650cb4002dbe740cb40005bd740cb40004ff7558740014fe7558740004fd7558740014fc755874002ebe5458740006bd5458740004ff7358740024fc735874002ebf4358740006bd4358740004ff725874004cfc725874002ef7715874002ef7415874002ef441587400067c505874002ebc40587400fef71058740024ff76cc74002cfe76cc740004fd76cc74012e7e65cc7400067d65cc74002dbe74cc740005bd74cc740004ff764c740004fd764c74002cfc764c7401267e654c7400067d654c74004cff76c874002cfe76c8740004fd76c874011e7e65c87400067d65c8740004ff7648740004fd764874002cfc76487401167e65487400067d6548740005bf744874002dbc7448740005df7348740005dc73487402457d76943400367d76943400ec7d76943400373f74943400373c74943400367e649434023e7e63943400067d63943402473f43943400073d43943400067e62943400067d629434010e7e61943400067d619434010e7c61943400357e70943400377a70943400377a40943400373c4094340036df6398e40036dc6398e40036dc6358e40004ff7558e40014fe7558e40004fd7558e40014fc7558e40006de5358e40006dd5358e40004ff7258e4004cfc7258e40004ff7158e4000cfe7158e4000cfc7158e40034fc7058e400367e5058e400367c5058e40036de3058e40036dc3058e40026de6390e40006dd6390e40035fa7090e40005f97090e403c6bf6590e403c6bd6590e4002dbe7390e402ef9e6390e402eebd6390e400079d6390e40005be7290e40005bd7190e402efba7090e40005bd7090e402efb97090e4002ebe6090e403473e5090e403473c5090e40024ff7650e40026de6350e40006dd6350e40005fb7050e40035f87050e40005bd7610e4002ebd7610e403bebf6510e403bebd6510e4002f9e7310e402eebd6310e40005be7210e40005bd7110e40005bd701
  | 27 => 0xf70506500357c705065024e7e60506501377a605065023d7f76cc6500357e76cc6500057d76cc6500357c76cc65023d7f74cc6502457e74cc6500057d74cc65023d7c74cc65010d7e73cc6500057e72cc6500057d72cc65023f5f32cc6500075d32cc65010d7d71cc65010f5e31cc65010f7631cc65010f5c31cc6500357e70cc6500057d70cc6500357c70cc65024e7e60cc65012f7a60cc6500057f764c6500357e764c6500057d764c6500357c764c6500057f744c6502457e744c6500057d744c6502457c744c65010d7f734c6500057f724c6500057c724c6500075f324c6500075d324c65010d7f714c65023f77314c65010f5e314c65010f5c314c65010f74314c6500057f704c6500357c704c65024e7e604c6501277a604c6500057f76c86500357e76c86500057d76c86500357c76c86500057f74c86502457e74c86500057d74c86502457c74c86500057f73c865023d7e73c86500057d73c865023d7c73c865010d7e72c86500076e32c86500076d32c865010d7d71c865010f6e21c865010f7621c865010f6c21c86500357e70c86500057d70c865024e7e60c865011f7a60c86500057f76486500357e76486500057d76486500357c76486500057f74486500073f74486500053f74486502457e74486500057d74486502457c74486500073c74486500053c74486500057f73486500075f73486500055f734865023d7e73486500057d734865023d7c73486500075c73486500055c734865010d7f72486500076e32486500076d324865010d7f714865000777214865010f6e214865010f6c214865010f7421486500057f70486500357c704865024e7e60486501177a604865002e7f745974002e7e745974002e7d745974002e7c74597400067f73597400067e73597400067d73597400067c735974002e7f435974002e7e435974002e7d435974002e7c43597400067f72597400067e72597400067d72597400067c725974002e7f425974002e7e425974002e7d425974002e7c42597400067f71597400067e71597400067d71597400067c715974002e7f415974002e7e415974002e7d415974002e7c41597400067e31597400067c31597400067e21597400067c21597401067f70597401067e70597400067d70597401067c705974002e7f405974002e7e405974002e7d405974002e7c40597400067f10597400067c1059740004ff7558f40014fe7558f40004fd7558f40014fc7558f4002edf7358f4002edf4358f4002edc4358f40004ff7258f4004cfc7258f40004ff7158f4000cfe7158f4000cfc7158f400067c5058f4002dbf7650f40006bf7650f403d5bf7550f403d5bd7550f4002f3e6550f4002f3d6550f4002f9f7350f4002f9f6350f40026be6350f40026bc6350f4002f9c6350f40035bc7050f403cf3c5050f40
  | 28 => 0xa502473f4210a502476e4210a500073d4210a502476d4210a5010d7e7110a500057d7110a5010d7c7110a503ff3e4110a502473c4110a500357e7010a500057d7010a500357c7010a503f67e6010a5018f7a6010a503a73c4010a5023d7f76cca500357e76cca500057d76cca500357c76cca5023d7f74cca502457e74cca5023f3e74cca500053e74cca500057d74cca5023f3d74cca500053d74cca5023d7c74cca5010d7e71cca500057d71cca5010d7c71cca500357e70cca500057d70cca500357c70cca503de7e60cca5017f7a60cca500057f768ca500357e768ca500057d768ca500357c768ca500057f748ca502457e748ca500057d748ca502457c748ca501657d738ca5023d7e728ca500075f328ca5023f6f328ca5010d7e718ca500057d718ca5010d7c718ca503ef5e318ca503ef5c318ca500357e708ca500057d708ca501567e608ca501577a608ca500057f764ca500357e764ca500057d764ca500357c764ca500057f744ca502457e744ca500057d744ca502457c744ca5023f6f324ca500075e324ca500057f714ca5010d7e714ca5010d7c714ca500057f704ca500357c704ca501667e604ca501677a604ca5023d7f760ca500357e760ca5023e7e760ca500347e760ca500057d760ca5023e7d760ca500047d760ca500357c760ca5023d7f740ca502457e740ca500057d740ca5023d7c740ca5023d7e730ca501557e720ca5023f5f320ca5023f6e320ca500075d320ca5023f6d320ca5010d7e710ca500057d710ca5010d7c710ca503e75e310ca5023f5c310ca500357e700ca500057d700ca500357c700ca503de7e600ca5014f7a600ca500357f76586500057f74586502457c74586500367f64586500067d64586500057f735865023d7c73586500367f63586500067d63586500057f72586500057c72586500367f62586500067d62586500357f715865003777615865010e7e61586500367c61586500377461586500357e70586500357c70586500367e60586500377a60586500377610586500377410586502457f76d06500357e76d06500057d76d06500357c76d065010d7e74d06503973f64d06503973c64d065023d7e73d06500057d73d06502473f43d06500073d43d06500057e72d06500057d72d06502473f42d06500073d42d065010d7d71d065010f3e41d065010f7641d065010f3c41d06500357e70d06500057d70d06500357c70d065024e7e60d065013f7a60d06503973c40d06500057f76506500357e76506500057d76506500357c765065010d7f745065031f3f645065031f3c64506500057f735065023d7c73506500073f43506500073d43506500057f72506500057c72506500073f42506500073d425065010d7f715065024777415065010f3e415065010f3c415065010f7441506500057
  | 29 => 0x23f5e6390e500075d6390e5023f3f4390e502475f4390e500057e7290e500057d7290e5010d7e7190e500057d7190e5010d7c7190e500357e7090e500057d7090e500357c7090e503de7e6090e501ef7a6090e500057f7650e500357e7650e500057d7650e500357c7650e500073e6450e500073d6450e500075e6350e500075d6350e502475f4350e5023f3e4350e500057f7250e500057c7250e500057f7150e5010d7e7150e5010d7c7150e500057f7050e500357c7050e501de7e6050e501df7a6050e5023d7f7610e500357e7610e500057d7610e500357c7610e502457e7410e503b73f6410e503b73c6410e5023d7e7310e5023f3f4310e5023f5e4310e5023f3d4310e502475d4310e500057e7210e500057d7210e5010d7e7110e500057d7110e5010d7c7110e500357e7010e500057d7010e500357c7010e503de7e6010e501cf7a6010e503b73c4010e500357d7698a502457e7498a500057d7498a5023d7e7398a500057d7398a500357e7298a500367f6298a500376f6298a500376c6298a5010d7e7198a500057d7198a5010d7c7198a500357e7098a500357c7098a500367e6098a500377a6098a500376e2098a500376c2098a500357f7658a500057f7458a500073f7458a500053f7458a502457c7458a500073c7458a500053c7458a500367f6458a500067d6458a500057f7358a5023d7c7358a500367f6358a500067d6358a500357f7258a500376f6258a500067e6258a500367c6258a500376c6258a500366c6258a500057f7158a5010d7e7158a5010d7c7158a500367f6158a500357e7058a500357c7058a500367e6058a500377a6058a500376e2058a500376c2058a502457f76d0a500357e76d0a500057d76d0a500357c76d0a5023d7e73d0a500057d73d0a5010d7e71d0a500057d71d0a5010d7c71d0a500357e70d0a500057d70d0a500357c70d0a503f67e60d0a501bf7a60d0a500057f7690a500357e7690a500057d7690a500357c7690a501a57d7490a5032f3f6490a5032f3c6490a5023d7e7390a500057d7390a500073f4390a500073d4390a502457e7290a500073f4290a502476f4290a5010d7e7190a500057d7190a5010d7c7190a504073e4190a504073c4190a500357e7090a500057d7090a501967e6090a501977a6090a500057f7650a500357e7650a500057d7650a500357c7650a500057f7350a5023d7c7350a502476f4250a500073e4250a500057f7150a5010d7e7150a5010d7c7150a500057f7050a500357c7050a501a67e6050a501a77a6050a502457f7610a500357e7610a502467e7610a500347e7610a500057d7610a502467d7610a500047d7610a500357c7610a502457e7410a503a73f6410a503a73c6410a5023d7e7310a500057d7310a502473f4310a500073d4310a501957e721
  | 30 => 0xe75d81210057d75d8121006bf64d8121006bc64d8121006df63d8121006dc63d81210077850d8121004ff75d8121014fe75d81210067e75d81210147e75d8121004fd75d81210067d75d81210047d75d8121014fc75d812102cfe74d8121004fd74d8121024fe73d8121004fd73d8121006fb50d81210067c50d8121006f850d81210067850d8121086fa10d8121005be7498121005bd7498121006bf6498121006bc6498121005de7398121005dd7398121006df6398121006dc6398121006fb60981210057f75581211157c7558121005bf7458121005bc7458121006bf6458121006bc6458121005df7358121005dc7358121006df6358121006dc6358121006bf6418121006bc6418121006df6318121006dc6318121006f96018121007785018121034ff7518121014fe7518121004fd7518121034fc751812102cfe7418121004fd7418121024fe7318121004fd7318121006fb50181210367c5018121036f85018121036785018121036fa1018121046f910181210357d76992500357e74992500367f64992500373f64992500373c649925023d7e73992500057d73992500057e72992500057d729925010d7e71992500057d719925010d7c71992500357e70992500357c70992500367e60992500377a60992500373e40992500373c40992500357f76592500357f74592500373f64592502467e64592500367c64592500373c64592500363c64592500057f735925023d7c73592500057f72592500057c72592500367f62592500057f715925010d7e715925010d7c71592500367f61592500357e70592500357c70592500367e60592500377a60592500373e40592500373c40592500357d7698e502457e7498e500057d7498e500357e7398e500367f6398e500375f6398e500375c6398e500057e7298e500057d7298e5010d7e7198e500057d7198e5010d7c7198e500357e7098e500357c7098e500367e6098e500377a6098e500375e3098e500375c3098e500357f7658e500057f7458e500073f7458e500053f7458e502457c7458e500073c7458e500053c7458e500357f7358e500375f6358e5023e7e6358e500367c6358e500375c6358e500365c6358e500057f7258e500057c7258e500367f6258e500057f7158e5010d7e7158e5010d7c7158e500367f6158e500357e7058e500357c7058e500367e6058e500377a6058e500375e3058e500375c3058e502457f76d0e500357e76d0e500057d76d0e500357c76d0e502473e64d0e500073d64d0e500057e72d0e500057d72d0e5010d7e71d0e500057d71d0e5010d7c71d0e500357e70d0e500057d70d0e500357c70d0e503f67e60d0e501ff7a60d0e5023d7f7690e500357e7690e500057d7690e500357c7690e501dd7d7490e503473f6490e503473c6490e5023d7e7390e50
  | 31 => 0x8d21146dc4118d21146df2118d21146de2118d21146dd2118d21146dc2118d21026df7018d21026de7018d21026dd7018d21026dc7018d21006df5018d21006de5018d21006dd5018d21006dc5018d210065c5018d21146df1018d21146de1018d21146dd1018d21146dc1018d2102cff76d0d21004fe76d0d21004fd76d0d2102cfc76d0d21006bf64d0d2102ebc64d0d21006df63d0d21026dc63d0d21024ff7690d21004fe7690d21004fd7690d21024fc7690d21006bf6490d2102ebc6490d21006df6390d21026dc6390d21005ee7290d21005ed7290d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21006bf6450d2102ebc6450d21006df6350d21026dc6350d21024ff7610d21004fe7610d21004fd7610d21024fc7610d21006bf6410d2102ebc6410d21006df6310d21026dc6310d21005ee7210d21005ed7210d2100df67110d21005f57110d2100cfe76d092100cfc76d0921006bf64d092102ebc64d0921006df63d0921006dc63d092100df671d0921005f571d0921184fe76909211aebf649092102ebc6490921006df6390921006dc639092104fe4219092102cff765092100cfe765092119cfd765092100cfc7650921006bf645092102ebc6450921006df6350921006dc6350921005f7715092100df4715092119fe421509211acfe76109211157e75109210057d7510921006bf641092102ebc6410921006df6310921006dc631092100cfe76cc92100cfc76cc921005be74cc921005bd74cc921006bf64cc921006bc64cc921006df63cc921026dc63cc92100df671cc921005f571cc921177e421cc921144fe768c921006bf648c921006bc648c92116edf638c921026dc638c921145ee768c921006ee768c921007af648c921007ac648c92115ded738c92116fcf638c921026ee638c921026ec638c921007cc638c921026cc638c92100dee718c92100dec718c92104eef618c92116fce318c92116fcc318c92141f6c508c921024ff764c92100cfe764c92115cfd764c92100cfc764c921006bf644c921006bc644c921006df634c921026dc634c921005f7714c92100df4714c92100dec764c921026ec764c92100cec764c921007af644c921007ac644c921007cf734c921007cf634c921026ee634c921026ec634c921007cc634c921007e7714c92100dee714c92100dec714c92115fe4714c92100de4714c92115eef614c92115fcf314c92115fcd314c9214176c504c92116cfe760c9211157e750c9210057d750c921006bf640c921006bc640c921006df630c921026dc630c92116dee720c921007cd320c92104fe4210c921007b764c8521007b464c8521007d763c8521007d463c852100df672c852100fe672c852100ef762c852100fe762c852104fe632c8521007e532c852140f7450c85211157
  | 32 => 0x4ff75d8d21014fe75d8d21004fd75d8d21014fc75d8d2102cfe74d8d21004fd74d8d21006df53d8d21006de53d8d21006dd53d8d21006dc53d8d2104cff71d8d2116cfd71d8d2116edf31d8d2116edd31d8d21034fe70d8d21004fd70d8d210067c50d8d21024de76d8d21006df65d8d21006de65d8d21006dd65d8d21006dc65d8d21006df64d8d210079f64d8d210069f64d8d21006de64d8d21006dd64d8d21006dc64d8d210079c64d8d210069c64d8d2116fcf72d8d2116fce21d8d2116fcc21d8d2116fd421d8d210075c50d8d21006df75d8d21006de75d8d21006dd75d8d21006dc75d8d21006df74d8d21006de74d8d21006dd74d8d21006dc74d8d21006df54d8d21006de54d8d21006dd54d8d21006dc54d8d2116edf72d8d2116edd72d8d21006df52d8d21006de52d8d21006dd52d8d21006dc52d8d2116edf71d8d2116ede71d8d2116edd71d8d2116edc71d8d2116edf51d8d2116ede51d8d2116edd51d8d2116edc51d8d2116edf41d8d2116ede41d8d2116edd41d8d2116edc41d8d2116edf21d8d2116ede21d8d2116edc21d8d21006df70d8d21006de70d8d21006dd70d8d21006dc70d8d21006df50d8d21006de50d8d21006dd50d8d21006dc50d8d210065c50d8d2116edf10d8d2116ede10d8d2116edd10d8d2116edc10d8d21005be7498d21005bd7498d21006bf6498d21006bc6498d21006df6398d2115ded7298d21005bf7458d21005bc7458d21006bf6458d21006bc6458d21175ef7258d21004ff7558d21014fe7558d21004fd7558d21014fc7558d21004ff7458d21006bf7458d21004bf7458d2102cfc7458d21006bc7458d2102cbc7458d21006df7358d21174ff7258d21006ef7258d2115cff7158d21006f77158d21004ff7058d21034fc7058d210067c5058d2116cfe7618d211157e7518d210057d7518d21006bf6418d21006bc6418d21026de6318d21006dd6318d2116dde7618d21006de7618d2116cde7618d210075e7518d210075d7518d21006df6518d21006de6518d21006dd6518d21006dc6518d21006df6418d210079f6418d210069f6418d21006de6418d21006dd6418d21006dc6418d210079c6418d210069c6418d21147cd7218d21147ce2118d21147cc2118d21147d42118d210075c5018d21026df7518d21026de7518d210265e7518d21026dd7518d210265d7518d21026dc7518d21026df7418d21026de7418d21026dd7418d21026dc7418d21006df5418d21006de5418d21006dd5418d21006dc5418d21026df7218d21026dd7218d21026cd7218d21006df5218d21006de5218d21006dd5218d21006dc5218d21026df7118d21026de7118d21026dd7118d21026dc7118d21146df5118d21146de5118d21146dd5118d21146dc5118d21146df4118d21146de4118d21146dd411
  | 33 => 0xb205832104ef8205832106efa105832102cfe76d9121004ff75d9121014fe75d9121004fd75d9121014fc75d9121006bf54d9121006be54d9121006bd54d9121006bc54d9121024fe73d9121004fd73d912104cff71d91211acfd71d91211aebf41d91211aebd41d9121034fe70d9121004fd70d91210067c50d912102cbe76d9121006bf65d9121006be65d9121006bd65d9121006bc65d91211afae21d91211afac21d91211afb421d91210073c50d9121006bf75d9121006be75d9121006bd75d9121006bc75d9121006bf73d9121006be73d9121006bd73d9121006bc73d9121006bf53d9121006be53d9121006bd53d9121006bc53d91211aebf72d91211aebd72d9121006bf52d9121006be52d9121006bd52d9121006bc52d91211aebf71d91211aebe71d91211aebd71d91211aebc71d91211aebf51d91211aebe51d91211aebd51d91211aebc51d91211aebf31d91211aebe31d91211aebd31d91211aebc31d91211aebf21d91211aebe21d91211aebc21d9121006bf70d9121006be70d9121006bd70d9121006bc70d9121006bf50d9121006be50d9121006bd50d9121006bc50d91210063c50d91211aebf10d91211aebe10d91211aebd10d91211aebc10d9121006bf6499121005de7399121005dd739912119ded7299121005df7359121005dc73591211b5ef7259121004ff7559121014fe7559121004fd7559121014fc7559121006bf7459121004ff7359121006df7359121004df7359121024fc7359121006dc7359121024dc73591211b4ff7259121006ef725912119cff7159121006f77159121004ff7059121034fc70591210067c50591211acfe76191211157e75191210057d751912102ebe6419121006bd64191211adbe7619121006be76191211acbe76191210073e75191210073d7519121006bf6519121006be6519121006bd6519121006bc6519121187ae2119121187ac2119121187b421191210073c501912102ebf751912102ebe751912102e3e751912102ebd751912102e3d751912102ebc751912102ebf731912102ebe731912102ebd731912102ebc7319121006bf5319121006be5319121006bd5319121006bc531912102ebf721912102ebd7219121006bf5219121006be5219121006bd5219121006bc521912102ebf711912102ebe711912102ebd711912102ebc7119121186bf5119121186be5119121186bd5119121186bc5119121186bf3119121186be3119121186bd3119121186bc3119121186bf2119121186be2119121186bd2119121186bc211912102ebf701912102ebe701912102ebd701912102ebc7019121006bf5019121006be5019121006bd5019121006bc50191210063c5019121186bf1019121186be1019121186bd1019121186bc1019121024fe76d8d21006bf64d8d21006bc64d8d21
  | 34 => 0x932104eee72d932104ef571d93211aebe41d93211aebc41d9321034fe70d9321004fd70d93210067c50d932119cfd769932104ebf649932104ebc649932102cff765932104ebc6459321004ff7559321014fe7559321004fd7559321014fc755932104ebf7459321004ff7359321024fc735932100cfe725932100cfc725932104ebe425932104ebc425932119ebf415932119ebd4159321004ff7059321034fc70593210067c505932104cff75d8f21014fe75d8f21004fd75d8f2104cfc75d8f2102cfe74d8f21004fd74d8f2104cfe72d8f2104eee72d8f2104ef571d8f2116ede31d8f2116edc31d8f21034fe70d8f21004fd70d8f210067c50d8f2115cfd7698f21005be7498f21005bd7498f2104edf6398f2104edc6398f21024ff7658f2104edc6358f21004ff7558f21014fe7558f21004fd7558f21014fc7558f21004ff7458f2102cfc7458f2104edf7358f2100cfe7258f2100cfc7258f2104ede3258f2104edc3258f2115edf3158f2115edd3158f21004ff7058f21034fc7058f210067c5058f2102cff76d0f2104cfe76d0f21004fd76d0f2104cfc76d0f21006bf64d0f2102ebc64d0f21024ff7690f2104cfe7690f21004fd7690f2104cfc7690f2104dee7290f21005ed7290f21004ff7650f2104cfe7650f21004fd7650f2104cfc7650f21006bf6450f2102ebc6450f21005f77150f2100df47150f21024ff7610f2104cfe7610f21004fd7610f2104cfc7610f2104dee7210f21005ed7210f2119cfd76d0b2104ebf64d0b2104ebc64d0b211b4ff7650b2104ebf6450b2104ebc6450b2115cfd76ccb21005be74ccb21005bd74ccb2104edf63ccb2104edc63ccb2100ded768cb2104eed768cb2100ced768cb21026ee638cb2104fce638cb2104fcd638cb2104eec638cb2100dee718cb2104fe6718cb2104fe5718cb2100dec718cb2116fce318cb2116fcc318cb2142f6c508cb21174ff764cb2104edf634cb2104edc634cb2104fcc324cb21175ef764cb21006ef764cb2104fcf734cb2104fcf634cb21026ee634cb21026ec634cb2104fcc634cb2100dee714cb2100dec714cb2115fcf314cb2115fcd314cb214276c504cb2104efb6098321034ff7598321014fe7598321004fd7598321034fc759832102cfe7498321004fd7498321024fe7398321004fd739832100cfe72983210367c509832104efb2098321036f82098321036fa109832107ef910983210057f755832111d7c7558321005bf7458321005bc745832104ef86058321004ff75583210067f75583210047f7558321014fe7558321004fd7558321014fc75583210067c75583210147c7558321004ff7458321006bf7458321004bf745832102cfc7458321006bc745832102cbc7458321004ff7358321024fc735832100cfc72583210067c505832104ef
  | 35 => 0x1e4fe761913102ebe6419131006bd641913100cfe76d0d3100cfc76d0d31006bf64d0d3102ebc64d0d3100df671d0d31005f571d0d3102cff7650d3100cfe7650d311d4fd7650d3100cfc7650d31006bf6450d3102ebc6450d31005f77150d3100df47150d31004ff75d8931014fe75d8931004fd75d8931014fc75d893102cfe74d8931004fd74d8931006ee52d8931006ed52d8931024fd71d8931176ef21d8931034fe70d8931004fd70d89310067c50d8931006ef6298931005bf7458931005bc74589311257e75189310057d7518931006ed621893104cff7518931014fe751893104e7e75189310147e7518931004fd751893104e7d75189310047d751893104cfc751893102cfe7418931004fd741893104edd731893104eee5218931006ed521893104cff7118931024fd7118931146de3118931146dc311893104eef2118931146ed2118931034fe7018931004fd70189310067c5018931004fe76d0931004fd76d093102cfc76d0931006ef62d0931006ec62d0931004fe7690931004fd769093104cfc7690931006bf649093102ebc6490931025de7390931005dd7390931004ff7650931004fe7650931004fc7650931004fe7610931004fd761093104cfc76109311257e75109310057d7510931006bf641093102ebc6410931025de7310931005dd7310931006ef621093104eec621093100df67110931005f57110931145de76cc931026de76cc931144de76cc9310279e74cc9310279d74cc93104edc62cc93100dde71cc93100ddc71cc931026df61cc931027d761cc93143f5c50cc93100cfe768c93115ddd738c93116edf638c931006ef628c93104eec628c93100df6718c931005f5718c93100cfc764c931006ef624c931006ec624c931027cc324c931005f7714c93100df4714c93100ddc764c93115edc764c93100cdc764c931025df724c931027cf724c931007cf624c93104edc624c931007cc624c931007d7714c93100dde714c93100ddc714c93115fd4714c931026df614c931027d7614c9314375c504c9311257e75d81310057d75d8131004ff75d8131014fe75d81310067e75d81310147e75d8131004fd75d81310067d75d81310047d75d8131014fc75d813102cfe74d8131004fd74d813104cfe72d8131004fd72d8131024fd71d81310067c50d81310befa10d8131006fb60981310057f75581311257c7558131005bf7458131005bc7458131005ef7258131005ec7258131006f96018131034ff7518131014fe7518131004fd7518131034fc751813102cfe7418131004fd741813104cfe7218131004fd7218131024fd71181310367c5018131036fa101813108ef9101813104cff75d9321014fe75d9321004fd75d932104cfc75d9321006be54d9321006bd54d9321024fe73d9321004fd73d932104cfe72d
  | 36 => 0xc7518141024fe7318141004fd731814104cfe7218141004fd721814102cfd71181410367c5018141036fa10181410cef91018141004ff7559331014fe7559331004fd7559331014fc7559331026bf745933100cfe735933100cfc7359331026be4359331026bc4359331004ff725933104cfc72593311d6bf41593311d6bd4159331004ff7059331034fc70593310067c505933104cff7598b31014fe7598b31004fd7598b3104cfc7598b3102cfe7498b31004fd7498b3100cfe7398b3104ede7398b3100cde7398b3100cfc7398b3104eee7298b3104edf3298b31026ef3298b3104eec3298b3116ede3198b31026dc3198b3104eef2198b3116eed2198b31034fe7098b31004fd7098b310067c5098b31004ff7558b31014fe7558b31004fd7558b31014fc7558b31004ff7458b3102cfc7458b3100cfc7358b31026ef7258b31026ef3258b31026ec3258b3115eef2158b31004ff7058b31034fc7058b310067c5058b3102cff76d0b31024fe76d0b31004fd76d0b3104cff7690b31024fe7690b31004fd7690b3102ebe6490b31006bd6490b31025de7390b31005dd7390b31004ff7650b31004fd7650b31024fc7650b31005f77150b3100df47150b3104cff7610b31024fe7610b31004fd7610b3112d7e7510b310057d7510b3102ebe6410b31006bd6410b31025de7310b31005dd7310b31025df764cb31006df764cb3116cdf764cb31027cf724cb31027cf624cb3104ede624cb31027cc624cb3100dde714cb3100ddc714cb314475c504cb31034ff7598331014fe7598331004fd7598331034fc759833102cfe7498331004fd749833100cfe7398331034fc739833104cfe7298331004fd7298331036fa70983310367c5098331026fb3098331036f83098331036fa10983310b6f91098331004ff75583310067f75583310047f7558331014fe7558331004fd7558331014fc75583310067c75583310147c7558331004ff7458331006bf7458331004bf745833102cfc7458331006bc745833102cbc745833100cfc7358331004ff725833104cfc7258331026fb70583310067c5058331026fb3058331026f830583310a6fa105833102cfe76d9131004ff75d9131014fe75d9131004fd75d9131014fc75d9131006be54d9131006bd54d913104cfe72d9131004fd72d9131024ff71d9131024fd71d91311e6bf41d91311e6bd41d9131034fe70d9131004fd70d91310067c50d9131006bf64991311d5dd73991311f5df7359131005ef7259131005ec7259131004ff7559131014fe7559131004fd7559131014fc7559131006bf74591311f4ff7359131006df7359131004ff7259131006ef7259131004ef725913104cfc7259131006ec7259131004ec72591311d4ff7159131006f77159131004ff7059131034fc70591310067c5059131
  | 37 => 0xd4102dbf7350d4102f9f7350d410079f6350d41026be6350d41026bc6350d410079c6350d410269c6350d41005bf7250d41007b77150d4100dbe7150d4100dbc7150d411d7b47150d4102ebf6150d4102fb76150d41005bc7050d4146f3c5050d41004ff75d8941014fe75d8941004fd75d8941014fc75d8941024fe73d8941004fd73d8941006ee52d8941006ed52d894102cfd71d89411b6ef21d8941034fe70d8941004fd70d89410067c50d8941006ef6298941005df7358941005dc73589411357e75189410057d7518941006ed621894104cff7518941014fe751894104e7e75189410147e7518941004fd751894104e7d75189410047d751894104cfc751894104ebd7418941006be5418941006bd5418941024fe7318941004fd7318941006bf4318941006bd431894104eee5218941006ed521894104cff711894102cfd7118941186be4118941186bc411894104eef2118941186ed2118941034fe7018941004fd70189410067c5018941185be76d094102ebe76d0941184be76d094102dbf75d0941465bd75d0941005bd73d094104ebc62d094100dbe71d094100dbc71d094102ebf61d094102fb761d0941005be70d094145f3c50d094100cfe769094119dbd74909411aebf6490941006ef629094104eec629094100df67190941005f5719094100cfc7650941006ef6250941006ec6250941005f7715094100df4715094100dbc765094119ebc765094100cbc7650941455bf7550941455bd7550941005bf735094102dbf725094102faf7250941007af625094104ebc6250941007ac6250941007b7715094100dbe715094100dbc715094119fb4715094102ebf615094102fb76150941005bc705094144f3c5050941004fe76cc941004fd76cc941024fc76cc94102dbe74cc941005bd74cc941006ef62cc941006ec62cc941004fe768c941004fd768c94104cfc768c94102dbe748c941005bd748c941006df638c941026dc638c941004ff764c941004fe764c941004fc764c94102dbe744c941005bd744c941004fe760c941004fd760c94104cfc760c9411357e750c9410057d750c94102dbe740c941005bd740c941006df630c941026dc630c941006ef620c94104eec620c94100df6710c941005f5710c9411357e75d81410057d75d8141004ff75d8141014fe75d81410067e75d81410147e75d8141004fd75d81410067d75d81410047d75d8141014fc75d81410febd74d8141006be54d8141006bd54d8141024fe73d8141004fd73d8141006bf43d8141006bd43d814104cfe72d8141004fd72d814102cfd71d81410067c50d81410fefa10d8141006fb60981410057f75581411357c7558141005df7358141005dc7358141005ef7258141005ec7258141006f96018141034ff7518141014fe7518141004fd7518141034f
  | 38 => 0x5bc7050f4149f3c5050f4104cff7598b41014fe7598b41004fd7598b4104cfc7598b4100cfe7498b4104ebe7498b4100cbe7498b4100cfc7498b4102ebe5498b41006bd5498b41024fe7398b41004fd7398b4102ebf4398b41006bd4398b4104eee7298b4104ebf4298b4102eef4298b4104eec4298b411aebe4198b4102ebc4198b4104eef2198b411aeed2198b41034fe7098b41004fd7098b410067c5098b4102ebc4098b41004ff7558b41014fe7558b41004fd7558b41014fc7558b4100cfc7458b41004ff7358b41024fc7358b4102eef7258b4102eef4258b4102eec4258b4119eef2158b41004ff7058b41034fc7058b410067c5058b4102dbf7650b41006bf7650b411acbf7650b41495bf7550b41495bd7550b41005bf7350b4102faf7250b4104ebe6250b4100dbe7150b4100dbc7150b41005bc7050b4148f3c5050b41024ff76ccb4102cfe76ccb41004fd76ccb4102dbe74ccb41005bd74ccb4104cff768cb4102cfe768cb41004fd768cb4102dbe748cb41005bd748cb41026de638cb41006dd638cb41004ff764cb41004fd764cb4102cfc764cb4102dbe744cb41005bd744cb41005f7714cb4100df4714cb4104cff760cb4102cfe760cb41004fd760cb4113d7e750cb410057d750cb4102dbe740cb41005bd740cb41026de630cb41006dd630cb41034ff7598341014fe7598341004fd7598341034fc759834100cfe7498341034fc7498341024fe7398341004fd739834104cfe7298341004fd7298341036fa70983410367c509834102efb4098341036f84098341036fa10983410f6f91098341004ff75583410067f75583410047f7558341014fe7558341004fd7558341014fc75583410067c75583410147c755834100cfc745834102ebc745834100cbc745834102ebe5458341006bd5458341004ff7358341024fc735834102ebf4358341006bd4358341004ff725834104cfc725834102efb70583410067c505834102efb405834102ebc405834102ef840583410e6fa1058341024fe76d8d41004ff75d8d41014fe75d8d41004fd75d8d41014fc75d8d41006de53d8d41006dd53d8d4104cfe72d8d41004fd72d8d4102cfd71d8d411f6df31d8d41034fe70d8d41004fd70d8d410067c50d8d41006df6398d41005ef7258d41005ec7258d41026de6318d41006dd6318d411c5be76d0d4102ebe76d0d4102dbf75d0d41485bd75d0d41026be63d0d41026bc63d0d41005bd72d0d4100dbe71d0d4100dbc71d0d4102ebf61d0d4102fb761d0d41005be70d0d4147f3c50d0d4100cfe7690d411d5bd7490d41006df6390d41026dc6390d4100df67190d41005f57190d4100cfc7650d41006df6350d41026dc6350d41005f77150d4100df47150d4100dbc7650d41026bc7650d4100cbc7650d41475bf7550d41475bd755
  | 39 => 0xd73594320267c73594320267f43594320267e43594320267d43594320267c435943214e7f725943204e7e725943214e7d725943204e7c725943204e7e425943204e7c42594320267f325943204e7e32594320267d325943204e7c32594320067f71594320067e71594320067d71594320067c71594320067e41594320067c41594320267f31594320267e31594320267d31594320267c315943204e7f21594320067e215943204e7c21594320067f70594320067e70594320067d70594320067c70594320347c70594320267f30594320267e30594320267d30594320267c305943204e7f205943204e7c20594320067f10594320067c1059432004ff7559032014fe7559032004fd7559032014fc755903204cff745903204ebf7459032024fe7359032024fc7359032026be4359032026bc435903204cfe725903204cfc725903204ebe425903204ebc4259032004ff715903200cfe715903200cfc7159032004ff7059032034fc70590320067c5059032004fd76d08321be7e65d08320067d65d0832004ff76508321a67e65508320067d655083204ddf764c832006df764c832004df764c83204f5e654c83204f5d654c83204ddf724c832027cf724c83204ede624c83204fce624c83204fce524c8324afcd524c832007cf424c83204fcc424c832145de714c832145dc714c8324af5c504c832004ff7558432014fe7558432004fd7558432014fc7558432004ff745843202cfc7458432026df3258432026ee3258432006dd3258432026ed325843204ef77158432146f64158432026f73158432146de3158432026dc3158432026f4315843204ef7215843204ef42158432004ff7058432034fc70584320067c5058432146f71058432034ff75980320367f7598032014fe7598032004fd7598032034fc75980320367c75980320347c759803202cfe7498032004fd749803200cfe7198032004fd7198032034fc7198032036fa70980320367c5098032026fb3098032036f8309803204efb2098032036f82098032004ff75580320067f75580320047f7558032014fe7558032004fd7558032014fc75580320067c75580320147c7558032004ff7458032006bf7458032004bf745803202cfc7458032006bc745803202cbc7458032004ff715803200cfe715803200cfc715803204efb70580320067c5058032026fb3058032026f8305803204efb205803204ef82058032004ff7558f41014fe7558f41004fd7558f41014fc7558f4100cfc7458f4102edf7358f4102edf4358f4102edc4358f41004ff7258f4104cfc7258f411d6df3158f41004ff7058f41034fc7058f410067c5058f4102dbf7650f41006bf7650f414a5bf7550f414a5bd7550f4102f9f7350f41026be6350f41026bc6350f41005bf7250f4100dbe7150f4100dbc7150f41
  | 40 => 0x823200cfe7198232004fd7198232034fc71982320367c509823204efb2098232036f820982320057f75582321557c755823204ef86058232004ff75582320067f75582320047f7558232014fe7558232004fd7558232014fc75582320067c75582320147c7558232004ff745823202cfc745823204cfc7258232004ff715823200cfe715823200cfc71582320067c505823204efb205823204ef8205823202cfe76d9132004ff75d9132014fe75d9132004fd75d9132014fc75d9132006be54d9132006bd54d913200cfe71d9132004fd71d913200cfc71d9132006be41d9132006bc41d9132034fe70d9132004fd70d91320067c50d9132006bf6499132005f7715913215df47159132004ff7559132014fe7559132004fd7559132014fc7559132006bf7459132004ff7359132006df7359132004ff7259132006ef7259132004ff7159132006f77159132004f7715913200cfe715913200cfc7159132006f4715913200cf47159132004ff7059132034fc70591320067c5059132004fe761913202ebe6419132006bd6419132004fe76d0d3204cfc76d0d32006bf64d0d3202ebc64d0d32005ee72d0d32005ed72d0d32027cc32d0d3202cfc7650d32006bf6450d3202ebc6450d320279c4350d32005ef7250d32005ec7250d32024fe76d0932024fc76d0932006bf64d093202ebc64d0932025de73d0932005dd73d0932004fe769093202ebe6490932006bd649093202cff7650932004fd7650932024fc7650932006bf645093202ebc6450932005df7350932025dc7350932004fe76109321657e75109320057d751093202ebe6410932006bd6410932025ee728c932026ef628c93204dde728c93204edf628c932027cf628c932005dd718c93216ede618c93216edc618c9324b75c508c93200cfe76d853215ef661d8532004ff75d8532014fe75d8532004fd75d8532014fc75d853202cfe74d8532004fd74d8532024fd72d853215ef651d8532006f551d853215ef441d853215ef631d853215ef621d8532034fe70d8532004fd70d85320067c50d853215ef410d8532005bf7458532005bc745853215ef461585321657e75d81320057d75d8132004ff75d8132014fe75d81320067e75d81320147e75d8132004fd75d81320067d75d81320047d75d8132014fc75d813202cfe74d8132004fd74d813200cfe71d8132004fd71d813200cfc71d81320067c50d8132006fb60981320057f75581321657c7558132005bf7458132005bc7458132005f7715813215df47158132006f96018132034ff7518132014fe7518132004fd7518132034fc751813202cfe7418132004fd741813200cfe7118132004fd7118132034fc71181320367c50181320067f74594320067e74594320067d74594320067c74594320267f73594320267e73594320267
  | 41 => 0x6bf5159332006be5159332006bd5159332006bc5159332026bf3159332026be3159332026bd3159332026bc3159332006be2159332006bc2159332006bf7059332006be7059332006bd7059332006bc7059332006bf5059332006be5059332006bd5059332006bc50593320063c5059332026bf3059332026be3059332026bd3059332026bc3059332006bf1059332006bc105933202ebe64d0b32006bd64d0b32025de73d0b32005dd73d0b3202ebe6490b32006bd6490b3202cff7650b3202ebe6450b32006bd6450b32005df7350b32025dc7350b3217d7e7510b320057d7510b3202ebe6410b32006bd6410b32004ff7558732014fe7558732004fd7558732014fc7558732004ff745873202cfc7458732026ee3258732026ed3258732026f77158732026f73158732026f43158732176f62158732004ff7058732034fc70587320067c5058732034ff7598332014fe7598332004fd7598332034fc759833202cfe7498332004fd749833200cfe7198332004fd7198332034fc7198332036fa7098332006fb50983320367c5098332036f85098332036785098332026fb3098332036f83098332004ff75583320067f75583320047f7558332014fe7558332004fd7558332014fc75583320067c75583320147c7558332004ff745833202cfc7458332004ff715833200cfe715833200cfc7158332026fb7058332006fb50583320067c5058332006f85058332006785058332026fb3058332026f8305833204cff75d9232014fe75d9232004fd75d923204cfc75d923204edd73d923204eee72d923200cfe71d9232004fd71d923200cfc71d9232034fe70d9232004fd70d92320067c50d9232004fd769923204ebf649923204ebc649923202cff765923204ebc6459232004ff7559232014fe7559232004fd7559232014fc755923204ebf7459232006be5459232006bd545923204cfc725923204ebe425923204ebc4259232004ff715923200cfe715923200cfc7159232004ff7059232034fc70592320067c505923202ebe64d0e32006bd64d0e3204dee72d0e32005ed72d0e3202cff7650e3202ebe6450e32006bd6450e32005ef7250e3204dec7250e3204ddd76cca32026dd76cca320279e74cca320279d74cca3204fce62cca3204fce52cca324bfcd52cca3216dde71cca32025dc71cca324bf5c50cca3200cff7658632025dc735863204ef4615863216fd63158632004ff7558632014fe7558632004fd7558632014fc7558632004ff745863202cfc745863204cfc7258632006df325863216ede315863216ef6315863216edc315863204ef7215863204ef42158632004ff7058632034fc70586320067c505863204efb6098232034ff7598232014fe7598232004fd7598232034fc759823202cfe7498232004fd749823204cfe729
  | 42 => 0xe52508424c7ad5250842185be7150842185bc7150842005bc70508424c73c5050842004ff7558442014fe7558442004fd7558442014fc755844202ebe5458442006bd5458442004ff7358442024fc735844202ebf4358442006bd435844202ebf4258442006bd425844204ef7715844202ef74158442186be415844202ebc415844202ef44158442186f6315844204ef7215844204ef42158442004ff7058442034fc70584420067c505844202ebc4058442186f71058442034ff75980420367f7598042014fe7598042004fd7598042034fc75980420367c75980420347c7598042024fe7398042004fd739804200cfe7198042004fd7198042034fc7198042036fa70980420367c509804202efb4098042036f8409804204efb2098042036f82098042004ff75580420067f75580420047f7558042014fe7558042004fd7558042014fc75580420067c75580420147c755804202ebe5458042006bd5458042004ff7358042024fc735804202ebf4358042006bd4358042004ff715804200cfe715804200cfc715804204efb70580420067c505804202efb405804202ebc405804202ef8405804202eb8405804204efb205804204ef8205804202ebf759933202ebe759933202ebd759933202ebc7599332026bf7399332026be7399332026bd7399332026bc7399332026bf5399332026be5399332026bd5399332026bc539933202ebf729933202ebd7299332006bf5299332006be5299332006bd5299332006bc5299332026bf3299332026be3299332026bd3299332026bc329933202ebf719933202ebe719933202ebd719933202ebc7199332006bf5199332006be5199332006bd5199332006bc5199332026bf3199332026be3199332026bd3199332026bc3199332006be2199332006bc219933202ebf709933202ebe709933202ebd709933202ebc7099332006bf5099332006be5099332006bd5099332006bc50993320063c5099332026bf3099332026be3099332026bd3099332026bc3099332006bf1099332006bc1099332004ff7559332014fe7559332004fd7559332014fc7559332026bf7459332006bf5459332006be5459332006bd5459332006bc5459332024fc7359332026be4359332026bc4359332004ff715933200cfe715933200cfc7159332006be4159332006bc4159332004ff7059332034fc70593320067c5059332006bf7559332006be7559332006bd7559332006bc7559332026bf7359332026be7359332026bd7359332026bc7359332026bf5359332026be5359332026bd5359332026bc5359332006bf7259332006bd7259332006bf5259332006be5259332006bd5259332006bc5259332026bf3259332026be3259332026bd3259332026bc3259332006bf7159332006be7159332006bd7159332006bc7159332
  | 43 => 0xd42026dc6390d42005ee7290d42005ed7290d42024fc7650d42006df6350d42026dc6350d4202f9c4350d42005ef7250d42005ec7250d4202dee729094202eef62909424eebf65909424eebd6590942006bf639094204dbe729094204ebf629094202faf6290942005bd71909421aebe61909421aebc61909424ef3c509094200cfe76d854219ef661d8542004ff75d8542014fe75d8542004fd75d8542014fc75d8542024fe73d8542004fd73d854202cfd72d854219ef641d854219ef431d854219ef621d8542034fe70d8542004fd70d85420067c50d8542005df7358542005dc735854219ef461585421a57e75d81420057d75d81420077850d8142004ff75d8142014fe75d81420067e75d81420147e75d8142004fd75d81420067d75d81420047d75d8142014fc75d8142024fe73d8142004fd73d814200cfe71d8142004fd71d814200cfc71d8142006fb50d81420067c50d8142006f850d81420067850d8142006fb60981420057f75581421a57c7558142006f96018142007785018142034ff7518142014fe7518142004fd7518142034fc7518142024fe7318142004fd7318142006be421814200cfe7118142004fd7118142034fc7118142006fb50181420367c5018142036f8501814203678501814202e7f745944202e7e745944202e7d745944202e7c74594420067f73594420067e73594420067d73594420067c735944202e7f435944202e7e435944202e7d435944202e7c435944218e7f725944204e7e725944218e7d725944204e7c725944202e7f425944204e7e425944202e7d425944204e7c425944204e7e325944204e7c32594420067f71594420067e71594420067d71594420067c715944202e7f415944202e7e415944202e7d415944202e7c41594420067e31594420067c315944204e7f21594420067e215944204e7c21594420067f70594420067e70594420067d70594420067c70594420347c705944202e7f405944202e7e405944202e7d405944202e7c405944204e7f205944204e7c20594420067f10594420067c1059442004ff7558c42014fe7558c42004fd7558c42014fc7558c4204edf7358c4202edf4358c4202edc4358c4204ede3258c4204edc3258c42004ff7158c4200cfe7158c4200cfc7158c42004ff7058c42034fc7058c420067c5058c4202dbf7650c42006bf7650c424e5bf7550c424e5bd7550c4202f3e6550c4202f3d6550c4202dbf7350c4202f9f7350c42026be6350c42026bc6350c42005bf7250c424debe6250c4202fae6250c42185be7150c42185bc7150c42005bc7050c424d73c5050c4204dbf7650842006bf7650842004bf76508424cdbf75508424cdbd755084204f3e655084204f3d6550842005bf735084204dbf725084202faf725084204ebe625084204fae625084204fa
  | 44 => 0x2ebf4198342036fa70983420367c509834202efb4098342036f84098342004ff75583420067f75583420047f7558342014fe7558342004fd7558342014fc75583420067c75583420147c7558342004ff7358342024fc7358342004ff715834200cfe715834200cfc715834202efb70583420067c505834202efb405834202ef8405834204edf6398e4204edc6398e4204edc6358e42004ff7558e42014fe7558e42004fd7558e42014fc7558e42006de5358e42006dd5358e4204cfc7258e4204ede3258e4204edc3258e42004ff7158e4200cfe7158e4200cfc7158e42004ff7058e42034fc7058e420067c5058e42005bd76d0e4202ebd76d0e4202dbf75d0e42515bd75d0e42026be63d0e42026bc63d0e42005bd72d0e4202fae62d0e421adbe71d0e4202dbc71d0e42005be70d0e4250f3c50d0e42026de6390e42006dd6390e4204dee7290e42005ed7290e42024ff7650e42026de6350e42006dd6350e42005ef7250e4204dec7250e42024bf7650e42505bf7550e42505bd7550e4202dbf7350e4202f9f7350e42026be6350e420079e6350e420269e6350e420079d6350e42026bc6350e42005bf7250e42007af7250e42007ac7250e4202ebe6250e421adbe7150e421adbc7150e42005bc7050e424df3c5050e4204dbd76d0a4202ebd76d0a4202dbf75d0a424fdbd75d0a42005bd73d0a4204fae62d0a4204fae52d0a424f7ad52d0a421adbe71d0a4202dbc71d0a42005be70d0a424f73c50d0a4200cff765864202dbc745864204ef461586421afb64158642004ff7558642014fe7558642004fd7558642014fc7558642006be5458642006bd5458642004ff7358642024fc7358642006bf4358642006bd435864204cfc7258642006bf42586421aebe41586421aef641586421aebc415864204ef7215864204ef42158642004ff7058642034fc70586420067c505864204efb6098242034ff7598242014fe7598242004fd7598242034fc7598242024fe7398242004fd739824204cfe729824200cfe7198242004fd7198242034fc71982420367c509824204efb2098242036f820982420057f75582421957c755824204ef86058242004ff75582420067f75582420047f7558242014fe7558242004fd7558242014fc75582420067c75582420147c7558242006be5458242006bd5458242004ff7358242024fc7358242006bf4358242006bd435824204cfc7258242004ff715824200cfe715824200cfc71582420067c505824204efb205824204ef82058242004ff75d8d42014fe75d8d42004fd75d8d42014fc75d8d4200cfe71d8d42004fd71d8d4200cfc71d8d42006de31d8d42006dc31d8d42034fe70d8d42004fd70d8d420067c50d8d42006df6398d42005f77158d4219df47158d42026de6318d42006dd6318d42006df639
  | 45 => 0xc71d8143006fb50d81430067c50d8143006f850d81430067850d8143006fb60981430057f75581431dd7c7558143006f96018143007785018143034ff7518143014fe7518143004fd7518143034fc75181432e6be43181432e6bc431814304cfe7218143004fd721814300cfe7118143004fd7118143034fc7118143006fb50181430367c5018143036f8501814303678501814304cff7598843014fe7598843004fd759884304cfc759884302ebe5498843006bd5498843026bf4398843026bd439884304cfe729884304eee729884302eef429884304eec4298843026ef329884304eec329884300cfe7198843004fd719884300cfc7198843034fe7098843004fd70988430067c509884302ebc4098843004ff7558843014fe7558843004fd7558843014fc7558843026ef725884302eef425884302eec4258843026ef3258843026ec3258843004ff715884300cfe715884300cfc7158843004ff7058843034fc70588430067c5058843004ff7558443014fe7558443004fd7558443014fc755844302ebe5458443006bd5458443026bf4358443026bd4358443004ff725844304cfc7258443024ff7158443026f7715844302ef7415844302ef44158443026f73158443026f431584431c6f62158443004ff7058443034fc70584430067c505844302ebc4058443034ff7598043014fe7598043004fd7598043034fc759804304cfe7298043004fd729804300cfe7198043004fd7198043034fc7198043034fe7098043036fa7098043006fb50980430367c5098043036f8509804303678509804302efb4098043036f84098043026fb3098043036f83098043004ff75580430067f75580430047f7558043014fe7558043004fd7558043014fc75580430067c75580430147c755804302ebe5458043006bd5458043026bf4358043026de4358043026bd435804302edd4358043004ff725804304cfc7258043004ff715804300cfe715804300cfc7158043026fb7058043006fb50580430067c5058043006f8505804300678505804302efb405804302ebc405804302ef8405804302eb84058043026fb3058043026f83058043004ff7558f42014fe7558f42004fd7558f42014fc7558f4202edf7358f4202edf4358f4202edc4358f4202ebc4258f42004ff7158f4200cfe7158f4200cfc7158f4202ebf4158f42006de3158f42006dc3158f42004ff7058f42034fc7058f420067c5058f42004ff7558742014fe7558742004fd7558742014fc7558742004ff7358742024fc735874202ef7715874202ef7415874202ef441587421b6f62158742004ff7058742034fc70587420067c5058742034ff7598342014fe7598342004fd7598342034fc7598342024fe7398342004fd739834202ebc429834200cfe7198342004fd7198342034fc7198342
  | 46 => 0x834302edd4358343004ff725834304cfc7258343004ff715834300cfe715834300cfc715834302efb70583430067c505834302efb405834302ef8405834304cff7598a43014fe7598a43004fd7598a4304cfc7598a43006be5498a43006bd5498a43024fe7398a43026bf4398a43026bd4398a4304eee7298a4304eee5298a43006ed5298a43026ef3298a4304eec3298a4300cfe7198a43004fd7198a4300cfc7198a43034fe7098a43004fd7098a430067c5098a43004ff7558a43014fe7558a43004fd7558a43014fc7558a43024fc7358a43026ef7258a43006ee5258a43006ed5258a43026ef3258a43026ec3258a43004ff7158a4300cfe7158a4300cfc7158a43004ff7058a43034fc7058a430067c5058a43004ff7558643014fe7558643004fd7558643014fc7558643006be5458643006bd5458643024fc7358643026bf4358643026bd4358643004ff725864304cfc7258643026f771586431e6f64158643026f73158643026f43158643004ff7058643034fc70586430067c5058643034ff7598243014fe7598243004fd7598243034fc7598243024fe7398243024de739824304cfe7298243004fd729824300cfe7198243004fd7198243034fc7198243036fa70982430367c5098243036df3098243026fb3098243036f83098243004ff75582430067f75582430047f7558243014fe7558243004fd7558243014fc75582430067c75582430147c7558243006be5458243006bd5458243024fc7358243026bf4358243026bd4358243004ff725824304cfc7258243004ff715824300cfe715824300cfc7158243026fb70582430067c5058243026fb3058243026f83058243004ff75d8943014fe75d8943004fd75d8943014fc75d894300cfe71d8943004fd71d894300cfc71d8943006ee21d8943006ec21d8943034fe70d8943004fd70d89430067c50d8943006ef6298943005f771589431d5f471589431dd7e75189430057d7518943006ed621894304cff7518943014fe751894304e7e75189430147e7518943004fd751894304e7d75189430047d751894304cfc751894300cfe7118943004fd711894300cfc7118943006ee211894304eec2118943034fe7018943004fd70189430067c501894300cfe76d85431d6f661d8543004ff75d8543014fe75d8543004fd75d8543014fc75d8543024fd74d854302cfd73d854304cfe72d8543004fd72d85431d6f641d85431d6f631d85431d6f421d8543034fe70d8543004fd70d85430067c50d8543005ef7258543005ec72585431d6f461585431dd7e75d81430057d75d81430077850d8143004ff75d8143014fe75d81430067e75d81430147e75d8143004fd75d81430067d75d81430047d75d8143014fc75d814304cfe72d8143004fd72d814300cfe71d8143004fd71d814300cf
  | 47 => 0x40010000003001400c0014005001000200040030000001000c00600140000004001005800d00200000018002002800000040010000000000400100000000000000000000a000800000000090040014000c00000000010018000003c0050010004001c0010010003000400100040030004006003001200040020004001000c001000000000080020018007000000c000c001002401d001400300180010028000003c006000001f00040030044001000000000000010000004000000a0010005000000000000100000001000c0000048002001400c000800100240000008000000000b001000100380000000013001c000000802100000010004002000c00c0010004000400000100050018000000000a000400400ac000000401900000000008005001c004002400100000060008002003c0040010000003c00900140000010003000800c002001000300010044000001400f0004008005400300000040004000001000000040010010002002800500000010030000000800a000000100100020000010001000900080040044002000c00000080000024003000400000000070010004003c000000c0020090002000800700000100010001003c0020008005000000000080000018000001000000f400000040010004002000800f00040020008000000c00200040000008007000800900300000000002004000500180000008014001400400380030004004001c00000200000014001000400300080000000000000c0050038000000001900200020008000003c00000000020010002001000204cff7598b43014fe7598b43004fd7598b4304cfc7598b43024fe7498b4304eee7298b4302eef4298b4304eec4298b4300cfe7198b43004fd7198b4300cfc7198b43034fe7098b43004fd7098b430067c5098b43004ff7558b43014fe7558b43004fd7558b43014fc7558b43024fc7458b43024bc7458b4302eef7258b4302eef4258b4302ebc4258b4302eec4258b43004ff7158b4300cfe7158b4300cfc7158b4302ebf4158b43004ff7058b43034fc7058b430067c5058b43004ff7558743014fe7558743004fd7558743014fc7558743024fc7458743004ff725874304cfc725874302ef7715874302ef7415874302ef441587431f6f63158743004ff7058743034fc70587430067c5058743034ff7598343014fe7598343004fd7598343034fc7598343024fe7498343024be74983432eebe439834302ebc439834304cfe7298343004fd729834302ebc429834300cfe7198343004fd7198343034fc719834302ebf4198343036fa70983430367c5098343036bf409834302efb4098343036f84098343004ff75583430067f75583430047f7558343014fe7558343004fd7558343014fc75583430067c75583430147c7558343024fc745834302ede435
  | 48 => 0xb000000c000000a0000011000c00300200010000000000400a000000600080030008010002000b000800000140000000002002c00100100000000002000000b001c004002000d0018000003400100000010000000000000000080080004000000000a000400000080040000005000000000000020008001001c002001002b0034009001000000000020054006006000b0024007002c000000400100040000034000000c001003c003000800d000c0170004000000400100000060000001000c0080000001000400200000000004000001000000040000000003002800c0000000000800400000010000005001c0010000003000c00d0004000001000000200000000015001c006008c00c00100070004000003800100000050000000005400000100000014000000000000040010018003001400300200010000001003c00600140000024006000000500140040000001000400a00000000000001000800500880040004002000c00100040000004003000002c0004005000800000040030000001000c00f0008000000400a0000001000801600100000014000000002c0024002001000200140000008000000000e00780020070003000400400480010010019002c00b0018006000400a0010002000c0030010006000400700000020008002000000400040060008001000000f000000a00040020014000000800500080040008001000000000100030024000000c00000000000008000002800d0004003001400700300010010000000400200200040014001001000100000050004000003400f000400d0008002001c0010000000000800f002800100040000004009003000000000020004006000c000000000300d4001000c000000c000001c000000000a000000300480080000004000c00500040000010000003000200100000004000001c00000040050004006000c000000000800000040024000000000a00080100004007002000200840000008001000c00d00180000000006002c002002000500000000000000001c0020000000001c001001400000140010000007003800600040020014001000401f000c000000c002000c0050018000000000000040010010000001c00200000020000007001800000280020008018003000e00000020008003001400a0008004005400c000400300100010000009006400000040030008005000c00000000050000000000000e000c0020008005000800900240030010021001000400000000004001001c002000000f000c001000000000000010000001000001400140020014001001c000000000f0004003003c00c000400400080030000001000000200440000000000000000000200020000013001000000000010000004000c0040000001000c00800000020010008000400200040000020000000
  | 49 => 0x1000c00000000070014011000c0020014008000c0020008005000801000480010008005000800e00080220004006003400000040020044000000c00000000170004023000c0040000000000000000000000054002000400100000000038008003c0000004000001800400400010000000003c004001c003000c00e0024007001400800040040000000003800000100070008002000401000100010000002000000000000010004001000000300000000008003000000a00000040000000000800000000000018011001c0000054003000400700380000020001001c00a000400500a400300000050004002000000200000030000004001000200040010004000004c00b0000003000c00000100000014001002400200000130010001000404a0004004002c003000001100000000000004002000b0000000002c003003400100040000008003002400300000020018002000c001000001d0000000001c004000000500780090004000003401300000000008004000800500100020000000003000100100060040006000800a004800700080000030003000c0030000000001800000000000000004000000100640010008007000000100000010000000002001300240000024004000000c00100020038010001c00a001c00000240150010000003000d0000000000000800000040014005001800700100000000002002800b00f801a00040020000000001400000040000004002001000a000000000080130048006000c0000000000001c012000400100000000000003000400a0000014000000400000050014004003000b00100000008000000000b00000030000007003c009000c0010000000000000d00040320000000000000300180020004003007000000000030004000000000200040060018001000c0040008001001800000000030008002000400b00040050000006000000a000000100300130014014000000000040010000000001400100000000010001000000100000010000002002000000000030014000002400100000060000000001800100000000010001001c0000008022001c0020014000000400000000100004001000000b0000002000000000d00020004006001801e0040000001400000000010004001000c00700000060000002001000100040010004001000c001000c00800000000020001001000000180040004002000c0030000000000000a000400600080000008000002c00c000000000000020024016000800c0010000000c001000800300200020000004000001700180040000000000c0050004001000800000280020004001001c000001c000000400200000000024000000800000300050030000000000d000402b0000001000000500040010000000000c000000800200040000004004000c00e004800
  | 50 => 0x300300000000006001c0000004001000000400100020000000002400800040000010008000001c00200180000002001000000440000004000000000200000010020001000400300900010014010000400500040020000000001c004003c00300000000010000001000000240040020003000c00100040010018012000000000080010004007000000000000000004006002c0020004005000800400040000008004000400100040010000000001c00100140030004002000400000040030004002000000100000020010008000000300080030058003000000100040070008001002c000000c001000803300000030014007000000200040000000000000000000000010010002001000a0004003000001000040000000000002000c00080000000005001800400000060000004000800000000260004002008400000280020008000000000000040000018004000000000040010000003000000a002c0040028008006400200040060008000000000a0000001000c004000400900180000000001000400000280040014005001000300080020000000000c0010004000000400000000000008002004800000000020038001001000700080060000000002001400140000018005001401000800000038001001400000000000024004000c00700000020000006000400c00100090000003002c007000000100340000000001002c003000c000002000000040020004003000000200040000000000004800100540000014005004c008000000000000170014000000000000040000000000001400300000040010001001c0080000011000800900140000014001000800300080230000001000400600080060004000006c00000040070004009000001400140030000004003400f0000002001400c000400000040020000011004000100000010000000000001100180040018003000c0010000001000c0040014000000400b000c0000000008000c000000c00000000000004013000400c001c0010008000001000000140090008001000400100040030008000001c000002c001000800200000010020001000000000000010004001000800700180000000001002c00500040010004005000000000000050004001000000000100000014001000400000000000000011000c00000000010000000003c013000000800000000004001000000100200000000000000400000000000000000002000a00040000004000001800200080000000005000400a00000000000004002c001000000800100000020001000800200100000010005000000c0024000000000b000800b0000006000c0020008001000c001002c00200080000000001005400b000c003000c005000c00b001800d0004004000000300080080020003000000000040020000000000000400
  | 51 => 0x40000004001000000700000060010003000000100040000000011002c000000000200180000000000000800500040000010002000c0010010009002c00b001000000040090000001001000000140020004000002400300000000000006000400a00040000028006000400000040180000002000c0010000000004c002002400100000000000007000400200280000014001000c003003801500080080010000000c00000000040004005001001900140070000000000000000200030004000000c0000004009000000900000010004002000c0000000003000c000001800000000000018007000000200080050000005003c00400140000008006000001d00240010018000000c0050004001000400b00000060000000001c0060014008000000d003800600d0012000000b0068030001c0070010000003c006002800b000c0000000001000400200080020010000007400800140070008003000800400080020000005000000b0020002000800a000800200000070000001000c00700000080008009000000100080010000007001000000100000004001000400a00040000008000002800000000000004002002000000140040024000000400d00100000000001002800400100000010004000800600040020000005000400d001400000000030000002000c00000080010004006000400300180090000002000800300180010004002000c000001000000000030034006000000000180000030019003000b003400000240020000001001c00200140070020001002000000500020000000002c007000000100080010024000000800000040020008002000c00400f000000000000008002003000000000030000002000000a0010003000800a002800500000010004003000c0000020000005400c002000800040020000000001401400000060000000000800200000000008007000000100300060018003000000a000000600a0002000000000040000004005000000000040090004000000c00800240020034000000c0010004000001c006000000500280030010004003c001000000000280020004000000000a006400500080040000000002000300040000004000002800300100010008000000400000000000000000001c005000000200080020000000001c02900040000008000000001400080090004000000c0020048004000000000040030000007000c0000000010000000600080000034001003800100000040008000000000200000010008003001c00200080090004006000400000a40000000006000800a00100010000005000401200000010008002000800400000000024001000c00a000c0090004002000000500000180030000007800300000020010000002c00100000000000005003400000040000004004000800000000
  | 52 => 0x97200000008a88000deaad286eb00000000f628bb992c000000000000000003ad2eb2000055e0f2c0368f187648000c8e802eb170686a693e4a284b0647ea103cfa4962200000001d88c7ed8c2d2c0000000496b56efa58f8033120080000000d7dbabcee71d98e6d2f546f48fb2c148000000000000013e6e03000050f34ac8da0000cf5308e7dba26067d234eb53aea2a75bbc8aa2bbb2b870b9274231ec6e09c2a3fba64ac8737fec2a2aee72f00000000000000144649b000099400000003aa00002018b0d3878a280000c4400000002e4c0000000e07af8800009a20002d56ad0000096e0dc43039d0a0000678d61a24a1c32b066c680000db922a00004640002f5e6b3b0b20002604c3d230000000000001a9ec8c0000de88000f75800000005740ab8000070b14400006ee0001b7c3adb848d8f83aed66000074d942cf9e266226a976ac051e16775a8ec9b095cc1d3284e00036a45a938e000000002c200000000752ac21854cf290be32700007cea4e89a2ae9c90a80000d780000e22b84bc23e82000036255ab2b660e147e33abc86000000000006066f5a91279f16cc4f10e569272b5858e196c3e598f082e128089d05984f8852a529217cca58a104c094dc34b3ed200002f00001fe81c6a32a0000000d9c8000beb96508c13bbaa100000bbe3d7cfb9a69a1b2a15e28c1044de9000016faede777000000032360000000000000000016a60001a26000154641cbf02000070409631fc70180005ca95ea271800000000007b70000bc5aac861c8f66400b3920a80000e649a48b51000000027f0000101c000000000021b84f2bc4e8daa62e6f38f30cf4252eb920e3a000301c3ba80008cb0ab800031e40220000ecf0000d3c000073da53600000002b4aad294500000000b843e823fc000106c0003160c1610e24428000b270000efd0000e1884c003517c20001a8895a0000b8597da6c780000003c6a00000000003396c8293d036fb642000000023112b69c7ad6c0003816000000025434ba0000000db38b8c0000f3408b3f3ca859770000023091e162a0000000000157c8f180004e193b20003a70b4300000003a2a0b381a476dbef430baf78000000000000000000000000000004d8852e3d80000733526a270d0439d80003c7b5680000000d7a285a3580236eab26e200032e69ec229800034aa0000000f2300008818000e52986ec43372c5448960000037ae3f82b86871d82c08997000000004768c3c00010069d0210400000000a2bf3edd48000e9e35800002ecac16aed4a22bd5220f2aa80000000be5a64c000263640d08c25138000000000000000000001eca00000004dd075c00000000000c2200040160000000001000300040000018007000000000600000000000000400c00080010010008000400b000001600100050
  | 53 => 0x4139d76cd3baea9a5aaf40631882a68a7bcd2e29ee17c810eceeaaf03b99ef0000385678e10941aa00000002f7cf2a2dc83eaa84c8810178d0580008e4bc1c9028d72935a5860000000000370c740aa0e00009fc0002cc291f000058d9bd887f85d01a2b63a07d0c968e7000011f89cadcc20d811505940002d1e94d067400000000000000000000000009e4d1b800089f1c320000000bf280000000000aeb3868c48b2d20000000baf00000030000bcf00006ccad247ff9be6dd93a027da087cd048dda74600003af32800002dcc000312cbd180004d41ee476180005a600005fd0000000000000000000ce80008e3a90cd983876e870000aff37e6f2c833e00032320d2b9e6b7c813200000002242eacd4b2e6a0ab2966000000069c008ab28bb1e59e01ae0001c7ef41bb6cb49ada4c289dce64cbb22366baa8684a5c439228a8c36ac32aaeb8a6000000085fbb740003818000314879800000000000000376e000000090e33a864ba7e4fb30000763800031d98e8e9dab70000000000000000002a880002d72000107eb9c0e527f200000000000000000000000000000000be38000000000000000000001ada00023f296380000000000000000072e000000039720000000000000000035160003b3acdda0c6ab38dec5588000000000000035b6c1ab4ee6a2a4187573b9ef7b87709af800000000000000000faf000056aa52c0000000ceb0000aba8930ab7a4dce0f80002143e627e90000000000036f0000bb816aa000178aa0b220e538b074eb98d8cb9d96060dc8748f84a4a0e933aa46ee15fa97fad4280688ac11f184a0ed16ac0000000a5b23d456280000599d58d59857c000000040ebd60367000052f0000000000000032340628000b353824a5d9bc2000000000012b82f19742c1136c07ae068c84f91ca7ba15d25e434e26d83e90000000029580000000470c11a1521900000b140000023000012e80000000b6ef7489ec6cb1d103dbb61a8ce1c6a9a3b1043858000000168ed7b8000139800016d00009938000b2d84da3da80000000000dda11be00039483a22a9e0d90000260867e0e2b3366b786340003cc2c94171e8613174983969ccd33d2c3df1b0c659131ece527eef32819a000000000000000003784000000000016d4c43a7080003a5600026fa00000000001c00000000000000002f31d52e9f29d2e6c33ea0002eb20002cf22553882b810000de1bae2e8a00003a98000dcc833c424b406aa405b60000000000000090b000000000000000000c46800049f1fa60001a3a0003134cd81f024839136fac9c264760000d9300baae6bbf8bafbbfca91163c50a8f547d0b3e6000154400000002a4a67ae069164fbb03b80001baaf528b16b4b800000000001c78000000000000015b8557162cbbea6c00002dbc9e8b5ae0001
  | 54 => 0x80000000d924f300009a62652cd58f3cc03ad64053aa142328586144bc08f4103227a02584f69a97c098bdae61430bc554800000000000001df00000000000321a0f5b48aa8c09f20003abe000000000000002c49a7c794065691fbb5600900004e688d43b0000045a01f600036d8ef60000000295adfe316c0000ebe31a8000016049039a00005d3080800021f22009d384feb00600036a2000077263b9cde00000000001382ce42b768259c76000000000024f800023f614d3b32dec3b7aca619d48f5a6262cf025400039d8000084c09415166feaec0945a792168ab9805100fa21a80007f7000000031eae3e80000001ebcee5a4e265bb7d617f80000002a7a5aa00f27f2a0760932fea454b4a8000095abe8aadc4d98000e86809e000350ab0e8e9ca4a2404b300000cc40940dd1a49ece718eaecf9358df786603fc2deae0b9ce47b6a0c8c768a3ef4000000003a801a02d083103c96135a8e4c398000071baf20002c7a000000095b3afc4df3c16c81a2ca907a0ca0002356a8180007aa844c000244800034002708edc76c00001830000000200a0002d3e000000000000000000ac894f2f205918f244638000a5480000002588ac90000000204e8db041a00017cc797800000034e80002a1a0002aa6b46a3b8eb098cc10e33c07c31ee0d460000000000000000000000c7411580008673ba60002fc64320000774200477da2c000024baa018000000394655f9314b08b65c4dc9c9e00012f68a000008d70000f85a91e0000d8a1bd8000e2c868e2ca368c4572dfc76332d4e1c10feaf0ae0e0f2a64280b02b00a400009a1a3086c098ce6061b3422c96c60310000000000000000001ad00004a580000001dd400003be402ae44815b59a0000b3241805fc0000352b9f24e0000000045f8006372810065117c64e9000096000000000000c5c0000cab9450704bc589d32c8c00023de000000000000000001d800001c489d600001801d6400037e0ea28000a649a3cf37ac6473f8756000212c000117a0000da488280000000efe7f185b054906ce1f0899039b00000000572000000057900001859cb0c4ca0ea5dd80002fd3a322ada93ee0006be00000000003272df40c0a0970066a171ffc3200b0a6e6b7240003048a78a5d46a0ab5eb7627b439790142dc00001730000b3219f091bb9fad790d744dc312899e04e8694301a9a7902045306080508252410a5bc5929b5e19c1aa40e9adb281a17e855d87ea324af985cf0b185222b10b2eab382df1cd2d2da5708d32e00d6884400272d58a889738bff8000beb2c20f6788a638a2e10f7a2bfe3600000173afccfa8bc069c8a37246d882248587ca05916562e80b9e21d01f268317c005a000038d151a0000f0e1bc9694b250000006396200000000002e90e4a1a6cac481880f8925c301a9e4
  | 55 => 0xa15eaff6379365800030def600b606f93de2000223ebfd2090000028231b8000000097296fa55a00000000003ab0daeb41a3b28246e60800000000000002e0a9b7893660d8fda00000007a38000e6137e80002fee000000015883a200019120000c0000022ac4273b1cb1300000b680003fd800086a8f020000b9664a00002d0ac4013f8390521aea8ce2b188000313cf099a9c3bd8d300002c5400027ecb4287465c01c90f0a987e6e1a902f7d3d4e00e80dc9ba0c4e90f0ece0c2b0106958f92380000033bb12e8e18b7eeb43da000027449d4874a26c3a5e504000051c8000c71121a75eb7049fd80a40003670000000027700000001402ad4bbb6ab181c0912800015d8804b57a9a605a80000e39bf2ad3a54afca0000876800000006b800000006d5a8ba11b80000001426f33244c00014fc84a84b6ec0806a000154ab782822e8100001a0a11a3510386c44bd3204ba878ba526bae183c9e93792221e6208e0000eb8c9dadf642a044af4980001aaa6060002f36b5520060000880c478d4a00005ac749306cf62348891c99be3619fecf8cb4382b32cdcc76047a2ed889658300ae090826449ba4106d3059a000292409b0000f8933621a990c6c1d8ce4606a040f8600c8000276462b0000088b58ca6bafb894c0452009af86b2bb9b87118000cf0bac0c1296185e0800035a0000d3780000003bda1c48a5e6d880002340000000041800000000000c18000048ae6f1af86bb1eb6a0c31a4000003e0002862000000000a0000ce20000000000094aa2a86df80003be0000b070000000000000038e4ee22e7a62bbca43828000508b3ec000000044c1a3024f00007f431ae7a580000000000f33b4dc0000000000000067fbcf4732affa2ce000086c0000000000a049000062d8000a6798c800036ae0003ce60003ab800000007083342f7f310671b8000866800000000000003302e6fa22629e3696a4b88563a0b04c91da6b0a5080000002ed000000000000000000000003080004230000000000000037369412f1c0000e3cf792526000000000030ce000182a365be50c3a00009dcbbb00002d7484d22bae7dae56da1b2b2cd69604cdd00000000000c7c201298d141a41880000002268000000000000000001f8a0001b2a32299745c89ff44f08d0ef9b00006ab000087f3d48b09190ce11ba9c0cc9ad6800a9ca00003d0d0b9f740002544000000000000000000000000225eb0a00000000000e971f52c2908f00000c2800000008f304883b1a50ceff800058f825e00000007040dc86d0b156eef3c422911f7a4692c0200696b0222352455080007b11f581cf04f4f408000000063c0002a56c1984068311bb0c64a33e2b726f2ae02712e41816eb4803582531f84c8123148f9138e6b128c27992194357bcb61c51c3eef1224690c8000d9e
  | 56 => 0x500008043a16000036aec2a84a91e90d600000000003c626e1000000015c40002b3000017bae7c11fc000298e4d68000bba059c00000000003da27a9a0820002e5c0000000f229a342c7000052a96cea1cb542a579f622b7a7424a7322c2c4128e6d127201fc2e2c0002e7e1a7217400004789b4bee815b00023e512a099600008e997d2000337c0000000000021e2460000000000000008b8216000000000000002ee4518800077c800000000003120626459af3a496037c9a901e07322cfc1ac1024dc6a23888b80000001d663533720000090a000004400035a800018f2ee2800018e80a01ec04f2000167c2bf3f0699a8dccf5b8c8e75080007d19e7429b38d600020a600000004d4b2ea953800082306dea29ac5ea0d8c8284712e476f052e3cd8e60a37187a3572890c0784ea0002f660001d50ac835fc00005520000000e710ae6fa9810a51b1ad8080114e3521ef87c819ba8331250192a054f1b9a7ea5292a815792629cf004814c1e86fce2e3a6630000f0c8914000000098ca71600728186e013307468a02a8e000000025105d88a88c0b316e7779c8842c27de0000d7e7a69f9e00006f8efa08700000000f643b4cf508e548ed0000000133a00012eccc6084409d1a20d65a8d02d5a1c26ed800005518e66ada37a888800000037c800000000b70000000000044b80000003e00d9a8d64000000046c14e00003b2a00022aa1cc0000f7e2c04409ab5c0000c1a73ba1e05df911299ba14aba18062b3936c6f668b00226392400024c07d226440c30964d7200005d41bca89080000000000bf480000000000f9a80008c335f0f3400005453b542fd819600000000000000576991a0000000730bc5cbc9b6ca0000000c782e0806d0000d7297ae35f000000014eee951e2416280008748000e6b8b20afd000000000002aa800092080004ab8342a76800005c10b6121a53ae3d27f81f680000002ab6c482e74e053eac70f33cedb6872ce110000000091cf1c8be6a23151c000000000028d40001f6abf90e922f3a89e87b0326026a60ae7a9af414980003dc3b6a0000696f1d3aee000174a8fa80006450000f770000000237e8e42e2e3d8237ce91365edc98ce217e2bb200000003aa3f000000000b988000b52aae400029960003560000352a5acb12a0001b4e000000006da66c7998000000150a7a62ed60000a946519926ba28000302133e00018c60000000acaac706da09ccc8010865cd9e3c3359b1c2091264f26221aeb1322a00003d20001b88dcf00007780000000000000000001750000000000000023a0ed9848cdbeba722870f86000101a00013260001ea40003c189ce235000026bc7948000aa70000120800040e1fb60000294d23a58a000062800004fa00012906fe3068bd28c6c475b8807168bec7df1bdcf1d9c8c00021f
  | 57 => 0x70a5ba45a2b8202a00000000000000c65b4a06588000c24b9a400000000001daa0000000000000000000000000000000000000000008b700000002d84d75b1a600000000c594c8fc2b33800b3bce000000082180009801d789bd19e20000f0417281ec07382f273716ec116000047d84100000000b601bae0003562000064400016745de3e40a5f800000000009772592d9e258c8ef306e0000000af780007ca2c0e59a000000038ce7d535003351e26000020234e10480000000b9e32c012f11ce0003cac00018600000000f818000cdfaffc8ff93fcc1e0000996800057280000003774f04a6cc5e12a9492e37e49e989b83b334b026e81d6c75875800021ca8f482ba0001ac625a8000d56216080d09ee913bd64076bd20a5411d047792aa85baf4e49ca39400015c081921484f700006dca974da80000e57923c3a680000002a8c530298c0000000016988a16f32eef3c0000000000000000004f9175800026247708000ea8903e00039649ff9f060000000a3100008bc34a23cb9d8449817a0fad000076ebb6ec6d22d00f0abf0000000030c00004e41d48a2026ec541000041512da00015d800024be88a000036a91ea414800000030c80002f5a0003582000272c5ef3264db1333a0000000faaae6639e80005fb2ca800e1754d211f106e631a200007661e48000292143ed6e0cfc2f89ca42d18610bb100000c42172d302fe29bc2224c860b4a566183ea8f055a00001a02690aa40000000f131f4e29a0000a73815803b0c68b128000000000077f8f12f831c6c3e432bc40ab914cbfa4cc32f21b6b64854edf385d25c3800065801020001cfc987ae3e613adb89211c24718bec0a7818865c5290624b000000000000001e2c00000003d1913a1bc2564412800000000002368000b3b08c6e1cbb8400000000002efea248750b078cd000008e8bfe3d44df60270df094fa72b80000002d04000000080303942fe1570a38a0aa000000000032900002860000144400024ecb7d3d50d0f9d5e9661adcd8325b2eb60f983a800000001a2422797ac33f9e4ea070000000000015186c08e0bbca00015820001a4653400005312dbe51a00001cf89be00000000eaa89400013e800030b078819526e899ae23a95546db090252f8000bfca866855b60a3db23f8e753f34599bbf6e23915ab61a0aebd71c4e0002c2c57e0000e980f7600004c60fb2af2ce380000000000000000024d03f040213d2d2600005d3b1840002b8a0000000a082106c5f000000000000003d28b8e2a2cc6039ec0e6b3b81eb239a8c60078e4c18e0c05867cc4f9856c632af80f72dcedc4000094800000003eee0000000b93adc2cc9800000035140003916851800000006c200021dc0000010f1e383600016d8f628000e6cb2a4c8bb458cb43080c1013b076434b25130000ca
  | 58 => 0x1c0f42784a4b60000350ebd8000f208214489167a0001fea0000000000287e0002320b531cf00001a10c048000def83a4155010c9850e900000d58f3ea7dcb798c507b395e06fc09f00000f0054a8f10de01aa200000005cb800050e9192252000044313181ca8446220ad8c9d200008d90000a623f12e3e114a0002e5ee6b0000000000000000000000000000000000006ea000000000000000002dd40000000000118667cad620f131e868114940002ccc2330fc8000002a64199c40de2340cc300006749274000347a1ffab1418280700002918699274a4b2a92624b800000004e0288ac98a4d091ab4d8000e5e000000000005e8bd66ce809d029a8000b312f6800000000003ed80000000000359e00016921ecbda400035cc000000000017a448e9e4036b2bf85578000000000005dadc4ce880000002c3c0000000abd800000000000000c5c04a0dae0001768786b58e0840f8a33d97521083d7042d0de600028f800038b00000000000394e0001922c228000d4827685a1832c9b22a669ee800000000005d2000000000006d600006d919ee00000007d7000096aa2721cd000000000003e70a62b238b9c1778e4cc2abd7a6d2207e0000000bb980000000000ec0000029c000000000001e980001b180000000bbe00000000001cbe0000000000000000000a2000000000000000000000000000000000000d210300829f5ade3000019b000099f00000001a8e6490000000164e000343200025c6edfb4c47e430c4beea80a0968786b74800000012269b98a50bc0ac16000000068218400000000000000063d18d20001fba6dbba4e7ce0b8200025580760432707a08a2cb349a000275e0001d7e932928858912327050000ec400005d03ed0000000033e8d280000000b27ab785cd128aadcbd8c1e782126fa00000000000aac0dfe8721084a1083345400d40bd128bc01d96b84b60000b34b8e2b2125520000000dd323ba00014420000000efc8000471000000029ecd0622e82ef0000a7e800015b976416ab618a93b90a4baac90cc83e280003e883a6000000030e2000007a03d80002a831ce00000005478b48000000000018bed2bbc500000dee6fd3e520000000ba0000084880000000370000095ed140000c9580e4178a3da1593e26e3ba0d02040000e1a80004d7000012880007a899e600013ae0003b524db80000a3986ca602a92000000000000000000000b962da6df2b02095d300ab1fa5969288d500000000c3c8000e370cd82be800000000000000000000000000000009df8000000015a829000000000000001cfaf8e8878d80ae1443b80000000000b5a1a3e43114ec37c0000000000000000008089c3014535f22ce82a8be2a05a0f987187c98d060000000e04b5521e32b88d3380d89020a82000000000000000c39b0a0000c
  | 59 => 0xa4c0002e9aa799c680003f2a4b3bcb800000007f61194dae0cc2bad8000d5f9b5c53fb44ac4d8000a5c000000035460000000909a10c5d1ac6adaa8000eed000059c3994dd113285980000e7199e800009c80000000eb3a76aa8326384db01e629bb42607f9c6411b270487394b293932e24830000f0b80002e3bed629f07b6000201ce788000000260c00023a24a132ec00010e854180000003548408a9ac0000d123080000033b05e0001e1c5e1800070280006ca2b3ab4024c61ad8000d7e00007b42a42c0e2ac46679dd2c608000a2a80000000000698037600000001b60000ad28000034916e0aa8580e3a003277000000000d0a0002d52bfa00000000000b9820143113398a6422d8b29000049311a89a21e280003a1400002de00000eea3f8a8a0000000f732f42c94800077900005fc1156000338200032c6a9b22fcd0b39080003f0e0000000ae780000000000897094e9e200000000000000000098f8be4000119e000000000013c80000000ca1b654262040ae943626000163405eb15c0000000e4630fe000000000000000000000000217065a349635a9132cac21322c796620000a4cdb22de4905b9b6b5e0000d27000088406120001e58000286c000065800002d000016fe0001cda3f89858b208f489c7344200000007c100000000000cfda940a9d0000d4a11905a40536c0f9228ade99ea28a1430990099c12980b25c6ab925430f880af2fd85f3b304cc7800000029c694c80000000000efb8f440001bbed779234cd017be00000007300a066cd884ecaa3ec893e817209cb2540001076978034cca384500000dc20000000f752948f5508ecaf3aa3a0000000b39b77e5978000ea991a25682212924397600025b67bf30f86e405782852a5a3b52a54dc7b73a0000000696b9de673981e04faf9408d2f302280ed254b8dd6eb5b172e703c460fea65eaabaa003108000f431e4a9b60000000000091a1996000012a00001eefc13e600003476000000000000000001ae00000000000000000018c4000000031925244c896be00024547c623c2d1d04c20cb80000000cb6f0f12eee4d2e9e0002000ceb9418571800009b8434140800045a86fa05724a65b8accab7e2986cae8000da10c320000000000000095e24bca4ca03ef7a92c4b51bdb26dd93340000894f70bd98111158e000122c76500000000b0600020a2d8d0000d241726b7f8ad6db980004ca9f1a0df80000001a68bf5a2ea0dd3b760003a0e00000000003c10c99bb78cb3b0ec84e2f2276b1d4ef38a5ce00000000002fd0f6080005100b62a31b3aa00000002c98b8073d33eeee82a783bc1dc425d1e027a0adb49c400fc129292a1cc92920e7811e0000eee00000000001564000262ace132e87c78000871000073e1ca01cb8000000000000004ee000054009d9bb47
  | 60 => 0x257600034f6c808000b1d99c6d8b3cec44d1afc2f28884a809a424bd05823558000463131200007ce48414d80000000ecb80000001a020001d4a505801683d38080000000000000066d000050132c80001c44c382b4400000003091a54f451b6aee6af84ac39f5e000000000030bec9f2a868ac3bb800000000001d3a000000000032080000a90205abe009ebec6f738000449b6b43282a98e080000fbebc64b3e80000001afea3682c80afbee4a9200a89d5a8100000000bdbb8a40001d4c5872bdcb9b0000dab2a206a02dd615a2e6e0b82fce234b96af8e063639115809e6bab466d863e0003c6800000005e98000000003600000007e689fad18b118596197aef912b281719b238c81066130000bbc014c9ca3c5ee0e000000004c4cbc8c5a5c08000000278e00000002ea000036c0000553adc614614ac8508000cde8000000000000038c40003a3aaba14e859900000b92e30ecc27eaba621ae98c379800020cef9622142049ce00000000cc1bc0094e35dae8c17f6e6a22daa1dbd3af61173e0000000000379af45a5a6e9a10ccb5c235250d909e2a9896ead5a648e723d3ec4e28b4326305c000193053380000003102e9a80006560dd40001d0c00023021a481e8c241ae6ab9b41084b9c4c00033a6b701bc8c2580000519bde00000000003a940002488daf0ae2a4e0000a4b000000009a8da280000000000000000000000000000fac000000000037b4670104600038bed709706e5f81de3c72964af5388400008e469786b22420000755b8ec526a5466210a3244121a096b80009090000f71b53a26f0000ee399a0348be723bea0580000bc800000000a3000072a89f6203970439e06c8b4d1124d55000006c80001ef35f4d5b1992439a8b206e00000000d0000013ac0000b14c9d0000046b7fcd938000000000000026ee0000a082d393ce000000000018b2bc6352e49c37c6f360000ee40014277bbd653534206828522e800000c6680000002654000000000000006c18000275bd3402c000051985e66619ef63b7a5e6000000000000000003edab2aa8e84b1817c04b287c18c93de9581236000341e00011c686880000002bb4c500d1000000000003a8e0000000afb0000db82b96000308c00000004f58fb433c8ac6236263c30f877812a000000000000000000f0c00000003a90d0eb5880002066000000000004ac2f0977aad6be4c00000000001a440000000cca800020e959c000111e0000000000193e31f35a4ccb3f36b0abec20000000f2ebc7e6410782dcf96ea49a1b8eae90000c15b3005c28738a39ba34b9022b2c5a0f5c2e90e0c212bcbcc301d3c00037b8dd0034e0001ee6d64b51a000000000000003128e40b848000d02000086c9ba06cc1d6a00024a800026640000c9e0000000000004cfc200008cd8cb0be42
  | 61 => 0x330843c2610296827e0000000f8f0000b2fb70800004dc00036768f40ffa7cc2fe00000f205b402d686d1ec09d183ee4949e0a00025480f6800000027c47c580000000000000306000000000002c0a2928000a0ab2be3070000bd400000001a6ac83a2440000f400000000cd180000000d3693c2c6cdca0000256000000013b4d8031bc0002c7c6441a86c3aaa26b3fafb0eb81d220000000000013c0000e5000000000000b884b8ac7281232cc024ba4623d8000d0d989e9888000bea369e55eb6debbb000010719c2000370e38e000017bb9ba4ba00000000000000350400000000170000ab6251a4239d9a0003328bdd17d8e46ab1cb9527c23962d8a20e08543f4040469b8148c00b702755000042b0bee0002450a2091000000324aaa9712000000000000000000000c0ca4da6ce8000b7425f4f8f8000dbd0000e7280003742284ecd8aca8309602b1d11ee1fdb9966790228000000000014480000000568b63600000000000000000000063b00001f539ce0000000f4630ae43483ac0c611aa455323800028ee6ac39f800035ec00037eca8b8000ed709a61c98566b520000b8d000000000000003cb4201ab4642093b8986026a44386685b4811c0002dca446a68000028d8cf4b80ef249a622ab2230ca0892a7298db8920323ed420000000041ecc38000d3f125e6460b2eb7ebc280002ac26553ebe0002d166762846000081ca5aa144ae3bc34a0e1c8000000005b120529d8ba2ef39000003837ea00000008718000000192a0000000b2200000001a96e4087a0f47b988c9e0000f8880000003b121e41792655b6940000000f272f70a3d01ea162319043dac78ee89902f008ac070612c06280000887997e930800037c95ec6e9b6eef1b389a594a27e8d181a204205c200000000000000fa700000000000261b45c000388ca21800000025fa917800000000006ac95b20002492811804200003d800008466599e8a5fbaf247cfb11c0000000cad38ac21790660000d52245afbe4562d3c40100000c6b00c000303051780000002554e4b800000037fabc2800081c8000000000000039fcd9200000000c341a6313adb5095c3e900000000000000033000008fca1600000000000000000002416480000000947b3680000000000000090c0dd2d24b60e89992e6ed38b660002a722d69fbcf079eac66aba82b0e126a84831301108bd6bcd000088e800000030b8c3bb1f2910b72247b0000ea7800019200000001fd690738de1009eec6cb800002da2c400027cc9ef9a328ab9e6a54fbc4466134fa2401e040001f64fb780f4f5e31f44bc80008cf05284b4089ab7a0eba0a6bde600000000000000000000033a1f2aa37b5a630b1e68b1800000002bb008600006652b36000000018a80008530ca2b8f050cf97800000000005c724864f50000
  | 62 => 0xc4980000000000d1c8f50f95985e00000000000596da02a125f7137800000009728d089db81d200000000000ed8de822542358000cb7a6b6000375e00000005ff36d668b000048fa10a000245c7f0b0629be1040fb2b8c04fb07408e1078acf10e66acf80f86268000db0beb6600226402000005770cc02da8000a3c22e497d8000000000027a0000000119c00000000e70e2236d800056db63200000000000000000000000000000003a0600023d8ef3000032b97e085e18fc00000000000000e1b897e982000087db0509268ad000000000001362000311478c0faef028000b1680000000000b4c963000000008112b6e3f000004723a5214400007158000dbaa44000028b60000000dfba90400000000000000e17b15e10babfad538000636800000037f04a7be425778e0e4df83467581b04d100000955ac9ac10800099fb616b0200007823c7a36600000002a34b1480006faa8d2ebf8d2ef323d0ed7a9a984a99f3220c866ea92abcc4a5078400000004ad00000001f3c0000000d11800076c800000000000003cae0003826000080c2678000e4380000001a22000327a00000000000000cfd10700000000810b430000359caa080006bab03af1f3dd830a80409880414b3e000000029007eca7da00000000002c6893cb99e000325a987029200000000000000cbc0000e3c8000c8a12dca38065e7e60000000340c92ba4b09f993940d73bc697aa5da1638f68b990f321199fb80002780425b71c0fa26943809760c88bb080002494af48000000268210c00000a9290e00010d095091d2c5600000000000824bb165c5a70c9c3b2108dba2cc00027827fe189800000000788000167800052e396625b1c0c6b5153a0003b4a0002df000019b0d4fb3dc76933b21559a745ed98b01490000000000000018b84b5000000000000ec9c9a0003c8e2338000687850400000000001bb2cb5a56e0000000e898864d9b350e7df8000e0a9e88d7f80000000000690262810b173a0000ec4e963bec490000023b800045d180c358a0500000000e820000c9702680000000a098000640031cf650a52000000000000004e3000000000002eb800036d000071f16720000000000000063505b20003a40ee33de04d5a2d2ba3341c894280ebbd89b4d2f90a6b893c601e925f005b0000b0404b0a7e3350000210ead980000bd1ab4bfb33de908b02e0001a0ecfc800044415a65b909428958a0cde4855c000000008aae4a5b584e29a41fe600000002d700000000000000000078016a266e0000e40056ac87a0f828b000006530f6e98bcd2c7892cc6801f1cc70904ca1a000056ba51c000000011a89e03e68000000000000013100001feed79800000021e6a7c8000000363800000005e6a9d86c0175a7950fde0000000d1f945a83f800086300000003baada6
  | 63 => 0x35c05dd00000000c0200023e00fab7d400000000000b7400000000000000ee01f1264d1c420000000cb82446b5832fa000318661a2316d910000f51800000008fe35bab42a293e5a00025c0058916c783b4c688325062098ca43fa9ec600028ac8c78f14cb627240258bf049201a800000008c18000fc980006420000f4e38902079888e90b54a061abca319947c00015d45033960a7d8d9479b8000bce156ce8b21f427e0000a1105707c88a8e499aab4a3c8000000000000012fc52886622d7898c38614d29ca8baaeeb8000f8b27d2000294400009702aca734000324a3d600000000000000276c50a1fcee0a1a7885680004c38000045000000013a800001c80002f0000035c4de2b4e400036ccb5698dc3b580005f7ba7a6533936371982c00010ba1ba04b8264906e0000a5cf1c36e40002196f0fb0fcf3f8b7894f8fcebc436621fe10580000bd0939bf30f2a8000bdc8000e74071000000008d10000ccc80001bf0af60000000008833831300008ef8000c590000a5830d419ca79493b800000007c65460152c3c000000019d0b09800077e290af29800000034785bf15b44280000000326a00001ca0000a960003cf80000000bca17100000d344470000000038c657871c3a180004950000933a462b65115e46814600012bae8383d74f6d80683638000f0d800074b00006b30448e5c0000a97962832512824cc80002418000000331a00038d20003e9a484a7fc0000000d341e844d1b29299d11cc7eb3a1027133a445204f0e070b500002d76e04000028d8892000075e7ed1a520003b0e00033648e7b938152000000010de1d68da0000000000000000660000000000027601f8f5d98d87bf93680003886331800000000000000000d291e4635680008211d6c000299cef400006c4bedcc528cb800000000002288bcf8000000000000028cc000384c1270a5400000000002420dec94d60001ca2d91800076a274efc8030459003bca01000000037a8000000074a87e2176800049d975cc85959a500000043caf043099f4c00000008280000e19178ea329bc40000a240638000e330000000000090b8000d5e9cb480e800000000001b327ca3ef800037e11e8b59a4fc26c8000673000000007a8c6e386c858b93a22e9b38cc71936c31a582000000016a0000dc02412c9a3dac6f686f40771e8c46080000000000000000000000000a18000dc600000000000000000051e1f5054d800000019485568000c5a8000000148000000000000000000005200030987be9f446c213541d53d6a724af5860f067a000380a332962e307a8324c6b084000000052980005393bc00002c00000000031e9e4223215bed3e3af4be724980000922751b90c000000000012fe3372b822f785a6f6aa6a29d73530317ac6e5db17b2a821834000000
  | 64 => 0xe800000000000508000000000008c0d4080000000b8a5fe99a428e1f8cb24b0d2ba21c72f809ed6e3aa028d96b26c492ba921dd2c8ac390000000335c00000004d900007c280000000000f4f00000002d90a70ba1278191968552b54000006e23880000002f06ee935104811f92d502ceacf20436caa86841ed062070e8fb60003b4642c80000001cea00000568b18000000000000000000000000c65277400010a40000e8a97f0000707332e5f8b8a2d9b8000417a1082fc8e803701e94b11843cad20000e3082e6f47000000023fac541deaa570bd81c29878334aada20aa02443e3a665ad179c0001526ae522fe2af3b5aaea22820003370000000000031fabaa80002f11ede1e50000000180a000241a1c83a98c2eb7f4000000000000000000000ca8aab2000088ad19bce000000000ec33526e902fe43e8484a6080be5b08db251d1ac08cbb4867d015e60001be0ecb00003d4849eb4e024ecefa6ea000355e4e5937654f1a5800039c2e16a24ccfe1c86d0a96ee0003aca0000000be98000a6280000003b286e5af2e2fa8ad4601a0b01fb15d0be802ee048273200016ca1eb800000013480000000000223c00005b8cff8000000021a000121c00000001b90000000134a00013f07abb2f604480000000000bd3154c32b0e1497b283a8f880de9c9b796f97000000036e84a18000ad4000000002ea6020ac288007020000000d44b7c09aa00000000000d230000e9907fc6439cd459100006dd1c364e12c2e064b330504ad120003a3600000005d1314e0003dbe9ecb93e0000a26f2111884798a860003bd4ce300001328000bc38a6697332da0000000a5c9976019000085b000081c217a000041210200001d9314c35e0000b342eda3e78000af936a8e82a3546be9de80000f844702252000000037d2036113a784a3380000003e740000fc467e036c32d000030500007cdb96e00000004660000000106a0003cee00000009e822780000e42000000000022340000000d6280000000000a8da95659d8000fbc01bc13200009b738c601b2bbce9f8000be02c3e8e2372a00000007450000997000000000000000000b460e5a0003b200fd3322441a75a28d1d729d517b443f0bdae1d0000000367e000229000d0a760000000c2d0000b1580000000000ca82808c0a156e8d699a2a7212e0ea323480001388bc693fe0000000b6680007dc295400000002bfad6a3ec00008d0a660cb0800000008a4d5c1bece9b00000001608000360446e9172000100e0001c2200000008e58ee420fab320001122187b89447e0000000398e00000000002bd000000000000000000000000016145f9a06c00000bc0002ca03a3bdc460880006a4acf0e8908860f7a03000031c8b88b1acf5cb5746389238a28bdfa5f29aa049180008bc800083025a4000000000
  | 65 => 0x2bd800010683f90de00000000c5989ea0000cce0001f0e00035b260b80002db0000e6800008ea800011a03cea2ba4280a980000000000458040e28e80fe7d5b7940002ae0000385c28f0000000235e000000000000002600000a47000000000001a68000b8300000001b660000d260000000e8e00000002d88d5a80009a4800000000003ef346c00000460001f8e0c21f2e9b82f2cfc60000bc50000f9d9d88df131f639cb86600000003fa000000000002748000c6a3776000293c000130617d88420f52786ed09788000000000000003a8a7b881800000001a94717800000022fa0000000a9dace800000004cb800000000005e5335e407800063f8000ae9a0e400000000001e7a0000000000360600030dceba00003698f5eeaeacaccd6294e0000000ebe8000d368000000364ad35369a1debd5c00022c29df0000000000000032260002e18000000047888e000000006d693c6194050e18b13f200000000003c900000c88d41800000000007008000dc490b8000262c0000000000154800013f40000a60000000000000008bd000000000000b51dfc6049d5a0000000000000000035442658000e151b92561a61292d3dec669a5508641ad22490000839b5aa0000e7e38f8000656800000025940000fc650b9bd4b3580005192e02377398000015228b52c48f01000011c8000e9bb19eaa89cb2ef4a5ee15800000000000000000000029161458000d3f80009c28dba00016000002b7e1b9ab900000000000297822a04cc00000009c63d08eaa8f4e8730000000000000000000001deca4c00000002896000112a000000000037da00020d46cf975ea6508f20003a180003d5e57880009de29de875800002194c6000383252082a21f7b3fc0d99724b418d3a290000047fac36c011de6c6db4948618000786000000007e800027066a4000071483ccbb88000046137afa110dc000230a52a27e822b840cb138000af68aa296c1ad059bb454485069e8d9936a0ea3d12809ae8243396fa0000000710107a0002b28a46b9a600020f0cf63acc000198821d80000003e80c77be4e000193c19686945df3f2c90085e80001b4a00029d46248a0e735943200027143d28722bbb98f80000000edc800000000004b229b20be1180e75a9e873cbeea000393c00000004ef1af00000a2e00031c6000000070a00001f5800019a80009238000d3b000000018420000000a87396c6341b9c0000000eea000049f8000a2380000000946749a2768eb99dc13f1cac5e0000000000000302114a561fa0f353f10d050000000043a619be860001dae44584d20000cc80002aa000036a645d9d3e8a186d6744afdc8ed99406d4817e9f5b04ebf204ae0e5963274a0c10bf1236034f05e4acb2a62a0a3ea800000006081aca9f3826000020800003d363e3a9ea5b01c
  | 66 => 0xf326ba0000e488000afc80000003754c5500000000000f9f800068a38d400036d0a2e109800000004be80003150fd800023e6ca320e2dac965a0003e36e8304940000614c91800057a38bc3ee1824ae8b6bec1f8fe6692898e0b02370d0931ba0001dccab000000003c8000028be61f16422ad000010015f0b051c4a259ad14ec63ade23e06d21fb8646c9c129aaeeb244ab582444b08f3e0bea1bc17b2e06cf803369e62a7c2f5000eec6bb624f6960a837121e92a827c30e8f781ca2518000000013400000002da80001a76fb83cfcab400002231f9c99c0d242de88e669ea6feb68397a9f898b4bedb05400000005a696167fc806032a31d0a5880009f80122b033ea47e5224039c014a53280007930fe00001f788bb26d600014a01f20c460000000c340000c0f2150000000066400006d1bb40e560630cde12a20002ba03d5877e0001bd03ff03b6fb8930a38b0000000000000020940000000000000067200000000000589b7cc00000000000000000000087b8000c922d96000000000039f20001cc4da70dce10a0000b2c01509958000000000000029b41469e22ef81870c98340a21e9dc662a000000000004e4934e00000008f700000002c80a4815c20002a4000029aab43a28ad5cb3e2ee62e1e6428000bd900007789128e2836286ff229e40a03827db00006bdbf3a0000b649720000000179ef9a2b6840ba270b1600009dc00000f9279c00009762c3000020d00000000e84f8100000000000c7f80000000eaa0000000bc486ec2fe99ecf9200000000000baeb77cdbf112045431240178000f8810ae000087ebe0bbdc7682b1e0000000eb680005ab8a58000374edce1af2d9d029c61480006de80000000b5495c8d420001d04dd8be30623a21c509191ef9c11c22f70d7a20514148ea00009b6aa1810a9ddaef9b25874c20984d80300314bb06000000000025d8be7a85ee1620be44f80000b8a5a8d08b82cd6b3480f50000000000004c5941c3ca8266249a0b63c29e9ce553b920003c40000283e00005500003d3084c1cd0d5d8104f768000e0f0590ad89aba2ca97d4e7fa110da415f22bc9e626039da6c79862ede2279e00000000000000ddb000001c81163b8032a00030d627f9832aefaaa44e780000000c78d32019cc32ae8ebed2cd81f9981c1af165ce61800067f12ac0a01420c6c25baaae000012d30726c90af00000c90af580009778000a148da80003706f42800060ea0fc65e000000000008590ff4575876cf58ac18d680bb2ced1d9cc7300001692afe00024f633e201e0000000f300fd6583ba3e6482a523f4a9cc536adaa1b704d4c098f0c7af8288a7c379e3869826cb73e8a000000000024000000000000000000000000003b6493f800087c161e0002e46afd80000000000f2c0000503b7e20e622a48e30dde0
  | 67 => 0x4c02d02b7739520000000000250a09007e48268aeedd7123011d80000000000bd4abe85152cf6c9f867677d367c3c88736000215c50d37acf03800015625ac8d2946a4790df6f6ea5621e68000adf20d200018ca61da20854c800039d000091811d400034d2e628000000000000015ba0003ae40000000000320c000134005000cae8890ca0811ffaf8aa04a2cda1806b0ad4023eb4042b6000001f80002ee114403a18ba22f255e64e9bbc000000000000000128e4e8a38000d840000000300034600006e500001861594000000000001d0000124200001a600000000002a280ca0000340800000000000001ae262a800006c011000017f21c5958812391bcca2800002d10e08ddafb2681800044204d8efe895200028fc0bd80002b6ba1ee103c0ca9a85d66e79408f3a9b0e00011f2792000060c000057f049200021d44a31490e5a01f01aba99838722e2ed80000b94b75addcb24ed888c624fb93f8cc29cba5659012fac39d200016e80003e140f00000d209ff000038baa6c09ce0001eee8f1229678c8000985bc5ac848000000198e000000016e8000725b7f23033d5a543bac60001ccc3160000dd580000000ec8f120a7a00033e8bac07425278000fa792b000000000000000d183a2000025d237e8f28dd805923c5a5d09758000000000038b9c82dd61c34c2b38b6c58be0e6af800000006900000cf0000000000000000003c240003db059b29364c824f400000000003c22d5f397c000103247d00004772d9849e8a641f498105d98fc29f20000cb28000d2980006af0b4000018620003214000000032e800044f0000000000000008b05ee000000000000000474b0c29b80000e10d78a444aa02a5c000224ed6114e60002cb21ee36ec8fc2bc40000bb47ddb92c0000fcc0ba15f4a1238c808f808200022320001d6200029feaf03c380002a2ac773b380001f6084d8000000099afbfba3c9cd9d3290da032e55be0a0002a1033695408740c9a71e0eb200000000003d1a63080002ec2abe7b30000516240cb68930c3ac36245c62beab368000605a6d44cd80000000000d138000000000000000000000000df4800000007ccb3780006010000000000000025e4b0480000000000d4c800000000005fe2eb892caf7651b8248a2104a00000000337a05e0002a50e2495020000000896399a3a5ab04d990e044b799daeb7248c0003b0cdbd997c00000000003bbe34695a88b9aa58cfc0a8c00027ae85d8f6400000000002dba7e899bc0003ce8000053a00000000000000de43354aea80000000000eac8000000000000000006c9a14000039da2cf884013b0de2ef0a31a3ffb830ec92d3a140093819700007172e9603991ac9d9a19ec1c15283cea22a27d03c81428f26f0b089c064000000026fc00000009a336b00002b60bbf0000381b
  | 68 => 0xa9c65080004808d3ee138000000095600022beca98d32567a198137800008700004668000000245666626ac338000000000000003e1a0ff97b0bf520a8d2f0b304faa496fc6af1e2442a9a20b3366f670356d039476555a3b0da0a8ea0003e986c4231c0c507685f4077c0000000fb52ec8fc31c2eea1bb26000347caa3a3b236200005b680005270000178388aa0f35b0999ac4414cb09cc508e1e7198000e50beae8a487005aeb4680002a46703a2b80002e26000029625880002412362e510984a3022bced637340002d7e5bd97284d100000002be61ae8ca66fbbbaca1d23ce8789d74b4400007fdadee00000008609ef4e4499ac00021beb2d2750b06a87054d023c2c09dd801f27308c40000000001e000019e000211eef7800000000000000000e0ea81ac218000000000000034c200036e2440800000038e600021acf6e05fa058143825287447aa0fba0001f8238a80009aba2f6ed1000030d81c400000006b23a9a000000074780002c881385a082c291a80000003c546a9841620c20fa00010883c232f40000bfcc29a0ba12abc4a635800000033da00000000003652152ad7a0000000d848000000106453c864e000073aa2c324282f21000002f6253e1e9200000000000000000000040da3280000a9e8a5254c000000075b800000023ec0001f006c80ba6424101035180005b99ec2ca700009e400009c6b536000378285394ccbabb4eae0d07f20880000b5bbb5e7f4800003a80000a782b20000000c3600000001c9400039dc67814f07e1b5944a93dc8060917879fbcdccdc8000fc50ee284f27f2f6f0b343df8000f14845c00005dc00000000001bba000380426517c4109820c714000000014527aea4ea000122e1a8905ac09315a00027960000000f91238a339800021b371400000000000000f7f800000016105f20a1e29c9f803b0800052320e800029a00002b7458693e000008680002e2a2ab80000000000bbd0000ccf80008620000188a13a515afaa588093a5cc361e000000000000000001e5c347280000010a200000f0000138ac62bf22978a474eb500000001cc60001d68445226a3478c723fb0e6e4062d228fbb49edd29e6c74bac863c6a73e54c1696a8f80004369cb60001fd455416f4b4c2f56bbcaabc3e0a04c7399dc80003b508c491ae6aa88a2a1eb36c2d30000d999a2a00000003058000000000000000002b38000d9580002e60000000053815f91b20002816e568000f7002785c3269c00013a24e99a4c1db80002753e640000848000309e000000079111840000000000000000012187e59c9c0002ff0efc3eba8059f0800000003182acc000345a95fae720003b7ca0d17a80959828a71000052c10bc652bc1aba995ee944a332a6eb62a3bf17ea8702fdad6fa29c0b2994e6190eda0000aa8e140000
  | 69 => 0x80791772000292200006a00001e3a6d0209c41d3578000326eb319d1c667293a6ffa55ce0196de4be2dac68635ce624362083c8a0ab019c8ede7307a3d31e3ef65acf49a9998a721343c2fa27c022f967e1b531a0f8d2d9eb571a8476586389fd0a2ac30b6f0f7cb5fa171b68e3230520d382b2257faa1ea35b288f9e9558d5418facc91684b4aacb881d2a84a89045eb8d890c1c907d84f0046200033868de0a16d718000d74969e000000083d9aa8d5734f4fbe2b3c000392a0002c668448fa21ab0e36f36ae2829087809918d4e24a2dda000096800011180000000bd80eec07eb46aa1500000000a9a1ea931c00000000000000ac6b4cce22050681f00008e90000df70000000259e4ed80008eb372ec892aacf6380006c89d40616a6c6a77259c970800079e02ccae300003dd07c039a9e14c06081835b0000f740c86559a102a19336a90ea50e69700004bc15ce8a83cf62e1a358000336e0001ec81fd2e322aeb6dc42024c880f1aaeafba9bc67d986a43b24d2000000090fa812c0d8000ebe11f02f484be5640e6444b241467799821c1a97a7dc8776e470000e4411700002a7e000000000033c60000b0ed8baf9a8b796b6451917c9b3b3b66fd989437a86d00002d7cc6fb2620d02398bf9941ef1998740000bc022d250873b12bc8b583680bf3b049312eced76166a00000006b900c66c5a2c8f05218a133802000000005210000a5a0000e7a10f4000144acec05c812c968caa5b2e420d843e38c1802cbf1e0c9a80dd8f2809c082d134c51c0298f288820e25bef6845b29e00038fca268d84628886e7ef8000ce02db63d6800000000000000000f2f8000ee5000000000006e32220ab2a47000000007f8b8ae827800028600008c98000a9c00004b4b348cc48000000000000000000001fc4922800068ba5e85bc2afc0000fa81a2000000008b6000281e95f33cc52580000001a16c269cce53a975617619a89f404989aaaed828009ac89e8fdc38914b6edc000021c800076fb7421512e1a000097a0003a740002a6000027b60001e5afae00007058f720002ce28fd00003fe1e1e2919db439f1d16d6f1e108220000000000000000000000abe39280001180000e10800000039749290232f3cb51cf5b1fda0e122169e3317a7eaa9b6a159a8c4881980e92147a56b2b0204c139cce799508a31b78be918a6c1f324c537a2029403da8738bcc485602b423700005a22ed20002b9c00000000c49d3400000007ba80000001298eaba984c88064281e0000c6394ae2198b1a000353c1471f341b6800000016f24cb29c00000000d59000000035e0000333c00003f2000233ab6080000000000f5f80000000000199b8a8000000086a0ae800001ba0d535d4706a7fa69c9938d120f3800026cae540aea0c090aa000000037f00000000000000
  | 70 => 0x90000bd21ed800000007ac8000abb03ba5ea9cd89ac80007a7976e00010c206b06a4c2d818099a200e741905600010e414f8ef22eeb6685cb02d23433e1c86380001612124a6a346400021189f515b04c2060e0003df60001c5829d308200025f2a1a8000523ae84e3400000000000f4bb71614f00000a1000000034b400000000ad80aa00039202d4b0a0fc591faf729fe45171e2a4efb608b8831b2436000022382248be00004ae90000001e2e00009da53d3334af8ab16e2e000819495bc40b317600000000003e084821796bf0991c0002038315a26e2ff9f2c1b81aeeb3bab000048c38584b7501930fd40003d560000000cbe06640000000768a6b4000399021800007b4be1e0000000000000095eb7b679c00006850000000000000000005c237664d78be074015085be124435c22b43c1a32278d8b685229d7c279bbea42295848b839982a0000076290d41d8000034a8074a8c820808e22a681e80840b6000054b0000d4e0000000116296d2fde000097cea22b0c6293d86a1415a49e29078000000000003202e883442029b5406fb99ca9b80000000000c0200008dd000000003920002afae149520c8f07dcfc706e253db444000000096833144e8023a0000000ddc3d100002f8cb10a9f4b9408aa00000009b40380def0000bad0000b338000015252290d189cc5e00004300ae44fd800055834703332ea4000000063933d681ba72e000000063d800000000000000e9ef9f04f60000000a3d8000af216a016b85c400031523609e909ea310871800009343a4a9869ed4623000088d800043a8000cc580009ea83f8693a464f250aec3f297980000000b2f01fcc97a1e4b6712788c91fae237ba968b398446d407ba0003b8200000001c3874e00000003688000876000038989ae0002602dbc85a0cef0000000158c3918000000000000000004e60000a1bbe5400022185e33b486172f9262000000d680007f0000000000000000000382351e72600000000184d8f000038800003678e8c8fa00008cd012600000000001f24ab88000d48b40234800008690ea47bcb5dc0838000cf935d0417000000000009b100002663822864be940000000d85058c0002e5aca69f1496403a0dc29c04f220a98000195c0000000186bdf000000000000b4400039aa0001f66d15a9d00000000a263688d5326e417027ace12a0dea8291b4dde13d8000000000037480002f7ea0b8000dda8000d6e80003bd0000ebc0d54000118ae500000e1e8000e498000f5626b8acb800055d07fa32c88629dd9680e7300000000000ce6afc0000120a00038ca743800052d14923e9bf2ebb18000ebb000023d000099d8000fa800d6e27100c00000004afa8c8000294c8c380000002c62a6680002680a840000000966800000006544802760835b34487a80005b7288
  | 71 => 0x5083b0000f4a80009f62decd941142f999ba80000000000153800013aa29f80001872814e2a83f600033fad55a29a2be00000f1b89ed8702c6000000000003fc00000003640000dbf8ac4b6b885a80b9bc693636d2d0a0306e4104e4e630c044cf20acd32b9e4d90140633b000085a8b909f1aec20000000bb716546cf00005cca3ca055b95c5648000ad31c7a000022600012d6000000000000001268000cb105f46ae0c1233d2b2675c25a22c10000f0e8af4dee80008ad897800000009038000000000000031c087a0000000000035da25a0000000000000049380000000000206800065ab53400030fae0091400000000085800032f8496f648000e368000fc7b0940000000000378e6c52b862d60000d0d0000eda0b244d080d0892000008b9ea0f91bc56fa3000000000000000000000009817a800075129fc89b11b8d17aca681aa824ac6319888b1f4abccb0ccb25909abdb1e56a6fabb804d1f880330542fbf0174c7e3284898b9320f80ee825134f2262893e405a94691b1c74ee198bcd6d3a5a86eb77afa39dee000090e0000ab0c0aa910e26290863012065260000ef89338d148000f5332b860511e07b8a4d497e15c81da8000f8b893224787961e231eeea10708c402ddeb908ed01089e727f794c2ada8d14c5f87a28f237aedad80000000000808184600f0e1292b0d66000000000000000000000e4780ac2ddaad41f81ca8c6700006121a36959a6f69c0350c0001e34f5a00002938f7a000000007531d20000000000000000015720000a2098e8000000311667587c400027a4699b9e00000000e3c18de9dea91479da52872280000000000469800049580000002ea0f49000000000005a2999aead8000000082e321000086980000001510013aecc8e02f2a6dc0000bc33b1483ba1687ec2e9200000000002bb600000000000604914800017c394c4c9052c76e000067287d0e7d21f839700006f03b34fbc800000000009018000cab39ee00000007f319fa000000055a00000003cd60000000f840eb437a20da10917d67729c38e1f09e2919b1aa0bb1c54345b4d82e50b9aa8104f80b11fe00000000153020652eb08881889203e30bac00000000000b72cd2be6e0000000e1f8000000000077ea1de5930caa000000000027020000000f08250220a0800d6416c80000000bd023300001be2fb3ade20001b8ab541c2cadb34d6000000000000000001d9e0000000acd1a9a5ff8000000078efc923c04140000d56b8b450280001ef8000000280200000006c60000000000000016bc0001bcc0002eeabde86c4da48eac000000000006fef6d36f8ad9254000000000000030286800004e9720000324082c81aa000085c6868912c429896f318ff20000000c7500001e7051e029815e8598000b6c3c9aa990000bdaa80c0251eb018
  | 72 => 0xb9a000074804800001c08b380000d399a389163dded1317e42812fbc0239eb4de980009a1256a02e3d22000273a0000e62c7280000001380092831e000045a00015f6af18360fb1000000009b6000000000000008498000ac2800041f000000039a284a28fa3ab9138e363146dfdad1c6458e94b63930418093ba58ea6720000000a9a00e200030345b800
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x87c855d9424400117f08bb2848800237e0d76509100246e41aeca1220008ef825d942440050f90b3b084880021fe1576109100143e42aec21220058bc845d842440011bf06bb084880123720d761091004c76412ec212200087c865d442440010ff0fb2884880021f61f65109100347a432e22122009ce4625c442440031f10cb8084880172e19170109100043fc2aed992200287c855db324400187ecb3a664880030f19674cc9100061fb2ae99922000c3c655d3324400195ce9b1664880032b9d062cc9100063c32ce199220018f8865c332440018f0cab8664880021fe15768c9100143e42aed19220018f8865c232440050fd0bbb264880021f617764c9100043fc2aec992200287c855d9324400117f08bb264880162f211764c9100046fc1aec99220008ef825d932440011ef02bb2648800a1f216760c9100043fc2aec192200287c855d8324400117f08bb064880162f211760c9100246e41aec19220098ec825d832440010f90cba864880021fe1f650c9100043ec3eca19220068f4865c432440031f10cb8064880133618d700c9100043fc3ac92822000a5f83592504408f4b906b24a0880029be09649411000536412c9282200087f8758e504400147f08b1ca0881228f211639411000537c12c72822000a6c8258e50440010fb0f314a0880021fe1d62941100051fc22c52822048a3c8458a50440014bf06b14a08811e9720d629411024c3e432eba02202187f87d9740440010fb0fb2e80880062fe1d64901102ed4e41ac92022000aac8259240440930fd0dbaa80881fa1fa1f655011010c3e43ecaa0220008bf8759040440b953906b208088002ab209641011031f1c282c82022000c5f659cc40440018b8cb398808800317d9573101100062e32ae62022005c9e645cc404400193ac8b98808801b56141731011024c3e432eb982202187f87d9730440010fb0fb2e60881261fa1b754c1103dc3f43eca982202187c87d95304400187ecbba260880030f197744c1100061fb28e89822000c3c651d130440b9938c63a260880034e140744c1100064e3a6c69822021c7876941304408f8f0edbaa60880871e1db654c1102ee5c3b6e89822000db071dd130440b9970ec3a260880034e1d4744c1100072c328c69822000b998418d304400187ecb3a060880030f196740c1100061fb2ae81822000c3c655d030440930f90cbae40880861fe1f65c81100043ec3ecb902204987e86dd520440010fd0fb2a40880861f21f65481100061fb2ee89022000c3c65dd1204400187eca3a240880030f19474481100069c280e89022000cac74d892044001958e8312408801a3da1b714811010e3c3b4a09022000c7876dd520440438f0edb2a40880032e1db74481100065c3b0e89022000d38751d120440031f10cb9a40880871d9db6584110
  | 1 => 0xee4282c8880031b1c850591100045fc3ac83222000a9c83590644400155904b20c8880022fe1172d8d1002c5e422e5b1a200087e87d9563440010fd0e32ac6880030fd977458d100061e32ee8b1a2000c3f651d16344001878ca3a2c6880031bd977258d100063632ee4b1a2000c6f651c963440018d8ca392c68800a1fa1f7558d100045fc22eab1a20058bc845d563440011df04baac6880263b2097558d100043f438eab1a2000c3f75dd16344001878ebba2c6880030fdd47458d100061e3a8e8b1a2000c9c74dcd63440018deebb92c6880031b1d77258d1000657ba6e4b1a2000cac74dc963440018deea392c6880031b1d47258d1000657ba0e4b1a2000cac741c9634400199ee6392c688003391cb7158d100043f438a0b1a2000c3f7414163440fd878e8282c6880031bdc85058d1000636390a0b1a2049c7970194634400187ecb3a0c6880030f1967418d100061fb2ae831a2000c3c655d063440011bf0eb18c688002a72116318d1000566412c631a20048be849db43440010ff0abb6868800a1f21576d0d100254e41ac9a1a2000aac8259343440010ff0abb4868800a1f2157690d1000c7c432e121a200287e85dd943440010fb0bbb286880021fe157650d100143e42aeca1a20008bf845d943440011bf06bb286880023be097650d1004c76412eca1a20048bc87591434400953906b228688002ab2096450d100043fc2aec21a200287c855d8434400b17908bb086880123720d7610d1000477c12ec21a20098ec825d8434400117b0fb2086880031e1967010d1000c7c432e021a2000c78655c0434400b970c8b8086880133618d7010d100043ec38a1312200287e86dd562440010fd0fb2ac4880021fa1c655891051e3db80cab122000c3f65dd16244001878cbba2c4880030fd9474589100061e328e8b122000c5f65dcd62440018b8cbb9ac48800317d9473589100062e328e6b12200287e87dd5624400d0fd01baac48801a1f20375589100045fc22eab1220058bc845d562440011bf06baac4880123720d75589100047dc02eab12200087e871d5624400187eebba2c4880030f1d774589100061fba8e8b122000c3c751d162440018beebb9ac488003171d773589100064fba6e6b122000c9c74dcd62440018beea39ac488003171d473589100064fba0e6b122000c9c741cd6244001958e9b92c488003331cf72589100066a39ee2b122000c7875dc162440010fd0e282c4880030fdd050589103f61e3a0a0b122000c5f7314162440f78b8e6282c48828f1edc0505891024e3cb80ca31220008ef87588624400155908b10c488002b320d621891024e3cb80a0312200087f855db42440050f90abb684880021fe1576909100143e42aed21220018f8865c242440050fd0bbb284880021f61776509100043fc2aeca122002
  | 2 => 0xf65c81200061f3aec99024000c3d75d93204800187cea32640900030f5d464c81200071c280c99024006e6b629432048001c70ca326409003b1b9db6588120006573b6c91024005cae761922048001cd6cbb04409001a3e20175590200345e43aa8b204006ab880551640800d1b90ea9ac61001a2f21d6450c200346e43ac6a1840068f8805d5610800d1e90ea8ac21000237e0d76504200246e41aeca0840068bc8759141080139c8e4b0a82100022fe11764c42002c5e422ec98840068dc8758d31080139c8e4b0a62101db4e140744c0200363d286ec9004006c7850dd920080e9a70a03a240100031b1d7764802003637286ec9004006c6c50dd920080018deedbaa40100032bddb744802000657bb0e89004000c7875dd920080018f6edbaa40100032eddb74480200065dbb0e89004000d38751d1200800d2f100bacc90801a3e20175592100345e43aa8b242006ab880551648400d1b90ea9ac7080162fa137258e100045ec26e4b1c200287e85dd943840010fb0bbb2870801a2f21d6450e100346e43ac6a1c2006c3e505d3628400d878a0ba6c50801b1794173d8a100362e282e7b14200687e805d6628400d0f900bacc50800b1b9d55298a100347643aa4b1420068bf87592428400d974e0b24850800a1fa177650a100043ec2eeca142005c3e645d4428400187aeab20850801a37e1d638ca100366d382c7194200287e85dd932840010fb0bbb2650801a3ea03764ca100262f31aea1942000c5d7558c32840eda70a03a261080034e1d4744c2103a69c280e89042000c7875dd92084001a70ea3a241080067c205734821001d3b436e3b2a20a8a7a80dd365440434f301ba6ca880030f5d074d95100051fc22e7b2a2000a3c845cf654400147d0839eca880028f61073d95100062eb98e7b2a20a7a7a801cf65440434f30039eca880028fe1172d95100051e422e5b2a2000c6d721cb654414d4f500396ca880869e60072d951000c7cc06ebb222049c797014364440010fd0fb2ac8880021fa1c65591100062fb2ee6b222000c5c65dcd64440018beca39ac88800317194735911000637b2ee4b222000c6c65dc964440018deca392c8880031b19472591100143f43eeab2220008df835d564440091b906baac8880023be09755911004c76412eab22200087e871d56444005878eb2a2c888297271ce54591100145e43aa8b2220a4c9c73551644400157100aa2c88800317dd773591100062e3aee6b222000c5f751cd64440018b8ea39ac88800327dd0735911000637baee4b222000c6c75dc9644400199ee7b92c888003331cf725911000637ba8e4b222000c6c751c9644400195ee8392c88800333dcc725911000666398e4b222000cae541c9644400195aa8392c8880021fa1c50591100062fb98a0b22207bc5c7314164440018d
  | 3 => 0x8b0a4000c3c75d91614800117d0e322c2900030fdd464585200061e3a8c8b0a4000c5f65dcd61480018b8cbb9ac29000327d9373585200064e326e6b0a4000c5f651cd61480018b8ca39ac29000327d9073585200064e320e6b0a4000cd4611cd61480010ff0abb6829000a1f21576d052000c5e422eda0a400287e85dd941480010fb0bbb282900062fa1f64505200043fc2aed98a400287c855db314800117f08bb662900162f21176cc5200143f42eec98a400087d85dd9314800b17d09bb262900022f613764c5200073210eca90a40008be86dd1214800187ecbba242900030f19774485200045f430e890a4000c3f651d12148001878ca3a242900c22fa1f64485201ac5e43ec890a4000ea421d91214806b17d0e32242900162f21c64485200062fb2ee690a4000c5c65dcd214800193ec9b9a42900032719373485200062fb28e690a4000c5c651cd214800193ec839a42900032719073485201466a308e690a4000cd473d8521480018f0cbb8242900031e194704852003637b14ed2824074a3e86d92504800187cedb24a0901970f9c3649412032f1d386c9282400087f8759250480cb47d0c324a0900030f9d864941203a61f380c92824074e3a7019250480010ff0eb1ca0900028fe1163941202451e422c72824000a778158e50480434e902b1ca09000a1f21676d01200043e432eba024005c3c645d740480010ff0fb2e80900021f61f65d01200061f3aec9a024000c3d75d93404800b958c939680900021fe1576501200143e42aeca02400087e86dd54048091878c9baa80901fa1fa1f65501202443e43ecaa024000c3f75d914048001878ebb2280900032bd9072501200062fb2ce62024000c5c659cc404800193ec939880900172719273101200062fb2ae62024000c5c655cc404800193ec8b98809001727191731012002d5c432802024062e38655004048001b32e6a00809000a1f21676cc1200043e432eb982400087f87d9730480010fb0fb2e60900030f9d764cc1200061ebaec99824000c3e75193304800187aea32660900032b19272cc12000656322e59824004ccc635cb30480010ff0abb2609000a1f215764c1200045fc22ec98240058bc845d930480031e902bb260900021fa1b754c1203dc3f43eca982404787c87d95304800117d0dba260900030fd97744c1200061e32ee898240008be861d1304800187eca3a260900030f194744c1202e45f43ec8982405d8bc87d91304800187eebb2260900030f1d7644c1202ec5f438c898240058bc87191304800187eea32260900030f1d4644c1200061fb2ce81824000c3c659d0304800187ecaba060900030f195740c1200045fc3ec818240008bd87d90304800b17f0e32060900022f61c640c120006ccba2601824000e9b644c0304800d0f90cbae409001a1f61
  | 4 => 0x44800b17d0e280c8900022f61c50191200054f418a03224000a9d83140644800155d04280c890002ab60850191200055b408a03224000ab58114064480e987d0e280c8901d30f61c50191203a70f418a03224074e1d8314064480e9c5d04280c8901d38b60850191203a71b408a03224074e3581140644800147f0a900c8900028f215201912002c5f43e2032240008bd87c40644800147d0b880c8900028f617101912000566c1063b1a4000ad9800c7634800187ecb3a4c6900030f1967498d200061fb2ae931a4000c3c655d2634800187cebb24c6900030f5d76498d200061f3a8c931a4000c3d7519263480010fd0fb2ac6900031d1c76558d200043f438cab1a4000c7471195634800187ecbba2c6900030f1977458d200061fb28e8b1a4000c3c651d1634800117d0fb22c6900030fdd76458d200061e3aec8b1a4000cb471d91634800117d0e322c6900030fdd46458d200061e3a8c8b1a4000cb47119163480018eecbb8ac6900031d1977158d200065bb26e2b1a4000cb464dc5634800117f08baac6900162f2117558d200047bc0aeab1a40018f4815d5634800187eebba2c6900030f1d77458d200061fba8e8b1a4000c3c751d163480018eeebb8ac6900031d1d77158d200065bba6e2b1a4000cb474dc563480018eeea38ac6900031d1d47158d200065bba0e2b1a4000cb4741c563480019aee638ac69000339dc87158d200143f42ee0b1a400087d85dc163480010fd0e282c6900030fdd05058d203f61e3a0a0b1a4000c777114163480938e8e2282c69000237e1d6318d200056a40ac631a400087f855db43480050f90abb686900122f21176d0d200043fc2aed21a400287c855da43480050fd0bbb286900021f6177650d200043fc2aeca1a400287c855d943480011ef02bb286900063d2057650d200245f43ec8a1a4004a9e83d9143480010ff0abb0869000a1f2157610d200063c32ce021a4005cb8649c043480131f10cb8086900031e1957010d2002e5c322e021a4005cb8649c342480018f0cbb8284900031e19470509200065db20e0a12400287c859d842480630f90cba884900170f19175109200043fc3eca212400e87d87d94424800187cebb2084900030f5d764109200045f434e99924000c3f659d33248001878cb3a664900022f21974cc9200061fb2ae99924000c3c655d3324800117f0fb2664900022f61f64cc92002c5fc38c999240008bd8719332480018f0cb38664900031e19570cc9200143e42cec192402987c865d432480010ff0fb28649003a1f61f650c9200061f3aec81924000c3d75d90324800187cea32064900030f5d4640c9200143f436eab0a400087e87d9561480010fd0e32ac2900030fd9774585200061e32ee8b0a4000c3f651d16148001878ca3a2c2900022fa1f64585200061fbaec
  | 5 => 0x3a1f61c21d95200051f42043b2a4000a3d8408765480014bd0610eca900029760c21d95200053d40043b2a404ca6e82dc365480010fd0f886ca900021f61f10d95200051f42621b2a4000a3d84c43654800187aebaa6c890002ab60b54d91200161e3aca9b2240028bf87553644800147d0a20ec8900028f61441d912000716c10cbb224000e2c6594b644800147d0b30ec8900028f61661d91200051f430a1b224000c3d751d7644800153d063aec890002a760c75d912000557410ebb224000aad821d7644800193ee739ec8900022fa1f53d91200045ec3ea7b224000e1f5394f644800117d0fa96c8900022f61f52d912000717a94a5b224000a3e859c7644800147b0b38ec890002aea0071d91200055cc00e3b2240008be87147644800117b0e28ec8900022fa1c31d91200045ec3863b224000a3e850c7644800147b0a18ec890002aba0831d912000556c1063b224000aba800c764480015730018ec8900022fa1c21d91200045ec3843b224000a3e85087644800147b0a10ec890002a7a0c21d91200054ec1843b224000aba80087644800147d0bb86c8900028f61770d91200054f41ee1b224000a9d83dc3644800147f0ab86c8900028f21570d91200071da84a1b2240008be87143644800117b0e286c890002a7a0c50d91200054ec18a1b224000aae82143644800155b04286c890002ada0450d91200055ac08a1b224065c3e8714364480cb87b0e286c89019787a0c50d912032f0ec18a1b224065e2e8214364480cbc5b04286c8901978da0450d912032f1ac08a1b2240008be87c43644800117b0f886c8900028fa1710d91200051ec2e21b224005c3c645d6644800187cebb24c8900030f5d764991200043f43ecab22400087e87195644800117f08baac8900023ee0175591200061fbaee8b224000c3c75dd164480050fd0bb82c8900021f61770591200063c3aee0b22400087e8714164480018f6e0282c8900022fe1d64191200051fc2ac83224000a3c85590644800187cedb28c8900022f61e65191200045fc3aca3224000c3e761946448001c5b04328c8900038b19652191200051f42cc23224000a3d85984644800147d0c280c8900162fa1f53191200045ec3ea63224000e1f5394c644800155d04298c890002ab608531912002c5f43ea432240008bd87d486448001c5ea5290c890002aee0152191200055c402a43224000aae82d44644800155b05a88c890002aea0251191200055cc04a232240058be87144644800117b0e288c8900162fa1c31191200045ec38623224000a3e850c4644800147b0a188c890002aba08311912000556c10623224000aba800c4644800157300188c8900162fa1c21191200045ec38423224000a3e85084644800147b0a108c890002a7a0c21191200054ec18423224000aba800846
  | 6 => 0x4d3741062b2e4000a6d820c565c80014f50018acb900029e60031597200051fc22e0b2e4000a3c845c165c80a34df04b82cb900021fa1f10597200043ec3e20b2e4000a3e84c4165c800147b09882cb9000b0f9d654d932052e4f39ca9b2640028bf8755364c814993ce6aa6c990002ae20154d93200043ec38a1b26407bc5e7314364c80018bae6286c9900021f61c50d8f203f61f3a0a1b1e4000c3d7414363c800187ccb3a4c7900030f5967498f200061f32ae931e4000c3d655d263c800917908bb68790012a7a0f64d0f2004c6fc3ac7a1e40098bf8759243c800917d0fb228790012a7a0f6450f200045fc3ac821e4000c3e659d332c800187acb3a665900030f99574ccb200061eb2ae999640018bc8759141c80031b90eb1a63900279908565487200061f32ee890e4000c3d65dd121c800187cca3a243900030f59474487200062f32ee690e4000c5d65dcd21c80018bcca39a439000317594734872003637312ed2864006d6a205da50c80010fb0fb24a19011e97a0f64943200052ec1ec9286400087d87d8e50c809147d09b1ca1900028f61363943200043fc32eba06400087f8759740c80bb53d07b2481900021f61b75503202443f43acaa06407e87c8759540c800117b0fb208190172a7a0f641032032f1c286c82064000c5e659cc40c80018bacb39881900031799573103200062eb2ae62064000c9f645cc40c800b938c8b98819001b5614173103200043fc32eb986400087f8759730c80010fb0dbaa619011e1fa1d654c3203dc3e43aca9864000c3e65dd130c800187acbba261900030f994744c3200061eb28e8986405cc9e631d130c8001a70a03a26190003271d1634c32004e66392c69864000c3e659d030c800187acb3a061900030f995740c3200061eb2ae818640068bc87551648800147b0a20ac91001a3721d5358e200052ec2862b1c4000a9d840c5638800159b0418ac71001ab6a003158e2002477c32e521c4004cce635ca43880050fd0bbb287100021f6177650e200345e43ac8a1c40068dc8758d438800117b0fb2085100132798d74cca200064eba2c799440068f487545618800317908bb683100022f61f64d06200143f42eeca0c400087d85dd9418800317d0fb22831000a1fa17764c6200043ec2eec98c4000c6e755db208800dcd4a0bb641100031b5d975c822007537436e5b2a4000a3e84987654800147b0930eca900030f5d074d95200051fc22e7b2a4000a3c845cf65480018bae639eca901329ea0372d95200051f424e3b2a4000a3d849c765480954f50038eca900029e60071d95200043f43883b2a400087d8710765480010fd0e18eca900021f61c31d95200051f42063b2a4000a3d840c765480014dd0418eca900029b60831d95200053d40063b2a4000a79800c765480010fd0e10eca9
  | 7 => 0x9e7690c404c00b5710ca00809818b8e195401013023e2f3b6cb1826047e5b60d96304c0bb93cedb246098017279d8648c13002c5f43ea532060008bd87d4a640c001c5ea5294c8180162fa1c51990300045ec38a332060058be87086640c00117b0e10cc8180028fa1421990300051ec28433206004a9e83086640c00153b0610cc81801aaea0021990300055cc00433206006a3e85d42640c00d47f0aa84c8180162fa1f10990300045ec3e213206000a3e85c42640c00147b0b884c81801a3e20175590300345f43ea8b206000c3f75d51640c00d1790eaa2c81801aae20154590300051f42882b206000a3d85105640c00187eeb3aac818002aee0175590300355c402eab206004a9e839c9640c00147d0a392c8180028f61472590300045f43ea4b2060008bd87d49640c001c5ea5292c818012a720d715903000557c12e2b206000aac825c5640c00147d0a38ac8180028f61471590300045f438a2b2060008bd87145640c00117d0e10ac8180022f61c21590300051f42842b206000a3d85085640c00953d0610ac818002a760c21590300355d40042b206000ab980085640c00d47d0ba82c81801a8fe1550590300045f43e20b2060008bd87c41640c00147d0b882c8180028f61710590300045fc22e331060058bc845c6620c00d1d90ea92c418013279cd64908300064eb22e72106005c3e645d4420c00187ceab2084180030f5d564108300347a43aa2b0860008ef825d9410c0131d904bb2821801a2f21d64504300264e39ac8a086000c9d64dcd410c00117f08bb242180162f211764843016c6fc1aec90860008bd86dd1210c00117b0c3a242180022fa1e644843002c5e43cc89086004c9c73991210c00117d0eb2242180022f21d64484300264e39ac89086000c9e64dcd210c00193ac9b9a4218013331ce62484300347643ac490860068bd845db400c00d8f0a0bb680180170f99175d00300061f3aac9a006000c3d75593400c00dc70a0b26801801a2f21376500302461f326eaa006000c3f75591400c001878eab228018003171d7764c0300064fc26ec9806000c9c84dd9300c00d8bca1bb2601801b17143764c0300062fbb6ea9806000c9f76dd1300c00193eec3a26018002a7a1d644c0300054e43ac89806000e1f75591300c001c38eab22601801b27dc1644c0300274db82c89806006e1e50591300c00dc38a0b22601801ba6881644c0300061fba4e8b2e4000a7b805d165c81574f100ba2cb900028fa1373597200051ec26e6b2e4000a3e849cd65c800147b0939acb9000317dce73597205553d404e6b2e4000a79809cd65c80014f700b8acb902a69e20171597200051f420e2b2e4000a3d841c565c80010fd0e20acb900021f61c41597200043f43862b2e400087d870c565c800147d0818acb900028f61031597200
  | 8 => 0xe2322c4980031dd9771589300063a32ee2b126000cb764dc5624c001968c9b8ac4980023be1d62189300057240ac431260008bf845c4624c00b17908b88c4980021fe1576d09300143e42aeda1260098bc845db424c0010ff0abb4849800a1f215769093002d4e432872126000c9e7650e424c0050fd0bbb284980021f61776509300143e42cec212600087f855d8424c0050f90abb084980021f219751093002e1e322ea212600087f87d94424c0010fb0fb2884980030f9d764109300061ebaec82126005c9c645cc424c00b5390ca1884980172e192701093002e5c322e02126000d99435c0424c0050fd0dbaac2980021fa1f65585300043f438cab0a6000c3f65dd1614c001878cbba2c2980030fd9474585300061e328e8b0a60008be87d91614c00187eebb22c2980030f1d764585300045f438c8b0a6000c3f75191614c001878ea322c2980031bd9772585300063632ee4b0a6000caf64dc9614c001958c9b92c2980031bd94725853000636328e4b0a6000caf641c9614c001958c8392c2980033918472585300043fc2aeda0a600287c855db414c00317908bb682980172719173d053002d4e43287a0a600287e85dd9414c0010fb0bbb282980062fa1f645053002d4e43286a0a6000c9c7650d414c0010ff0abb6429800a1f21576c85300045fc22ed90a60058bc845db214c0050fd0bbb242980021f617764853002c5f426ec90a60008bd84dd9214c00b17d093b242980022f61276485300246e418ec90a6047c5c73d95214c00117d0dba242980030fd9774485300061e32ee890a60008be861d1214c00187eca3a242980030f19474485300045f43ec890a60008bc87d91214c0bb938e7b2242980022fa1c644853002c5e438c890a605cc9c73191214c0018becbb9a42980031719773485300064fb26e690a6000c9c64dcd214c00d8bec73b4a0981da8fa1b64941300061f3b6c92826068c3e70d92504c0d1c74e1b24a0980021fe1d64941303451f430c92826000c3e76192504c0edc3b06324a0981db0f9c064941303b71d380c9282607bc5e7690e504c091c38c921ca09801a9721943941303062f3b287282607b87c865d7404c00b878c8bae809811e1fe1f65d01300043ec3ecba026000c3e75d93404c00187aebb26809801aa721943d01300346ec1ced2026006c78509da404c0b993ced21c80981a3c614243901300043fc2aeca02600287c855d9404c0f70fd0dbaa80981230f19375501303f43f43ecaa02604787c87d95404c00187eebb2280980030f1d764501302ee4e39ec8a02600699c8750d404c00d5390ca1a809801ae620143501305678c28286a0260068dc839d8404c08f8bce7b288098177279cf64101300062fb2ae62026000c5c655cc404c00193ec8b988098017271917310130004cec3c86202605dc
  | 9 => 0x50d913000557410a1b226000aad82143644c00156d02286c898002ad60450d91303461f438a1b226068c3d87143644c0d1c3d06286c8981a38760c50d913034717410a1b226068e2d82143644c0d1c6d02286c8981a38d60450d91302ec5f43e21b2260008bd87c43644c00147d0b886c8980028f61710d913002e1e322eb3226000c3e75d92644c00187aebb24c8980021fa1f65591300043f438cab2260008bf845d5644c0011f700baac8980030fdd774591300061e3aee8b22600287e85dc1644c0010fb0bb82c8980031e1d770591300043f438a0b226000c7b70141644c00117f0eb20c8980028fe1564191300051e42ac83226000c3e76d94644c00117b0f328c8980022fe1d65191300061f3b0ca3226000e1d83194644c15bc7660328c8982b78e0c065191300070fb2ae63226000e1c655cc644c001c38cb298c8980028fa1661191300051ec2cc23226000a3e86140644c00b17d0fa98c8980022f61f53191302e70f29ea63226000abb8054c644c00157100a98c8980162fa1f52191300045ec3ea43226000e2f52948644c00157700a90c898002ae20152191302e54f418a43226000a9d83148644c0b953d07a88c898002a760f51191300055d404a23226000ab980944644c00b17d0e288c8980022f61c511913002c5f4384232260008bd87084644c00147d0a108c8980028f61421191302e54f418423226000a9d83084644c00157500108c898002ae600211913002c5f438a032260008bd87140644c0b953d06280c898002a760c501913000557410a03226000aad82140644c00156d02280c898002ad60450191303b61f438a03226076c3d87140644c0edc3d06280c8981db8760c50191303f70f398a03226076e1d73140644c0edc5d04280c8981db8b60850191303b71b408a03226076e3581140644c0edc74e0280c8981fb8e5c0501913056f1d980a03226076e3830140644c00147f0a980c8980028f215301913002c5f43e2032260008bd87c40644c00147d0b880c8980028f617101913002e5c324e1a1a6005a9e86d92434c00193cedb24869800387d946490d300070e328c921a6047e1c43d95434c0018f0cbb8286980031e1947050d300065db20e0a1a6000e1f65191434c0b9b36e838286980123e60375d893000566c1843b126000ae980087624c0f78f2e0286c4980030fd9674989300061e32ce93126000c3f655d2624c001878caba4c4980030f9d764989300061ebaec93126000c3e75192624c00187aea324c4980021fa1f65589300063a38ecab12600087e87195624c0018e8e232ac4980030fd9774589300061e32ee8b126000c3f651d1624c001878ca3a2c4980022fa1f64589300061fbaec8b126000c3c75d91624c001968e3b22c4980022fa1c64589300061fba8c8b126000c3c75191624c001968
  | 10 => 0x216600287e855d842cc0010ff0cba885980021fe1d6510b300043ec3aca21660018bc8759141cc009938eca1a83980022fe11764873002c5e422ec90e60068dc835d921cc0098b8e6b2a43980030f99774487300061eb2ee890e6000c3e651d121cc00187aca3a243980031799773487300062eb2ee690e6000cac7498921cc009998e731243980063b21d6248730006563a2c490e6004ccc7358921cc0035c902b124398163175d943943300043fc32eba06600087f8759740cc0b917f0eb26819817267e1d43d03305878c28287a06600087d86dd540cc0910fd0eb2a81981fa1f21d65503300262f39aca2066000c5e655cc40cc0018bacab98819817327d91731033002e4e322e62066006d58505cc40cc00d1790eaa2c9181762fe1d64d0e30034bc402eb314600687e805d6628c00d0f900bacc51800b1b9d55298a300045fc22eab1460058bc845d5628c00d1f100baac5181970f9437458a3032e1e286e8b1460068ec87549628c0bb93ce7b2485180172e1917010a300347a43aa2b0c60018bc845db418c00317d0fb228318177271cf645063000d5b40ec8a0c60008bf845db218c00b17908bb6431800a1fa1776486300043ec2eec90c60008bf845d9218c00b17908bb2431805697a1b73d95300051f424c3b2a6000a3d84987654c00187ae83a6ca9811e97a0c74d95300052ec18e9b2a60afa7a801d3654c08f4f3003a6ca981529ea0373d95305753d406e5b2a6047a7980dcb654c00147f08b96ca980028f21172d953000636b90e5b2a6000a3e849c7654c00147b0938eca9812e9ea0071d953023d3cc00e3b2a600087e87107654c0010fb0e20eca980021fa1c21d95300043ec3843b2a6000a3e84087654c00147b0810eca9811e97a0c21d95300052ec1843b2a6000a7a80087654c0014f30010eca9811e1fa1f10d95300043ec3e21b2a6000a3e84c43654c00147b09886ca980030f5d754d91300054ec1ea9b226002c3c75953644c00517f0eaa6c8980028fa1441d91300051ec2883b226000e1d83197644c001c38cb29ec8980028fa1661d91300051ec2cc3b226000a3e86143644c00187aea3aec898176a7a0c75d91300054ec18ebb226000aae821d7644c00155b043aec8980022fa1f53d91300045ec3ea7b22605de1e53d4f644c00147d0b396c8980028f61672d91300045f43ea5b2260008bd87d4b644c001c5ea5296c8980028fa1671d91300051ec2ce3b226000aba801c7644c0bb5730038ec8980022fa1c51d91300045ec38a3b2260008be87087644c00117b0e10ec8980028fa1421d91300051ec2843b22605da9e83087644c00153b0610ec898002aea0021d91300055cc0043b226000a3f855c3644c0014790ab86c8980038ed4250d91300045f438a1b2260008bd87143644c0bb53d06286c898002a760c
  | 11 => 0x100011bd0e10ac6200023761c2158c400052f42842b188000a5d85085631000b53d0810ac620002a76102158c400356d40042b188000ad980085631000d4bd0ba82c62000297a171058c400052ec2e20b188005a9e84c41631000153b09882c62001727a0d7690c4002e4ec1aed2188068c3e505da43100d1878a0bb486201a3879416390c403470e282c72188000c9d639ca431000193ac6b8c86200032758d7090c400046fc1ae331080048dc835c6621000b17908baac42001a3b21d52588402e45fc3ac7210805cc9e7358e421000193f0eb1c8420017a39c9639084032f0f282c72108065e1c5058e421006b17f0cb8c84200032758d71908400064eb1ae121080048bd845db321000993cc6ba66420017279d163cc8400064eba2c79908005c9e7458e321000193ae8b1c64200023de05764c84000c7a40aec9908000c9f7458d321000b938e8b1a6420026b3209634c8400262f31aea1908006978805d432100018bceab186420003175d5630c8402e64fba2c61908005c9c7458c321000d1e90ea8ac2201722f21d63504402e64e39ac6a088000c9c8758d411000bd2ee2b1a822018f87941635044031f0e282c6a088000c9d631c941100013730039282200032758f70504402e64fba2c79888005c9c7458f31100011df04bb262200263b209764c4400346e43ac69888000c9f7458d311000b938e8b1a622000327dd163c844002e4e3a2c790880358bf845d921100011bf06bb242200123720d76484400046ec36e690880008dd861cd21100011bd0f31a42200123721e63484400064fba4c69088005c9c7498d21100011bd0eb1a42200023721d63484400064fba2c69088005c9c7458d211000b958e9312422001a3b21d62484400061e3aeeca008006e3850dd9401000d87ca1bb2802001b0f14376500400061fbb6eaa008006b3a80dd540100b91790eb1a8020173271cd63500400371c282c6a008000c9c8758d4010001c3eeab1a8020003871d5635004002f4db82c6a008000e9b5058d401000dc3ca0b1a802001b8714163500400374c282c6a008006e185058d401000dd3440b1a80200032758c72500403a69c280e4a008000c9d63dc540100e5a70a1b8a80200030fdd274597300252f41ce8b2e6061a5d839d165cc0014f700ba2cb982c69e20174597300051f426e4b2e6000a3d84dc965cc0018dee5392cb980028fa1071597300051ec20e2b2e600087e8710565cc0010fb0e20acb980021fa1c21597300043ec3842b2e6000a3e8408565cc00147b0810acb9801297a0c21597300052ec1842b2e6000a7a8008565cc0014f30010acb980028fe1170597300051e422e0b2e605ea5f835c165cc0010fd0f882cb980021f61f10597300051f42620b2e6000a3d84c4165cc0131d904ba4c598013339cd62d0b300264f3b287
  | 12 => 0x237e0d71189400246e41ae23128009ce4215c462500018f0cbb8284a00031e19470509400245e424ed992800087f855db32500050f90abb664a00263720d76cc9402461f3a6cb9928000c3f655d33250001878caba664a0003275d363cc9400043fc2aed192800287c855da32500050fd0bbb264a00021f617764c9400143e42cec192800087f855d832500050f90abb064a00021f219750c9400043fc3eca192800087d87d94325000157100aa6c2a000a1fa1b75585400043f43ecab0a800087e8719561500018becbb9ac2a00031719773585400062fb28e6b0a8000c5c651cd61500018decbb92c2a00031b197725854000637b28e4b0a8000c6c651c961500010ff0abb662a000a1f21576cc5400143f42eec98a800087d85dd931500010ff0abb642a000a1f21576c85400143f42eec90a800087d85dd921500091bd073b242a00023760e764854002c5e420ec90a8048c3c74d95215000187ecbba242a00030f19774485400062fb2ee690a8000c5c65dcd21500018beca39a42a00031719473485400361fb24ed2828076a3e86d0e50500fd87ceda1ca0a01e70f9d943941402461f3b6cb2028048e3b60d96405000b1790cb9c80a01772718d739014002d4f426a53188000a9d84d4a6310001c9ea5294c620016a7a105198c400054ec20a331880048de8708663100011bb0e10cc62000297a142198c400052ec28433188005a9e84086631000153b0810cc62001ab6a002198c400056cc00433188006a5e85d42631000d4bf0aa84c62000297a171098c400052ec2e213188005a9e84c42631000153b09884c6200162f2117558c400346f43ea6b188000c5f75d4d631000b53d09a9ac62001a3721d5358c4002d4e422a6b188006ad88054d631000b53d0918ac62000297a143158c400052ec2862b188005a9e840c5631000159d0418ac620002b36083158c400356d40062b188000c5f759d5631000b53d093aac620002a76127558c400054fc22eab188005a9c845d563100015b700baac62001ab62017558c4002d4f426e4b188005a9e849c9631000b53908b92c620002b5e057258c400056a40ae4b188000a5e851c963100014bb0a392c620016a72107258c4000666b90e4b188005a9e84d49631000153b09a92c62000393d4a5258c400054fc22a4b188005a9c8454963100015b700a92c62001ab62015258c4002d4e426e2b188005a9e849c5631000153b0938ac620016a72117158c4000567c12e2b188000acc825c563100014bd0a38ac620002976147158c4002d4f420e2b188000a9d841c5631000159d0438ac620002b36087158c400356d400e2b188000ad9801c5631000b53d0928ac620002a76125158c400356d404a2b188000ad980945631000b53d0828ac620002a76105158c4002d4f42442b188000a9d8488563
  | 13 => 0x43f43862b2e800087d870c565d000b47d0818acba00028f61031597400053741062b2e8000a6d820c565d00014f50018acba00029e60031597400043f43842b2e800087d8708565d000b47d0810acba00028f61021597400052f41842b2e8000a5d8308565d00014f50010acba00029e60021597403851fc22e0b2e800087e87c4165d00010fb0f882cba00168fa1310597400051ec2620b2e8004c9e7350e62d000b87ce8b2e65a00030f99574ccb400061eb2ae9996800287e855d832d00010ff0cba865a001a5e201750cb400043fc3aca196800087d8759432d00b917f0cba065a000b0f9d554587400264e39a86b0e805c8bf865d331d000d17908bb243a000237e0d76487400246e41aec90e8005c3c7459521d000187ccbba243a00030f59774487400062f32ee690e8000c5d65dcd21d00018bcca39a43a00031759473487403661ebb28728680068dc8754d63900d1a74a0b8487200172e9817610e403b69c282e021c800687e805d6629000d0f900bacc52000b1b9d55298a400347643aa4b148065d3a505c2429000b974c0bb085201762fe1d6310a401845fc32e22148030cb6615c4429000b37108b80652001a3d21d51586402ec5fc3ac7a0c80018bf865c341900611790eb12832018f4e94370506400143f42eec90c800087d85dd921900011bf06bb243200123720d76486402ec5fc3ac7a04805dc9e7358f409003b47d0dba6caa018acea0374d95403153d406e9b2a8000a3f845cf655009147908b9ecaa01228fa1073d95400051ec20e7b2a8000c5d731cf65501654f50039ecaa01229e60073d95400051fc22e5b2a8048a3c845cb65500018dae4396caa01228fa1271d95400051ec24e3b2a800087e870c765500010fb0e18ecaa01228fa1031d95400051ec2063b2a8000a6e820c765500014db0418ecaa00029ea0031d95400053cc0063b2a800087e8708765500010fb0e10ecaa01228fa1021d95400051ec2043b2a8000a5e8308765500014bb0610ecaa00029ea0021d95400053cc0043b2a804887e87c4365500010fb0f886caa01228fa1310d95400051ec2621b2a8000a9d840c7635000159b0418ec6a0002b660031d8d4000637b2ce531a8000c6c659ca63500bb95ec9394c6a00031bd957298d400063632ae531a8000ccf635ca6350009998c6b94c6a00021fa1f6558d400043f438cab1a80008df8758c6350001878cb3b686a01db0f14276d0d400061f3b6cba1a8048e1c43d9543500018f0cbb8286a00031e1947050d400070fb28c6a1a8000aad84087625000159b0610ec4a0002ba60021d89400062fb2ce73128000c5c659ce62500018becab9cc4a000317195739894004e66312e73128000ccd73d8a62500010fd0fb2ac4a00021fa1c655894000477c3ac43128002c3e75550625000157100aa0c4a0
  | 14 => 0xf8750e429408fa3ce6a1c85280031e9837650a5032c9fc22eca14a07493c845d842940e9878c8bb085281d30fe117610a502461e422ec214a048c3f435d8429400d0fd00bb0852801a1f2017610a503a61f202ec214a074c3c405d8429400187aeca1885280024fe1d4210a503f43fc32e0214a074d38405c042940018f4c0bb665281ef0f98274cca500069d304e9994a07bc3e605d33294001a74c0ba665281ee1fe1970cca502449f426ed194a00093d84dda329400127f08bb265281224f211764ca50004bbc0aec994a021974815d932940012ef02ba265280865d205744ca500049fc22ec194a04893c845d8329400187f08bb065280030f211760ca500343f402ec194a00687c805d832940012bf0e99065281ee1fe19700ca500049fc22e0194a04893c845c032940430f90eb22c3281230f1d1645865010c3e43ac6b0ca000a3f8458d619408f8b8e6b1ac32801a5ea00725865010c3e43ac4b0ca000a3f8458961940018d8e4b12c3281ca4f21176d06503961e322eda0ca02193e849cb419417127f0ea1683281fa1fe1970d06503949e422e1a0ca06393d84dd941940012bf06bb2832811e5720d7650650004b7c12eca0ca00096c825d941940432790ea1a832811f471cd43506500343f430e4a0ca00087d861c9419417727d0fa1283280864f21d425065031c9ec26e0a0ca00093f845db319409127908bb6632808657a0e72cc6505b4afc3a6598ca07b87f865c3319400127f08b8663281224f21170cc6500049fc22ec98ca04893c845d931940012df04bb263280025b209764c650004b7c12e898ca00096c825d1319400d0fd0c39263280021f618724c6505d4af43e6498ca02195c874c9319400127f08bb643281224f21176c865010cb6c3c6590ca00093f845c3219409127908b8643280031e98376486500049fc22ec90ca04893c845d921940012bf06bb2432811e5720d76486502449f43ee890ca0b9c3e60dd12194001a74c1ba2432800257e0d744865023cae41ae890ca0b893e871d1219409187d0c3a243281230f61874486503f61f300e890ca000d3a601d1219408f2bd0fb9a432800347dd373486500068e3a6e690ca0b7c5e60dcd2194001ab4c1b9a43280024fe1173486502449e422e690ca0b695e871cd2194001a3ee839a4328003471d0734865023e2f430e690ca047c5d861cd219408fa9b0439a43281ef179807348650006ad300e690ca047d4c738c921940432d90e9924328086d9205324865002d1f426e6b2e8020a3d84dcd65d000b47d0939acba01ea8f61273597400062fb9ce6b2e8000a7b805cd65d016b4f100b9acba00168fa1372597401051ec26e4b2e8000c6f729c965d00014f700b92cba02d29e201725974059d3d404e2b2e8000a79809c565d000b47d0838acba00828f610715974000
  | 15 => 0xc32264908c3691c4644c921026663b6e6992422ddc471dcd324845b998edb1a64908b7711c7634c921026663b0c69924200e8c6418d3248451b88e231a649080679a1f714c9210262e31aea1924209d64215d4324840187cebb2064908030f5d7640c9210061f3a8c81924200c3d7519032484018bcebb186490803175d7630c92102566432641924200e8c644c83248451789029906490803a519063c8521174f3c3a6590a4200c3e75d93604840187aebb26c0908030f9d464d81210061eba8c9b024200c5e75d8f60484018baebb1ec090803179d463d81210062eba8c7b024200e3b641436048401c70c8286c09080396d8c50d81210072c318a1b02420287f875d760484018f700baec0908031e5d450d812100574c10a1b024200af18114360484014f30e286c0908031e61c50d81210071d420a1b024200e39841436048401cb506286c0908039660c50d812100735410a1b024200e69821436048547ce502286c0908039c60450d81210064fb24e73024200c9c649ce604840193ec8b9cc0908032719173981210064f3a6c73024200c9d74d8e604840193ce831cc090803275d063981210045f43ec8b024200c3f75d916048401878ebb22c0908022fa1c64581210061fba8c8b024200c3c75191604857b95ee4322c09080327d9373581210064e326e6b024200c9f641cd6048401938c839ac09080237a1f63581210062fbaec6b024200c5c75d8d604840193ee9b1ac090803271d363581210046f438c6b024200c5f7518d60484018b8ea31ac09080327dd063581210064e3a0c6b0242bcccf7218d60484011f70eb00c0908029e21560181210071db20a03024200e38641406048401cb6c6280c0908039618c50181210045fc22e630242058bc845cc604840d4f50ba80c0909a38718f7458e503461fb16e8b1ca068c3f61dd163940d187cc1ba2c7281a34e9837458e503b70e318e8b1ca076d1d831d163940ed87cc03a2c7281db4e9807458e503b49fc3ac9a1ca04793c845cb43940fd0ff0cb8687281a30fd917690e502458e422c721ca07b87f865c243940018f4c1bb287281a24fe117650e503449f43cc8a1ca00693c87591439400d878ecb22872801a5721d6350e500362e3b2c6a1ca00687e861c943940010fb0c39287281da4f2117610e503b61e322ec21ca000c7a605d843940f70ff0cb8087281ef1e9817010e503b69c202e021ca065e2c62dd162940cb87ec3ba2c5281970f9837458a5032e9d306e8b14a074e2c621d162940e987d0c3a2c5281d30f9807458a503a69d300e8b14a04887c875916294091878e8b22c5280029b2096458a5023c3e43ac6b14a000a3f8458d629408f8b8e6b1ac5280029b2096358a5003537414c4b14a07e87f865c3429408f2bd07bb485280025760f7690a5032e1fb22ed214a04793
  | 16 => 0x398d210045f43ec8b1a42008be87191634858f95ee4322c6908022fe117558d2102c5e422eab1a42008df835d563484011f700baac69081a3e2017558d210064fba6e6b1a4200c9c74dcd6348401958e9b92c6908032d1d37158d210143f42ee0b1a420087d85dc1634840187ee8282c6909fb0f1d05058d210063db80a0b1a4206c787014163484098b8c6ba8c6908030f9d76418d210061ebaec831a4200c3e75190634840187aea320c69080237e1d6318d210054fc22c631a4200a9c8458c63484018bced3a8c690803179d97518d210046ec3cca31a4200a9e84994634840153b09328c690b1ab360a6518d210046fc3aca31a4200a9f84594634840153908b28c690802b6e016518d210056c402ca31a42c5c9e76d906348401c3cebb20c690803875d76418d2162746b96c831a42008dd87990634858753d09320c69080237e1d6418d2161567c12c831a4200a5e8519063484014bb0a320c690b06a7a186418d216064f3b0c831a4200e1e851906348401c3b0a320c690803879d46418d210070eba8c831a42bee8d72190634857dd1c42320c690afba30846418d215f74a108c831a420095d871406348401c3ec8280c690803871905018d210070faa4a831a4200a9e84d48634840153b09a90c6908a2b5a075218d210056ac0ea431a4200e4f5294863484091bd0e280c6908023761c5018d210054f420a031a4200a9d84140634840159d04280c690802b36085018d211456b408a031a4200ad58114063484f74bf0e280c6909ef17a1c5018d213dd2ec38a031a4200c5d8714063484010bb0e280c69080387a105018d210070ec20a031a4200e4e821406348401c9b04280c6909ef939c85018d213df26b90a031a42bfe56811406348401cab02280c6908122f21176d0d210246e41aed21a4200caf649ca4348409998c739486908063b2197290d210266631ae521a42019e4815ca434840117f08bb2869080237e0d7650d2100477c12eca1a42008f7815d943484050fd0a3b286908021f6147650d210245f43ec8a1a42058de87d8d434840b17908bb086908123720d7610d2102e56324e421a4204ccc639c843484031d90cb9086908263d2197110d211ae5a38ec8a124228cd47118d42484019a8c7b8a84908170f19175109210061f3aec82124200c3d75d9042484018bcebb188490803175d763109210062f3a8c62124200c5d7518c424846b17d0d3a664908132718e74cc9211845e432e99924204c9c635d33248401b4842ba664908d62fe1f64cc9210045ec3ec999242058bf87193324840117b0e3266490803279d363cc9210064eba6c79924204acc839da324857d95cec3246490803a3d90638c92100746320c71924230cb471191324845b9a8e3b1a64908032d193714c9211ae563b6c89924235da471d913248461958e
  | 17 => 0x224200a3e85dc3644840147b0bb86c890802a7a0e70d91210054ec1ce1b224200a3f855c364484014790ab86c8908022fa1c50d91210045ec38a1b224200a9e83143644840153b06286c890802aba0850d912100556c10a1b224235ab681143644840156b02286c8908030fa1c50d91210061ec38a1b224200e1e831436448401c3b06286c8908038ba0850d912100716c10a1b2242cbe36811436448401c6b02286c89080327d92739912102e4e324e73224200c9f645ce644840b938c8b9cc8908022fe1175591210046fc1aeab2242048dc835d564484011f700baac89081a3e20175591210064fba6e6b224200c9f741cd6448401998e7b92c890803351cf71591210143f42ee0b22420087d85dc164484018bee6282c8909ef171cc50591210063db80a0b224206c7870141644840b878c8ba8c8908022fe1d64191210054fc1ac83224200a9c83590644840187ced3a8c8908030f9d975191210045ec3cca3224200a9e83994644840153b07328c890b2aab60a65191210045fc3aca3224200a9f83594644840153906b28c890802aee0165191210055c402ca322420093d87140644840b17d0fa98c8908022f61f53191210070fa9ca63224200aae8214c644840155b04298c8908162fa1f52191210045ec3ea43224200e2f52948644840b17d0e280c8908022f61c50191210054f418a03224200a9d83140644840155d04280c890802ab60850191211855b408a03224200ab58114064484fd47f0e280c8909fb0fa1c50191213f51ec38a03224200c3d87140644840107b0e280c89080387a0c50191210070ec18a03224200e2e821406448401c5b04280c890b278da0450191210071ac08a03224200c5d75d4f634840153d09a9ec690802a761353d8d210146fc3aa7b1a420087f855c363484050f90ab86c690802a7a1265d8d210054ec24cbb1a4200a9f84597634840153908b2ec690802b6e0165d8d210056c402cbb1a4200a5e8519363484014bb0a326c69080387a1464d8d210070ec28c9b1a4200e1f641436348401c38c8286c690803175d475d8d210054f420ebb1a4200a9d841d763484014bd0a3a6c6908029761474d8d210070faa4a9b1a4200a9e84d4b634840153b09a96c69080393d4a52d8d210052f42ee1b1a4200a5d85dc3634840153d09b86c690802a761370d8d210054f424e1b1a4200a9d849c363484014bf0ab86c6908029721570d8d210046f438a1b1a42008dd87143634840153d08286c690802a761050d8d2100567410a1b1a4200acd82143634845b5ad02286c690802b560450d8d210062f438a1b1a4200c5d871436348401c3d08286c6908038761050d8d2100727410a1b1a4200e4d821436348591cad02286c6908039560450d8d210264e31ce931a4204c9c635d2634840193ce9b1cc690803275d36
  | 18 => 0x4031790cba664a08032b5d062cc94100c5e432e919282018bc865d1325040336902ba264a08131718d750c94104e36312ea19282018bc865d03250409938c6ba064a0803175d7630c94100636baec419282018bd84dd7605040187ae93aec0a080a1fe1d75d81410061eba2ebb0282008bd87953605040587ceb2a6c0a080b0f9d554d81412e45fc3a87b028263c3d7414360504011f70eb00c0a08023ee0175593310347c402eab26620287e85dc164cc4010fb0bb82c9988031edc050593310363c380a0b26620087f855c262cc4050f90ab84c598927179cc5098b310143f42ee0b16620087d85dc162cc40993ce6b2485988022fe11729833102c5e422e5306620287e87dd560cc40117f08baac1988162f21175583310061fbaee8b066200c3c75dd160cc40187eea3a2c1988030f1d4745833123c3f438a0b066200c3f7414160cc4fd878e8282c19880a2fe1d54d91310043fc2ae1b22620287c855c3644c4011df04baac8988263b20975591310047dc02eab2262068f8805d5644c40195ee8392c89880333dcc725913104e37428e4b226209c6d851c9644c4019c8e5b8ac89880a1fa1770591310043ec2ee0b226200c6f72141644c4018d8e4282c8988031edc050591310363c380a0b2262008bf87590644c40155904b20c89880a3be1d52d89310043fc2ae1b12620287c855c3624c4011df0eb10c498802ab211621893166567c1ac4312620687c805d4624c4058dceaa90c4988021fe1570189310143e42ae031262008bf845c0624c40b17908b80c49881a1fe1c50189310043ec38a03126249c5d73140624c4031b90cb9c84988263b209761093102e1e322ea2126209c6c625d4424c40187aebb20849880637219731093102e4e322e62126200c6d75d88424c4139c8c4b88849882739189718c9310143fc3aebb0262008fb87580604c40117f08b90c0988162f21172181310145fc3aa9b26420087f855c364c84050f90ab86c9908023ee0175593210347c402eab26420287e85dc164c84010fb0bb82c9908031edc050593210363c380a0b26420087f855c363c84050f90ab86c79080a1fa177058f210043ec2ee0b1e42048bc845db43c840917d0fb228790812a7a0f6450f210143f43eeab0642008bf845d560c840b17908baac1908030fdd774583210061e3aee8b064200c3f751d160c8401878ea3a2c1908030fdd050583213f61e3a0a0b064200c3d75d53644840517f0eaa6c8908021fe1570d91210143e42ae1b224200a9e83997644840153b0732ec890802a7e0d65d91210054e41acbb224200abb80597644840157100b2ec8908030f5d475d91210051f428e7b224200a3d851cf644846b55b0439ec8908022fa1f53d91210045ec3ea7b224200e1f5394f644846b17d0fa96c8908022f61f52d912100717a94a5b
  | 19 => 0xa1f21570d91320047bc0aeab2264018f4815d5644c8011f700baac89901a3e20175591320065bba0e2b226400cd7731c5644c8019cee438ac89900a1fa1770591320043ec2ee0b226400c7771141644c8938e8e2282c8990031edc050591320363c380a0b2264008bf87590644c80156902b20c8990d6ad205649093200c7a40aeca126409d4c325d4424c80117f0eb2084990c2ad20564109320246e432e3192642dcd4615c6324c813b8e42b8c649900a3de1d51d85320043fc2ae1b0a640287c855c3614c80117f08b86c2990162f21170d85320065a308e8b0a64008fb87580604c80187ee93a2ca190029ee0174594320053c402e8b2864cea5f835c5650c8094b906b8aca190028fa1071594320051ec20e2b28640087e87105650c8010fb0e20aca190028fe1170594320051e422e0b286400a3e841c1650c80147b08382ca1901297a0c705943214d2ec18e0b286409a6e821c1650c8534db04382ca190029da0470594320053ac08e0b286406c7a701c1650c8010fd0f882ca190021f61f10594320051f42620b286400a3d84c41650c8011f700baac81901a3e20175590320143f42ee0b20640087d85dc1640c8018f6e0282c81901b1e1c0505903204e67296ec9906400ccd52dd9320c8018b8a1bb264190123720d75584321446e43a64b086428ad4814c9610c813d8e42992c21900a1fa1770584320043ec2ee0b08640087f855d2600c8050f90aba4c0190021fe1571980320143e42ae3300640287e87dd5600c80117f08baac0190162f21175580320061fbaee8b006400c3c75dd1600c80187eea3a2c0190030f1d4745803223c3f438a0b006400c3f74141600c8fd878e8282c01900a1fa177058f410043ec2ee0b1e8272d38501c143d040117f0eaa4c5a08022fe1d4398b410264f39a87316820087f855c262d04050f90ab84c5a09270f9d05098b410143f42ee0b16820087d85dc162d04e5a70a038285a0817279d1638cb4100c5f426ec99682008bf865d132d040336902ba265a080a1fa1f75583412461e3a6eab0682018bc845d560d04fd878e83aac1a08022f21d54583410055c402a8b06824887e8714160d04e5878e8282c1a09cb8e10050583410146fc3aa7b1a820087f855c363504050f90ab86c6a080237e1d6318d4100566412c631a8204a9e86d8d435046117d0db9286a09732718c7050d4131e9c280e0a1a82028ef8754b62504010ff0ab86c4a080a1f21570d894100477c3ac431282cdaaf84588625040159906b10c4a081a1f20175189410045ec3ca83128202c3e75950625040587ceaaa0c4a08022f61f431894100556c16863128200aaf8250c62504058dceaa90c4a08038b55152189410043fc2ae0312820287c855c0625040d0ff0e280c4a08021f61c501894124e1eba0a03128263d38501c1425
  | 20 => 0x5c402a8b008400ab88050d60108910fd0e282c0211d38e100505804202c5f43ea532664008bd87d4a64cc801c5ea5294c999002aba0b519933200556c16a332664058be8714664cc80117b0e28cc9990162fa1c21993320051f428433266400a3d8508664cc80953d0610cc999002a760c21993320055d400433266400ab98008664cc80b17d0e284c9990022f61c50993320254f418a13266400a9d8314264cc80155d04284c999002ab60850993320055b408a13266400ab58114264cc8fd87d0e284c9990030f61c50993323df0f418a13266400e1d8314264cc801c5d04284c9990038b60850993320071b408a13266400e358114264cc80b17d0f884c9990022f61f10993320051f42e213266400a3d85c4264cc80917d0faa2c9990030fdd754593320254f41ea8b2664048bc8755164cc80147d0a20ac9990028f61441593320143f42ee0b26640087d85dc164cc80187eeb3aac999012a7a0e75593320054ec1ceab266400ab7815c964cc80156902b92c9990022fa1f52593320045ec3ea4b266400e2f5294964cc80953d0738ac999002a760e715933200557c12e2b266400a3e851c564cc80147b0a38ac9990022fa1c51593320045ec38a2b2664008bd8708564cc80147d0a10ac9990028f61421593320254f41842b266400a9d8308564cc8015750010ac999002ae60021593320051f42ee0b266400a3d85dc164cc80147f0ab82c9990028f21570593320254e41ae0b266404a9e831c164cc80117d0e282c9990022f61c50593320254f418a0b266400a9d8314164cc80155d04282c999002ab60850593320055b408a0b266400ab58114164cc80187d0e282c9990030f61c50593323df0f418a0b266400e1d8314164cc801c5d04282c9990038b60850593320071b408a0b266400e358114164cc80117d0f882c9990022f61f10593320051f42e20b266400a3d85c4164cc80953d06082c999002a760c105933202e4f322e7a166400c9d64dcd42cc80b87cc8ba885990030f9d56410b320061ebaac8216640287e85dc161cc8010fb0bb82c3990162fa1370587320045ec26e0b0e6406a7a85d4260cc8050fd0fbaac19911f1e603755833223c3f438a0b066400c7b7514160cc8095b506282c199002ba608505833200578c08a0b066447a7a8714160cc8018f50e282c1990038ea1050583320071cc20a0b06647be5a8314160cc801cb306282c1990039aa08505833200734c10a0b066400e728114160cc801ce302282c1990021fe1570d92320143e42ae1b246406c7a70143648c8018f2e0286c9190262f21d54592320143f42ee0b24640087d85dc1648c85b1bd0f992c3190b6b5a0732586320143f42ee0b0c640087d85dc1618c80b17d09b82c3190022f61370586320145fc3aa9b226400a3d85107644c8010ff0ab86c8990
  | 21 => 0x805516010c091f50fa82c021816aea13505804323c3f438a0b008676e38401416010c018f6ea282c021816aea1050580433f71d2a0a0b008600e39541416010c095b506282c021802ba608505804300578c08a0b008647a7a871416010c018f50e282c0219fb8ea1050580430071cc20a0b00867be5a831416010c01cb306282c0219ef8ed0c50580433df2d218a0b00867be39431416010cfdcb286282c0218039aa08505804300734c10a0b008600e72811416010c01ce302282c021816a7a103158f4200566c1062b1e8400ad9800c563d08050fd0bb82c7a10021f6177058f420143f42ee0b0e840087d85dc161d08050fd0fbaac1a11221fa1c505834204c6e43aa6b1c840287e85dc163908010fb0bb82c721027331c96350e420254fc32c6a1c845cc9e631c143908cba70a038287210d62fa1e54586421ac5f43e86b0c84358be87d09619086b56d03a12c32100a1fa1770586420043ec2ee0b0c8402c3c759516090805878eaaa2c1211722f21d43582420054ec2063b1a8400acd820c763508010ff0ab86c6a100a1f21570d8d420046fc3ac631a8400ad48158c6350809998c6b9486a10162f21971909421ae5a30ae3212840087f855c361508050f90ab86c2a10033518473585420063dc02ebb028400c7975d4360508018f2ea286c0a1002ae61050d814200574c10a1b028400a798714360508018f30e286c0a10038ea1050d81420071cc20a1b028400e5a831436050801cb306286c0a10039aa0850d814200734c10a1b028400e72811436050801ce302286c0a10023ee1d60181420053c42ac03028465e3850908605080d4f50ba80c0a10168fa13735944218d1ec26e6b288405a3e849cd651093947b0939aca2100317dce735944267d1fc22e2b288405a3c845c5651080b47d0838aca210c68f61071594420043f43862b28840087d870c5651080b47d0818aca210028f610315944204d3741062b288400a6d820c565108014f50018aca210029e60031594423ad1fc22e0b288405a3c845c1651080b47d08382ca210c68f61070594420052f418e0b288400a5d831c165108134dd04382ca210c69b60870594420053b408e0b288400a75811c1651080d8f4e0382ca210021fa1f10594420043ec3e20b288405a3e84c41651080147b09882ca2100a1fa177058c420043ec2ee0b188474d38501c1431081395ca5bb284210032b54b76508420061e286eca108474d38501c1421080b17908baac2210c22f21d54584420161f3aaa8b0884308bc8750d6110809938e6a1ac2210c22f21d42584421855a40a84b08840287e85dc161108010fb0bb82c2210021fe1573980420143e42ae7300840087f855c660108050f90ab8cc02100a1fa1f75580422461e3a6eab008448e3840dd560108fd878e83aac0211fb8e1007558042005
  | 22 => 0x600000000000001c01c00001b00303600300800300400400901900000500c00500301000200004800702e00500000001a00900900100200001900800100200a00000000000000e00300102402d00400200000000200500000000100d03300702200101200c02000800000000900203000901000800302a00701402e00c00600e00200001000200101b00702100100b01901200200300200000100600500000500501d00100300002500000800200900100100600100400901601101600300000600600f00300000100400400000401901100000a00200101200101a00000000000000300000e00200000901900300303100103b00300001600200302900d00000001e00100101000002001602300000000100301000d00300201601e00b00200200200000b01e00200000000200301200000400300f01000200b00100101300201e00300200400104900101100900000600f00000600001400e00000900002001901500200900000200700000300800401500000b00000100000000200501600000004200101400400201301f00100700200900502006000900501f00700f00000a00302c00800b00501300805203c01d00400d01100000904905201600100400400000100201700100000200100501600300000900500000a0000060000080110043fc2ae1316860287c855c262d0c0917908baac5a18023ee017558b430347c402eab16860287e85dc162d0c010fb0bb82c5a18031edc05058b430363c380a0b16860287e85dc161d0c010fb0bb82c3a180a1fa1f75583432443f438a0b068602c3e755526290c01c5aa8a94c5218021fe157098a430143e42ae131486048ec875496290c050fd0bb82c5218021f6177058a430143f42ee0b0c860087d85dc16190c050fd0fbaac12180b0f1d654582430161e3aaa8b04864787e871416090c0155b0810ec4a1802b360c21d89430043fc2ae1b12860287c855c36250c011df0eb10c4a1802b920562189430343e402ea312860087f855c06250c050f90ab80c4a181a1fe1c50189430043ec38a0312860087f855c36150c050f90ab86c2a18033918472585430063dc02ebb028600c7975d436050c018f2ea286c0a1802ae61050d81430056cc18a1b028600a79871436050c018f30e286c0a18038ea1050d81430071cc20a1b028600e5a831436050c01cb306286c0a18039aa0850d814300734c10a1b028600e72811436050c01ce302286c0a18023ee1d60181430053c42ac03028668e3b641406050c0d4f50ba80c0a18021fe1570988430143e42ae1310860287e85dc16210c010fb0bb82c42180a1fa1770584430043ec2ee0b0886068f8805d66010c0d4f50ba84c02180a1fa1f75580432461e3a6eab008648e3840dd56010c8f8f301baac0219fb0f1d075580433f71c200eab008600ab8
  | 23 => 0xa00000700100300001500700000103200800b00300101600300000f00a00000100000702200101200102000700000700700000100603c01f00000900901000b00001f00903600200200000100400801e00500300500300000100a00100300400300900100200100400000c00700b00c00200100202c00600100300700000d00800000200200c00200600002200300000000f00200100800000701400f02000000c02c00000e00100000000100000000100003800500600600800000401d00003501a00802001b00003700a05200000201a00000900000000400300e00000201900600700c00000400101700201000301700000000201000300000000300e00302c00300300601a00800500100400000000000700a00700300100100a00000800500000000000c00400b00001200800202000200300000701600e00000100800b00000300e00101700000801100600801c01d00401501000000300200300901900000100100900200200503d00e01200100006f00300003400e01a00b00b00100000000000500300f00901a01900200002100100700000100300e00200500500101702300000000a00202402401102a03800100000002900000700000100000c00300c00300000100300000000a00200400a00c00100000000002300500e00001a00200300000000000001100300502f00900000a00700100d00000600b00100000000300c00001001200400000000400c00f00100007700300200000b00300c00e00600000400000c00c00600300000300200100400400c04100500900f00100a01c00001400000401500000c00d00400c00001100c00000701100700300701800400000102f01c01900201201100000e00108101b01201b00001600400300100f00100000100200900600000200200000600000a01200000101a00700b00600900400100000000000000000400000000800800201800b00101500000100600602d00b01900000000400000302800001600200100300500100100100100000300000600000100100000101201e00501600000400000801d00600106206600200000400002a02b00300000f00400101b00600001602a00300001600600301c00700800000000600900003100000d01405101600200002f00500100300100700300200300000400a00000c00300100300500000000004000800a01400300501e00600100100300b01600101a00000400200302400200600c00700100000700700100b00600202002a00f00f00000100200600700100500200901600c00600100000101400f00101700702301700000100101300000000000600300000101200400900200100802300000d00400700000700802000a00f04400000100000600200900000000300000700100100500000400600400000f005000001004000001001
  | 24 => 0x3aa906cf0a539514131519246700003fc0006300000390ab400059e00010ec000588113011c8464a021ac51c2434989c709dca630862cfc00076722100011a000007a84640007b23cf12c57e83d642b210d5908be43da920a980002a7800000017e32eac00d0c0004028dd00006cb00000000000004a700840000001f68a442de8543e202d4bd0ae10ba2e9d0f240644f999c02a93a01500012f000024223e80006ab5540f9cc6864757827f05462620000cd113248c1739f5cb38a4d14589d467e00000012841d60a6367867c0e69c10822a140009fe11fa2e55c6c2308795c0c8096c1638c11114b331359cf450470854d01a0392972169a62c4dc3295272ae48380f4433acb014e03a5de19a010a9d5470265cd5a000477000000000043629849aa7d459b8cf80009933af8a2005c6c62f3214d3c668e3ac255000042a0000f8092272a60f158c000b701fa959c0aaae80002a2c99c00000021318627e712cae10bc254a02b07fd37c5cc2558e5c68239209c937015e5361b3afb83e20f008a30510da62a03081ad8160932fa075d77614f285a284a786c524a80014e687c579a47496e7b546192685c462348fb07d2ea6273451acd7b40f757c29b062898412610a547e4f10e507212cc3870e0a644de80005a02da4eba26131b91dcc381cf3d430284eca7f48d0ea14284a7101145d51cbfa02682813604394e687784388ff3bb13109fe42d3d2a35d3bc0ce4d18af511627c25d1048a2c29a35caa20afc9581608b288f643b050a4f53e20cf34609ece5c03639e0798000000000125139419c1e8956cb662394c000002124a5426ad9045618d01f8855474bb93cd2a443689024f20cdcfc801c2dc02fd4b49c531714a51d4be6600a4f8a26797612894463e32310a1b4072079f26810c8d7c3f85d120888b23753a19ed864c00037c8ba103ca8d30a1d041aa4e54ad151933e4b610906eca6e35842e9cb07baa014e480005ac9ff2d687b13a26ea21a0c248465143b52d28b227da4bda51cfba9d35d18000b8a0592e9120c3502e92e780013de00012b96fd2f8000000000065e57a000000000046e3100b48ad272000000000006500f98000e6cbcd1232b54ab87592ec0e753363ce5888fb10b078a02885e076068d23e0c1c000ac328fa2480005fd1190b851800001c500013b65b200002e4c5e0000001fb8ad430e10f98f52ce9b63088b6800000049c88d096aaa91d581b80002f438d9b7d0268e72f8a824d4ea6431b06989c8b2e48793d17e043a15e215c5ea37855628380009f3567193c2380003c4a1d102253220ea95904652b36a8c6c3184fe5ec1a852c83955fa9f80f722b303a86e895c00000400300100600c00000700409f01200c00000200200300400000201f00200800f00200000300000600200200400a00001d0010080000
  | 25 => 0x4f81620000002b700009110fb846d79400006d105c000a7e1e509d11500001fc800000000026fa57cabc0004101d2c71000047e2428130b3521b0c0869c00017803a51f6a45307800067620b07da7956ee0ed102123ccb80cb587269cf9eb7939f8418e5219b19c831d0cc22535b2e697405a300025045be03b5ee2ea180428756280016f87d1138859c0f8607000000000c0002e38b5123600051f1b103f06cc5a58f9115ac03255212d35a3935e71c98de233060d067567c9253618978ee87ed3251d680506f81b5a08516e0c42fe00047c24784c92e357caa6739d9738a3698f00023b07a43010f48dd80d25c1583afb52a60b704917656987ad19b1ac52ac54e27819a89ec1321af99d14be1bc49c1f1cd3430618d02683c08b65b0a0f8bac35a20989bc176a9309a8700dbc19547e9125052005296a9d50765bb3d105556b06b2062adc9484c0d1e494894b2a05114a154f221e8496245cd464c00fb177451a1fb3f49788a96b271a6ad8817a66c11d1e70e0e74d3561ab9664a02196900445401e5ab291c2484151600e0915e27a555103c38c0004a200000009d230a8f704322f146a82340006bd2208bb40002035aa049d4a646b0002bb80c49a90bfa060000b3834e00005000001eda460000b961c614d42c44651b830d85360003262f18a3800015680007a8a2c52f14b0ff200005a29280900003bb8000abeac2000051c0002e50a106bc450a3100000016a60000af00f954e94a21baee133a04a20699215cc4a62df2314f1627e1a010b17966665478000ff41b50001f39692c18321abb525e70c4c19524f04a36000122859a0490f5aa182e08b55ea9ba40bab5238e9bf906c2180382ca0000431103995c000000000000185e95b4460f3c00096815d91355b2a160b89534000acf0001b7400074e2bdad691760000000398d8067f1921830352490423a1041be58f32d0cc568e2920e902b945a9aa4fd0b6428c66b1e28000ee60002e980000005e917d80007fe6e41791df96c6317316809d16258c3ab151c3dc04f003aff40789332bf90440002501a491c81a812b0bbb0c000094b00000015920004381d8c00000000011e4aec87a16e800000031d043182054800000007f49fa63f58e915c18cbd30801f145746650fd0a9c99492056893807b46f303b2d195c0a3d579238cf323ae000034002e00000023dc00061d00029f463c19a53905b03aa12d23e89248d888456ea6a04d22a833c8c857d82dc0d511214520005ad800094400000000000003793f999a40008781cf9f7c3003d900000002c84930002164e084d8452a36d710be83b8ace4000a8a0002e7493c00045c24140009e63aba120d24233007938939000000017ac00080800000000001725890bb90c2802306a3a100c83c1589b586f82ac5c492643de408608236842c0
  | 26 => 0x7485cf2c3575668838680000004071509828bf60004020f1d4a85ba5132a518567124642954c348df0001478e7ca5b00020a044ca0b12da7384a88d4000063c000ab20baaae984202d30590f882c5cb54090601028895eb1d943a24f256d808cc625ab000131cda20003a0053074c28a5b988144ac0000c22a613ee0000000000c585b900013b16325e4228291134c0000000000000772173209400040c36e00002b600012780017ae95d25694a07409625632a40d6ab5500fa2995eebfe3f50b812ae4710000bbc0002fc00000000000002930e9017443830d8df49667ec1dda0554b80002c58000000abd33896f095800047900000f442046b0fe8b4400000000015409260001de00008383ee00015603610000bf45c800021119395a00000000838ddabeb24b27ecf6693752c000122691c46305f00008e65fb8000b4298732d82c953e0002e8a8cc6903864de94945ae14b08ea6789b410d34f1a1073483207b0000fec55601c8c3563819733797957fe7d55c32c084b008f373000185486329213e0e8e9f41d7889cb688823f4054408208814e22e8f600c322e9dc113495e1408000000839442a3780fac112c3146474404c42f2050e2e1852c809cd148869185984d4baa9d072907c000000521ac4d43a8260002c180000005d3097c00042b44baa701ac41e03cabb00001c24cc8000afa9f053705155245c844f0000cfa00050c85a07c49e23f82d215660f31de057d14402409f1a64834a3c4bfac513dc5f54f422fc16c1223eb0e057629e916815b4b843591850948b0a7f44ef8378ed23d038d1bc86da659398b0dc66abf6041abc40be1530fa830538cb8b14a1460c500a221f815d6dc8933d894bc9ea7005d292803a659a002056580e05c32f04600000000228a55038b7f455828d4f02cf33e0b30e0c00000000000001cd24eaeb56480003fa9c2d2fc0780000ab85b64865330d781b26a60940c650d4acd39900010628d359100000002f80000e6d3669320df80004946242742628000be12b315b071ac2e3411424f0e46a4ca241089c2a5496ad14dfa0314501d7000003200000000005f60fe23bc00000001a1661374a651d930a0000b2156080001983e9000014d40c38426630b01520000b7072c6ae8f03b41afcc5642f5fd96c0512a9e00002296401d40d5a9a51f2a3517b8ff49680ca1b12b106560000002aac000b6d00000002fa89500010095180001b32f48cc00713b20db15b41f91ae00000007c03481b386b69880002e3800087d0000660be66765f904e925614a51800340001992881e480005b12d328902ae14d3fd934436c9b90002cc00004971bb80653f296f37f954483220158783f00000ea26b0ed000040349a117825281d19e2d990fc9280001b1d1b228f0001d295703ef5e62bd091c70f0351b8c29c5600001
  | 27 => 0x9d41215df17a8746b8a00000000001d04ac839c0000965a784e0ed6a6f46e216c00000033b8001788b9f2e6811180a36400029dc0004a93e42a0948c3f71432d811789f60000000f2c0002cf04050144215109fc80007024b5a7d44d4595584966c2ec2de0232530a0a0d70000558d3abcf57cad640ce000000281c0003054378000d00404157951078c1b0538800169c7bd000011d72e59d0000001752ae941b88b0540bc730716d56627be0f1af0d30424447c28942ba6e50982110e328a73828d10a546d20e38c30e8ca121cb11bd04e8455da000037a81b10800b002260001a97c9430a6815819f809c61f000000087a0002c0829513a6e70ef94100005ec25e8000000bf14eb29e42f69360000000dde3562e50000cda01300000006fe0ab2a180e17827ba3528604d7040b42009c89e692202196645689761c2941d5f849b4049768cc65894798fd032cb0509fa1c8e705f95082ff0b50bd002a25207663e34bc819526a06d5ce0ae4b1a718056845d7f05d06130e3853236e36cac6070621d4cc24fcffe67b0300ca89022b7213868c0249f834297244f220959da58c1de6a45a12eb105429d30915652e082b2b0a40538678039b911d668afe53b2d9565a82400d0d7564667a59d0c2088009e5d517196f0b040db95e110634325191149165152ef03c40104894f903889d63fc4c08ef81222210c9232d2e289b324a8bd81eba4112164849ab033db92607801ae5358ad86a04b946781680049301670dbd3421253bd8ed4f829bf49200000003eb0001588a1a1e742808b40120000002658ebc0030df2f7c3e0b6858419c8000454197006c88847400000c077e7bb5c1af5000097d130000000000000000000e800055a200c3b04d23fb93255b04431179c4d1d233211b8c0cc0c7f8040197ceda2ab33aa6b965e20c3a292087aa9ec2b595bcb14a6044a1bdce5038f3780384d0e29f338118c4d08cc083a880e600a832c28e46a449f04cb0207708865b8a72cbda54520718149703ee03f802c00033d0d0adbd72013c2d2a17122a4f7403a8555be9af329026c3121131622dd05ec5d74da2144f702673b3070c00070e5ca8b248c200048f0aa93d4a8732b2688c305114271ea4c8a3530918b543222c556506c53182c83652ed4326bc52833048e7409c2ac0c582ccbea34080014a28170000000000bb255b1e8cf8400000026e000000000028dd41a000284062d71845803794e0f280004a28da47984e13bd1c0c0004260003090cf02d11b02fbc9bc6610000c804004be00000000000002a0821c120000000136400079d23f0ce00802e30ac286caa09514f02258000b265ed86410006fc0d009fd2aa51d0f6af246386294a316109ce8b02320f78a7a8f433100000003fe0000000c7623150204d8000abb0850000f203c80000000000
  | 28 => 0xac72301f30000a2a000301000000007c93ec00038b0000001020300000175486a9bb1a31f857ba51a000000105c8c2000000129e7ae2b71bec99e0001ef8000e6a8fe0000969548555000000169a00038888f40005f81cc88e170200000000001480001a1000127844a0d60000f1a0005e422f40000004570000d2e9e70ee02a981c0001d6000000009d0001a5185a00015c03b02804cd3e6871400049c4c70bfc4800000b48000e8863c00030c98327bf10d1ce544498539a21c4dd61022890ca14804fa2812124b065963b61600e14ba146e83e01586d43c625080007c9393a7b47387d20b19a5488c9c70f29700e6602f00004cc0005ae13c00009820001a8800165200000000013d66101c4adf80000004bd1aa92b855309d8000000ad70000000b28b8258b92bd44e00000000000008873478ef4fe2b6c00020cc8660000002dd51a256814baaf00400640ad2be88aca0a454af4549200000014c0c425ac000169c41400048593a573000037416dd29a0000002b5000014100003e8c06000486883c00000022780984cc066000000000054800018e53a02f303b86e1682b1657e80008be0cd50f85e93b072f3190ccd4c45ee01baefc53048d60d84b0bb81ea4a485704cab993be1f608d22221a504541e422e5061944f08bc035d2b9d7c44c80462d7c31422312085108b83c24b48478e84a7b1088058c04875000250d20ca8355300016029c04800dc45b0aaf064223536a6bc409148d2123b61040c6080aa3441a217cd069dd451aec00006012ef918822426323b24211ea6e234f80a41707d35bd9b6c7742303a81d8046a8b2569aa58ca655728184c441a8682cb892d6f429e348a108e460000002180e3e00019d06080004680072904c12b5c02f2b30bb646d22d818c0f69035351f949de5425570fa06267814479d258686b41d4af80ff88c700002f0fc600031980000007a10000000000b0a0002b2c0009c23d20000000000000000000063800000005520520002e3c00000000000004ba10b556a54910200058f22cc17c1610ca0000bf4c1d000008907400035006b400088e34b28ac000ade5c88710000af557d80000003f200014d030e2c255f00009cc3a16198baccc87935bb07c90321262541e550b40005519bb0000b9b4ce271141e000000000182600027e287879600a15a80001ba48856b1dbc00037e00014e80006460c723600001604ea10900008803ed94fcec41a25088000bce75300001c93ae3683bc869479a1da229a440e2a30f4d224306d492e3ad80018003f0142294182e9650002b896a258228606c8000716000195000000051920697c63273d311e8aa892725f9f0c964b3d258000185247f603202c0000002938000000a4c60a840cfc48b42cf8c4827a00050e1c410a48e1000000154a4300002a0109e255000
  | 29 => 0x68a0db3da1e20786c273aa0d5429205b2bb885c0000fe36096d952e92a1d296a54963b94a81214b48a7a0b2aa2547634732595d45d86da4de042101a50e064a9480001a73e30bf936e1f42b914b8fdeb7d041137428682f30f19116362b211f2e4c0000000000000c08775351000000065553800016d6693390a18870012022a9350484a2e577ab00a14000000138c1dc4c65dbac94bfc9210448a40b8616d0002c2c85c63a0a402cd31257407196201c07092c391cd3347af09504bcf1c00000000000004bb2331b240000000b9a310fa0b5e1e08000000b2a1fd9e0d844a1707e8000af28f65861a6cffa5734d014c4aa400034480012e879b0002730fd6bc21d521ccc6a6a8000134cf4e000366800119ac1604a27840003f100019cd2dca232049c7800082d35da65400000058a9b8099607e14195944b87512fb825400083d0e700000000003b080013b20000bc97fcf5400040710287ca7242d5000073c0003b720c00000001510001838480465178cf561b3558a77122c44b35b80011542a60000000c8228c4c300012e61370f20dc83b211a1360f5c0003ad38a0074ea474c5041404000000208248d09400026100006f621e55091d4fcc5644c82e483fc2535fc8a5848e3d80198348ba84704712ed87ec34f1b1a41cdc21a4192a5b575e617127295c07ab1f042092170abe4364075822206c08b012d3646b04bb84b8c4c43c3ec85515ec9ab44c05a94e8a1a5d70000000a7c1b280015440000001e3c00063e00a16bc6e6000472a7f400000000000000004522b882c00004874c680000180000000000180000467000177490e444135c0009614609f2d66c8164b01710bdebe925200009866fa08700405d453b1a58c4457e23c13b9864a80000572293d3623ea400a3c55d43151881eb06f40185d9a270efab5d380a3ac76e1e2509a19033cbd906c0000abab1a1d8990858c80c287a1dcd8400000024a4c4483500023b44e00e8069acac42618644828e0b40000045abac0000005deaafc184b6a13e978085086555a800072268b0c400ac0006f6416047d812c201e9ae01224000396985935891949d80003c22fa3e522450fe000000041400032c0000000586b944ed00955fe0005691094084521000164d01e15027c9abc7886ee55ba5a80007fe4e792f00001cc3372d9c37200000016380a041434c14cc3ba5000001cac50a3225728e50af821b10300014dab870002450000798000037048a0005aba0fc0006d70002a6400000000000000004db54aaa11686a0022d2f797e62205019f78f0c6a954da2b07e63a711d9dfd03e64d17c948057cc0c3d005ac698be704f9894e4a15200009b4e9e7225a80b2cdb06f504ba6940001831aa16f42680002000e610dcb440ed924846c8e461a89907cc000369a3489da293000000000
  | 30 => 0x1144f7811000017c00b00d100
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xc0008000804001408040048082414100040581c1408140020101450005008001c00141c01a298460850d81430069260d821436050c01a318460450d81430069460d811436050c01a618260450d81430068a551821416010c01a315460450580430068a611821416010c01a498360850580430068c611811416010c01a5183604505804300698609811416010c01a298460850d81420069260d821436050801a318460450d81420069460d811436050801a618260450d8142004a664c80551601080181d8760c50993320060b61d8214264cc801a0d8360850993320060d61d8114264cc801a15836045099332006896098114264cc80181e8760c50593320060b61d8214164cc801a0d8360850593320060d61d8114164cc801a15836045059332006896098114164cc801a298460850583320069260d8214160cc801a318460450583320069460d8114160cc801a618260450583320041b66072141644c40181d8760c50d91210060ba1d821436448401a0d8360850d91210060da1d811436448401a158360450d9121006896098114364484018368161c50191210060761e83140644840181d8760c50191210060b61e82140644840182d8760850191210068360d8214064484018358760450191210068560d811406448401a258260450191210048766064143634840181d8761050d8d2100613a1d821436348401a0d8460850d8d2100615a1d811436348401a158460450d8d210069160981143634840103d989d46418d210048766275190634840181d87d905018d210048766064140634840181d871905018d2100615a0587140634840184e9261c5018d210061364987140634840181d87a105018d210060761d84140634840184d87a085018d210061361d821406348401a0d846085018d210061561d811406348401a15846045018d210069160981140634840d078906147650d215f7211c46418d324840103d989d4640c9215f6a1204644c8324840103d989d464d8121004176627518f60484012399819050d812100496660631436048401a298460850d81210069260d821436048401a318460450d81210069460d811436048401a618260450d81210048e6606414060484012599818c501812103496241851c963100014c4915c87258c40035162417558c32100018996360072504403b7061408758d401000d61a95d4163500403a706141631c940100e5c185058f71500400040f662651d121cc00189a7320154d93200040f662651d121c80b909e98d91731032032f06143645cc40c815bc1a63140744c32002e26219735004048001c18655cd4010120006261cc8055164440014a89055072591100068a1408259040440b909c98591731011000523249645cc40440c7c1850591731011056f0618c501d13044001a1865610634c110
  | 1 => 0x10c9ca0800026000e150c1580001080280007b63680110000002a8011a01c288000002397800e80313833a41a0b9f24ae132b091f9907318034148022af8584821401800809800d800a86aeaa101217002f3716800d1b00298004000f8b270308a6b5a79d929ea18f02acad00053786290000182d8a300032802bb0ac3325801b9d0023039a9618b20034a51980b51380211e220045
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xd02140925917310110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x6
  | 3 => 0x94e
  | 4 => 0x4
  | 5 => 0x5
  | 6 => 0x1
  | 7 => 0x124e
  | 8 => 0x8a
  | 9 => 0x3
  | 10 => 0x8e
  | 11 => 0x128e
  | 12 => 0x150e
  | 13 => 0x98a
  | 14 => 0x98e
  | 15 => 0x128a
  | 16 => 0x150a
  | 17 => 0xca
  | 18 => 0xce
  | 19 => 0x12ce
  | 20 => 0x9ca
  | 21 => 0x9ce
  | 22 => 0x12ca
  | 23 => 0x168a
  | 24 => 0x168e
  | 25 => 0x10a
  | 26 => 0x10e
  | 27 => 0x130e
  | 28 => 0xa0a
  | 29 => 0xa0e
  | 30 => 0x130a
  | 31 => 0x180a
  | 32 => 0x180e
  | 33 => 0x134a
  | 34 => 0xb0e
  | 35 => 0x154e
  | 36 => 0xb4e
  | 37 => 0x16ce
  | 38 => 0xb8e
  | 39 => 0x184e
  | 40 => 0x3ca
  | 41 => 0x3ce
  | 42 => 0x15ce
  | 43 => 0xcca
  | 44 => 0xcce
  | 45 => 0x15ca
  | 46 => 0x170a
  | 47 => 0x170e
  | 48 => 0x40a
  | 49 => 0x40e
  | 50 => 0x160e
  | 51 => 0xd0a
  | 52 => 0xd0e
  | 53 => 0x160a
  | 54 => 0x188a
  | 55 => 0x188e
  | 56 => 0x58a
  | 57 => 0x58e
  | 58 => 0xe8a
  | 59 => 0xe8e
  | 60 => 0x178a
  | 61 => 0x178e
  | 62 => 0x18ca
  | 63 => 0x18ce
  | 64 => 0x124956
  | 65 => 0x95256
  | 66 => 0x98956
  | 67 => 0x128956
  | 68 => 0x9c956
  | 69 => 0x12c956
  | 70 => 0x180956
  | 71 => 0x134c
  | 72 => 0x134d
  | 73 => 0x14a
  | 74 => 0x99256
  | 75 => 0x9d256
  | 76 => 0x98096
  | 77 => 0x150096
  | 78 => 0x128996
  | 79 => 0x99296
  | 80 => 0x150996
  | 81 => 0x151296
  | 82 => 0x9d516
  | 83 => 0x181516
  | 84 => 0x9c0d6
  | 85 => 0x12c9d6
  | 86 => 0x9d2d6
  | 87 => 0xa09d6
  | 88 => 0xe89d6
  | 89 => 0x9ce96
  | 90 => 0x1789d6
  | 91 => 0x9d796
  | 92 => 0x10c
  | 93 => 0x130c
  | 94 => 0x1692d6
  | 95 => 0x181696
  | 96 => 0xe9696
  | 97 => 0x168e96
  | 98 => 0xa0116
  | 99 => 0xb89
  | 100 => 0xb8116
  | 101 => 0x1609
  | 102 => 0x161316
  | 103 => 0x160116
  | 104 => 0x1789
  | 105 => 0x178116
  | 106 => 0x130a16
  | 107 => 0xa1316
  | 108 => 0xe8a16
  | 109 => 0xa0e96
  | 110 => 0x18ca16
  | 111 => 0xa18d6
  | 112 => 0x181316
  | 113 => 0xb9316
  | 114 => 0x1849
  | 115 => 0x185316
  | 116 => 0x409
  | 117 => 0x41316
  | 118 => 0x589
  | 119 => 0x59316
  | 120 => 0x179316
  | 121 => 0xe9816
  | 122 => 0x180e96
  | 123 => 0x14c
  | 124 => 0x3d352
  | 125 => 0x15d352
  | 126 => 0x14d
  | 127 => 0x41352
  | 128 => 0x161352
  | 129 => 0x154b16
  | 130 => 0xccb16
  | 131 => 0x15cb16
  | 132 => 0xcd556
  | 133 => 0x15d556
  | 134 => 0xccb56
  | 135 => 0x170b56
  | 136 => 0xcd6d6
  | 137 => 0xd0b96
  | 138 => 0xb8d16
  | 139 => 0x188b96
  | 140 => 0xb9896
  | 141 => 0xe8b96
  | 142 => 0xb8e96
  | 143 => 0x18cb96
  | 144 => 0xb98d6
  | 145 => 0xd1856
  | 146 => 0x184d16
  | 147 => 0xe9856
  | 148 => 0x184e96
  | 149 => 0xcc3d6
  | 150 => 0x15ccd6
  | 151 => 0x1715d6
  | 152 => 0xd0416
  | 153 => 0x40d16
  | 154 => 0xe8416
  | 155 => 0xe9616
  | 156 => 0x40e96
  | 157 => 0x160d16
  | 158 => 0x189616
  | 159 => 0x161896
  | 160 => 0x160e96
  | 161 => 0x18d616
  | 162 => 0x1618d6
  | 163 => 0x15512
  | 164 => 0x104c
  | 165 => 0x194c
  | 166 => 0x95296
  | 167 => 0x952d6
  | 168 => 0x94116
  | 169 => 0x150056
  | 170 => 0x1512d6
  | 171 => 0x150116
  | 172 => 0xe8a09de
  | 173 => 0x14114
  | 174 => 0x9c096
  | 175 => 0x9d316
  | 176 => 0xe98169e
  | 177 => 0x168116
  | 178 => 0xa12d6
  | 179 => 0x181256
  | 180 => 0x180096
  | 181 => 0x1800d6
  | 182 => 0x1355d2
  | 183 => 0x15c152
  | 184 => 0x135612
  | 185 => 0x160152
  | 186 => 0x1343d2
  | 187 => 0x134412
  | 188 => 0x3d292
  | 189 => 0x41292
  | 190 => 0x403d2
  | 191 => 0x143d2
  | 192 => 0x415d2
  | 193 => 0x3d612
  | 194 => 0x3d892
  | 195 => 0x3c412
  | 196 => 0x1603d2
  | 197 => 0x1615d2
  | 198 => 0x3cd52
  | 199 => 0x41712
  | 200 => 0x155d2
  | 201 => 0x14412
  | 202 => 0x40d52
  | 203 => 0x15612
  | 204 => 0x3d5d2
  | 205 => 0x41612
  | 206 => 0x3d456
  | 207 => 0x41496
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 2657
  | 6 => 8096
  | 5 => 3128
  | 4 => 113
  | 3 => 1
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
  | 8 => packedAt gbK8 (1752+((h/20+packedAt gbK8 (1612+(h % 20)*7) 7) % 75)*7) 7
  | 7 => packedAt gbK7 (108929+((h/885+packedAt gbK7 (98309+(h % 885)*12) 12) % 3857)*13) 13
  | 6 => packedAt gbK6 (426380+((h/2698+packedAt gbK6 (388608+(h % 2698)*14) 14) % 11755)*14) 14
  | 5 => packedAt gbK5 (197056+((h/1042+packedAt gbK5 (184552+(h % 1042)*12) 12) % 3754)*13) 13
  | 4 => packedAt gbK4 (8206+((h/37+packedAt gbK4 (7910+(h % 37)*8) 8) % 149)*8) 8
  | 3 => packedAt gbK3 (82+((h/1+packedAt gbK3 (81+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffc3f01f03e0fffc3fe01c0019e99fc43f7cc
  | 1 => 0xf007c001fffff07ffc1fffffc66966607c78ff
  | 2 => 0x7fffe003fff83ffe001fff87187878f8f0f
  | 3 => 0x7ffffffc00003fffffe003f81f807f00ff0
  | 4 => 0x7fffffffffffc000000003ffe0007fff000
  | 5 => 0xfff8000000000000000000003ffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x10f40b10720e04a5c1320c41808208ac41b3cc
  | 1 => 0xa1108000945290484404a49482282260145055
  | 2 => 0x221556200252902aa40112b185185818a8d0a
  | 3 => 0x44666b52a800423339958022d81d806e00ea0
  | 4 => 0x8887b8d9cf39ce700110600c37fe00077f6000
  | 5 => 0xcf0000e00c018840220180303f7df750000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeeeafce8ecc0feeaeeeafce8ecc0feeaeeeafce8ecc0feeaeeeafce8ecc0feeaeeeafce8ecc0feeaeeeafce8ecc0feeaeeeafce8ecc0feeaeeeafce8ecc0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37101
namespace PEqualNP.Outside.L_meta_37101
open PEqualNP.Outside.L_meta_37101.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 4 := bs0_2_0
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
theorem bs1_2_0 : Interval s1Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 4 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 24 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_32 : Interval s1Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_64 : Interval s1Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_96 : Interval s1Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 117 := (concat (concat bs1_4_0 bs1_4_32) (concat bs1_4_64 bs1_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_32 : Interval s1Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 46 := (concat bs1_5_0 bs1_5_32)
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
theorem bs3_3_0 : Interval s3Atlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 2 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 6 := bs3_4_0
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
theorem bs5_2_0 : Interval s5Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 4 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 28 := block_range (n:=28) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 28 := bs5_3_0
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
theorem bs5_4_128 : Interval s5Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_160 : Interval s5Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_192 : Interval s5Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_224 : Interval s5Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_256 : Interval s5Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_288 : Interval s5Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_320 : Interval s5Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_352 : Interval s5Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_384 : Interval s5Atlas 4 384 12 := block_range (n:=12) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 396 := (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat bs5_4_96 (concat bs5_4_128 bs5_4_160))) (concat (concat bs5_4_192 (concat bs5_4_224 bs5_4_256)) (concat (concat bs5_4_288 bs5_4_320) (concat bs5_4_352 bs5_4_384))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_64 : Interval s5Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_96 : Interval s5Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_128 : Interval s5Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_160 : Interval s5Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_192 : Interval s5Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_224 : Interval s5Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_256 : Interval s5Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_288 : Interval s5Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_320 : Interval s5Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_352 : Interval s5Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_384 : Interval s5Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_416 : Interval s5Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_448 : Interval s5Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_480 : Interval s5Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_512 : Interval s5Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_544 : Interval s5Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_576 : Interval s5Atlas 5 576 25 := block_range (n:=25) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 601 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 bs5_5_96)) (concat (concat bs5_5_128 bs5_5_160) (concat bs5_5_192 (concat bs5_5_224 bs5_5_256)))) (concat (concat (concat bs5_5_288 bs5_5_320) (concat bs5_5_352 (concat bs5_5_384 bs5_5_416))) (concat (concat bs5_5_448 bs5_5_480) (concat bs5_5_512 (concat bs5_5_544 bs5_5_576)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_32 : Interval s5Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 40 := (concat bs5_6_0 bs5_6_32)
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
theorem bgb_3_0 : Interval gbAtlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 1 := bgb_3_0
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
theorem bgb_4_96 : Interval gbAtlas 4 96 17 := block_range (n:=17) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 113 := (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96))
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
theorem bgb_5_3104 : Interval gbAtlas 5 3104 24 := block_range (n:=24) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 3128 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat bgb_5_288 (concat bgb_5_320 bgb_5_352)))) (concat (concat (concat bgb_5_384 (concat bgb_5_416 bgb_5_448)) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))) (concat (concat bgb_5_576 (concat bgb_5_608 bgb_5_640)) (concat bgb_5_672 (concat bgb_5_704 bgb_5_736))))) (concat (concat (concat (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928))) (concat (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)))) (concat (concat (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)) (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312))) (concat (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)) (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 bgb_5_1536)))))) (concat (concat (concat (concat (concat bgb_5_1568 (concat bgb_5_1600 bgb_5_1632)) (concat bgb_5_1664 (concat bgb_5_1696 bgb_5_1728))) (concat (concat bgb_5_1760 (concat bgb_5_1792 bgb_5_1824)) (concat bgb_5_1856 (concat bgb_5_1888 bgb_5_1920)))) (concat (concat (concat bgb_5_1952 (concat bgb_5_1984 bgb_5_2016)) (concat bgb_5_2048 (concat bgb_5_2080 bgb_5_2112))) (concat (concat bgb_5_2144 (concat bgb_5_2176 bgb_5_2208)) (concat bgb_5_2240 (concat bgb_5_2272 bgb_5_2304))))) (concat (concat (concat (concat bgb_5_2336 (concat bgb_5_2368 bgb_5_2400)) (concat bgb_5_2432 (concat bgb_5_2464 bgb_5_2496))) (concat (concat bgb_5_2528 (concat bgb_5_2560 bgb_5_2592)) (concat bgb_5_2624 (concat bgb_5_2656 bgb_5_2688)))) (concat (concat (concat bgb_5_2720 (concat bgb_5_2752 bgb_5_2784)) (concat bgb_5_2816 (concat bgb_5_2848 bgb_5_2880))) (concat (concat bgb_5_2912 (concat bgb_5_2944 bgb_5_2976)) (concat (concat bgb_5_3008 bgb_5_3040) (concat bgb_5_3072 bgb_5_3104)))))))
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
theorem bgb_6_7168 : Interval gbAtlas 6 7168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7200 : Interval gbAtlas 6 7200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7232 : Interval gbAtlas 6 7232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7264 : Interval gbAtlas 6 7264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7296 : Interval gbAtlas 6 7296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7328 : Interval gbAtlas 6 7328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7360 : Interval gbAtlas 6 7360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7392 : Interval gbAtlas 6 7392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7424 : Interval gbAtlas 6 7424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7456 : Interval gbAtlas 6 7456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7488 : Interval gbAtlas 6 7488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7520 : Interval gbAtlas 6 7520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7552 : Interval gbAtlas 6 7552 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7584 : Interval gbAtlas 6 7584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7616 : Interval gbAtlas 6 7616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7648 : Interval gbAtlas 6 7648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7680 : Interval gbAtlas 6 7680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7712 : Interval gbAtlas 6 7712 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7744 : Interval gbAtlas 6 7744 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7776 : Interval gbAtlas 6 7776 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7808 : Interval gbAtlas 6 7808 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7840 : Interval gbAtlas 6 7840 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7872 : Interval gbAtlas 6 7872 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7904 : Interval gbAtlas 6 7904 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7936 : Interval gbAtlas 6 7936 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7968 : Interval gbAtlas 6 7968 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8000 : Interval gbAtlas 6 8000 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8032 : Interval gbAtlas 6 8032 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8064 : Interval gbAtlas 6 8064 32 := block_range (n:=32) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 8096 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat (concat bgb_6_224 bgb_6_256) (concat bgb_6_288 bgb_6_320)) (concat (concat bgb_6_352 bgb_6_384) (concat bgb_6_416 bgb_6_448)))) (concat (concat (concat (concat bgb_6_480 bgb_6_512) (concat bgb_6_544 bgb_6_576)) (concat (concat bgb_6_608 bgb_6_640) (concat bgb_6_672 bgb_6_704))) (concat (concat (concat bgb_6_736 bgb_6_768) (concat bgb_6_800 bgb_6_832)) (concat (concat bgb_6_864 bgb_6_896) (concat bgb_6_928 bgb_6_960))))) (concat (concat (concat (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 bgb_6_1088)) (concat (concat bgb_6_1120 bgb_6_1152) (concat bgb_6_1184 bgb_6_1216))) (concat (concat (concat bgb_6_1248 bgb_6_1280) (concat bgb_6_1312 bgb_6_1344)) (concat (concat bgb_6_1376 bgb_6_1408) (concat bgb_6_1440 bgb_6_1472)))) (concat (concat (concat (concat bgb_6_1504 bgb_6_1536) (concat bgb_6_1568 bgb_6_1600)) (concat (concat bgb_6_1632 bgb_6_1664) (concat bgb_6_1696 bgb_6_1728))) (concat (concat (concat bgb_6_1760 bgb_6_1792) (concat bgb_6_1824 bgb_6_1856)) (concat (concat bgb_6_1888 bgb_6_1920) (concat bgb_6_1952 bgb_6_1984)))))) (concat (concat (concat (concat (concat bgb_6_2016 (concat bgb_6_2048 bgb_6_2080)) (concat (concat bgb_6_2112 bgb_6_2144) (concat bgb_6_2176 bgb_6_2208))) (concat (concat (concat bgb_6_2240 bgb_6_2272) (concat bgb_6_2304 bgb_6_2336)) (concat (concat bgb_6_2368 bgb_6_2400) (concat bgb_6_2432 bgb_6_2464)))) (concat (concat (concat (concat bgb_6_2496 bgb_6_2528) (concat bgb_6_2560 bgb_6_2592)) (concat (concat bgb_6_2624 bgb_6_2656) (concat bgb_6_2688 bgb_6_2720))) (concat (concat (concat bgb_6_2752 bgb_6_2784) (concat bgb_6_2816 bgb_6_2848)) (concat (concat bgb_6_2880 bgb_6_2912) (concat bgb_6_2944 bgb_6_2976))))) (concat (concat (concat (concat (concat bgb_6_3008 bgb_6_3040) (concat bgb_6_3072 bgb_6_3104)) (concat (concat bgb_6_3136 bgb_6_3168) (concat bgb_6_3200 bgb_6_3232))) (concat (concat (concat bgb_6_3264 bgb_6_3296) (concat bgb_6_3328 bgb_6_3360)) (concat (concat bgb_6_3392 bgb_6_3424) (concat bgb_6_3456 bgb_6_3488)))) (concat (concat (concat (concat bgb_6_3520 bgb_6_3552) (concat bgb_6_3584 bgb_6_3616)) (concat (concat bgb_6_3648 bgb_6_3680) (concat bgb_6_3712 bgb_6_3744))) (concat (concat (concat bgb_6_3776 bgb_6_3808) (concat bgb_6_3840 bgb_6_3872)) (concat (concat bgb_6_3904 bgb_6_3936) (concat bgb_6_3968 bgb_6_4000))))))) (concat (concat (concat (concat (concat (concat bgb_6_4032 (concat bgb_6_4064 bgb_6_4096)) (concat (concat bgb_6_4128 bgb_6_4160) (concat bgb_6_4192 bgb_6_4224))) (concat (concat (concat bgb_6_4256 bgb_6_4288) (concat bgb_6_4320 bgb_6_4352)) (concat (concat bgb_6_4384 bgb_6_4416) (concat bgb_6_4448 bgb_6_4480)))) (concat (concat (concat (concat bgb_6_4512 bgb_6_4544) (concat bgb_6_4576 bgb_6_4608)) (concat (concat bgb_6_4640 bgb_6_4672) (concat bgb_6_4704 bgb_6_4736))) (concat (concat (concat bgb_6_4768 bgb_6_4800) (concat bgb_6_4832 bgb_6_4864)) (concat (concat bgb_6_4896 bgb_6_4928) (concat bgb_6_4960 bgb_6_4992))))) (concat (concat (concat (concat (concat bgb_6_5024 bgb_6_5056) (concat bgb_6_5088 bgb_6_5120)) (concat (concat bgb_6_5152 bgb_6_5184) (concat bgb_6_5216 bgb_6_5248))) (concat (concat (concat bgb_6_5280 bgb_6_5312) (concat bgb_6_5344 bgb_6_5376)) (concat (concat bgb_6_5408 bgb_6_5440) (concat bgb_6_5472 bgb_6_5504)))) (concat (concat (concat (concat bgb_6_5536 bgb_6_5568) (concat bgb_6_5600 bgb_6_5632)) (concat (concat bgb_6_5664 bgb_6_5696) (concat bgb_6_5728 bgb_6_5760))) (concat (concat (concat bgb_6_5792 bgb_6_5824) (concat bgb_6_5856 bgb_6_5888)) (concat (concat bgb_6_5920 bgb_6_5952) (concat bgb_6_5984 bgb_6_6016)))))) (concat (concat (concat (concat (concat (concat bgb_6_6048 bgb_6_6080) (concat bgb_6_6112 bgb_6_6144)) (concat (concat bgb_6_6176 bgb_6_6208) (concat bgb_6_6240 bgb_6_6272))) (concat (concat (concat bgb_6_6304 bgb_6_6336) (concat bgb_6_6368 bgb_6_6400)) (concat (concat bgb_6_6432 bgb_6_6464) (concat bgb_6_6496 bgb_6_6528)))) (concat (concat (concat (concat bgb_6_6560 bgb_6_6592) (concat bgb_6_6624 bgb_6_6656)) (concat (concat bgb_6_6688 bgb_6_6720) (concat bgb_6_6752 bgb_6_6784))) (concat (concat (concat bgb_6_6816 bgb_6_6848) (concat bgb_6_6880 bgb_6_6912)) (concat (concat bgb_6_6944 bgb_6_6976) (concat bgb_6_7008 bgb_6_7040))))) (concat (concat (concat (concat (concat bgb_6_7072 bgb_6_7104) (concat bgb_6_7136 bgb_6_7168)) (concat (concat bgb_6_7200 bgb_6_7232) (concat bgb_6_7264 bgb_6_7296))) (concat (concat (concat bgb_6_7328 bgb_6_7360) (concat bgb_6_7392 bgb_6_7424)) (concat (concat bgb_6_7456 bgb_6_7488) (concat bgb_6_7520 bgb_6_7552)))) (concat (concat (concat (concat bgb_6_7584 bgb_6_7616) (concat bgb_6_7648 bgb_6_7680)) (concat (concat bgb_6_7712 bgb_6_7744) (concat bgb_6_7776 bgb_6_7808))) (concat (concat (concat bgb_6_7840 bgb_6_7872) (concat bgb_6_7904 bgb_6_7936)) (concat (concat bgb_6_7968 bgb_6_8000) (concat bgb_6_8032 bgb_6_8064))))))))
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
theorem bgb_7_1632 : Interval gbAtlas 7 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1664 : Interval gbAtlas 7 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1696 : Interval gbAtlas 7 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1728 : Interval gbAtlas 7 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1760 : Interval gbAtlas 7 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1792 : Interval gbAtlas 7 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1824 : Interval gbAtlas 7 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1856 : Interval gbAtlas 7 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1888 : Interval gbAtlas 7 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1920 : Interval gbAtlas 7 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1952 : Interval gbAtlas 7 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1984 : Interval gbAtlas 7 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2016 : Interval gbAtlas 7 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2048 : Interval gbAtlas 7 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2080 : Interval gbAtlas 7 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2112 : Interval gbAtlas 7 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2144 : Interval gbAtlas 7 2144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2176 : Interval gbAtlas 7 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2208 : Interval gbAtlas 7 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2240 : Interval gbAtlas 7 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2272 : Interval gbAtlas 7 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2304 : Interval gbAtlas 7 2304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2336 : Interval gbAtlas 7 2336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2368 : Interval gbAtlas 7 2368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2400 : Interval gbAtlas 7 2400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2432 : Interval gbAtlas 7 2432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2464 : Interval gbAtlas 7 2464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2496 : Interval gbAtlas 7 2496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2528 : Interval gbAtlas 7 2528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2560 : Interval gbAtlas 7 2560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2592 : Interval gbAtlas 7 2592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2624 : Interval gbAtlas 7 2624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2656 : Interval gbAtlas 7 2656 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2657 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 bgb_7_192) (concat bgb_7_224 (concat bgb_7_256 bgb_7_288)))) (concat (concat (concat bgb_7_320 bgb_7_352) (concat bgb_7_384 (concat bgb_7_416 bgb_7_448))) (concat (concat bgb_7_480 (concat bgb_7_512 bgb_7_544)) (concat bgb_7_576 (concat bgb_7_608 bgb_7_640))))) (concat (concat (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 (concat bgb_7_768 bgb_7_800))) (concat (concat bgb_7_832 bgb_7_864) (concat bgb_7_896 (concat bgb_7_928 bgb_7_960)))) (concat (concat (concat bgb_7_992 bgb_7_1024) (concat bgb_7_1056 (concat bgb_7_1088 bgb_7_1120))) (concat (concat bgb_7_1152 (concat bgb_7_1184 bgb_7_1216)) (concat bgb_7_1248 (concat bgb_7_1280 bgb_7_1312)))))) (concat (concat (concat (concat (concat bgb_7_1344 bgb_7_1376) (concat bgb_7_1408 (concat bgb_7_1440 bgb_7_1472))) (concat (concat bgb_7_1504 bgb_7_1536) (concat bgb_7_1568 (concat bgb_7_1600 bgb_7_1632)))) (concat (concat (concat bgb_7_1664 bgb_7_1696) (concat bgb_7_1728 (concat bgb_7_1760 bgb_7_1792))) (concat (concat bgb_7_1824 (concat bgb_7_1856 bgb_7_1888)) (concat bgb_7_1920 (concat bgb_7_1952 bgb_7_1984))))) (concat (concat (concat (concat bgb_7_2016 bgb_7_2048) (concat bgb_7_2080 (concat bgb_7_2112 bgb_7_2144))) (concat (concat bgb_7_2176 bgb_7_2208) (concat bgb_7_2240 (concat bgb_7_2272 bgb_7_2304)))) (concat (concat (concat bgb_7_2336 bgb_7_2368) (concat bgb_7_2400 (concat bgb_7_2432 bgb_7_2464))) (concat (concat bgb_7_2496 (concat bgb_7_2528 bgb_7_2560)) (concat bgb_7_2592 (concat bgb_7_2624 bgb_7_2656)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 62 := (concat bgb_8_0 bgb_8_32)
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 5 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 12, 28)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 18, 19),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 18, 19),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeeeafce8ecc0feeaeeeafce8ecc0feeaeeeafce8ecc0feeaeeeafce8ecc0feeaeeeafce8ecc0feeaeeeafce8ecc0feeaeeeafce8ecc0feeaeeeafce8ecc0
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
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
  have low := boundgb certgb allCuts
  have lift := lift_ok (u:=true) (ms:=fixRows 0 0) (raw:=fullRoots) (T:=fullWord) (xs:=[]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 0 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809450 * 2 ^ 32 + 4243123392) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37101.Model.Repr at out
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

def mono : List Gate := [⟨.and,[2,4]⟩,⟨.and,[1,2]⟩,⟨.and,[0,2]⟩,⟨.or,[1,8]⟩,⟨.or,[6,9]⟩,⟨.and,[0,4]⟩,⟨.or,[3,11]⟩,⟨.and,[10,12]⟩,⟨.and,[0,5]⟩,⟨.or,[13,14]⟩,⟨.or,[7,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4243123392) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4243123392) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37101

open PEqualNP.Outside.L_meta_37101 in
theorem PEqualNP.Outside.L_meta_37101 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4243123392) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4243123392) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
