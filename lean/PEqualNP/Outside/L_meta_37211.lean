import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37211.Model
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


end PEqualNP.Outside.L_meta_37211.Model

namespace PEqualNP.Outside.L_meta_37211
open PEqualNP.Outside.L_meta_37211.Model
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

def SB : Nat := 7

def tips (raw : List Sig) (v : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let b := v % 256
    (b/36,raw.getD (b/6 % 6) zero,raw.getD (b % 6) zero)::tips raw (v >>> 8) n

def deadTest (raw : List Sig) (ws : List Sig) (k hint : Nat) : Bool :=
  let j := min ((hint % 8)-1) 5
  let d := neg (raw.getD j zero)
  let cs := tips raw (hint >>> 6) (hint/8 % 8)
  (makePool true d raw cs).any (fun pool => poolCut true d SB k cs.length pool ws)

def mirrorSteps : List Move := [swapRows 16,swapRows 50]

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
      Slice true (roots g) (target g) (neg ((roots g).getD (min ((tip g k i % 8)-1) 5) zero)) SB

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

end PEqualNP.Outside.L_meta_37211

namespace PEqualNP.Outside.L_meta_37211
open PEqualNP.Outside.L_meta_37211.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0xa8f01731320082500064b0220097a955b6005a88c009271d99a00452b1a43a70101511ca34820a5001c1040086227ff42fe42fd42fc42fe32fd32fc32ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x441ff20883de41107ec8220ffaa2417f54483fca8905f95120feaa2417d54483f8a8905f15120ffa9a417f53483fca6905f94d20fea9a417d53483f8a6905f14d20ffa1a41fe43483fa86907f10d20ffa1241fe42483dc84907f50920f6a1241fc42483fe64907f8c920f719241fd32483da64907f0c920ffa8a417f51483fca2907f54520fe28a417c51483fe82907f90520fea0a41fc41483fe62907f8c520fe98a41ff21483de42907f88520fe90a41ed21483f842907fd0120ff20241fd40483f880907fcc120ff18241fd30483f860907fc8120fd90241fe20483dc40907fd5020bfaa041fe54082fca8106f950209f2a041fd54082faa8106f550209eaa041fc54082f8a8107fd4c20bfa9841fe53082fca6107794c20af29841fd53082faa6107754c20aea9841fc53082f8a6107fd0c20ff21841fd43083f886105f94820ffa1041fe42083fa84107f10820ff99041fe32083fa64107f0c820ffa8841fe51082fca2107d94420bb28841fd51082faa2107d54420baa8841fc51083fe82107f90420fea0841fc41083fe62107f8c420fe98841fc31083fe42107f88420fe90841fc21082fca0107fd0020ff20041fd40083f880107fcc020ff18041fd30083f860107fc8020f790041fe20083f440107f48020f690041f920083fea9085fd5210ff2a4217e54843faa9085f55210fe2a4217c54843fea7085fd4e10ff29c217e53843faa7085f54e10fe29c217c53843fe87087f90e10fea1c21fc43843fea5085fd4a10ff294217e52843faa5085f54a10fe294217c52843fe85087f90a10fea1421fc42843fe65087f8ca10fe99421fc32842faa3087fd0610ff20c21fd41843f883087fcc610ff18c21fd31843f863087fc8610ff10c21fd21843f843085f94210ffa0421fe40843f481087f50210fca0421fc40843fe61087f8c210fd18421fd30843f261087f0c210ff90421fe20843f441087f48210fc90421fc20843fe21087ec4210ffaa2217f54443fca8885f95110feaa2217d54443f8a8885f15110ffa92217f52443fca4885f94910fea92217d52443f8a4885f14910ffa1221fe42443fa84887f10910ff19221fd32443f864887fd0110ff20221fa40443fa80887e50110fe20221ff30443fc60887e8c110fe98221f930443f860887fc8110ff10221fa20443fa40887e48110fe10221fe10443ec20887fd5010bfaa021fe54042fca8086f950109f2a021fd54042faa8086f550109eaa021fc54042f8a8087fd4810bfa9021fe52042fca4087b94810b729021fd52042faa4087b54810b6a9021fc52042f8a4087fd0810ff21021fd42043f884087f8c810fe99021fc32042fca0087fd0010ff20021fd40043f880087fcc010ff18021fd30043f860087fc8010ff10021fd20043f840087f84010fd08021fd10043f220087c44010
  | 1 => 0xe52cc2fca5987f54b30bea9661fc52cc3fe85987f90b30fea1661fc42cc3fe659877ccb30ff19661fd32cc3ba65987f0cb30ffa8e61fe51cc2fca3987f54730bea8e61fc51cc3fe83987f90730fea0e61fc41cc3fe43987fd0330ff20661fd40cc3f881987fd5230bfaa461fe548c2fca9187f55230beaa461fc548c2f8a9185f54e30ffa1c61fe438c3fa87187f10e30ffa9461fe528c2fca5187f54a30bea9461fc528c3fe85187f90a30fea1461fc428c3fe65187f8ca30fe99461fc328c3fea3187f94630bf28c61fd518c2faa3187f14630ffa0c61fe418c3fa83187f10630ff90c61fe218c2fca1187fd0230ff20461fd408c3f881187fcc230ef98461fb308c3fea8985fd5130ff2a2617e544c3faa8985f55130fe2a2617c544c3fe86987f90d30ef21a61fd434c3ba86987f10d30ffa92617f524c3fca4987f54930fe292617c524c3fe84987f90930fea1261fc424c3fe649877cc930ff19261fd324c3ba64987f0c930ffa8a617f514c3fca2987f54530fe28a617c514c3fe82987f90530fea0a61fc414c3fe42987f88530fe90a61ff404c3fc80987f50130fe20261ff304c3f660987f8c130ef18261ff540c2fea8187f95030bf2a061be540c27ca8187f55030beaa061bd540c27aa8187f15030be2a0617e530c3fe86187f90c30fea1861fc430c3fea4187f94830bf29061ee520c2dca4187f54830bea9061ed520c2daa4187f14830ffa1061fe420c3fa84187f10830ff99061fe320c3fa64187f0c830ffa8861fe510c2fca2187d94430bb28861fd510c2faa2187d54430baa8861fc510c3fe82187f90430fea0861fc410c3fe42187f88430fe90861fc210c2fca0187fd0030ff20061fd400c3f880187fcc030ef98061fe300c3f460187f4c030ee98061f9300c3fea9905fd5320ff2a6417e54c83faa9905f55320fe2a6417c54c83fea7905fd4f20ff29e417e53c83faa7905f54f20fe29e417c53c83fe87907f90f20fea1e41fc43c83fe85907f90b20f721641fd42c83da85907f10b20ff99641fe32c83dc65907f4cb20f699641fc32c83fea3907f94720bf28e41fd51c82faa3907f14720ffa0e41fe41c83fa83907f10720ff98e41ff21c83de43907f88720fe90e41ed21c83f843907fd0320ff20641fd40c83f881907fcc320ff18641fd30c83f861907fd5220bfaa441fe54882fca9107f55220beaa441fc54882f8a9107fd4e20bfa9c41fe53882fca7107f54e20bea9c41fc53882f8a7107fd0e20ff21c41fd43883f887105f54a20ffa1441fe42883fa85107f10a20ff99441fe32883fa65107f0ca20ffa8c41fe51882fca3107f54620bea8c41fc51883fe83107f90620fea0c41fc41883fe63107f8c620ff90c41fe21883fa43107f08620bf28441ff40883fc81107f50220fe20441ff30883fc61107f4c220fe18
  | 2 => 0xafaa6217f14c42ffa1885bf4310bfc86217f50c42dea1885fc4310afca4217fd0842dfa1085fe4210bdc84217f50842dea1085ed4210b5a84217fd4442ff288857e5110bfaa2215f54442fe28885ff5010bfca0215f94042fea80857d5010bf8a0217fd5232bfaa465fe548cafca9196f952329f2a465fd548cafaa9196f552329eaa465fc548caf8a9195f54e32ffa1c65fe438cbbc87197f50e32eea1c65fc438cafca5197fd0a32f7a1465fe428cbfa85197f10a32f621465ff328cbde65197fd4632ff28c657e518cbfaa3195f54632fe28c65ff508cbfca1195f94232fea84657d508cbf8a1197fd5132bfaa265fe544cafca8997f55132beaa265fc544caf8a8997fd0932f7a1265fe424cbfa84997f10932f621265fe324cbbc64997fd4132bfa8265fe504cbfaa0997f14132be28265ff540cafea8197f95032bf2a065fd540cafaa8197f15032be2a0657e520cbfe84197f90832f721065fd420cbda84197f10832ff19065ee320cbfa64197b4c832e699065ff500cbfca0195f94032fea80657d500cbf8a0197fd4f40ff29e817e53d03faa7a05f54f40fe29e81ff43d037e87a07f90f40fea1e81bd43d03f887a07fd4b40ff296817e52d03faa5a05f54b40fe29681ff42d037e85a07f90b40fea1681bd42d03f885a07fccb40ff19681fd32d03f865a07fd4740ff28e817e51d03faa3a05f54740fe28e81ff41d037e83a05f55240ffa9c81fe53902fca7207f54e40bea9c81fc53903fe87207f90e40fea1c81fc43903fea5207f94a40bf29481fd52902faa5207f14a40ffa1481fe42903fa85207f10a40ff99481fe32903fa65207f0ca40ffa8c81fe51902fca3207f54640bea8c81fc51903fe83207f90640bf28481ff409037e81207ed0240ffa9a817f53503fca6a07f54d40fe29a817c53503fe86a06fd0d40ff21a81fd435037a86a07f10d40ffa92817f52503fca4a07f54940fe292817c52503fe84a06fd0940ff21281fd425037a84a07f10940ff99281fe32503fa64a07f0c940ffa8a817f51503fca2a07f54540fe28a817c51503fe82a06fd0540ff20a81fd415037a82a07fd0140fda0281fe405037c80a05f95040ffa9881fe53102fca6207794c40af29881fd53102faa6207754c40aea9881fc53103fe86207f90c40fea1881fc43103fea4207f94840bf29081ee52102dca4207f54840bea9081ed52102daa4207f14840ffa1081fe42103fa84207f10840ff99081fe32103fa64207f0c840ffa8881fe51102fca2207d94440bb28881fd51102faa2207d54440baa8881fc51103fe82207f90440fea0881fc41102fca0207fd0040dfa0081fe40103f480207f50040dea0081f940103fea9985fd5330ff2a6617e54cc3faa9985f55330fe2a6617c54cc3fe87987f90f30ef21e61fd43cc3ba87987f10f30ffa9661f
  | 3 => 0x40000000000000559544000000007140038f04ae8000000000000000000007c48758b806ed4d74789b0750000ad000d34839767928c17ec11000000000000007a4000000000000006d000c6c6380049300600001800400c02c00400000800400000400800401005400000c00800c00800000000003c00c01000000804401801400805400000800800004c00000000002804000800002400000400400c00400401800c00800000000406000000c00400c02801000001400000400400000002800004800400800001800000802801c01001002c00c05802800800000000001400c00000800000000800400000001006000000000001001001402800001800000c00c01000400c01401000002c00001c00004806000400000803c03c00c00000803400001001000c01000404000800000400000000000000c00400401001001400400400000001000001000002c07400002c01c00c00400801c02c01000000001400400000404001401000000005c00400000401400000000000001800000800001000000002002c02401000800c00002c00400001801400000001400002400400000400000000401403000000000401401400c01001800c00000800000000000004400c00001000800002000000000000000000400400401400000000001000001000400c00000000800c00c00000c00401400001401801404401000c01400400000400400004002800400000400000006400400c00402800400000000800401800000400400c00800000400c00002000400000000000800000000000400c01c00800c00001c00800400003000801000000000400400000802400402000000000000000002800c00000c00402c00400000800400c01000400800801c01400802c00400801400000c00400403000000000c00001c00800001c00000802002000400000401801800802402000400000402c00000002c00400000800001000000000400c01c00402800c01c00000000801800400c02400400800000400800003c02c00000c00c033fea7a17f94f42bf29e85de53d0abca7a17f54f42bea9e85dd53d0abaa7a17f14f42ffa1e85ff51d0bfca3a15f94742fea8e857d51d0bf8a3a17fd4342ff286857e50d0bfaa1a15f54342fe286857d5490bfea7217f94e42bf29c85de5390abca7217f54e42bea9c85dd5390abaa7217f14e42ffa1c85bf4390bfc87215f94a42ffa1485bf4290bde85217fd4642ff28c857e5190bfaa3215f54642fe28c85ff5090bfca1215f94242fea84857d5090bf8a1217fd4d42bfa9a85fe5350bfaa6a17f14d42be29a85ff4350bfc86a16f90d42fea1a85ff4250bde84a17f90942df21285ff5150afea2a17f94542fea8a85fc5150af8a2a17fd4142bfa8285fe5050bfaa0a17f14142be282857e5410bfea6217f94c42bf29885fd531
  | 4 => 0x9a000000af9aa0ce0f7caa408000007c85c80000000084b12da8c20000006f0000000000005e40d17f188bbd86fb100000131800000017e53282260fa1a63965c4bc4197e80052d3db7600066945a5498c001a4b3789d2f20036f00008f4416e768498d087386b97d23168000364000000009893ea1e0000014b33e800d99a20657709980000029a11800000000001f08000000001d400000001852d71c00000020c319c382040000000125800000f4c4b097169876000f6000820740000000003e0004ca0013d336f907218d03b083f2db983bae4c412980032c0000000059a7e22210a000b4c0000001e35c0006a0009847880035800048f1146650480c8ece2d458baf922201e0000010c21d76c00000c80d6e6b000b0d42eeab00cf7f00ac00000000140f2e0000000000000131f45000d308a00049a8d69980000081c002e9748dc92af1df8c0006a4007a4347bd80b5f894000000000000003348007f89386b0005bc001ea2cc5758e2c52ea4470ba060001727196c0000013cc00000c3c9d74080000000000000001ef00016ac7d9d00000000075011e28665ee05d0009752c2c70000000000009c1ec00207882000c295e16ed3c8284c7be5ca001f9800000dec004a100104ac821963b1e000439000858005fe7dd891d0192ade0c8e2000de83bc750000e46e8f5030814a00000000000001508f000000000009299ff4b0a100171800000c8400015eaace4d5c00522001700007525534e8aa74af6800151b632ed324b3706000000495d42e3064b000056dee80000000000171800ecc003db7155a8002778007d20011afa2b1827ce53e800000000569bf400026000000c062d1b6000ea8000008a80003a67c000000000006b80017b3b4cc4c895c0005959059d0e073c022340ed6ed508000009d4c1a9b000000001041380008400051c0015b2ce0dc000acb9a592112000004111dcbbdfc388f6592ac7adf27400000746001821862f4a5e003a756000003800000a60cd80000058c00239e182dee883f66b8ff08361a6a4f0d7dbe2ff000ad0004b6000002da0000000000015c6a528c68476d594f8007080000000052600000202562000000005e6000b238b80000000000000000001aa70ce99db800000001cfab42dd418003590001705480048a00000000262000bb9d708000065800000001b80005f400000000000771c600028a000cb8000003fa00000000000de00008573f2000066e9d8b4b906abc8e6ac06017a5c66a900009481940010a13c8f12a000e78faebb370e4821d758003dc0021ef58ef0a30822480000004d200000000da000001933008000000016d800000471b20006e8001e2000070002e83847a7d900048e07a19c006d69114c80000053db14001fb0000000050c868a632b4a200028c00000000002529e62f591
  | 5 => 0xe0800000000003cd000b76003bb65e001b07532a800153a6a6586491717d7aa1c56638232a28c0fc00018529b493731b17800000000283d58553151cacf39d03e90c64c0055a1f2000003d8e26001db000f40003b0277465aeb150000000007e7b0b57b7088270484810f04e0001ca9701120000027f14c000d88005a200000000056000000000002ce0025c0196dc0034e0000019b281000000000000000005efcc000850001484d90000377734a488000003720000cc4ac91c6f43bd406c8c48ab85108c3e00000000cb40007800046c000002f000000000000412001101868a60000000000009800000a8c00000000a24003c7000001c892867e00112365cf80016e800436cec0014e10d314904000003e49e94991422c001d3000000000001481ea5a213000001cc27e0000280740ad560007e4590420408f400000000e9c004b2000002563ca0015287180043155deca73f106f98c05a4b182a26c4eb49644498700ff792601770d0d8141f8a000d998100039d3c800000000000004220000000000063db280000000000000000000000000006d400000000000000003c023e000b280048c0000043a7a2002eb8009973051600000101a180008dbba8a700040400000097091b100008e0018e51befa001e1000670dbe00069000000e9000000462000000000000000031615c694002520000000066ad00000002e800007039db60019e000000dc477b501a6bec000000009b8000a5000cf2000331d877d0908c52a7589908d00023353000409000002cf4007f5cd987446af09ff06392ca3b4361012b2704eee3f43f43a0456e8b12aa8798003a40a5dd80047180a78000635911a740800143edf28e2698f18274926c001388ecd818680072600000000000000000000008580000000000000016000cee8693b6c81fcab0e15e02ea0000075e0e3c73bd2dab85d084a000000c9bad3442e9bf024aa52a051100800ef8aaf279a40000037f000a130dcc05248a5b1a9e6f857c7d0f4292ea11c07a0cce59788722fca91c3f5f000e70000d60001bc0000064d9a56800018400136800456d2800000474000002d83b0000cc010800262000001a8000dfd300000000031957a5806536a2720016a93f000ae0002200000000020a5314d962311800e34069cb64e3f8c40005448380029c74bca7a1363800474b9bb64e4c8ce1af7000000000b2000000001c04cd0009f4ff00000000325800000000006bd08c0000044f0010f9ce00080598000000de40000021cab9590000006f20000000000000000000000503a2000320000007000000033477e000000a1307d680000042ae237a1420d899001ea03baa50000000000000003e000719a40001e43ecf41712060016500000087e00000009742f78f80000012d1900000000019c4320003200f800000
  | 6 => 0xe400000000000526a43ef4200002f000142807ac2e60000020b0080000006d3b4310b1368b651beec5c87d840df6dfc0015aedfe3510c9591762147c0010df7d448002348ce98741037b6c0004d52547e0000000051490800000230db472000000ce60000000000000000000078000003d6f0cba475800aa4f38001788d82d0fabcc0c0000cb8a0ab6001edb28c74001a40000f400000000d0400255000b580000038e00006e0ebea5f000000000f3c0000002d1fa040000990000009400091e4a8005b9a693c4730c0ea85f20b16c0c7078de2d65412b852800bac00022bdc0009ee05c4ae1c0026800040e0026c666c60153c163db17730000006b4e52b5000322002e739ac08000003468bd0e00000099cf093a1210000c7471dc0012a0f9828efe0d8005d900000000000e24b384b090bb40eec246a24a000541cc0016f35b4986f531400000f39c53574920006e00009152ef21ebd540019d40000002669ea8000000000000000820011980000002800040001ca000000000001b080000120af50000000028d3408dc57b3d000888d594335e8f8f98123f2001990b84506a19c43100000000000000b700001bd33c012727325aeb84802740d005849488c2d0c1902c572a5a759890fae9a002c69f8610001fb0846b3c41440000000000000006a000ab606be0f818e000000c5157000000e631648d14c0035ff8040a0016100005ca9aaf33eacc4cafe8110004f09f06e7e1132832b7ee44c01d5c4ee9eba5e0000000003c7025db899582a7834178000e9e2c003676b80002c000000a1585a486b00000028c2c400000000000000f6aac596e64000006bc480ec87911e8b17b0921a018ce75d18b624d479a66d8b04002b70be2fc28822464afc5af4660e33d37970bc69dcf56e5000000660003bc000000000799d18ce4f1aa0869f0000521366082e0003449700000046800000652ae9920002a4000df8000000000000006acce0003dc42244003248a78f40032a000c3a8788000000160000000000000000000002b0003fe0003fc000000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x2400435e5390010d754e400436e5290010db54a40042f66190010bd586400437a50900109fd95400433e5450010cf551400435e5350010d754d400436e5250010db549400437a50500109fd94400427e65100109f594400427c6510010cf950400433d5410010b798c40042dd6310010d794c400435d5310010bb98840042ed6210010db948400436d5210010bd98440042f561100109f597300433e54cc010cf553300435e53cc010d754f300436e52cc010db54b300427f658c0109f596300433e548c010cf552300435e538c010d754e300436e528c010db54a30042f6618c010bd586300437a508c0109fd95300433e544c010cf551300435e534c010d754d300436e524c010db549300437a504c0109fd94300427d650c010af99030042bd640c010cf950300433d540c010d794c300435d530c010bb98830042ed620c010db948300436d520c010bd98430042f5610c0109f597200433e54c8010cf553200435e53c8010d754f200436e52c8010db54b200427f65880109f596200433e5488010cf552200435e5388010d754e200436e5288010db54a20042f66188010bd586200437a50880109fd95200433e5448010cf551200435e5348010d754d200436e5248010db549200437a50480109fd94200427e65080109f594200427c6508010af99020042bd6408010cf950200433d5408010b798c20042dd6308010d794c200435d5308010db948200436d5208010bd98420042f56108010cf952100433d5484010d794e100435d5384010db94a100436d5284010be596100437965840109e596100437b5484010ee95210043795484010ee55210043395484010ded4e10043da5384010de54e10043d95384010d654e100437b5284010fa94a10043795284010fa54a10043695284010be58610042f16184010de94610043f251840109fd95100433e5444010cf551100436e5244010db54910042fb6544010ded95100427b6544010ded5110043ba5444010de55110043b95444010ce551100437b5344010f694d10043795344010f654d10043595344010ded4910043ea5244010de54910043e95244010da54910042fb6144010de94510043f25144010fcd0510043f24144010fc50510043f04144010fccc510043f23144010fc4c510043f03144010fcc8510043f22144010fc48510043f02144010fcd9510042f36544010dcd9510043f36444010fc99110043f16444010fc19110043f35444010dcd5110043f25444010ec95110043f15444010dc55110043b15444010cc55110043f05444010fcd8910043f26244010fc58910043f06244010fcd4910043735244010fc94910043e25244010fc54910043715244010f854910043615244010fc14910043f34244010fc90910043f14244010fc10910043f23244010fc4c910043f03244010
  | 1 => 0x433d54d4810b798f52042dd63d48109f993520433e64d48108f993520427d64d4810cf593520423d64d48109f98f520435e63d48109798f520427d63d4810d758f520425d63d48109f987520437661d48109f983520437a60d48109f596520433e5494810cf552520436f52948109f992520427d64948109f98e520427d63948109b596520436f5494810db95252043ae5494810cb952520436d5494810eb552520432d5494810db152520436f5394810db94e52043ce5394810d394e520436f6494810db992520436d6494810db192520436f6394810db98e520436d6394810db18e520436e6194810db186520436e6094810db182520433e5454810cf551520435e53548109fd91520427c64548109fd8d520427c6354810dbd89520427f61548109f585520427f60548109f581520436f6554810dbd51520436e5454810eb951520432e5454810db55152043ad5454810cb551520436c5454810dbd4d520436e5354810f394d520434e5354810db54d52043cd5354810d354d520436f6454810db991520436d6454810db191520436f6354810db98d520436d6354810db18d520436e6154810db185520436e6054810db181520436c1054810af99052042bd6414810cf950520433d5414810b798c52042dd6314810d794c520435d5314810bb988520436d52148109f990520433e64148108f990520427d6414810cf590520423d64148109f98c520435e63148109798c520427d6314810d758c520425d63148109f988520436e62148109b988520427e6114810dd984520427661148109f980520437a60148109e980520427f65d08109f997420427d65d08109f197420433e54d0810cf55342042de63d0810b758f420435e53d0810d754f420436e52d0810db54b420427f65908109f996420427d65908109f196420433e5490810cf55242042de6390810b758e420435e5390810d754e420436e5290810db54a420427f65508109f995420427d65508109f195420433e5450810cf551420435e5350810d754d420436e5250810db549420427f65108109f994420427d65108109f194420433e5410810cf550420435e5310810d754c420436e5210810db54842043ad42108109fd96320427e658c8109f596320427c658c810af99232042bd648c810cf952320433d548c810d794e320435d538c810db94a320436d528c8109fd95320427e654c8109f595320427c654c810cf951320433d544c810db949320436d524c8109fd94320427e650c8109f594320427c650c810cf950320433d540c810db948320436d520c810f34c8320427e64940109f592500427e63940109f58e500427e62940109f58a500427d61940109f597400433e54d0010cf553400435e53d0010d754f400436e52d0010db54b400427f65900109f596400433e5490010cf55
  | 2 => 0x5450110bed8d40443bb4350110ee50d40442fb6250110eed0940443b94250110fcd8540442f86150110fc18540442f06150110eed0540443f24150110ee50540443f14150110ec505404427e6510110b798c40442dd6310110bb98840442ed6210110bd98440442f56110110be98040443b940101109f997304435f53cc110d714f30442f661cc110bd587304427e658c110be996304437a658c110bed9230442f9648c110be58e304437a538c110de14e30442f9628c110fcd8630442fa618c110fc18630443f2418c110fc50630443f2218c1109f195304435f534c110d714d30442f7614c110bd1853044378654c1109e19530442fb644c110be59130443db634c110f6d4d304437a534c110de14d30443d8534c110f690d30443d9434c110bed8930443db324c110f64c930443f3614c110be18530443f0614c110bc18530443f2414c110fc50530443f2214c110fc485304427e650c110af99030442bd640c110bb98830442ed620c110bd98430442fa600c110f64c0304427e65c8110dbd4b204436c52c8110bd98720442f561c8110f9487204427e6588110be996204437a6588110bed9220442f96488110bed8e20442f96388110be58a204437a5288110de14a20443f36188110be98620443f06188110fc90620443f14188110fc8c620443f22188110fc486204427f65481109f595204427c6548110dbd49204436c5248110bdd8520442f46148110f948520442f86548110de19520442786548110bed9120442f96448110bed8d20442f96348110fad8920443eb5248110de94920443785248110fa14920443ea4248110fa50920443ea3248110fa4c920443f36148110be18520443f06148110bc18520443f24148110fc50520443f23148110fc4c520443eb2148110fc88520443e92148110fc48520443e121481109f99420442be6408110af59020442de6308110b758c20442f66108110bd58420442fa6008110fa48020442f76484110bd59210442f76384110bd58e10442f76284110bd58a10443f35084110fc90210443f14084110fc8c210443f13084110fc88210443f12084110bb98b54042ed62d50109f98b540436e62d50109b98b540427d62d5010db58b540426d62d50109f983540437a60d50109f596540433f54950109f98a540427d62950108f596540433f6295010cf98a540433d6295010cf18a540433e6095010cf182540433f64550109fd89540427c62550109fd81540427d6055010cfd95540433f6255010cf989540433d6255010cf189540433e6055010cf181540433c1055010af990540433d5415010bb98854042ed62150109f990540433e64150108f990540427e6215010db988540426e62150109f588540436d62150109b588540427e6015010de980540427a6015010af99352042bd64d4810cf953520
  | 3 => 0x210b758c208436e5208210db54820842f66108210bd58420843e92008210be597108437965c4210bed9310842f964c4210bed8f10842f963c4210bed8b10842f962c42109f98b544427d62d5110cfd52544427e64951109f98a544427d62951109f58254443796095110bbd8954442ec6255110cfd91544427f6255110dbd89544426f62551109f189544436c62551109b189544427f6055110ded81544427e6515110cf55054442ee6215110bb588544433e64151109f988544436e62151109b988544427d6215110db588544426d62151109f980544437960151109f180544427e64d49109f593524427e63d49109f58f524436f52949109f992524427d64949109f98e524427d63949109f98a524427d6194910dd586524427d6094910de58252442bf6454910af19152442df6354910b718d524427f6454910cfd91524423f64549109f191524433c64549108f191524427f6354910d7d8d524425f63549109f18d524435c63549109718d524436f62549109fd85524437761549109fd81524437b60549109f99452442be6414910af59052442de6314910b758c524436d52149109f990524433e64149108f990524427d6414910cf590524423d64149109f98c524435e63149109798c524427d6314910d758c524425d6314910db988524427e6114910dd584524427c61149109f980524437960149109f180524427f65d09109f997424427d65d09109f197424433e54d0910cf55342442de63d0910b758f424436f52d0910db14b42442f661d0910bd58742442fa60d0910be583424427f65909109f996424427d65909109f196424433f5490910cf15242442de6390910b758e424436e5290910db54a42442f66190910bd58642442fa6090910be582424427f65509109f995424427d65509109f195424433e5450910cf551424436e5250910db549424427f65109109f994424427d65109109f194424433f5410910cf150424436f5210910db14842443ad4210910bd98442442f56110910be98042442f960109109fd96324427e658c9109f596324427c658c910af99232442bd648c910d7d4e324435c538c910db94a324436d528c910bd98632442f5618c910be98232442f9608c9109fd95324427e654c9109f595324427c654c910db949324436d524c9109fd94324427e650c9109f594324427c650c910dbd48324436c520c910f34c832442fa600c910be580324427e65d0110cfd53404433c54d0110bd98740442f561d01109f99640442fa6590110de99640442f96490110de95240443785490110be58e40442f96290110fcd8640442fa6190110fc18640443f241901109fd95404427d65501109f195404433f5450110cf15140442f76150110bd185404437865501109e19540443bb6450110eed51404437a5450110de15140443b8
  | 4 => 0xf551428436e5250a10db549428427f6510a109f994428427d6510a109f19442843ad4210a10be98042842f96010a109fd97328427e65cca109f597328427c65cca10af99332842bd64cca10d794f328435d53cca10be98332842f960cca109fd96328427e658ca109f596328427c658ca10af99232842bd648ca10db94a328436d528ca10be98232842f9608ca109fd95328427e654ca109f595328427c654ca10d794d328435d534ca10db949328436d524ca109fd94328427e650ca109f594328427c650ca10f34c832842fa600ca10be580328433e54d0610cf55341842fa60d0610be583418433e5450610cf55141842fb6050610be18141842de6310610b758c41842ee6210610bb58841842f96010610d794f318435d53cc610be98331842f960cc610d794d318435d534c610bed8131842f8604c610af99031842bd640c610bb98831842ed620c610be580318436e52c8610db54b21842fa60c8610be583218436e5248610db54921842fb6048610be18121842be6408610af59021842de6308610b758c21842f96008610cfd53408433c54d0210cf952408433d5490210bd98640842f56190210be59640843796590210de95240843ba5490210ee55240843785490210be58e40842f96290210be98640843f26190210fc586408433f5450210cf15140842fb6550210ded9540843bb6450210eed51408437a5450210de15140843b85450210bed8d40843bb4350210ee50d40842fb6250210eed0940843b94250210be18540843bb4150210ee505408433e5410210cf55040842de6310210b758c40842ee6210210bb58840842f66110210bd58440843b94010210d7d4f308435c53cc210d794e308435d538c210bd98630842f5618c210be5963084379658c210bed9230842f9648c210de94e30843da538c210f654e3084378538c210be58a30842fa618c210fc98630843f1618c210d7d4d308435c534c210bed95308437b654c210bed9130842f9644c210f6d8d30843db534c210de94d3084378534c210f614d30843da434c210f650d30842fb624c210f6cc930843d9324c210be18530843db314c210f64c530842be640c210af590308435e530c210d754c30842ee620c210bb58830842f6610c210bd58430843d9300c210dbd4b208436c52c8210db94a208436d5288210bd98620842f56188210be59620843796588210bed9220842f96488210bed8e20842f96388210de94a20843ea5288210fa54a20843785288210be98620843f26188210fc586208436f5248210db14920842fb6548210ded9520842fb6448210be59120842fb6348210be58d20843eb6248210fad49208437a5248210de14920843e85248210fa90920843e94248210fa8c920843e93248210be18520843eb2148210fa48520842be6408210af59020842de6308
  | 5 => 0x200837151880209fd95200833e5448020cf551200835e5348020d754d20083765148020dd54520082ef6548020dbd95200826f6548020dbd5120083ae5448020db55120083ad5448020cb551200836f5348020f394d200836d5348020f354d200834d5348020f9945200836d5148020f954520083655148020bbd81200836e5048020bed95200837b65480209ed9520083ba5448020ee55120083da5348020f654d20082fb6248020fad89200837a5248020fa94920083f25148020de54520083f15148020dc54520083eb2148020fa485200827e63d52109f58f548427e62d52109f58b548437561d5210de983548433f54952109f98e548427d63952109f98a548427d6295210de982548433f64552109fd8d548427c63552109fd89548427c6255210cf55054842de6315210b758c54842ee6215210bb588548433e64152109f98c548435e63152109798c548427d6315210d758c548425d63152109f988548436e62152109b988548427d6215210db588548426d6215210dd584548437a60152109f993538427d64d4e109f98b538427d62d4e10dd587538437a60d4e10d7d4e538427e6494e109f592538427e6294e109f58a538437a6094e109fd91538427c6454e10d7d8d538427f6254e109f18953842be6414e10af590538435d5314e10bb98853842ed6214e109f990538433e6414e108f990538427d6414e10cf590538423d6414e10d798c538427e6214e10db988538426e6214e109f588538436d6214e109b58853843756114e10de980538427f65d0e109f997438427d65d0e109f197438433e54d0e10cf55343842ee62d0e10bb58b43842fa60d0e10be583438427f6590e109f996438427d6590e109f196438435e5390e10d754e43842ee6290e10bb58a43842fa6090e10be582438427f6550e109f995438427d6550e109f195438433e5450e10cf551438435e5350e10d754d438427f6510e109f994438427d6510e109f194438439d4310e10be98043842f96010e109f993528427d64d4a109f98f528427d63d4a10dd587528437a60d4a10dbd4a528427e6494a109f592528427e6394a109f58e528437a6094a109fd91528427c6454a109fd8d528427c6354a10dbd8952842be6414a10af59052842de6314a10b758c528436d5214a109f990528433e6414a108f990528427d6414a10cf590528423d6414a109f98c528435e6314a109798c528427d6314a10d758c528425d6314a10db98852843756114a10de980528427f65d0a109f997428427d65d0a109f197428433e54d0a10cf55342842de63d0a10b758f42842fa60d0a10be583428427f6590a109f996428427d6590a109f19642842de6390a10b758e428436e5290a10db54a42842fa6090a10be582428427f6550a109f995428427d6550a109f195428433e5450a10c
  | 6 => 0x33e5450420cf551410835e5350420d754d41082ef6250420bb18941083765150420dd545410827f65104209f994410827d6510420cf950410833d5410420b798c41082dd6310420d794c410835d5310420bb98841082ed6210420dd94441083755110420be98041082f960104209fd97310827e65cc4209f597310833e54cc420cf553310835e53cc420d754f310837651cc420dd547310827f658c4209f996310827d658c420cf952310833d548c420d794e310835d538c420dd9463108375518c4209fd95310827d654c4209f195310833e544c420cf551310835e534c420d754d31082ef624c420bb1893108376514c420dd545310827e650c4209f594310833e540c420cf55031082ee620c420bb58831082fa600c420be580310833e54c8420cf553210835e53c8420d754f210836e52c8420dd947210837551c8420be98321082f960c84209f596210833e5488420cf552210835e5388420d754e210837551884209fd95210833e5448420cf551210835e5348420d754d210836e5248420dd94521082be6408420af590210833e5408420cf55021082de6308420b758c210835e5308420d754c21083765108420dd54421082fa6008420be580210827e64940209f592500827e63940209f58e500827d65d0020cf953400833d54d0020d794f400835d53d0020dd947400837551d00209fd96400827d6590020cf952400833d5490020d794e400835d5390020bb98a40082ed6290020dd946400837551900209fd95400833e5450020cf551400835e5350020d754d40083765150020dd545400827f65100209f994400827d65100209f194400833e5410020cf55040082de6310020b758c400835e5310020d754c40082ee6210020bb58840082f66110020bd58440083765110020dd544400827d65cc020cf953300833d54cc020d794f300835d53cc020dd947300837551cc0209fd96300827d658c020cf952300833d548c020d794e300835d538c020bb98a30082ed628c020dd9463008375518c0209fd95300833e544c020cf551300835e534c020d754d3008376514c020dd545300827f650c0209f994300827d650c0209f19430082be640c020af590300833e540c020cf550300835e530c020d754c30082ee620c020bb58830082f6610c020bd5843008376510c020dd544300833e54c8020cf553200835e53c8020d754f200837651c8020dd547200836f54c8020eb953200836d54c8020eb553200832d54c8020dbd4f20083ce53c8020db54f20083cd53c8020d354f20083e651c8020db54720083e551c8020d9547200833e5488020cf552200835e5388020d754e20082ed6288020db94a20083765188020dd54620083ba5488020ee55220083da5388020f654e20082f96288020de94a20083ea5288020fc94620083795188020fc546
  | 7 => 0x350c209fd94430827e6510c209f594430827c6510c20cf950430833d5410c20d794c430835d5310c20e750c430827e64948209f592520827e63948209f58e520827d65d0820cf953420833d54d0820b798f42082dd63d0820d794f420835d53d08209fd96420827d6590820cf952420833d5490820b798e42082dd6390820d794e420835d5390820db94a42082fa6090820be582420827f6550820cf951420833d5450820d794d420835d5350820db949420827f65108209f594420833e5410820cf550420835e5310820d754c42083ad4210820be98042082f960108209f59732082be64cc820af593320833e54cc820cf553320835e53cc820d754f320827f658c8209f59632082be648c820af592320833e548c820cf552320835e538c820d754e320836e528c820be98232082f9608c8209fd95320833e544c820cf551320835e534c820d754d320836e524c8209fd94320827d650c820cf950320833d540c820d794c320835d530c820f34c832082fa600c820be58032082be64d4420af593510833e54d4420cf55351082de63d4420b758f510835e53d4420d754f510833e5494420cf552510835e5394420d754e510837751944209f992510827d64944209f98e510827d6394420ddd5251083765494420ed95251083365494420dd55251083b55494420cd55251083745494420ddd4e51083765394420f594e51083565394420dd54e51083d55394420d554e51083745394420ddd9251083766494420dd59251083746494420ddd8e51083766394420dd58e51083746394420ddd0e51083764394420dd50e51083744394420dd18a51083774294420dd90a51083754294420dd10a51083773294420dd8ca51083753294420dd0ca51083766094420dd182510833e5454420cf551510835e5354420d754d510827f64544209f191510827f63544209f18d51083776554420ddd5151083765454420ed95151083365454420dd55151083b55454420cd55151083745454420ddd4d51083765354420f594d51083565354420dd54d51083d55354420d554d51083745354420ddd9151083766454420dd59151083746454420ddd8d51083766354420dd58d51083746354420ddd0d51083764354420dd50d51083744354420dd98951083774254420dd90951083754254420dd10951083773254420dd8c951083753254420dd0c951083766054420dd18151083742054420af99051082bd6414420cf950510833d5414420b798c51082dd6314420d794c510835d5314420bd984510837551144209fd97410827e65d04209f597410833e54d0420cf553410835e53d0420d754f410837651d0420dd547410827f65904209f996410827d6590420cf952410833d5490420d794e410835d5390420dd946410837551904209fd95410827d65504209f1954108
  | 8 => 0x20d758f540825d63d50209f98b540836e62d50209f987540837661d50209d987540827d61d5020dd587540827561d50209f983540837a60d50209f596540833f54950209f98e540827d63950209f986540827d61950208f596540833f6395020cf98e540833d6395020cf18e540833e6295020cf18a540833f6195020cf986540833d6195020cf186540833e6095020cf182540833f64550209fd8d540827c63550209fd89540827d62550209fd85540827c6155020cfd95540833f6355020cf98d540833d6355020cf18d540833e6255020cf189540833f6155020cf985540833d6155020cf185540833e6055020cf181540833c2055020af990540833d5415020b798c54082dd6315020bd98454082f561150209f990540833e64150208f990540827e6315020d798c540825e63150209f58c540835d63150209758c540827e6215020db988540826e62150209f984540837661150209d984540827d6115020dd584540827561150209f980540837a6015020af99353082bd64d4c20cf953530833d54d4c20bd98753082f561d4c209f993530833e64d4c208f993530827d64d4c20cf593530823d64d4c209f98b530836e62d4c209f987530837661d4c209d987530827d61d4c20dd587530827561d4c209f983530837a60d4c209f596530833e5494c20cf552530835f5394c209f992530827d6494c209f986530827d6194c2097596530835f5494c20d7952530839e5494c20c7952530835d5494c20e7552530831d5494c20d7152530835f6494c20d7992530835d6494c20d7192530835e6294c20d718a530835f6194c20d7986530835d6194c20d7186530835e6094c20d7182530833e5454c20cf551530827f6454c209f191530835f6354c209fd89530827d6254c209fd85530827c6154c20d7d95530835f5454c20d7951530839e5454c20c7951530835d5454c20e7551530831d5454c20d7151530835f6454c20d7991530835d6454c20d7191530835e6254c20d7189530835f6154c20d7985530835d6154c20d7185530835e6054c20d7181530835c2054c20af99053082bd6414c20cf950530833d5414c20b798c530835d5314c20bd98453082f56114c209f990530833e6414c208f990530827d6414c20cf590530823d6414c209f98c530835e6314c209798c530827e6214c20db988530826e6214c209f98453083766114c209d984530827d6114c20dd58453082756114c209f980530837a6014c209fd97430827e65d0c209f597430827c65d0c20cf953430833d54d0c20d794f430835d53d0c20bb98b43082ed62d0c209fd96430827e6590c209f596430827c6590c20cf952430833d5490c20d794e430835d5390c20bb98a43082ed6290c209fd95430827e6550c209f595430827c6550c20cf951430833d5450c20d794d430835d5
  | 9 => 0xd9132482ed644c920db951324836c544c920f3d8d32483cf534c920db94d324836c534c920f314d324834c534c920f3d0d32483cc434c920bbd8532483eb604c920bb18132483e8604c9209f99432482ee620c920f34c8324827e64d45209f593514827e63d45209f58f514836e42d4520db50b514836e32d4520db4cb51483775194520afd9151482bc6454520b7d8d51482dc6354520af99051482bd6414520b798c51482dd6314520dd544514827e6414520cf990514823e64145209f590514833d64145208f590514827e6314520d798c514825e63145209f58c514835d63145209758c514837960145209f997414827d65d05209f197414833e54d0520cf55341482ee62d0520bb58b41483ad42d05209f996414827d65905209f196414833f5490520cf15241482ee6290520bb58a41482fa6090520be582414827f65505209f995414827c6550520cf951414833d5450520eb509414827e65105209f594414827c6510520cfd50414833c5410520b798c41482dd6310520bb98841482ed6210520be98041482f960105209f997314827d65cc5209f197314835e53cc520d754f31482ee62cc520bb58b31483cd32cc5209f996314827d658c5209f196314835f538c520d714e31482ee628c520bb58a31482fa608c520be582314827e654c5209f19531483cd324c5209f99721482ee65c8520db99721482ef64c8520bb593214836f54c8520db55321482ef63c8520bb58f214836f53c8520db54f214836c51c8520fad8321482ee60c8520fa18321482ed6288520ddd4621483745188520be98221482f96088520ddd4521483745148520bed8121482f86048520bbd9121482ed6448520dbd51214836d5448520bbd8d21482ed6348520dbd4d214836d5348520f9d8521483e75148520db14521483e45148520fad8121482ec6048520fa181214827e6508520af99021482bd6408520b798c21482dd6308520bb98821483e52108520be980214827e65d0120cfd53404833c54d0120bb98b40482ed62d0120eb50b404827e65901209fd95404827d65501209f195404833f5450120cf15140482ef6250120bb18940483ad42501209f99440482de6310120b758c40482ee6210120bb58840482f66110120bd584404827e65cc120d7d4f304835c53cc120bb98b30482ed62cc120f34cb304827e658c1209fd95304827d654c1209f195304835f534c120d714d30482ef624c120bb18930483cd324c1209f99430482be640c120af59030482ee620c120bb58830482f6610c120bd58430483ea42c8120fa50b20483ea32c8120fa4cb20482f961c8120fac8720483e921c8120bbd9220482ed6488120bbd8e20482ed6388120bb58620483eb5088120b798f54082dd63d5020bd98754082f561d50209f98f540835e63d50209798f540827d63d50
  | 10 => 0x882ee628c220bb58a308835f534c220d714d30882be640c220af590308835e530c220d754c30882ee620c220bb58830882f6610c220bd58430882ed65c8220db597208836f54c8220db553208836f53c8220db54f208836d51c8220be597208837965c8220be587208827e63d51209f58f544827e61d51209f587544833f5495120b798e54482dd63951209f992544827e6395120d798e544825e63951209f58e544835d63951209758e544827d6295120db58a544827e61951209f586544827d6095120de582544833f64551209fd8d544827c63551209fd89544836f62551209fd85544827c61551209fd81544837b60551209f994544833d5415120cf990544827e63151209f58c544827e6215120db588544827c62151209f984544827d61151209f993534827d64d4d209f987534827d61d4d20af99253482bd6494d20d7d4e534827e6494d20cf992534823e6494d209f592534833d6494d208f592534827e6394d209f58a534836d6294d209f986534827d6194d209f58253483796094d209fd91534827c6454d20d7d8d534827f6254d20dbd89534827f6154d209f185534827f6054d20ded81534827e6514d20d754c534827e6414d209f590534835e6314d20db588534827c6214d209f984534827d6114d209fd97434827e65d0d209f597434827c65d0d20cfd53434833c54d0d20bb98b43482ed62d0d209fd96434827e6590d209f596434827c6590d20d7d4e434835c5390d20bb98a43482ed6290d209fd95434827e6550d209f595434827c6550d20cfd51434833c5450d20d7d4d434835c5350d209fd94434827e6510d209f594434827c6510d20e750c43482ee6210d20bb58843482fa6010d20be580434827e65d0920cfd53424833c54d0920b798f42482dd63d0920be98342482f960d09209f99642482de6390920b758e42482ee6590920db99642482ed6490920db952424836c5490920f398e42482ed6390920f358e42482cd6390920db94e424836c5390920ebd0e42483ad4390920bb58642482ee60909209f195424833f5450920cf15142482fb6050920be181424836c65509209b19542483af6450920ebd51424836e5450920db15142483ac5450920cb15142482ef6350920db94d424836c5350920eb90d42483ac4350920bbd8542483eb6050920bb18142483e860509209f99442482ee6210920eb508424827e65cc920af99332482bd64cc920d7d4f324835c53cc920be98332482f960cc9209f99632482be648c920af59232482ee658c920db99632482ef648c920eb99232482ed648c920eb59232482ad648c920db952324836c548c920bb58e324836e538c920db14e32483ce438c920f350e32482ed618c920bb982324827c654c920d7d4d324835c534c920bed8132482f8604c920db195324826c654c920bb
  | 11 => 0x7e63d52209f58f548836d62d52209f987548827d61d5220de983548833f54952209f98e548827d63952209f986548827d6195220cfd91548827f63552209f18d548827f61552209f185548833d5415220b798c54882dd6315220bd98454882f56115220cf990548827e6315220d798c548825e63152209f58c548835d63152209758c548836d62152209f984548837661152209d984548827d6115220dd58454882756115220de980548827e64d4e209f593538836d62d4e209f987538827d61d4e20de983538835f5394e209f992538827d6494e209f986538827d6194e209fd91538827c6454e20d7d8d538827f6154e209f18553882be6414e20af590538835d5314e20bd98453882f56114e209f990538833e6414e208f990538827d6414e20cf590538823d6414e20d798c538836d6214e209f98453883766114e209d984538827d6114e20dd58453882756114e20de980538827f65d0e209f997438827d65d0e209f197438833e54d0e20cf55343882ee62d0e20bb58b438827f6590e209f996438827d6590e209f196438835e5390e20d754e43882ee6290e20bb58a438827f6550e209f995438827d6550e209f195438833e5450e20cf551438835e5350e20d754d438827f6510e209f994438827d6510e209f194438839d4310e20be98043882f96010e20cf953428833d54d0a20b798f42882dd63d0a20be98342882f960d0a20b798e42882dd6390a20cf951428833d5450a20bed8142882f86050a20eb50842882be64cca20af593328835e53cca20d754f32882fa60cca20be58332882be648ca20af592328835e534ca20d754d32882fb604ca20be18132883cd320ca20ddd46518827e64946209f592518827e63946209f58e518837a60946209fd91518827c64546209fd8d518827c6354620af99051882bd6414620b798c51882dd6314620dd544518827f65d06209f997418827d65d0620cf953418833d54d06209fd96418827e65906209f59641883765190620dd54641882fa6090620be582418827f65506209f595418827c6550620cf951418833d5450620bbd8941882ec6250620dd945418837551506209fd94418827e65106209f59441882de6310620b758c41882ee6210620bb58841882fa6010620be580418827f65cc6209f997318827d65cc620d794f318835d53cc6209f996318827d658c620be98231882f9608c620dd94621883755188620be98221882f96088620dd94521883755148620bed8121882f86048620af99021882bd6408620b798c21882dd6308620be580218833f54d0220cf153408833e5490220cf55240882ee6290220bb58a408833f5450220cf151408833e5410220cf55040882de6310220b758c40882ee6210220bb58840882f66110220bd584408835f53cc220d714f308835e538c220d754e3
  | 12 => 0x90b20be98242c82f96090b20db59642c836e5490b20eb95242c83ad5490b20db15242c83ce6390b20bb58e42c83cd6390b20b358e42c836e5390b20db14e42c83af4390b20eb50e42c82ed6190b20bb98242c83ea6090b20fa58242c833f5450b20cf15142c82ef6550b20dbd9542c83af6450b20ebd5142c836e5450b20db15142c83ac5450b20cb15142c82ef6350b20db94d42c836c5350b20eb90d42c83ac4350b20bbd8542c82ec6050b20cf95042c833d5410b20eb50842c82fa6010b20be58042c82be64ccb20af59332c835f53ccb20d714f32c82be648cb20af59232c835e538cb20d754e32c82fa608cb20be58232c836d658cb20bbd9232c83ae648cb20bb59232c83ad648cb20ab59232c836e548cb20db15232c836e538cb20f394e32c83cd538cb20db14e32c83ce438cb20f350e32c82ed618cb20bb98232c83ea608cb20fa58232c835f534cb20d714d32c82ef654cb20dbd9532c82ef644cb20bb59132c836e544cb20db15132c83cf634cb20f3d4d32c836e534cb20db14d32c83cc534cb20d314d32c83cf434cb20f310d32c82ef614cb20bb18132c835e530cb20d754c32c83cd320cb20be98032c82f9600cb20ddd4651c827e64947209f59251c827e63947209f58e51c827f64547209f19151c827f63547209f18d51c836e4254720db50951c836e3254720db4c951c82be6414720af59051c82de6314720b758c51c837551147209fd9741c827e65d07209f59741c833e54d0720cf55341c82ee62d0720bb58b41c83ad42d07209fd9641c827e65907209f59641c82ee6290720bb58a41c827f65507209f59541c827c6550720cf95141c833d5450720eb50941c827f65107209f99441c827d6510720b798c41c82dd6310720bb98841c82ed6210720be98041c82f960107209f99731c827d65cc720bb98b31c82ed62cc720f34cb31c837651c8720dd54721c82fa60c8720be58321c82ef64c8720bb59321c836f54c8720db55321c82ed63c8720dbd4f21c836d53c8720db94721c83e651c8720f954721c82ee60c8720fa98321c83e960c8720bbd9521c836f6548720bbd9121c82ed6448720dbd5121c836d5448720bbd8d21c836f5348720db54d21c83e76148720f9d4521c836e5148720f914521c82ec6048720af99021c82bd6408720b798c21c82dd6308720dd94421c83755108720f948421c82fa6008720be58021c833e54d0320cf55340c82ee62d0320bb58b40c83ad42d0320cf95140c833d5450320bbd8940c82ec6250320eb50940c82de6310320b758c40c82ee6210320bb58840c82f66110320bd58440c835e53cc320d754f30c82ee62cc320bb58b30c83cd32cc320d794d30c835d534c320bbd8930c82ec624c320f34c930c82be640c320af59030c82ee620c320bb58830c82f6610c320bd58430c82
  | 13 => 0xdd545400c27f65100309f994400c27d65100309f194400c33e5410030cf550400c2de6310030b758c400c2ee6210030bb588400c36e5210030db548400c2f66110030bd584400c3765110030dd544400c33e54cc030cf553300c36e52cc030db54b300c37651cc030dd547300c35f54cc030e7953300c35d54cc030e7553300c31d54cc030f394b300c35d52cc030f354b300c34d52cc030f5947300c35d51cc030f5547300c35551cc030cf952300c33d548c030b758e300c35e538c030db94a300c36d528c030dd946300c375518c030ee952300c3b9548c030be58e300c37a538c030f694e300c3ea528c030fa54a300c3f2518c030de546300c3f1518c030dc546300c27f654c030cf951300c33d544c030db949300c36d524c030dd945300c375514c030b7d95300c35f654c03097d95300c35f544c030e7951300c35d544c030e7551300c31d544c030f3949300c35d524c030f3549300c34d524c030f5945300c35d514c030f5545300c355514c030b7d81300c35e504c030bed95300c37b654c0309ed95300c3ba544c030ee551300c2fb634c030f6d8d300c37a534c030f694d300c3ea524c030fa549300c3f2514c030de545300c3f1514c030dc545300c2de63d5320b758f54c827e63d5320d798f54c825e63d53209f58f54c835d63d53209758f54c836e62d53209f98754c827d61d5320de58354c833f5495320b798e54c82dd63953209f98e54c835e63953209798e54c827d6395320d758e54c825d6395320db98a54c827e61953209f58654c833f64553209fd8d54c827c63553209fd8554c827c6155320cf55054c833e64153209f98c54c827d6315320db98854c827e61153209f58454c83796015320af99353c82bd64d4f209f99353c833e64d4f208f99353c827d64d4f20cf59353c823d64d4f20db98b53c827e61d4f209f58753c837960d4f20af99253c82bd6494f20d7d4e53c827e6494f20cf99253c823e6494f209f59253c833d6494f208f59253c836e6294f209f98653c827d6194f209fd9153c827c6454f20d7d8d53c827f6154f209f18553c835d5314f209f99053c827d6414f20d798c53c836e6214f209f98453c827d6114f20de58053c827f65d0f209f99743c827d65d0f209f19743c833f54d0f20cf15343c835e53d0f20d754f43c82ee62d0f20bb58b43c827f6590f209f99643c827d6590f209f19643c833e5490f20cf55243c835f5390f20d714e43c82ee6290f20bb58a43c827f6550f209f99543c827d6550f209f19543c833f5450f20cf15143c835f5350f20d714d43c827f6510f209f99443c827d6510f209f19443c833e5410f20cf55043c835e5310f20d754c43c839d4310f20bb98843c82ed6210f20cfd5342c833c54d0b20b798f42c82dd63d0b20cf95242c833d5490b20b798e42c82dd63
  | 14 => 0x53510c2ee62d4430bb58b510c36e52d4430db54b510c33e5494430cf552510c36e5294430db54a510c37751944309f992510c27d64944309f98a510c27d6294430ddd52510c3765494430ed952510c3365494430dd552510c3b55494430cd552510c3745494430ddd4a510c3765294430f994a510c3665294430dd54a510c3e55294430d954a510c3745294430ddd92510c3766494430dd592510c3746494430dd18e510c3774394430dd90e510c3754394430dd10e510c3776294430dd98a510c3756294430dd18a510c3774294430dd90a510c3754294430dd10a510c3773294430dd8ca510c3753294430dd0ca510c3746094430cf951510c33d5454430db949510c36d52544309fd91510c27c64544309fd89510c27c6254430ddd95510c3775454430dd951510c3b65454430cd951510c3755454430ed551510c3355454430dd151510c3775254430dd949510c3e65254430d9949510c3755254430f9549510c3655254430dd149510c3776454430dd991510c3756454430dd191510c3766354430ddd0d510c3764354430dd50d510c3744354430ddd89510c3766254430dd589510c3746254430ddd09510c3764254430dd509510c3744254430ddcc9510c3763254430dd4c9510c3743254430dd981510c3743054430af990510c2bd6414430cf950510c33d5414430bb988510c2ed6214430db948510c36d5214430bd984510c37551144309fd97410c27e65d04309f597410c33e54d0430cf553410c36e52d0430db54b410c37651d0430dd547410c27f65904309f996410c27d6590430cf952410c33d5490430db94a410c36d5290430dd946410c37551904309fd95410c27d65504309f195410c33e5450430cf551410c2df6350430b718d410c36e5250430db549410c3765150430dd545410c27f65104309f994410c27d6510430cf950410c33d5410430b798c410c2dd6310430bb988410c2ed6210430db948410c36d5210430dd944410c3755110430be980410c2f960104309fd97210c27e65c84309f597210c33e54c8430cf553210c36e52c8430db54b210c37651c8430dd547210c27f65884309f996210c27d6588430cf952210c33d5488430db94a210c36d5288430dd946210c37551884309fd95210c27d65484309f195210c33e5448430cf551210c2df6348430b718d210c36e5248430db549210c3765148430dd545210c27e65084309f594210c33e5408430cf550210c36e5208430db548210c2fa6008430be580210c27e64940309f592500c27d65d0030cf953400c33d54d0030db94b400c36d52d0030dd947400c37551d00309fd96400c27d6590030cf952400c33d5490030b798e400c2dd6390030db94a400c36d5290030dd946400c37551900309fd95400c33e5450030cf551400c36e5250030db549400c376515003
  | 15 => 0xc33e6195030cf586540c33c6195030cf982540c33c6095030cfd91540c27f62550309f189540c27f61550309f185540c33f6555030cf98d540c33c6355030cfd89540c33e6255030cf589540c33c6255030cfd85540c33e6155030cf585540c33c6155030cf981540c33c6055030cf0c1540c2be6415030cf550540c2ee6215030bb588540c2f66115030bd584540c27e6415030cf990540c23e64150309f98c540c35e63150309798c540c27e6215030db988540c26e62150309f588540c36d62150309b588540c27e6115030dd984540c27661150309f584540c37561150309d584540c27e6015030de980540c27e6494c309f592530c27d65d0c30cf953430c33d54d0c30bb98b430c2ed62d0c309fd96430c27d6590c30cf952430c33d5490c30d794e430c2ee6290c30bb58a430c2fa6090c30be582430c27f6550c30cf951430c33d5450c30d794d430c27f6510c309f594430c33e5410c30cf550430c39d4310c30be980430c2f96010c30af993520c2bd64d4830cf953520c33d54d4830bd987520c2f561d4830cf952520c33d5494830dbd4a520c27e64948309f592520c27e61948309f586520c36f5494830db952520c3ae5494830cb952520c36d5494830eb552520c32d5494830db152520c36f6494830db992520c36d6494830db192520c36c6394830dbd0e520c36e4394830db50e520c36c4394830dbd86520c36e6194830db586520c36c6194830db982520c36c6094830cf951520c33d54548309fd91520c27c64548309fd85520c27c6154830dbd95520c36f5454830db951520c3ae5454830cb951520c36d5454830eb551520c32d5454830db151520c36f6454830db991520c36d6454830db191520c36e6354830dbd0d520c36e4354830db50d520c36c4354830dbd85520c36e6154830db585520c36c6154830db981520c36c6054830db0c1520c2be6414830af590520c33e5414830cf550520c2ee6214830db548520c2f66114830bd584520c27f65d08309f997420c27d65d0830cf953420c33d54d0830b798f420c2dd63d0830db94b420c36d52d08309fd96420c27e65908309f596420c33e5490830cf552420c2de6390830b758e420c36e5290830db54a420c27f65508309f595420c27c6550830cf951420c33d5450830db949420c36d52508309fd94420c27e65108309f594420c33e5410830cf550420c36e5210830db548420c3ad4210830af993320c2bd64cc830cf953320c33d54cc830d794f320c36e52cc830db54b320c2fa60cc830be583320c27d658c830af992320c2bd648c830cf952320c33d548c830db54a320c27f654c830cf951320c33d544c830d794d320c36e524c830cf950320c33d540c830db948320c36d520c830f34c8320c2fa600c830be580320c2be64d4430af593510c33e54d4430cf5
  | 16 => 0xe6390930b758e424c39d4390930dbd4a424c36c52909309fd95424c27e65509309f195424c33f5450930cf151424c39e4350930dbd49424c36c52509309f994424c27d65109309f194424c2de6310930b758c424c39d4310930eb508424c2fa6010930be580424c27e65cc930af993324c2bd64cc930b7997324c35e65cc930b7d93324c39e64cc930b7593324c39d64cc930a7593324c35e54cc930d7153324c35c52cc930f390b324c3cd42cc930b7587324c2de60cc930af992324c2bd648c930b758e324c36f528c930db14a324c2fa608c930be582324c36f524c930db149324c2fb604c930be181324c2df644c930b7591324c35e544c930d7151324c3cf624c930f3d49324c35c524c930f3149324c34c524c930f3d09324c3cc424c930b7d85324c3db604c930b7181324c3d8604c9309f994324c2de630c930f34c8324c27e64d45309f593514c35e43d4530d750f514c27e62d45309f58b514c35f32d4530d74cb514c3775194530afd91514c2bc6454530bbd89514c2ec6254530af990514c2bd6414530bb988514c2ed6214530dd544514c27e6414530cf990514c23e64145309f590514c33d64145308f590514c27e6214530db988514c26e62145309f588514c36d62145309b588514c27e65d05309f597414c27c65d0530cf953414c33d54d0530b798f414c2dd63d0530e750f414c27e65905309f596414c27c6590530cfd52414c33c5490530b798e414c2dd6390530be982414c2f960905309fd95414c27e65505309f195414c33e5450530cf551414c39d43505309f994414c27d65105309f194414c33f5410530cf150414c2de6310530b758c414c2ee6210530bb588414c2fa6010530be580414c27e65c85309f597214c27c65c8530b798f214c2dd63c8530f34cb214c27e65885309f596214c27c6588530b798e214c2dd6388530dbd4a214c36c5288530be982214c2f960885309f995214c27c6548530f34c9214c27e65d0130cfd53404c33c54d0130b798f404c2dd63d0130e750f404c27e65901309fd95404c27d65501309f195404c33f5450130cf151404c2df6350130b718d404c39d43501309f994404c2de6310130b758c404c2ee6210130bb588404c2f66110130bd584404c3da43cc130f650f304c3db32cc130f64cb304c2f961cc130b7d92304c2dd648c130b758a304c2dd618c130f6d42304c2ee62d5030bb58b540c2f661d5030bd587540c27e63d5030d798f540c27e62d5030db98b540c26e62d50309f58b540c36d62d50309b58b540c27e61d5030dd987540c27661d50309f587540c37561d50309d587540c27e60d5030de983540c27d6595030cfd52540c27e62950309f58a540c27e61950309f586540c23d6595030cf98e540c33c6395030cfd8a540c33e6295030cf58a540c33c6295030cfd8654
  | 17 => 0xa309fd96428c27e6590a309f596428c2de6390a30b758e428c36e5290a30db54a428c27f6550a309f595428c27c6550a30cf951428c33d5450a30db949428c36d5250a309fd94428c27e6510a309f594428c3ad4210a30be980428c2f96010a30af993328c2bd64cca30af992328c2bd648ca30db94a328c36d528ca30be982328c2f9608ca30db949328c36d524ca30bed81328c2f8604ca30f34c8328c37751946309f992518c27d64946309f98a518c27d62946309fd91518c27c64546309fd89518c27c6254630af990518c2bd6414630bb988518c2ed6214630dd544518c27f65d06309f997418c27d65d0630cf953418c33d54d06309fd96418c27e65906309f596418c3765190630dd546418c2fa6090630be582418c27f65506309f595418c27c6550630cf951418c33d5450630b7d8d418c2dc6350630dd945418c37551506309fd94418c27e65106309f594418c2de6310630b758c418c2ee6210630bb588418c2fa6010630be580418c27f65c86309f997218c27d65c8630db94b218c36d52c86309f996218c27d6588630be982218c2f96088630cfd53408c33c54d0230cf952408c33d5490230b798e408c2dd6390230cfd51408c33c5450230cf950408c33d5410230b798c408c2dd6310230bb988408c2ed6210230bd984408c2f56110230b7597308c35d65cc230d7d53308c35d54cc230d754b308c35d51cc230be597308c37965cc230be587308c27e62d51309f58b544c27e61d51309f587544c33f5495130bb98a544c2ed62951309f992544c27d6395130d758e544c27e6295130db98a544c26e62951309f58a544c36d62951309b58a544c27e61951309f586544c27d6095130de582544c33f64551309fd8d544c35f63551309fd89544c27c62551309fd85544c27c61551309fd81544c37b60551309f994544c33d5415130cf990544c35d63151309f988544c27d62151309f984544c27d61151309f997434c33f54d0d30cf153434c2ee62d0d30bb58b434c2fa60d0d30be583434c27e6590d30bb98a434c2ed6290d30b7996434c35e6590d30b7592434c35e5490d30d7152434c3ce6290d30b758a434c3cd6290d30b358a434c2dd6190d30b7982434c27c6550d30cfd51434c33c5450d30bed81434c2f86050d30d7195434c25c6550d30e7d91434c39f5450d30d7951434c35c5450d30e7151434c31c5450d30b7d89434c2df6150d30f6d81434c2dc6050d30f6181434c27e6510d30b798c434c39d4310d309f993524c27d64d49309f987524c27d61d4930af992524c2bd6494930dbd4a524c36d52149309f990524c27d6414930d790c524c35d43149309f984524c27d61149309f997424c27d65d09309f197424c33f54d0930cf153424c2de63d0930b758f424c39e43d09309f996424c27d65909309f196424c2d
  | 18 => 0xdb54852cc27f65d0b309f99742cc27d65d0b30cfd5342cc33c54d0b30b798f42cc2dd63d0b30e790f42cc36e52d0b30db54b42cc27f6590b309f99642cc27d6590b30cf95242cc33d5490b30b798e42cc2dd6390b30e750e42cc27f6550b309f59542cc27c6550b30cfd5142cc33c5450b30e790d42cc27f6510b309f99442cc27d6510b30cf95042cc33d5410b30b798c42cc2dd6310b30e750c42cc36e5210b30db54842cc3ad4210b30af99332cc2bd64ccb30db94b32cc36d52ccb30be98332cc2f960ccb30b7d9332cc39e64ccb30b759332cc39d64ccb30a759332cc35e54ccb30d715332cc35e52ccb30f394b32cc3cd52ccb30f390b32cc3cd42ccb30b758732cc2de60ccb30f698332cc3d960ccb30af99232cc2bd648cb30b7d9532cc35f654cb30b7d9132cc2dd644cb30d795132cc35c544cb30f3d8932cc3cf524cb30d794932cc3cc524cb30f3d0932cc3cc424cb30b7d8532cc2dc604cb30db94832cc36d520cb30f34c832cc2fa600cb30be58032cc37751947309f99251cc27d64947309f98a51cc27d62947309fd9151cc27c6454730d790d51cc35d43547309fd8951cc27c6254730d7cc951cc35d3254730af99051cc2bd6414730bb98851cc2ed6214730dd54451cc27f65d07309f99741cc27d65d0730cf95341cc33d54d0730b798f41cc2dd63d0730e750f41cc27f65907309f99641cc27d6590730b798e41cc2dd63907309fd9541cc27d65507309f19541cc33e5450730cf55141cc39d43507309fd9441cc27e65107309f59441cc2de6310730b758c41cc2ee6210730bb58841cc2fa6010730be58041cc27e65c87309f59721cc36e52c8730db54b21cc3cd32c8730cf95340cc33d54d0330b798f40cc2dd63d0330e750f40cc33e5450330cf55140cc2df6350330b718d40cc39d4350330b798c40cc2dd6310330bb98840cc2ed6210330bd98440cc2f56110330d758f548c27e62d52309f58b548c27e61d52309f587548c37a60d5230cfd52548c27e62952309f58a548c27e61952309f586548c33f64552309fd89548c27c62552309fd85548c27c6155230cf550548c2ee6215230bb588548c2f66115230bd584548c33e6415230d758c548c27e6215230db988548c26e62152309f588548c36d62152309b588548c27e6115230dd984548c27661152309f584548c37561152309d584548c37a6015230cf953438c33d54d0e30bb98b438c2ed62d0e30be983438c2f960d0e30bb98a438c2ed6290e30cf951438c33d5450e30bed81438c2f86050e30e750c438c36f5294a309f992528c27d6494a309f986528c27d6194a309fd91528c27c6454a309fd85528c27c6154a30af990528c2bd6414a30db548528c2f66114a30bd584528c27f65d0a309f997428c27d65d0a30cf953428c33d54d0a30b798f428c2dd63d
  | 19 => 0x151103746054440dd10151102de6314440b758c511035e5314440d754c51102ee6214440bb588511036e5214440db54851102f66114440dd544511033e54d0440d794f411035d53d0440db94b411036d52d0440dd947411037551d0440be98341102f960d04409f596411035e5390440d754e411036e5290440db54a411037551904409fd95411033e5450440d794d411035d5350440db949411036d5250440dd94541102ee6210440bb588411036e5210440db54841102fa6010440be580411035e53d0040d754f401036e52d0040db54b401037651d0040dd547401039e53d0040cf54f401039d53d0040c754f40103ae52d0040cf54b40103ad52d0040cb54b40103b651d0040cf54740103b551d0040cd54740102bd6490040cf952401035e5390040d754e401036e5290040db54a40103765190040dd54640102f96490040de95240103ba5490040f694e40103d95390040fa94a40103e95290040fc94640103795190040fc546401037151900409fd95401035e5350040d754d401036e5250040db54940103765150040dd54540102bf6550040cfd95401023f6550040e794d401033d5350040e754d401031d5350040eb949401033d5250040eb549401032d5250040ed945401033d5150040ed54540103355150040afd81401033e5050040bed95401037b65500409ed9540102fb6450040eed91401037a5450040ee95140103da5350040f654d40103ea5250040fa54940103f25150040de54540103f15150040dc54540103bb4150040ee50540102ee62d5330bb58b54cc35e63d53309f98b54cc36e62d53309b98b54cc27d62d5330db58b54cc26d62d53309f98754cc27d61d5330de58354cc33f5495330bb98a54cc2ed6295330d798e54cc27e6295330db98a54cc26e62953309f58a54cc36d62953309b58a54cc27e61953309f58654cc33f64553309fd8954cc27c62553309fd8554cc27c6155330cf55054cc33e6415330d798c54cc27e62153309f58854cc27e61153309f58454cc3796015330cfd5343cc33c54d0f30bb98b43cc2ed62d0f30cf95243cc33d5490f30bb98a43cc2ed6290f30be98243cc2f96090f30d759643cc35e5490f30e795243cc39d5490f30d715243cc3ce6290f30b758a43cc3cd6290f30b358a43cc2dd6190f30b798243cc3da6090f30f658243cc33f5450f30cf15143cc2df6550f30d7d9543cc39f6450f30e7d5143cc35e5450f30d715143cc39c5450f30c715143cc2df6250f30b7d8543cc2dc6050f30cf95043cc33d5410f30e750c43cc2fa6010f30be58043cc2be64d4b30af59352cc2be6494b30af59252cc36f5294b309f99252cc33e6494b308f99252cc27d6494b30cf59252cc23d6494b30d790e52cc35d4394b309f98652cc27d6194b309fd9152cc27c6454b309fd8552cc27c6154b30
  | 20 => 0x36f6394840db98e521036d6394840db18e521036f4394840db90e521036d4394840db10e521036f6194840db986521036d6194840db186521036e6094840db182521035e5354840d754d521027f63548409f18d521027f61548409f185521036f6554840dbd4d521036e5354840f394d521034e5354840db54d52103cd5354840d354d521036c5354840db991521036f6354840db98d521036d6354840db18d521036f4354840db90d521036d4354840db10d521036f6154840db985521036d6154840db185521036e6054840db181521036c4054840b798c52102dd6314840d794c521035d5314840bb988521036d5214840bd98452102f56114840cf95342102de63d0840b758f421035e53d0840d754f421036e52d0840db54b42102fa60d0840be583421027d6590840b798e42102dd6390840d794e421035d5390840db54a421027f6550840cf951421035e5350840d754d421036e5250840d794c421035d5310840db948421036d5210840eb50842102fa6010840be580421027f65cc8409f997321027d65cc840af99332102bd64cc840d794f321035d53cc840db94b321036d52cc8409fd96321027e658c8409f59632102be648c840af592321035e538c840d754e321036e528c840db54a321027f654c8409f595321027c654c840d794d321035d534c840db949321036d524c8409fd94321027e650c8409f594321035e530c840d754c321036e520c840db54832103cd320c840b798f51102dd63d4440d794f511035d53d4440bb98b51102ed62d4440db94b511036d52d4440d794e511035d5394440db94a511036d5294440ddd46511027e63944409f58e511027e62944409f58a51103775394440dd94e51103d65394440d594e51103755394440f554e51103555394440dd14e51103775294440dd94a51103e65294440d994a51103755294440f954a51103655294440dd14a51103746494440ddd8e51103766394440dd58e51103746394440ddd0e51103764394440dd50e51103744394440ddd8a51103766294440dd58a51103746294440ddd0a51103764294440dd50a51103744294440ddcca51103763294440dd4ca51103743294440dd98251103746094440d794d511035d5354440db949511036d52544409fd8d511027c63544409fd89511027c6254440ddd9551103775354440dd94d51103d65354440d594d51103755354440f554d51103555354440dd14d51103775254440dd94951103e65254440d994951103755254440f954951103655254440dd14951103766454440ddd8d51103766354440dd58d51103746354440ddd0d51103764354440dd50d51103744354440ddd8951103766254440dd58951103746254440ddd0951103764254440dd50951103744254440ddcc951103763254440dd4c951103743254440dd98
  | 21 => 0x63d0940cf14f425033c52d0940af58742502be60d0940af59242502de6390940b758e425036f5290940db14a42502fa6090940be582425036f5250940db14942502fb6050940be18142502bf6350940cf14d42503af6250940ebd49425033c5250940eb149425032c5250940afd8542503bb6050940af18142503b860509409f99442502be6410940eb508425027e65cc9409f597325027c65cc940af99332502bd64cc940d7d4f325035c53cc940e7d0f32503ad42cc9409f996325027d658c9409f19632502be648c940af592325039d438c940dbd4a325036c528c940ebd0a325027f654c9409f995325027c654c940af99132502bd644c940d7d4d325035c534c940e7d0d325036f524c940db14932503af424c9409f994325027d650c9409f19432502be640c940af590325039d430c940eb50832503cd320c940be98032502f9600c9409f98f515027d63d4540cfd0f515033d43d45409f98b515027d62d4540cfd0b515033d42d4540ddd4651502df6354540b718d51502ef6254540bb18951502de6314540b758c51502ee6214540bb588515037551145409f98c515035e63145409798c515027d6314540d758c515025d63145409f988515036e62145409b988515027d6214540db588515026d6214540af997415033e65d0540af58f415033f53d0540af58b415033f52d0540cf14741503bb60d0540af98341503b860d0540af59241503775190540dd14641502fa6090540be58241502fb6050540be18141502bf6250540cfd4941503bb6050540af18141503b86050540eed0f40503b943d0140eed0b40503b942d0140be58740503bb41d0140ee50740502bd6390140af58a40502bd6190140eed4240502ee62d4c40bb58b53102f661d4c40bd587531035f5394c409f98a531027d6294c409f986531027d6194c40d7192531035f6294c40d798a531035d6294c40d718a531035f6194c40d7986531035d6194c40d7186531035e6094c40d7182531027f6254c409f189531027f6154c409f185531035f6554c40d7991531035f6254c40d7989531035d6254c40d7189531035f6154c40d7985531035d6154c40d7185531035e6054c40d7181531035c4054c40b798c531035d5314c40bb98853102ed6214c40bd98453102f56114c40cf953431035e53d0c40d754f43102ee62d0c40bb58b43102fa60d0c40be583431027d6590c40d754e43102ee6290c40bb58a431027f6550c40cf951431035e5350c40d794c431035d5310c40e750c43102fa6010c40be58043102de63d4840b758f521035e53d4840d754f52102f661d4840bd587521035e5394840d754e521036f52948409f98e521027d63948409f986521027d6194840dbd4e521036e5394840f394e521034e5394840db54e52103cd5394840d354e521036c5394840db192521
  | 22 => 0xb40af59132d039f434cb40ebd0932d027f650cb409f99432d027d650cb40af99032d02bd640cb40d794c32d035d530cb40e750c32d036e520cb40db54832d03ad420cb40f34c832d037751947409f98e51d027d63947409f98a51d027d62947409fd8d51d027c6354740cfd0d51d033d43547409fd8951d027c6254740cfd0951d033d4254740b798c51d02dd6314740bb98851d02ed6214740dd54451d02fa60d0740be58341d02bd62d0740cf54b41d02be60d0740ee98341d03b960d0740d7d4e539027e6294e409f58a539027e6194e409f586539027f6254e409f189539027f6154e409f185539035d5314e40bb98853902ed6214e40bd98453902f56114e40bb98b43902ed62d0e40d794e439035d5390e40bb98a43902ed6290e40be98243902f96090e40d794d439035d5350e40bed8143902f86050e40e750c439036f5294a409f98e529027d6394a409f986529027d6194a409fd8d529027c6354a409fd85529027c6154a40b798c52902dd6314a40db54852902f66114a40bd58452902de63d0a40b758f42902de6390a40b758e429036e5290a40db54a42902fa6090a40be582429036e5250a40db54942902fb6050a40be18142903ad4210a409fd97329027e65cca409f59732902be64cca40af593329035e53cca40d754f329027f658ca409f996329027d658ca40af99232902bd648ca40db94a329036d528ca409fd95329027d654ca409f195329035e534ca40d754d329036e524ca40db549329027f650ca409f994329027d650ca40f34c832902fa600ca40be580329037751946409f98e519027d63946409f98a519027d62946409fd8d519027c63546409fd89519027c6254640b798c51902dd6314640bb98851902ed6214640dd54451902fa6090640be58241902bd65d0240cf597409033d53d0240cf54b409033d51d0240be597409037965d0240be587409027e62d4d409f58b535027e61d4d409f587535035f5394d40bb98a53502ed6294d40d754c535027e6214d409f588535027e6114d409f584535027e65d0d40bb98b43502ed62d0d40af997435033e65d0d40cf14f43503ae62d0d40af58b43503ad62d0d40ab58b43502bd61d0d40af98343502bd6490d40d7d4e435035c5390d40bb98a43502ed6290d40be98243502f96090d40d7d4d435035c5350d40bed8143502f86050d40e7d8d435039f5350d40cf14d435039c5350d40c714d43502bf6250d40afd8543503bb6050d40af18143503b86050d409f99443502be6410d40e750c435027e63d49409f58f525027e61d49409f58752502de6394940b758e525036f5294940db548525027e63149409f58c525033f4314940cf50c525027e61149409f584525027e65d0940b798f42502dd63d0940af997425033e65d0940e798f42502bd63d0940e758f425029d
  | 23 => 0xfd94420ca7e65108329f594420ca7c6510832cf950420cb3d5410832b798c420cadd6310832e750c420caee6210832db948420cbad4210832af992320cabd648c832bbd92320cbae648c832bb592320cbad648c832ab592320cb6e548c832db152320caed638c832b358e320cb6e538c832f394e320cbce438c832f350e320ca7f654c832bbd95320cb6f654c8329bd95320caef644c832bb591320cb6e544c832db151320caef634c832db94d320cbce534c832f3d0d320cbce434c832f350d320cbcc434c832f3d95320cacf654c832d3d95320cbcf644c832b3d91320cbce644c832f3591320cacd644c832f3191320cbcf544c832f3951320cb4e544c832f3551320cbcc544c832d3151320cbcf604c832f3981320cbcd604c832f3181320cbcd32d4032f34ca500cb7b50940329f992500ca7d64940329f986500ca7d6194032f34c9500ca7f64540329f191500cb5e4354032d750d500cb6e4254032db509500cb5f3254032db8c9500cb5d3254032db4c9500cb4d32540329fd85500ca7c6154032af990500cabd6414032f34c8500caf66114032bd584500cb795014032bb98b53d02ed62d4f40d7d4e53d02ee6294f40bb58a53d027e6294f40db98a53d026e6294f409f58a53d036d6294f409b58a53d027e6194f409f58653d027f6254f409f18953d027f6154f409f18553d035d5314f40d794f43d035d53d0f40bb98b43d02ed62d0f40be98343d02f960d0f40cf94f43d039e53d0f40e754f43d03ae62d0f40af58b43d03ad62d0f40ab58b43d02bd61d0f40af98343d03ba60d0f40ee58343d02ee6290f40bb58a43d02bf6550f40cfd9543d039f6350f40e7d4d43d033e5350f40e714d43d02bf6250f40afd8543d02bc6050f40d794c43d035d5310f40e750c43d02fa6010f40be58043d02de63d4b40b758f52d02de6394b40b758e52d036f5294b409f98e52d035e6394b409798e52d027d6394b40d758e52d025d6394b40cfd0e52d033d4394b409f98652d027d6194b409fd8d52d027c6354b409fd8552d027c6154b40db54852d02de63d0b40b758f42d036e52d0b40db54b42d02fa60d0b40be58342d039e63d0b40af58f42d039d63d0b40a758f42d033e53d0b40cf94b42d03ae52d0b40eb54b42d02bd61d0b40af98342d03ba60d0b40ee58342d02de6390b40b758e42d02bf6550b40cfd9542d02bf6350b40cf94d42d03af6250b40ebd4942d033e5250b40eb14942d02bf6150b40af18142d036e5210b40db54842d03ad4210b40be98042d02f96010b409fd9732d027e65ccb409f59732d02be64ccb40af59332d039f43ccb40db94b32d036d52ccb40eb50b32d027f658cb409f99632d027d658cb40af99232d02bd648cb40d794e32d035d538cb40e750e32d03af428cb409fd9532d027d654cb409f19532d02be644c
  | 24 => 0x508cb3e5494232cf552508cb7b50942329f992508ca7d64942329f986508ca7d6194232cf951508cb3d54542329fd91508ca7c6454232d790d508cb5d4354232d7cc9508ca7f61542329f185508cabe6414232af590508cb3e5414232cf550508caf66114232bd584508cb795014232db58b544ca7e60d51329f583544cb3f54951329f992544ca7d6295132db58a544ca6d62951329f982544ca7d6095132cfd91544ca7f6255132dbd89544ca7f60551329f181544ca7e6515132cf550544cb3e64151329f980544ca7d60151329f997424cb3f54d0932cf153424cade63d0932b758f424cb6e65d09329b997424cb6f54d0932ebd53424cb6d54d0932eb153424caee63d0932f398f424cace63d0932f358f424cbcf43d0932bb587424caed60d09329f996424cb3e5490932cf552424cade6390932b758e424cb9f4390932bb98a424ca7f65509329f595424ca7c6550932cfd51424cb3c5450932b7d8d424cadc63509329f994424cb3e5410932cf550424cb9f4310932eb508424caee6510932db994424ca6e6510932bb990424cbae6410932dbd50424cbae5410932db550424cbad5410932cb550424cbcf6310932bb98c424cbcc6310932ebd0c424cbcf4310932e3d0c424cbad4310932f310c424caed6110932bb580424cabe648c932af592324cade648c932e7992324ca9e648c932e7592324cadc648c932d7d52324cb5d548c932f3d4a324cbcf428c932f310a324cadd618c932b7582324ca7e64d41329f593504ca7e61d41329f587504cb7b5094132af990504cabd6414132bd984504caf56114132de540504ca7e6414132cf990504ca3e64141329f590504cb3d64141328f590504ca7e6114132dd984504ca7661141329f584504cb7561141329d584504ca7e62d5032db98b540ca6e62d50329f983540ca7d60d50329f596540cb3f5495032db98a540ca7e60950329f582540cb3f64550329fd81540ca7c6055032cf550540cafa6015032be580540ca7e6415032cf990540ca7e6215032db988540ca7e6015032de980540ca7a60150329f580540cb7960150329e580540ca7e6494832cf992520ca3e64948329f592520cb3d64948328f592520ca7d65d0832cfd53420cb3c54d0832b758f420cb6e52d08329fd96420ca7d6590832cf952420cb3d5490832b798e420cadd6390832bb596420cb6d65908329b596420caed6490832db952420cbae5490832eb552420cb6c5490832f398e420caed6390832f358e420cacd6390832db94e420cbaf4390832f390e420ca7f6550832cfd51420cb3c5450832e790d420caef6550832dbd95420ca6f6550832ebd91420cbaf5450832db951420cb6c5450832eb151420cb2c5450832bbd8d420cbce6350832f358d420cb6e5350832eb90d420cbce4350832e390d420cbcd43508329
  | 25 => 0xbad42d4042eb50a5010b7b50940429f98e5010a7d63940429f9865010a7d6194042eb5095010a7f63540429f18d5010b3f4354042cf50d5010b3f4254042db9095010b3d4254042db5095010b2d42540429fd855010a7c6154042b798c5010add6314042eb5085010af66114042bd5845010b795014042d758f548cb6e62d52329f987548ca7d61d52329f983548ca7d60d5232cfd52548cb5d63952329f986548ca7d61952329f982548ca7d6095232e758e548cbac6295232cfd8e548cb3d6395232c758e548cb3e6295232cf18a548cb3f6195232cf986548cb3d6195232cf186548cb3f6095232cf982548cb3d6095232cf182548cb3f6455232db189548ca7f61552329f185548ca7f60552329f181548cb3f6555232e758d548cbac6255232cfd8d548cb3d6355232cf989548cb3c6255232cb189548cb3f6155232cf985548cb3d6155232cf185548cb3f6055232cf981548cb3d6055232cf181548cb3d5415232cf990548cb5d6315232db988548ca7e61152329f584548ca7e60152329f580548cb3e54d0e32cf553438caee62d0e32bb58b438cb3e5490e32cf552438caed6290e32b7596438cb5d6590e32d7952438cb9e5490e32c7952438cb9d5490e32d7152438cbce6290e32b758a438cbcd6290e32b358a438cb3e5450e32cf551438caef6250e32bb189438cb5f6550e32e7d91438cb5e5450e32e7951438cb1e5450e32e7551438cb5c5450e32b7d89438cbcf6250e32f3189438cb3e5410e32cf550438cb9d4310e32cf953428cb3d54d0a32b798f428cadd63d0a32e790f428caed65d0a32db597428cb6f54d0a32eb953428cb6d54d0a32eb553428cb2d54d0a32bb98f428cbce63d0a32b398f428cbcd63d0a32eb90f428cbce43d0a32f350f428cbac43d0a32bb587428caed60d0a32cf952428cb3d5490a32b798e428cadd6390a32e750e428cb3e5450a32cf551428cb9e4350a32cf950428cb3d5410a32b798c428cadd6310a32e750c428cbad4210a32bb594428cb6d6510a32eb990428cb6f5410a32eb950428cb6d5410a32eb550428cb2d5410a32bb98c428cbce6310a32f358c428cbaf4310a32f390c428cbad4310a32f350c428cb8d4310a32bb584428caed6010a32cf953328cb3d54cca32bb597328cb6d65cca32bb993328cbae64cca32ab993328cbad64cca32bb193328cb6f54cca32eb953328cb6d54cca32eb553328cb2d54cca32af993518cabd64d4632cf953518cb3d54d4632cf952518cb3d5494632ddd46518ca7e64946329f592518ca7e60946329f582518cb3e5454632cf551518ca7f64546329f191518cb5e4354632d750d518cb5f32546329fd81518ca7c6054632af990518cabd6414632cf950518cb3d5414632dd544518cafa6014632be580518cabe64d4232af593508cb3e54d4232cf553
  | 26 => 0x390d42bb98a4350aed6290d42cfd4e4350b9f5390d42e714e4350abe6290d42eb98a4350aae6290d42eb58a4350abd6190d42af5824350aef6250d42bb1894350ade63d0942b758f4250aee63d0942f398f4250ace63d0942f358f4250b6f53d0942eb90f4250aed61d0942bb5834250ade6390942b758e4250abe6390942e798e4250a9e6390942e758e4250b3f5390942ebd4a4250abd6190942af5824250a7e63d45429f58f5150a7e60d45429f5835150b775194542b798c5150add6314542dd5445150afa6014542be5805150a7e6314542d798c5150a5e63145429f58c5150b5d63145429758c5150a7e6014542de9805150a7a60145429f5805150b7960145429e5805150a7e63d41429f58f5050a7e61d41429f5875050b7b5094142b798c5050add6314142bd9845050af56114142de5405050a7e6314142d798c5050a5e63141429f58c5050b5d63141429758c5050a7e6114142dd9845050a7661141429f5845050b7561141429d5845050b5e6395042d758e5410b5f5394c42db98a5310a7e6194c429f5865310a7e6094c429f5825310a7f6154c429f1855310a7f6054c429f1815310b5d5314c42bd9845310af56114c42be9805310af96014c42d794f4310b5d53d0c42bb98b4310aed62d0c42cf94f4310b9e53d0c42e754f4310bae62d0c42af58b4310bad62d0c42ab58b4310a7d6590c42af5924310aed6290c429fd954310abf6550c42cfd954310a3f6550c42e7d8d4310b9f5350c42cf94d4310b9c5350c42afd894310bae6250c42eb5894310b3e5410c42bb9884310aed6210c42d798e5210b5d6394842cfd0e5210b3d4394842b798f4210add63d0842e798f4210abd63d0842e758f4210a9d63d0842cf94f4210abd6490842cf9524210ade6390842b758e4210aed6490842ab5924210b6e5490842eb9524210bce6390842bb58e4210bcd6390842b358e4210b6e5390842ebd0e4210bad43908429fd954210abf6550842cfd954210a3f6550842afd8d4210b3e5350842afd894210b3e5250842bbd954210b6f65508429bd954210aef6450842ebd914210b6e5450842eb9514210aef6350842db94d4210baf4350842eb90d4210bad4350842eb10d4210baf6550842abd954210b2f6550842ebd8d4210aaf6350842eb98d4210bad6350842eb18d4210baf5350842eb94d4210b2e5350842eb54d4210bac5350842ebd854210bae6150842eb5854210bac6150842ebd814210bae6050842eb5814210bac6050842eb50b5110bad4294442ddd465110a7e63944429f58e5110a7e60944429f5825110bad42544429fd8d5110a7c6354442cfd0d5110b3d4354442cfd095110b6e4254442cf5095110b6d4254442cb5095110a7f60544429f1815110ade6314442b758c5110bad4214442dd5445110afa6014442be5805110
  | 27 => 0x42d7d8253d0b5e6094f42d758253d0b5c6094f429fd8553d0a7c6154f429fd8153d0a7c6054f42d7d9553d0b9c6454f42f358953d0b5e6454f42d758953d0b5f6154f42d798553d0b5d6154f42d718553d0b5f6054f42d798153d0b5d6054f42d718153d0b5d5314f42bb98b43d0aed62d0f42b798f51d0add63d4742d794f51d0b5d53d4742d794e51d0b5d5394742ddd4651d0a7e63947429f58e51d0a7e60947429f58251d0b5e5354742d754d51d0a7f63547429f18d51d0a7f60547429f18151d0ade6314742b758c51d0b5e5314742d754c51d0b755114742be98051d0af96014742b798f50d0add63d4342d794f50d0b5d53d4342d794e50d0b5d5394342ded4250d0a7e63943429f58e50d0a7e61943429f58650d0b5e5354342d754d50d0a7f63543429f18d50d0a7f61543429f18550d0ade6314342b758c50d0b5e5314342d754c50d0af66114342bd58450d0b795014342d7d4e5390a7e6194e429f5865390a7e6094e429f5825390b9d6494e42f318a5390b5f6494e42d718a5390b5f6194e42d79865390b5d6194e42d71865390b5f6094e42d79825390b5d6094e42d71825390b6c6254e429fd855390a7c6154e429fd815390a7c6054e42d7d955390b9d6454e42f31895390b5d6454e42d79895390b5c6254e42d31895390b5f6154e42d79855390b5d6154e42d71855390b5f6054e42d79815390b5d6054e42d71815390b5d5314e42d794f4390aed62d0e42af5974390b3d65d0e42cf94f4390b9e53d0e42c794f4390b9d53d0e42eb98b4390abd62d0e42eb58b4390aad62d0e42bb98a4390aed6290e42b798f4290add63d0a42d794f4290b5d53d0a42af5974290b3d65d0a42e798f4290abd63d0a42e758f4290a9d63d0a42cf94f4290b9e53d0a42c794f4290b9d53d0a42bb5974290b6d65d0a42bb98f4290bce63d0a42b398f4290bcd63d0a42f394f4290b6d53d0a42f354f4290b4d53d0a42bb5874290aed60d0a42b798f5190add63d4642d794f5190b5d53d4642d794e5190b5d5394642ddd465190a7e63946429f58e5190a7e60946429f5825190b5e5354642d754d5190a7f63546429f18d5190b3f4354642cfd095190a7f60546429f1815190ade6314642b758c5190b5e5314642d754c5190b755114642be9805190af96014642b798f5090add63d4242d794f5090b5d53d4242d794e5090b5d5394242ded425090a7e63942429f58e5090a7e61942429f5865090b5e5354242d754d5090a7f63542429f18d5090b3f4354242cfd095090a7f61542429f1855090ade6314242b758c5090b5e5314242d754c5090af66114242bd5845090b795014242db58b5350a7e61d4d429f5875350a7e60d4d429f5835350b5f5394d42d754c5350a7e6114d429f5845350a7e6014d429f5805350aee62d0d42d7d4e4350b5c5
  | 28 => 0x40010010007000800000200010018002000000500340020008003001800a0000003000800d000c006000400a00040050000000000000b001c00d001000100300010000000000c00100000010000000000000600000060004020000400000040000000000000400000080000000009000400200200050010000002400300100030000001001800000000090004004000c00200040040000001001c00400100100010000000400100000040000000000000700080030008005002000400000020004009000000000080030000000000400200040010000001000c0020008002000c000001000000000070034001000c0000030005001400000180030004000001c001001c001001000000000020004006000c0020000004000400000000070004002000000300000060048001000c00000040030000001000c01800000020000000001000100000000024001000400f0000005000c000000c007000000000040000004003000400200000050034001000c00200000070000000000000000040000004009000800100000000028005001c000007c00000280080070002002c0000004000000c00300000030000001001c001001400a000000000d40010000000001000100000020000004000000800000010000000002c00000000000000001001000000540020000000000c002000400000040010000004000000000040000000008002400100100030008001000c00a0000000000000000080000000003000c00000040090008009000800c0014000003000300080000018000001400200080080018001000001400180000014000000c011000c00100280000004002001c0020000006000000300080000004000000000100040030028014000000000080000000002000000b000000400000020044000000800100000020048001000800200300000020000000000600000030014000000c00500100040000001000000000000000028000000800000100000000004001000300000000010001000400400000000000001000400000000030008012006c001003c000000000200140000000000000c00400000020008003000000000040060014001000000100000030004012000000000080000010000001c0000000006000400100000060004001002c00c0000005001400100000020004001000000400600070058003000800e000000100280040008002001c00b006c00300000000008003001400000100000010003001c005001400300040000050001000c00200000000000002001c0000000007000000200400030000003003c0090010000004c006003400300100000004000001000100235f5394f429f98653d0a7d6194f429f98253d0a7d6094f42e719253d0bcd6294f42d719253d0b5f6294f42d7d8653d0b5e6194f42d758653d0b5c6194f
  | 29 => 0x400000010000002004c0010000004000000500000030004000001c0010004003002c000000800400000000030002007000000100050008000003c000000400100080040004006000000000040010024000000000000180030010005000c00000000000000006000000500000000000007000800100000140014001001c00c0038002000c004002c00000000000000000000400400180010000001000400d000400a001c003000c00300000010000000000400b000400300100070008000000000500000030018000000c00100080000008000000c0010020004001000c001c001000000500100010008001000000000080000048000000400000000050000016000001f000000400200020040001000c00a000000100080010000000002000200000040000000000800100400000008001000000200000010018000000000300200040000000000c00800000080000002001c002000400700080000010002000c0130008000000c002000000e00240010004000000000000280010010006000000000040020000000001803a00040000000000001c00100400080004008005000000240000018000000c000000800100c400000000010000002000400000040010020000001c000001400000040000008000000400000240030010000000000100080000004007001000500140010004016000000600000020034001001c0010030000000c000000c00000140010000000000c0020008000000800000100010000001002c000002c002001000b004c00a000401500100000004000003c00200140010010000000400600240000010003000400000000000000005000400500040000030002000400600100000000013001000100000030004000000c003000000400000000004000004c003000400700000090014001002000a000400000080020008009000c000001c0020004003000c0040000000000000000080000000000000c0020000006000c00100000000000001000000300000010004001000400300140020008000000400400000010004000000000400240000000002000000f00300010000000000000000240020008003000000100040010008000000400100040060000000002c00b000000000000010004000005c0000030001000000200100030000000001c0000040003000000000100000000003000001f001400100200000004009002000200080030000000000001a0004002000400300000000008000003c00200000000000011000800000440030010006000800700140040054003000400b002800300200000010009000c00000000010004000000400000080050008002002c000000000000000000000000001c00100000000000003000001400040060004001000000000040050000003000000900380080004002000000300
  | 30 => 0x3001000100040040000000000400c0004002002000200040160000001002c0010000000000000000000000000003000000100000000000003005c00c00700000000006001c003001400200000020000000000400000240040004001000000200200040008001001c0000030000000000700040030010000000800000480160044009000c0050004006001800c0018004000400300000000000002000800600040000000003000400700180010008001000000d00300000008000002c0010000002000800100140000004003000400100100090018000003c003000800d002800000040000000001000c003000000500300040000007001c0000010002000800800200000000004000400100080010000000000000300000000000000000c0050000000001800000180000000019000800b000c000000800300040020000000000800000000040004004001000000180010008000000400700000010000001001c0000008000000c000000800f00180190014000000c00200300010004000001800000400010004000001000a000000000040080018000000800000100020028001001400100340050000000001c0130000000000800200000000014000000001100000120020001000000300000150018000005000c002000a0000004000400000180000040000000c002000800100040030004001001c003000800000100000000000000800000040020000009005c00c000c00000040060004002000000000000130004000002c00000300010000000000000200a4000000000f0004001000000000180000000000000001e0004008000000700000060020002000c001000c00800000020000000000c00000040000008000000400a000400200200020008001000c0000004000001000000080000004007001400000000070010000001c002000c0050004006000000200180000004003001800300180010010000003c005000800e000800200000000000000000000100140160014000002c0000004000000400e002000400040040004005001c000004800000000020000007000c000000800900080000004005000000000080000004000000400400ec0020014001000c0030000003000000000000020020003000000a00000010020001000c00400040010000000000000000000000000005000000000000010004003001c00100100000028012002800100040030004000000800000100090018004000400000000020014007000400200000020004000001c00200240000000000002c000001000300500050030001000800300080020000011000000000080040004001000400400000020004011000800000000020004002000800000000000008019001c0030000006002000000080060008000000800800080000000000000000300440
  | 31 => 0x200040000000009003000400080010004000000000100240000000001005c00400000120000001000400c002400000000060000000000000b0010000000800600140040000002000000e000001800200000008004000000700040050000001000000b0028007001400300000010000002002c001000c000000c0000000002001c00400080050000003003400a000000c000c004000800000480000004000000000300300010004004000800c0000000000800500000000000001002c00000040020000004000800300100000000002001800100080000004006001c00000100000000000000800b00300000010009001000c00180120000000001400000200010004006005c00000000060004000000c00100000090000000000000000000000000001000800100000060000009001000000040070004000000000000040010008004000400100000060000000000400b000801700200030008000000c00c00240000000009000800500000060018000000800e000400a0014000000c00000040020000009003c00000000000008003000000600040000008004001c00400000000004000001400000000040000001001000000040030004009000c001003c0030020013000400200040060008005000000000080020008000000000200040030010000000002f0000007000000400000000004003000000b00100000028003000000100500030000000000000100640050004001000000000000010038001000400500000010004000000800100000000008004000c0000000006000c0010010001000000000580020004000000400800040000008002001c013000400000000010008002000c0070048006001c00300040060024000001400100280000008000001000000000030004003003400000040040008002000000100100070014004001c00100080020008000000400000200000000001002400e000000300180050020000000400f004000500080010010001000000200140000000004000000100040100000005003c002000000000040090000002001400000000000024010000000500140150054014001000300080040020000001c002000c00c00a800000000000018018000400000000020000000000000600000000064002001400a002400400080000014002000800b00000010010000000000b0010001001000500280040000000001400e000000700080060000000000c0000010000000000200040000010006000800000000000004002000c0050000002000000100200000008001000000000100010004000000000e001800400640000004001000800500000000034000000c000008000300000080000001000400b0000017000000400000040034002000000000000010018004001000900100000004000000000000000010
  | 32 => 0x9f00000002edc07456de0000f3a41290c130802566bfa39c9729aca9c100006ecca702ef267c0000000000000005f0a98a292a202d9e6fc00000002721fb85a1000000000000f946a500006891f6a9d37669f095c8a762198dd8624240004b1a04f00000004b2530900022b752f40009661efc0001c48182a3a93658000a05800000c9f2a0001e660001aea4381fce5fd0000000220495a000090a280c0000fca0001fb100000008340000ac11a0691210f33cba83eac71b1061aa8dc00a0000a2c5498830a8feb3e000014280005cf0ec24bc80000000000baa00008c197fe9bea793000000013e287879e1022abd12b03ab873a1f40f229de56f600000009b84e900be99a01a54000a2f5ebc0001e428301483000160000000001e1800078201a655c2d4c00000000001d2c6920b1c54c096d0d300b364c9b0d000000000015c0000000000020ab00000001bfab640002140842000000003fa697a724000042c09a4000ac6000000000000000dde000000000004d6a9d03bca63439b2991ff44f19ec20092f0a6ed17883ff80000fd400000004b600001280000c3601464d8000000013a80009d90000000000000019da0001a1e5e480003d39f25a91a9163fac1afba2ab9e36642d460f000000009e40000000000047c0000cda00011ae991cfd95cd8000a9c0000a0b4c9e820ad6793a2f22000000017d00000000000a4f9c1e48b800000028824f38a8a0b30804ab81d6a951acf20000788078a9460002ef27fd539485f24b085deb0700000000000000a5c87d89b3a72c00000000000a4400000000000000000000000000000000000000049a0001ece51203a64b28000b6a8d426a1db0244080003d1059e000000000000002e40000000000a0001d72b2883cc0000056b622420000800000000000000002000400200000040010004000800b00380030000000002c003000000000000060020000000800400100060000008001400a000000100100030008001000000500040000000007000000000080000004000000c00100080020000000001800000000020060001001c0000000001001000700080000010000001c0000014001000000600040020000002001c0010004003001000000000000008000001000000000080000000000800700040010040004000000d00100010000000004c000000000c005c00000140000024003000c00c001c000003c00000000000008000000000a00100010000002001c000000c000000c004002c00300000000008000000000600140000000005000800a000400100080090000000000000c0000002001800200040020004001000c0030010000000000000100060000011000c00300000050008000001800400480130020002001c00100000010008009001000200140020000000000000700040000000
  | 33 => 0x9944152a1ce00000000d82382000257100000000000000931800000000004ce8000706278e00012744ec80005569282000168a70f40000001f7d0002e0233fa82787a0df8000000000006240002222154ee968cf80002f7c0000000000819e82c0000000000181e000000015000005e50000ae08389000000000009d2000000000015820000000960aa8c000000087816566e900000002956000287d00028c5000202809982d600009261b480009a080000000000000171400000000000000000294514a093a00000000000ff8a2c80001a045eb00000000000000b60a9b667517e07a28872461c000063c00091180004fc95053e300000000000000000000007a1000264d0544000000000043ca14a0001ccc0000000214408a00000003a78000000190e6e7000051e23faa3391518f212b25ac213a83900000002993a1b80008eac8ffa0f447d56329945929c9c8e1964400000e60002c240001f2758680003ed8000000000000000003a028d600000005225758000000061e80003b8abe00000000000000000000000000a380001288b478f8a2410b68b971a1401561877142aac72a1bcb87191e00000000ade163a0ce40008379a9a0000000bc58000bc92718000000000003700001d3a3c700000002165858594600007144af4000746c00000000000001fc41eca41600000003742c4a00000000002bfa0000000000000067fad0a00015f80000000992ac92000074c6c5a22c00014649e91f2634095625b1211c3e6800099e5e95411229a0000a0000013459960000228010b5678000a6c8000000000000007ea000218a000181400013896cb160e50704917969a2c6f55a5d3fb57a6639a16000000000002f3c000000087527b000000000000ba793718480001d08b9b80004b949b70000000811c00062725926db80007a6066bb072641000069c71e0000a1d80008a4ab7c2a00a882312d4e1cc0b5b74591960d48e86b8aa0f8a5fc07a89da1280ca8c948e5909e677963f3da025a615990c00f9e36a699c6c00022a244681028ed9fa075b231a83a0142640263288981fa543a76d7cfaa0256e29eb423013c000000000000001b71c2c932400000000005d580001a6a86674324a800014fb00000aa0000000000000000000000000660b5b4018a73c0008ba1b18108091c2d78000000288f3df27e22308b3400000001c0d58b000253d7d71c320002db80000000000000000003b71802e606d99eca00000007b600001a4523e000000000027f51a7800073eae388551b87134e4ce00000000000000babaf1000027b20000573bc800004f700000001b86000108e00000004c4c0000000aee0000000288800000016f24212e2200000650001ab400009b401766753eb02d3000000000022c00000000000225202d0ab86a6148e1daa6847ad97b4
  | 34 => 0x4ed830475380000001a009e81f0e4df078e05240000001f965328a2842683b64990000000000000009de000000094894bb3f20a5e000103ba69075047e81da8b39034132009a0000000000000000000003f5c0004f280000000000000000079c19bc737c00000000000b7800086e88a2b34ac0c3c90e7800000000002c56973c0000000000b938b5973714f000021d00000000b2580000141e7b0df90f000000001f1000043980007aa23ca81b0000ac22b1b63004ee0000bda00000000000000000209e7ce279e316925c9b280000000000000031400000007758cf01de066d7cd0dfc5e3c69331ca7fe6058f3200008884f500000001418000147c000800000018b200022646e7d276aa5a46ea50c0757520000a24146e000000023ceb4400029b70002afd07e0fea83f8000131228200018fa111c0000001b9b0000000000000081f17cb000000000000000001c4a65c6df800006f204c40000002dca000167a86c00000000000682ac265b0000069d98589b0a10200022ca0000c564e5e9c08ec00007c2800069d47fc2fe9b683c080004d71fa74d90000bbbadc0b88000e000113e5790255990807c000112a79f4000000070e0d889135108000b14582300002e59f6ed9800000000002dea00000000001a4e77cabe670200002d800f6533900f39200d55e3ae746ce04539110e0e0000dad720979011a1064132916c20f8cf800000005822393b28cea20ef800000027b40000ed02988000aa42cda14c035f7be00009d840007f0945a0001fa40002abb832800037685e5af300001ee80004620f840000000ba301e4000000062a047600000001534462710000070f00000000000000036c23e8d9a1ff57de93b844609cebbe73847443fbea2a75dadd00dadc5b0002f306598000bbe0dd4000000000000000000000000000000017b671ba83800003e21bf0000795800000000000975057a850000af428be6abced44539544bb00e363b70000b3c06305538000281800060fc0007074000b9d400052503d90c4c72c00000002548000000000000002900000fe604612b191710c800028246b6af0257d1fd600008f20ebc2ee06d400000000000000000000016abb480000000000000000000000003e7913a00000000000000000000000020a400006e4000000000018b80001fde00028000000ace4e3000046000000000000ab7c0009dd80000001800000000000004c55cf833c0000000000000000017c684d800000000000000414000000000006d07b880000000000074aaf20001b7f2c22960b5a19b0000097e0001682a3dc48c3a0974400000000fb1b2e8df00005e100008db9f9314d1c8a31113e40000eda00000e200023aa00000000c6400039580004fd98aa0002d7c0002d087bb80000001f4c00000009e88000000000000002331f7
  | 35 => 0x295400000000ee4000230000000017ac67e8dcc39a094c574856820b1ad4ab994fc57ca2aa9f5965854aa2940001bcaa66aa3a701000000000000001f24818852c7e96c8a5e2c0000001c734c818652691d21af516fc085c0c00000000000026ca148000bb119c888b80e000011c60101a24b5968b3231adf005e147f000290400021920001aae3078fb1aa568e61f8e94231807c05582e406a04e3030200000c9c0000002248018000071da62ebbf2ab608863646f1000000000004aa1cda8d384b04cd6ee80002b2640a800040c0000565000000000000000fae297276c87903c6a1701ff9ce09a06e4420e27c8fd6000189e0e928f3000227a000000089000002a48000453161c0001240860800000000007da186e72d117451410a80000000045800000000000b25d2030a99ec4220b820002e1619585960000000000000000002938af00003d3080b51100000002e6100000008ce037d24d9c5600f0000141af1c4b1d336217cdd800000000c49bdc5f34f9292b94347b59fa63870c1a814c3367b191b061e00002e283a9a18c000000281f9dde844000068a00005b80000000000000000000000002b6a477615c00004717752423772928a26592c4580abec000000029d000000009a6000000099a2ba2755991635695be52958da38c8a7a8ac0000817800000000498d700008af9fc8031645449111a415c285a0b3dab0000000034ba5f691f8683103283235800b047d02245f2832486d9f060000000580c0007b1000042fd6426529a6f90e8000308989400000000002c3e0000000000000047c068e1e7800000000000000000000000079f236caf7907e152434a1f191de008474a52741cd0b7dff000000000000000581c0004fb9d8e64215ea7c363a8258144090d64b2996a826000000f3d596c61b68cb4000000018180009548000560041eb4683353ee9cc4a53031b98e8000000000000016ae36cc000000148552699a627f0938000232a0001185738d03881c0b2800007d60516c4e199000000027f20d125de00009ca0000980a1e9c5e00000000bc8000110a25c26123f664f81d69e18e54596aaf0b38199a52d05d48bd9dbc1ef2b247ac2efb04e20806f52dcc2c76a8a0492d5f7eae61c00016c845696965b48000000000088c00000002076900000000027d44e0c0000002554ba800000ec0e8408b00006c21b0192e90860001a16b2e23240dd68fa4b3211093c1a688542aaa7801a65048c000751e73eac31958aa499f00000000a0dc6107850000000000000000000000000000000000000000000000aec9b7a0000e4e00025a6a0f13a80000000a3acd16a8683a0ab5948403ddb7d172a8cc443c8f00880c060001b5c18c9daa190d4e21662eb4a46029512400005da8000000000017b14ee0000000000286b468ecd0000000
  | 36 => 0x9a00008947160000000000011e2e364c98e0ab49acee000209200005465e60000000180ab3a099e000000000007e44f80000000000074f0000443037a00000000000000000000000017f05828cb82c800000002c08000290a48808190000000000000052a431c90311f600003ad1cd80000000742000000064e00000000000000000000000000001b1a0000b4c00004012a780009970e2a28ba98742ca3560136e9c0001a5400000000138000000235800001484aeecaa229a8d505da78c0bd45c8b828208463007991a23e42850010219a9014c5a21a04d82d175b8000000264568080000000199000220c36f8eac02ca6d200000007e36c7600027c67e0137e000000096b00000001b3e00008c8b50ab7400019e0a7ca54c26600ea4820000199ac8b6a987b8a3e2a729acd62c06d9c72ac8400000000000000000000000000000008b5075a000000000000002f600000002d8e0000000000000000000000000000000217aa528000622a7b800007a811f81c9000263b9c08bb600000007a2000000000004e29ed1000005b0000adc7eb09ee73fc718b6d07d200007f2226039200013fe6d4a8a56f980006e7400049a162ba6266e26100000a6e0000bc01b8f000000000000000001fb09669cae88400007d98b066d29f010001dc8148103c921000049e80001ac2b6c00000000000152a1900ab059c18650491d25beaa4000000005acaf061038fe2000000054ec436000051400017d6000000000019842ac9cb85ca819d1a98ca6000000000005f0000000000000000001be028fa6a63b980000000855261aabe00026060001880000000039b80000000665a38c000b1480005c48000000244e2e640007878000baf800000022b63820000aaea52c9b74000390946600016ba036209c5c0074891d000000000000001a2a000000052a14da1f2000047f00000be0a4a0002a8847b0ced0001090ad680000002ecc00000000000000371036400006ce162000000000000000405446000000000006848ae4a3c000000000008ef000000001920002a6c0001211b1f9f4e289112f1af118b8f58000578adba1069bc100027cd000006146c6a6336ba17000021aa0000000a7d80001e90000a5b4000000000000017d21f240002e5ab561c9647a1465faa430800024580003f24000204ae84a32991e4b9ac8774e14d2b27000000000004dc8000b3d8000000000000022346a92e860001fca000000021bae703446056b236e62b7d18c4a37c00057f9f64b570d24aaa176057d9acc000015b000000079d800600000000001f90abac0003ac19100001d1200001fb0000fa47f480004a180009b11ab23a4965e7a1e37e0000000ad3800036a934a561800000005940000000a24dbad2468e6082e0000000154808f800074c92b89be21690001546770648c00
  | 37 => 0xe158e800000005dc800086d217500014160990db8b57855eb01197c58d04a32f4ab120000000000000000007ee45821ae60b8000980000000026f000000006dc800000000000001dc63af069f39dac22000033e567000000004408be2553000270c2b480002c9249e0000000797800000028d46d600000000000000000000000003ea9b400000000000000000000006862d2035416fe199cbf40001a7e0001310000181a73f800046811da00000001e2800032c14ef00000000000cba56c800000017d87c8917e637a3480000ea4000000024200000000000000000035329480000bbe77629846880b23714800072b2da400018379e0800000000003148000b12000000019486dee3e8a8f018a0001c5797c20460000000000151e1b5000000004aa657185c0001bb5000000000013870002ca52ffa43f000272024500e8a958f9446680007bfc00032884528b91518891248271f8b6698f27d54bc63e20000000000000000004cb461800000000008a26726a76a7cc3e390ea32f0000000020b00000000000000420850e12e00006ee1dec000000044980000001a2805cd42000010d5815000000009b00002b3477d80002dce80800000007d50fbb6138000000000000025650000000000000015f4b800001104526c0000098dea000036e4b8ee288881526982245e6a494301b600004cb00005718d20b671b6018ba6bf2ea80000002068b5620774960000000000070aa02600000000000058648923a9898000000000008013c88a92ee08d0a2f0000254e0002208000276600012d70000000000000000000003e7128c000121c174aa12363a57f79a000b5d8a4cb7e180000001d5ca5f0d585ee84660ee9c7c64b00000e18000795000042b0000b91000000022e697d221613d000000010b367100002fa281239d05c17de84b9000035c0ac0e520178dca969100a00000006f0c0000002572af6228a0ca202a00006888614b709d01300637000000003e6b0d80001ae000000003c57a3637462f15f92fc6186000054700027ef00000003f1057600025e01470dc7000000000013b0944800000000005f9c00062180000002b52000088ab952c06a3ec00000000001fb17c554700001ca97428c8a9b0601000026a95c70338cae3f1c00052411d50001dac00026775bb00006ef1b638f71c4c6cf0bd409500000002cb900025147319384493202e0001fef177417d0a94fee00000000500622b102b20a7f9f780000000000000027107580190000b0a18fc000000000000003c781de00002f1b2d692a0000000000000000000001e5000008ec87c0001a9000000007181fa369c0000000000000008ae2bf97286bb88f40000000b37866a00000001a180000a30000017c0000f84000833800000000000002d4a000000000001bb0000000000000000008
  | 38 => 0x6920e00640000145600000000000000000000000003c827823a400010740000000163153900009270002ef60c30000ab70fe000013f021780000000000000295f00000000000000a4f100400000000000000000000071ad9f60001214008e19c82183b580f92b607c82e17840fa069cd1be191ae04000255600000000000000000000038a1b65000000019eed930000000000000000020b046d0b7a000284e42c00004180000aa68000000000099b0000381119b9440000740901826890cb000000048d9f3a000000000015f747e000046eaa6e000000000000002ab0000037295e8cd98212c792f00000000299ab921f2d5e87970ee1a604dd645a9b240000d7200020a80001e1800006e83d80000ad780003518b3e0002b8843323620001bbf0000000514ac16b4a001d1488000bb4000019480000001cee87898fe7248c7c2b0084cb171f3300015641b20000000043480480009da191a000079800025b60000070b738000000098e28487ce3e0ad6e54d0cd400024187fb1bce0002ee409480000000000000000000000006390000039c00098d2c8f1279a4600000004108cfc02bc000883c00067081f610bab585d703fc0000000090903e00026b200000000000000000000000000000000000046c000000000028200002f280000001976000000000000000000000000134e092ac82000082839f80009d227ba58757b3000044157287a24131eaaa7fea08a5a066c00009549ff000001d8dc2a37800000010d4577800000028949ea296b00000000001ac2536c0004adc0003f440008651b4c527deea7f72a0e03d000000000000000fdb000000000022e0460881c000039a01a972c0000000aed8e0210c8000b0d0000000022b53b1ba8000000017f9b040000000000000070880002cf000036a000000000008eb0000000000064a17326daa6b8a1c6d7700005e87cf148a0001e60171800000000000000ab00002c745c60f480001ee061d0000000000066e80008d4070a8e12ec6719c000564a6d07c140004db815f07f9bbb554000000028ae000000026e9eba8dc28ba00006181114e268cc8000a128000000069297de8180001266000000044e00000000000a0e800000023400000000000000000004b30000000900881e00000000000d6e286800000027b6ae58000000144600000000001f4475800003b5ad2400000008efaa7315f08300001bd72771cec19f655e000091758c032e3a58fa60000000000124612080001e980003c00000866000074b800031b40002d4c8e905a0dc87a700127e890a23c500000001a9400000000000e70000216a0e40ec600000000002e3b0001bf24d22734000000000021209c880008a7af1200029d400027bc1692041000299e000053f0000094970263000000002df00000000c108458000000246c9
  | 39 => 0x24cc00000002768000974a983000000041f106187780005ef13da5f7dfdab224d54000000060a8000000000000000002830000afb80009ad000000000000000072584d34300011a200011c0a0b8dbc000000000000000000834846895c6a28000000235a0001e2e7e20f76956dfee80ed6f0885000003c9bb20108000000000036700ecb2c21a868685c4000000000027ae100c00000000000000ad694f90bc3d88da200011e6a7e21f0b9a22b26be0000020421a00000003c3000d1499a77000015000000007349fe200000000000000000000000000000000000000010ab3226c65d205aa41aa30c60197d538780006210d670002aeda3807ed9bd0000b8b0000451909600023b8000096c58bd35a000051a000298b008238b000000009c937a0000000000000061500003be028800000008fb12940000000acb82ca87a82800002183ba08caa8162a60a5ea97e5f427e064b800000000005c6983847a000000023bf7bdae48459000000000000000000ad81c6595400002aa9d3081a9ffa2daae390e840000000a6e0000000000233056a0c4c0450f7a5b0a8485e3400051a800021880009d5db8b22e942ab8325e466b8662abe15525c40000b29c1664ee902300003f99e0cfdf0d3add60000bac493979a20b526c3d728d7087080e176dcde6f4000000008290000000000242f0000000000000000007cf53e8000000075100000000000000094e6de1ac800000015560000000000000000012300aa0000208a4063fa000000029fcaba6f180000000000000000000007a0800000005c900000007c6a3100000000000033a00000004da80008c7a05900d837622d13d2000000000011100000ff624c0000000000041c5c12aa3a90c667ab495b3031800021c4af58000000148100000001cc8000ba891f277080000621774305850f11524b411800000002268683051200000000001bee000242136c800060c00009378000a362b1074714c10000000740c338789000000028d14684000a40811c87e841c0cd061eaa09ec00000000a1f8000000000000000009c7a89c3a30e5c5b396d40001a348b40b16b77000000001ae32a00001c1ad520002adaa349cf0333977053aaa1c000139e1aa800067880007735e040000fb452b88ce0001bfc00026142e9000041590461fcdb0aa2151c81c7a9a856400000bc18a06ba1fd89fe443c2db80003fe6a441122a9c79f90390002d8a0000f3e145c5e600000000000000000102400021304d2c000950ddf028380000000000000255f00016beb74ad64566800057804c01f7c000809c0001018c2c0000000b0e27d2aef06f00002a5c00000000001ba1a73945e00017e6bb580009320805000000000000006619058000000000001dc0000000a16d2e80000000a9940008a100009200b740001
  | 40 => 0x6ef4000000000015067a616a0000000299b1351dce5ea0d8b4d80b860000e7a000000007e4e34b751a4a00000000000000000000033281e800011b673d000000000000000000a3b8000a59d7062ebeb6e00026bb0001a604ca29f412dc0008eb80000000000a0761145161b540000429a6604ec6e1506e00017dc00000007f9000054c5542006d396513226e000267e9a2ac6c000000000000000cb12aa00000000001952000228e00b80000299ca900017d135d80003528000000000000000003f94b940000000b5a5d78270a86fb908000a26000000000004dfc26a13d85fc0002ae80a700000538000000214600006c40211436ba600006b59c6319508ed34680000000000000000064c1ba03d08000000000034c9d2444547f42e80000000044a7a2db620e0aca87e0a846000149100e281a002000000014221592861000000000000000000b361da1c680000000000000060e6794000063c337031a02b00003090d7e000000082e80004dac00066700000721dfe00000007f50000979827840b62960b0c0002ed00000000b88a36a6baab189e84f3000049c80009dec18b8ee81c42f880a0000000077816800000000136d3ec7e300004bcc00089088f677706854a994f6198400007802c84fa29e868e12e26d1a1729fa8f900000000b890b2c0000a1c2460dfe844944a000000001280004d18fec0000000000000025109f480c40000000ce2a10cd6841a406e0c8ccd20000b64000103a000185094f00003d981800001cc86fa0000000000000000001cd09d6258426d5382d0e0000fe9ac399800000000ade8f2a57ea16800005a205c0000a401824b5e129ea96a6162cc8000000162490b2b8c0001b641e400000000000bd02f1a97e9bd80b6a075088aee238500000001dfc1c8c00040c918ea3428af7289f3b83d068c65f5500633a376a19e5c272c9a78b4010d0a5f662a1191e85b3f00006f8942c000059d0000000000264c167cd957a680000000af80000000000000000012e90002efe0000a4e0000000767aa7c617ab024610000000000000020940002a4200005e2562204b00015a60e1ecd415b884002394086a2c7ae805069057ba5da1930143aafdd402ce849cb6d8be04418ed8b1505bc1fa000069b242d0001b0676fda2244b13d643394c44b7aab479fc7eb0001f10403a4a400000000001bdb164c00058184e6880aaf67ea57345a601d445729c5b284077afd236a41a05ea32695d663d130eb4e2e3c0d51d8090484a84e8241f00016a84be400000000000fec00000023c42a50c6820f20a68410b4400026d7513ae942c52b030000c3c0002b500002b1400000003edeb7e0000b9c51d24cf2702c3c87482aab27d7a4a841d0d8f00000000151243a1f0835b1027331268690e00008ca00008fc80000002e568c4801f
  | 41 => 0x1d64000005a00012ea5b68000afdab954c720725612c44acb0883a18890d20aa5c859395041a0166e97f69d88ba8f267e48c66a6aa6ec66b02d9af71cc0000052100010aa192c0000000000700942e702880102b54a657715baa8782983f9000086f9b75994a0a2a388063359967e99a80e53c2a8ad0000a16000098a1c1000000010c422c2a6b2180262696c10fb8c046c800a23eaca0000000000000000007080b1b0000000000000000000008e8800000014dc000000000000000002eac00000006fa89ae0000000aeb80000b4800000011487894cc08b48000000000006b6d9a00000009074b4388284f30000000ae62b327b22eb078b202ba3110da00000000000000000000000012c27a7aeb80002e9a0000000008800082f0000894069400001749f99cef68c000004c000000000004084000000000096e000099c000000024fa0002d444540c40a21845c00001973ba10949a492cf73e197400019a4acc00000002b3e467c2029e0025800003b800025047a0400000000000001c8600000000000000a6bc00002dd780834a9d20002ad7724000000000008221d4238b05360002ae200000000002abc88c9cfb96586ec89280000000e1200000000000000832109c0000000000029d0002e76a961dde435c7cc39f25ce4434000a0387dc000000090d0000000075d93486f8492ab36201ec8800021ad0002de413868c0000080300004501fd8a4c8c0800000000000000af25cc041600001b13f3c9d425092c34ca69923a60000455c00000018ba0000000000000000024d08f48000000243900000000f70000175800000000000000000000000000018646e0299c6984000122800035d000000000000000000000000000000000002c943dbc000179c000000132a89c00003f1a73000000009d7800000018ac9408000696901e0bf8c3800026727bb10f64f426a86ee9a3e6ce8c805ab14de918000024bc00034418cc06380000001866000258e23e000080bc00000140009fb800038609cc00000000000000689800000028801d38000000000000000000000562b4f00000000000af1800090d84c385f80000002d2a0c5492b000000037480006c78000a71c0006d580000000000bc100000000000000064895c2b46000000000021785ae2b762d5abe863c98d0a44000096b909812d0000011af3e65bda5080c0000a6d0000000000000000002170000000000000000004660000000000036d9b8c0000000698c0e452f00002a9400000018e2481000033797f60000000abeaa22396a5ccb2c954f00000007a880000000000a38400000000005840000000000048b199200005130001e3411d2efa00000004b680000002d3e00000003af800000002aca92801560f80dd5300a5416c96363ad24c300019ca43783650a4800000000000ad
  | 42 => 0xda88c8aa065c00000008ae243c00019738401fea51a1e4825006f617b8cb681ad810bb087808192d9e0000d780f0d844000000017c831f0002c5895aad169fe968843907be0f1000000003e476280007c82dbe7c4400000023261bb9e4a9ab99ee000031700019d84db12acbcaa46a21a99b47b90ec080e80004be8e8e2af8c8c22f836da98a3441938340877264858a8612b6127580000000157548c0000000000000000007c74809edc43b00000001eae000000000007fa16f80000000000000160400003a7241d74e0001fe864628a800000000000000b581a8087e2c804cc9d266a3c19abcb87d9586c0bc00000000dc4000b3b26e43ae10b431a8000000000000000003be9a84000000045a156800008029400000b3e80005c78000000000064280000000000aed0000000276e0000000129a5066aea1387cbcc92852000080400000b2c000a5e00008430d48035aa0a00000000001406029000004240002e4a2d6098243295d40000000fb840a14d95d51df80000000000000048400000001df4000000000000000002d750000000125c0009560000000000013f8000907000000000004e70000000244a55da0be4739d39a589bf680016d854e80009f9131e0000fcd0002524000054e6189bda0002c9e5220000000140a758e2fc89caaf7b6180007c7e30a73f6d506912c99674a024695ac2087f025099103f0000154a0001e80725800035f242b3fcd82c96eaa36566110e8c517e1b7a1e9300024905bb800060800003d780000001119876823c0000000000041200012c14a82b90681177c0321b2667006780a0abe246ace62811264f97e50d69e56eb670e696fb440c6200000003290f400001834000004b00027ac8e3e8c8000000014f8b9a9b94a8c02f4880803203793584de8489bd316a561f30b986c0435c103d922a0b2a5f28b0a800029fc000ab00000000000000026369a90000005c7749e61b889f00000766039f05c9cbc05811b2000000000000009678000000000000000000000216000000000020f66329f50925000000000009d6c0000000000b3080000fe1f1918380001a09181b4313e2099c000000000075c2c68bb9939025c9eb270994f43674000b4b15365d42e1c23704f720b8000000101d0000000000000014900000970000000195b04822c67d603024d080000000000000028458498920000000b1f5ff86b39fae00013229f780000001d1a4b7ee5eb04a6b0587845e3842e3400c0b1061ca9ba92a981c50e1dcf02a054c13607f15a3a09a23f0000000133400023970000000000000000000000002bc8448ab2541c1dab000270e36212db000096600000002b1037202205ed23a8cea0000000016400028f00000000000000000004f800022dabb8a6ec8473a800c97e44c8a0b084d02f100002488000000000
  | 43 => 0x74a80000000000000000052014fd0000a7825e651899d8eca31eaf1437e92dd00013ae7f000002e3000003e4000590296c240cc18291ae3222a062ca571215aae4b2900000005b705a088e000047515740c19ac50000000000023a00000006e0ab3c0000000000000000026e6a72800028e800004bc000000071aac265d34a4ac1a0e5dc98a6096e252fa57c83b16760000000000000020980004abedac000174008780000001d6671a580276f90523402b8a01b25c64ef193c52e4c82700102e00103de887a06524b8efe6c72b802bb00000001622936a5c47dc8a7c00004a900029739041d0e0000000000119244c2e1833ea84ca395a4203c000000000000000000a1f0000aee800001c4000000000000000000000c0e53f90351b59dc50000000000000019c000000010660001bd20001ad00000ab447887f8000000034b1fbe40c60550f48000025c0006238108b8e80000000000000291200001850000bdc89a8bb8bce00006650000000000000028c76a70000000219e000000023426200ae05ac000038d0e8800012b239d0000000223994c00002a76d9d5ce00017960000726090de89aeb19a804cc3969fb2c0aa4b948748780000002d30000000053a400085900001dfc000000000010a2e33b60169a4969f9aa2580000488000ae901bf9ef800000000000001fc600000000000000a9a2da8247970a4af9b120001cd7000008000000008d4800000001f42941aaa9dd535600014f50001d7ca426c780a800008cf00000000fbf0002612a1620cc2c880f85f8942493900000590f100001dba8639476000000051c80005f0edee000000000000006ed800000019540002b660002dc40001a6a738120013f24767c59d362d845f128b277a5181e064d242e478f2cb43a50ff75680de855b041874dc99a2258000000181d0000000337c00000028b800000002bc00006aad116767140e0000f12b64000000028f984b934d77914a043bae5f00a9f946ec139907c18115099836aff8b5c00028bb9c28000142000074d00001bd0000000000000003f606f830e31600000000000000000069e4368278a35e0000716a228df0a20cf86476042f247c6a30096b549abdb6c55725b2a782a2c000000000000000000cf400014d6a9a4b5d55eaeba000000017087fe00000009c200002028f34000000024d0f7e000276a000000026ac4a20001238abfc8fe530cd409b6a0e69c42ade0002cdc121039405b08522090b8e85607006a88000102000006b000046794c200000001ed59827fda1746d08675742619a414467f309a022992d8c61eb2814909a71613680004e18fe3738967c4da00008129fdba2880000001ebe53262e23030000000266275f8c026bc1faf05680008da0346000000053c816ba4a00001d01fb600000003511f9f9b
  | 44 => 0x87848f225cd5c0001a72000178600000004bb9da64730000ae39a580001497b11800013640000000000000000037180002b880008e2000000000000000098000138000000000001f2e97a183a3d4a8cf0a38000000000046cd11752080008491f764068f9830c9db06c80fc000000000000000000000058f00003000f5095040009b70000009c000000096a70c29ee00000007dbc7c24c30fde00004ed8e9c0006bd85d02140f06a480df281b81e70864a604a7119cb23005769714bf1f81f480fa884471c001a460c3da00000000d9a3f430fa8aa00000000000000000127c06080004bd9dbb80f0000133ae49a6cca8400000007cd800088f2e8000014a454b049d7a91557100885600000009304ffb205ac2c0001db72eb8a407b7800000002c5252a5b40002791000000047085b6000000000000006caa9e13eb6a6a0000000bce8000000000000006c000000000a5a25807388aa00009324fa8994921800034f13fa9b2000073d80000001f6c000000029fa5905d9832616705a12b985830001ef259986cc0e6071cbaaacbe430ddcc37b9172000087425880006322819991800000b12248e4000095080002e78000a979dea8f09c1400001aa93f1428b3a80000000c140c41d524b5a1ee76c81a000000009d2800034a21c80002b5f000000000000006a0d97fa2491290002b9aaba8000000000004ec0000002b2f0001aeb0001496186e2b4236a3e1000218904489bc0b7000000003ae60605ba8368ffc3418000831a44c7be8c6c000000006928414122d6226312b400006c227e2c184c90d8093080009ccaef06492588000000000000001e803b40001c3e9caabda70582d5392800067900004420000000000089691766cc2d360e8cea8a10800000000007b400000000000000000028da31c6b9053500013c4000095e00000000b343ee0000000205e23a616980d0001e581392c5ea99c000000232e589c0000d687e79f0e1c22052afb9e4184608d213e553057e92563ceb0e9db6b33800000000000000321000097c53302ce1fde89a0e280f571180000000de4a65c000542275057689b89d08590563cf741deaab081fa58a30d0d7565e03ca9bca57399817ae4979ab81ba80007940000347a07107b800066f800000012c025d8fcc2fda9bf201a3d40001ee80000000a54957c0001cdd0bd11b800000007870d8ab1a97520d6053a0000000000000014027147c1204e0001f8400021f60350000256808d0001ad809a1da7000000000000000001e8c000000000000000002ec800024e265b80000000000000092a0000000990c0000000616000000000026807e280004559ff2abf800000000000dfc000146000008c40006ab000010fe49a5ce135842997b83f869769fc1a40a4c800065380004249ef0000065fbca273a000000000000
  | 45 => 0x98c096c0007d585fa0000e64405800002880000000000000000054597fa89f400000009a80ad80007a3c000789c00000024ea5da2e4a000195e33adb0f87f99261d996f800000006bc98b4b1c19a26ec453874f8d712eca0d40a905789c02cc4a07248aa41e354abf10c600000000001d0094ea0b240227f800000000001ca48de19f8141da2e0001c4f0001e620001a109d4800083814105d900000ff4d920001654000000016680009a7c00000026740002ca66f31f30a100000b89800074a0a760c88a9a00000000000ffa5df80002328000000000000000000001373485a8292fb00000002db0ab90000b78890e7d02cb71c080008cd00006b80000000000000000000000000537c0006d21e7400000000ab97b10002b94000000000012e4b5b00000000000242800000022860b5ca264eb10a0414167423a1c5500025ec00000000728000000166c0000c8e02d894800005865b900000002c8500009f601bcbb7000000000000000fa000000028fc03e80000000e8897bac90000000031724a6000000000003f70000000000000000016782a18000000070c2d5c12e35c0ef60bd80007910000022ddc400000004b705321aa400041647829296ca000000000b410330000eee46b25be00000001040b5800018c2860000016dc00000008ec9a79e94029c00033ba528396254017e0000956800000000008f40a853f680000002acca2fe440000000090444dc000000000000007f4695d2c0ad1c0000d64000000093b1065000133e0000000000000013c83d800000000e9400010ac78c8f81f7c23780000000000260acbc735400010eec2700002f949880001c8a9c28891b0c00012c81da40001f46a7a21a120e94ca85400000002a900005254000000243e0002b400001f2b0000f960000bf8000000000000000002036783a074849800000018d60001de6000073c000000000000000000974000015900000000002930a23800041e8dc05c8000000000009d8c0002adaef4a7c0aa200010006e5800027180002d400003258e0c2c31c945f0000041d40009158000484a87598b000095ac0003624bbf0000bba11eaf1e000122600013b40000a2a00000004f000007298d2a15a87649742cc658307d496b68d9531a42997f80000001d3b28c037427f9388830db361c04000604d43c14f1cf50002018000022e01880009f22ce6a65a4a000013a7883ae921440000a600f1691683f303f0bad2d68000085510a041a0529a315c8000260c91880000000000b55298800000009220000b5989ceba2000076969341550000185000095d800015459c6000105e0000000952800013e8000903c00017717c7a9d80735f218ec3e00cf255c86725544ae089b1ffca4e00005aa8f72155a28cb7f87b40001047000276000020400576c9800014e66348000b
  | 46 => 0xc2a4fead1c0001ae800039b000099396e000000005a8251e8a21d4a000249c8b084ae7ea0000b392a3200000000000000000000059c1f81000000000000002a040000000139070893c00000001b880006e9800058f81580001de522f285e483253b19a1da20001920000000000000004dbef0e2b7839c77e982808a9bfa144610a18ea14400014b5391a71a9f74000a244d22a789ac400025a20000000000000000000002c100000000000b5207e6ab2800000000000000000679800000015a451500004a100a99869d548bf9ce80000000000000036e8fab0000674296000000022cc000000000000009df91783ebdd274598f784509062aaf596443f25f295a596c0000ef26b2214e0829bf8000087372750c08aec4639f6856ca5c2a502a9a01a0688fbc55f9ac0b0024c0afe0d611522872345cd1c64d0147000000024480000000636739800006ac0000000000540848006600000000000000147000001d8955400000025160001d17a1b0000a08887e24766eea2da6a71e480000000000a711b2d62928ed9751db936b0000a53a260000000004a80006e94000000121a1f846a10002042000000000027c200000000000000000000000000000cc17f812500000002eec8a000000000000367a6710ea0e6661d80e9a4880002388a1e09c06be164836a5fb0de240199400001db4b410000b80077213480009dc80000002c6624405820000000000000000027566dc000070a172648f03d40000000ac58000802000000016147ab1d964f9800000012e10000000a676a4c000224e5970e6a83c8b55943141a88a28a90000000902800043281cc1638eb600000007560b455f242481a74b69a56ad34000000000000008b10d26000000080780005f3c66f650803a726a6bd95e84263cc1bcf7902ad40000000020d0ba62d80003b8cc70a2c23ee713889c0f046499d6a56e9a82bf004407840000684000259c0001e8443881e5031800062620fc0000000a1a08e00002e584054ad4b652b6869325e244d8f549e28a72b5c80000001338b25d3b8b2ea2ec3912a71ae8064a82a890b9068000036835e00000000001c420000e160000000b5840007f4000000000000000000a5a80004f7a765452881dab8400009b800091e16505a71b74000205c69c51ca8a604700d75d7400003001290000000200608504c70000fa8000000079eadfa00012bc19ced96b2124500000db00000000614c000000000049087e50a5000000000007e39f9500012fc3ce05b00f087ffab426940000cb2b7b02460000000546800000006760001301000000000000000002f0c6ef80000002f34187256054e26bc000102600029e60000000a6392066d78000000105a8a5400000002c710c24436038b258959e30196158a86b2f324e0ab723b900009e215b48f605600002
  | 47 => 0xaad1034964660ac000ab20db482813920002e907d1aaf91f7400000012d89902bf25c100000001e1600000000002aa06628000000000032b26b9a56c00012140009829e3a40b000003ae93a240a13222e29e96f185f679b08704be07b03c1037863601613ca0b7e8f9a39bb55ac5a0151d1f46eed2e94e25749fc5f98000275fb10a8a69245b00000000000000000baa8e48e3000000017ee84aaa80bba9404216aa7800028c2000000000005bf1ad00004e4ce1a0eb00000df0000000256401fd6bc6f08000b8c47e90000afc9198ff080b090c0465aa89248d3e11310105e71dee08e1ab5556049f1516823748e66e0312aec2ec000000011581ea80009dcd34485888b29df69c350f8d52a8586ca527261e8e60d90698800c40300000e2da7d415672e2136ccc3aa85ce6452a350378092109000031d8000664234a63da3f80002a387ef267a6eb23165a9aa9466621a21db00000996ce2084853940964276a352ec315252a5ba1e32607c9fa608a42257626b6ae11d7a865800077a0bea25c077e00000000002d8c5c5a52e000218c479c229528a9753db8a9c000000000000002d280000001a0e10a8000000258434600000000000b9e8000041c000000000013300000000000803970292393982e10000000000044a11448d1a77038a6be4000290e23b8000aaacc300000f8847958122bd04c200017da2fc9cbe0001a3a34e8bdea4200006e1000000001fd3a98f2c995811d96ac2441510d0a0f3a88865400007d480000000ac68c3acd77690f70000024e9c1a1ec0936dc666385da1d7c2a6162800033a0000aa5c000a0e46381c81baeb19100200000668ff8aba5a888320dbc277bb529eca68828a57501cfa32ea0cb2b06456af22ae00019680001f3100002716129eb8071d036000118f74140002b69100a704096072e9241d18000000000000000000000b00b9aa89e0001f7e0001e6e4e6800000000000000000000000000021560002cf408b40004cb89282d05626a471ae273ceb426f200006621c7a644a7ca00005e000000005050000000158e0000f4a6e5c0000001e46000018c365063e81a52d48b60810b8d46a73b80000253800000003d05355b8e000232c5d680000002ef9880000000000007232320b5a800086f24987b999ceb6f1256675adda00000009dfc55f53463de251a82867f1de26c526fe92f2a66135c000000000054926d6000000042902fc0001d446bb00002a823fc000241406cae9e2d3800038180007620a6806f0f1a0001f0f00023da000000000000000000000a1640005d191af7a48000b7207ca69d038f15700005988000b841cf20000c1282ba0516be96482908000a18012c0b88333a7580007c3000000000000000000000089e00007cd14785720000bd600011c412f80008728000017000033da4e6
  | 48 => 0x14c104321000028418324ea80003b3904e0001a3c861106c0001cd653e68ec469a00477005ae9575a7c000188c2ba0b3013a1e720fc9d826e7896851dc0008f315f079300002f900000002d3a00000004c480002ff0ce69b307249fce4ad98fa08452c20d8000222a0b8d1d00002392000111100009ea372c000000000000000000000d6232f8000b5acb870cdc4e000000007c50bcb87d000000000000000ddc000000000000000000000000000076e00003c828065ec2bc245e84888bc80000002c02000000000000000000000000000000000007201902000076b04b589ab35a698a61800071920c45428000000000000000001cbabc4259000000000000000e9a77751327110c46210a60e0000f1800000006b19ab60001f2c0002a98b869fb53902f083cdac722d51c84404c0683241e207a80000aa9000061c000004300009fd963800024640a89d5a2ab866ea599f7b0ecaa0099bc04f4942b1f609a4f8004400000000ee12c5cb07c0a6ea000284f34200003558afa0000000859a057000000000000000000fce154a3c69fa000000028f273a906b7d880000002774113800069e80006f5800075340000000000000065e0000000000134c06eada2000000000002329cd9232000000000000001b829b16180146000000057f101400026281808395538df6e77564580bcec2e49200009a680002114e3c20d843e62f800091f1c277280000b68000054f8000000001900026c096a90b60000000159a0d60000000000129678a9c0ca76e4b66fd15ae186401400009d06af9b5006a0a963322e3ea2aea062d18c9c81e865a3222ab2903ae2e15d16f41869e864a39631564400087580000000ede000000000000000000000000000053900009351f00055800037800004bfe8b955008001cf8000a3a00000531ceb0002ebc00000000001078227d6ca00019f418a8000058a7846ff80002bd824700000006a44000000281e000000000000008fc000021e15f565c88829ab47d70000000000000038f800000000000c78000000000000027d88e96804000043a000000036992b300000001602d7d0000000ac0298a000140c00010722ea00009d52ac2061158d5ef87b60c5800000013540000000000000000000008120eea000000051ec4a70000ad800000008b780000000bcc066c81100010493631668161273c0b100b99589fcc958e3722f0467c065ab053f48e3a3ec1a9614a8e2046f122a699c1b08bea78f20e09f054f62ba134572e7c49da8000205a4170e5055e019053a1d684070be6043943261099b287610fa67a0e5e000000085b96900e6400000000000002d5a92880000000a5a0000000000000000000000002bfc0000000000000075796722346995b85174a40dd5a19148000602280a97e2c8627980009ab0d5e69902bc786
  | 49 => 0x1f320000e2407f02742352c292c280001111e0c037c00004ea0606131170719849978f90533109a366cd12a2aab96609e043884772547995000006940004628013b991cdb71d00000001a8c00023ea403556600000002248a56ae7000000000000000000000211e00006342a9de648a72e7ca2f208c1b7881a11b8461b4880000000000909000000000001882c620d210b80000fb30e7a4ac4d7800008141ea000191c00026105e4400004780000000000a3a99dcbac85b91430000000000000000000001b9a000127e0002e0e0001c590002820000169400014b600000003fd0ef05d785a600000003b4a142b5f95b6a0d80001b9800000004984b4a91eb940000101052310f4dce72a8d1400025df494a12c0001596b0798f000000001f0de4e70383085f100002490ba5000000000580000000000102834200026664e39da080c829e34e000099cc0000000c982dd800000000002b40000479000048600000002d702120b9d9c7000082d99704d0000000004b24d8865049500006d11d1e000155400022748a4000000002be00017a000013780000000000000041b40000000000000257802700003cf1f180001402b4c93f4000097a9ca15bc0c800b531fa1b20000000000129a000000000016ea0000000999054b00000004e880000002c4c826000000017fb7849bec379836711580005ad8b6c7bd25867eb52f40000000000091b000000001480008578c4e00000003f400cc6a093f85f3253673413c251e800000000006f91e020000000023014a0b19cce49800000002edeb1400003bd0b42658059713d466915ddf1c4dd0eec23903e069480005c900008bba74c0001ecc0000000a40c00000000001e5800015c400000010f40002ab8000000054897fc0002090b2b9020000257da72171c80d198c38e000070dad1400000008930f5800000008ad400083c00003d1800001e0abcb7f000017780006f7800000006b66e8a3a600000005079c5ab5000000002534454a20600000004c185dfb1f151076480000001d9400000006ea99cc4b39ce4748ab1a00027d0000193600000003a2a4420000000237654400007c19f454c8774a50e8ed00000000000040000043e08eba744000000000000000000000000a0ac000156281b9b7cbce00000000000000b1fc7e200000000000a6a89e0000000201603cc00004d0000412c00000025200000f0834d8e7298880902c600000001506000033b00008ef00000000002cca0002eda8ebc000123af260000fb20000048000000000009900002618000087a00000000002d06000074576f461f52ea21c97a94f154514d30000ba20002ae780e00000002884000000000014ac0000000000000000012fe5de800000019aa0000000b79976c7d6a1630000000115ec6e000088600000009af83bd28c800
  | 50 => 0x926a19e38000011a000019e34d0332000278d2d4a825579a59430711bf53e114083a800000017a21474000ace8000b708000bb60dec7454a0278a1a085fc849525b800046407541911b76032e07886e01263ac945c14129ae09785c36fc15aa000262400002c00001f8309e84217e3e549367c09e0d40d19a948a0400028b40f000004b2db920000000000000000000000000000706a38d000000000000000000000000156a00000000000ccc12bc00000000003e880000002a282a400004ad40000002950658800015085502cb8c5e9b500007a38000a6f1ba30000000870032500015ac00015c4000022873dc0003ef46083308ce40a5ee8e4ae800016ad26a138939f89f800000022548ec9d01000000081b42d80000000000275968728f4a46824c959800000000000001d4bb18000000009ac000000000007fb582c33f0f74000000000000000000002cfe0000b720000000bcb1f1eba92ece51b0000a7e969e44799b800000000002ca41fe400025e27ce0000000751840054a042d0001c3ba9394a70002bb07ad00000000132000086c000000000000000000000968000000000000000000a0a80000002a7e267000000003bf3682e4600000000000b38abbabd2000000048a0000548257e075c8ac013000089f000028611620000000000000000000006de1c6a29b000000000000002489000000000000006df997e4d9a856021800058c800010e00000070acc000025f37d254508c20b469ba9642f200005e322f4942000000000000a7d92a00022363010000302d70c741993a1d892220001fe00000f6b00000000001c54000289b0000000000000000000005880000aa100000000000aca800021180002559896730884a000000000017826ca0000b9c8d6a00022a66e2838e000000096c2e78001e5bc00020dca0c1ade614a37a386ca20419cd0c21609d800000000001776336116ea00a74400026960000708a5105cc0001e96b8198ea000059506d21e6331929000014790002d79813068f0001fe600000006f0000000010be00000000000bd00001f42a8b80d70001ab140a602992f89b601eea9e000000056c0000ab4938f00025fc2d240005188000055e9b9af2931400024307fdc0000000000b998000000206600000000000000248000000000000001b0e1d4913c0002d7449bae4c42b8cd6169640833b0697000296e079a425a36e33a000000072386260000000000038c7d800004da58f800000000000000aea94860000000000000000000003690c500001e9011b4000000000015e85d88c607350000000000000000000003efade00000000699800059480000000bee0001adcb2d88840001dae00000000000213000269c2ba88d809fadae404a74e4ff00820002b5c6032e370000ca000010010001304a1fe4f2a73000000
  | 51 => 0x4280000000194239800000005e95b591a811ca1a47ee94aa7e798d4a986b0600028100000000000299f000111c0002a18000000074100004ef8c4a00018681df10d80570ec89de04bca89263705b40007588900000000000008081e700000000f5a00027dc3fc8aa84f6215a026c0001a1cfd42e6199646505371b180009fdc84f24840fe000256c00000000000000000000000009b20f1c000adc28f1a1c21520001d143da8e22126d79e9b600000000b0e95bd1ee156800000000000000d86789800050e8000743e958a45095046a80000000f6d0000000000000012591d60078000000000000003d653628ac2b20a528e0279a42285b44a00000b53e1f200004810000000000170e000117f744000000002ba8d98000000000000000007c540000002e5a0812b196a22d1876316645f925a8a6806fa9311f0b70d2c0e06cc19c00004c6000000000014b3108920a0002b227532530000263926495d0746195601d1cd44c29d8437d800000000007c1ea2603080002c543690000000b9b2a860002b4a15d4000a4980000000000a99000000000000000ba600000000000000000176e000283400000008d80d1200000000000000a8d050da31915e8ab24ca8b6a63d65a88a455b99b6b0c239a6b992b918a1a697b50b9f73c6e0801f655c0002472535ea3010e527000021184482db20000c4897700aeafaa8a78e2a990000048308424f60000000000000000000000000000000150c0000fc200000ba2082079718400041022620b980008530d30843807e88480007e7000038b8356980800075413089e580000002d7a717111484f0d9800000002c3e1063218486b6999ea7ffa9411d8061700000005352ea672d82b23f6000000020630000bf00000000ad3000000000000001a598e50000a5a69d500018907d280000000000a418d4e58442e0179029a09d8000b30238e6208000032a033086d8a60001f976a387f00001ed200000000000000747472800020e2868000000000005f5155e000248d000060470b800000003738d30b2a7b680000000000b0500000002f36031dd615a30000b77800012e9f5e000000019f9977000000033814cf00014b212818a2a4d89ec000000012b51ea00029e7213a75c1aad6a490ddb98000000014b8d82000000008600000000000ab62266000050200009060000000000000000018ee000000070e1532532ed1258a0000000020c0000000963087672e8b789ba0000000000000016b40eaa3a311680000000000641a5d61a59fb41dda096b51800000000008124000b40a8dd000000070e8000ac78000a4140000000efc00000004cc2ae5000000000000004dc19048b21bd185d80000002ba61db800043712a4000003400015a23a70000776ecadb0424a783e964c00026a2ab38f6c302abc08134000ab127
  | 52 => 0x10809428000000000013c18b0000000000000008e800009fd00000002b0a0001b7c00000001d7046a000248f33405c0a8f800000029ea00000000000770000208a000000094980001a600004e900d0434927868c839141d970800024f4b26a67814240000001e22444817f31d202048d286a0001e5269fdfb754ba07370729741a8800000020ee000026b00000000001b22a4b000035e800025600000000000002468d91c1fb2ad212ae0bb00009c480004db471200000002b09f70000000008f4000b94800000000004d4a2180002e7e80280001160b11b36166a44d25480001b5a02f8f0e58597c2727929882b000000000002f080005fa17ea79a89be2d881bd00000009a3a65e73600000000000000000000000007bf849200000000001ea66a800000000000000000000000004152a5477bc0009a200001ab823600018e078282065b998882a381170001afc90b8eba00004df00000004c081c654f1b4e00000000001b11000000092e2c32656a51a47f80000000000000000000000009ea80004b800000002a04000201c927c0000002ba8000000000000000ba080da1d000000000005248000103c000b2ac0000000187901000062baaa6a50000000015cc0000864947295924f85a319ea8f605b87b7000092c00000000000fd50000000000000000000000914000000022700029e400019f2b7dab62455088ca7429b59078000ace00000000fdc65e800040440000000000000074700000000000000938000000000000a19c2451fa2dc6cc88cc05101b807053a300019d00f9c51fa1cc7c52061c620000fb50000c3a0e10bc000000000000000958400095b4000410e85f5860b1a145a08e9f8d6d00eec7d30000000b84a8450741c7144b82401aa187e3801c3599b4b124e980006e5075e000153fa77ec8e76414d0859e580a2657b22b2a850857ddda2f1a8211a9017a8c124961ce08909df1d07a7769c64c6abcea282eca31e0c6445f06425cea39e84d079a77406ac44906a020e81546b4a9d90fd0b4085b015e4b40d0443faa48b5d9686955c3feb58e9de80d54b876ccb482828169b7c82db98e1c0629202265ea949e891a9dc5de174c00000b887326500c74000add66048c021907dd205b97615c27220d840000000814085473f2dd857b29ac0000a340000000000000000000000000ecc9d18000000000030a21880000000000133c000131800027c4aa8ac7a73281c0000000000000006a78000234817e04461a6000080c0000b260001af400029be07b187c00000009aa800020f4000b6480003b1162e00013761830fff9a40c6e1c42b0b8c20000011098834380005001b930002b865f3a25e6e4242a360679c5e28a82a2dc00002c4000235800000000003930000a2047560001f6a00026e04d401d57
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x87336595110042b93b2a8880215c1d95444010e66e8aa22008733645511004398322a8880215cdc95444010e66eaaa220086b3655511004399b2aa888021ccdd95444010e64ecaa220087317655110043983b2a888021ccdc95444010e64e4aa22008731725511004398392a8880213c9d85444010ae4ea2a220085b2741511004398aa0a888021789c85444010bc2e42a2200873154d8910042b8bacc488021cc5526244010ae6eab1220085b37458910042d83a2c488021cc5516244010ba6e6b1220085d07358910042d93a0c4880216c5d06244010e62a831220085d27318910042e8b98c4880213c9db5244010b64e9a9220085b174d4910043992a6a488021cc5535244010ba4e7a9220085d173d4910042b93b6a4880219c9db5244010e64e9a92200857174d491004398ba6a4880214c5d35244010ea4e7a92200857173d4910043a8b9ea488021545cf5244010ae2eb29220087315494910042f0baca488021585d65244010dc6cb29220087636594910043b1aa4a488021e89525244010ec2a929220087a1549491004390aa4a488021d8d4e5244010f84a72922008732545491004398aa2a488021d494d5244010ae4eca9220085707654910042b9ba2a4880215cdcd5244010ec6e4a9220087636254910043b0312a488021d8dd55244010dc6caa9220087636554910043b1aa2a488021d89515244010f44a8a9220087225454910043b0aa2a488021e85515244010e42a8a9220087605454910043b1a9aa488021d894d5244010f84a6a9220087425354910043b0a9aa488021f054d5244010e82a6a9220087637654910043b13b2a488021d85d95244010ec0eca9220087637454910043b13a2a488021d85d15244010ec0e8a9220087636454910043b1322a488021d85915244010ec0c8a9220087637354910043b139aa488021d85cd5244010ec0e6a9220087636354910043b131aa488021d858d5244010ec0c6a9220084f27614910042b93a8a4880216c9d05244010b62e829220087315414910042e9398a488021745cc5244010ea2a629220085e27214910043b0a90a4880215c9d74244010ae2eba12200873154d0910042e939e8488021745cf4244010ea2a7a12200876152d0910042b93ac84880215c5d64244010e62a921220085d27390910042e8b9c8488021d454e4244010ec2a521220085727550910042b8baa8488021cc5514244010ea2a6a1220087615250910042b93a884880215c5d44244010e62a821220087515310910043b0a908488021e85084244010ae4eb1922008571758c910042d93a464880216c5d23244010e62a91922008751538c910043b0a9464880215c9d53244010ae2ea9922008731544c910043b0a9264880215c9d43244010ae2ea1922008731540c910043b0a906488021f04c83244010
  | 1 => 0x200422ebb4a610021879925308010c3ac9298400845f7654c200422ebb2a610021879915308010c3ac8a98400862e649482004316b24a4100219398e5208010c9ac7290400862e645482004316b22a4100219398d5208010c9ac6a90400863654984200431aaa4c2100219594e6108010caaa7308400866552984200431b2a2c2100218d5516108010caca6b084008655535842004333292c2100219954961080108f2edaa4200855973d5210042b4b96a9080218e5965484010c72caaa4200847976d4e100429cba6a7080215a5cb5384010e32a929c200871a5454e100438caa2a7080211e5db5284010a72e9a94200855973d4a1004334b2ca508021ca5525284010e92a729420086696554a10043952a2a508021ca5515284010e94a6a9420087495354a100423cbb4a3080211e9db5444010ab2e7aa2200856972d51100429cbaca8880218ed965444010c76caaa2200873271551100439838aa8880211e9db5344010a72e9a9a200856972d4d10042acbaca68802196d965344010e32a929a200865b6554d100438d2a2a688021c65515344010ea4e2a9a20087507154d100423d3b6a4880214e5d35244010ab2e7a922008569759491004335b2ca488021ca5525244010e92a7292200866b6554910043952a2a488021ca5515244010e94a6a9220087495354910043b138aa488021d81c55244010c72a9b0a200865953d851004334a96c2880211e9da5144010e62a928a20087515394510043b0a94a2880215c5d74144010e62a9a0a200875153d0510043b0a968288021cc5524144010ea2a720a2008761529051004398aa28288021d454d4144010ec2a4a0a2008571751051004398aa08288021749cc4144010ba2e620a20087515310510042f13908288021785c84144010ec2a420a200857175cc51004398aa66288021d454f3144010ec2a598a2008731548c510043a8a9c6288021d854a3144010e62a898a2008751534c510043b0a9262880215c5d43144010b64e818a20085b1740c51004398aa06288021d454c3144010bc4e418a20085e1720c510043b0a9062880215c5d72144010e62a990a200875153c8510043b0a964288021cc5522144010ea2a710a2008761528851004398aa24288021d454d2144010ec2a490a20085717508510042d93a042880216c5d02144010e62a810a20085d27308510042e8b984288021d454c2144010ec2a410a200867175d9510042b93b6ca880219c9db6544010ae2e9b2a200857172d9510042b8bacc8880215cdd56444010bc6e4b2220085e07259110042f1390c888021785c864440109e4edaa220085e272d5110042f0b96a8880215c9db5444010ce4edaa2200876272d5110042b8b96a888021d85cb5444010ac2e5aa220085717595110042d8baca8880214c5d65444010d66cb2a220
  | 2 => 0xa9190210fdd9548c81087aecaa4640861e6494e320430eb24a71902187991538c810c3ac8a9c640862e6494a3204316b24a5190218b991528c810c5ac8a94640843e74995320421eba4ca990210f9d0654c81087ae832a640847a7019532042a639aa4990210f9d2650c81087ae9328640843e74194320421eba0ca190211e9c0650c810a9ae7290640854f754c832042a6baa641902193d95320c810c9aca990640870e544c83204386aa264190218d5526190010caaa730c800866552986400423bbaac3200218d5516190010caaa6b0c800866552586400422f39eca20021175cf65100108dce5b28800846d72d944004237394ca200211b5ca65100108eae2b28800846e721944004236b90ca20021175d66310010c3ca9318800861d5498c400422fbaac620021879516310010c3aa8b18800845f7694c400422ebb4a62002117dd953100108baeca98800846d7598840043172a4c4200218b5526210010c9ca7310800864d539884004237baac4200218b9516210010c5aa8b10800864e535884004326a9ac4200211bdda52100108daed290800864e639484004326b1ca4200211bdd952100108daeca90800864e635484004326b1aa4200218d5526110010caca73088008655539844004333294c2200219954a6110010c6ca8b08800863554584400432b29ac2200219554d6110010ccca4b08800866552584400431aaa4c3180219554e618c010ccaa530c600847775586300431aaa2c3180219554d618c010ccaa4b0c600843e74d94300421eba6ca180211b9cb650c0108dae5b28600847571594300421ebacc8180210fdd5640c01087eed2a0600843d76950300421fbb2a8180210f5d9540c010c3cc9298600861d6494c300430f322a61802187591530c0108daeb310600862e549883004316aa4c4180219394e620c010c9aa7310600846f7558830043172a2c4180218b551620c010c9ca6b10600864d535883004237bb4a4180211b5da520c010c5cc9290600862d649483004237bb2a4180211b5d9520c010c5cc8a90600862d64548300431b2a4c2180218d552610c010caaa73086008666529843004332a94c2180218d951610c010c6aa8b08600865653584300432aa9ac21802199949610c010ccaa4b08600863554986200432aa9cc3100219954a61880108eeeab0c400863554586200432aa9ac31002199549618801087ce9b28400843d74d94200422f39eca10021175cf650801087ce9328400843d74994200422f39cca10021175ce65080108eae2b28400843e74194200421eba0ca10021179cc65080108bae6328400843d75990200421fbaac8100210fdda540801087aed2a0400843f76550200421ebb2a810021175d66308010c3ca9318400861d5498c200422fbaac610021879516308010c3aa8b18400845f7694c
  | 3 => 0xd36394810a5ce931ca40852d7498e5204326b18c7290214b9d06194810a5ae830ca40854e7318652042a6b98c3290214b9d06094810a5ae8304a40854e7318252042a6b98c129021179cf64548108bae7b22a40843e74d8d520421eba6c6a90214b9d36254810a5ae9b12a40854e73d8952042a6b9ec4a90211b9db5454810a9ce7aa2a40854d73d5152042373b0a8a9021539cc5454810a9ae62a2a40852e74d4d5204296ba6a6a9021c39525354810e1aa929aa40870e5454d5204386aa2a6a9021539cf6454810a9ae7b22a40854e7399152042a6b9cc8a90218b5906454810a5ce9b1aa40852d74d8d52042973a4c6a90214b5d26354810c9ac631aa40852e741855204296ba0c2a9021539cc6154810a9ae630aa40852e741815204296ba0c0a9021539cc6054810a9ae6302a40852e740415204296ba020a9021535cc105481087aed2a0a40843f76550520430f2a4c629021875526314810c3ca8b18a40861d5458c520422ebb4a629021879925314810c3ac9298a40845f7654c520430f322a629021875915314810c5ca9310a40862d54988520432729cc4290219354e62148108deeca90a40862e645485204316b22a4290219398d5214810c9ac6a90a40861e6498c520430eb24c629021879916314810c3ac8b18a40862e649885204316b24c4290219398e6214810c9ac7310a40863664984520431ab24c2290219598e6114810caac7308a40863a64980520431cb24c0290219698e6014810cb2c7300a40845e73d97420422eb9ecba1021179ce65d08108bae732e840845e73197420422eb98cba10211d9c465d08108f4e032e840845d7598f420430f2a4c7a10218755263d08108beeab1e840861e5458f420430eaa2c7a102117dda53d08108baed29e840845f7654f420422ebb2a7a10219398e52d0810c9ac7296840864e6354b4204326b1aa5a1021179cf65908108bae7b2c840845e73996420422eb9ccb21021179cc65908108bae632c840847671196420423d380cb21021175d66390810c3ca931c840861d5498e420422fbaac721021879516390810c3aa8b1c840845f7694e420422ebb4a72102117dd953908108baeca9c840864e6394a4204326b1ca5210219398d5290810c9ac6a94840845e73995420422eb9ccaa1021179cc65508108bae632a840847671195420423d380caa10214b1c95450810a58e8a92840845e73994420422eb9cca21021179cc65108108bae6328840847671194420423d380ca210214b5ca5410810a5ae9290840852f755084204296baa84210218bd954210810c5acaa10840870e535084204386a9a84210210f9d3658c81087ae9b2c640843e74996320421eba4cb190210f9d0658c81087ae832c640847671196320423d380cb190210f5d6648c81087eeab24640843f76952320421ebb4
  | 4 => 0xe0ec90a60887c132485304434cb226018221b2589300c110a5ae8296408854d7314b20442b23aa4390221781c121c81109e0e2b2440884f07158e20442b93a8c3102216c5d06188110ba2e630c40884f0765062044358b22831022178dc94188110ae0ea90c408843f74595204421e3a2ca9022117dcd65481108b8e6b2a408852d7414920442a6b98a4902212d5d061481109aae630a408856475485204423c3aac8902213c1c564481108f0eab1a40884f07158d204423d3b0a4902216a5d05248110b92e629240885c97390920442f0b8c84902216a5d23248110bc2e319240884b974185204426cb98c2902216c5d06148110ba2e630a40884f27518520443393a8c290221ac9d061481109e2e830a40886b1741852044258ba0c290221b49cc61481109e2e630a40886d1731852044268b98c2902213c1da4148110d66c920a40885e17290520442783b28290221ac5914148110f4284a0a40884f0768c52044369b1c6290221785ca31481109e0ec98a40887c1324c5204433432e4290221b81872148110ce0cb10a40885e172885204433432a42902215c1d52148110ce0ca90a40887607548520443b1b2a4290221b81952148110ec0ca90a40885e37448520442f0ba24290221b8d912148110dc2c890a40885e37348520442f0b9a4290221b8d8d2148110dc2c690a40886a9644802044364b1a4010221b85852008110d62c920420886b3645021044368b1c6108221b4d8d3084110dc2c510420886e362482104432731cc5aa0219398d62d5010c9ac6b16a808659639835404334b14c1aa0214b9cb5495010a5ae5aa4a80845e7398a540422eb9cc52a021479cf6295010a3ae7b14a80851e7398a540428eb9cc52a0218b5886295010a3ce6304a80851d731825404297390c12a0214b5c86095010a5ce5b22a80852d72d91540422f39ec4aa021175cf6255010a3ce7b12a80851d73d89540428f39cc4aa021475ce6255010c5ac4312a80851e73181540428eb98c0aa0214b9c86055010a5ae4302a80843f765505404316aa4c42a0218b5516215010c5cc9310a80864e639885404317322c42a0219398d6215010c9ac6b10a80865a63980540432cb1cc02a0219a98a6015010cd2c5300a80861e5498f520430eaa4c7a90218795163d4810c3aa8b1ea40861e6498f520430eb24c7a90218799163d4810c3ac8b1ea40863564987520432ab1cc3a90218e59260d4810cb2c7306a40852e74d4a5204296ba6a529021539cf5294810a9ae7a94a40845e73992520422eb9cc9290210f9d2639481087ae931ca40854e73d5252042a6b9ea929021539cc5494810a9ae62a4a40852e74d4e5204296ba6a729021c39525394810e1aa929ca40854e73d9252042a6b9ec929021539ce6494810a9ae7324a40862d6419252042973a6c7290214b5
  | 5 => 0x84f071582424422fb9acaa1221171cd65509108bce632a848845d73195424421f3b4a8a12210f1d95450910a38e6aa2848852c7255142442373b4a4a12211b1d95250910a58e8a92848854c73549424422fb9aca21221171cd651091087ce8328848845e73194424422eb98ca212211b9c8651091087aedaa0848851d731504244296b90a8212211b5db5210910a5ae8290848854d7314842442973aa84212214b1d54210910c5ecaa10848862d65508424423a3aac221221a950961109109e0e0b088488478755804244354a12c0212213c1c5601091087ce9b2c648843d74d96324421f3a0cb192210f5d0658c910c3cc9a9c648851d7414e324430f320a719221535c8538c910c5ac9294648852c7454a3244316b22a519221531cd528c9108e8eab0c64884f070586324423c3aac1192213c1c5608c91087ee8b2a648843c74595324421f3a0ca992210f5d0654c9108dced292648846c7654932442963a2a499221531cd524c91087ee8b28648843c74594324421f3a0ca192210f5d0650c9108dce4328648846d76d483244296ba0a419221535cc520c910a9cea990648854c754c83244327b2a641922193595320c9108f0eab0064886c932580324427838ac019221475cc54d0110a5ae42a680884f07158e404427838ac5202215c9d46190110ba2e630c80885e1721864044237b92caa02211b1c96550110a3ae62a2808852d72151404426ab98c2a0221395c861501108f4ec2a280885997315140442d4b90a8a02216a5cb4350110b62e3a1a808859973d0940442d8b8e84a0221365cc61501109d2e430a80885d17318540442f0b90c2a02213c9d46150110ce4ea30a80886d2731854044278b98c2a0221b45cc61501109a2e630a80886e2721854044278b90c2a0221b85c861501109c2e430a808863865d05404435830e82a02219c1964150110b62e920a808863865505404433832a82a0221ccd954150110e60caa0a80885b3725054044359b1282a0221a658d4010110d52c4a0080886b161500404428eba0a798221535c853cc1109e0e2b2460884f07158a30442b93a8c3182216c5d0618c110bc2e430c60884f0765063044358b22831822174dcd418c110a3ae829a608854d7214d304425aba0c298221395c8614c1108f0eab2260884f071591304423d3b0a698221665d0534c110b92e429a60885c97290d30442e8b8c8698221665d3324c110ba2e399260884b9741853044274b90c2982216c5d0614c110bc2e430a60884f27518530443393a8c298221ac9d0614c1109e2e830a60886b1741853044258ba0c298221b89c8614c1109e2e430a60886e1721853044270b90c2982213c1da414c110d66c920a60885d17390530442783b28298221ac591414c110f2286a0a60884f07688530442e8b9c4298221b8d8a214c1109
  | 6 => 0x842d8b8ea8a04211e9d85450210974ec2a281085997315140842d4b90a8a04216a5cb4350210b32e7a1281084d9731854084274b90c2a04210fdd95410210c3ca8b18810861d5458c40843172a2c4204218b5516210210c6ca8b08810863554584408434cb1a8020421aa5894010210d62c2a00810851d7414f30842a6b90a798421179d8534c210a3ae829a610854d7214d30842e8b8ea6984211e9d8534c2109b4ec29a61085997414d30842e4b90a698421725ca434c210b32e999261084b9741853084274b90c29842187592530c2108beeca98610861d6454c308432729ac4184219354d620c210caca6b08610865553584308434cb226018421b2589300c210da2c2980610852d7414b20842a6b98a5904211b9d85248210a5ae8292410854d7314920842f0b8ea4904211e9d852482109d4ec29241085a97414920842e4b98a490421725ce4248210b52e919241084b974185208426cb98c2904218b5925208210c9ac7290410846f765482084316b22a4104219358d5208210ccca4b084108665525842084354b224010421b258d2008210dc2c2900410845f7358b544422e39ac5aa221179ce62951108bae7314a88864f63d895444317b20c4aa22193d8c6255110c98c6312a88843f765505444296392a82a2218b5516215110c9cc7310a88862e64588544432731ac42a2219358d6215110cb4c6b00a888659635805444335312c02a2219a5896015110ce2c2b00a88845e73180544422eb98c02a2211b9c860151108dae4300a88845f73593524422e39ac9a92210fdd163d4910878e8b1ea48845e73992524422eb9cc9292210f9d2639491087ae931ca48862d72191524430fb26c6a9221871936354910c3ec831aa48861c6418d5244316326c4a92219318f62549108deeca90a48852c745485244316b22a429221531cd5214910c9ac6a90a48862c72590524430f324c629221875926314910c3cc8b18a48861d6458c5244326392c6292218b5926214910c9ac7310a48863664584524431ab22c2292219598d6114910caac6b08a48843e74184524421eba0c229221179cc61149108bae6308a48863a64580524431cb22c0292219698d6014910cb2c6b00a48867161580524421f3a0c0292210f5d060149108bce6300a48845d73180524422f39ecba1221175cf65d09108bce632e848845d73197424428e39aa9a12214b1c954d0910c3ca8b1e848861d5458f424432731ea5a12214b5d052d0910a9ae6296848864e6314b424423a3aac3a12213c1c161d09108f0eab0684884f071583424422f39ecb21221175cf65909108bce632c848845d73196424428eb98a9212214b5c85490910c3ea931c848861c5498e4244326b1ca5212214b1d15290910a98e6a94848864d6354a424423a3aac3212213c1c161909108f0eab04848
  | 7 => 0x6900414b5d35348020acae3a9a401054d7594d2008327b2ca690041c35525348020c9ecaa9a401070e5454d2008386aa2a69004199d965148020e4aa928a4010745539452008333b2aa290041c99515148020e4aa8a8a40107465354520083a2a9aa290041d89c15148020c5aa9b02401064d53d81200831db2ca8900418ed955448020cb6cb29a401065b6554d200838caa2a690041ca5525248020e92a72924010673659452008339b2aa290041cc9515148020e62a8a8a40107525354520083a8a9aa290041d89495148020ec4e4a8a40107636254520083b0a8e42900419c58660d52108dce531ca90846d7298e548422f39cc52a421175ce629521087eecaa0a90861d5458c5484316aa2c42a421879916315210c9cc7310a90864d639885484317322c42a4219398d6215210c9ac6b10a90865663584548432ab1ac22a421999896115210ccac4b08a908671619805484338b0cc1a9c211b9ca6494e108dae5324a70843e7498a538421eba4c529c2117dd95314e10c3ac8a98a70864d53588538430eb24c629c218b9926214e10c5ac9310a70862e645885384316b22c429c219398d6214e10c6cc8b08a708635645845384333312c229c21995896114e10ce2c3300a70846e72d974384236b96cba1c211b9c865d0e108dae432e870862e5458b4384316aa2c5a1c211b9cb6590e108dae5b2c870846e721964384236b90cb21c219394d6290e10c9aa6b14870846e721954384236b90caa1c21471cd5450e10a38e8a9a870846e721944384236b90ca21c2187d954310e10c3acaa188708699435804384338b0cc1a9421179ce6494a108bae7324a50843e7498e528421eba4c7294211bdd95214a10c5ac8a90a50864d63548528430f324c629421875926314a10c3cc8b18a50861d6458c5284316b24c4294219358e6214a10c6cc8b08a50863564584528432b31ac2294219558d6114a10ce2c3300a50845e73d97428422eb9ecba1421179cc65d0a108bae632e850861e5458f428430eaa2c7a1421179cf6590a108bae7b2c850845e73196428422eb98cb214219358e5290a10c9ac6a94850845e73195428422eb98caa14214b1c95450a10a58e8a92850845e73194428422eb98ca214218bd954210a10c5acaa1085086a942580428421f3a6cb994210f5d365cca1087ce832e650843d74197328430eb24a7994218759153cca1087ce9b2c650843d74d96328421f3a0cb194210f5d0658ca10c5ac9294650862d6454a328421f3a0ca994210f5d0654ca10a98e4a9a650854c73549328421f3a0ca194210f5d0650ca10c9eca990650864d654c83284364992c019421365cc60506109d2e430283084b9741813184274b90c098c212e5d060486109b2e6302430851d731534084296b90a9a04210f9d85450210a3ae62a2810852d721514
  | 8 => 0x1600c420c72a8b00621065a53580310832ca9ac0188419c945600c420ce2a2b00621067151583210821ebacc8108410fdd5640842087aed2a0421043f76550210822ebacc610841879526308420c3aa9318421045f7558c210830f2a2c6108418755163084208baed298421061e6494c210830eb24a61084117dd95308420c3cc8a98421061d6454c210831b324a2108418d5925108420cacc7288421065563944210831b322a2108418d5915108420cacc6a88421065563544210831d2a4c0108418e5526008420cb4a73004210659539802108338a8cc0108418e9516008420c72a8b00421065a53580210832ca9ac0108419c9456008420c5aa9314801064d5398a4008237baac5200418b5516290020c9aa6b148010666625464008332b12a320041179cf65100208bae7b28801045e73994400822eb9cca20041179cc65100208bae6328801045d7598c400830f2a4c6200418755263100208beeab18801061e5458c400830eaa2c62004117dda53100208baed298801045f7654c400822ebb2a6200418b5526210020c9ca7310801064d5398840083172a2c4200418b5516210020c9ca6b10801064d53588400823abacc2200418d9526110020c6aa9308801065653984400832aa9cc2200411ddd56110020c6ca8b08801063554584400832b29ac2200419554d61100208eaed288801065663944400832ab1ca2200419998a5110020ccac5288801047776544400832b31aa2200419558d5110020cccc4a888010665625444008316aa4c5180419354e628c0208deeab14601062d5458a3008326a9ac51804199989518c020ccac4a8c601043e74d94300821eba6ca180410f9d2650c02087ae9328601043e74194300821eba0ca180410f5d6640c02087eeab20601043f76950300821ebb4a8180410fdd9540c02087aecaa0601061e6494c300830eb24a61804187991530c020c3ac8a98601062e549883008316aa4c4180419354e620c020c5ca8b10601062d54588300832729ac4180419354d620c0208eaeb308601063654984300831aaa4c2180419594e610c020caaa7308601047775584300831b2a2c2180418d551610c020caca6b08601065553584300823abb4a2180418d992510c020c6ac92886010666629443008332b14a2180411ddd9510c020c6cc8a886010635645443008333312a21804199589510c020a9ae7aa6401056571d532008296ba6a790041595c753c8020e1aa929e401070e5454f2008386aa2a790041c955251c8020e8aa728e4010726545472008392aa2a390041d194d51c8020e8aa6a8e401046d7694a200838caa2a7100411e5da5288020e64a8a8c40107315454620083a929aa310041d454d51880208dcedaa2401054d73d5120082b2b8ea8900414b5d65448020c5ecb2a2401062f6555120082373b6a
  | 9 => 0xae6304a21045e73191510822eb98c8a88410f9d0635442087ae831aa21047676d5151082ab39ea8a8841555cf54544208ecec2a2a2105567315151082aab98a8a88411d9db5354420a6ce9a9aa21053574d4d510838b2a4a6a8841c55525354420e2ca8a9aa2107155454d510823b3b0a6a88414d9d05354420a6ae829aa2105647259151082ab398c8a8841555cc6454420acce4322a2105727019151082b2392c6a88414d9d06354420a6ae831aa2105667218d51082b9380c6a8841599cb4354420acae5a1aa2105667290d51082b2b9486a8841c550c4354420aace7a12a21055573d0951082ab39c84a8841555ce4254420ae4e1212a210571709095108392a1084a88415c9c04254420ae2e0212a21053674cc9510829aba664a88414d9d23254420a6ae9192a210572708c951082b8b8464a8841d14c83254420ae4e0192a210571700c9510829b3a0c0a88414d5d06054420aace6302a21055573181510829b3a040a88414d5d02054420aace6102a21055573081510821ebb4a8288410fdd95414420c3ca9318a21061d5498c510830f2a2c6288418755163144208baed298a21061e6494c510830eb24a62884117dd95314420c3cc8a98a21061d6454c510831b2a4c2288418d5526114420caca7308a21065553984510823bbb2a2288418d9915114420c6ac8a88a21065663544510832ab1aa228841179ce65d04208bae732e821045e73996410822eb9ccb20841179cc65504208bae632a821046d75d894108316aa6c4a08419354f6250420c5aa8312821064d531894108333b12a2a08419918951504208bce7b28821045d73d94410822f39cca20841175ce65104208baeb318821061e5498c410830eaa4c62084117dd56310420c3ca8b18821061d5458c410822fbb4a620841175da53104208beeca98821045d7654c41083172a4c4208418b5526210420c9ca7310821064d5398841083172a2c4208418b5516210420c9ca6b10821064d53588410832b31ca2208419558e5110420cccc5288821066562944410832b31aa2208419558d5110420cccc4a88821066562544410831d2a4c0208418e5526010420cb4a73008210659539804108338a8cc0208418e9516010420c72a8b00821065a53580410832ca9ac0208419c9456010420ce2a2b00821043e74997310821eba4cb988410f9d2658c42087ae932c621043e74195310821eba0ca988411b5d7624c420c5aa9b12621064d53d893108316aa0c4988419354c624c420ccec4a8a621066462545310821f3a4ca188410f5d2650c42087eed2a0621043d76950310821fbb2a8188410f5d9540c420c5ca9310621062d54988310832729cc4188418b951620c420c5aa8b10621064e535883108326a9ac4188418e952600c420c72a9300621065a53980310832ca9cc0188418e95
  | 10 => 0x639649805308338b0cc0298411d9c665d0c208eae332e861046d725974308237390cba18411d9c465d0c208eae232e861046d7598b4308316aa4c5a18419394e62d0c20c9aa7316861062e5458b4308316aa2c5a18419394d62d0c20c9aa6b16861047671996430823ab8ccb218411b5c96590c208dce432c861047671196430823ab88cb218411b5d66290c20c5ca9314861062d5498a4308326a9cc5218418b9516290c20c5aa8b14861064e5358a4308326a9ac5218411d9c66550c208eae332a861046e72195430823b388caa18411d5c46550c20a38e6aa2861051c7454d430823b38cca218411d5c66510c208dce4328861047671194430823ab88ca218411e9c06510c20a3ae72a0861051d7494c430828fbaa8621841475d54310c20c3ecaa18861061d6550c430822f39cc929041175ce649482087ce931ca41043d7498e520830f2a4c7a10418755263d0820c3ca8b1e841061d5458f420822fbb4a7a1041175da53d08208beeca9e841045d7654f420822f39ecb21041175cf65908208baeb31c841061e5498e420830eaa4c72104117dd56390820c3ca8b1c841061d5458e420822fbb4a721041175da53908208beeca9c841045d7654e4208326b1ca5210418e5516090820a5ae4aa0841062f655084208316b2a8421041c394d4210820e1aa6a10841065953980420831d2a2c0210419654d601082087eed2a6641043d76953320821fbb2a9990410f5d954cc820c3cc929e641061d6494f320830f322a7990418759153cc82087ce9b2c641043d74d96320821ebacc9190410fdd5648c82087eed2a4641043d76952320821fbb2a9190410f5d9548c820c3cc929c641061d6494e320830f322a71904187591538c820c5ac929464106595358232082a6b92a61904193d95320c820c9aca990641070e544c83208386aa264190418e552600c820c72a8b00641065a53580320830f2a4c7a88418755263d4420c3ca8b1ea21061d5458f510830f324a7a88418759253d4420c3cc8a9ea21061d6454f510829b3a6a3288414d5d35194420aace7a8ca21055573d4651082ab39ea928841555cf5494420aace62a4a21055573152510829b3a6a7288414d5d35394420e2ca929ca2107155494e510838b2a2a728841c55515394420a6ce829ca2105357414e51082ab398c928841555cc6494420acce4324a21057270192510829b3a0c7288414d5d06394420acce431ca2105727018e51082b33968728841595cb4394420acce521ca2105657290e510838aa1887288414d9d06294420a6ae8314a2105567318a51082aab98c528841559cf4294420aaae7a14a2105567390a51082aab9c8528841c95084294420a6ce9994a21053574cca510829b3a465288414d5d23294420e8a64194a21053674182510829aba0c128841559cc6094420aa
  | 11 => 0x482963aa84a02418b1954250120b50e0a1280904ad7498b304832629ac598241531d532cc12087ce9b2a609043d74d9530482a63aa649824193195324c120b90e099260905c97390b20482d4ba46590241b858721c8120c9ac7316a81065663987540832ab1cc3aa0419598d61d5020caac6b0ea810666625875408338b0cc1aa041479cf5495020a3ae7aa4a81053671d52540829ab8ea92a0411b9ca6395020a5ce5b1ca81052e7298e540830eb18c72a041479ce6295020a3ae7314a81051e73186540828eb98c32a0414b9c86195020a74e030ca81051e73182540828eb98c12a0414d9c46095020a6ae2304a81051e73d91540828eb9ec8aa0414d9c76455020a6ae3b22a81045e73d89540822f398c2aa041175cc6155020a5ce5b1aa81052e7298d540830eb18c6aa041479ce6255020a3ae7312a81052c72585540828f398c2aa041475cc6155020a5ce430aa81053a70185540828f398c0aa041475cc6055020a6ce2302a81053571181540821fbb2a82a041875526315020c3aa8b18a81063554984540831aaa2c22a041879926315020c3cc8b18a81064e639885408326b1cc42a0418d9926115020cacc7308a810655639845408333314c22a0418d9916115020cacc6b08a810655635845408333312c22a0419658e6015020ce2c3300a81063654987530831aaa4c3a98418d95161d4c20c6aa8b0ea61062d6498b530831b324c3a98418d59261d4c20c6cc8b0ea610635645875308333312c3a98419c58660d4c20a3ce9a9ca61051d74d4e53082ab38ea729841555c75394c208dce5324a61055671d5253082aab8ea929841559c45494c20aaae22a4a61054e72d9253082a7394c929841875906494c20a3ce9314a61051d7498a530828f3a0c329841475d06194c20a9ce430ca61055a70186530828f3a0c129841475d06094c20aace2304a61055571182530828f3a6c6a9841475d36354c20aace3b1aa61055571d8d530821f3a6c4a98410f5d36254c2087ce830aa61043d74185530822f3b6a8a9841559c75454c20aaae3aa2a61045e7615153082ab388a8a9841555c45454c20a9ce5b22a61054e72991530830eb20c8a9841479d26254c20a3ae9312a61054c72585530828f3a0c2a9841475d06154c20a9ce430aa61055a70185530828f3a0c0a9841475d06054c20aace2302a61055571181530828f3a040a9841475d02054c2087aed2a0a61043f76550530830f2a4c629841875526314c208beeca98a61061e6454c530830eb22a6298418d9526114c20c6aa9308a61065553984530831b2a2c2298418d5516114c20caaa6b08a61061e6498c530830eb24c6298418b9926214c20c5ac9310a61063664984530831ab24c2298419598e6114c20cccc5308a61063664584530831ab22c2298419598d6114c20cccc4b08a610
  | 12 => 0xaa2410fdd95415120a3ae7320a89061d64d4e5348316b94c929a418b9916294d2087ce830aa69043d74185534822fbb2a629a41475d26314d208dae5b2e869046c7558b4348317aa2c5a1a418b15162d0d208dae5b2c869046e7219643482363aac521a4193d4d6290d20c98a6b14869047771595434823a38acaa1a41479cf5450d20a3ce9a9a869047671194434823ab88ca21a41879954310d20c38caa18869068d4398843482363aac421a411e1d56010d20d3286b00869061f5458f424830e2a2c7a1241539ce5490920c9ccab1c849064c7558e42483272a2c7212419315163909208daed29c849052e7494e4248326b1ca7212411b5d85390920c9ac629c849070c5350e4248278b88c0a12414b9d76450920b1ce7b22849052e7495142482a739ca8a12411b9d85450920a5cec2a2849062e761514248297398a8a12414b5c45450920c58a9b1a849046e7694d42482973a4a6a12411b9d85350920a5ceb21a849070c5390d42482573b086a12414b1d44350920b52e021a84904cd731814248272b88c0a1241785c46050920c3ac9a9e649061d6414f324831732ac9192418b1d5648c9208daed2a4649062d6495232482a739ca9192411b5d8548c920c5ac82a4649052e7494e3248316b24a7192418b590538c920e18a8a1c64904f17118132482363aac8992413a1c1644c9208dced2a2649054e7395132482373b0a8992418b590544c920a9cebb1a649058e74d8d32482973a4a699241539ce534c9208dcec29a649054e7614d32483273b0a699241539d0534c920c9ec829a649064d6414d32482a6b88a699241339db434c920a9ceba1a649070c54d0d32482673b08699241531d4434c920d1ac821a64905c97010d3248256ba0c099241395c4604c920bc2e230264904ad74988324822f39cc9a8a41175ce64d452087ce931ea29043d7498f51482a6b9c85a8a414b5d232d45208eeeca88a29061e6498c514830eb24c628a41879916314520c3ac8b18a29063a64580514831cb22c028a419698d6014520cb2c6b00a29051d739534148266b9cc5a0a418b19542d05208bee6b2c829045c73596414822f398cb20a41175cc659052087ced2a2829051d73951414831632a84a0a41179cc65105208bae6328829043d76d50414830faa2c620a41871516310520c5ea8b10829062c54588414831daa2c020a418e1516010520a3ae929e62904ad7498b314832632a6598a410fdd1658c520878e8b2c629043e74196314821eba0cb18a4193195324c5208dcebb2642904cd73d932148237bb2a990a411b9d763c852095ae9b1e429046f7654f2148296ba0a390a41535cc51c8520ad4ea306429052d7414521482a6b98a290a412b5d0604852099ae630242904cd7398b40483162a2c5a02414b1d542d01208bce7b2a809045d73d9540
  | 13 => 0x654cb20a5ce9b2a659046e7695132c82a739ca8996411b9d8544cb20c5ac82a2659058e74d8d32c82c73a6a699641725c3534cb20a5ce929a659046e7614d32c82673b0a699641539d8534cb20c9cec29a659054e7414d32c8327b20a69964193590534cb20a9ae229a65907497014d32c82a73ae8699641c3153434cb2099cec21a659054c7510d32c8346b208699641c3950434cb2095ae830265904e57118132c828eba4a61964117dd9530cb20d9264b00659054d7390951c831632284a8e414b5d23254720c98c6992a3904777654451c822f39ecba0e41175cf65d07208bce732e839045d7399741c828eb9ca9a0e41335ce62d0720a3ae72a2839062c6550941c822f39eca20e41175cf651072087ce932e639043d7499731c8256ba4c598e41335cf64c8720a9ae7aa6439052d74d4f21c82373b6a890e41535cf54487208dceda9a439052d74d4d21c82f0b86a290e41399d8514872095ae830243904cd7318121c8338a8ac010e41b84856008720a3ae72a681904cd7398b40c828eb9ca8a06418b5506250320a3ae929e61904ad7498b30c828eba4a6986419354c624c320ae2e3306a91045e73185548822eb98c2aa4410fdd95415220c3aa8b18a91063554584548830f322c62a4419398d6215220c9ac6b10a91065663984548832ab1cc22a4419958a6115220c6cc8b08a91065663584548832ab1ac22a441995896115220ce2c3300a91057171983538821f3a0c2a9c410f5d06154e208beeca98a71061d6454c538832aa9ac229c41875926314e20c5cc8b10a71062d64588538831b324c229c418d5926114e20ccac5308a71063664584538831ab22c229c419598d6114e20ccac4b08a71067161980538823b388cba1c411d5c465d0e20c5ca8b16871062d5458b438823b388cb21c411d5c46590e20c9ca6b14871064d5358a438823b388caa1c411d5c46550e20a38e6aa2871051c7454d438823b388ca21c411d5c46510e20c3ecaa18871061d6550c438834ca1ac021c418795163d0a20c3aa8b1e85104f171181428830eb24a7994418759153cca209e2e2302651045e73191518822eb98c8a8c410f9d0635462087ae831aa31047776544518831ab22a228c419558d51146208bee6b2a831045c73595418822f398caa0c41175cc65506208bce7b28831045d73d94418828eb98a9a04414d5c454d022087cec2a2811051d73151408829ab88a8a04410fdd95410220c3ca8b18811061d5458c40883172a2c4204418b5516210220c6ca8b08811063554584408828eba0a798441555c453cc2208bcec29a611051d7414d30882aab88a69844187592530c2208beeca98611061d6454c308832729ac4184419354d620c220caca6b08611065553584308830faa2c72a241935ca6395120c9cc6b14a89045e73185544822eb98c2
  | 14 => 0xa4a8c601876152546300c22f3b6a898061535cb544c030aaae3aa2601851d75951300c30fb2ca89806187d95544c030c9ecb292601870d54949300c327b2aa498061c3951524c030e1aa8a92601865765945300c38aaa4a298061d154a514c030caecaa8a601871654545300c38aaa2a298061d1949514c030e8aa4a8a601875270545300c30eaa6c0980618ed96544c030c76caaa260187195494d300c335b2ca4980619ad95524c030e52a8a92601874a53549300c339b2ca2980619cd95514c030e64a8a8a601873154545300c3a929aa298061d8949514c030ec2a4a8a601875273545300c3a9b1aa2980619358e62d5320a3ce7aa4a99061f5458e54c8327394c72a641935ca6395320c9cc7314a99064d6398a54c828f39ec8aa641179cc61553208bae630aa99043f7655054c828eb9cc82a641535ce6215320c3ae7326a79062d6498b53c828f3a6a729e41875935394f20c5ce5324a79062d7299253c830e39ac929e418b9926294f20c5ac9314a79051e74d8d53c821f3a0c2a9e410f5d06154f208beeca98a79051d7498c53c8296ba4c429e41479cf54d0f20a3ae929e879064e5398b43c8326a9cc5a1e418bd5162d0f20c58a8b16879051d7395243c828f3a6a721e418b9526290f20c5aa9314879064f5358a43c832629ac521e41479cf5450f2087cec2a2879051e74d4d43c822f3b0a6a1e411d9c46510f208eae2328879051d7395043c821fbb2a821e41475d25310f208beeca98879051f7550c43c828ebaa8621e41879954310f20c38caa18879068d4398843c828f39ea9a164187d5163d0b20c38a8b1e859051d7395242c830f2a4c721641875526390b20a9ce72a4859058d7395242c8326b2cc721641935956390b20c9eeab1c859064c7558e42c83272a2c721641931516390b208daed29c859052e7494e42c8326b1ca7216419358c5390b20a5aeba1c859070c5350e42c8364b1ac121641479cf5450b2087cec2a285904cd73d9542c82a739ecaa1641639cf6450b20b1ce7aa285905a970d5142c82a739ca8a16411b9d85450b2095cec2a2859052e7615142c83173b0a8a16414b9cc5450b20a5ae22a285907297015142c83162a6c6a16411b9da5350b20a5ce929a859046e7614d42c82973ac86a1641c314e4350b2095cec21a859052c7510d42c838729886a1641335cc6050b209cae2302859051d7395042c821fbb2a821641aa5096010b20a3ce9a9e659061d64d4f32c830eb20a799641475d2538cb20c3cc929c659061e6454e32c8316b2cc9196418b595648cb20c5eeab24659062c7559232c8236bb4a9196418b592548cb20a9ce72a4659062d6415232c82973a4a7196418b592538cb20b1ae929c659062d6414e32c82a6bac8719641c3151438cb20d52c8b04659051e74d4d32c822f3b0a6996412b5d3
  | 15 => 0x3d76950510c21fbb2a8288618b9526214430c5aa9310a21862e54588510c316aa2c4288611b5da5214430c5cc9290a21862d64948510c237bb2a4288618b9915214430c5ac8a90a21863654984510c31aaa4c2288619994a6114430ccaa5308a21847776544510c31b322a2288618d5915114430cccc4a88a21866562544510c237394cba08611b5ca65d04308dce532c821846d72996410c237390caa08611b5c86550430c3aa9b1a821861d5418d410c327b1aa4a08619318d5250430caec6a8a821865463545410c237396ca208611b5cb65104308dce5328821846d72994410c30f2a4c620861875526310430c3ca8b18821861d5458c410c236bacc4208618b9526210430c5aa9310821846f75588410c3172a2c4208618b55162104308deed290821846d76948410c32731ca4208619358e52104308deeca90821846d76548410c32731aa4208619358d5210430cacc7288821865563944410c333314a2208619958a5110430cacc6a88821865563544410c333312a220861995895110430c74a9300821863954980410c335294c0208619a54a6010430ce2a3300821863a54580410c31caa2c0208619a9496010430cd2a4b00821867251580410c338a8ac0208610f9d265c843087ae932e421843e74996210c21eba4cb108610f9d0654843087ae832a421861d54d8d210c30eaa0c69086193d8d5248430c98c6a92421865763545210c32a31aa2908610f9d2650843087ae9328421843f76950210c21ebb4a8108610fdd9540843087aecaa0421862e64948210c316b24a4108619398e5208430c5cc8a90421862d64548210c32731aa4108619358d5208430c74a9300421863954980210c335294c0108619a54a6008430c74a8b00421863954580210c335292c0108619a5496008430ce4a2b00421867151580210c30eaa4c72006117dd56390030c3aa8b1c801864e6354a400c326b1aa5200619598d5190030caac6a8c801861d5498c400c30f2a2c6200618755163100308daeb310801862e54988400c316aa4c4200611bdd56210030c5ca8b10801862d54588400c236bb4a4200619398e5210030c9ac7290801846f76548400c32731aa4200619358d52100308eaeb308801863654984400c31aaa4c2200619994a6110030ccaa5308801847775584400c31b2a2c2200618d5516110030ccca4b08801866552584400c23abb4a2200619598e5110030caac7288801866662944400c332b14a2200611ddd95110030cacc6a88801865563544400c333312a220061995895110030a9ae5aa6601855571d53300c386aa4a598061c395152cc030e1aa8a96601871554947300c3a2a94a398061c595151cc030e2aa8a8e601874652547300c3a2a92a398061175da538c0308f2ed29c60187295454a300c3992a2a318061cc551518c030ec4
  | 16 => 0xc332a94c2290618d9516114830c6aa8b08a41866552584520c23b38ccba10611d5c665d0830c3aa931e841861e5458f420c30eaa2c7a10619398e52d0830c9ac7296841864e6354b420c326b1aa5a10611d9c665908308eae332c841861e5498e420c30eaa4c721061879516390830c3aa8b1c841864d6394a420c32731aa5210619358d52908308ece232a841847571195420c296392a8a10614b1d152508308ece3328841847571994420c296b94a8210614b5d25210830a5eeaa10841852d75508420c317b2a84210618b595421083087aeb326641843f75593320c21ebb4a9990610fdd954cc830c3ac929e641862e6494b320c316b24a5990618b99152cc830c5ac8a96641866952583320c21fbb4a9190610f5da548c83087eecaa4641843d76552320c317322a5190618b591528c830e1ca8990641870d544c8320c31caa4c0190618e551600c830cd4a4b00641862e5498b510c316aa4c5a88618b95162d4430c5aa8b16a21862e6494b510c316b24a5a88618b99152d4430c5ac8a96a21853674d46510c29aba6a328861599cb5194430acae5a8ca21856672d52510c2b2b96a928861599c85494430acae42a4a21853674d4a510c29aba6a528861c99525294430e4aa9294a2187265454a510c392aa2a5288614d9d05294430a6ae8294a21855673192510c2b3390c928861595c86494430ae4e0324a2185367418e510c29aba0c728861599c86394430acae431ca21856672d0e510c2b2b968728861599ca4394430acae521ca2187154310e510c29b3a0c5288614d5d06294430aace6314a2185727018a510c2ab39e8528861555cf4294430aace7214a2185557390a510c392a1085288614d9d33294430a6ae9994a218536748ca510c29aba46528861d14c83294430a6ce8304a21853574182510c2b3390c128861595c860944308dce4322a21846d72191510c21f3a0c4a88610f5d062544308ecedaa2a21856672d51510c2b2b96a8a88611d9d85454430acce42a2a21856572151510c23b3b6a4a88614d9d35254430a6ae9a92a21872654949510c392aa4a4a8861c99515254430e4aa8a92a21847676149510c29b3a0a4a88614d5d05254430aa8e6b22a21855673191510c2b3390c8a8861595c86454430ae4e0322a21856672d0d510c2b2b9686a8861599ca4354430acae521aa2185727090d510c2b8b8486a8861c550c4354430ae4e021aa2185717010d510c2aa39ac4a88614d9d06254430a6ae8312a21855673189510c2b9380c4a8861559cf4254430aaae7a12a21855673909510c2aab9c84a8861c95084254430a6ce9992a21853574cc9510c2b938664a88615c5c33254430a6ce9192a218535748c9510c3a299064a88615c9c03254430ae2e0192a218536740c1510c29aba060a8861599c83054430acae4182a2184
  | 17 => 0xa618719543505308dce4328829846d72194414c21ebb6a820a6187d516310530c38a8b18829862f54588414c3162a2c420a618ed516010530c70a8b00829849d7498f214c32632a6590a610fdd16588530878e8b2c429843e74196214c21eba0cb10a6193195324853099ae531e809861c5458f404c28e3aa87a0261471d54350130c38caa1a80985987050d404c2e4b948798261665d332cc130c9cc6b16a81866662987540c332b14c3aa0619598d61d5030cccc4b0ea81866562587540c338b0cc1aa0614b9cb5495030a5ae5aa4a81853671d52540c29ab8ea92a0614b9ca6395030a5ae531ca81851e73d8a540c28f39cc52a0618b5886295030a3ce630ca81852e72186540c296b90c32a0614e9c06195030a5ce4304a81852d72182540c29b388c12a0614d5c46095030a5ce5b22a81852d72d91540c29b38ec8aa0614d5c764550308dce430aa81846d72185540c297394c6aa0614b5ca6355030a3ce7b12a81851e73989540c316b10c4aa061471cd6155030a3ce630aa81852e72185540c296b90c2aa0614e9c06155030a5ce4302a81852d72181540c29b388c0aa0614d5c4605503087eecaa0a81862d54988540c316aa2c42a0618d5526115030c6aa8b08a81862e64988540c32731cc42a0618b9916215030c9cc6b10a81863664984540c32b31cc22a0619998a6115030ccac5308a81863664584540c32b31ac22a061999896115030ccac4b08a81866962980540c338b0cc02a0618b95262d0c30c5aa9316861862e5458b430c316aa2c5a18611b5d66290c30c5ca9314861862d5498a430c237baac5218618b9516290c30c5aa8b14861864e5358a430c31caa2c12186187d954310c30c3acaa18861863a54580430c31b2a4c3a90618d55261d4830c6ca8b0ea41863554587520c2973a6a5290614b5d35294830acce3a94a41856571d4a520c2b338ea929061595c75494830acce22a4a41856571152520c2a739ec929061539ce6494830c5ac8324a41846e76d0e520c236bb48729061c350c4394830a5ce830ca41852d74186520c2a7398c3290615a9c06194830a5ce8304a41852d74182520c2b3388c129061595c4609483087ce830aa41843d74185520c2373b6a8a9061599c75454830acae3aa2a41846e76151520c2b3388a8a9061595c45454830a9ce7b22a41854e73991520c316b20c8a90614b9d26354830a5ae931aa41846d76d0d520c2373b486a9061c350c4354830ad4e021aa4185697010d520c2a639ac2a90614b9d06154830a5ae830aa41854e73185520c2b5380c2a90614b9d06054830a5ae8302a41856671181520c2b2b88c0a90614b9d03054830a5ae8182a41843d76950520c21fbb2a8290618b9526214830c5aa9310a41846f76548520c317322a4290618b5915214830c6ca9308a41863554984520
  | 18 => 0x1552308dae430aa91843f76550548c316aa2c42a4618d5516115230c9ac7310a91862e64588548c326b1ac42a4619558e6115230cccc5308a91866562984548c31b322c22a4619558d6115230cccc4b08a91866562584548c338b0cc02a4618b95162d0e30c5aa8b1687184f171181438c21f3a0c2a94610f5d06154a308deeca90a51862d64548528c332a92c2294618795163d0a30c3aa8b1e851864d6394a428c326b1aa5214611d9c46550a308eae232a851852c72551428c2963a2a4a14618bd954210a30c5acaa1085186a942580428c316b24a5194618b591528ca309e2e2302651846e72191518c236b90c8a8c610f9d0625463087ae8312a31847776544518c31ab22a228c619958951146308dee4b2a831846c72595418c237390caa0c611b5c865506308dce5b28831846d72d94418c296b90a9a04614d5c454d023087cec2a2811852d72151408c29ab88a8a04610fdd95410230c3ca8b18811861d5458c408c3172a2c4204618b5516210230c6ca8b08811863554584408c317aa2c52a2619358e6295130c9ae7314a89846e72185544c236b90c2aa2610fdd95415130a5ae5320a89862f5458b434c3162a2c5a1a61539ca5490d30c9ccab14869864c7558a434c3272a2c521a61931516290d309e2e2302869851e75d91434c2c7396c8a1a61479d25450d30a9ce52a2869845e76151434c28f3b0a8a1a61879d85450d30a3ce42a2869851d71151434c30e2a6c4a1a61335c86050d309aae230286985d171181434c316b26a5292611bdd95214930a9ae5218a49845f7650c524c30faa2c7a12618715163d0930c3ccaa1c849864d63d4a424c326b18a521261c350c5290930a5ce5aa2849852e74d49424c387218a4a12611d9c465109308eae2328849849f7650c424c30e32a86212618b9954210930c58caa10849868e63508424c34ca1ac021261aa5096010930c3ccab26649861c75593324c22ebb4a9992618759254cc930a9ce52a6649845d76153324c30eb20a9992618759052cc930e18a8a16649862d64d4a324c316b20a5192613c5c4604c9309b0e0b22649854e72951324c22f3b0a89926187590544c930a9cebb12649858e74d89324c2a73b0a499261939d8524c930a9ce8292649864f64149324c326b20a499261535c4524c93099ceda12649854e75d09324c3862a68499261339d8424c930a98ea212649868d64109324c2e4b808499261275d0604c9309aae230264985d171181324c24eba4c6192611b9ca64d45308dae5326a29854d7290f514c21f3a4c5a8a610f5d262d4530a3ae9996a29847776544514c317324c428a618b5926214530c5cc8b10a29862d64588514c296b94a9a0a61335ca63d0530c38caa1e829846f72596414c236392cb20a611b9c865905308dae432c829843e76951414c296b94a8a
  | 19 => 0xb28a8020715539454010392a94a2a00818dd955150040e2ca6a8a8020715535454010393292a2a0081c95495150040e64e0a8a802065b6594d401032db2aa6a0081c69515350040cd6cb292802066b6554940103952a2a4a0081d254d5250040ce6cb28a80206736554540103992a2a2a0081d494d5150040ea2a6a8a80207625254540103b0a92a2a0081cc9d15150040e66c8a8a802073151d05401032731ac5aa6614b9cb5495330c5ea8b14a99864e6398a54cc32739cc52a661935ce6295330c9cc6b14a99852e72d9154cc237390c2aa6611b5c8615533087eecaa0a99852d7299054cc2a6b94c62a6614b9cb54d0f30c5ea8b16879862c5458b43cc296b94a921e618b9526290f30c5aa9314879854e7295243cc2c6b94a921e61935966290f30c9acab14879864f7558a43cc3263aac521e61939516290f30c98a8b1487986c96258243cc297396a8a1e610f9d85450f3099ae5b2a879854e72d9543cc2c7396c8a1e61639cb5450f30b32e1aa2879854e7295143cc22f3b0a8a1e61279d85450f30a3cec2a2879861e7615143cc28f390a8a1e61475c45450f30e32e02a2879861c54d8943cc266b90c0a1e61355c46050f30a5ae52a0879843f7655043cc34ca1ac021e614b9d35294b30c5ac9a94a59861e7399252cc30eb9cc9296618b1c96494b308baed21ca59861e6490e52cc2a6b948729661879914394b3087ce830aa59843d7418552cc237bb2a4296614b9cb54d0b30c3ea8b1e859861c5458f42cc30eb2c87a16614b5d252d0b30c9cc7296859864e6354b42cc296b94a921661879526390b30c3aa931c859861e6550e42cc297396a8a16610f9d85450b30a5ae52a0859843f7655042cc24fbb286216614b5d25210b30e1a87290859852f7550842cc296baa84216618b9954210b30d1cc6a10859852d7494b32cc317324a5996618b99152ccb30c3eeab26659861c7559332cc22ebb4a9996618759254ccb30a9ce52a6659861d6415332cc28f3a4a5996618759252ccb30b1ae9296659854d7590b32cc3862a28599661a659160ccb3093ae9b2a659851e74d9532cc22f3b4a899661539ca544cb308bcec2a2659861d6415132cc2c73a6c499661639d3524cb30b92e1a92659851e7494932cc2673b0a499661539d7424cb30e18a9a1265984ce7610932cc346b208499661c3950424cb3093ae830265984d57118132cc296ba4a419661b24c9600cb30a9ae521aa39861c6450d51cc28eba664a8e619318932547308eeeca88a39846e72d9741cc236b96cba0e611b9ca65d07308dae532e839852d7295341cc266b94c7a0e614b5ca5450730c38caa1a839846e72d9441cc236b96ca20e610f9d265c873087ae932e439852d7494b21cc296b94a9a0661335ca63d0330a5ae52a2819861d5418d40cc2b8b8cc1aa4611b9c86
  | 20 => 0x572d4e51102b3390a728881595c85394440aace7a94a22055573d4a51103a329ca528881d154e5294440e8ca6a94a2207455354a51102ab398a528881555cc5294440aace6324a2205557319251102b3390c928881595c86494440a6ce831ca2205667218e51102b2b90c7288815c9c06394440acce5a1ca22056572d0e51102b33948728881595ca4394440e2a8621ca2205367418a51102ab398c528881555cc6294440ae4e0314a22055673d0a51102aab9e8528881559ce4294440aaae7214a2207254210a511029b3a665288814d5d33294440a6ce9194a220535748ca51103a29906528881559cc6094440aaae6304a2205667218251102b2b90c1288811b9c863544408dae431aa22045e73189511022eb98c4a88811d9db5354440acce5a9aa22056572d4d511023b3b0a6a8881599c85354440acae429aa22047676d4951102ab39ea4a8881555cf5254440e8ca7292a2207455394951103a329aa4a8881d154d52544408ecec292a2205567314951102aab98a4a88814d1d16354440a6ce831aa2205667218d51102b2b90c6a88815c9c06354440acce5a1aa22056572d0d51102b938686a88815c5c34354440acce521aa2205657290d511038aa1886a88815c9c04354440ae2e021aa22053474589511029b3a0c4a8881559cc6254440aaae6312a2205727018951102ab39e84a8881555cf4254440ae4e1a12a22057170d0951102ab39c84a8881555ce4254440e4a84212a2205727010951102b8b8084a88814d9d33254440a6ae9992a220536748c9511029aba464a8881d14c83254440aace6302a2205557318151102b3390c0a8881595c86054440aace6202a2205557310151102b339080a8881595c840544408baed298a22045f7654c511032729cc4288819354e6214440c9ca6b10a22064d535885110236bb4a4288819398e5214440c9ac7290a22046f76548511032731aa4288819358d5214440caca7308a220655539845110333294c2288819954a61144408eeeca88a22065663544511032ab1aa228881999895114440ccac4a88a220671515834110236bacc4208819394e62104408deeab10822064e535884110326a9ac4208811b5da5210440c9cc7290822046f76548411032731aa4208819358d5210440cb4a73008220659539804110335294c0208819a54a6010440cb4a6b008220659535804110335292c0208819a5496010440ce4a2b00822070d5394b401038729aa5a0081c354d52d0040e2aa728e802072552947401038b29aa3a0081c554d51d0040e4ca4a8e802072552547401021ebb4a9200811e5da5490040e92a6a9480207525354640103a8a9aa320081d89495190040ec2a4a8c802061f6594d401030fb2aa6a00818bd965250040e1aa7292802062f65549401038729aa4a0081c354d5250040c6ec
  | 21 => 0x2ad380c329881539c86094c40a9ae4304a6205567118253102aab88c1298811b9c86154c408dae430aa62054e7299153102a6b94c8a9881479d36254c40a3ce9312a62064d62189531028e3a2c2a9881479d06154c40a9ce430aa62054d7218553102ad380c2a9881539c86054c40a9ae4302a6205567118153102aab88c0a988117dd95314c40c9aa7310a62064d53588531032aa9cc2298819554d6114c408daeb316862064e5398b4310326a9cc5a18811bdd562d0c40c5ca8b16862064e5358b4310326a9ac5a18819654d60d0c40c9aa7314862064d5358a431032d29ac0218819594e61d4840caaa730ea42065653587521032aa9ac3a9081539cf5294840a9ae7a94a42056671d4a52102b2b8ea529081599c75394840acae3a9ca4205667114e52102b2b88a7290814b9d36394840a5ce931ca42064d6318e5210236bb687290811b9da4394840e1a8621ca42052e7418652102a7398c329081535cc6194840ad4e030ca42054e7318252102a6b98c129081599c46094840acae2304a42045e73185521022eb98c2a90811b9db5354840acce3a9aa42056571d4d52102373b0a6a9081599c45354840acae229aa42054e7399152102a6b9cc8a90814b9d36354840a5ce931aa42064d6318d52102373b686a90811b5da4354840e1a8621aa42056a7010d52102b4b8086a90814b1d16154840a5ce830aa42054e7318552102a6b98c2a90815a9c06154840a9ce6302a42054d7318152102b3388c0a9081595c46054840a9ce6202a42054d73101521022ebb4a62908117dd95314840c9ca7310a42064d539885210237bb2a4290819398d5214840c9ac6a90a42065653984521032aa9cc2290819954a6114840caca6b08a420655535845210332a92c229081175d663d08408beeab1e842061e5458f421022ebb4a7a108117dd953d0840c9cc7296842064d6394b421032731aa5a10819358d52d0840cd2a4b06842045f7694e421022ebb2a7210819398d5290840c9ac6a94842070e535084210386a9a84210819654e6010840cb2a6b00842066a52580421023b38ccb990811d5c665cc840c3ac929e642061e6454f321030eb22a7990818b99252cc840c5ac9296642062e6454b3210316b22a5990811d9c6658c8408eae332c642061e6494e321030eb24a71908187991538c840c3ac8a9c642062d6494a3210317322a5190818b591528c8408ece232a64204757119532102a6392a699081531cd524c8408ece332864204757199432102a6b94a619081535ce520c840a9eea990642054d754c83210327b2a641908193595320c840c9ca7316a22064d5398b511032729ac5a88819354d62d4440c9cc7296a22064d6394b511032731aa5a88819358d52d4440aace7a8ca22055573d4651102b3396a328881595cb5194440acce5a9ca22056
  | 22 => 0x681639cf5250b40b52e1a9285a051e7394942d02573b0a4a1681275cc6050b4096ae230285a054d7394842d0354a12c0216818759743ccb40c5cc929665a054d7394b32d0317322a5996818b99542ccb40c3cc929c65a054d7294e32d030f322a71968187995438cb40c5acba1465a054d7294c32d024fbb28619681535ce520cb40e1a8729065a04af7650832d038729a841968153dd5320cb40a9aea99065a064e654c832d02c6ba26419681a3991320cb40a5ae5a1aa3a061c6350d51d028eb9e84a8e818b18942547408eeeca88a3a046e721855390236b90c2a9c8117dd95314e40c9aa6b10a72065553584539032729ac521c819354d6290e409e2e2302872045e73185529022eb98c2a94811bdd95214a40c9ac6a90a520665525845290326b1ca5214819358d5290a409e2e2302852061d6494f329030eb22a7994818b592528ca40c5ac8a94652047671195329023ab88ca99481531c9534ca40a98e6a92652064f654c83290326b2a6419481b24c9600ca408dce431aa32046d7218d519022f398c4a8c81175cc62546408eeeca88a320655635445190332b12a228c8193d4d6294d408beeca98a6a062e6558b43503163aac5a1a818b14d62d0d40c9ea6b1486a064c5358a4350278b88c0a1a81479d76350d40b1ce5b1a86a051e7614d435030f3b0a6a1a81479c85350d40a3ae229a86a061c53d894350256b90c0a1a812d5c46050d40b62e230286a064d63d4a5250237bb2a4292814b5cb431494087eeca18a4a061e6558f425030e3aac7a12818758c53d0940c3ac629684a064d63d4a4250326b18a5212813c5c4605094087cec29a84a052e75d8942502c739ec4a12814b9d85250940c5cec29284a052e731494250317b18a4a12814b5c4525094093ae630284a04b57118142502d8b88c0a12818759353cc940c3ac829e64a062e6550b325038629a859928187995438c940c5ac9a9464a062d6414a3250386a18a519281275ce644c94095ae532264a04b87059132502a7396a69928187590534c940a9ce7a9264a062d641493250387a18a499281c314f424c9408ece232864a047571194325024fbb2861928187195430c94095eeca1064a062c65508325032732a641928193195320c940b1ae899064a068e644c8325034ca1ac019281aa509600c940d9264b0064a046e7298f5150236b94c7a8a814b5cb43d45408bce7316a2a045d7398b515028eb9e85a8a811ddd95114540c9cc7310a2a064d63988515032731ac428a819358d6214540a3ae628e82a052d72147415029d3a8c1a0a81275cc605054095ae430282a05a972d0f40502ccb9e85a0281ac58741d0140a9ce5a9ca62054d72d4e53102ab38ea729881555c75394c40a3ce9b14a62051e7498a5310326b10c529881479d06194c40a9ce430ca62054d721865310
  | 23 => 0x4c832c5ae9b2a641946f75591320ca373b4a8990658bd92544c8328dcec2a2641962d64151320cab2b88a8990655a5c0544c83295ae9b1a641952e7494d320cac73a4a699065635d2534c83299ceda1a641970c54d0d320caa6bac8699065a3592434c832a9eeaa1a641968f6450d320cb862a28699065339d8434c832d1ac821a641970e5410d320cac73a6ca99065635d3654c832c9aebb2a641968e74d95320ca66ba6ca99065a35d3654c83291ae9b2a641964e76d95320caa73a6ca99065c39d3654c832a1ce9b2a641970d74d95320caa6b86ca99065935d7644c832a9aeb322641954f75591320ca67baac89906593dd5644c832d1ee8b2264194ce76191320cb46b20c899065339db544c832d1ac9aa264194ce76951320cb47b24a899065539da544c832c9ced2a2641944e76951320caa63b4a899065539d2544c832c9ec92a2641970f64951320cb26b24a899065c3192544c832a9ae12a264194ce76551320ca66bb2a899065a3d91544c83299cec2a2641968d64151320cb86aa0a899065729c0544c832b92e02a2641954e76151320cb273b0a899065539d0544c832e1ce82a2641964f64151320cb87320a89906593590544c832e1ac82a2641960d64151320cba5380a899065535c0544c832e92e02a2641954970151320caa6bacc09906553dd5604c832b1ce8302641958d74181320cae3388c099065715c4604c83299eec996a01947671191500ca3ab88c8a8065535ca4354032c38c8a1aa01954d73909500cb86a1c84a80658b1914254032e1c86a12a01951d74cc9500ca96ba464a806593dd93254032c98ec992a01954f744c9500caa6ba264a8065931913254032e96e0992a019748704c9500cb26996c2a80650f9d0615403287ae830aa0194cf764c8500cb473226428065a35913214032d8a65308a0196c532584500ca3dbb2a0280658e5915014032ce2c2a80a01954e72d4e53d0327a9ac529e818b9d26294f40c5ae9314a7a046e7218553d0236b90c2a9e8117dd95314f40a9ae529e87a064e5398b43d0326a9cc5a1e814b9ca53d0f40b1ae529e87a062f7558b43d03163aac5a1e818b94d62d0f40d52c4b0687a04ad72d9543d0297396caa1e81639cb6350f40b1ce5a9a87a059970d4d43d0297394a6a1e81279d85350f4095ae430287a04b57118143d02a6b94a621e81a650d6010f40a9ce7a94a5a064d63d4a52d030f3a4c729681875d26394b4087aeda1ca5a061e63d0e52d0296b9687296818798d4394b408bce630aa5a045d7318552d0237bb2a429681535ce52d0b40c9cc729685a064e6354b42d030fbaac7a1681871d563d0b4087aed29e85a061d6394f42d0297394a7a1681479ce52d0b40c3ac729685a058d7394b42d034cb1ac1a1681275cf6550b40a3ce7b2a85a052e7294d42d02c739ec4a1
  | 24 => 0x2a4849961e5498e424cb0eaa4c72126587997439093287cec2a2849951d73950424ca96b94a8212650fdd95410932c3ccba18849962e65508424cb26b9cca21265635ce54109328deecaa084994af76550424cb1732aa82126563dcd5410932a5eecaa0849962f76550424ca97b9aa821265c3dcd5410932e1aa9b18849962d5498c424caa73a8c621265939946310932e1aa831884995c57118c424cae4b80c6212658b9974310932a9ceba18849964e65d0c424cb873ae8621265c35d74310932d1ccba18849970e65d0c424ca57bb286212654b5d54310932c5ccaa18849964e6510c424cb473208621265c35504310932c5aa8b0884994cc73584424cb47a1ac2212658b5516010932998e6b00849968f43580424cb0f3acc919265a31ca648c932c3cc9aa4649961e64552324cb47326a519265a3993428c932d1cc8214649970d5410a324ca3dbb2a0282659c5855014132c6cc9308a09963564984504cb1b322c2282658d5916114132c9cc7314a81947671181540ca3ab88c0aa0650fdd95415032c72a8b00a81967261980540cb1d322c02a0659698d6015032cd4c4b00a81967261580540cb38b0ac02a065875ce6494832c58e4b24a41951e73d53420ca97396a9a10654d5c454d0832a72e02a6841961f5458f420cb0e2a2c7a10654b5d252d0832c3ca931c841961d5498e420cab2b88a9210655a5c05490832c9acb31c841946f7558e420cb26b2ac72106533dd56390832c9eeab1c841964e5458e420cb262a2c7210651b5da5390832a5ce929c841964d6394e420ca96bae8721065935964390832a3ce7aa2841952e72d51420ca1f3b0a8a10654d5c45450832a72e02a2841961f6590d420cb2739ecaa1065639cf54508328dcec2a2841956571151420cab4b80a8a10652b9d85450832c5eca2a284195a571151420cad4b80a8a10654b9d85450832c5cec2a2841952e73151420cb87398a8a1065c99c45450832a5ae22a2841972571151420ca92b88a8a1065ca9c05450832a5ae02a2841972970151420ca94b80a8a10658b1536350832e18a931a841954f7558d420cb27b2ac6a1065c31516350832a5ce929a841962f6590d420caa6bac86a106593d964350832e1ceb21a841970d7590d420cb47b2c86a1065c3d964350832c9ecaa1a841970c5450d420ca1fbb2a82106517dd5631083293eeca18841951f7550c420cb46a1cc4210654b5d25210832e1a87290841952f75508420cb1632a8421065a398d4210832c5eeab24641968d73592320ca36bb4a9190658b592548c832c5ac82a4641956571152320cab4b80a9190651b5da538c832a5ce929c641962d6494e320cb46b24a719065535d6438c832d1ac921c641968d6450e320cb862a287190650f9d3654c83287ae9b2a64194ad74d95320ca973a6ca990658b9d365
  | 25 => 0x731855010a57bb28428085a398d4214042d1ac6a10a0216a5429845010b52a12c2280851edd95014042cb2c6a80a021671615405010b26b1cc5aa465a358c6295232b4ae2314a9195a97018a548cb0eb1cc52a4654d9c46295232a6ae2314a91953a7018a548ca9cb80c52a465475cf6195232c3ac6b0ca91951d73186548ca97390c32a4654e9c06195232a72e030ca91951d73d82548cb0eb1ac12a465475cc6095232a5ce4304a91953671182548ca9ab88c12a4651e9c061552328f2e030aa91947671181548ca3ab88c0aa465a358c6255232c5ec6312a91952d71189548ca96b80c4aa4654b9ca6155232a58e4b0aa91951d73185548ca97390c2aa4654e9c06155232a72e030aa91952e72981548ca96392c0aa465475cc6055232a5ce4302a91953671181548ca9ab88c0aa4650fdd95415232c9ac7310a91962d5498b438cb172a2c5a1c658b55162d0e32c5ca8b14871962d5458a438cb0eb2aa921c65935966290e32e1ca9314871961e5458a438cb872a2c521c65939516290e32d1ca8b14871960e5458a438cb46aa2c521c65931516290e32c5aa9b12871962d54189438ca2f3b4a8a1c65479da5450e32c3ced2a2871951d71951438ca8eb84a8a1c65879536250e32c3ca931e851961d5498f428cb0eaa2c7a14658b59654d0a32c5aa931e851970d5498f428cb27aa4c7a1465a395263d0a32c9aa931e851968d5498f428cb06aa4c7a14659359563d0a32e1aa8b1e851962d54587428cb16aa2c1a1465879526390a32c3aa931c851961e5458e428cb0f2a4c621465879516310a3293eeca18851962d65950428ca37bb2a8214654bdd95410a32c5eecaa0851962d5498c428ca66bb486214652bdd94310a3299eeca18851958f7650c428cb47bb2862146563dd54310a32d1acaa18851962d54584428cb46a1ac2214658b5516010a32d1a86b00851943f76553328cb16b2cc9994658b5d664cca32c5acab26651962e64d53328ca57bb4a9994658b59654cca328deecaa6651962e64553328ca57bb2a9994658b59554cca32a5eecaa6651962f76553328ca17bb2a9994654b5d954cca32c58ecaa6651954d7290d518ca8eba664a8c650f9d0605463287ae8302a31943d76950518ca1fbb2a828c651ddd95114632c74a9300a31963954980518cb1d2a2c028c658e5516014632ce2a2b00a31954d7290d508ca8eba664a84650f9d0615423287ae830aa11943d76950508ca1fbb2a8284658d9526114232c6aa9308a11963654584508cb1aaa2c2284651edd95014232ce2c2a80a11964d6358b544ca3b388c0aa2651d5c4605513287eecaa0a89961f5458f424cb0e2a2c7a1265339d663d0932c9ceb31e849964f5498f424cb26aa4c7a1265335c663d093299ae131e849964e6558f424cb2732e87a1265475ce5490932a5ae5
  | 26 => 0x2b29cc2284859554e6114242caca6b08a121655535845090a3dbb2a0284859c58550142428beeca98a6a164f5358a4350a573acc521a858b9d66290d4295ae331486a14ad7098a4350b463a4c7a12859398f53d0942d18e531c84a161e63d4e4250ac739ea521285a398f52909428eeeca88a2a1671515805150b2d31cc028a859658e6014542cb4c6b00a2a1659635805150a3dbb2a0282859c5855014142cacc7308a0a1655639845050b2b31ac2282859558d61141428f4e030aa621479701855310a3b388c0a98851d5c46054c428beeca98a621655535845310b2ca9ac0298859394e62d0c4295eeab16862162f7558b4310b17396caa1885639cb5350c4293cec29a862161f6514d4310acab88a6a1885665c05350c42a5eeab12862162f655894310b0fbaac7a1085a35c963d084287aed29e842161d6394f4210a1ebb4a9210851b5da5490842b1ae72a4842168d7458e4210b472a2c7210859358e5390842d1ac6a1c842145e73d954210a2eb9ecaa1085275cf6550842a3ce7b2a842161e73d954210b0eb9ecaa108587d8e535084299ae7b2a842154e73d954210b2739ecaa1085935cf6550842b1ce7b22842158d73d914210ac739ca8a1085635ce5450842c9ec729a842152f7550d4210b47b1a86a10852b9d84350842e1ca621a842158e73d954210ac6b9ecaa10858b5d76550842d1ce7b2a84214ad73d954210b46b9ecaa1085235cf6550842c5cedb2a842152e73d954210b8739ecaa1085439cf6550842e1ae7b2a842152d71d954210a96b86caa10858b5d76350842a5aeb31a842152f7558d4210b46b18c6a10852b9db535084295ced29a842168f6394d4210a973b4a6a10858b9da5350842a58ed29a842162f6394d4210b87b1ca6a1085c318e5350842a5ae329a842152d7094d4210a573b2a6a1085a3d8d535084295cec29a842170d5314d4210ad3388a6a1085695c45350842b54e029a84215a97014d4210a96bacc2a10854bdd56150842b1ce630a842158d731854210ad5380c2a10856a5c06150842a5aeb302842152f755814210ac7398c0a1085635cc6050842b4ce230284215a5711814210a57bb285a88851e9c063544428f2e031aa22152d72d0d5110b0e31a86a8885475cf4254442a9ae7212a22162f765095110b163b284a88854bdcd4254442c58c6a12a221727715095110b9238a84a88858b50b60544428bce6302a22145d731815110a57bb28428885a398d4214442d1ac6a10a221477765445110b2ab1aa228885aa50a6014442d5284b00a221671515805110a57bb285a80851d9c463540428eae231aa02152d72d0d5010b0e31a86a8085475cf4254042a9ae7212a02162f765095010b163b284a80854bdcd4254042c58c6a12a02172b705095010b9438284a80858b50b61540428bce630aa02145d
  | 27 => 0xc00200080020004010000000000040030004000001c002000001000080010008006000000100000080000006000000200000010004001001c00900100020004000000c000001400000180020004009000000100000000000002000800200080080014002000000000000050000007000c000000000000040020010024b2ae2324a7a15997019253d0b46322c529e85559c46494f42aaae2324a7a155a7019253d0aacb80c929e85535cb6194f42a3ce830ca7a154d7218653d0aad380c329e85565c06194f42a9ae5b04a7a151e7418253d0aa6b90c129e85559c46094f42aaae2304a7a147a7018553d0a3cb80c2a9e851d9c46054f428eae2302a7a168c6458953d0a8f3a4c2a9e85471d16154f42a3ce830aa7a154d7218553d0aad380c2a9e85565c06154f42a3ce9302a7a151c7458153d0a8f3a0c0a9e85535c86054f42aace2302a7a15557118153d0a2fbb2a629e859394d62d0f428bce6302a3a145d7318151d0a2ebb4a628e8517dd953147428eeeca88a3a165a5398051d0b2ca9cc028e859694d6014742cb2a6b00a3a16715158051d0a2f398c2a8685175cc61543428baed298a1a145f7654c50d0b2b29cc2286859554e6114342caca6b08a1a16555358450d0a3dbb2a0286859c5855014342d1ac8314a7215c57118a5390ae4b80c529c85559c46294e42aaae2314a72155a7018a5390aacb80c529c85475d36194e42a3ae830ca72154e721865390aad380c329c85565c06194e42a3ae9b04a72151d741825390aa7390c129c85559c46094e42aaae2304a72147a701855390a3cb80c2a9c851d9c46054e428eae2302a72168d641895390aa6b88c4a9c85535c06254e42a9ce530aa72154c725855390a8eba0c2a9c85539c86154e42ab4e030aa721559701855390aa7394c0a9c85531c96054e42a3ae8302a72154e721815390aab388c0a9c85555c46054e428beeca98a72164e5358b4390b0eb2aa7a1c858b59662d0e42e1ca7316872161e5358b4390b8729ac5a1c858b94d62d0e42d1ca6b16872160e5358b4390b46a9ac5a1c859394d6290e42c3acb31e852161d6558f4290b0fbaac7a14858758e53d0a4293aed29e852161d6594f4290a8fbb4a7a1485475da53d0a42c3aed29e852149d7654f4290b0eb2aa7a14859359663d0a42c9aeb31e852164d6558f4290a67bb4a7a14859359653d0a42c9cc6a9e85214cf7654f4290b26b2aa7a148553dd953d0a42c9eeca9e852154d7654f4290b26a9ac3a14859354d60d0a42a5ae5a1aa32151d73d095190a2f398c0a8c85175cc60546428baed298a32145f7654c5190a3bbb2a228c859694e6014642cb2a7300a32165a535805190b2ca9ac028c859c5456014642a5ae5a1aa12151d73d095090a2f398c2a8485175cc61542428baed298a12145f7654c5090b
  | 28 => 0xc0010018003000000700040000024001000000100040000004002001000100300000000000000800300000000014004000c000000c000000000700340000000000000400000040010010005001c0060004002001000600000010000000000001100080050000002000c004000800000240050004001000400100400040014000000000000080070004000000c0010000001000000d0008000001c0020000000000000d000000000040000008006000c01200000030004017000000c000000100100040010012001c000000400d0008005000000100180040004000000c008000000000000000024001000000000100050000001001000900000090000001001400200180320000013000c00200000000014009000400200000000000000001400000440030014005005c00100000000004000000400000000000004000002000200000010038000000400100040010014009000400000040000014002000000200200000004000001400000000020004000001c0010008001000c00000000010000002001c00c000400000000040004003000000000040010008001000000000040010004000001000200000010000006004c00100000010010006000800e0000003001c0010000000000c001000c0010004000000000d000000400440140044008000400100040070038001003400000380000004007002800c0000001000400000080020000003000000500080010004009000c0010000000001c0010024000000c000000000500000000010008000400200040000000002001000300140030030003001000d0018000000c00200240000004003000000400140000004000000400300180060094001005c00000200000008001000400000100000010006000001100100040008000000c001002c00d000400000000010000004001c0030004000000800800500000000001000000400000070000000000000000040000000000000800900040020004002002401000040000014005000400d00100010000005000000c00100020004000006000600080050000006000400000000050000001000002300080010028000000000300040000000000001c00200740020000002000000200080070000000000c0020004000000c007000000300000000020001000400600000000000000000000c0000000000000d0008001000801f000c0010000001000000000040030008000000c00300000060000004000000300440050000009000400000000000008002000c005004c00200200040008001000c0010064002002400400000030028002000000700000050014001000000800b00000008006000000800000000004004000c003000400100240000000000001400500080000000004002400000040000000002000400d001400100040060010002000c002
  | 29 => 0x400240040028002001400400280120008001001400200000000008000003800000000030004002000000600080050014001000c0000000000007800000040030020005000c00000080000004000000c003001c00c000c0020004013000000c001000000140000008002000800000280090004000001800d000c000000400100000010004009001000500040070018005000800500000130000002000800500040000004002000c0000000005001800000040000000000002c00200040000004004001c0020000000000000000000000000009000000600040030018001000000100500120008007000400000000060004007000002a000800d000400700000020014010000c0020020000002000000000000000000001000f0000003005c00000140050000009000c00000100000000001000800c005000400000020004006000000e0000000002c003000400700100070008000000400500000000004000001c000002400000100000004002001000000300010014004000000000000010000002000c0020004000000c000000400000000120008000002c00500040000000001000800b0004001002c0030014005000000900000020000008000800000200010004000001c0100000002000000100000030018001001c00000080010008000000400a00000050000001000400000140080000001000800c0000003002400000040060008010000000800000000008001000c00100080020034001000000100040000000000001c0000000001000400000000000008000001c00800800000000002000400900080010000002000400b000c00200080030024000000400100000000018000002c00100000000008000002400000080000004000000400300000060008002000000000000000000003002400000580050004000001000200000000010004003000c00000000000013001800c000000200040000000000003400000040080008002000400100040020004000000400d0000000000800600180070000000000000a003400100100030010003000000100000080000006000000700240000000000000c0000000000001400000000000020000002400000000060000000000000200180030000001000000000040040028000002400300000000024001003400000080010018003000c00300000000014000001c0080004000000c001001c006001c00000040000000002000000100080010000002002c0000004001000000800140090004001000800000040010000000002400200000020008001000000000000000000000000000a000000200000010000006000000000000070010002000c0000000005001800000100000000000000001900000010000002000000200040010000001000c002000c0020020002002000100040010014002005
  | 30 => 0x3c016000000200080000014010000000000140010028006000c0010004000000400300000000098002001c000000000000140030000009003000200500020000004000c00200040010000010000000700000020000007001c000000c0000014004000c00400100000010004000001100000010004015000800000040020008000000400100040000014007000c0010010014000000000080000000005000400600040060004000000000100040020000003000000100300020014002000800500040010000000002400000000040004000000000b0010007000c0040038000001000c0000002001c00000000010010003000000300040000004000000000100300050010000004400000200030000004000c00000280040008002002c00000080010014005006800d00080120000005000000700040010004000003800000040000008000000000d000000200180020008001000c00c0008003001c005000c0000018000002c002001c005000000400200050008000000000500000030000002000000000000000000001001801800180000008000000800a000800800000220000001001c001000000000140030000007001c0030000016000800000080030068002000400100100000008014001400000000050020001004c00200240060000000000800000000030000000000000000000000008001000400200000010010002000000200080080000002001c0020048000002800000000000000000000000300040050000000001000500000000000000000000400000030014000000000000040030004002000800300000000008003000400000000000024001001c0020058000001400500040030004000000800000000020000000000000400000000024004000000200040020000000000c004000000000040000000000000c00000000010014001001c0020000002001800000240030000002000800300140030000002000000000180060000002000000100080030018002002c0040004003000000000180070050000001000c0000003000000000000000000000000c002000c0000008000000800700000140000002000c00000100010014000000000000000010014003000800800280060078000001c001000000400040020000000001c0000000007000c004000800a000400b0000001000400600040010000003000800200140000058001002400000000030000012001000200140010004007000400100000000010007003400000080000000000000c0150000000002800000000010040002000000000040000014000000000000180000000000000000100000020000000000400000000180004009001000b000800100040010020002004400d000c00300300040008001000000000040040000002000000000080020014000000800
  | 31 => 0x5600012fe1850000516c000000072c00018377c78000906000036240003989cfa000000065b45a67c6a27c664831000008b282ec0004da80002470b6a1d1da665ad81ce0aa0a7a00021e243e0106000194c67300000001bd0000216a87412e027085cb000216430fa06f02a4d302c81c5065007c479e009739a063866fceae4d60abe4e820be49d400000000000001a6d00000007f3220a0000978582800000000007940000791c2f07af4000000000060c073620980ee000000021900000000000078a34a10a8cf47a745268b798c26898000000042600000000650c9656f93a86ee0000106800077ea1ba0001c9736922c24559d0c84b96120b2c00000023fc00005f200000001c60c407bd13105a920b300016e86af83fa0000000000119286f80001c9800000000005d200002f8000052e11dc000017f000000000006f40000000098150c0df80000000000404a0f4795c0005139f555b70ef20001a143d28000221000061e01320000f0000000000000000000000036600000000dcb490962c4cb18e66ae0000748591211d000000012236af22fc3c98c4800013ae032088b0820c1c20c000067280001f6c000000183e0000522355a2bc5db4000039000000000001764000000000038480002ae13826475d9800002140000000001800058b8000000113c000209d00018f21a71860841c0000000dd00000000000142006d40000000e00000000000017220179276000000037283a66fd06dc0001fa490e00000210bc44731d8057200004e218b165e800000000004f21f3a3665adc0000fc400000005bec3708ac800000001a40a0000000009ca5095fd03bc0000000012b3bf000000012d87fd00008b20f36000000000017ec2f423946698000000023a02e20087a10d0e00005f90c284b821810c3809c0002de07c107b8bc50000000856000000000004d017c47ddd2c58db15fe81d11da79501603c79f868de800044b80000001f900001fbb00019fe000000000000001380000245222227480000000000000000088f0000000000050780004750000061532a887000081b52781868fe75ea9c6221419082b7006d00a8a1e846010e664cf148c805a000018ea19a18ae04840390000b8a4328000000114c000000081a400000000004a580001f996e20001f5e0000000000000000000008948b540000000000000000019b50000c0800000005fe815400000000921da20001ffb01541a10c393061a980000a281b6000009e1538000030000033a86265ef00004471af034ca4440a6000034b8000110244a3911a386da913000019141d21e517e6000030a03da0000000000038819099060ac400090410e760600000000000000127e82712b51ce00007264ef42ee105670e0e0223e0b086d400040004005002800100000050018000000400600
  | 32 => 0x7a6000000000007f040c30c9c68200018a25329f316c4000063d05780745df47c919a2241197c8258d907ad0000000047e000000008298e2000000000011fe6b7800030e80006aa9c4088007ad31080007b49d207468a5640990a05e3823c2eb985e00000002631854053000036a009816480003f2c0000001c30083800047204dc00000000000ba46eddea80000000000000000021ac00000005d7800088511384754934000000014f0374000000054387680000bb51bc80006fc93be000049480e225659c800000011d872a156c00004564ae844b185c488313958e27f216682ca2a219793c6000175c2c9a3465aa114483b14802529f92465069e0001b8e47918d0000063443140008a9e33a00000000799c1671492729139cd613480005bc00ce000019873800000319122000034800001902c49f637dbc04220f80005784000697c00000000000ec800003600000001e7a00023c60001cea5668000000133c4bd23ec30e205e65500000000000000000000020a20001b6c56c0000000005800000005f188d000018dc0001b1a000000000010c0000162a629000033908064a780001f5c0000000c8a19b4e26000000000000000d5e2d03c4800000000002041ed432300000ea80000000000000000033f09d48ec21240d8195640f816847a848c234837f1482184000000000000000001c8a00022c4083404a47397367ce5cc60000c567e0da9a00000008fd986c1b2015854a8000000087575c800037c967840d13f690911c2000000049b8000000165a00000000000000000116d8f900007e12171000142d13b000043901b7519800066b14e44608000000024c18e908205b40000e60000824e2b02d0c000000000011e88086cc12e4000171a000189226b8000456c00000009680000000652089823d92843a112623f91cc00a920465bb209844980fe28a44080d7000000011648531db71c4800000020070000000391800016c10df00019b600003ab0000b71000000056f218b00017e815800001548000000203200008560000000000167666cc6f50001fe884e80000b780007f0800000000000000bfa00000000000000000056a00000000000000000000014142ca4318bda8c394127a5800053c8bb9000000079f9e9e0cb8000427000000004be00004e25c60a68000022938418ec0089d8a4375826000000009a00005fd0dd20000000000000074a949900001a30000000000076e00fe2d613b818d00000001b400005548000512800032a0e9600004540000000151000082b00007cf931a089c745440800000019a800000000c3000002480000001de300010c41ea0000000148e0000b3c7fe0000857c7770001de0000078800017de000058600000000001bc27cdc000000240e000145800022e30855a105508ca33e800000001e
  | 33 => 0x46200015366bc8b8d00000000000000105400000000007f4800000000002501f9183eddc450e89e20000000747c0004b7c11f7cfc97a56b0a864c501ad6dd14905c9202478b07588d89ec006e00ba3d612382e459972058ab03448e72846946f454c6048014a004cd139e8f2114e79c80187e807de00e19ce2bd9e5a00000008a4800000021806e69208000209b0bd1fa77e50f7200009865000000000093900000000cc57a6000000029a800000015cc094a3e00a396fd6a610100df11ae43b000000000dd327086a6d4800000016926abc0764d09e9576d9e6e70500000f080002d88338149000000007c2000145349400006a4030300003de08f9b0400019381df007a06709cc0a5026573384340e81bb05c296d51bad93d0001cee82b800000020000001a52224a0d28a10d6c0d040001d5d2f2000022442ad20010b800000000008bb224a6a7000000015c0000000046a835a0001c000dd849e0000000000068f00012985850f320000b362e40e862608000858800000000008d7973281f13ce835800088e000040780001c7c0000001f9f000015017340a65ff08462fd80000e8c00000000004d80ad205911f21a89a7c8aaa14400020c200000001a100008950000627887600014500000000000000068a0f2a7be8e9a340073431d000000000000000c607b400005a605f865a0000000000016aa2a400012da0d280002b89ae452707004d9800071f800000014f86de13b0000000032f128000004fc59512d6382993a36700488749fb4143c00038247703ee04d67d500000000c22000000062d10034db000015f800037b8a8e0001630105000000000008f2d8d207f159677b99426bfa3c028080006860165564825170f87dd2150d20170201f7eaa22a5e6139248281e97508e4e0001d54000060e6074000000084a2bf8000646000000000004e29b900071620000000000000008df800020b000000012292a600000000000509c00079a000000000005d3075c00000001eb0000000000000000000000878000177e7e2cd1e00023e8000185a14c923a5db193e2ea84b62df038c491025860c4000360000064980000000ca200000000000000000068e000000000000002719a4200007ba0f1800047a40005568000052000000000000000000908000000000002710000000096e0b99f7628d8000000229c6fc22ac00000003160f9800023a200000004f28000000000000000008a393c20000322104e2588f38000841896c16fa1f27808000106000053192ee000000000000000000000000000034d000009c17461ff00264b3051000000005bfdfea28906808aa0000000049000000002a02414000062a8e9000000008f02be10f43f7502d0001fac077854d850000000000008c980001cbc0003a41ece7fb0000000000000012b041a94260
  | 34 => 0x45f0000076c00000017a400000000000000000000000000007c300008f4000000000000001024000024e0bb00000000000000036e2990000000000066500006aac00000000000a74caa4bd8bee87005e02f38000000000000000003e5908868f14707928ed20fd851a4de226c21f5d242dd87528ed88850c2073e41d89847ba82ed61f82a262685c46b29b5a7ec00008e814cc0000cac0000000554000000021702ef000000018946640a3a000109e000000017bd032000234806f0000000000021f800018d9dea21d055a4de800076ba12a1ba102e3f282d047f16fe60112ea0000000000056c00019f800000006d793ea0000ada54c000069c800036580000000eb400000000cb01be0001be80000000000000039a800081c176a61d800049a01428d983c100009006bf1ed81cc0bdc00006ea69315740000c06000000000000000000000000000081500000000585132a21e0f380000af9771798c000095813871e03211b5961833995e22d6004600000000a58e420001d080d0c0000429150545800000000003ef238074c1d6664ad7c0147043e45188a435aa01a5b9013634d8a5a3f3a1bc7b68bf803983860f89c9811200006900000862125402180000000000000000015ca0c670186c600000000000fde037d59c62e899e820c00000000000001904000000019f00000000000000042c000000000006ac0fd15567a49b4e712060565bc000227800006c568c0d40ef84f8a35c000238c4ee0000000123c0000000000192200017866c60970698d79c00018d66c880002d9064c3e7800000000000e5046e3eb157c5690c7a00010b0303000000000000000d407c5938e6fe1c70539963264f190c4ff19165fc8b0c187400000023b2000000000000003381fed00000000265d6f0000f5612f5634150a43a02a8d762dec9c82408a0e5aec0a509711be09da09052980007f01d0600014ea05bcbea2179df83200a941f24aa820305008760166000000076f093e000055567360ba62a80003af82cf6d9161e08611d019fa2f141d42440000000559077648500005cf0000492996c1775f7000000006ba80007a012d2000000000018d3000098e3629c460000aac19e400000000004860906000000000007f8000016e00000000000000000119a70a81fe7098fec62cd0837b9800000000000000d3c4b9a39e4b8458a2e09c547d2d35201ae3ee0000f22104879811387bc00b800078923321001502204a0bd0cf800000008058ea038a2cb166800013bc00000000000000071dcdc000000039c0a460000000000000059b80004218000076400000003ee0000e2c6580b5e0000000000173a00000000000fd8094c2eb876c0000000cc0000000070f00007630000000000005ac0001c780002c40000000229090488f4805800000011ba00022320000
  | 35 => 0x43e9be28250b4e000109480b000024d610c0cc06226f71daa0000fe000016fc877800001f400000004f423a0c205c122b8000000085704d500014ae00000000000c2c000204c0001fe00000de00000027285829226e8fe689700007d222ab21000006f388ae0000bbd00010e000000006db8c9f0000000763814e701218d54e000024a000000011e0000000000000000000db44d70000000131e5820000000000000000006b200000000de238182220000000122485273200001e140004f81be44229ca61ac8f9d21e8dfe06edf32000000000000000000000086cb93481800027e9f26767000000016c567500004d905b85d28000305d5187258000000191e0000f3c58382f600001691f900001d2954022f9c6e000126056e800000009104fe00000b50000000152813c800086b800014e88c64418000573a31a28c00000000e527f35bac000000000000001b1c0008b810be3d48cc83ea01c2000125600000002820d5c823143e2d680001690dcd0000e5a0870fc26aa11a67e2000017a00000000000000000000001f500012b600000001b45f6a0001ae600000006df9f0e2ec048b53d9e8a1a1a2be2468bb68df20fa20915c27b893c014490ac00000004969744510940403e80002c1800000000000000000657000000008880000a4c73600008f99558000120263d80004e920b8022129012484f674b000000008c4403800032c1fe2414140a2b98bf08ad80ac8174bd86bda0de3e38f4c084a0580eb028863a00000001f2d0000000000143600000002c2800000024500000bc330f000000000005c3219a2831c086e080005619ef65a70210309852c2dc00a30d60e7650c000000000000000000000188a00001df0000000663800086801f48340000000000081e85974da0ae4742cdb259a88e200000005af244c8bd000000002b0000074c00001840000000000000029400006a880001374d026351cb81c1800000000005e593b63049da82ea000080b95f40000b4936c169687100002ad00000000000000014600023f417d4000000000000023a60001f8d000000085d915c00004c344394d600001cc000048a783800000001ed0000ea655303660000000000133e300000000000000000000000121b1cb8e1c097a39800002da0001e580000fee00010e500002ab1ee15dc000000000002787b306e6032a190502164e0c906fd0a807d40000bd234e1ee062000001d41964758df743cb817e77443d847e0be263810b6280e0cc07586528420d5413787b27f9d88e058c21e00000f60002062000143c00023ba00000000001f431670e3100000000000a2c000000089f98c6000000000017687b703420001f6b05a981f6e2879e41a1fae6f78000603a10d000000000000000000a780001a867b280000000025775941a00012b46b18d44
  | 36 => 0xc75185740001f128211bd66ea00006b49f9713e97ce1b500000000b1887f800009181e56560cf88cf8dec7980ffa099c0008ba81b42a219827008000000008e00000000cbdfda00014c0000000000400000001c60389035f0001832479800021100008568000000210400018ca0001ca43508314890000000004cc00000003ac8000000041e0000ece5adc0002a9000000001ca00000007f20ac6000058f1864000000171e20c97e6000065046d80003ec800004980000000c32673c000000155e0ce4896000055800000000000000000000073b00002e594400589ce6863819547b00001e804b7000000064d9f64000226212d000051d8af200011a230d800043b80000001b8007c0e4a00000006378302528a464000000087b09a206f40004520000511071448706f37915a8055a80004c48fe800022ba62d965248b1c3a0000a8c00000008811f10863000082640001aa000000000002ba8000000000014346ee00000000000000659a1b400013d64320c8432da3341239c933fc8384000000000000000000fae0001b6600000000000dd86338000000000065d8000000156800000000000000000000074e8000000000066ec1a08d400005de80000001f3833600000b0cd7a000003c00000004f6800048a8f3e180c0ec00000008d081f78e4a08e8084ddc000196a34a0f70174800024c970e383c00024c400008e4eca000000021b99b201a087c0000000000057634280000000000000000000000008c6163882f080467c968e0880b406a3a2e470481c1680957e19112400000e2f31301104ff80e0000000006880001c69fb2209c00025220107ac20f200006bc8bd9ba48b7013a6260b600ec1c1c3698ebc00000000d90000000053e8da01740001448063d05a70b17626cb9d520000d1456a800000004860001f6e5c58478000082b6ed9a847c21eac0000fc586c1f341aba11000000005979a6c000000000000002c91e120784e7a00009b60b81a7a59b22f2661000000000000000000084c00000000000000000000000000018648b9c000819800000000007345d84908400051a00006ac800000000005fd98f00000000033c0001990000782800000000004db80000001ed765b818257e895e8d3800009a80000001c725d5000053b200d58d993063f800070c822a0c99ab60000ba200003900001929518942838e400005291b02244cf2305137211e569407bc2170000dcc4ce00001b3800021ca31e3220ca125d9c4a220a2ce7bf0584545000000005ec03040562ab9e5e46a0aee67d9b5c68d19914061a085efc7604fb000b4588000000000000000000000124000000000000001e30e8e1e040000000000031000000017910000e2013c01da873000006194aa000079048d10047a986b9864a04230c506c5918782800d80a37c08b846b
  | 37 => 0xb8c1a6818c903b508174269b948d51b3e4b41f87005451e78a11f941480047e3c00072a800000013ee0000c7887c113e05f095832ea03c8360f683858000000124c206400000019a476094fe59207f00ab812d5600d180001f20000112c079cd74302c2fc8a6a1ca881a24c7069c0c1c221480000d5200000007ff00003b99f3c3738611000204300013460000000027e3c983c18165221a5a00021542a499be8d619fc66680004ba0cb43370d1c8f0937e220000000000000001b265971ebe13f83c032e174200018ad00019ba000000000016a05910eaa0001a2e00000003f3000072d8dc72f097dc1fdd9500cccf204b50ea22bf0eba212006702510b8876951e4128b3200012820000acc000027e3368786880843255500003b119e6075215600000000000000693c18a0d880000afc96a141154a562800000000000000000000000079a80002e0210a00000001640000755a03000021ad0001aad00019c7332800000002ee00015d40341a6a000012a0000000000000000007960000c6c584078e00000004b1a0e00001b087a709ec5ca03c87e080783b0d1eb4fe9b700000000000000000000000000c5031682f93ee40006c509260000fa648c1db20000000639d9802039d380001e7400003b800000001f89f8c41880000000e2b8a99c1e0001f2f0001e1c1939d3100005015774fba28d1c340000866000000025f00000fa000000000120001dd4000055346e0b9a23c5c6c2f78d267530a843fc221860d056600002b45768000565179059815c40ca8000000046600000008bce112463800024c000011f0b5c7d093de000000000001116119a32000087f86996280000000081800000007f40001cd9000110a00000000000000867800000000000001cfc070c0000000c700e7000000000000000ac406a9ba21988000000224e3b210364a18000000000000010801ae97b000000006368f823860c2900020828f880000000000000000044412660000000470134c5641ff63539a964b7632e00015d2639000000023300000000000000000012ae12a000038d8000000000034e80002951d706e3000075700008eb0000000000086ac000382000086580007770000000000000000004298f940000000370000000000000000000000180216a002886080000001118000000000000008054000000000000000008e41dd307b000004314be000000081b0e5e5c998b83db1fa900007a2000000000d5c5a01c909217993b200000000000fa415580007e74a9e70600a000008c20000dae000073a000082e5dc931c8c218eb73e0c1518c83f048995c600000004e180000000000000000044580000001e100000000000a36400012ac000000000000bc00004e680d9423000000000019340000bb40000000886800084f03cc6c1800012b187a00012d
  | 38 => 0xc92970c9a3ca06075ad57ba8aa62447ef82e20000fd208dc77a000147c00000003901e8e72ea27680485fe04c400000000001f211f40aece9881403d0000000062c864f61405b200000006b0800064280002c080000001f3600020e624cc000000000064d40000000000009001709b000076e82c1889000000006cf0000000000127a00020880000f0c1c400000000000000000085f0ba6000191a36bcc1064a16f800005825d390206050000000000036880003b880004490000048232f7289ff000000000001bee1805c6a7ca9f580000000000000056d00001fc80005b5800000003004c318f88519b3c0000000537800000002c90000000290800000020a63b30630000009c43a800080898521aa88897ba10c1159d0a81ef940e5d003fe0001e1a4a1d7e400000000000000000000014d00000001f005be4bc816d85090368eea666228a00000cb0001f474e51ec3342000082d40008de029e0908000276800001000005928886000000035a15ea4a7107f52c9c928a780006748f165338000000028400011f500000003c2000009680003f8da94532197e43980006c487ee45018b085853980de84246741743000000017fcd843f0103a8be099c74619d605d40000cd4000000000076d000000011f045781e48d3142c29f84d080303525218134417945400012fd06580004b100001148000000000090c9cde000052a07a202a59d00001f8c5ee821960266ba0a06718a6245a92246f01a5d7aa47e0251917002b819d8e095825f40000000000000003201c3943881f9fe4121034e0000c4600000006ab13dc000000089414f02b9c0003d8977435c8016475800064a8d648cb5cfd03495484211a2211a078079c0e9e0001d7e000000000013d400005368eb8000000000026280005fa4000000000000000003f24000000000087d800000005480000cd65a7868a7028936536024a0000594757cca640304387b9df7e00000001d699ec38d121d00000007cb126c000000080180000000000069c000254147e2228a1c21ce2ad000127382540008a01e4c1b940003ce9686131934e3bb0e8a413893787f05d63b60f9a174482d00001b342e8000790800000020928471e0c446800000000002e20000000148c3b8172c000000081a80006080a724e304c82af159e77384825ae0e7c000000000000004d5000000000000000d86740995d8e680000000c1142d0b4266700b65009c7341ba430095c4720ca173400000006f1800082c23de1dedbcc145895c0000f400000000000000086920aa1d01fe3325010451b9fb864421d439408944970000000000000000000000de60000000000000000023dc6f500000fc80000000000501a29800002c082ac00054000001be584a45d800091020dc00000000000ec624f00004dd000000016a244d005060
  | 39 => 0xf8a50900000000000758500a000081c8c304230001b4000000005b200005d622d245694e800000000000a4e6958b3483a90540000ec2000151c0000000629951a62306e3000097e805c0004bf000039991040001e38000000000023f888c000000000000000d8e918000000005ba000000048480002b40a9c67700000001c7c7a8945280100000000ea008f535e6988ea80002002000000065680000001572197caaa7fc8e78000000068b0000000000057f22201571f7808e00000bce404000083b3b900000b913020e9152290d0ade3b41a687d9d6d151e800000002fe00000002ff80000000f044a4925e2c78e380000d7e000121e4aa000000000000000dd374103d45e792f0486948a6790cce0ae10da5afca6e0001fd668805d0000168209b9e642e813800fcd11e64c9e4812a949882d05980001bb400000008e7000060a800018307f6828598626f1f350000cf0000222c0000122577d7147080000000000000000007a8c0007cf5b0a6e580008cd80004b88000000000000015e000000002d10966000000015796fa2fd02e300016b40000228744a386054872517adfbc875858c7e01da3000000002d21e3665800031707677da0000162c00019b80c2000000000000000000000000000000000000000000000000000000003f8800000000d450b800054e8b8f74d0a18154400000000005fc00008488628000000000000000001fbf19195f613a968000017c200002bc1bc00009029e9a00cc00000010e28ad1e3e0000000134e3ca0001d0a0e09794198ce0c4c344db160caf06f2800073f9e5b142000000000001fe8000000000000000000000000000000000000d900000005b6019f00007d826d11862f9013c000069a000070285ba20c9189a755af9f501b80b8e725025921a181c12c5d942d998fc29c1ffe4120000000000014b800057c00003208674499015b6ef0dc248b99c0179c000000000000000001be971c3fd1a926f2021900016b040595a2000000000000000000000610c22d51d208a0001c7900000008a306535df0000438cbcc00000003d39cbc5c0800000000000001520192000037ec15a1cf0b745c8040a00000000000ff60e49a57130a01d854800000005c8000000000020811edd7521d9496237d986a8b881cb13651a044820c40f7000000002b90f11f45684992e6c309960000e6426a83f817b4b520001fc63331c740001f33000002f3e7dbbd000000000000006b306cd0808000000000000000007d34d105f35f6d00010960001362744100875d472805b095a03e168411b06f8823e0642b097884691e8c00012ca00011d30000e80000022600010d65a29be600022da000245a000000000009f600000002080000301000017319d89120000000213231980007da40000000f1c00000e8000000064905
  | 40 => 0x55e00000000000000000084b09d88be42936160095000223e7199ab017ddbb928503160000000061df8a000000083f00008d69d9a8cf2130328102a5e3171005e000000000000fa800000018a075a00008b000007bb000000018fa0000000113400000019e200000000001434000000000000007d30000073c436557012f83f8c1e65e0000000000000003400000000000000008ad6c483d8000088c0002ce84a60ef03f56c0230200000005f58df800000000000800613018312f21680e7c1d744c934a2c502160001fca5388b3e5810f6455c08f23da86a4794907e5b35f027af09a02660ad6000000062f06d50001ffd2029a8c00000007a217ae0da9d7800024520ea0000062516e462a07815f1dda27d05fa1e685ca5db85c71171f9a091ddec79340006d50eda903000038e9dc23d800000c11a9e23980001e2904b000103c76b23990000c92133890c6018000000000000000001d892220000062000184273880005280b2253815ec7aa9c76000000054f88cc6df1e3600001ba5ee00008618ff8566011417f4236359985c121c2d651b000056109de0c617b66654f9931880000b1089c1368836000000034900002899d0e0000000772851866d198b1b6920c103928e4cb9a1a77980002881884756803a1a8225e00008f92c0072151940778be8c18811000078c9f4669b90d407249747f5c1410000dd604723400e7492236305e200000002d31fa8000072006a5bea2828e9c397007b24b000023b8e4d000139a00000000000f6e65d0000000000073fe42e00022a000000003e19d7a000000038a46be8542278022800017ecd062caa0b60000a4404b800000008ca00000000c4800018b00000000000840829a0000128000000000000008ce06ec51306007cc1fd80000c30000000045600001bb527020e059385b076c220df2e65c1f183eaa05b0000000029c89a86a88b08bf9e3a3c689201b0c82a0000000000000086880004af20a448ae02600005fc4f10fea5312072000223a4e704b514e241c0f29de425380004f918566cb07c6774066a00000007b7800000023d60000000000000000000002e300a80001d4074580008da8e8218599f00000000758800000000000000cfa000000000008148200000000163c000000027c9a1c4939d6c0021fa300017927d4c8a838106e100002c709900000001e2e34f80006ca80003be8000000000000007e82998116000243e000214e000000014c09e649480000000000646c0006fb1600000000021c400033480007f5000019506553f58d7800015e6376827c000000000000000000000000000054d149500000005680c6e503213e00c400037180000001f650001e2a228135600000fb0000918060400071700004c605681f40d9f5728de8606a1e007e0b6c4fa0bbb0000be61b60f7e0
  | 41 => 0x843a1160000d4600000000069f4000000007210000569800000015e843a1844244800039b81927d481eb7bc2352466000054c8829377834c62594bc7a4c0000388e6c905825b00006603275a1e6d89a7e243800045e1098034c0000000a1a549000073680000e540007268000891800000017841c899ee00003970000000667856e0000000000000000003e0000194a60bc9e8000000033a0180098800015180000000ae807615b81d1800046f146d4842328092ccd073c800039513047e58a826fe80008d580000000000223000000010bc0000000735ce887bb861208cc8ec3e00ede3e302860001cd40001662000000013105021a3141012349b81b28a2e00013700000e4c000054c00001123090d94000000023f8b92828c000000000037916de000000068e800044da2086ff80000001fc510f000040c18d8000000000023243bb97c87fcd0221168ae0505047681a0bb20000dac000241a20080000201a8a0000000000000000004700000000000000000014844ce800069400004ee8000000110840e00002300000817d19c8998000000186200000001bbc77301a8000000050e000204100000005ef8000526836c4c580005e88fb451580007ae80000001aa65ae9d4a45806690000f242c387da000163e73a14b000000004431390000000000006de0b490d9277ce2300000007f854920c180000000000000000000020c0000061e8c880000001db8433800076597768e1145a7ae1b4273d01c07fad7f84349a2484d90f08920bcd01912a00000e1a0001cf67a08d5a00005ce000000000000007db1cbe76f96c28ea97ee1bd8d50394de940c71b4a06ad6ca216953c79b083c428800008c00000001af43ed854000009f07578000000000000001dc0000000000216f28a0000583086c00023da8db9606854c8c80000f84437800028a80005f480002d180004f98000000204e47189be847e1f44d21fa64afa00b0ed82fa1260a4a2cc1afa3cb241e8dd1f6069280000198cfe00000000000000000117e00000002b280000000fc60001a5428f80000b390dc000000000000000da000000000007a1800000016c01a6033d000065882b400000013f055892b80d5000040cc04771e9c2266800002491aec7ac840c000125831a80000000d4a1dd16ac5cf80005ac9a78281007023f0000542116643f013e8ee000000000001f29d3290200d12ee80cc00015661ae0000000107a00009387a81d7305e9e4072b069475d000039d13090379b487988a7c613a2100001142000044c0001a2a02ac000206983c0000cc67f940006780bfc39220a878814a4000181e3649e301ff888e7fb800054b9090127164200002cd0638172000000027a969a176890829d8f780001f8e6d5800013fc00060e0344000081b0002040787899a7e79fef09140006518
  | 42 => 0x169000018ee0000044604000000019c10000000264157a17a998864b0000224000057b96aa8e28000000000000000008c59bda368222831f842200000000001d8600009ac02423d2401a45681490420001ae800000000001ac0000022c0001664000000000021a8000094200000be4331b3800000000001aa44529870587000041c175a919800000006c400008fa0000000503dd1c000000000000002fc5066802400000005280000000000204800000001c700000000000000000049a8000000000082a400090080000001e16000000000000005f6162648814a877d97780b6d0783f6927c76400007dd5cae00020da2de800027004e800000008b5101a000000000000005de400000016c60078000879000018f91e216b80000000000476e3726be1f0a47a14ac54b19ea01510ae3e71c10314a2742d420db029218a0f900b062410b209d1cc40a3041c5c20fdc1af4e301a55dde8c1a3b47ad975712b81c864099418a20ac076ecafa78f086f6ea998a026983a43f8d1686e1d140800c2a062da486769b36461040624e874e11a8e7e25ca14a00003af3ef99623d124225f81180000000056a000004b000012c1b160001b987ee80000001bbe65c8000000000053d1c4228899bc1f58dc400017fe00000006d6000006e4f3021605af48d8c98000011938789f86330688109400002fc0d65ce0000000008c0001f0474f00001b08000199c18c53f002c000000075100000c6805700004a45e2a1200000cae35c00008b1800000000007b081cd8bb995233b9c9000000000000cd480d1ec647e8e8c6c38000000071659f00f4000059677f85c60bbc1d5177901c000044a4a20e940000cb23c288628c480004b09be05999d88000176469801a600002b200009160000000000000090f000006c119600000008ef20ee00020ce778a3602f5800006b000081b80004b7884c5b820202d58589463172e7748d5824bc00051e043a0001ef2078023431d800020e945f000000045a090a000000089c800000000000000000210800000005f300000001e500001201712916006977f21fa45d4d2c632000000019c256c8000255868b00d80000000f886e4800000000ad5250107000000000003ae00021722f18db800000000000e3c7d700001674a90000044600000000ae867209000001b910390a080004f605060000f061588000000000000007660cd084e79d82f82055c9c5cc004d475e2f054181dd360800059e83365caa13419c058181c51b434106bb0f597002b380006938378832819a0000000224c0005959bf600000000cb49b00001a3e000000083a210089805d80001f416270bc036d9aa91b4a37003c800033103567d291c46e19770000000051180006d11d368b7cafd0000b7e6b80000000204b1809d9200000000000000
  | 43 => 0xed65ba80000000784000039e2bd00006b1020485ac9b500000740001d480001b7600000000adc0000d780006e9879c45ca3f00001ebf047598c7d884502a597501f39fd500000000000f5555195ae6f61f663028b86861400000002a63c3804c739000000000000000bac000000055b80006eea0970000000000000000017b2255000000000003b7006000000006a08000000244600000002620000000000061d00a1000000000000002170000586800028c8000000000000000003d1920e0000000000000038c800090b066c0000000000135000010742da0764167800300024282e5000075900003d7a09a42fc00000001300001f564a2962290003a28f300a23f3449a16d00964ea84ba000000000003857ca00000001d9e67781f2000000000005800000f48000231400023440f340000000afb078c000000000000000000000000000245c0000000000000000000006088000000000000000000001da400002e5000000e21c0000802963a00013ac0000000000104676c0cde00007c700019f400009dc0000000643c00041f011e037011a776119009e8000338a3c4804400000001027ebd37c6d310f600001c60000000279194429480001adc0003cd20633d083552600000536941950580f932780000001dcc00002d80000f5a00000000001c8600018ac8e38dbe0e5a0d45b383b100000006de89b200003ec1ad872a00000006121ef8653841000005077c7000022b158815408ea3f50dc80f986fc18200005e0800000007fb000000000019fa00000006910000000000031a061887e00007ef40004448a9a0000a5e04616400001b347df02f200c0daa4a980000175ad86f944b200000005b9a21237e8dbc000000047486653eddaae000164c000000043c8000074c0004cd9b8477c53841fa945c0000d881890b043178000818021f5ae5ec10421ffa00000005b685990000e5614510d072082f1551050c3a902b6622031e71a1ec81da9c584c00000000075e00015265f500005b300000000000000112a0000dea000000086ca20e1929688478df440000c6400024066d808d471913b48b61aa000000004fc80005e821283ec000038880001dfc00000007c064814fa000000020d0b1c10597a86218c342650f5413600000dc8442188000000000000000c0e00012a478d01bf4f309520000000672000000001a88a0a013284803e7329b020001344315000000003d200000003f4000000000000000000000000000000000001e4675420f80000731000000001ba3ea60d8000758000053096ae36e8b2800000004f41a46164603a83cc0000000000609000000012fa000113a4b2060a0aa87447308fa254280003578a8a85e033a6ff00000354000000000089a80000b19d58000000000021ce01b00000679f0600000000b5c000000
  | 44 => 0xa00003ad800000000000000ffe000000000000000001c2859f93a603f00004f486e21708be845b08ba0000000645c00075d88d859c0000000000000000008169a30000000000014ee17916a680516f24dd800000012fb786120400021dc0000000000000008b80008c70b166b58732585800019e05bc0da5e001259411026e02388d94ba000025019008dc5bb80006021fde1dc850300007d23521a0e00000002cb9c361d0857f3290a4827b96500000ab20000000000000000013260e38000000191c8508d9a1d04000000000087093222e114d0000000000000006c9211e00000000001fdc00004307eb46060000fc8000046000012a28cb000000000000000f900ba12f81a41e4e2ad9e083218e2a4b0000000007b135b800000000000001e146ca1c8c720ca38000070462a00000620c2e000019148a0000301c000000004e4c053300001c5e60a1c4e1770666472905c6b892742a80b9e033465a48c80000001658722027207d87ec81ad2aa0001dd50e4c67619ed6d3198481886d88e400000004c280000000d9e00004207c882257d6904c000000022a85640001fb600001a50001fa20000000000000000000000000ec10314e1d29d00003ae19e83a484c03488c4a18f176600000001d594182530000000107200000002c68000207a2ca000108e0001ada0000c4400000f000012ce4a50ec000017ab45d01d279f186800001d000000006ce98c000000000209b1c50721940000359228800041600005c18b6e445195e85042dc03a9a64725528c296005216395f82ffc0207998e4952780007f987cc7fc400a5f680007810000000000019705f622da061000000040a180c17d000000000008c280000001320235a01c392dda01620b3828400006a223767970000000000000000006cc9ab460cc15c7c4c00000000000001df700000006b4007900000000001c4455380008799ba07ec57ac7d3d79a15c04022b51fe901f0000000054f00018120000dfc000112820880000000aa21351d28000225a52d89d66c82388000039a0000000631000088d1bb274f80004c915d061b800000000000ed00000000000000057a16b42c58a5000000007780001a0c00501fa00023f200000008c0000000007eb00010aa055d39651c95de00000000000eb06dca11538dc96000000000001a00000020c0000e6000000000000000000000019594d40574000395400000022cf0001b4600000004c20a0690a80320001d0000000000169cd005c0e280001a5e5259cd2832092a22d0d7c6b500000000000000222615a400066e0c8e0000000000000087a80003850000436c00000000000e6c5a23ff061c8ca9f72358130e857807e0001d6e175224237500005758000000000085e800000018be000000000000000001c802d2a114669c0005178696000000
  | 45 => 0x801e6d19e8c402ea2339e440001bae4400000000000000015f2866000069d800000000007b9077e000000077c800078880000000000000000055800006bb8e0e000000072d02078158000000000016b13280001b880001cb06810000000000000000000000f7a576000048590647498bd48ba16f600003a1839050a89b8f0200001568ff80000565dc0000000000000000001d2e000182c1c300005e00000086929a6401040000000035880000000000772151200000000000dad000000000000000000000910854a8f5000000000000000000000039948f800000002c200011de0000000696000000000005fa9432000000052d000066a80005f89ec40ff00000000000000121f000102f53487b0000187c000000000000001179cb20000c7237d146083881764550d0c47d942242306bf000080b03263fa858044449200000000a40000000018b8a6c00000003bf800071ec54b0001d1e748980000021c800018668499e99400029c00d00006f10ee81550e5831f21ee1f716244180f9250ad9b05191a704d681930954ac80000e2e00006cc00018821ac12ec116118800022160cc8000000000000004e400000002ef9c242ae8bec2f28000000000055d9f7a1e499b768295e77e71b687330b9c000069251a80002dc942a84e16f477191ee8991ca03c4070a000217e2378000000000007a8000474400000001c500023967a40000713217432f9a366ae8000000230406be43600006c10274000454800000000007cee01e00000000000000000000087a09d000000009098f7c2d2000000022e630594dc499400000000000711fc461c80002b608df66ada5c0000f7422992b206b9cf039056d0685825488b9bd2036c000182e27a6e70000000000024b9246024c9440171e06790600e75397600a41fc31e9209e46c85f028f0c026b38e4300310c269d1c8e6438d2a0b306102478807416c7b62fc89a83d7148245e800080a0000000000000015b67279da6000204a3d424540501f1400001b275a89a638f8000000203e8b31eae1e5517d77c0ef60001002000079f60847b4000000027809fe89a000081d84d700000005b500000000aed051000089c02ac541000000000004cc8000000059a8ef8eac000019b02bc0001a4433c00000000001c0e000000043617ca8a5a45e264951000000005b490443531ed612897b400021c61eaa3d85790aec61008bc40b025d000000013e0404829c0000000cc28670000000000000000000af53f4065c000000096400001fd1c9000000022863c600638ab823200004773f1c15e29817cc67107a61ad02c81191014000000000000004e8834600000006e78000000000000009a40001fce00000000000000000075419e810000020192e61a5570b9efe5d5983b80600000ef873300000000000000000000077
  | 46 => 0xf762739ea46eedf4e71580b200008da000000000000000000000000000000000000000aa642903ba0001d7c789800000004283d9859b06644a0000000000007ae3ce082800006c00998000035e335000000081706fe7b648e033d9b1e5630d1a33b03
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x95444010b21821d95444010b1283dc95444010b1183dc95444010b12839c95444010b11839c95444010d21721c95444010d21549c85444010d21545c85444010932875516244010930875516244010d1154dcd6244010d11541cd6244010931859d06244010933875506244010951859cc6244010d11549cc6244010d11545cc6244010d11549cf5244010d12545cf5244010d11545cf5244010d11749cf5244010d12745cf5244010d11745cf5244010b4183d525244010b2184d4e5244010f015494e5244010931841d9524401095183dd1524401093184dcd5244010b2284dc95244010b2184dc95244010b4283dc95244010b4183dc95244010b22841895244010b21841895244010b42831895244010b41831895244010b4283d515244010b4183d515244010b21859515244010962871515244010b22841515244010b42831515244010b41831515244010b2284d4d5244010b2184d4d5244010b418594d5244010f025494d5244010f015494d5244010f025454d5244010f015454d5244010b23845d95244010b20845d95244010b43835d95244010b40835d95244010b22841d95244010b21841d95244010b42831d95244010b41831d95244010b4283dd15244010b4183dd15244010b42839d15244010b41839d15244010d21741d15244010963875915244010960875915244010b43835915244010b40835915244010962871915244010961871915244010b42831915244010b41831915244010b2284dcd5244010b2184dcd5244010b22849cd5244010b21849cd5244010d41731cd52440109638758d52440109608758d5244010b238458d5244010b208458d52440109628718d52440109618718d5244010b228418d5244010b218418d5244010933875505244010d11549cc5244010d11545cc52440109538754c5244010d127454c5244010d117454c5244010d21549c85244010d41539c85244010d22745485244010d21745485244010d42735485244010d41735485244010951839d74244010951859cf4244010d11549cf4244010d11545cf42440109538754f42440109518754f4244010d427354b4244010d417354b4244010951839d64244010951859ce4244010d11549ce4244010d11545ce42440109538754e42440109518754e4244010d427354a4244010d417354a4244010931849d54244010951839d54244010961829d54244010951839d44244010931845d44244010b21855084244010d21755084244010f01535084244010931849d63244010931859d23244010933875523244010931875523244010d127454e3244010d117454e3244010d227454a3244010d217454a3244010931849d53244010961829d53244010931849d43244010961825d43244010b41854c83244010d41754c83244010f01544c83244010
  | 1 => 0xc89645c0434c920989831c142501209a1811c14250120989841c1324c1209c1811c1324c120a0c835516215110c0d641cd5214910c0c7458d5214910a0c8255163d0910c0d7498c52d09108d1831c161d09108d1831c560d0910a0d82152639091084c8758d5290910c0c7458d52909108d1831c161909108d1831c5609091090d831d5421091082c875954210910a0c835954210910a248550961109108d1831c16110910a288550960109108d1831c5601091081d87990538c910c0e645c8538c91082c87591528c910c0d641cd528c9108b1841c1618c9108b1841c5608c91090d841d5320c91084c87595320c910a0c84595320c910a48854c9600c9108b1841c5600c9108e1821c563901108d1831c56290110cc1739c86150110cc2735c86150110cc1735c86150110a91831874150110aa18218741501108e1821c5648c1108b1841c5628c1108e1821d9418c1108e1821c5644c110ca1749c8614c110ca2745c8614c110ca1745c8614c1108e1821da414c110c907650d414c1108b1841da214c110cc0764c9214c1109a1841c121c81109c1831c121c81108d1831c564881108b1841c563881108d1831d941881108d1831c564481108b1841c56348110c91749cc6148110c92745cc6148110c91745cc61481108d1831da4148110ca07650941481108b1841da3148110cc0764c93148110aa1841872148110ac1831872148110b12831c55444010b11831c55444010b22821c55444010b21821c55444010b12841c55344010b11841c55344010b42821c55344010b41821c55344010b22841c55244010b21841c55244010b42831c55244010b41831c55244010951859cc4144010d11549cc4144010d11545cc41440109538754c41440109518754c4144010961859c84144010d21549c84144010d41539c84144010d21545c84144010d41535c84144010963875484144010961875484144010d42735484144010d41735484144010931859d03144010933875503144010931875503144010d127454c3144010d117454c3144010961859c83144010d21549c83144010d41539c83144010d21545c83144010d41535c83144010963875483144010961875483144010d22745483144010d21745483144010931859d02144010933875502144010931875502144010951859cc2144010d11549cc2144010d11545cc21440109538754c21440109518754c2144010d127454c2144010d117454c2144010d22745482144010d21745482144010d42735482144010d41735482144010963825d36544010933845cb6544010953835cb6544010961859c86444010d42735cb5444010d41735cb5444010b2282dd15444010b2182dd15444010b22821915444010b2182191544401095183dc95444010b23825d95444010b20825d95444010b22821d
  | 2 => 0xc05450832c2a765c05450832d0a735c05450832d22715c05450832d21715c05450832a25811536350832a2980153635083290d871526350832b05811526350832b09801526350832b05811516350832b09801516350832b05819d64350832b09809d6435083290d87d964350832b09801514350832c25645c4548c832c29645c0548c83282f87592538c832c0d75592438c832b0581151438c832b0980151438c83282f87590544c832c25645c4544c832c29645c0544c832b0581153434c832b0980153434c832b0581151434c832b0980151434c83288d849d9544c83288f87590544c832c89645c0544c832d09545c0544c83284d87d90544c83290d87990544c832a0d86990544c83284f87590544c83290f87590544c832a0f87590544c832c0f87590544c832e09649c0544c832c0d645c0544c832c4a765c0544c832d0a745c0544c832e09645c0544c832d42715c0544c832d41715c0544c832c4b645c0544c832d0a645c0544c832c49645c0544c832d09645c0544c832c09645c0544c83288d84dd932d4032a15811914354032a25811914254032a0e84dd93254032c0d741913254032a45811913254032b09841c13254032b41811c13254032c0e635cb4394b40c0d639ca53d0b40c0e645ce52ccb40c0e645ca538cb4084e87995320cb4090e829d85350d40a0d829d85350d4090e839d85250940a0d839d852509408b1811c1644c940a1581195430c940a2581195420c940a4581195320c940c0c655d1320c940a89844c9600c94090e829d85450f30a0d829d85450f30c1a765c05450f30c0e645ca4394b30a0e82d5163d0b30c0d7498e52d0b30a0d829526390b3082e879954210b3082d8799252ccb30c0d649ca54ccb3081f8759252ccb3090e829d85450d30a0d829d85450d30a15811954310930a25811954210930c0d649ca54cc9308d1811c1644c93090e849d8524c930a0d849d8524c93084d87d90524c930945811d4424c930c0c75590424c930c89645c0424c930989821c14350130991811c14350130a0d8494e62d0f20a0e83d5162d0f20a0d839526290f20a0e84d4d6290f2081e879954310f20a15811954310f20c0e7458e5390b2090e839d85450b20a0d839d85450b20c2a765c05450b20925811d44350b2081f8759353ccb2081d87992538cb20c0d649ce548cb2082f87592538cb2090e849d8534cb20a0d849d8534cb2084d87d90534cb20c4a765c0534cb20945811d4434cb20c0c75590434cb20a15811954310d20c187550d6010d20c0e7458e539092090e839d85450920a0d839d85450920925811d44350920928855c04350920c0d649ce548c92082f87592538c9208e1811c1644c92090e849d8534c920a0d849d8534c92084d87d90534c920945811d4434c920c0c75590434c920948855c0434c92
  | 3 => 0x170000a20026200000000001cc6200089002141305a1d1f4002c8b790a07af4000000e800bf8002d0000000015c38002cc7db62b6d220f04e278856a820b3e9a879144db6ae104ad3086d007546c0022cb875b15198004a156463039684200000d121a9491a8b9100a800b5b11000fc9f95e35318d72bedf154cb03e50f32de11e82189001a620c00206ba44464e2804b0248ad124cd67c5c4cae300000000001790032201a68cf07e8c0ba11000ac81071800241dcc2b5a728767e8c579139258226618f000007a01c001ce3a000000006dc005300068afcac1400000030826000009b238306d585c542a16f2bc000000a002350030b0000000304000ec0013a00350c91eddd80c0029250800001190011c6f1800006fc95741f2ffe4158a9000bf40000116c6d7e6d562000003e0000020700000000c31e00000000000000037200000002360015b7083400000c5aeed1c000016088c00cd040b754f65ae1ca1012697d00341cc000710a4000008380018000840006440059f4a0000000194cce4352b0f000984ed2cbc9a4330a0165063704634802040040100003400000020140000000000050400003c0701009004080040200c08000070000000400018060300502002008000100600006000090000f000030480305c0500c040000001401018000000000007004080000402c100080000c03000010180003000048000481d00407008080000002c00000160000101007000010000100800000000d0000080704000004100000200001014000101800801000010100900800000000140105805004080000200404004160000300c030000800007000000000600000004040000301c0200c0201c370080000c0102401004030140100c000100100c0801c02040030280000406004040180000015a85811916294f42a89801916294f42c85645c46294e42c89645c06294e42a85811d263d0942a89801d263d0942a85811ca6390942a89801ca6390942c17655c45350c42c1b655c05350c42d05535c45350842d09535c0535084288d83dd942d4442a198018d4354442a0e83dd94254442a298018d4254442b05831c54254442b21801c5425444288d83dd942d4042a158118d4354042a0e83dd94254042a258118d4254042b09831c14254042b21811c14254042c85635c46295232c89635c0629523290f875536310932c46655c46310932d05545c46310932c4a655c06310932d09545c0631093290d879974310932c0d541cd61109328c9801cd6110932c0d541cd60109328c5811cd6010932a85811ca648c932a89801ca648c932a0e82d5163d0832a158115163d0832a198015163d0832a45811516390832a49801516390832c0e7458e5390832c27655c45450832c2b655c05450832c26765c45450832d06735c45450832d21719
  | 4 => 0xa20e400000b4c000031c0000000193002127e16b9d8aca3926160f45e25c23068c4000958b75cee3c1d4706202003808d270bc152b080b3863c092ae00123b9b602f800ba182539031b2ca546007786a19d486b18d82ad1158f654007a112e322d856400d48004313f05000b650e47400001e0000001b9ea9e2320c8f2b68006c8000a00000186002a6b392f0033a0033e0026400000a7b05001370005c00240d5071000000031400358a402d4ab64221206d05e68246d08de2c31306800880004d6046a1e63180000000b928a00000a018e368000000093800aa1440000012000cf569b7e5ec0294bd576733464c3205d595e20bc00190b1149000000000eb34fa5fc00a8b06d59660000000386003080013d555ae7b14d229ba4020c6693c0022638afa001be7000098000002867215d270b67f108b50b9dfa99591b0d395c62a3ea30001a52dc08002d4000000036000a70e6000000031a00000000000000051800c5f8ead829c06e0311452aa5838153da272149f02102e870700024c9a800bb13e000f07500000184000000022c0013214000408000015a00000000000024486000cbb2a65d8b74adc35a21002bcc98000023a762a02ef098880000030dc2824e0007f800d22c6000005ba42c330e0000020af844c000000000000e480043d044cc00b4afb5a89437ceec65e2ab1681ac00ba9770016c8a8009400000000000004c4007c80000000672966da4a81800d78ea001b8002e22ba160599e0027ad987a00000000007b82ccdb6ea61dacfc8f55cb1b437a4ac0023934dd2242f67424a6e4558c5f19258c00048003f94133af330072000000000000000000000200077c000017a000000031e0000000000ce16d001d02cb0d52f6cc4800ae00057c00002665ef82584d0aa800bd800298005c8009505f0011f8a00020000000366232b8fd1200165000
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x80018008000001c4d021331e40c53760780a1700000000081140201c04aa30039ac2212658055460473580424cb802c938ae02a26419700591715c0544c832c02ba30232264a806540591195744c832502813253b2e02a2879850164475590424c930a04c9cecb80a8a1641409949d97014d32c8280b223aac821a659050164475590434c920c0442ac8b8086992412059321542584424424132642a84b008488482650854c9600c910
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 22
  | 6 => 994
  | 5 => 6049
  | 4 => 4660
  | 3 => 458
  | 2 => 16
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (i*5) 5
  | 7 => packedAt gbK7 (i*16) 16
  | 6 => packedAt gbK6 (i*27) 27
  | 5 => packedAt gbK5 (i*38) 38
  | 4 => packedAt gbK4 (i*49) 49
  | 3 => packedAt gbK3 (i*60) 60
  | 2 => packedAt gbK2 (i*71) 71
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (6+((h/1+packedAt gbK8 (5+(h % 1)*1) 1) % 2)*1) 1
  | 7 => packedAt gbK7 (430+((h/13+packedAt gbK7 (352+(h % 13)*6) 6) % 49)*6) 6
  | 6 => packedAt gbK6 (32106+((h/439+packedAt gbK6 (26838+(h % 439)*12) 12) % 2105)*11) 11
  | 5 => packedAt gbK5 (265128+((h/2519+packedAt gbK5 (229862+(h % 2519)*14) 14) % 12069)*14) 14
  | 4 => packedAt gbK4 (254114+((h/1841+packedAt gbK4 (228340+(h % 1841)*14) 14) % 8822)*14) 14
  | 3 => packedAt gbK3 (29480+((h/200+packedAt gbK3 (27480+(h % 200)*10) 10) % 874)*10) 10
  | 2 => packedAt gbK2 (1172+((h/6+packedAt gbK2 (1136+(h % 6)*6) 6) % 37)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xc3de3f8fc7f1f8fc7e388f1f8f1f8fc78534cf
  | 1 => 0xfc1fc7f1f8fe3f1f8fc0f1e3f1e3f1f88acb33
  | 2 => 0xffe007fe00ffc01ff1ff01fc01fc01ff730c3c
  | 3 => 0xfffff80000ffffe001fffe0001fffe007c0fc0
  | 4 => 0xffffffffff00000001fffffffe0000007ff000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x420080081001008000020480048040001045
  | 1 => 0x4040100012000201000102100210080004112
  | 2 => 0xc881b2249244925802d9014825482536330c28
  | 3 => 0x5108906d24893009256aa40049926c125c0e80
  | 4 => 0xa2112449800da49249b4c9926c0048246fa000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xfeeeeee8feeeeee8feeeeee8feeeeee8feeeeee8feeeeee8feeeeee8feeeeee8feeeeee8feeeeee8feeeeee8feeeeee8feeeeee8feeeeee8feeeeee8feeeeee8, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_37211
namespace PEqualNP.Outside.L_meta_37211
open PEqualNP.Outside.L_meta_37211.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 16 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_64 : Interval gbAtlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_96 : Interval gbAtlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_128 : Interval gbAtlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_160 : Interval gbAtlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_192 : Interval gbAtlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_224 : Interval gbAtlas 3 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_256 : Interval gbAtlas 3 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_288 : Interval gbAtlas 3 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_320 : Interval gbAtlas 3 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_352 : Interval gbAtlas 3 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_384 : Interval gbAtlas 3 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_416 : Interval gbAtlas 3 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_448 : Interval gbAtlas 3 448 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 458 := (concat (concat (concat bgb_3_0 (concat bgb_3_32 bgb_3_64)) (concat (concat bgb_3_96 bgb_3_128) (concat bgb_3_160 bgb_3_192))) (concat (concat (concat bgb_3_224 bgb_3_256) (concat bgb_3_288 bgb_3_320)) (concat (concat bgb_3_352 bgb_3_384) (concat bgb_3_416 bgb_3_448))))
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
theorem bgb_4_320 : Interval gbAtlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_352 : Interval gbAtlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_384 : Interval gbAtlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_416 : Interval gbAtlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_448 : Interval gbAtlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_480 : Interval gbAtlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_512 : Interval gbAtlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_544 : Interval gbAtlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_576 : Interval gbAtlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_608 : Interval gbAtlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_640 : Interval gbAtlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_672 : Interval gbAtlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_704 : Interval gbAtlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_736 : Interval gbAtlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_768 : Interval gbAtlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_800 : Interval gbAtlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_832 : Interval gbAtlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_864 : Interval gbAtlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_896 : Interval gbAtlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_928 : Interval gbAtlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_960 : Interval gbAtlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_992 : Interval gbAtlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1024 : Interval gbAtlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1056 : Interval gbAtlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1088 : Interval gbAtlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1120 : Interval gbAtlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1152 : Interval gbAtlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1184 : Interval gbAtlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1216 : Interval gbAtlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1248 : Interval gbAtlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1280 : Interval gbAtlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1312 : Interval gbAtlas 4 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1344 : Interval gbAtlas 4 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1376 : Interval gbAtlas 4 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1408 : Interval gbAtlas 4 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1440 : Interval gbAtlas 4 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1472 : Interval gbAtlas 4 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1504 : Interval gbAtlas 4 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1536 : Interval gbAtlas 4 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1568 : Interval gbAtlas 4 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1600 : Interval gbAtlas 4 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1632 : Interval gbAtlas 4 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1664 : Interval gbAtlas 4 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1696 : Interval gbAtlas 4 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1728 : Interval gbAtlas 4 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1760 : Interval gbAtlas 4 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1792 : Interval gbAtlas 4 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1824 : Interval gbAtlas 4 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1856 : Interval gbAtlas 4 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1888 : Interval gbAtlas 4 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1920 : Interval gbAtlas 4 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1952 : Interval gbAtlas 4 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1984 : Interval gbAtlas 4 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2016 : Interval gbAtlas 4 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2048 : Interval gbAtlas 4 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2080 : Interval gbAtlas 4 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2112 : Interval gbAtlas 4 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2144 : Interval gbAtlas 4 2144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2176 : Interval gbAtlas 4 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2208 : Interval gbAtlas 4 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2240 : Interval gbAtlas 4 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2272 : Interval gbAtlas 4 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2304 : Interval gbAtlas 4 2304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2336 : Interval gbAtlas 4 2336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2368 : Interval gbAtlas 4 2368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2400 : Interval gbAtlas 4 2400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2432 : Interval gbAtlas 4 2432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2464 : Interval gbAtlas 4 2464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2496 : Interval gbAtlas 4 2496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2528 : Interval gbAtlas 4 2528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2560 : Interval gbAtlas 4 2560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2592 : Interval gbAtlas 4 2592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2624 : Interval gbAtlas 4 2624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2656 : Interval gbAtlas 4 2656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2688 : Interval gbAtlas 4 2688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2720 : Interval gbAtlas 4 2720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2752 : Interval gbAtlas 4 2752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2784 : Interval gbAtlas 4 2784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2816 : Interval gbAtlas 4 2816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2848 : Interval gbAtlas 4 2848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2880 : Interval gbAtlas 4 2880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2912 : Interval gbAtlas 4 2912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2944 : Interval gbAtlas 4 2944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2976 : Interval gbAtlas 4 2976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3008 : Interval gbAtlas 4 3008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3040 : Interval gbAtlas 4 3040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3072 : Interval gbAtlas 4 3072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3104 : Interval gbAtlas 4 3104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3136 : Interval gbAtlas 4 3136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3168 : Interval gbAtlas 4 3168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3200 : Interval gbAtlas 4 3200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3232 : Interval gbAtlas 4 3232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3264 : Interval gbAtlas 4 3264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3296 : Interval gbAtlas 4 3296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3328 : Interval gbAtlas 4 3328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3360 : Interval gbAtlas 4 3360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3392 : Interval gbAtlas 4 3392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3424 : Interval gbAtlas 4 3424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3456 : Interval gbAtlas 4 3456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3488 : Interval gbAtlas 4 3488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3520 : Interval gbAtlas 4 3520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3552 : Interval gbAtlas 4 3552 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3584 : Interval gbAtlas 4 3584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3616 : Interval gbAtlas 4 3616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3648 : Interval gbAtlas 4 3648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3680 : Interval gbAtlas 4 3680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3712 : Interval gbAtlas 4 3712 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3744 : Interval gbAtlas 4 3744 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3776 : Interval gbAtlas 4 3776 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3808 : Interval gbAtlas 4 3808 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3840 : Interval gbAtlas 4 3840 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3872 : Interval gbAtlas 4 3872 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3904 : Interval gbAtlas 4 3904 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3936 : Interval gbAtlas 4 3936 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3968 : Interval gbAtlas 4 3968 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4000 : Interval gbAtlas 4 4000 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4032 : Interval gbAtlas 4 4032 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4064 : Interval gbAtlas 4 4064 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4096 : Interval gbAtlas 4 4096 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4128 : Interval gbAtlas 4 4128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4160 : Interval gbAtlas 4 4160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4192 : Interval gbAtlas 4 4192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4224 : Interval gbAtlas 4 4224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4256 : Interval gbAtlas 4 4256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4288 : Interval gbAtlas 4 4288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4320 : Interval gbAtlas 4 4320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4352 : Interval gbAtlas 4 4352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4384 : Interval gbAtlas 4 4384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4416 : Interval gbAtlas 4 4416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4448 : Interval gbAtlas 4 4448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4480 : Interval gbAtlas 4 4480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4512 : Interval gbAtlas 4 4512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4544 : Interval gbAtlas 4 4544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4576 : Interval gbAtlas 4 4576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4608 : Interval gbAtlas 4 4608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4640 : Interval gbAtlas 4 4640 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 4660 := (concat (concat (concat (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 (concat bgb_4_224 bgb_4_256)))) (concat (concat (concat bgb_4_288 bgb_4_320) (concat bgb_4_352 bgb_4_384)) (concat (concat bgb_4_416 bgb_4_448) (concat bgb_4_480 (concat bgb_4_512 bgb_4_544))))) (concat (concat (concat (concat bgb_4_576 bgb_4_608) (concat bgb_4_640 bgb_4_672)) (concat (concat bgb_4_704 bgb_4_736) (concat bgb_4_768 (concat bgb_4_800 bgb_4_832)))) (concat (concat (concat bgb_4_864 bgb_4_896) (concat bgb_4_928 bgb_4_960)) (concat (concat bgb_4_992 bgb_4_1024) (concat bgb_4_1056 (concat bgb_4_1088 bgb_4_1120)))))) (concat (concat (concat (concat (concat bgb_4_1152 bgb_4_1184) (concat bgb_4_1216 bgb_4_1248)) (concat (concat bgb_4_1280 bgb_4_1312) (concat bgb_4_1344 (concat bgb_4_1376 bgb_4_1408)))) (concat (concat (concat bgb_4_1440 bgb_4_1472) (concat bgb_4_1504 bgb_4_1536)) (concat (concat bgb_4_1568 bgb_4_1600) (concat bgb_4_1632 (concat bgb_4_1664 bgb_4_1696))))) (concat (concat (concat (concat bgb_4_1728 bgb_4_1760) (concat bgb_4_1792 bgb_4_1824)) (concat (concat bgb_4_1856 bgb_4_1888) (concat bgb_4_1920 (concat bgb_4_1952 bgb_4_1984)))) (concat (concat (concat bgb_4_2016 bgb_4_2048) (concat bgb_4_2080 (concat bgb_4_2112 bgb_4_2144))) (concat (concat bgb_4_2176 bgb_4_2208) (concat bgb_4_2240 (concat bgb_4_2272 bgb_4_2304))))))) (concat (concat (concat (concat (concat (concat bgb_4_2336 bgb_4_2368) (concat bgb_4_2400 bgb_4_2432)) (concat (concat bgb_4_2464 bgb_4_2496) (concat bgb_4_2528 (concat bgb_4_2560 bgb_4_2592)))) (concat (concat (concat bgb_4_2624 bgb_4_2656) (concat bgb_4_2688 bgb_4_2720)) (concat (concat bgb_4_2752 bgb_4_2784) (concat bgb_4_2816 (concat bgb_4_2848 bgb_4_2880))))) (concat (concat (concat (concat bgb_4_2912 bgb_4_2944) (concat bgb_4_2976 bgb_4_3008)) (concat (concat bgb_4_3040 bgb_4_3072) (concat bgb_4_3104 (concat bgb_4_3136 bgb_4_3168)))) (concat (concat (concat bgb_4_3200 bgb_4_3232) (concat bgb_4_3264 bgb_4_3296)) (concat (concat bgb_4_3328 bgb_4_3360) (concat bgb_4_3392 (concat bgb_4_3424 bgb_4_3456)))))) (concat (concat (concat (concat (concat bgb_4_3488 bgb_4_3520) (concat bgb_4_3552 bgb_4_3584)) (concat (concat bgb_4_3616 bgb_4_3648) (concat bgb_4_3680 (concat bgb_4_3712 bgb_4_3744)))) (concat (concat (concat bgb_4_3776 bgb_4_3808) (concat bgb_4_3840 bgb_4_3872)) (concat (concat bgb_4_3904 bgb_4_3936) (concat bgb_4_3968 (concat bgb_4_4000 bgb_4_4032))))) (concat (concat (concat (concat bgb_4_4064 bgb_4_4096) (concat bgb_4_4128 bgb_4_4160)) (concat (concat bgb_4_4192 bgb_4_4224) (concat bgb_4_4256 (concat bgb_4_4288 bgb_4_4320)))) (concat (concat (concat bgb_4_4352 bgb_4_4384) (concat bgb_4_4416 (concat bgb_4_4448 bgb_4_4480))) (concat (concat bgb_4_4512 bgb_4_4544) (concat bgb_4_4576 (concat bgb_4_4608 bgb_4_4640))))))))
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
theorem bgb_5_4224 : Interval gbAtlas 5 4224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4256 : Interval gbAtlas 5 4256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4288 : Interval gbAtlas 5 4288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4320 : Interval gbAtlas 5 4320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4352 : Interval gbAtlas 5 4352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4384 : Interval gbAtlas 5 4384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4416 : Interval gbAtlas 5 4416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4448 : Interval gbAtlas 5 4448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4480 : Interval gbAtlas 5 4480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4512 : Interval gbAtlas 5 4512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4544 : Interval gbAtlas 5 4544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4576 : Interval gbAtlas 5 4576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4608 : Interval gbAtlas 5 4608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4640 : Interval gbAtlas 5 4640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4672 : Interval gbAtlas 5 4672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4704 : Interval gbAtlas 5 4704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4736 : Interval gbAtlas 5 4736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4768 : Interval gbAtlas 5 4768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4800 : Interval gbAtlas 5 4800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4832 : Interval gbAtlas 5 4832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4864 : Interval gbAtlas 5 4864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4896 : Interval gbAtlas 5 4896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4928 : Interval gbAtlas 5 4928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4960 : Interval gbAtlas 5 4960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4992 : Interval gbAtlas 5 4992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5024 : Interval gbAtlas 5 5024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5056 : Interval gbAtlas 5 5056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5088 : Interval gbAtlas 5 5088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5120 : Interval gbAtlas 5 5120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5152 : Interval gbAtlas 5 5152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5184 : Interval gbAtlas 5 5184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5216 : Interval gbAtlas 5 5216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5248 : Interval gbAtlas 5 5248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5280 : Interval gbAtlas 5 5280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5312 : Interval gbAtlas 5 5312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5344 : Interval gbAtlas 5 5344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5376 : Interval gbAtlas 5 5376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5408 : Interval gbAtlas 5 5408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5440 : Interval gbAtlas 5 5440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5472 : Interval gbAtlas 5 5472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5504 : Interval gbAtlas 5 5504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5536 : Interval gbAtlas 5 5536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5568 : Interval gbAtlas 5 5568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5600 : Interval gbAtlas 5 5600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5632 : Interval gbAtlas 5 5632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5664 : Interval gbAtlas 5 5664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5696 : Interval gbAtlas 5 5696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5728 : Interval gbAtlas 5 5728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5760 : Interval gbAtlas 5 5760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5792 : Interval gbAtlas 5 5792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5824 : Interval gbAtlas 5 5824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5856 : Interval gbAtlas 5 5856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5888 : Interval gbAtlas 5 5888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5920 : Interval gbAtlas 5 5920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5952 : Interval gbAtlas 5 5952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5984 : Interval gbAtlas 5 5984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6016 : Interval gbAtlas 5 6016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6048 : Interval gbAtlas 5 6048 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 6049 := (concat (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 (concat bgb_5_192 bgb_5_224)) (concat bgb_5_256 (concat bgb_5_288 bgb_5_320)))) (concat (concat (concat bgb_5_352 (concat bgb_5_384 bgb_5_416)) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))) (concat (concat bgb_5_544 (concat bgb_5_576 bgb_5_608)) (concat bgb_5_640 (concat bgb_5_672 bgb_5_704))))) (concat (concat (concat (concat bgb_5_736 (concat bgb_5_768 bgb_5_800)) (concat bgb_5_832 (concat bgb_5_864 bgb_5_896))) (concat (concat bgb_5_928 (concat bgb_5_960 bgb_5_992)) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088)))) (concat (concat (concat bgb_5_1120 (concat bgb_5_1152 bgb_5_1184)) (concat bgb_5_1216 (concat bgb_5_1248 bgb_5_1280))) (concat (concat bgb_5_1312 (concat bgb_5_1344 bgb_5_1376)) (concat bgb_5_1408 (concat bgb_5_1440 bgb_5_1472)))))) (concat (concat (concat (concat (concat bgb_5_1504 (concat bgb_5_1536 bgb_5_1568)) (concat bgb_5_1600 (concat bgb_5_1632 bgb_5_1664))) (concat (concat bgb_5_1696 (concat bgb_5_1728 bgb_5_1760)) (concat bgb_5_1792 (concat bgb_5_1824 bgb_5_1856)))) (concat (concat (concat bgb_5_1888 (concat bgb_5_1920 bgb_5_1952)) (concat bgb_5_1984 (concat bgb_5_2016 bgb_5_2048))) (concat (concat bgb_5_2080 (concat bgb_5_2112 bgb_5_2144)) (concat bgb_5_2176 (concat bgb_5_2208 bgb_5_2240))))) (concat (concat (concat (concat bgb_5_2272 (concat bgb_5_2304 bgb_5_2336)) (concat bgb_5_2368 (concat bgb_5_2400 bgb_5_2432))) (concat (concat bgb_5_2464 (concat bgb_5_2496 bgb_5_2528)) (concat bgb_5_2560 (concat bgb_5_2592 bgb_5_2624)))) (concat (concat (concat bgb_5_2656 (concat bgb_5_2688 bgb_5_2720)) (concat bgb_5_2752 (concat bgb_5_2784 bgb_5_2816))) (concat (concat bgb_5_2848 (concat bgb_5_2880 bgb_5_2912)) (concat bgb_5_2944 (concat bgb_5_2976 bgb_5_3008))))))) (concat (concat (concat (concat (concat (concat bgb_5_3040 bgb_5_3072) (concat bgb_5_3104 (concat bgb_5_3136 bgb_5_3168))) (concat (concat bgb_5_3200 (concat bgb_5_3232 bgb_5_3264)) (concat bgb_5_3296 (concat bgb_5_3328 bgb_5_3360)))) (concat (concat (concat bgb_5_3392 (concat bgb_5_3424 bgb_5_3456)) (concat bgb_5_3488 (concat bgb_5_3520 bgb_5_3552))) (concat (concat bgb_5_3584 (concat bgb_5_3616 bgb_5_3648)) (concat bgb_5_3680 (concat bgb_5_3712 bgb_5_3744))))) (concat (concat (concat (concat bgb_5_3776 (concat bgb_5_3808 bgb_5_3840)) (concat bgb_5_3872 (concat bgb_5_3904 bgb_5_3936))) (concat (concat bgb_5_3968 (concat bgb_5_4000 bgb_5_4032)) (concat bgb_5_4064 (concat bgb_5_4096 bgb_5_4128)))) (concat (concat (concat bgb_5_4160 (concat bgb_5_4192 bgb_5_4224)) (concat bgb_5_4256 (concat bgb_5_4288 bgb_5_4320))) (concat (concat bgb_5_4352 (concat bgb_5_4384 bgb_5_4416)) (concat bgb_5_4448 (concat bgb_5_4480 bgb_5_4512)))))) (concat (concat (concat (concat (concat bgb_5_4544 (concat bgb_5_4576 bgb_5_4608)) (concat bgb_5_4640 (concat bgb_5_4672 bgb_5_4704))) (concat (concat bgb_5_4736 (concat bgb_5_4768 bgb_5_4800)) (concat bgb_5_4832 (concat bgb_5_4864 bgb_5_4896)))) (concat (concat (concat bgb_5_4928 (concat bgb_5_4960 bgb_5_4992)) (concat bgb_5_5024 (concat bgb_5_5056 bgb_5_5088))) (concat (concat bgb_5_5120 (concat bgb_5_5152 bgb_5_5184)) (concat bgb_5_5216 (concat bgb_5_5248 bgb_5_5280))))) (concat (concat (concat (concat bgb_5_5312 (concat bgb_5_5344 bgb_5_5376)) (concat bgb_5_5408 (concat bgb_5_5440 bgb_5_5472))) (concat (concat bgb_5_5504 (concat bgb_5_5536 bgb_5_5568)) (concat bgb_5_5600 (concat bgb_5_5632 bgb_5_5664)))) (concat (concat (concat bgb_5_5696 (concat bgb_5_5728 bgb_5_5760)) (concat bgb_5_5792 (concat bgb_5_5824 bgb_5_5856))) (concat (concat bgb_5_5888 (concat bgb_5_5920 bgb_5_5952)) (concat bgb_5_5984 (concat bgb_5_6016 bgb_5_6048))))))))
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
theorem bgb_6_992 : Interval gbAtlas 6 992 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 994 := (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 bgb_6_224))) (concat (concat (concat bgb_6_256 bgb_6_288) (concat bgb_6_320 bgb_6_352)) (concat (concat bgb_6_384 bgb_6_416) (concat bgb_6_448 bgb_6_480)))) (concat (concat (concat (concat bgb_6_512 bgb_6_544) (concat bgb_6_576 bgb_6_608)) (concat (concat bgb_6_640 bgb_6_672) (concat bgb_6_704 bgb_6_736))) (concat (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 bgb_6_864)) (concat (concat bgb_6_896 bgb_6_928) (concat bgb_6_960 bgb_6_992)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 22 := block_range (n:=22) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 22 := bgb_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 1 := bgb_8_0
theorem allgb : ∀ k ≤ 8, ∀ i < count gbAtlas k, checkRow gbAtlas k i = true := by
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

theorem boundgb (cert : Complete gbAtlas) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeeeee8fee0eee0feeeeee8fee0eee0feeeeee8fee0eee0feeeeee8fee0eee0feeeeee8fee0eee0feeeeee8fee0eee0feeeeee8fee0eee0feeeeee8fee0eee0
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 0 32) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,3,35)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,3,35)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277071592 * 2 ^ 32 + 4276154080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37211.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,4]⟩,⟨.or,[2,3]⟩,⟨.and,[3,4]⟩,⟨.and,[2,8]⟩,⟨.or,[4,7]⟩,⟨.and,[5,6]⟩,⟨.or,[0,9]⟩,⟨.and,[1,10]⟩,⟨.or,[7,11]⟩,⟨.or,[12,13]⟩,⟨.and,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071592 * 2 ^ 32 + 4276154080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071592 * 2 ^ 32 + 4276154080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37211

open PEqualNP.Outside.L_meta_37211 in
theorem PEqualNP.Outside.L_meta_37211 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071592 * 2 ^ 32 + 4276154080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071592 * 2 ^ 32 + 4276154080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
