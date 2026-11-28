import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36398.Model
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


end PEqualNP.Outside.L_meta_36398.Model

namespace PEqualNP.Outside.L_meta_36398
open PEqualNP.Outside.L_meta_36398.Model
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

def SBf (j : Nat) : Nat := [7, 7, 5, 7, 7, 6].getD j 0

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

end PEqualNP.Outside.L_meta_36398

namespace PEqualNP.Outside.L_meta_36398
open PEqualNP.Outside.L_meta_36398.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x16ab081868f300462c005ce1f200c02300215146200915140002f2cc088000010070064002006d2805015724009cf21122c01d0068000524d3221c00586000c04704060000f1e00300ff43fe43be43fd43fc43bc43ff42bf42fe42fd42bd42fc42ff32df32fe32fd32dd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x4d28750c0c0001e001e920000000080000001c66530004800004b80000930002c0000110d800004c80000003b280000000000005e2500000000000000201d0440000240004e5646800fa1b390ac420000000182800000000000138d60030134000000000005700269300000000ba004b020e200178001a4700000b00000000aa000000000001e9bd00003f0012a0000000003b51a89385f0021c02040b164e80000000000000150f8001f0000000000000000000000a9b440006e243420400001e104001d0000118004100000000000084a400000007b2e0008c0045000cc890005400790a0c800521c96c000000000004b00000d8000000000000000000000000000730000034a1308986a0028000009100000006e32800c60000000005a0000000310000116000000124003c040000000144006700000700035000120000000002a00000000a278000000000fcfe290000000001600000000000000000019068840011400000010c061f00274006d010000c00000011e83000004a86000000019000000000118710a2e3b8001e2d0000000002600000000000200000000200018000200000000400000000200000000205008000200000000003000000000000240000010000001008040200008000002004f94e439ea94873e5190e7aa121db94843b6a90873e5310f3ca621eb948439ea9087ad5210e5aa421cf944439ea80873e53d0a7ca3a14f543429eaa4855e5390abaa7214f14d42d7a92853c5150a7ea0a14f95042af298855d5310a7ea9994f15332cf21e659c43ccb3ea9996715332cfa16659d42cca7ca9194f55232aea9c65ad428ca7ea8994f15132cf21a659c434cb5a849967d5132ce2a265cf524cb3e84997390932cea1265cd424cb1a84994f950329eaa0655e530cabca720d754e419f29c839e539063ca720e754e419ea94839f329073a6520cf946419ea84833e531067aa420e7cc841ce990833e511076ca220cf540419f2a6633d54cc7388798db94b31b6a96633e548c67aa918cfd51319e2a2639c434c67ea818cf150319f2a6433d54c86bca790d754f219faa4433c548879a6510cfd51219e2a2433e540867aa810d794c21aea9843cd32086f4a010de540219f29e813d52d033e65a0674cb409f28e813d54902bea6a05714d40cfa9a813c5350338a6a04714d409fa92819f325033a64a04f14540dda82813e541027ea9984f153309f2a4613d548c33887184fd51309e2a2613e540c27aa8186710c30b7290616d520c2eca2185d544309f2a6413d54c82bca7905754f20e6996413e548827aa9104f951209eaa241cd324827ca8104f55020af298415d53082eca2105d544209faa6213c54c427ca9084f552109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | 1 => 0x18800690000092004f238880e0000000700b800009f00
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x3800000292802a655b500a458d30e5b330a98411045d18c002401d08bddb8060001f001800036dc82c38c401254b80000051013000110042000272c01d003c01a01601d400003c01a48b4032000008081144838104240010020005000c100c394d5210f0e63548438798e51d0a1c63543428d98754cca8d62d5332a598754cca8d62153328b195424ca8d6490932a3995424ca8c6550932a3185424ca8f60509329358a539062d6294e41a358a539070e6294e418758a539070d6294e418358a539061f65cca4187d95329070d524c8418718d501068d6210f31c310d52cc68d6210d318798f540c62d62150318e580540c61e63d5221c3d51328861e63d5121c355132087493254021c354932d021e639474093588535022d6214d40a3588535030e6214d4087588535030d6214d4083588535021c65cc94087195325022d6215330a3588438c21d6510c30a3588430c30c4354830c510d510c30d544cb208718d548821c63551208d185544830d544c9208798f54c421c6355210
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x120080c428000180e242c0a82b8cc6a9087219c6655093281ae431aa020c0d7298f5448606b94c728e81415c84354430818ecaa26490504715513248206b94c7aa621035c86355210
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
  | 6 => packedAt s0K6 (6+((h/1+packedAt s0K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s0K5 (912+((h/16+packedAt s0K5 (800+(h % 16)*7) 7) % 67)*7) 7
  | 4 => packedAt s0K4 (4950+((h/55+packedAt s0K4 (4455+(h % 55)*9) 9) % 381)*9) 9
  | 3 => packedAt s0K3 (2420+((h/20+packedAt s0K3 (2280+(h % 20)*7) 7) % 88)*7) 7
  | 2 => packedAt s0K2 (502+((h/3+packedAt s0K2 (490+(h % 3)*4) 4) % 15)*5) 5
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
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcfcfcc0fcccfcc0fcfcfcc0fcccfcc0fcfcfcc0fcccfcc0fcfcfcc0fcccfcc0fcfcfcc0fcccfcc0fcfcfcc0fcccfcc0fcfcfcc0fcccfcc0fcfcfcc0fcccfcc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36398
namespace PEqualNP.Outside.L_meta_36398
open PEqualNP.Outside.L_meta_36398.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x38008802c000004a00b803c000000000c80181c0000a4d2263ea04004208500000158000000010011180006ce80200000352000150001380003470600a8000002400000680004000900005000f0060022000000016000000000002000608000000c000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21ee21fd21fc21ec21ff40fe40fd40fc40ff30fe30fd30fc30ff20ef20fe20fd20ed20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x1e2a299e928009800c00100c88961ca12180048e00080e8418a3a71aa41f821094181b990000292817139480a880118000028013261d87a79c12000a998f8ba083a301002295858026a5a22b1b0d890b2aad1d2bac801f000024802c0006818525032007168d17951a0a112d860f000682002438400000000004180001c00806000031e9c180040c482cea18876e5210edaa421d794c42aea98853e540ca7aa8195794f41aea9e836e52d06daa5a0d794e41aea9c836f52506d8a4a0cf953319eaa6636e52cc6daa598cf952319eaa4636f524c6d8a498db94621b6a84433e540867aa810d794c21aea98437a50086f2a010eb95021d6aa043ce530879aa610db94421f328843ea50086daa010fa54021b4a80436e52902daa52057d4d40ae29a815e53102baa6205b94840b6a90817651102eaa2205b94a30b6a94613f544c278a8984f950309eaa0616e520c2daa4185d94430baa88613e54c827aa9905794f20aea9e41ae54c835aa9907394f20e6a9e416e51c82daa5105b14520f5a82416e52082dea5885b14b10b7294216d52843d241084fd51109e2a2215f53442b8a6885bd4910b629221e9204427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x60a0008ec020004030c350d5210f0d5454c21ca95150087295454021d294d50087495354021c355153c82686548110
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 8
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
  | 6 => packedAt s1K6 (6+((h/1+packedAt s1K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s1K5 (802+((h/14+packedAt s1K5 (704+(h % 14)*7) 7) % 99)*7) 7
  | 4 => packedAt s1K4 (2694+((h/30+packedAt s1K4 (2484+(h % 30)*7) 7) % 111)*8) 8
  | 3 => packedAt s1K3 (312+((h/2+packedAt s1K3 (304+(h % 2)*4) 4) % 16)*4) 4
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xc1ffff83ffff0f07f0fe1fffc3fff81e89f3f3
  | 2 => 0xfe1f0ffc3e1ffff87f0fe1c1fc383fff764c9f
  | 3 => 0xffe00fffc01ff1ff800ffe01ffc03fe1878f1c
  | 4 => 0xfffffe001fffff00001ffffc001f80fe0
  | 5 => 0xfffff000000001fffffffffe00000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x44020088040010008012024440488844009131
  | 2 => 0x88841110902a00283104208884111298324486
  | 3 => 0x144aaa290d548353888b54156a82a545858b18
  | 4 => 0x3954cc42a906a59d5aa11021b3270189d80ec0
  | 5 => 0x219888733198c9e66ccd993822040611ef6000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfafafaaafaaaf0a0fafafaaafaaaf0a0fafafaaafaaaf0a0fafafaaafaaaf0a0fafafaaafaaaf0a0fafafaaafaaaf0a0fafafaaafaaaf0a0fafafaaafaaaf0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36398
namespace PEqualNP.Outside.L_meta_36398
open PEqualNP.Outside.L_meta_36398.Model
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
  | 0 => 0xffffc0ff87f843f87f87fff87f07f8093f73c
  | 1 => 0xf0787ff0ff87ffc3f87f8703f87f83ff6cc9cf
  | 3 => 0xff807fff0007fffc007ff803ff8003ff8f0e0f
  | 4 => 0x7ffffff807ffff800003fffffc01f00ff0
  | 5 => 0xffff8000000007fffffffffc00000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x6110046210800804809809198091188c01531c
  | 1 => 0x250088a2400a0081882882288825092424c145
  | 3 => 0xc23551443555455c44555053550232598b0e0a
  | 4 => 0x8a466208a441566a55044082664a6011d00ca0
  | 5 => 0xc64438cc66667b3666664e0440c4061fea000
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaaeeeecc00eeeeeeaaeeeecc00eeeeeeaaeeeecc00eeeeeeaaeeeecc00eeeeeeaaeeeecc00eeeeeeaaeeeecc00eeeeeeaaeeeecc00eeeeeeaaeeeecc00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36398
namespace PEqualNP.Outside.L_meta_36398
open PEqualNP.Outside.L_meta_36398.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x28000000ce04008c0053e4832900994003c6c71510000213234d0c26012980e005912050001009c00f04584a43a890002e00a00008509c081184203ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10f710fe10fd10f510fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x14467e0048381600004a004c00002c5e6400080052000082005080000604626a000012263200401e0034000000000e1a7c000c7200000000106022766c280020006e3a000030184e007a422e02362478561c0054000068003e2a00740a3c5c000000000070665a44580e0808206001030204400000020200000060002dca521db54a43af29c855d5390a7ca9994f553329f2a4653d548caeea2995d14532e6990657a50906f2a120cf950319eaa0636e520c6daa418de94031bca80633e540867aa810d794c21aea98437a50086f2a010dd94640baa8c815e53102baa6205b94840b6a90817651102eaa2205d94630baa8c613f544c278a8984f950309eaa0616e520c2daa4185d94430baa88617651882eaa3104fd51209e2a2413e540827aa8105794c20aea98417651082eaa2104f953109eaa621b654c436aa9885d54610f9a8221f340443e080887c8c110f898221f220443e240885d94410
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0xa04600802009c580514cab264d4110b458c40442e16210110ac19130442b06448110
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 42
  | 4 => 66
  | 3 => 6
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
  | 6 => packedAt s3K6 (6+((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s3K5 (756+((h/14+packedAt s3K5 (672+(h % 14)*6) 6) % 56)*7) 7
  | 4 => packedAt s3K4 (1936+((h/22+packedAt s3K4 (1782+(h % 22)*7) 7) % 105)*8) 8
  | 3 => packedAt s3K3 (236+((h/2+packedAt s3K3 (228+(h % 2)*4) 4) % 9)*4) 4
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x3fe1fffc1fe3f8e1c71f8fff8fc1fc1e09f673
  | 1 => 0xc1fe0e3fe1fc7f1e07e3f1c1f1fe1fe036cb9c
  | 2 => 0x1fff03ffe007ffff803fe01fe001fffc70c1f
  | 4 => 0xfe00003fffff801ffffc0001ffffe001f80fe0
  | 5 => 0xffffffc00000001ffffffffe00000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x84242004440401000104824482444444005231
  | 1 => 0x9444a048c480a0240321908c9094494412c294
  | 2 => 0x288844910849500ac802241124089298c50c0a
  | 4 => 0x8194922114012535448002149298089680d40
  | 5 => 0x31118c039992649da693493800310311bfa000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xfefeeaeaeeeee0e0fefeeaeaeeeee0e0fefeeaeaeeeee0e0fefeeaeaeeeee0e0fefeeaeaeeeee0e0fefeeaeaeeeee0e0fefeeaeaeeeee0e0fefeeaeaeeeee0e0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36398
namespace PEqualNP.Outside.L_meta_36398
open PEqualNP.Outside.L_meta_36398.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x9200013000018017287440000891ab4e2c01c0034002504000a369020000000112aa4016001551934001984a303a03c3d089007c0131c2400970040c00002c0000ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x4c3507143b5700584f3e002b282244000a270000323433460429485100211a003d13083756491d1800001b031c16000939234500020000000e5a3c244b365059051701525406120000002600000d382c00400043003a4d0019200055312f2a53000f411e2e00002d30003f4e0b4a001025110000150c42471f00000c0800818089240400f04000800414a010c080050008305077a5090ef2a121cf943429eaa4857b5050af0a0a16bd4942dda82853c5050b70a0a14e141429f2a0853e548ca7aa9195dd4532ba28a653e540ca7aa8195d94432baa88657a500caf2a0195e94241bca84833e540c67aa818db94831b6a9063d5310c6f4a018de540319f2a6433d54c86bea690d714d219f2a0433d54086bca610d754c21bd2804379500867aa5204f94240af298815d53102dca4205b54840bb2888175511033ca6206754c40d7290813d521035aa4204b54840db28881b5511027ca0206e940409f2a6613d54cc2eca3185d54630dc204613f544c278a8986e101309f2a6413d54c835a85906e103209faa4413c548827ea8904f15120d6a12413e540827aa8105794c20aea98417651082eaa2106e100209f2a6213d54c42bca7085754e10dc204213f5444278a8886e10110
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x800049e6a201002610e000a00600000000bacc00a9400029c0240a00003001805830400c0001271a6314142c658c5050b326114142cc5845050a386055232d1549310c6386055321c394d521030d5354840ca18152103255294440c554d51103255254440aa588408c3315110230aa588404c2a86050b20aa58840c822c65509208e59440083195310020cc54440083195310210aa58840842a96210110
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x68200418458d6114142a12e6302a420521711815210310b12a2204618254d6210210
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 91
  | 3 => 25
  | 2 => 5
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (i*5) 5
  | 5 => packedAt s4K5 (i*16) 16
  | 4 => packedAt s4K4 (i*27) 27
  | 3 => packedAt s4K3 (i*38) 38
  | 2 => packedAt s4K2 (i*49) 49
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (6+((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s4K5 (788+((h/14+packedAt s4K5 (704+(h % 14)*6) 6) % 63)*7) 7
  | 4 => packedAt s4K4 (2667+((h/30+packedAt s4K4 (2457+(h % 30)*7) 7) % 121)*8) 8
  | 3 => packedAt s4K3 (998+((h/8+packedAt s4K3 (950+(h % 8)*6) 6) % 44)*6) 6
  | 2 => packedAt s4K2 (248+((h/1+packedAt s4K2 (245+(h % 1)*3) 3) % 7)*4) 4
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x1fe3fffc0f1c78e38f1f8fffc70e0e1e19f993
  | 1 => 0xe1fc1e3ff01fff1c0fe3f1c0f80fffe066c1fc
  | 2 => 0x1ffe03fffe07ffff003fe00fff00fff870e1f
  | 3 => 0xfe00003fffff801ffffc0000fffff001f80fe0
  | 5 => 0xffffffc00000001fffffffff00000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xc428c4046220910083048246c122624c085991
  | 1 => 0x4c494048a24820240521908a4804a4c422c0b4
  | 2 => 0x1080089104014009100224101240091085020a
  | 3 => 0x8012952248101252aa480024a4a94009580d40
  | 5 => 0x191318038c9a649f4c93493800c18191f7a000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xfeeafeeafce0fce0feeafeeafce0fce0feeafeeafce0fce0feeafeeafce0fce0feeafeeafce0fce0feeafeeafce0fce0feeafeeafce0fce0feeafeeafce0fce0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36398
namespace PEqualNP.Outside.L_meta_36398
open PEqualNP.Outside.L_meta_36398.Model
def s5K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x6802000bf42bd42fa10f910
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 4
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (i*5) 5
  | 4 => packedAt s5K4 (i*16) 16
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (6+((h/1+packedAt s5K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s5K4 (67+((h/1+packedAt s5K4 (64+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf0fe3fc7f078c71ce38f8fc3f8e1c38f1b3993
  | 1 => 0xff1fc3f8ff80ffe303f1f1fc1f01fff025c1fc
  | 2 => 0x1ffc00ffff07fffc01fe001ffe03ffc60e1f
  | 3 => 0xffe00000fffff803fffe00001ffffc00f80fe0
  | 4 => 0xffffffff00000003ffffffffe0000000fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x1642988813110a2021828248d82458a6091991
  | 1 => 0x224488012112000400909088490089220140b4
  | 2 => 0x888011244201401440124110248024846020a
  | 3 => 0x440132a48a40824aab24002294953004b80d40
  | 4 => 0x889123000c64a493d249493300182048f6a000
  | _ => 0
def s5Atlas : Atlas := ⟨5,rawDecor 31 s5Pos s5Neg, 0xfeeefce0feeefce0feeefce0feeefce0feeefce0feeefce0feeefce0feeefce0feeefce0feeefce0feeefce0feeefce0feeefce0feeefce0feeefce0feeefce0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36398
namespace PEqualNP.Outside.L_meta_36398
open PEqualNP.Outside.L_meta_36398.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c381821404000040850002380850000001007fd5009fe54007f55009fc54007fd4c07fe53007f54c07fc53027fd0c07fe43007f50c07fc43007fd4801fe52007f54801fc52027fd0801fe42007f50809fc4201ffcc801fe32007f4c807fc32007fd4405fe51007f54405fc51027fd0405fe41007f50405fc4101ffcc405fe31007f4c405fc31007fc8405fe21007f48405fc21007fd4003fe50007f54003fc50027fd0003fe40007f50003fc4001ffcc003fe30007f4c003fc30007fc8003fe20007f48003fc20017fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x864001ff8432000ff82190003ff65480017fb2a4000dfd9520004feca90003fe654800f7f32a4000ff59520005faca90003fc654800f7e32a4000df19520004f8ca90003ff64480017fb22400aff99120025fcc890003fd64480017eb22400aff19120025f8c890003ff5448015ff2a24000ff55120057f8a890003ff63480017fb1a4009ff98d2001dfcc690003fd63480017eb1a4009ff18d2001df8c690003ff5348013ff29a4000ff54d2004ff8a69002bff4348013ff21a4000ff50d2004ff88690006ff6248001ffa924000ff94920007dca490003fd5248001f6a924000ff14920057fe8490003fe4248001f72124000ff50920007da849002bfc4248013ff9924000ff8c920007fa6490027fc3248001ffb0a4000bfd8520047fcc29000afe6148001feb0a4008ff18520015f8c290003ff5148011ff28a4000ff54520047f8a29002bff4148011ff20a4000ff50520047f88290027ff3148011ff18a4000ff4c520047f86290003ff2148011ff10a4000ff48520047f84290006ff6048003ffa824001ff9412000ffaa090007fc5048003ffa024001ff9012000ffa8090007fc4048003ff9824001ff8c12000ff46090007fd3048001fc9824001ff0c12000ffe4090003fb2048003ff1024001fb8812000ff84090007ec2048003fc1024001ffc412000ffc2090007fa1048003fe0824000ffd9510005feca88003fe654400f7f32a2000ff59510005faca88003fc654400f7e32a2000ffd9110005fec88801bfe64440097f3222000ff59110005fac88801bfc64440097e3222000ffd5110037fca888003fd544400dfe2a22000ffd8d10005fec688017fe63440077f31a2000ff58d10005fac688017fc63440077e31a2000ffd4d1002ffca688003fd534400bfe29a2006ffd0d1002ffc8688003fd434400bfe21a2000ffd8910005fec488003fe62440017f3122000ff58910005fac488003fc62440017e3122000ffd4910007fca488003fd5244001fe2922006ffd0910007fc8488003fd424400dfe2122005ffcc910007fc6488003fd324400bfe1922001bfd8510017fea28800bfe5144005fb28a2002ff54510007eaa28800bfc5144005ffa0a2002ff90510017ec828800bfd4144001faa0a2002ff10510017fe6288017f73144005ff18a2002ff4c510017f8628800bf43144005ff90a2002ff88510017ec428800bfd2144001fa90a2002ff0851000dfec088007ff5044001fda822001ff9411000ffaa088007fc5044003fc2822001ffd011000ffc8088007fa4044003fea022000fe5011000ff88088007ff3044003ff1822001fe8c11000ffa6088003f93044003fe1822001ffc811000ffc4088007fa2044003fe9022000fe4811000ff84088007ff1044005fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x7fc3150001ff90a8011ff88540007fa42a0047fc21500037fb028001ffd414000ffca0a0007fd5050003fe2828001ffd0140027f680a0007fe4050003df2028001ff1014000f7880a0007f84050003ff9828001ff8c14000ff860a0007fe2050003fe1028001ffc414000ffc20a0007fa1050003fe0828000ffd9530005feca98003fe654c00f7f32a6000ff59530005faca98003fc654c00f7e32a6000ffd9130005fec898043fe644c0097f3226000ff59130005fac898043fc644c0097e3226000ffd5130087fca898003fd544c021fe2a26001bfd8d3001ffea69800ffe534c007ef29a6003ff54d30007baa69800ffc534c007ffa1a6003ff90d3001fbc869800ffd434c001eea1a6003ff10d30007fec498002ff624c001ff3126000ff58930007f8c498002fc624c001ffa926000ff94930007faa498003fc524c021ffa126000ff90930007fa8498043fc424c007ff9926003f7cc93001ffc649800ffd324c001ee9926003ff0c930007fec298002ff614c01fff30a6002bf98530007fac29803ffc614c0057e30a6000ffd453007ffca298003fd514c01ffe28a6010ffd053007ffc8298003fd414c01ffe20a6003ffcc53001ffc629803fde314c007fe98a6003ff0c53001fb86298003ff214c01fff10a6000ff4853007ff84298006ff604c003ffa826001ff9413000ffaa098007fc504c003ffa026001ff9013000ffa8098007fc404c003ff9826003fecc13000ffc6098007de304c003fe1826001f70c13000ff06098007fe204c003fd1026001ff0813000ffe2098007fe104c003fd0826001ff0413005ffecb90002ff65c8001ff32e4007bf99720007facb90002fd65c8017fe32e4007bf1972005ffec990002ff64c801dff3264004bf99320007fac990002fd64c8017fe3264004bf19320007fea99003bfe54c8001feaa6400eff1532005ffec790002ff63c801bff31e4003bf98f20007fac790002fd63c8017fe31e4003bf18f20007fea790037fe53c8001fea9e400dff14f20077fe8790037fe43c8001fea1e400dff10f2000dfcc590003ff52c8017ff2964000fb94b20007faa590003ed52c8017fe296400effd0b2005ffc8590003ee42c8001fea164000fb50b2005ff88590037ff32c8017ff1964000ff4cb2005ff8659002fff61c8019ff30e4002bf98720007fac390002fd61c8017fe30e4002bf18720007fea390033fe51c8001fea8e400cff14720077fe8390033fe41c8001fea0e400cff1072006ffe6390033fe31c8001fe98e400cff0c72005ffe4390033fe21c8001fe90e400bff0872000dfac190007ff50c8003ff2864001ff5432000ff8a190007ff40c8003ff2064001ff5032000ff88190007ff30c8003ff1864001ff4c32000ff86190007fe20c8003f71064001fe8832000ff84190007ec20c8003ff8
  | 2 => 0x5003ffac5a8002fd62d400ffe316a007ffd4b5003efea5a801ffe52d400ffea96a000df54b5003ff8a5a8063ff42d4001ff216a000ff50b500c7f885a805fff32d4001ff196a000ff4cb500bff865a801fff61d400fff30ea002bf9875003ffac3a8002fd61d400ffe30ea002bf1875003ffea3a801ffe51d400ffea8ea007ff147500c7fe83a805bfe41d4001fea0ea016ff107500bffe63a805bfe31d4001fe98ea016ff0c750007fe43a805bfe21d4001fe90ea016ff0875000dfac1a8007fe50d4003bf286a001fe9435000ff8a1a80077c50d4003ffa06a001ff9035000ff881a8007ff30d4003ff186a001ff0c35000ffc41a8007fc20d4003ff886a001ff8435000ff421a8007fc10d40037fb2aa000ffd9150005fec8a8057fe64540097f322a000ff591500aff8c8a8012fc645400fffaa2a000dfd51500affca8a8003fd5454001beaa2a007ff15150007fec6a8002ff6354029ff31aa003bf98d50007fac6a8053fc63540077e31aa007ffd4d500a7fca6a8003fd535400ffe29aa015ffd0d500a7fc86a8003fd4354029fe21aa000ffd8950005fec4a8003fe6254001feb12a000ff18950005f8c4a801fff5254001bfa92a000ff94950007faa4a80037d525400ffe292a015ffd0950007fc84a8003fd425402bfe212a014ffcc950007fc64a8003fd3254029fe192a000ffd8550005fec2a804ffe61540057f30aa000ff5855009ff8c2a800afc615400fffa8aa013ff94550007faa2a801ffc515402bffa0aa013ff90550007fa82a804ffc4154029ff98aa013ff8c550007fa62a804ffc3154001ff90aa013ff88550007fa42a804ffc21540037fb02a001ffd415003ff6a0a8007fe5054003bf282a001ff1415000ef8a0a8007f85054003ffa02a001ff9015000ff880a8007ff3054003ff182a001ff0c15000ffc40a8007fc2054003ff882a001ff8415000ff820a8003ff65500017fb2a8000dfd9540004fecaa0003fe655000f7f32a8000ff59540005facaa0003fc655000f7e32a8000df19540004f8caa0006ff6450009ffaa28004ff951400277ca8a0013fd5450001deaa28004ff15140007fec6a0002ff6350025ff31a8003bf98d40007fac6a004bfc63500077e31a8000ffd4d40097fca6a0003fd5350025fe29a8004ffd0d40027fc86a0013fd4350009fe21a8000ffd8940005fec4a0003fe6250001feb128000ff18940005f8c4a0003ff5250001ff2928000ff54940007f8a4a0013ff4250009dfa128004ff90940027fa84a0003bd4250009fe2128012ffcc940007fc64a0003fd3250025fe1928000ffd8540005fec2a0047fe61500057f30a8000ff5854008ff8c2a000afc6150001ffa8a8011ff94540007faa2a0047fc5150009ffa0a8004ff90540027fa82a0013fc4150025ff98a8011ff8c540007fa62a004
  | 3 => 0xfb2e4200ff9972103dfccb90803fd65c84017eb2e420bff1972103df8cb9082fff64c84017fb26421eff99321025fcc990803fd64c84017eb26420bff19321025f8c990803ff54c843dff2a64200ff553210f7f8a99082fff63c84017fb1e421dff98f2101dfcc790803fd63c84017eb1e420bff18f2101df8c790803ff53c843bff29e4200ff54f210eff8a79087bff43c843bff21e4200ff50f210eff8879080afe62c8401ffa96420bff94b21007faa59082ffc52c843dffa16420bff90b21007dc8590803fd42c8401f6a16420bff10b210effe659082ffe32c8401f71964200ff4cb21007da659082ffc32c84057eb0e4202ffd4721017fca39080bfd51c8405fe28e4202ffd0721017fc839080bfd41c8405fe20e4202ffcc721017fc639080bfd31c8405fe18e4202ff88721017dc439080bf621c8405fe10e4202fb0872105ffec190873fe60c84037f3064200ff58321005fac19082ffc60c84037e306421cff943210e7f8a19087bff40c8439ff206421cff103210effe6190873fe30c8439fe186421cff8832105ff8419080bff10c8405ff0864202ff04321007feca90802ff6548401ff32a4207bf99521007faca90802fd6548401fe32a4207bf19521007fec890802ff6448437ff3224204bf99121007fac890802fd6448437fe3224204bf19121007fea89086ffe5448401feaa2421bff15121007fec690802ff6348401efb1a4200b7d8d210d7fcc69080efe6348401feb1a4200bf58d210d7f8c69080efc6348401ee31a4203b718d21007fea69086bfe5348401fea9a421aff14d210dffe869086bfe4348401fea1a421aff10d21015fec490803ff5248401ff2924200ff54921007f8a49086fff4248401ff2124200fb90921007fa8490803ed4248437fe212421affcc921007fc6490803ee3248401fe9924200fb4c9210d7f8649080aff6148405ffa8a4202ff94521017faa29080bfc5148405ffa0a4202ff90521017fa829080bfc4148405ff98a4202ff8c521017ec629080bfd3148401fa98a4202ff0c521017fe4290803f72148405ff10a4202fb88521017f8429080bec2148405fa10a4200ffd8121005fec090867fe60484037f3024200ff581210cff8c090806fc6048433ff2824219ff141210dffe8090867fe4048433fe202421affcc1210cffc6090867fc3048433ff1024219ff08121017fe209080bf71048405ff0824202ff0412100dfccba801fff64d400fff326a004bf9935003ffac9a8002fd64d400ffe326a004bf1935003ffea9a801f7f54d400fff2a6a007ff55350006faa9a801ffc54d400fffb1ea007ff98f5001dfcc7a801ffd63d40017eb1ea007ff18f5001df8c7a801fff53d400fff29ea007ff54f5003ff8a7a8063ff43d402fff21ea000ff50f500bff887a801fff62d400fff316a000bf98b
  | 4 => 0x803fe3254401fe992a224ff0c951015fec2a880bff515440ffba8aa202ff94551016fca2a880bfc5154405be28aa202fd14551017fe82a880bfe4154405fe20aa202ffcc551017fc62a880bfc3154405ff10aa202ff08551007fec0a8802ff6054447ff302a201bf98151007fac0a888ffc60544037e302a223ff9415111efca0a881ffc5054447be282a225ffd015111ffc80a888ffc4054449ff982a223ff8c15111ff860a888ffe2054447fe102a202ffc4151017ee20a880bfe1054405fe082a200ffd9541005fecaa0803fe655040f7f32a8200ff59541005facaa0803fc655040f7e32a8202bfd9141027fea8a0813fe5450409feaa28204ff15141007fec6a0802ff6350445ff31a8203bf98d41007fac6a088bfc63504077e31a8200ffd4d41117fca6a0803fd5350445fe29a8204ffd0d410277e86a0813fe4350409fea1a8200ef50d41027f886a0803ff62504017fb128200ff98941007fac4a0803fc62504017e3128200ffd4941007fca4a0803fd5250401fe2928204ffd09410277e84a0813fe4250409fea128200ef50941027f884a088bff3250401ff1928200ff4c941117f864a080aff6150405ffa8a8202ff94541017faa2a080bfc5150405ffa0a8204fdd0541017fc82a080bbe4150405fe20a8202ef10541017e882a080bff3150405ff18a8202ff0c541017fc42a080bfc2150401ffb028200bfd814110ffcc0a0806fe6050401feb028221ff1814100df8c0a0887fe5050443fe2828204ffd0141027fc80a0813fc4050445ff9828221ff8c14110ff860a0887fe2050443fe1028202ffc4141017ee20a080bfe1050405fe0828200ffd9531005feca98803fe654c40f7f32a6200ff59531005faca98803fc654c40f7e32a6200ffd9131005fec898883fe644c4097f3226200ff59131005fac898883fc644c4097e3226200ffd5131107fca898803fd544c441fe2a26202bfd8d3101ffea69880ffe534c407fea9a6203ff14d3101ffe869880ffe434c407ef21a6203ff50d31007ba869880ffc434c401ffb126200bfd8931007fcc498803fd624c401fe3126200bf18931007fea498803fe524c401fea926200ff14931107fe8498803fe424c401fea126220ff1093101ffe649880fdf324c407ff1926203ff4c931007ba649880ffc324c4057fb0a6202ffd4531017fca29880bfd514c405fe28a6202ffd0531017fc829880bfd414c405fe20a6202ffcc53101fee629880bfe314c405ef18a6202ff0c531017b8629880bf4314c405ff10a6202fd88531017f84298803ff604c4017fb02621fff9813100dfcc098803fd604c43ffe3026201bf181310fffca09887ffc504c441ffa02621fff901310fff8809880fff304c407ff1826203ff0c1310fffc409887ffc204c405ff8826202ff84131017f8209882fff65c84017
  | 5 => 0x4232167fc21190b3fc108c801ffb2a6400bfd9532007fcca9901efe654c801feb2a6400bf59532007f8ca9901efc654c801ffb226400bfd913215ffcc899012fe644c801feb226400bf5913215ff8c899012fc644c801ffaa2642bff95132007faa8990affc544c8077fb1a6403ffd4d3201ffca69900ffd534c807fe29a6403ffd0d3201ffc869900ffd434c807fe21a6403bfd8932007fea499003fe524c801fea926400ff1493215ffe8499003fe424c801fea12642bff1093201ffe649900fef324c807ff1926400f78c93201ff8649900fdc324c807f61926400ffd8532005fec2990abfe614c8057f30a6400ff58532157f8c29900afc614c855ff28a642aff1453215ffe82990abfe414c855fe20a6403ffcc53201fbe629900ffe314c807fe18a642aff88532157f84299003ff604c8017fb026429ff9813200dfcc099003fd604c853fe3026401bf1813214ffca0990a7fc504c857ffa026429ff9013214ff8809900fff304c807ef9826403ff8c13201ff860990a7fe204c853fe102642affc413214ffc20990a7fc104c8057f32ea207ffd935103ffcc9a8812fe64d440ffeb26a200bf5935103ff8c9a8812fc64d440fffaa6a207dfd535103ffca9a881ffd54d4401beaa6a207ff1535103ffec7a881ffe63d44077f31ea207ff58f51005fac7a881ffc63d44077e31ea207ffd4f5103efea7a881ffe53d440ffea9ea200df54f5103ff8a7a88a3ff43d444fff21ea200ff50f5113ff887a881fff62d440fff316a200bf98b5103ffac5a8802fd62d440ffe316a207ffd4b5103efea5a881ffe52d440ffea96a200df54b5103ff8a5a88a3ff42d4401ff216a200ff50b51147f885a889fff32d4401ff196a200ff4cb5113ff865a880afd61d4405ff28ea202df94751017eca3a880bfc51d4405be28ea202ffd0751017fc83a880bfc41d4405ff98ea202ff8c751017f863a880bfe21d4405fe10ea207ffd835103ffcc1a8806fe60d440ffeb06a200bf5835103ff8c1a8806fc60d440fff286a226df9435103ff8a1a881f7c50d4451ffa06a226ff90351137f881a889fff30d444dff186a226ff0c351137fc41a889bfc20d4405ff886a202ff84351017f821a880aff6554401ffb22a200bfd915112ffcc8a8812fe6454401feb22a225ff19151025f8c8a881fff5454401bfaa2a225ff95151007faa8a88037d545440ffe2a2a200ffd8d51005fec6a8893fe63544077f31aa200ff58d51127f8c6a880efc635440fffa9aa200dfd4d51127fca6a8803fd5354401bea9aa207ff14d5112ffe86a8893fe4354401fea1aa224ff10d51007fec4a8802ff6254401ff312a200ff58951007f8c4a8802fc625440fffa92a200dfd4951007fca4a8803fd5254401bea92a207ff1495112ffe84a8803fe4254401fea12a225ff10951127fe64a8
  | 6 => 0x1fea9c8434ff14e42027fe8721013fe4390809fea1c8404ff10e42025fcc521003ff5290817ff2948400ff54a4205ff8a521013ff4290809dfa148404fbd0a4205ff88521013ec4290869ff994840bff0ca4205ffec3210cffe61908057f30c8400ff58642005fac32102ffc61908057e30c8433ff9464219ff8a321013ff4190809ff20c8404ff106421a7fe63210cffe3190867fe18c8433ff8864205ff8432102fff6090865ff3048401bf98242007fac121002fd6090817fe3048401bf18242197fca1210cbfc5090809ffa048404ff90242027f881210d3ff3090865ff1848432ff0c242197fc412102ffc2090867ff8848432ff84242197f82121003ff65508017fb2a8400ff9954203dfccaa1003fd65508017eb2a8400ff1954203df8caa1012ff6450809ffaa28400efd5142027fca8a1013fd5450809fe2a28404ef15142007fec6a1002ff6350863ff31a8403bf98d42007fac6a10c7fc63508077e31a8400ffd4d4218ffca6a1003fd5350863fe29a8404ffd0d420277e86a1013fe4350809fea1a8400ef50d42027f886a1012ff6250801ffa928400ff94942007faa4a1003fc5250809ffa128404fbd0942027fc84a1003be4250809fe2128404ef10942027d884a10c7ff3250863fe1928400ffd8542005fec2a10c3fe61508057f30a8400ff58542187f8c2a100afc6150861ff28a8430ff14542027fe82a1013bf4150809ff20a8404ff1054218ffe62a10c3fe3150861fe18a8430ff88542187f842a1003ff60508017fb02842fff9814200dfcc0a1003fd605085ffe3028401bf1814217ffca0a10bffc5050809ffa028404efd0142027fc80a1013fc4050863ff982842fff8c14217ff860a10bffe205085ffe1028430ffc414217ffc20a10bffc1050817ffb2c6400bfd9632007fccb1901efe658c801feb2c6400bf5963205ff8cb1901efc658c817ffb246400bfd9232177fcc919012fe648c801feb246400bf5923205ff8c919012fc648c801ffaa4642eff95232007faa9190bbfc548c8077eb1c6403ffd4e3201ffca71900ffd538c807fe29c6403ffd0e3201ffc871900fde438c807fea1c6400f750e3201ff8871900efe628c801ffa94640bff94a32007faa51902ffc528c85dffa14640bff90a32007fa851902ffc428c807ff9946403f7cca3201fde651902ffc328c807f6194640bffd863216ffcc31900afe618c801feb0c6400bf5863205ff8c31900afc618c85bff28c642dff14632177fe83190b7fe418c85bfe20c6403ffcc63201ffc63190b7de318c807fe18c6403f70c63216ffc431902ffc218c817ffb04642cff9823200dfcc119003fd608c8017eb04640bff1823200df8c1190b3fe508c859fe284642effd0232167fc81190b3fc408c807ff9846403ff8c23201ff861190b3fe208c817fe104642dffc
  | 7 => 0x2902ffc3294817ffb0ca43eff98652015fcc329003fd61948017eb0ca40bff18652015f8c3290fbfe519480ffe28ca440ffd06521f7fc83290fbfc419487fff98ca43eff8c6521f7f863290fbfe2194817fe10ca40bffd82521effcc129006fe6094801feb04a400bf5825205ff8c129006fc609487bff284a43ddf9425203ff8a1290f77c5094881ffa04a43dff902521eff881290ffff309487bff184a43dff0c2521effc412902ffc209487dff884a43dff842521eff82129003ff64548017fb22a43cff99152025fcc8a9003fd6454879fe322a404bf1915203ffea8a90f3fe5454879bf2a2a400ff5515203ff8a8a90f37c5454801ffb1aa400bfd8d521dffcc6a900efe6354801feb1aa43bff18d5201df8c6a901fff5354801bfa9aa43bff94d52007faa6a90037d535480ffe29aa43cffd0d521dffc86a9003fd4354877fe21aa407ffd495203fdea4a9003fe5254801bf292a43cffd09521e7f884a90efff3254877fe192a400ffd8552005fec2a90ebfe61548057f30aa400ff585521d7f8c2a900afc6154875ff28aa407ff145521e7fe82a90ebfe4154875fe20aa43bffcc5521d7fc62a90ebfc3154875ff10aa43aff08552007fec0a9002ff6054873ff302a401bf98152007fac0a90e7fc60548037e302a439ff9415203ff8a0a90f3ff4054873ff202a439ff101521dffe60a90e7fe3054873fe182a439ff881521cff840a90ebff1054873ff082a439ff0415203dfcca2902fff641480fff320a404bf9905203ffac829002fd6414817fe320a404bf1905203ffea82901f7f541480fff2a0a407ff55052006faa82901ffc5414817ffb18a407ff98c5201dfcc62901ffd63148017eb18a40bff18c5201df8c62901fff531480fff298a407ff54c5203ff8a6290e3ff431486fff218a400ff50c521bff88629002fe621480fffa90a407dfd485205ffca42901fee521480ffea90a400df5485203fdaa4290e3ff4214817fe210a437ffcc85205ff8642902fff611480fff308a402bf9845203ffac229002fd6114817fe308a402bf1845203ffca22901ffc5114871ffa08a436ff904521b7f882290dfff311486dff188a436ff0c4521b7fc422902ffc2114817ffb00a407ff9805200dfcc02901ffd60148017eb00a40bff1805200df8c02901ffe501486bbf280a407ff1405203ef8a0290e3ff401486bff200a435ff100521bffe60290d7fe301486bfe180a435ff8805205ff840290dbff101486bff080a435ff0405205ffecb21002ff6590801ff32c8407bf99642006fccb210027e6590801feb2c8400bf59642006facb210027d6590817fe32c8407bf19642025fac921013ff5490809ff2a48404ff55242027f8a92102fff6390869ff31c8403bf98e42007fac721002fd6390817fe31c8403bf18e42007fea7210d3fe539080
  | 8 => 0xfcc55301ffc62a980ffc3154c91ff10aa648ff08553007fec0a9802ff6054c8fff302a601bf98153007fac0a991ffc6054c037e302a647ff9415323efca0a981ffc5054c8fbe282a649ffd015323ffc80a991ffc4054c07ff982a603f7cc15301ffc60a980ffc3054c8fff102a647ff08153247fe20a991ffe1054c8ffe082a600ffd9543005fecaa1803fe6550c0f7f32a8600ff59543005facaa1803fc6550c0f7e32a8603bfd9143027fea8a1813fe5450c09df2a28604ff551430077aa8a1813fc5450c077fb1a8603ffd4d4301ffca6a180fde5350c07fea9a8600f754d4301ff8a6a180fff4350c09efa1a8603ff90d4301f7c86a180ffc4350c07de21a8603f710d43007fec4a1802ff6250c01ff3128600ff58943007f8c4a1802fc6250c09ffa128604efd0943027f884a180fff3250c07fe1928603f70c943007fec2a1802ff6150c8dff30a8602bf98543007fac2a191bfc6150c057e30a8646ff94543237f8a2a1813ff4150c09dfa0a8604ff90543027f882a180fff3150c07ef98a8603ff8c54301ff862a191bfe2150c8dfe10a8600ffd8143005fec0a1917fe6050c037f3028600ff5814322ff8c0a1806fc6050c8bff2828645ff14143027fe80a1813fe4050c8bdf2028604ff101430277880a180fff3050c07ef9828603ff8c14301ff860a1917fe2050c8bfe1028646ffc414322ffc20a1917fc1050c0fffb26a407ff99352025fcc9a901ffd64d48017eb26a407ff19352025f8c9a901fff54d480fff2a6a444df9535203ffaa9a901ffc54d480fbe2a6a407ffd8f5203ffcc7a900efe63d480ffeb1ea400bf58f5203ff8c7a900efc63d480fffa9ea407dfd4f5203ffca7a901ffd53d4801bea9ea407ff14f52227fe87a910ffe43d4801fea1ea443ff10f52227fe85a9113fc42d4887ff996a443ff0cb5203ffec3a901ffe61d48057f30ea407ff58752005fac3a901ffc61d48057e30ea407ff9475203ff8a3a9113ff41d4885ff20ea442ff1075221ffe63a910bfe31d4885fe18ea442ff88752217f843a901fff60d480fff306a401bf9835203ffac1a9002fd60d480ffe306a401bf1835203ffca1a901ffc50d4889ffa06a441ff9035220ff881a910fff30d4883ff186a441ff0c35220ffc41a9107fc20d4885ff886a441ff8435220ff821a9002fd6594817ffb24a440ff99252025fcc929003be64948095f324a400ff59252005fac929003bd64948015eb24a40bff19252025f8c92901fff5494801bfaa4a440ff95252007faa9290037d549480ffe2a4a40bffd8e521fffcc72900efe6394801feb1ca400bf58e5205ff8c72900efc639480fffa9ca43fff94e52007faa72901ffc5394881ffa1ca43fff90e52007fa87290fffc439480f7f314a407ffd4a52006fea52901fef5294881ffa14a40bff10a521fffe65
  | 9 => 0x57e30ea807ff9475403ff8a3aa013ff41d5009ff20ea804ff10754297fe63aa147fe31d50a3fe18ea851ff8875428ff843aa01fff60d500fff306a801bf9835403ffac1aa002fd60d500ffe306a801bf1835403ffca1aa01ffc50d5009ffa06a804ff90354027f881aa14bff30d50a1ff186a850ff0c354287fc41aa143fc20d50a3ff886a850ff84354287f821aa012ff65550097fb22a804ffd515403f7ea8aa013fe5455009bf2a2a804ff15154026f8a8aa013bc5455001ffb1aa800bfd8d5427ffcc6aa00efe6355001feb1aa84fff18d5401df8c6aa13ffe535500ffe29aa804ffd0d540277e86aa013fe4355009fe21aa800ffd8954005fec4aa003fe6255001feb12a800ff18954005f8c4aa013ff4255009fe212a84fffcc95427ff864aa003ff61550017fb0aa84eff98554015fcc2aa003fd615509dfe30aa802bf18554277fca2aa01ffc5155009ffa0aa804ff90554027f882aa13fff315509dff18aa84eff0c554277fc42aa13bfc2155001ffb02a800bfd815426ffcc0aa006fe6055001feb02a84dff1815400df8c0aa137fe505500ffe282a804ffd01540277e80aa013fe4055009fe202a84fffcc15426ffc60aa137fc305509bff102a84dff08154277fe20aa137fe105509bfe082a803bf9975303ffec9a981ffe64d4c097f326a607ff59353005fac9a981ffc64d4c097e326a607ffd535303efea9a981ffe54d4c0ffeaa6a600df5535303ff8a9a980efd63d4c07ff29ea603df94f5301fbca7a980ffc53d4c07be29ea603ffd0f5301ffc87a980ffc43d4c0fffb16a607ff98b53005fcc5a981ffd62d4c017eb16a607ff18b53267fe85a9933fc42d4c07ff996a603ff0cb5303ffec3a981ffe61d4c057f30ea607ff58753005fac3a981ffc61d4c057e30ea607ff9475303ff8a3a9933ff41d4c97ff20ea64bff1075301ffe63a980ffe31d4c07fe18ea64bff8875325ff843a981fff60d4c0fff306a601bf9835303ffac1a9802fd60d4c0ffe306a601bf1835303ffca1a992b7e50d4c0ffe286a607df14353267fe81a992bfe40d4c95fe206a603ffcc35301ffc61a980ffc30d4c95ff106a64aff0835325ffe21a992bfe10d4c95fe086a603bfd9553007fec8a9802ff6454c93ff322a604bf99153007fac8a9927fc6454c097e322a607ffd5153006fea8a9927fe5454c01feaa2a600df5515303ff8a8a980eff6354c07ffa9aa607f7d4d5301ffca6a980f7e5354c07fe29aa603df14d5301fb8a6a980fff4354c07ff21aa603f790d5301ff886a9803ff6254c017fb12a600ff98953007fac4a9803fc6254c017e312a649ffd095324ff884a980fff3254c07fe192a600ffd8553005fec2a9923fe6154c057f30aa600ff58553247f8c2a980afc6154c91ff28aa607ff1455324ffe82a9923fe4154c91fe20aa603f
  | 10 => 0x10000002000800400000000000000020010000000004000000000000000300400000000040020000000000000000c00200000000100000030020008002000000800000000000080000000000000000014003000001000000100180000040050000000004008000800800600300000000080000018000004003001000000200000180080000020008000002000000800000000600000040040000000000000000000800000000000280000020010000028002000000000c00a000000000000800000080040040000010000000000001800400000000000180000010008000000000001000001600100000040040020008008008000000000000200500200000060090000008008001000800c00e000002800800800000000000040020010000004001000800400e00000300000000000000000000000000800c000001000000c0060030008000000000000800c00600000000000000010018000000000000001800000000000040000000000018000006000000400400000000000080000020020000000000801400000000100000000030000000000005001002400400e00080040020000018000008000000000800000000080000120000038000000000000000c0080050000008000002000000c000001000000000200000000040080010000004000002003800000400000000080040000000000000001000800c000002000801000000100580040000000000000002003000000800000000500080000010008004002001004000000000200080000060020000000000000000000400000000000000000040000000000000001800800200000480080000000000000000000000002c004006000000000400000000040020000000000000000000000000000100000040000010000004000002000000000000000000000020000008008000001000000000a002000000c000000001000000000500700000000000000004000001000000400600000180100000000020000000000000801000000000300000000000000000002000001801001c00000180000040040030010006000000000000200100000000000020020004002002000000000200000000040000000008000000001000000400000000000080060010000010002000000000400400000200000000000008020004001001800000c002000812fe65d50097eb26a804ff95354026fca9aa013be54d50099f2a6a804ff15354026f8a9aa01fff63d500fff31ea803bf98f5403ffac7aa002fd63d500ffe31ea803bf18f5403ffca7aa01ffc53d5009ffa1ea804ff90f54027f887aa01fff62d500fff316a800bf98b5403ffac5aa002fd62d500ffe316a804ffd0b540277e85aa013fc42d50a5ff996a852ff0cb5403ffec3aa01ffe61d50057f30ea807ff58754005fac3aa01ffc61d5
  | 11 => 0xc80ffc1e234980000000000000000000104000111017600034100000000000001dbcda00000000fb80000003f180000000002120001088473000074508a00000000000000000e780000000003bd1cb400000008e0ad80000000000000000767000000035400038d800000043c08b133c55a0000e40960000000000000000000017d00000000000000fa0000000000152c0000000000000000783000000115e63500014e00000003e500000000001780000000000000000000000000022d00e800000008100000000e3135cf6c000000000000011d00000000006980000ca80006df0000000000000000000000000000000005ea4e703580000006cb0000000000115000000000000009c0e800000ce2e5800032840b00021b468a000000000000000000000000000000000ba400024400000000002e722b061c382000373857c4b85de22281d806000003c11d43f0831000000000000000008b0c880130a5003036055507210cc0005dd0000000000000000000000063035702940000000000444cf0000000000000000010e1a3492429034a000096025d0001ac4ae80001b9000000000011da14010e0000000eccbd60000001f0800000020000000000000001e7000000012d1d6800036200000005340000001dc8ef60000000000000000000000000000000000740000000000000000523000136c36e8220000000ad80000000000000000000000086c00000014b800000000000000002ff2a1953000000000000000000000000000000000000000000000045a800000000000003281822dd00000003f60000001054000000000000058600000000000000001eb800c1fc00019d91a0a280000000000000000000000000071a0001c940000001921174000000079800000021d0000000a440000000000000001800c0020000000004004002000800400a000000800000400000100000020010000000000005000000000400100000040020040018004008000000000400600000000040020000008000000003004800c004002000001000000000000000040020028000000000001003400c0010000004000000000000000000200180000040000020004006000000000000000000000000020000008000000000001001000c000000800400000800080140000030000000002001002800000000000000080060020008004000002000800400000700100040040020000000000000000000000a00100000000020000008014002000000001000e002002001000600400000000000010000000000000001800c000000004001000000100000000020030058004000000000000000000000300000020010028000004002000002400c001000801401000900000040180000000000002000000800800400000000040040000000000008001000800000a007
  | 12 => 0x63f3231e480003ca1400eb800000017e00000003db00000000000000000000b5c2992e40b4c0000000d5800087a00000013a8000000000000000073e00000001b80000000000ac65933a800000b40000001ad00000004428000b24000350000061228800012a000000000006e88342e30000000b2c000000206c00000000008384a60000000000000000000000000000000000000000000000000dfc0000000000fc20003c49a24000000000176800000008d90ec0000002ed81287ba000000000000081812f800000000037a000017a000000000000000000020f000072245581200001cc2ae929000035a02c000000000000000006385090b3993842a67d43c113c0003340f08cf400009500003d865c00020880140000000000000000000000000010400020220d400007b000000030804f00020810824b642b800000085e0000000ebe2ab000000099a65d0002028000000000000087037e18a0b500001270ef800103c6161cd00000000000000000000497000000000015a000000000037d000000000000029980009b00000000000000870000104800000030d800000000011b000000051c0eb0f940000000908000000000000000000035d000128c0005fe000100c00078b000000065e38b000105c000000000000000073700000000005c31549c580007170000000000000000043000000017a000000000000000000004ec000000000037000003dc72600000000000000000000000000000000000071e5e50af00b8e662810000000000000000204400046c00004c90480000000000fa64010fe869cd583553d81ec48548863699124ae600000000000000000000000000000441800000000000000000000000378abc5944d13631a8c0006c700000000000000000000000000439000000079b000220400000017700000004eb060000000000000000009ac2cd0000000fe40002fa80000000000001a9800053d233a0a863400000000000004fe00000000000002b580000007f4000050000e0000a100000160000001418000379000000000069f00018ac340000316157c0000000000000b2800000000000000000000000b9a00000000000000002f888a04fe4431fa00000004481f1800000000007c0000bbe0810940af8f0e10f04c0000000000000159467400030a800000000000003a4000000000000010000025b800000000000000010464fd0000000000000000000000000000000000000002ad00005d841d0000000000000329879cf7c0000000fdc00000000000000002c6213822c0000001d1800000000000000006d40d52561cd40000000000a311340000ec184400000010900000000004640d7057423c10d800000000000000010d8000324800000000000000000000000000000c988080001eec0000eb0000c7c000000000
  | 13 => 0xb86b82543de000173c00086a0000408fce6c200000008f473d1cb092c00024e1b69b90000000183807c00000000017c8000000355800111a0000000000bc26f82b48000a0e00000000000003f0000000000000039d00000000002b08000000000000000000000035100000006ee000000045c0001908001026000000033513605627d1e640000000000000d3800000000000000000000000b8c00000000000a60000c500000001b1000027482c8461a59bcd15426613e9f5ccc248a3bf8170fa044e2b500000d400002105dc0004c51bd154c5b437b16594405da30813280000004890001d20caa6ec0001580b50000000000016a00016100000006e500004e80001e538580000000001e900004de000000060852a04e46180003b47f6000000000000000009c09320000001560cb8000000000000000000004b107e622000000000076a0b90000cce00000000f480e70a0000944b1216f01d91540000000000000c406510001cb8f1e2b0000104056455e0d7a07ccac5880001c7400000043700000001e600001900000000000000000000000000000000016216ec00081443da2240000c9000183d06600000000003b20002eb8000b2a5f32cba030bd8359082a00800000034a9018f9600000000000000001f4800026000000000000000003dc0000000000000000069e000000025000000017c00003366e000000010ec0000000a60d9a00036a9df02f6860179209429600023c0054a560000000000000000000000000024d35c075c00000034e8d5000000000000000000000001214ada00000000000002610000000f560002a680000008ad2a80000e207de0b01cc406200000020140000001a40000f4026a3c2853403034617c9914e42000069000000048e000095400052100018c8000000282000000004c0910ebc1b200003b9a580002f100000010d207900014a8d787a82b794b4fde1ff00000002720002ab20b800000000000000000000000fa8ba04390001d600000003a280000000000000000e0a00038996100000000001cbce5029326300000004b3000080800028a25518280000220aa1d1800000000007100000000000000000000000000000067017786e413e0002900850c0068e0001d8c44a0000000e5c15a45900000000000003f480000004963d683b4f8a37f2960e20b8e0cb3e600000000f50000000cdc4c023715f8fb60000001094ee60000fc9be43e466500000000005e93618cf00001cd34385200006da37080010ca2b31588c98000000000000000000000016a800000000000000000000080000000000000000000000042e951414200028e8000d4a00000015ec27867513608c909819d37e10603160540000c0c3d8000000000800066208005546580240b0865806487d0000f200000001f698a083824c23a0ff85c
  | 14 => 0x1bb00000000008091fe8000dd40000b19aa0d1670321a80d897426200012180000001319de4a5e4871721fcc05e000012991c26c0000ab064cd804ee2d1800024652500000000000001cc0000000000000000000034e0b69e5800038100000000000b90000000000420000000000000034784b800018e00001780000000000e1ce5216c057180807208a000000000045c00019b0ad0614229800000000027e193c3f80000000000000000000000000000000000000007740000d9cb0a41e1050000b0c2230000000a9e000000000000000005a00009da0000000000a480001628000000000104800000000016b1f1834600000000000004692a38000d0a0000000000000000000089c14c0000000000c200000000290e786db00000000000000000f1cbb80af000000000000010b000000000019f800060007a3578f246e6000000000000000006c1e94000000000000000053b000150400076e0f20000000000000134c0000000001a4000000000000010be000000000004e0000ac19d8fbe8b20000000000000000000000000000000006c83ff000190020242133497490320000000d08000000000201cde40000ee1dd8dae16b3749cec3780001dd80000005020000ddcb5626d0001240f000000000e341063991890ae4000000000152114286703400000000000000000000000000189d11e4e200000002560bf2289acc000000000000000004d00006008500960000000fb087900000000004e0000187cb4e0001879df400065b0c90000000085000000000000000000000000000000000000000127800000000017b8000dda205000000000071800000000007ce01980000004ef00020e4000000000000000060e0000000f54000000000089620f00000010c415221d09e875a49f0001c900006913020d8094c3353b09adc0000c813380001fe48b0770b606207fa0ba9d28d020400de800031800000000000007b2000000000008c0000000000652000089800000000001b90b00003bb8000c1200000011d8f3c3860001d98d9063709a002828200000022cd04e0613c988e42ca35200000004607d10000000000000000000000000041600000005ff11f152476c0002ae16748de56e31e00006a6000000000000000045480000000000001628a6e376000000021a169000000001a0000a280000000000000000d0600000000000003913168000d3207f438800000000000000000008121e80000000000000000000000000000009b8000175000000000005d000000000003880000000000001d0ced000016c825c00008d00000000000000000000d5200038880000000000001d5800000000000000000000000000d4834d00014e400000003293ec37c0000f807500001332c08000000000186800000040c000000000088e3c
  | 15 => 0x1c20e9c0000470ec8000000000011c0000000000000e3836f00000000000003da015cb8400000000010b2000000000040e446103000000000021900001380002cf839818800007e80007be0001388b840000000510000b1a0003e48000f4800000014f80000003069894fd60e5000000000083800000000003b1000000110e0001571edcbaa7883aa22711466de0001340e02000302a0700001fe0ef00000003a7000000026a0002b30c543e86cc0000f3caf80f01fc07b8000000000000000071e000000000000000000000003492f40000000000000000028c0000000000000000000000000033800000005d60000ae80b031a00002e85d000003f16700000000002798000000000000190c000000335180c2980173a000b45444c42ab80000007dc12f2168f744831390000c6200013e128893400000000000000000000000000000000000000037c04780000006cf000000000070000000000000000000000000000000000000000026e800101600026f000000000000000000000000001f943aa77000000000000002d1000000000000000000000000000000e8400006a0000614000000000000086b37b00000000000000000b8014e00d040c000582000000000000037816600000001b4a2e0b4063422f10984220b306e8d6c1a26d2000231c000000000000000000000017d050a00000000000000000000000630000000000000000008b80001641860000ce40a234c18d800000036300000006080000000000cbe17900a0c94dee19f02207a4000000000000096a0000000001100000000196400000020ca14d0b600000010c4c300de000000000000029f80000005fc07080000000000001fc50948360000000000000000000015629d25e90c0000000000000013c000000000000010a0000ee83100520000000000000110215400000000000000000000001980d08000000082c0ea57809d80000000000760ea42f0043000011888041f000000000000019380000000000000000cae4620000000000000096906cba22c700019206520002e600000007690b8000000000000000000007591da00000000000000000000000426800014000000016e800007c398071c00000f0cd00010c83571b600000000000000f3000061d29d05d80823a41098000aea5b02690e84f7a3510000000bac00000000000000002f68000000000000000015200041800010ea00000000004f20001fa979d09e000000179111400000004c51160003a78000f9a00000000000006ad0001ce0000000000000000000000000000008c6000000000037133c8d600000000000000dc400000000000000000000000000000000000000000000000009ec000000000000036100015d86a0000000182000048027190b0fda75b00000000001080d980000000003ea80000
  | 16 => 0x3ba28e2570ee00000000000000e3e000000000000000021100008cc00044a8eac00000014312600000000000b305d05fa000000000000000000000008a700000000000003fd982c00000000000002240003740000000000000085c000000000000000000012501b00002b500000000000003de000000060700000007968041dc946400078c00015900000000000000f8600000000001a01ce00016c44a84b81321220bdc6d1000000000000003180000000d70000ea800009300000001540001e2030c00000000000000000000000000000000000000000082d04200009a800038480000000000000e880004f70000000e884e923f000000000000020849ca15000015fc0383d900005643444950001c504000001f9800005000031b000000000000000000003a812400000000000000000bf03d810185e914c000000161c00021811100011760000000000000000000147c000000207800000000000000000000000000bf80005c10001ad400000035d80000007ae1a18000e7e3e6000021800000000000007ec0000fb80009d000000000000002e500000008be1b536a0000bde0003620000000000000000000000000000011507a30000000000000280812d0f8000000000070a42d0000000f0442e0fd00000000b73951c3c00080d3f10000000000195a2b826e51e15080000004c200002c4042571000000000000000000000002a400204f80000c70000000dea39b3ee8a4400000000012c4c2600031483e8000000194000000012f1a0a0980000000000cd81ce70e0bf8924f820003e387b400000000000000000002049e7c00039f427000000000005c0a7062c4bc00014600004da00019900003be36e000030a05021f00009e04f8000000073c00029496fc810000058090c71465e0000f5095628b4178f18e40289000000033000023192a4000000000000000000000000000005b332587d4000000000000097267400000000008772f800010520010ad80a4c2e72b00000000466fb000000000000900000007d66412f001f800000000000000008a23ab8000fd45b926a80000000000000000158000000000112219526c8b490a22f300000000000002940cb40000003398c740000000be80000000000000000b5a0003e40000ab600000000000001c900020d000000000000000001f10000fe800000000007140001b400021082862fd4379b740000000001ae800000021b80000000001c80164000000000000043e00000000000000002f100006ac00000000000000000000000000000000000090200009209ec6164a04259f680007a2000000000000000009a400048d000144c3c00000ae0000758874015800000028400000007d800000020f4c740490000264c847914071830000337000000000000000015c066472c00000003a66060
  | 17 => 0xa489e200025900004680002da8000000760346000000000000000000000000000000000000000000000000000000008a853522911c02f8000000000000000000000000000000000000000000000219800000000014d08460001db8000ee20000b20078c02151000225c06e00001300000003d52df00000003d63f4000102a28f0001a6895e00000000000003010001870000734000000116c0001af94450025b42a1082023e0000000000af447f000036c1f86b6452000000039200003c800038c2f31d44110000000000000000000000000000000480a580000001b3000000016a00000000000000d480000000000000000000544000000038600006980000002d00b980f800000000000000ce00000000003500000e5a21000000000016c80007d400b00006268ac3f70000000000000000000000000019e8a1600036b111c000790000000000000000004946ea000000000000043438206440004a513f06d800000000000000000000000000000000000000018400000000000000003ae00000002730000d000000000830000000000000000000000016b8000000000000000000000000000000003b0298017c0000000001fd4728000164863d0342ac267000000007300000640000000000a1c78400025399b4a4e5d416016d89be0703f000000002df00000000000000001a7800000012380000005a10000c440da00045880000002bf08d00000000000000000000000000118000073611ba274e4c6881a51f9800000000011e466043f05b00000000000001e18c7600023d80000000001af00000002b400000000006aa0000b3c00000000000000000000000908b9400000000000000002800000b520000b4060c0000002ac9698a4c6a1000000034800000020e8000000000000000009100000000000000000000ed62310000001128000117800000000000000010003ce45b800000046d000000000000000010a400000000009d000044124d80008940000000000ffe5e33b28d9472a3ef00000009283a61de800000000000000000000001ed03e452e00032a0000f14380000000000000000013fc0000000000000000000000220901e82800000000000000000000000000000145c000000000000000000000700000001d000000000000002b900000000000000000c4c00000000000008b02868a6c97600000000000000000d9000000059900000010f400030f000014e2bb000000000064d0000000000000000000000000000000001240000000000000000000000000051234b80000000001c1015489a7ac0001b8c442000000037c000000000038800000045280000000001068000ff06bd00000000000000001e680005082ec00000b67550d68a8ca0a55100000000000690000000b6e0004461c480000000000000
  | 18 => 0x23f05f0000dcc70c00000000003dc11c1b6000078d13b12708fa8520000000b9c8ca2cf000000000000000001345a4044838cb1800000000000000000fb000000017100000009cc00000000004ac03c00000000000002de15e40000000001960000000328069513e3b50d311090fe82b00000010a8000000043829e01b0000000000000000000000000000000000000000f980000002350f5051000000028a80000002db0000000ea659a00000006dc00045f800063c000000143c000000205000000000000000000002a500002a00006683df9cc8000000000000000000015b8000b000000000000000000421800000000000000000008630000000000000232000118000000000004ee0000000000000000000118493a000000000000000000014580000001418000e9800046100000000000000dad0804c9000000117800000000000000000000000a1c0000000c640002bc00019dc000000000000057a00000000000003470ce000000030520a000044847100000007a211e2aa0000e8e2a71f383147e46920000000aee00045021a0d824c7000000043261a4620000ed868022b800022689000000000740002cd85b8000000000000000083231200004548c500000000007982861548ef00001f20000000000129000000000000000000007640c488b400000032d046400000000001140005911e18000000000000000000047c0001fb00000000001a6c99654a0000001130000343000027a00000000000007fc08594d80007fd00000000001090001c090fc49e00009e051a2aa000045085e4cc25680000000000000000000199000224800018135800004d000024600000000000000000de200000000000005c500000005cc00000023040000000000000000000000000000000000000000000000000000000000000000000000000007acf1c00000000000004f93d30000cd600045d22f4ce200000000000003e0000000000000000010380000003a9070068859c430800085600000008683585af2e49bf40000d6153000000000000003a000058b44b0e1070607d33314f001026b000123c00051b000000006a000000000000000000000000005030000c0800000000000000000002e980000000003c088f40007f010083ec00019e000000000000000000001d448200002f00003e200000000004bf41d9c8c53e00026500000007060000b880000000000000482000000000000029425a000000000000017a8000000000000000077e00022648d661900008a400000000000000000002c700000002a804d9bfc0008c90000000ac467f000000099000022d0000f0800000016945b83890c801800000004030f14000000000000054067e2608b04cde00040e83c400000016a8000ec47a70000ff00000000000000bec5bd1bc0000000465
  | 19 => 0x700003a5a170000719000000000000000011c80000000000000f9e00000007a06d0000000212400000009493c800000000000000001a10bf17ec20e30e00017640001c20dc1a9ccc67b505180000007272350000d725f900000007a600000000000000000000000f3a0000000000f6668a0e52058d94795449800062e45b000096c00000000000007808030001e500000000001928d7e70d0cb8000d923742a708ac1b4000000000000000000000000000720000000f880000001f48000000000000080a000000076cf803bc0000524ace00000000000001620090000db200001a000000000007780000000003a68000ce400031797f400000022c090028e2590088000000000000000000000000015f4a8c4130000878666000317124c5f625013708cc9220000930ae09e839c1c709d41e82de1689008df400010600000c40000000598000153010000000025731c18f4000623000000106e0cc00017dc00000031f00000000000001db42400000000000e2a8880000000c420000000000000000206800000000000000a80001e3000000000000000000002ae000000000000000000000000000002dc000000058f0000000c7200000000007f600000000000001183ba8fe473a00000000000003a50000840f5e000141000089800000016b078200045c80000001ef000000000067b1f08c8cff267c000000000033e40b9b15020000000000098630c2c822f8f724a12708000000000000000000032200009800cc4840000b20e720000000000d9c0003a4a12048a75d3ec91dcc2475e000000113c30600000008a000000000000004f528500004748473591468fc80c63838000f42110198801827e00000000000000000001390a620003a09ea50e653217b1710c541bf1df92f853c0000001f580000000000000000000000000000085600000001c000000000000001d2000000000000037780000006eb12318cc79a583000000019e3f141f0000a806be3fb800
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x57548510005f77448510005f57448510007d7734851002df6734851002df47348510007d4734851002dd47348510006f76348510006f56348510015f77248510017e77248510007e7624851005ef6624851005ef46248510007e46248510007e64248510007e54248510007e63248510007e53248510007f3704851000df6704851000df470485100cff07048510016f76048510017f360485100cff050485100cff240485100cff230485100cff22048510015fa76d41100b6fa76d4110014fa76d411000dfa75d411000f7a75d41102a6fb65d41100077b65d41102a6f965d41102a77865d4110005f974d41102a77b54d41100077954d4110005f973d4110005f972d41102a77b52d41100077952d4110015fa71d41100b7f271d41102a7f171d4110015f871d411000efb61d411000ff361d41100b7f251d41102a7f151d41100b7f241d4110007f141d41102b7f331d41100b7f031d41100b7f221d4110007f121d4110015f87650110026f87650110014f876501100077b75501102a5fa75501102a5f8755011000778755011000578755011000dfb745011000fbb7450110007bb6450110026fa6450110026f86450110037b86450110037ba5450110007b95450110005fb7350110005fb7250110037bb4250110007b94250110007f37150110015fa7150110015f8715011008ff0715011000efb615011000ff3615011008ff25150110007f1515011008ff24150110037f141501102aff3315011008ff0315011008ff22150110007f12150110015f8764c11001ef8764c110014f8764c1102a5fa754c1102a5f8754c110005fb744c110005f9744c11000dfb734c11000fdb734c110007db634c11001efa634c11001ef8634c11002fd8634c11002fda534c110007d9534c11002fda434c110007d9434c110005fb724c110006fb624c110006f9624c11002fdb324c110007d9324c110007f3714c110015fa714c110015f8714c11007ff0714c11000efb614c11000ff3614c11007ff2514c110007f1514c11007ff2414c110007f1414c11002ff3314c11007fda314c11007fd8314c11007ff0314c11007fd0314c11007ff2214c110007f1214c110015f87648110046f87648110014f876481100077b75481102a5fa75481102a5f87548110007787548110005787548110005fb7448110005f97448110005fb7348110005f97348110006fb6348110006f9634811000dfb724811000feb7248110007eb624811005efa624811005ef86248110007e86248110007ea5248110007e95248110007ea4248110007e94248110007f37148110015fa7148110015f87148110047f0714811000efb614811000ff36148110047f25148110007f15148110047f24148110007f1414811029ff33148110047f03148110047f22148110007f12148110
  | 1 => 0x891005cfc731891005cfe721891005eee721891000cff7118910014fe711891000cfd711891005ef57118910014fc711891005eef211891005ef621189102c6ed2118910014ff701891000cfe7018910014fd701891005ef9701891000cfc701891005eef201891005efa20189102beed201891003cff76d4910004fe76d4910004fd76d491003cfc76d491003e7e65d49100067d65d4910015f671d4910005f571d491000df870d491005cff7694910004fe7694910004fd769491005cfc76949100067f659491003e7c6594910035be7494910005bd7494910015f67194910005f5719491000dfa7094910005f970949101ef785094910004ff7654910004fe7654910004fd7654910004fc765491003e7e65549100067d6554910015f67154910005fb705491000df8705491005cff7614910004fe7614910004fd761491005cfc76149100067f651491003e7c6514910015f67114910005f5711491000dfa7014910005f970149101af78501491005cff7690910004fe7690910004fd769091005cfc76909100057e75909100057d7590910006bf6490910026bc649091005eee6290910006ed6290910015f67190910005f5719091000dfa7090910005f97090910004ff7650910004fe7650910004fd7650910004fc7650910026be6450910006bd6450910006ee6250910006ed6250910015f6715091000dfa705091005cff768c910004fe768c910004fd768c91005cfc768c910006df638c91001edc638c910015f6718c910005f5718c91016fd4318c91000dfa708c910005f9708c910004ff764c910004fe764c910004fd764c910004fc764c91001ede634c910006dd634c910005f7714c910015f4714c91002fd7314c91000dfa704c91000df4765451003ef4765451000cf47654510015f7755451001777755451000777655451003ef6655451003ef46554510007746554510005f7745451000777545451000775545451002df6735451002df47354510007775354510007755354510005f77254510007775254510007755254510007f3705451000df6705451000df4705451011ff07054510016f76054510017f3605451011f76505451011f74505451011ff0505451011f70505451011ff2405451011ff2305451011ff2205451000df47650510026f4765051000cf47650510005f77550510005f57550510015f77450510017b77450510007b76450510026f66450510026f46450510037b4645051002df6735051002df47350510037b74350510007b54350510005f77250510037b74250510007b54250510007f3705051000df6705051000df4705051010ff07050510016f76050510017f3605051010ff0505051010ff2405051010ff2305051010ff2205051000df476485100cef4764851000cf47648510005f77548510005f
  | 2 => 0xcf571d8d10014fc71d8d102f6df31d8d1002ef731d8d102f6dd31d8d102f6f431d8d102f6f621d8d10014ff70d8d1000cfe70d8d10014fd70d8d1000cfc70d8d102e6df30d8d102e6dd30d8d102e6fa20d8d1001cff7658d1002edc6358d102ddf77158d1007fd43158d102edfb7058d10004ff7558d1003cfc7558d10004ff7458d10024fe7458d10024fc7458d102e4ff7358d10006df7358d1002ede4358d10004ff7258d1005cfc7258d1002edf3258d102dcff7158d10006f77158d1002ef73158d1007ede3158d1007edc3158d1007ef43158d1007ef62158d100fcff7058d10006fb7058d100fefa2058d1003cff76d4d10004fe76d4d10004fd76d4d1003cfc76d4d100067f65d4d1003e7c65d4d10015f671d4d10005f571d4d1000df870d4d102577850d4d10004ff7654d10004fe7654d10004fd7654d10004fc7654d100067f6554d1003e7c6554d10005f77154d10015f47154d10005fb7054d1000df87054d1023f785054d10004ff7650d10004fe7650d10004fd7650d10004fc7650d10006bf6450d10026bc6450d1001ede6350d10006dd6350d10005f77150d10015f47150d1002fd73150d1000dfa7050d1022fba4050d1003cfe75d8910004fd75d8910024fe74d8910004fd74d8910024fc74d891001cfe73d8910004fd73d891001cfc73d891000cff71d891000cfd71d89102d6ef21d89102d6ed21d8910014ff70d8910014fd70d89102cefa30d89102ceef20d89102ceed20d89100ccfd7698910006ef62989100cdf57198910045f9709891003cfe7598910004fd7598910024fe7498910004fd749891005cfc749891001cfe7398910004fd739891005cfc739891005cfe72989100ccfd719891005ef5719891005ef621989100e4fd709891005ef9709891005efa20989100057f75589100057c7558910005bf7458910035bc7458910005df735891002ddc73589100e5f77158910065fb7058910004ff75589100067f75589100047f755891003cfc75589100067c755891003c7c7558910004ff7458910006bf7458910004bf7458910024fe7458910024fc7458910006bc7458910024bc7458910004ff7358910006df7358910004df735891001cfe735891001cfc7358910006dc735891001cdc7358910006ef72589100e4ff7158910006f771589100ccff7058910006fb70589100cefa30589102ccfe76189100057e75189100057d7518910035be7418910005bd741891002dde7318910005dd7318910006ed621891003cfe751891005e7e751891003c7e7518910004fd751891005e7d75189100047d7518910024fe741891005ebe7418910024be7418910004fd741891005ebd7418910004bd741891005cfc741891001cfe731891005ede731891001cde7318910004fd731891005edd7318910004dd731
  | 3 => 0xa424c120007e9424c12004fdb324c120007d9324c120005fb714c120006fb614c12032fda314c12004fd8314c12000dfa76c812000efa76c812000cfa76c81200077b65c81200077865c812005dfb73c8120005f973c812000dfa72c812000fea72c812000efb62c812000feb62c812005fea52c8120007e952c812005fea42c8120007e942c8120005f971c812003cfe76d9510024fe74d9510004fd74d9510024fc74d95100067e54d95100067c54d951001cfe73d9510004fd73d951001cfc73d951005cfe72d9510004fd72d951000cff71d9510014fe71d951000cfd71d9510014fc71d95103267f51d95103267d51d9510014ff70d951000cfe70d9510014fd70d9510326f970d951000cfc70d951031e7f50d951031e7d50d951031ef850d951011cfd76995100067f659951011df5719951009df9709951013778509951003cff7659510005bf7459510035bc7459510135f771595100b5fb705951011f7850595100067f7559510004ff7459510006bf7459510004bf7459510024fe7459510024fc7459510006bc7459510024bc7459510004ff735951001cfe735951001cfc7359510004ff725951005cfc7259510134ff7159510006f7715951011cff7059510006fb705951011e7e505951011e7c505951011ef8505951031cfe761951003e7e65195100067d6519510024fe76d9110036be64d911003cfe75d9110004fd75d911010cfd74d9110036bc54d911001cfe73d9110004fd73d911001cfc73d9110036bf43d911005cfe72d9110004fd72d9110036bc42d911000cff71d9110014fe71d911000cfd71d9110014fc71d9110316bf41d9110316bd41d9110014ff70d911000cfe70d9110014fd70d911000cfc70d9110306bf40d9110306bd40d9110024ff76591100057f75591100057c7559110036bc64591102fdf7715911030dfb7059110004ff75591100067f75591100047f755911003cfc75591100067c755911003c7c7559110304ff7459110006bf7459110004ff735911001cfe735911001cfc7359110004ff725911005cfc7259110036bf42591102fcff7159110006f7715911010cff7059110006fb705911003cff76d5110004fe76d5110004fd76d511003cfc76d511003e7e65d51100067d65d5110006bf64d5110026bc64d51100373e54d5110015f671d5110005f571d511000df870d5110004ff7655110004fe7655110004fd7655110004fc765511003e7e65551100067d6555110015f67155110005fb705511000df8705511001cfe76d8d1002ede63d8d10015f671d8d1000df571d8d1002fd731d8d1003cfe75d8d10004fd75d8d10024fe74d8d10004fd74d8d10024fc74d8d100fcfd73d8d1005cfe72d8d10004fd72d8d1002edc32d8d1000cff71d8d10014fe71d8d1000cfd71d8d102e6f571d8d10
  | 4 => 0x49201ecfe76149200067f651492003e7c65149201edee72149200076d5214920344fe76909200057e75909200057d75909200067f65909200067c6590920345ee769092033eee7690920005ef75909200076e7590920005ed75909200076d75909200056d75909200076f65909200076c659092017ded7490920026ee6490920026ec649092000dee709092000dec709092005eef6090920197ea3090920197ea1090920024ff765092000cfe765092017cfd765092000cfc76509200067f65509200067c6550920006bf6450920026bc6450920057ac4250920005fb705092000df8705092000dec7650920026ec765092000cec7650920005ef7550920005ed75509200076f65509200076c6550920195ef7450920007af7450920007af6450920026ee6450920026ec6450920057ac6450920007af5450920057ac5450920057af4350920007ad4350920057af4150920007eb705092000dee705092000dec705092017fe8705092017eef605092017faf405092017fad405092017fea305092017fea1050920334fe768c9200067f658c9200067c658c92000df8708c92001cff764c92000cfe764c92014cfd764c92000cfc764c9200067f654c9200067c654c920006df634c92001edc634c920005fb704c92000df8704c920014fe76d85200067f65d85200067c65d8520046f661d852003cfe75d8520004fd75d8520024fe74d8520004fd74d8520024fc74d852001cfe73d8520004fd73d852001cfc73d852000cfd72d8520014fc72d8520006ee42d8520006ed42d8520046f621d852000cfe70d852000cfc70d85200e6fa30d85200e6f710d85200057f75585200057c75585200067f65585200067c6558520005bf7458520055bc7458520005df735852004ddc7358520046f46158520004fe76d4520004fd76d452003cfc76d45200067f65d452003e7c65d4520005ee72d4520005ed72d45200076d52d4520004ff7654520004fe7654520004fc76545200067f655452003e7c65545200076d5254520004ff7650520004fe7650520004fc76505200067f65505200067c6550520007ad4250520004ff764c520004fe764c520004fc764c5200067f654c5200067c654c52000dfa704c5202bcfe76c85200067f65c85200067c65c852000df870c852000cfc76485200067f65485200067c6548520005df734852004ddc7348520006f76148520016f46148520005fb704852000df8704852004df8764c12001ef8764c12001cf8764c1200077b654c12000778654c12000dfb734c12000fdb734c120007db634c12001efa634c12001ef8634c12004fd8634c12004fda534c120007d9534c12004fda434c120007d9434c120007eb724c12005df8724c120007e8724c12000efb624c12000feb624c120007ea524c120007e9524c120007e
  | 5 => 0x56bc645912035def7259120004ff75591200067f75591200047f755912003cfc75591200067c755912003c7c7559120194ff7459120006bf7459120004ff735912001cfe735912001cfc735912035cff7259120006ef7259120004ff7159120014fe7159120014fc715912017cff7059120006fb705912017efa105912003cff76d5120004fe76d5120004fd76d512003cfc76d51200067f65d512003e7c65d51200573e54d5120005ee72d5120005ed72d5120004ff7655120004fe7655120004fd7655120004fc76551200067f655512003e7c655512001cfe76d8d200067f65d8d200067c65d8d2004ede63d8d2003cfe75d8d20004fd75d8d20024fe74d8d20004fd74d8d20024fc74d8d2004ede43d8d2005cfe72d8d2000cfd72d8d2005cfc72d8d2004edf32d8d20014fe71d8d20004fd71d8d20014fc71d8d20006de31d8d2004edc31d8d2005cff70d8d20164fd70d8d20166df30d8d20166dd30d8d20166fa10d8d200057f7558d200057c7558d200067f6558d200067c6558d2004edc6358d20355ef7258d20004ff7558d200067f7558d200047f7558d2003cfc7558d200067c7558d2003c7c7558d20004ff7458d20024fe7458d20024fc7458d20164ff7358d20006df7358d20354ff7258d20006ef7258d20004ff7158d20014fe7158d20014fc7158d2014cff7058d20006fb7058d2014efa1058d2003cff76d4d20004fe76d4d20004fd76d4d2003cfc76d4d200067f65d4d2003e7c65d4d20005ee72d4d20005ed72d4d20004ff7654d20004fe7654d20004fd7654d20004fc7654d200067f6554d2003e7c6554d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200067f6550d200067c6550d20006bf6450d20026bc6450d20006df6350d2001edc6350d2000cfe76d492000cfc76d49200067f65d492003e7c65d492000dfa70d4920005f970d49201acfe76949201ee7f659492003e7c6594920055be7494920005bd74949201adee7694920006ee76949201cded75949201ef6f659492003eee659492003eec65949200076c659492003e6c6594920007ae7494920005ed7494920007ad7494920005ad74949200076f54949200076d549492000dee709492000dec709492005eef60949201ef6e50949201ef6c50949201efea30949201efea109492003cff765492000cfe76549201ccfd765492000cfc76549200067f655492003e7c6554920005fb705492000df8705492000dec765492003eec765492000cec76549200076f75549200076f655492003eee655492003eec65549200076c6554920005ef745492034f6e545492034f6c54549200076f53549200076d5354920007eb705492000dee705492000dec70549201cfe870549201ceef60549201cf6f50549201cf6d50549201cfea30549201cfea105
  | 6 => 0xc63d95201ef6f72d95200067e61d95200067c61d95201ef7a30d95201ef6e20d95201ef6c20d95201ef7820d95201ef7a10d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200067e73d95200067d73d95200067c73d95200067f43d95200067e43d95200067c43d95201ee7f72d95201ee7d72d95200067f42d95200067c42d95200067f32d95200067c32d95200067f71d95200067e71d95200067d71d95200067c71d95200067f41d95200067e41d95200067c41d95200067f31d95200067e31d95200067c31d95200067e21d95200067c21d95201ee7f70d95201ee7e70d95201ee7d70d95201ee7c70d95201ee7f40d95201ee7e40d95201ee7d40d95201ee7c40d95201ee7f30d95201ee7e30d95201ee7d30d95201ee7c30d95201ee7f20d95201ee7e20d95201ee7c20d95201ee7f10d95201ee7e10d95201ee7d10d95201ee7c10d95200067f65995201cded729952020def72595200067f7559520004ff7459520024fe7459520024fc7459520004ff735952001cfe735952001cfc735952020cff7259520006ef7259520004ff7159520014fe7159520014fc71595201ccff7059520006fb70595201ecfe761952003e7e65195200067d65195201ed7e76195200067e76195201ec7e76195200067e64195200067c64195200067e63195200067c63195201af6d72195200067e61195200067c61195201af7a30195201af6e20195201af6c20195201af7820195201af7a101952003e7f741952003e7e741952003e7d741952003e7c741952003e7f731952003e7e731952003e7d731952003e7c73195200067f43195200067e43195200067c431952003e7f721952003e7d721952003e6d72195200067f42195200067c42195200067f32195200067c321952003e7f711952003e7e711952003e7d711952003e7c71195200067f41195200067e41195200067c41195200067f31195200067e31195200067c31195200067e21195200067c211952003e7f701952003e7e701952003e7d701952003e7c70195201ae7f40195201ae7e40195201ae7d40195201ae7c40195201ae7f30195201ae7e30195201ae7d30195201ae7c30195201ae7f20195201ae7e20195201ae7d20195201ae7c20195201ae7f10195201ae7e10195201ae7a10195201ae7d10195201ae7c1019520024fe76d91200067f65d91200067c65d9120056be64d912003cfe75d9120004fd75d912001cfe73d9120004fd73d912001cfc73d9120056bf43d912005cfe72d912000cfd72d912005cfc72d9120056bf42d9120014fe71d9120004fd71d9120014fc71d9120006be41d9120056bc41d912005cff70d9120194fd70d9120196bf40d9120196bd40d9120196fa10d91200057f75591200057c75591200067f65591200067c6559120
  | 7 => 0xf2005cfc7650f20026be6450f20006bd6450f20006df6350f2001edc6350f201ccfd76d4b2005e7f65d4b2005e7c65d4b2000ded7694b2005eed7694b2000ced7694b2003eee6594b2005f6e6594b2005f6d6594b2005eec6594b2005fae7494b20005ed7494b2005fad7494b20005ad7494b200076f5494b200076d5494b2000dee7094b2005fea7094b2005fe97094b2000dec7094b201ef6e5094b201ef6c5094b2020cff7654b2005e7f6554b2005e7c6554b2005f6c5254b2020def7654b20006ef7654b2005f6f7554b2005f6f6554b2003eee6554b2003eec6554b2005f6c6554b20005ef7454b2036f6e5454b2036f6c5454b200076f5354b200076d5354b2000dee7054b2000dec7054b201cf6f5054b201cf6d5054b2000ded7690b2005eed7690b2000ced7690b2005def7590b2005f6e7590b20005ed7590b2005f6d7590b200056d7590b20026ee6490b2005fae6490b2005fad6490b2005eec6490b2000dee7090b2005fea7090b2005fe97090b2000dec7090b2035cff7650b2005ebf6450b2005ebc6450b2005fac4250b2035def7650b20366ef7650b20005ef7550b20005ed7550b2005faf7450b2005faf6450b20026ee6450b20026ec6450b2005fac6450b20007af5450b20077ac5450b20077af4350b20007ad4350b20077af4150b2000dee7050b2000dec7050b2017faf4050b2017fad4050b20354ff764cb2005edf634cb2005edc634cb20014ff7658720005df735872006ddc735872005ef46158720004ff755872003cfc7558720004ff7458720024fe7458720024fc7458720004ff7358720006df7358720004df735872001cfe735872001cfc7358720006dc735872001cdc7358720014fd725872000cfc7258720006ee4258720006ed4258720066f6315872005ef7215872005ef421587200cefa20587200cef7105872003cff76d472005cfe76d4720004fd76d472003e7e65d47200067d65d472005dee72d4720005ed72d47200076d52d4720004ff7654720004fd765472005cfc765472003e7e65547200067d65547200076d5254720004ff7650720004fd765072005cfc7650720026be6450720006bd6450720007ad4250720004ff764c720004fd764c72005cfc764c72001ede634c720006dd634c720016f6614c720006f5614c7202ccff7648720005df734872006ddc7348720016f4614872003cfe76d9520024fe74d9520004fd74d9520024fc74d95200067e54d95200067c54d952001cfe73d9520004fd73d952001cfc73d95200067e53d95200067c53d952005cfe72d952005cfc72d9520014fe71d9520004fd71d9520014fc71d95200067e51d95200067c51d952005cff70d95201ecfd70d95201ee7f50d95201ee7d50d952003c7e76d95200067e64d95200067c64d95200067e63d95200067
  | 8 => 0x5cfc76c853001dde73c8530005dd73c8530007cd32c853000dfa70c8530005f970c8530004ff7648530004fe7648530004fc7648530005df734853001ddc7348530007cd3248530016f6614853007fd6314853000dfa7048530024fe74d972005ebe74d9720024be74d9720004fd74d972005ebd74d9720004bd74d972005cfc74d972001cfe73d9720004fd73d972005cfc73d972005cfe72d972005eee72d9720014fe71d9720004fd71d9720014fc71d972005ef970d97201ee7e50d97201ee7c50d97201ccfd769972005e7f659972005e7c659972003cff765972005e7c655972005e7f7559720004ff7459720024fe7459720024fc74597200067e54597200067c5459720004ff735972001cfe735972001cfc735972003cff725972000cfe725972003cfd725972000cfc725972005e7e525972005e7c5259720004ff7159720014fe7159720014fc71597201ce7f50597201ce7d505972003cfe75d932005e7e75d932003c7e75d9320004fd75d932005e7d75d93200047d75d932017cfd74d932001cfe73d9320004fd73d932005cfc73d932005cfe72d932005eee72d932005ebf42d9320014fe71d9320004fd71d9320014fc71d932005ef970d9320024ff765932005ebc6459320004ff755932003cfc755932005ebf7459320076bc5459320004ff735932001cfe735932001cfc7359320076bf4359320024ff725932000cfe7259320024fd725932000cfc725932005ebe425932005ebc4259320004ff7159320014fe7159320014fc7159320076bf415932017ebf405932017ebd405932003cff76d532005cfe76d5320004fd76d532005cfc76d53200067f65d532003e7c65d5320026be64d5320006bd64d53200773e54d532005dee72d5320005ed72d5320004ff765532005cfe7655320004fd765532005cfc76553200067f655532003e7c6555320005fb705532000df8705532003cfe75d8f20004fd75d8f20024fe74d8f20004fd74d8f2005cfc74d8f2014cfd73d8f2006ede43d8f2005cfe72d8f2005eee72d8f2005edf32d8f20014fe71d8f20004fd71d8f20014fc71d8f20006de31d8f2006edc31d8f2005ef970d8f2005efa20d8f2001cff7658f2005edc6358f20004ff7558f2003cfc7558f20004ff7458f20024fe7458f20024fc7458f2005edf7358f2001cff7258f2000cfe7258f2001cfd7258f2000cfc7258f2005ede3258f2005edc3258f20004ff7158f20014fe7158f20014fc7158f2006edf3158f2014edf3058f2014edd3058f2014efa2058f2003cff76d4f2005cfe76d4f20004fd76d4f2005cfc76d4f2003e7e65d4f200067d65d4f2005dee72d4f20005ed72d4f20004ff7654f2005cfe7654f20004fd7654f2005cfc7654f2003e7e6554f200067d6554f20004ff7650f2005cfe7650f20004fd765
  | 9 => 0xb70589300057e75189300057d7518930085be7418930005bd7418930006ed621893007df67118930005f5711893003cfe751893005e7e751893003c7e7518930004fd751893005e7d75189300047d7518930024fe741893005ebe7418930024be7418930004fd741893005ebd7418930004bd741893005cfc741893000cfd731893005edd7318930386de4318930006dd431893005edf321893005eee3218930386ed3218930014fe711893005ef67118930014f67118930004fd711893005ef57118930004f57118930014fc7118930006de3118930386dc311893005cff701893001cfd701893005ef9701893005eef201893005efa2018930336ed2018930004fe76d4930004fd76d493003cfc76d493003e7e65d49300067d65d493001dde73d4930005dd73d49300075d53d4930004fe7694930004fd769493005cfc76949300067f659493003e7c6594930085be7494930005bd749493001dde7394930005dd739493000dfa7094930005f97094930004ff7654930004fe7654930004fc765493003e7e65549300067d655493001dde73549300075d5354930004fe7614930004fd761493005cfc76149300067f651493003e7c651493001dde7314930005dd731493000dfa7014930005f97014930004fe7690930004fd769093005cfc76909300057e75909300057d759093001dde7390930005dd739093000dfa7090930005f97090930004ff7650930004fe7650930004fc7650930026be6450930006bd645093001dde73509300079d435093000ddc764c93014edc764c93000cdc764c930005df754c930005dd754c930005df744c930005dd744c93001ddf724c93001fcf724c930007cf624c93005edc624c930007cc624c930006cc624c93007dde714c93007ddc714c930007db704c93000dde704c93000ddc704c93014fd8704c93001edf604c93001fdb604c93014fda204c93014fda104c930014fe76d853001dde73d853000ddd73d853007ef661d853007fd631d853003cfe75d8530004fd75d8530024fe74d8530004fd74d8530024fc74d853000cfd73d85302dedd73d853000cdd73d8530014fc73d853037ede43d8530006dd43d853005cfe72d8530004fd72d853037edf32d8530006dd32d853007ede31d853007ef631d853037ef531d853007edc31d853001cfd70d85302defa20d85302def710d853007ef4615853007fd43158530375fb7058530004fe76d4530004fd76d453003cfc76d45300067f65d453003e7c65d453001dde73d4530005dd73d45300075d53d4530004ff7654530004fe7654530004fc76545300067f655453003e7c6554530005df735453001ddc73545300075d5354530004ff7650530004fe7650530004fc7650530005df735053001ddc73505300079d4350530004fe76c8530004fd76c8530
  | 10 => 0x953003cff7659530255df73595300bdfb70595300067f7559530004ff7459530024fe7459530024fc7459530254ff7359530006df73595300a6de4359530004ff725953005cfc7259530004ff7159530014fe7159530014fc715953023cff7059530006fb705953023e7e505953023e7c50595303b4fe761953003e7e65195300067d6519530085be7419530005bd7419530024fe76d9130086be64d913003cfe75d9130004fd75d913022cfd74d913000cff73d913001cfe73d913000cfd73d913001cfc73d91303aede53d91303aebf43d91303aebd43d913005cfe72d9130004fd72d9130014fe71d9130004fd71d9130014fc71d913001cff70d913001cfd70d913039ebf40d913039ebd40d913039efa10d9130024ff76591300057f75591300057c7559130086bc6459130395df73591303a5fb7059130004ff75591300067f75591300047f755913003cfc75591300067c755913003c7c755913039cff7459130006bf7459130086be5459130394ff7359130006df7359130096de5359130004ff725913005cfc7259130086bf4259130004ff7159130014fe7159130014fc715913022cff7059130006fb705913022ebe405913022ebc405913022efa105913003cff76d5130004fe76d5130004fd76d513003cfc76d513003e7e65d51300067d65d51300873e54d513001dde73d5130005dd73d5130004ff7655130004fe7655130004fd7655130004fc765513003e7e65551300067d6555130026be6455130006bd645513001dde7355130005fb705513000df8705513000ddc7654d3003edc7654d3000cdc7654d3001ddf7554d3001f5f7554d300075f6554d3003ede6554d3003edc6554d300075c6554d30005df7454d30006df6454d30006dd6454d300075f5454d300075d5454d30005df7254d3007dde7154d3007ddc7154d30007db7054d3000dde7054d3000ddc7054d3023fd87054d3001edf6054d3001fdb6054d3023f5e5054d3023f5c5054d3023fda2054d3023fda1054d3000ddc7650d30026dc7650d3000cdc7650d30005df7550d30005dd7550d30006df6550d30006dd6550d3001ddf7450d3001f9f7450d300079f6450d30026de6450d30026dc6450d300879c6450d300879e5450d300079d5450d30005df7250d300879f4250d3007dde7150d3007ddc7150d300879f4150d30007db7050d3000dde7050d3000ddc7050d3022fd87050d3001edf6050d3001fdb6050d3022f9e4050d3022f9c4050d3022fda2050d3022fda1050d3003cfe75d8930004fd75d8930024fe74d8930004fd74d8930024fc74d893000cfd73d893038eee32d893038eed32d8930014fe71d8930004fd71d8930014fc71d893001cfd70d8930356ef20d8930356fa10d8930006ef629893004df970989300057f75589300057c755893006df
  | 11 => 0x3cfe7518940004fd751894000cfd741894005ebd741894001cfe7318940004fd731894005cfc731894005ebf421894005eee4218940366ed4218940014fe7118940004fd7118940014fc711894005cff7018940024fd701894005eef2018940346ed2018940004fe76d4940004fd76d494003cfc76d49400067f65d494003e7c65d4940025be74d4940005bd74d49402273e54d4940004fe7694940004fd769494005cfc76949400067f659494003e7c6594940025be7494940005bd74949400073d5494940004ff7654940004fe7654940004fc76549400067f655494003e7c6554940025be74549401e73e5454940004fe7614940004fd761494005cfc76149400067f651494003e7c6514940025be7414940005bd74149400073d541494000dfa7014940005f9701494000dbc765094017ebc765094000cbc7650940005bf7550940005bd75509400073f65509403d6be65509403d6bc65509400073c65509400063c6550940006bf6350940025bf7250940027af7250940007af625094005ebc6250940007ac6250940007bb705094000dbe705094000dbc705094017fb87050940026bf6050940027bb605094017fba1050940004fe768c940004fd768c94005cfc768c9400067f658c9400067c658c940025be748c940005bd748c940004ff764c940004fe764c940004fc764c9400067f654c9400067c654c940014fe76d85400067f65d85400067c65d854008ef661d854003cfe75d8540004fd75d854000cfd74d8540014fc74d854001cfe73d8540004fd73d854001cfc73d854005cfe72d8540004fd72d85403cebf42d8540006bd42d854008ef641d85403cef541d8540024fd70d85402fef710d85400057f75585400057c75585400067f65585400067c655854008ef461585403c5fb7058540004fe76d4540004fd76d454003cfc76d45400067f65d454003e7c65d4540025be74d4540005bd74d45400073d54d4540004ff7654540004fe7654540004fc76545400067f655454003e7c65545400073d5454540004ff764c540004fe764c540004fc764c5400067f654c5400067c654c540004fe76c8540004fd76c854005cfc76c85400067f65c85400067c65c8540025be74c8540005bd74c8540007ad42c8540004ff7648540004fe7648540004fc76485400067f65485400067c6548540005df7348540095dc7348540007ad424854003cfe76d9530024fe74d9530004fd74d9530024fc74d95300067e54d95300067c54d953000cff73d953001cfe73d953000cfd73d953001cfc73d95303be7f53d95303be7d53d95303bede43d953005cfe72d9530004fd72d9530014fe71d9530004fd71d9530014fc71d953001cff70d953001cfd70d95303b67f50d95303b67d50d953023cfd76995300067f659953023ddd73995300a5f9709
  | 12 => 0xe76195400067e76195403fc7e76195403f73e74195403ef3d74195400075e73195400075d73195400067e63195400067c63195403f73f42195400067e61195400067c61195403f77b40195403ef3e40195403ef3c40195403ef7840195403ef7a101954003e7f741954003e7e741954003e3e741954003e7d741954003e3d741954003e7c741954003e7f731954003e7e731954003e5e731954003e7d731954003e5d731954003e7c73195403f67f43195403f67e43195403f67d43195403f67c431954003e7f721954003e7e721954003e7d721954003e7c72195403f67f42195403f63f42195403f67e42195403f67d42195403f67c42195400067f32195400067c321954003e7f711954003e7e711954003e7d711954003e7c71195403f67f41195403f67e41195403f67d41195403f67c41195400067f31195400067e31195400067c31195400067e21195400067c211954003e7f701954003e7e701954003e7d701954003e7c70195403ee7f40195403ee7e40195403ee7d40195403ee7c40195403ee7f30195403ee7e30195403ee7d30195403ee7c30195403ee7f20195403ee7e20195403ee7d20195403ee7c20195403ee7f10195403ee7e10195403ee7a10195403ee7d10195403ee7c101954000dbc765514003ebc765514000cbc7655140025bf75551400273f75551400073f655514003ebe655514003ebc65551400073c6555140005bf7255140007bb705514000dbe705514000dbc705514026fb87055140026bf6055140027bb605514026f3f505514026f3d505514026fba105514001cfe76d8d400067f65d8d400067c65d8d40096de63d8d4003cfe75d8d40004fd75d8d4000cfd74d8d4001cfc74d8d403e6be54d8d40006bd54d8d40096de43d8d403e6dd43d8d4005cfe72d8d40004fd72d8d403e6bf42d8d40014fe71d8d40004fd71d8d40014fc71d8d40024fd70d8d40396be40d8d40396bc40d8d40396df30d8d40396fa10d8d400057f7558d400057c7558d400067f6558d400067c6558d40096dc6358d403ddfb7058d40004fe76d4d40004fd76d4d4003cfc76d4d400067f65d4d4003e7c65d4d40025be74d4d40005bd74d4d400073d54d4d40004ff7654d40004fe7654d40004fc7654d400067f6554d4003e7c6554d400073d5454d4001ede6354d400067f65d89400067c65d894003cfe75d8940004fd75d894000cfd74d894001cfe73d8940004fd73d894001cfc73d894033eee42d894033eed42d8940014fe71d8940004fd71d8940014fc71d8940024fd70d894035eef20d894035efa10d89400057e75989400057d75989400067f65989400067c6598940006ef6298940055f970989400057f75589400057c75589400067f65589400067c6558940075fb70589400067f65189400067c6518940006ed6218940
  | 13 => 0xc95005cfc768c95003d7e758c9500057d758c950004ff764c950004fe764c950004fc764c950014fe76d855009ef661d855000cfd75d8550014fc75d8550024fe74d8550004fd74d8550024fc74d85500067f54d85500067d54d855001cfe73d8550004fd73d855001cfc73d855005cfe72d8550004fd72d85500067f52d85500067d52d855009ef651d855003cfd70d855040efb50d85501367e50d85501367c50d8550136f850d8550136f710d8550005bf74585500adbc745855009ef4615855000cfc765455011e7f6554550006f76154550016f46154550005fb705455000df8705455003f785054550004ff7650550004fe7650550004fc7650550004ff764c550004fe764c550004fc764c550004fe76c8550004fd76c855005cfc76c855003d7e75c85500057d75c8550004ff7648550004fe7648550004fc7648550005df73485500a5dc734855003cfe76d954000cff74d9540024fe74d954000cfd74d9540024fc74d95404067f54d95404067d54d954001cfe73d9540004fd73d954001cfc73d95400067e53d95400067c53d954005cfe72d9540004fd72d9540014fe71d9540004fd71d9540014fc71d95400067e51d95400067c51d9540024ff70d9540024fd70d95403fe7f50d95403fe7d50d954003c7e76d95403ff3f74d95403ff3c74d95400067e63d95400067c63d95404073f42d95400067e61d95400067c61d95404077b40d95403ff3e40d95403ff3c40d95403ff7840d95403ff7a10d95403fe7f74d95404067e74d95403fe7d74d95403fe7c74d95400067f73d95400067e73d95400067d73d95400067c73d95404067f43d95404067e43d95404067d43d95404067c43d95400067f72d95400067e72d95400067d72d95400067c72d95404067f42d95404067e42d95404067d42d95404067c42d95400067f32d95400067c32d95400067f71d95400067e71d95400067d71d95400067c71d95404067f41d95404067e41d95404067d41d95404067c41d95400067f31d95400067e31d95400067c31d95400067e21d95400067c21d95403fe7f70d95403fe7e70d95403fe7d70d95403fe7c70d95403fe7f40d95403fe7e40d95403fe7c40d95403fe7f30d95403fe7e30d95403fe7d30d95403fe7c30d95403fe7f20d95403fe7e20d95403fe7d20d95403fe7c20d95403fe7f10d95403fe7e10d95403fe7d10d95403fe7c10d954026cfd76995400067f659954026dbd74995400adf9709954003cff7659540285bf74595400c5fb70595400067f7559540284ff7459540006bf7459540004ff735954001cfe735954001cfc7359540004ff725954005cfc7259540004ff7159540014fe7159540014fc715954026cff7059540006fb70595403fcfe761954003e7e65195400067d6519540095de7319540005dd73195403fd7
  | 14 => 0xaebf42d9150014fe71d9150004fd71d9150014fc71d9150006be41d91500aebc41d915003cfd70d9150286bf40d91500aebc64591503ed7e76d515003e7e76d51503ec7e76d515026d7d74d51500267e64d51500267c64d51500057d72d51500af3f42d515000d7e70d515000d7c70d515003e7f60d515003f7b60d515000cfc7655150006bf6455150026bc645515003f3c5455150005fb705515000df8705515000d7c76551500267c765515000c7c765515003d7f745515003f3f74551500073f64551500267e64551500267c64551500af3c64551500af3f43551500057f72551500077b705515000d7e705515000d7c705515026f78705515003e7f605515003f7b605515026f3f405515001cfe76d8d500a6de63d8d5000cfd75d8d5001cfc75d8d50024fe74d8d50004fd74d8d50024fc74d8d500067f54d8d500067d54d8d500a6de53d8d5005cfe72d8d50004fd72d8d50014fe71d8d50004fd71d8d50014fc71d8d5003cfd70d8d502567e50d8d502567c50d8d50256df30d8d500a6dc6358d5000cfc7654d5023e7f6554d50006df6354d5001edc6354d50005fb7054d5000df87054d50004ff7650d50004fe7650d50004fc7650d50006bf6450d50026bc6450d500073d5450d5001ede6350d50024fe74d8950004fd74d8950024fc74d895001cfe73d8950004fd73d895001cfc73d8950014fe71d8950004fd71d8950014fc71d895003cfd70d895020eef20d89500adbe7498950005bd7498950006ef6298950006ed621895005e7d7518950024fe7418950004fd741895005cfc74189500067f54189500067d541895001cfe7318950004fd731895005cfc7318950014fe7118950004fd7118950014fc711895005cff701895003cfd70189501ae7e50189501ae7c501895005eef20189501aeed20189501ad7e76d495003e7e76d49501ac7e76d49500057d74d49502267e64d49502267c64d49500067f63d495005e7c62d495000d7e70d495000d7c70d495003e7f60d495003f7b60d495000cfe76949501cd7d75949501ee7f65949500adbe7494950005bd7494950006ef629495005eec629495000dfa7094950005f9709495000cfc7654950006ef6254950006ec625495003f6c5254950005fb705495000df8705495000d7c76549501ce7c765495000c7c76549500057f74549501e67e64549501e67c64549500067f635495003d7f725495003f6f72549500076f625495005e7c62549500076c62549500077b705495000d7e705495000d7c70549501cf78705495003e7f605495003f7b6054950004fe7690950004fd769095005cfc769095003d7e75909500057d7590950004ff7650950004fe7650950004fc765095003d7e75509500057d7550950006bf6450950026bc64509500073f5450950004fe768c950004fd768
  | 15 => 0xa105935003d7f76553503f67f76553503fc7f765535003f3f745535003f3f64553500267e64553500267c645535003f3c64553500c73f43553500057f725535000d7e705535000d7c705535026f3f405535026f7a105535000cfe7558f5001cfd7558f5000cfc7558f50004ff7458f50024fe7458f50024fc7458f5003e7f5458f500067d5458f5003edf7358f5003edf5358f5003edc5358f500bede4358f50004ff7258f5005cfc7258f5003e7f5258f50004ff7158f50014fe7158f50014fc7158f5023e7e5058f5003e7c5058f5023edf3058f5023efa1058f50004ff7650f50004fd7650f5003cfc7650f50026be6450f50006bd6450f500073d5450f5001ede6350f50006dd6350f5000cfe7598b5005e7e7598b5000c7e7598b5000cfc7598b50024fe7498b5005ebe7498b50024be7498b50004fd7498b5005ebd7498b50004bd7498b5005cfc7498b5003e7f5498b500067d5498b5001cfe7398b50004fd7398b5005cfc7398b5005eee7298b5005e7f5298b5003eef5298b5005eec5298b50014fe7198b50004fd7198b50014fc7198b501ee7e5098b5003e7c5098b5005eef2098b501eeed2098b5000cfc7558b50004ff7458b50024fe7458b50024fc7458b50004ff7358b5001cfe7358b5001cfc7358b5003eef7258b5003eef5258b5003eec5258b50004ff7158b50014fe7158b50014fc7158b501ceef2058b501cefa1058b5003d7f7654b500067f7654b501ec7f7654b500057f7454b501e67e6454b5003e7c6454b500067d6354b5003f6f7254b5003f6f6254b5005e7e6254b5003f6c6254b5000d7e7054b5000d7c7054b501cf7a1054b5005cff7690b5003cfe7690b50004fd7690b5003d7e7590b500057d7590b50004ff7650b50004fd7650b5003cfc7650b5003d7e7550b500057d7550b50026bc6450b503d73f5450b50005fb7050b5000df87050b5005cff768cb5003cfe768cb50004fd768cb5003d7e758cb500057d758cb50004ff764cb50004fd764cb5003cfc764cb5000cfe7558750014fd755875000cfc7558750004ff7458750024fe7458750024fc745875003e7f54587500067d5458750004ff735875001cfe735875001cfc7358750004ff725875005cfc725875003e7f52587500067d525875003ef7715875003ef7515875003ef4515875011e7e505875003e7c505875011ef71058750004ff7650750004fd765075003cfc7650750004ff764c750004fd764c75003cfc764c75005cff76c875003cfe76c8750004fd76c875003d7e75c87500057d75c8750004ff7648750004fd764875003cfc7648750005df73487500bddc7348750024fe76d91500aebe64d915000cfd75d9150024fc75d91500aebe54d915001cfe73d9150004fd73d915001cfc73d91500aebf43d915005cfe72d9150004fd72d9150
  | 16 => 0x921006df635092118edc63509210dfac4250921005f77150921015f47150921015ec7650921026ec7650921014ec765092119def7450921007af7450921007af6450921026ee6450921026ec64509210dfac6450921007af54509210dfac5450921005ef7350921007cf6350921007cc63509210dfaf4350921007ad4350921007e77150921015ee7150921015ec7150921187e47150921186ef6150921187af4150921187ad4150921187e631509210dfaf4050921187e7105092141cfe768c92116edf638c92101edc638c921015f4718c92116fd6318c92105fe4218c92141dee768c921416ee768c921005ef748c921005ed748c921155ed738c92116fcf638c92101eee638c92101eec638c9210d7cc638c92101ecc638c9210d7ce438c921007cd438c92105fe7718c921015ee718c921015ec718c92105fe4718c92105eef618c92116fce318c92116fe6318c92116fc6318c92116fcc318c92116fe7108c92101cff764c921014fe764c921154fd764c921014fc764c921006df634c92101edc634c9210d7cc324c921005f7714c921015f4714c921157e4214c921015ec764c92101eec764c921014ec764c921005ef744c921005ed744c92116def734c921007cf734c921007cf634c92101eee634c92101eec634c9210d7cc634c921007e7714c921015ee714c921015ec714c921157e4714c921156ef614c921157cf314c921157e6314c921157cd314c9210d7cf304c921157e7104c9210d5f4764c52101ef4764c52101cf4764c521015f7734c521017d7734c521007d7634c52101ef6634c52101ef4634c5210d7d4634c5210d7d6434c521007d5434c521007e7724c52105df4724c521007e4724c521016f7624c521017e7624c521007e6424c521007e5424c5210d7d7324c5210d7e6324c521007d5324c5210d7e5324c521007c5324c521005f7704c52105df773c8521005f573c8521007d763c8521007d463c8521015f672c8521017e672c8521016f762c8521017e762c852105fe642c8521007e542c852105fe632c8521007e532c8521005f570c852100cfe76d8121006df63d8121006dc63d81210cefa60d812103cfe75d8121004fd75d8121024fe74d8121004fd74d8121024fc74d812101cfe73d8121004fd73d812101cfc73d8121014fd72d8121006ee42d8121006ed42d812100cfc71d81210cefa20d81210cefa10d81210057f75581210057c7558121005bf74581210ddbc7458121005df73581210d5dc7358121006df6358121006dc63581210cef8605812100cfe7559350024fd755935000cfc755935003ebf745935003ebf545935003ebc5459350004ff735935001cfe735935001cfc73593500c6bf4359350004ff725935005cfc7259350004ff7159350014fe7159350014fc715935026ebf405935026ef
  | 17 => 0x6dc60d8d2116fd710d8d21006df75d8d21006de75d8d21006dd75d8d21006dc75d8d21006df74d8d21006de74d8d21006dd74d8d21006dc74d8d21006df54d8d21006de54d8d21006dd54d8d21006dc54d8d2116edf72d8d210d6de72d8d2116edd72d8d21006df42d8d21006dc42d8d2116edf71d8d2116ede71d8d2116edd71d8d2116edc71d8d2116edf51d8d2116ede51d8d2116edd51d8d2116edc51d8d2116edf41d8d2116ede41d8d2116edd41d8d2116edc41d8d2116edf21d8d2116ede21d8d2116edc21d8d21006df70d8d21006de70d8d21006dd70d8d21006dc70d8d21006de50d8d21006dc50d8d21006df40d8d21006de40d8d21006dc40d8d21006de20d8d21006dc20d8d2116edf10d8d2116ede10d8d2116edd10d8d2116edc10d8d210d6dc6358d21435ef7258d21004ff7558d2103cfc7558d21004ff7458d21024fe7458d21024fc7458d2116cff7358d21006df7358d21434ff7258d21006ef7258d21154ff7158d21006f77158d21004ff7058d2100cfe7058d2100cfc7058d2116dde7618d210d6de7618d2116cde7618d210d75e7518d210d75d7518d21006df6518d21006de6518d21006dd6518d21006dc6518d210d79e7418d210d79d7418d21006df6418d21006de6418d21006dd6418d21006dc6418d2141fcd7218d2141edf6218d2141fd67118d210d7d57118d2141edf6118d2141fce2118d2141fcc2118d2141fd42118d210d7da7018d210d7d97018d21006de6018d21006dc6018d2141fd71018d2103cff76d4d21004fe76d4d21004fd76d4d2103cfc76d4d2103e7e65d4d210067d65d4d21006df63d4d2101edc63d4d21004ff7654d21004fe7654d21004fd7654d21004fc7654d2103e7e6554d210067d6554d21006df6354d2101edc6354d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21026be6450d21006bd6450d21006df6350d2101edc6350d21014fe76d4921014fc76d49210067f65d492103e7c65d4921006df63d492121edc63d4921015f671d4921005f571d49211b4fe76949210ddbe7494921005bd7494921006df63949211fedc639492105fe4219492103cff7654921014fe76549211d4fd7654921014fc76549210067f655492103e7c6554921006df63549211dedc6354921005f77154921015f471549211d7e421549211f4fe7614921006df63149211bedc631492142cfe76909210057e75909210057d7590921006df63909211a6dc639092142dee7690921426ee76909210076e75909210076d7590921185ed7490921026ee6490921026ec6490921005ed7390921007cf6390921007cc6390921015ee7190921015ec719092105eef619092119fe6319092119fe71090921024ff7650921014fe7650921184fd7650921014fc7650921006bf6450921026bc645
  | 18 => 0x86058321004ff75583210067f75583210047f755832103cfc75583210067c755832103c7c7558321004ff7458321024fe7458321024fc7458321004ff735832101cfe735832101cfc7358321014fc7258321006ee4258321006ed4258321046f621583210e6fa305832105efb205832105ef820583210e6fa105832103cfe76d9521024fe74d9521004fd74d9521024fc74d952101cfe73d9521004fd73d952101cfc73d952105cff71d95211f4fd71d95211f67f51d95211f67d51d952100cfe70d9521004fd70d952100cfc70d95210067e50d95210067c50d95211f6f710d95210067f65995210ddbe7499521005bd74995210d5de7399521005dd73995211d5ed7299521005df73595210d5dc7359521215ef72595210067f7559521004ff7459521024fe7459521024fc7459521004ff7359521006df7359521004df735952101cfe735952101cfc7359521006dc735952101cdc7359521214ff7259521006ef72595211d4ff7159521006f77159521004ff705952100cfe705952100cfc70595211d6f710595211f4fe761952103e7e65195210067d6519521024fe76d91210debe64d912103cfe75d9121004fd75d91210debe54d912101cfe73d9121004fd73d912101cfc73d9121014fd72d91210debf42d912105cff71d912119cfd71d912119ebf41d912119ebd41d912100cfe70d9121004fd70d912100cfc70d9121006be40d91210debc40d912119ef710d91210debc6459121005df73591210d5dc735912143def7259121004ff755912103cfc755912119cff7459121006bf7459121004ff7359121006df7359121004df735912101cfe735912101cfc7359121006dc735912101cdc73591210debf435912143cff7259121006ef7259121184ff7159121006f77159121004ff705912100cfe705912100cfc7059121186f7105912103cff76d5121004fe76d5121004fd76d512103cfc76d51210067f65d512103e7c65d51210df3e54d5121296dc63d5121004ff7655121004fe7655121004fd7655121004fc76551210067f655512103e7c6555121006bf6455121026bc645512127edc635512101cfe76d8d210d6de63d8d2103cfe75d8d21004fd75d8d21024fe74d8d21004fd74d8d21024fc74d8d210d6de53d8d210d6dc53d8d21006df43d8d210d6de43d8d210d6dc43d8d21014fd72d8d210d6df32d8d2105cff71d8d2116cfd71d8d2116edf31d8d2116edd31d8d2100cfe70d8d21004fd70d8d2100cfc70d8d210d6df30d8d21006de30d8d210d6dc30d8d2141dde76d8d2101cde76d8d21006df65d8d21006de65d8d21006dd65d8d21006dc65d8d21006df64d8d21006de64d8d21006dd64d8d21006dc64d8d2116fcf72d8d21007d771d8d2116fd471d8d2116fce21d8d2116fcc21d8d2116fd421d8d21006de60d8d21
  | 19 => 0x9321004ff755932103cfc755932105ebf74593210f6bc5459321004ff735932101cfe735932101cfc73593210f6bf4359321014fe7259321014fc725932105ebe425932105ebc4259321186bf4159321186bd4159321004ff705932100cfe705932100cfc70593210f6bf405932103cff76d532105cfe76d5321004fd76d532105cfc76d53210067f65d532103e7c65d5321026be64d5321006bd64d53210f73e54d5321004ff765532105cfe7655321004fd765532105cfc76553210067f655532103e7c655532103cfe75d8f21004fd75d8f21024fe74d8f21004fd74d8f2105cfc74d8f21154fd73d8f210eede43d8f2105cfe72d8f2105eee72d8f2105edf32d8f2105ef571d8f2116ede31d8f2116edc31d8f2105ef621d8f2100cfe70d8f21004fd70d8f2100cfc70d8f2101cff7658f2105edc6358f21004ff7558f2103cfc7558f21004ff7458f21024fe7458f21024fc7458f2105edf7358f21014fe7258f21014fc7258f2105ede3258f2105edc3258f21156df3158f21156dd3158f21156f62158f21004ff7058f2100cfe7058f2100cfc7058f210eedf3058f2103cff76d4f2105cfe76d4f21004fd76d4f2105cfc76d4f2103e7e65d4f210067d65d4f21004ff7654f2105cfe7654f21004fd7654f2105cfc7654f2103e7e6554f210067d6554f21004ff7650f2105cfe7650f21004fd7650f2105cfc7650f21026be6450f21006bd6450f21006df6350f2101edc6350f21005f77150f21015f47150f211d4fd76d4b2105e7f65d4b2105e7c65d4b21214ff7654b2105e7f6554b2105e7c6554b21015ed7690b2105eed7690b21014ed7690b2105f6e7590b2105f6d7590b21026ee6490b2105fae6490b2105fad6490b2105eec6490b21005ed7390b21015ee7190b2105fe67190b2105fe57190b21015ec7190b2143cff7650b2105ebf6450b2105ebc6450b2105fac4250b2143def7650b2144eef7650b2105faf7450b2105faf6450b21026ee6450b21026ec6450b2105fac6450b21007af5450b210f7ac5450b21005ef7350b210f7af4350b21007ad4350b21015ee7150b21015ec7150b21187af4150b21187ad4150b210f7af4050b21015ed768cb2105eed768cb21014ed768cb2105def748cb21005ed748cb2101eee638cb2105fce638cb2105fcd638cb2105eec638cb210efce438cb21007cd438cb21015ee718cb2105fe6718cb2105fe5718cb21015ec718cb2116fce318cb2116fcc318cb21434ff764cb2105edf634cb2105edc634cb2105fcc324cb21435ef764cb21446ef764cb21005ef744cb21005ed744cb2105fcf734cb2105fcf634cb2101eee634cb2101eec634cb2105fcc634cb21015ee714cb21015ec714cb21157cf314cb21157cd314cb210efcf304cb2100cff76583210057f75583210057c755832105ef
  | 20 => 0x14fd731893105edd7318931446de4318931006dd431893105edf321893105eee3218931446ed321893105cff711893101cfd711893105ef5711893141ede311893141edc311893105eef211893105ef6211893141eed211893100cfe701893105efa701893100cfa7018931004fd701893105ef97018931004f9701893100cfc7018931004fe76d4931004fd76d493103cfc76d493103e7e65d49310067d65d4931004fe7694931004fd769493105cfc7694931105be7494931005bd749493101dde7394931005dd7394931015f67194931005f57194931004ff7654931004fe7654931004fc765493103e7e65549310067d6554931004fe7614931004fd761493105cfc761493101dde7314931005dd7314931015f67114931005f57114931004fe7690931004fd769093105cfc76909310057e75909310057d759093101dde7390931005dd7390931015f67190931005f57190931004ff7650931004fe7650931004fc7650931026be6450931006bd645093101dde73509310079d4350931015dc764c931156dc764c931014dc764c931005df744c931005dd744c93101ddf724c93101fcf724c931007cf624c93105edc624c931007cc624c931007d7714c931015de714c931015dc714c931157d4714c93101edf614c93101fd7614c931157d6214c93100cfe76d81310057e75d81310057d75d81310fefa60d813103cfe75d81310067e75d813103c7e75d8131004fd75d81310067d75d81310047d75d8131024fe74d8131004fd74d8131024fc74d8131014fd73d813100cfc73d8131376de43d8131006dd43d813105cfe72d8131004fd72d8131376df32d8131006dd32d813101cfd71d8131376f731d81312eede31d81312eedc31d81312eef431d81312eef621d81310fefa30d81310fefa10d81310fef86058131024fe74d972105ebe74d9721024be74d9721004fd74d972105ebd74d9721004bd74d972105cfc74d972101cfe73d9721004fd73d972105cfc73d972105cfe72d972105eee72d972105ef571d972100cfe70d9721004fd70d972100cfc70d97210067e50d97210067c50d97211d4fd769972105e7f659972105e7c659972103cff765972105e7c655972105e7f7559721004ff7459721024fe7459721024fc74597210067e54597210067c5459721004ff735972101cfe735972101cfc7359721014fe7259721014fc725972105e7e525972105e7c52597211d67f51597211d67d5159721004ff705972100cfe705972100cfc705972103cfe75d932105e7e75d932103c7e75d9321004fd75d932105e7d75d93210047d75d9321184fd74d932101cfe73d9321004fd73d932105cfc73d932105cfe72d932105eee72d932105ebf42d932105ef571d932100cfe70d9321004fd70d932100cfc70d9321024ff765932105ebc645
  | 21 => 0xd74d814100cfc74d814101cfe73d8141004fd73d814101cfc73d814105cfe72d8141004fd72d81413c6bf42d8141006bd42d8141024fd71d814110efa40d814110efa10d81410057f75581410057c755814110ef8605814103cfe76d9531024fe74d9531004fd74d9531024fc74d9531014ff73d9531014fd73d95314867f53d95314867d53d9531486de43d953105cfe72d9531004fd72d953101cff71d953101cfd71d953147e7f51d953147e7d51d953100cfe70d9531004fd70d953100cfc70d9531244fd76995310067f6599531245dd7399531125f5719953103cff765953125ddf735953113df771595310067f7559531004ff7459531024fe7459531024fc745953125cff7359531006df7359531126de4359531004ff725953105cfc7259531244ff7159531006f77159531004ff705953100cfe705953100cfc70595310067e50595310067c505953147cfe761953103e7e65195310067d6519531024fe76d9131106be64d913103cfe75d9131004fd75d9131234fd74d9131014ff73d9131014fd73d9131476bf43d9131476bd43d913105cfe72d9131004fd72d913101cff71d913101cfd71d9131466bf41d9131466bd41d913100cfe70d9131004fd70d913100cfc70d9131024ff7659131106bc645913145ddf735913146df77159131004ff755913103cfc7559131464ff7459131006bf745913145cff7359131006df7359131004ff725913105cfc7259131106bf4259131234ff7159131006f77159131004ff705913100cfe705913100cfc705913103cff76d5131004fe76d5131004fd76d513103cfc76d513103e7e65d51310067d65d51311073e54d5131004ff7655131004fe7655131004fd7655131004fc765513103e7e65551310067d6555131015dc7650d31026dc7650d31014dc7650d31006df6550d31006dd6550d3101ddf7450d3101f9f7450d310079f6450d31026de6450d31026dc6450d311079c6450d311079e5450d310079d5450d31005df7250d311079f4250d31007d77150d31015de7150d31015dc7150d31237d47150d31015d47150d3101edf6150d3101fd76150d312379f4150d312379d4150d31237d62150d314579e4050d311079c4050d3103cfe75d8931004fd75d8931024fe74d8931004fd74d8931024fc74d8931014fd73d8931416ee32d8931416ed32d893101cfd71d8931436ef21d893100cfe70d8931004fd70d893100cfc70d8931006ef62989310d5f571989310edf771589310057e75189310057d7518931105be7418931005bd7418931006ed62189310fdfa7018931005f9701893103cfe751893105e7e751893103c7e7518931004fd751893105e7d75189310047d7518931024fe741893105ebe7418931024be7418931004fd741893105ebd7418931004bd741893105cfc7418931
  | 22 => 0x9541006bf7459541004ff735954101cfe735954101cfc735954112ebf4359541004ff725954105cfc7259541274ff7159541006f77159541004ff705954100cfe705954100cfc7059541276f7105954149cfe761954103e7e65195410067d651954101cfe76d8d41116de63d8d4103cfe75d8d41004fd75d8d41014fd74d8d41116de43d8d41496dd43d8d4105cfe72d8d41004fd72d8d41496bf42d8d41116dc32d8d41024fd71d8d4145edf31d8d4100cfe70d8d41004fd70d8d4100cfc70d8d41116df30d8d41116dc6358d4148df77158d41004fe76d4d41004fd76d4d4103cfc76d4d4103e7e65d4d410067d65d4d41004ff7654d41004fe7654d41004fc7654d4103e7e6554d410067d6554d41015bc7650d4101ebc7650d41014bc7650d41006bf6550d41006bd6550d41025bf7350d410279f7350d410079f6350d4101ebe6350d4101ebc6350d411179c6350d411179e5350d410079d5350d41005bf7250d411179c3250d41007b77150d41015be7150d41015bc7150d41237b47150d41026bf6150d41027b76150d412379f3150d4122ebe6050d4122ebc6050d411179f3050d41237b71050d4103cfe75d8941004fd75d8941014fd74d894101cfe73d8941004fd73d894101cfc73d8941426bf43d8941006bd43d8941426ee42d8941426ed42d8941024fd71d894143eef21d894100cfe70d8941004fd70d894100cfc70d894143ef710d89410057e75989410057d7598941006ef62989410ddf57198941005df7358941115dc73589410f5f77158941006ed621894103cfe7518941004fd7518941014fd741894105ebd741894101cfe7318941004fd731894105cfc731894105ebf421894105eee421894144eed421894105cff7118941024fd711894105eef211894142eed211894100cfe7018941004fd701894100cfc7018941004fe76d4941004fd76d494103cfc76d49410067f65d494103e7c65d4941004fe7694941004fd769494105cfc7694941025be7494941005bd7494941004ff7654941004fe7654941004fc76549410067f655494103e7c6554941004fe7614941004fd761494105cfc7614941025be7414941005bd7414941015f67114941005f57114941015bc7650941186bc7650941014bc76509413d6be65509413d6bc6550941005bf7350941006bf6350941025bf7250941027af7250941007af625094105ebc6250941007ac6250941007b77150941015be7150941015bc7150941187b47150941026bf6150941027b76150941187b71050941004fe768c941004fd768c94105cfc768c941025be748c941005bd748c941006df638c94101edc638c9410079d438c941004ff764c941004fe764c941004fc764c941025be744c941005bd744c94100cfe76d814110efa60d814103cfe75d8141004fd75d8141014f
  | 23 => 0x24fc74d895101cfe73d8951004fd73d895101cfc73d89510067f53d89510067d53d895103cfd71d8951216ef21d895100cfe70d8951004fd70d895100cfc70d8951216f710d895112dbe7498951005bd7498951006ef6298951005df7358951125dc7358951006ed621895105e7d7518951024fe7418951004fd741895105cfc74189510067f54189510067d541895101cfe7318951004fd731895105cfc731895105cff711895103cfd711895105eef21189511b6ed211895100cfe7018951004fd701895100cfc70189510067e50189510067c50189511b57e76d495103e7e76d49510057d74d49512267e64d49512267c64d49510057d73d49510067f63d495105e7c62d49510157e71d49510157c71d495103e7f61d495103f7761d495111d7e70d495103d7c70d49512177710d4951014fe76949511d57d759495112dbe7494951005bd7494951006ef629495105eec6294951015f67194951005f57194951014fc7654951006ef6254951006ec6254951005f77154951015f471549510157c76549511d67c76549510147c76549510057f74549511e67e64549511e67c64549510057f73549510067f635495103d7f725495103f6f72549510076f625495105e7c62549510076c62549510077771549510157e71549510157c71549511d774715495103e7f615495103f77615495111d7e705495111d7c70549511d7771054951004fe7690951004fd769095105cfc769095103d7e75909510057d7590951004ff7650951004fe7650951004fc765095103d7e75509510057d7550951006bf6450951026bc64509510073f5450951004fe768c951004fd768c95105cfc768c95103d7e758c9510057d758c951006df638c95101edc638c951004ff764c951004fe764c951004fc764c95103d7e754c9510057d754c95100cfe76d815103d7e75d81510157d75d815111efa60d815111f7a50d8151014fd75d815111e7d75d81510147d75d815100cfc75d8151024fe74d8151004fd74d8151024fc74d81510067f54d81510067d54d815101cfe73d8151004fd73d815101cfc73d815105cfe72d8151004fd72d81510067f52d81510067d52d815103cfd71d815111e7e50d815111efa50d815111e7c50d815111efa10d8151005bf745815112dbc745815111ef8605815111f78505815103cfe76d9541014ff74d9541014fd74d95414a67f54d95414a67d54d954101cfe73d9541004fd73d954101cfc73d95414a6bf43d954105cfe72d9541004fd72d9541024ff71d9541024fd71d954149e7f51d954149e7d51d954100cfe70d9541004fd70d954100cfc70d95410067e50d95410067c50d954149ef710d9541274fd76995410067f6599541275bd749954112df5719954103cff765954128dbf7459541145f771595410067f755954128cff745
  | 24 => 0xf764cb51004fd764cb5103cfc764cb5103d7e754cb510057d754cb51014fe755835100cfd7558351014fc755835103e7c75583510147c7558351004ff7458351024fe7458351024fc745835103e7f54583510067d5458351004ff735835101cfe735835101cfc7358351004ff725835105cfc725835103e7f52583510067d525835103ef6515835103ef5515835103efb705835103efb50583511367e505835103e7c505835103ef85058351136fa1058351024fe76d915112ebe64d9151014fd75d915112ebe54d915101cfe73d9151004fd73d915101cfc73d915105cfe72d9151004fd72d915112ebf42d915103cfd71d915128ebf41d915100cfe70d9151004fd70d915100cfc70d9151006be40d915112ebc40d915128ef710d915112ebc64591514b57e76d515103e7e76d51512757d74d51510267e64d51510267c64d51510057d73d51510057d72d515112f3f42d51510157e71d51510157c71d515103e7f61d515103f7761d515111d7e70d515103d7c70d515128f7710d5151014fc7655151006bf6455151026bc6455151005f77155151015f471551510157c76551510267c76551510147c765515103d7f745515103f3f74551510073f64551510267e64551510267c645515112f3c64551510263c64551510057f735515112f3f43551510057f72551510077771551510157e71551510157c715515127774715515103e7f615515103f77615515111d7e705515111d7c705515112f3f405515127777105515101cfe76d8d51126de63d8d51014fd75d8d51024fe74d8d51004fd74d8d51024fc74d8d510067f54d8d510067d54d8d51126de53d8d5105cfe72d8d51004fd72d8d51126dc32d8d5103cfd71d8d5125edf31d8d5100cfe70d8d51004fd70d8d5100cfc70d8d510067e50d8d510067c50d8d51126df30d8d51126dc6358d514ad7e76d4d5103e7e76d4d510057d74d4d510067f64d4d512457d73d4d5101e7e63d4d5101e7c63d4d510057d72d4d510157e71d4d510157c71d4d5103e7f61d4d5103f7761d4d5111d7e70d4d5103d7c70d4d512567e60d4d512567c60d4d5125f7710d4d51014fc7654d51006df6354d5101edc6354d51005f77154d51015f47154d510157c7654d5101e7c7654d510147c7654d510057f7454d510067f6454d5103d7f7354d5103f5f7354d510075f6354d5101e7e6354d5101e7c6354d511275c6354d511275e4354d510057f7254d51007777154d510157e7154d510157c7154d51247747154d5103e7f6154d5103f776154d5111d7e7054d5111d7c7054d5123e7e6054d5123e7c6054d511275f3054d51247771054d51004ff7650d51004fe7650d51004fc7650d5103d7e7550d510057d7550d51026be6450d510073d5450d5101ede6350d510075d5350d51024fe74d8951004fd74d8951
  | 25 => 0x8132004fd75d8132024fe74d8132004fd74d8132024fc74d813201cfd72d8132014fe71d8132004fd71d8132014fc71d813214efa30d813214efa20d81320057f75581320057c755813214ef86058132014fe7559351014fc755935103ebf745935103ebf545935103ebc5459351004ff735935101cfe735935101cfc735935103e7f5359351146bf4359351004ff725935105cfc7259351146bc4259351276bf4159351004ff705935100cfe705935100cfc7059351146bf405935103d7f76553514c67f765535103f3f74553510267e64553510267c64553510057f73553511473f43553510057f72553510157e71553510157c71553511357e70553511357c70553511473f4055351014fe7558f51014fc7558f51004ff7458f51024fe7458f51024fc7458f5103e7f5458f510067d5458f5103edf7358f5103edf5358f5103edc5358f5113ede4358f51004ff7258f5105cfc7258f5103e7f5258f5113edc3258f51246df3158f51004ff7058f5100cfe7058f5100cfc7058f510067e5058f5103e7c5058f5113edf3058f5103d7f7654f514be7f7654f510057f7454f510067d6454f5103f5f7354f5101e7e6354f5101e7c6354f5113f5e4354f510057f7254f510157e7154f510157c7154f511357e7054f511357c7054f5123e7e6054f5103e7c6054f5113f5f3054f51004ff7650f51004fd7650f5103cfc7650f5103d7e7550f510057d7550f51026be6450f51006bd6450f510073d5450f5101ede6350f51006dd6350f510075d5350f51014fe7598b5105e7e7598b510147e7598b51014fc7598b51024fe7498b5105ebe7498b51024be7498b51004fd7498b5105ebd7498b51004bd7498b5105cfc7498b5103e7f5498b510067d5498b5101cfe7398b51004fd7398b5105cfc7398b5105eee7298b5105e7f5298b5103eef5298b5105eec5298b5105eef2198b511f6ed2198b5100cfe7098b51004fd7098b5100cfc7098b510067e5098b5103e7c5098b51014fc7558b51004ff7458b51024fe7458b51024fc7458b51004ff7358b5101cfe7358b5101cfc7358b5103e7f5358b510067d5358b5103eef7258b5103eef5258b5103eec5258b511d6ef2158b51004ff7058b5100cfe7058b5100cfc7058b5103d7f7654b510067f7654b510057f7454b511e67e6454b5103e7c6454b510057f7354b510067d6354b5103f6f7254b5105e7e6254b510157e7154b510157c7154b511357e7054b511357c7054b5105cff7690b5103cfe7690b51004fd7690b5103d7e7590b510057d7590b51026be6490b51006bd6490b51004ff7650b51004fd7650b5103cfc7650b5103d7e7550b510057d7550b51026bc6450b513d73f5450b5105cff768cb5103cfe768cb51004fd768cb5103d7e758cb510057d758cb5101ede638cb51006dd638cb51004f
  | 26 => 0x5cfc725823204edf3258232004ff7158232014fe7158232014fc7158232006de315823204edc3158232166fa305823205efb205823205ef82058232166fa105823203cfe76d9532024fe74d9532004fd74d9532024fc74d953205cff73d95321fcfd73d95321fe7f53d95321fe7d53d9532014fe71d9532004fd71d9532014fc71d953200cfe70d9532004fd70d953200cfc70d95320067e50d95320067c50d95321fedf30d95320067f65995321dded729953221def72595320067f7559532004ff7459532024fe7459532024fc74595321dcff7359532006df735953221cff7259532006ef7259532004ff7159532014fe7159532014fc7159532004ff705953200cfe705953200cfc70595321dedf30595321fcfe761953203e7e65195320067d6519532024fe76d913215ebe64d913203cfe75d9132004fd75d913205cff73d91321a4fd73d91321a6bf43d91321a6bd43d913201cfd72d913215ebf42d91321a6dc32d9132014fe71d9132004fd71d9132014fc71d91321a6df31d913200cfe70d9132004fd70d913200cfc70d91321a6df30d913215ebc64591324d5ef7259132005f77159132155f47159132004ff755913203cfc75591321a4ff7459132006bf745913218cff7359132006df73591324d4ff7259132006ef725913218edc3259132004ff7159132006f77159132004f77159132014fe7159132014fc7159132006f47159132014f4715913215ebf415913218edf3159132004ff705913200cfe705913200cfc705913218edf305913203cff76d5132004fe76d5132004fd76d513203cfc76d51320067f65d513203e7c65d513215f3e54d5132004ff7655132004fe7655132004fd7655132004fc76551320067f655513203e7c655513201cfe76d493201cfc76d49320067f65d493203e7c65d493201dde73d4932005dd73d49321bcfe769493215dbe7494932005bd74949320076f529493205fcc329493203cff765493201cfe76549321dcfd765493201cfc76549320067f655493203e7c6554932005df735493201ddc73549321dfcc32549321fcfe76149324ccfe76909320057e75909320057d759093205fcc3290932024ff765093201cfe765093218cfd765093201cfc7650932006bf6450932026bc6450932005df735093201ddc735093218fcc3250932006df648c932006dd648c93205dde728c93205fce728c93205edf628c93201fcf628c932005dd718c93216ede618c93216edc618c932005dd708c932014fe76d8532156f661d853203cfe75d8532004fd75d8532024fe74d8532004fd74d8532024fc74d853201cfd72d8532006f741d8532156f441d8532156f631d8532156f621d853200cfe70d8532004fd70d853200cfc70d8532156f710d8532156f4615853200cfe76d813214efa60d813203cfe75d
  | 27 => 0xc755814217ef86058142024fe74d963205ebe74d9632024be74d9632004fd74d963205ebd74d9632004bd74d963205cfc74d963205edd73d96321fede43d963205cfe72d963205eee72d9632014fe71d9632004fd71d9632014fc71d963200cfe70d9632004fd70d963200cfc70d96320067e50d96320067c50d96321dcfd769963205e7f659963205e7c659963203cff765963205e7c655963205e7f7559632004ff7459632024fe7459632024fc74596320067e54596320067c54596321de7f53596321de7d53596321dede435963205cfe725963205cfc725963205e7e525963205e7c5259632004ff7159632014fe7159632014fc7159632004ff705963200cfe705963200cfc705963203cfe75d923205e7e75d923203c7e75d9232004fd75d923205e7d75d92320047d75d923218cfd74d923205edd73d923205cfe72d923205eee72d923205ebf42d9232014fe71d9232004fd71d9232014fc71d923200cfe70d9232004fd70d923200cfc70d9232024ff765923205ebc6459232004ff755923203cfc755923205ebf7459232176bc545923218ebf435923218ebd435923205cfe725923205cfc725923205ebe425923205ebc4259232004ff7159232014fe7159232014fc7159232176bf4159232004ff705923200cfe705923200cfc7059232176bf405923203cff76d523205cfe76d5232004fd76d523205cfc76d52320067f65d523203e7c65d5232026be64d5232006bd64d52321773e54d5232004ff765523205cfe7655232004fd765523205cfc76552320067f655523203e7c6555232175df7650e32026df7650e32024df7650e32006df6550e32006dd6550e3201ddf7450e3201f9f7450e32026de6450e321779e6450e320079d6450e32026dc6450e321779e5450e320079d5450e32005df7250e32007cf7250e32007cc7250e3201ede6250e3201fce6250e321779f4250e3216dde7150e3216ddc7150e321779f4150e324df9e4050e321779c4050e321dcfd76d4a3205e7f65d4a3205e7c65d4a3205f6e52d4a3221cff7654a3205e7f6554a3205e7c6554a321dfcf3254a324d4ff7650a3205ebf6450a3205ebc6450a3201dde7350a320079d4350a32014ff765863201ddc735863205ef4615863216fd63158632004ff755863203cfc7558632004ff7458632024fe7458632024fc74586320d6de4358632006dd435863205cfc72586320d6df325863216ede315863216ef6315863216edc315863205ef7215863205ef42158632004ff705863200cfe705863200cfc705863216ef7105863200cff76582320057f75582320057c755823205ef86058232004ff75582320067f75582320047f755823203cfc75582320067c755823203c7c7558232004ff7458232024fe7458232024fc745823204ede4358232006dd4358232
  | 28 => 0x9542004fb705954200cfe705954200cfc7059542006f8705954200cf870595421e6bf4059542204fe761954203e7e65195420067d65195423d6be76d5142004be76d5142025be75d51420273e75d51423d6bf65d51420073f65d51420063f65d51423d6bd65d51423d73c65d5142005bd73d514205dbe72d51423d7ae72d5142005ae72d51423d7ad72d5142026bf62d5142027af62d5142005bd71d5142005bd70d514201cfe76d8d4218ede63d8d4203cfe75d8d42004fd75d8d4218ede43d8d42176dd43d8d42024fd72d8d4218edf32d8d42014fe71d8d42004fd71d8d42014fc71d8d42176bf41d8d42006de31d8d4218edc31d8d4200cfe70d8d42004fd70d8d4200cfc70d8d4218edc6358d424e5ef7258d42005f77158d42185f47158d42004fe76d4d42004fd76d4d4203cfc76d4d4203e7e65d4d420067d65d4d42025bc74d4d423d73f54d4d42004ff7654d42004fe7654d42004fc7654d4203e7e6554d420067d6554d42005bf7454d42025bc7454d420073f5454d42005ef7254d42005ec7254d4218dbc7650d4201ebc7650d4201cbc7650d423d5be7550d423d5bc7550d42006bf6550d42006bd6550d42025bf7350d420279f7350d420079f6350d4201ebe6350d4201ebc6350d4218f9c6350d4218f9e5350d420079d5350d42007af7250d4205dbc7250d42007ac7250d42005ac7250d42026bf6250d42027af6250d4218f9c3250d42005bf7150d4218f9f3150d42005bf7050d4222ebe6050d4222ebc6050d4218f9f3050d42024fe76d4942024fc76d49420067f65d494203e7c65d4942025be74d4942005bd74d49422273c54d49421c4fe769494203e7e65949420067d6594942025be7494942005bd74949420073f54949420076f529494205fac429494203cff7654942024fe76549421e4fd7654942024fc76549420067f655494203e7c6554942005bf7454942025bc74549421e73c54549421e7ac4254942204fe761494203e7e65149420067d651494205dbc74149423d73f54149423d5be759094205f3e75909420053e759094205f3d759094205dbc7590942005bd739094205dbe729094205fae729094205ebf6290942027af6290942005bd7190942005bd7090942014fe76d8542186f661d854203cfe75d8542004fd75d854201cfe73d8542004fd73d854201cfc73d85420f6bf43d8542006bd43d8542024fd72d8542186f641d8542006f731d8542186f431d8542186f621d854200cfe70d8542004fd70d854200cfc70d8542005df735854218ddc7358542186f4615854200cfe76d814217efa60d814203cfe75d8142004fd75d814201cfe73d8142004fd73d814201cfc73d8142024fd72d8142014fe71d8142004fd71d8142014fc71d814217ef850d814217efa40d814217efa20d81420057f75581420057
  | 29 => 0x67f73596420067e73596420067d73596420067c73596421e67f43596421e67e43596421e67d43596421e67c435964205e7e725964205e7c72596421e67f425964205e7e42596421e67d425964205e7c42596420067f325964205e7e325964205e7c32596420067f71596420067e71596420067d71596420067c71596421e67f41596421e67e41596421e67d41596421e67c41596420067f31596420067e31596420067c315964205e7f21596420067e215964205e7c21596420067f70596420067e70596420067d70596420067c70596421e67f40596421e67e40596421e67d40596421e67c40596420067f30596420067e30596420067c305964205e7f20596420067e205964205e7c20596420067f10596420067e10596420067c105964201cff7658e420067e6558e420067d6558e4205edc6358e42004ff7558e4203cfc7558e421a6de4358e4215edd4358e4205cfe7258e4205cfc7258e4215ebf4258e4205ede3258e4205edc3258e42004ff7158e42014fe7158e42014fc7158e421a6df3158e42004ff7058e4200cfe7058e4200cfc7058e421a6df3058e4203cff76d4e4205cfe76d4e42004fd76d4e4203e7e65d4e420067d65d4e42004ff7654e42004fd7654e4205cfc7654e4203e7e6554e420067d6554e42005ef7254e4205dec7254e421e4fd76d4a4203e7e65d4a420067d65d4a4205f6e52d4a42224ff7654a4203e7e6554a421e67d6554a421e7af4254a42014ff76586420067e65586420067d655864205ef46158642004ff755864203cfc7558642004ff735864201cfe735864201cfc735864205cfc72586420debf425864219ef6415864219ef6315864205ef7215864205ef42158642004ff705864200cfe705864200cfc705864219ef7105864200cff76582420067e65582420067d655824205ef86058242004ff755824203cfc7558242004ff735824201cfe735824201cfc735824205cfc7258242056bf4258242004ff7158242014fe7158242014fc7158242196fa4058242196fa305824205efb205824205ef82058242196fa105824203cfe76d954205cff74d9542204fd74d9542006bd74d95422067f54d95422067d54d9542206bc54d954201cfe73d9542004fd73d954201cfc73d9542206bf43d9542014fe71d9542004fd71d9542014fc71d954200cfe70d9542004fd70d954200cfc70d95420067e50d95420067c50d9542206bf40d95420067f65995422273c54995421e5ed72995421e73c5459542225ef7259542005fb705954217df870595420067f75595421e4ff7459542006bf74595421e67e54595421e67c54595421e6bc5459542004ff735954201cfe735954201cfc73595421e6bf4359542224ff7259542006ef7259542004ff7159542014fe7159542014fc7159542004ff7059542006fb705
  | 30 => 0xf7458452024fe7458452024fc745845203e7f54584520067d5458452004ff735845201cfe735845201cfc735845203e7f52584520067d525845205ef7715845203ef7515845203ef451584521b6f641584521b6f6315845205ef7215845205ef42158452004ff705845200cfe705845200cfc70584520067e505845203e7c50584521b6f71058452004ff7458052024fe7458052024fc745805203e7f54580520067d5458052004ff735805201cfe735805201cfc735805203e7f525805203eee52580520067d525805203eed5258052004ff7158052014fe7158052014fc715805205efb705805203efb50580521ae7e505805203e7c505805203ef850580521aefa40580521aefa305805205efb205805205ef820580521aefa105805205ebd74d964201cfe73d9642004fd73d964205cfc73d964205cfe72d964205eee72d9642014fe71d9642004fd71d9642014fc71d964200cfe70d9642004fd70d964200cfc70d96421e4fd769964205e7f659964205e7c65996421e47d769964205e7f63996420067e639964205e7c639964205f3f42996422276f429964205f6c429964205e7f61996420067e619964205e7c619964205e7f60996420067e609964205e7c609964203e7f749964203e7e749964203e7d749964203e7c749964203e7f739964203e7e739964203e7d739964203e7c73996422267f43996422267e43996422267d43996422267c439964205e7e729964205e7c72996422267f42996422263f42996422267d429964205e7c42996420067f329964205e7e329964205e7c329964203e7f719964203e7e719964203e7d719964203e7c71996422267f41996422267e41996422267d41996422267c41996420067f31996420067e31996420067c319964205e7f21996420067e219964205e7c219964203e7f709964203e7e709964203e7d709964203e7c70996422267f40996422267e40996422267d40996422267c40996420067f30996420067e30996420067c309964205e7f20996420067e209964205e7c20996420067f10996420067e10996420067c109964203cff765964205e7c655964205e7f75596421e67f54596421e67d5459642004ff735964201cfe735964201cfc73596420067e53596420067c535964205cfe725964205cfc725964205e7e525964205e7c5259642004ff7159642014fe7159642014fc71596420067e51596420067c5159642004ff705964200cfe705964200cfc70596420067e50596420067c505964205d7f76596420067f765964203c7f765964205e7f63596420067e635964205e7c635964205f3f42596421e76f425964205f6c425964205e7f61596420067e615964205e7c615964205e7f60596420067e605964205e7c60596421e67f74596421e67e74596421e67d74596421e67c7459642
  | 31 => 0x4d521e57c7454d520067f6454d5203d7f7354d5203f5f7354d520075f6354d5201e7e6354d5201e7c6354d521df5c6354d521df5e4354d520076f7254d5205d7c7254d520076c7254d5203e7f6254d5203f6f6254d520057f7154d520057f7054d5223e7e6054d5223e7c6054d521df5f3054d52004ff7650d52004fe7650d52004fc7650d520057f7550d5203d7c7550d52026be6450d521e73e5450d52006df6350d5201edc6350d520075d5350d521e5be7494952005bd749495203dee72949521e57e749495205f3e74949521e53e749495205f3d749495205d7c74949520067f64949520057d739495205d7e729495203f6f62949520057d71949520057d70949521ee7e60949521ee7c6094952014fe76d85521d6f661d8552024fe74d8552004fd74d8552024fc74d855201cfe73d8552004fd73d855201cfc73d85520067f53d85520067d53d855203cfd72d85521d6f651d85521d6f621d855200cfe70d8552004fd70d855200cfc70d8552005df73585521dddc73585521d6f4615855200cfe76d81521cefa60d8152024fe74d8152004fd74d8152024fc74d815201cfe73d8152004fd73d815201cfc73d815203cfd72d8152014fe71d8152004fd71d8152014fc71d81521cefa50d8152006fb40d81521cef840d81521cefa20d81521cefa10d81521cef8605815205cff745905205ebf745905203ebf545905203ebc5459052004ff735905201cfe735905201cfc73590521c6bf435905205ebe425905205ebc4259052004ff7159052014fe7159052014fc71590521c6bf4159052004ff705905200cfe705905200cfc70590521c6bf405905203d7f76550522267f76550522247f765505203d7f745505203f3f74550520267e64550520267c64550521c73f43550520057f725505203f6e62550521ad7e70550521ad7c70550521c73f4055052004ff7458c52024fe7458c52024fc7458c5203e7f5458c520067d5458c5205cff7358c5205edf7358c5203edf5358c5203edc5358c521bede4358c5203e7f5258c5205ede3258c5205edc3258c52004ff7158c52014fe7158c52014fc7158c521bedf3158c52004ff7058c5200cfe7058c5200cfc7058c520067e5058c5203e7c5058c521bedf3058c52004ff7650c52004fd7650c5205cfc7650c52026be6450c52006bd6450c520073d5450c5201ede6350c52006dd6350c52024fe749885205ebe7498852024be749885205ebd749885203e7f54988522067d549885201cfe739885205e7f529885203eef529885205eec5298852014fe719885200cfe709885203e7c509885205d7f76548520067f76548520047f76548520057f74548521e67e645485205e7c64548520067d635485205d7f725485203f6f725485205e7e625485205f6e62548521ad7e70548521ad7c7054852004f
  | 32 => 0x1ed7e70552521ed7c70552522073f4055252006be6458e52006bd6458e5205edc6358e52004ff7458e52024fe7458e52024fc7458e520067f5458e520067d5458e521fede5358e5205cfc7258e5205ede3258e5205edc3258e52004ff7158e52014fe7158e52014fc7158e521fedf3158e52004ff7058e5200cfe7058e5200cfc7058e520067e5058e520067c5058e521fedf3058e5201cff7654e5224ebe6454e52006bd6454e5201ede6354e52006dd6354e52005ef7254e5205dec7254e5203f6f5254e52004ff7650e52004fd7650e5205cfc7650e52026be6450e52006bd6450e520073d5450e5201edc6350e5205d7d76d4a5203e7d76d4a520057d74d4a522267e64d4a5205f3e64d4a522263e64d4a5205f3d64d4a5205e7c64d4a520067d63d4a5205f6e62d4a521ed7e70d4a5203d7c70d4a52006be6458652006bd645865205ef46158652004ff7458652024fe7458652024fc74586520067f54586520067d5458652004ff735865201cfe735865201cfc735865205cfc72586520067f52586521f6f651586521f6f6315865205ef7215865205ef42158652004ff705865200cfe705865200cfc70586520067e50586520067c50586521f6f71058652006be6458252006bd645825205ef860582521ef7a5058252004ff7458252024fe7458252024fc74582520067f54582520067d5458252004ff735825201cfe735825201cfc735825205cfc72582520067f5258252004ff7158252014fe7158252014fc71582521ee7e50582521eefa50582521ee7c50582521eefa305825205efb205825205ef820582521eefa1058252024fe76d915203d7e75d91521e6be64d91521e73e54d91521e67e54d91521e6be54d91521e63e54d91521e67c54d915201cfe73d9152004fd73d915201cfc73d915203cfd72d91521e6bf42d9152014fe71d9152004fd71d9152014fc71d915200cfe70d9152004fd70d915200cfc70d91521e6bc64591521e73c5459152005fb70591521cdf87059152024fc76551521e57f7555152006bf6455152026bc645515203f3c5455152005ef7255152005ec725515201cfe76d8d521dede63d8d52024fe74d8d52004fd74d8d52024fc74d8d521dede53d8d521dede43d8d5203cfd72d8d521dedf32d8d52014fe71d8d52004fd71d8d52014fc71d8d52006de31d8d521dedc31d8d5200cfe70d8d52004fd70d8d5200cfc70d8d521dedc6358d520057e76d4d5203e7e76d4d521e57e74d4d5203d7c74d4d520067f64d4d521dd7d73d4d5201e7e63d4d5201e7c63d4d5205d7e72d4d5203e7f62d4d5203f6f62d4d520057d71d4d520057d70d4d522567e60d4d522567c60d4d5201cfc7654d52006df6354d5201edc6354d52005ef7254d52005ec7254d521dd7c7654d5201e7c7654d5201c7c7654d521e57e745
  | 33 => 0xd6450f522273e5450f5201ede6350f52006dd6350f520075d5350f52004ff7458752024fe7458752024fc7458752004ff735875201cfe735875201cfc735875203e7f53587520067d535875203ef7715875203ef7515875203ef45158752216f62158752004ff705875200cfe705875200cfc7058752216f71058752004ff7458352024fe7458352024fc7458352004ff735835201cfe735835201cfc735835203eee525835203eed5258352004ff7158352014fe7158352014fc715835203efb705835203efb505835203ef8505835220efa205835203eef52596522073d75992522079e73992522079d739925205ebf6399252006be639925205ebc639925205ebe62992524efaf529925205fac529925205ebf6199252006be619925205ebc619925205ebf6099252006be609925205ebc60992520073e50992520073c509925205ebc6459252206be5459252004ff735925201cfe735925201cfc7359252206bf4359252006be4359252206bc435925205cfc725925205ebe425925205ebc4259252004ff7159252014fe7159252014fc7159252206bf4159252006be4159252206bc4159252004ff705925200cfe705925200cfc7059252206bf4059252006be4059252206bc4059252206bf76592520073d755925205ebf6359252006be635925205ebc63592523d7af525925205fac525925205ebf6159252006be615925205ebc615925205ebf6059252006be605925205ebc60592520073e50592520073c5059252006bd7559252206bc7559252006bf7359252006be7359252006bd7359252006bc73592523d6bf5359252006be53592523d6bc5359252206bf725925205ebe725925205ebc72592523d6bf525925205ebc5259252006bf325925205ebe325925205ebc3259252006bf7159252006be7159252006bd7159252006bc71592523d6bf5159252006be51592523d6bc5159252006bf3159252006be3159252006bc315925205ebf2159252006be215925205ebc2159252006bf7059252006be7059252006bd7059252006bc70592523d6bf5059252006be50592523d6bc5059252006bf3059252006be3059252006bc305925205ebf2059252006be205925205ebc2059252006bf1059252006be1059252006bc10592520057d76d525203e7d76d52521e47d76d52520267e64d52522073e64d52520263e64d52520073d64d52520267c64d52520057d72d525203f6e62d52522073f42d52521ed7e70d525203d7c70d5252024ff7655252026be6455252006bd6455252005ef725525205dec725525203f6f52552522057f76552520267f76552520247f765525203f3f74552520267e64552522073e64552520263e64552520073d64552520267c64552522073f43552520057f72552520076f72552520076c725525203e7e6255252
  | 34 => 0x4d430075f6554d4303ede6554d4303edc6554d430075c6554d430079f7454d43025de7454d43025dc7454d4324f9c7454d4301edf6454d4301f9f6454d4324f5f5454d4324f9e5454d4324f5d5454d430079d5454d430071d5454d43005dc7254d4324f9f4254d43005df7154d4324f9f4154d43005df7054d434ff5e5054d434ff5c5054d434ff9e4054d4324f9c4054d4303cfe75d8943004fd75d894301cfd74d8943024fd73d89434e6dd73d89434e6ee42d89434d6ee32d89434d6dc32d8943014fe71d8943004fd71d8943014fc71d89434e6bf41d89434d6df31d894300cfe70d8943004fd70d894300cfc70d89434d6df30d89430057e75989430057d7598943006ef6298943005f77158943235f47158943006ed621894303cfe7518943004fd751894301cfd741894305ebd7418943024fd731894305ebf421894305eee42189434f6ed421894305eee32189434ceed3218943014fe7118943004fd7118943014fc711894300cfe7018943004fd701894300cfc7018943014fe76d8543236f661d854303cfe75d8543004fd75d854301cfd74d8543024fd73d854305cfe72d8543004fd72d854348ebf42d8543236f641d8543236f631d8543236f421d854300cfe70d8543004fd70d854300cfc70d8543236f710d8543236f4615854300cfe76d8143025be74d814301dbd74d814322efa60d814322fba40d814303cfe75d8143004fd75d814301cfd74d814322ebd74d814301cbd74d81433debe54d8143006bd54d8143024fd73d81433a6de53d8143006dd53d814305cfe72d8143004fd72d81433debf42d8143014fe71d8143004fd71d8143014fc71d814322ebe40d814322efa40d814322ebc40d814322efa30d81430057f75581430057c755814322ef8605814303ebf745935203ebf54593522267e545935203e7c545935203ebc5459352004ff735935201cfe735935201cfc735935203e7f5359352226bf435935203e7c5259352226bf4259352004ff7159352014fe7159352014fc715935203e7f5159352006be4159352226bc4159352004ff705935200cfe705935200cfc705935203e7f5059352226bf4059352004ff7458f52024fe7458f52024fc7458f5203edf7358f5203edf5358f5203edc5358f5221ede4358f5221edf3258f52004ff7158f52014fe7158f52014fc7158f5203e7f5158f52006de3158f5221edc3158f52004ff7058f5200cfe7058f5200cfc7058f5221edf3058f5203d7f7654f521be7f7654f522257e7454f522257c7454f520067d6454f5203f5f7354f5201e7e6354f5201e7c6354f5221f5e4354f5205d7c7254f520057f7154f520057f7054f5223e7e6054f5203e7c6054f5221f5f3054f52004ff7650f52004fd7650f5203cfc7650f520057f7550f5203d7c7550f52026be6450f52006b
  | 35 => 0x267c645515324f3c64551530075f735515301d7e735515301d7c735515327f5c735515303e7f635515303f5f635515327f3f435515327f5e43551530057f72551530057f715515323d7e705515323d7c705515324f3f405515327f5f3055153024fe74d8953004fd74d8953024fc74d895303cfd73d895321eee32d8953014fe71d8953004fd71d8953014fc71d895300cfe70d8953004fd70d895300cfc70d895321edf30d895324dbe7498953005bd7498953006ef6298953006ed621895305e7d7518953024fe7418953004fd741895305cfc74189530067f54189530067d541895303cfd73189531bede431895305eee32189531beed3218953014fe7118953004fd7118953014fc711895300cfe7018953004fd701895300cfc70189530067e50189530067c5018953014fe76d8553246f661d855301cfd75d8553024fe74d8553004fd74d8553024fc74d85530067f54d85530067d54d855303cfd73d855313ede43d855305cfe72d8553004fd72d8553246f651d8553246f631d855300cfe70d8553004fd70d855300cfc70d85530067e50d85530067c50d8553246f710d8553246f4615855300cfe76d815303d7e75d815301d7d75d815323efa60d815323f7a50d815301cfd75d815323e7d75d815301c7d75d8153024fe74d8153004fd74d8153024fc74d81530067f54d81530067d54d815303cfd73d81530bede43d815305cfe72d8153004fd72d8153014fe71d8153004fd71d8153014fc71d815323e7e50d815323efa50d815323e7c50d815323efa30d815323efa10d815323ef8605815303cfe76d954301cff74d954301cfd74d954350e7f54d954350e7d54d9543024ff73d9543024fd73d95435067f53d95435067d53d954305cfe72d9543004fd72d9543014fe71d9543004fd71d9543014fc71d954300cfe70d9543004fd70d954300cfc70d95430067e50d95430067c50d9543506df30d954327cfd76995430067f659954327dbd749954324ddd739954303cff7659543295bf7459543265df73595430067f7559543294ff7459543006bf745954327cff7359543006df7359543004ff725954305cfc7259543004ff7159543014fe7159543014fc7159543004ff705954300cfe705954300cfc705954327edf3059543504fe761954303e7e65195430067d651954301dbc765514303ebc765514301cbc7655143025bf75551430273f75551430073f655514303ebe655514303ebc65551430073c65551430079f735514301dbe735514301dbc735514327f9c7355143026bf63551430279f635514327f3f535514327f9e535514327f3d5355143005bf725514327f9c3255143005bf715514327f9f315514322dbe705514322dbc705514327f9f3055143025dc7654d4303edc7654d43024dc7654d4301ddf7554d4301f5f755
  | 36 => 0xa30d815426ef820d815426efa10d815426ef8605815401cfe755935301cfc755935303ebf745935303ebf545935303ebc545935303ede535935303edd535935327ebf4359353004ff725935305cfc7259353004ff7159353014fe7159353014fc715935303e7f5159353004ff705935300cfe705935300cfc7059353266bf405935303d7f765535351e7f765535303f3f745535303f3f64553530267e64553530267c645535303f3c645535301d7e735535301d7c735535327f3f43553530057f72553530057f71553532557e70553532557c70553532673f405535301cfe7598b5305e7e7598b5301c7e7598b5305cfc7598b53024fe7498b5305ebe7498b53024be7498b53004fd7498b5305ebd7498b53004bd7498b5305cfc7498b5303e7f5498b530067d5498b5305eee7298b5305e7f5298b5303eef5298b5305eec5298b5305eee3298b531feed3298b53014fe7198b53004fd7198b53014fc7198b5300cfe7098b53004fd7098b5300cfc7098b530067e5098b5303e7c5098b5301cfc7558b53004ff7458b53024fe7458b53024fc7458b5303eef7258b5303eef5258b5303eec5258b531deee3258b53004ff7158b53014fe7158b53014fc7158b5303e7f5158b53004ff7058b5300cfe7058b5300cfc7058b5301cfe755875301cfc7558753004ff7458753024fe7458753024fc745875303e7f54587530067d5458753004ff725875305cfc725875303e7f525875303ef7715875303ef7515875303ef4515875325ef63158753004ff705875300cfe705875300cfc70587530067e505875303e7c505875325ef7105875301cfe755835301cfc755835303e7c755835301c7c7558353004ff7458353024fe7458353024fc745835303e7f54583530067d545835303ede535835303edd5358353004ff725835305cfc725835303e7f5258353004ff7158353014fe7158353014fc715835303efb705835303efb50583532567e505835303e7c505835303ef85058353256fa3058353024fe76d915324ebe64d915301cfd75d915324ebe54d915303cfd73d9153296bf43d915305cfe72d9153004fd72d915324ebf42d9153014fe71d9153004fd71d9153014fc71d915300cfe70d9153004fd70d915300cfc70d9153296df30d915324ebc64591535157e76d515303e7e76d515327d7d74d51530267e64d51530267c64d515303f5f73d515301d7e73d515301d7c73d515303f5c73d515303e7f63d515303f5f63d51532975e43d51530057d72d515324f3f42d51530057d71d515323d7e70d515303d7c70d51532975f30d515301cfc7655153006bf6455153026bc645515303f3c5455153005df735515301ddc735515303f5c535515301d7c76551530267c765515301c7c765515303d7f745515303f3f74551530073f64551530267e6455153
  | 37 => 0x8f54024fc7558f5403ebe5458f5403ebd5458f5403edf7358f5403edf5358f5403edc5358f54296de4358f54004ff7258f5405cfc7258f5424ebf4258f54004ff7158f54014fe7158f54014fc7158f5403e7f5158f54004ff7058f5400cfe7058f5400cfc7058f54296df3058f54024fe7598b5405cfc7598b5401cfe7398b54004fd7398b5405cfc7398b5405eee7298b5403eef5298b5405eec5298b5405ebf4298b5405eee4298b54206ed4298b54014fe7198b54004fd7198b54014fc7198b5400cfe7098b54004fd7098b5400cfc7098b54024fc7558b5403e7c7558b540247c7558b541e67e5458b5403e7c5458b54004ff7358b5401cfe7358b5401cfc7358b5403e7f5358b5403eef7258b5403eef5258b5403e7c5258b5403eec5258b541e6ee4258b54004ff7158b54014fe7158b54014fc7158b5403e7f5158b54004ff7058b5400cfe7058b5400cfc7058b5403e7f5058b54024fe7558754024fc7558754004ff735875401cfe735875401cfc735875403e7f5358754004ff725875405cfc725875412ebf425875403ef7715875403ef7515875403ef4515875428ef64158754004ff705875400cfe705875400cfc705875428ef71058754024fe7558354024fc755835403ebe545835403ebd5458354004ff735835401cfe735835401cfc7358354004ff725835405cfc72583540aebf4258354004ff7158354014fe7158354014fc715835403efb705835403efb505835403ef85058354286fa405835401cfe76d8d5427ede63d8d54024fd75d8d5403cfd74d8d5427ede53d8d5427ede43d8d5405cfe72d8d54004fd72d8d54014fe71d8d54004fd71d8d54014fc71d8d5400cfe70d8d54004fd70d8d5400cfc70d8d5427edc6358d542267d75d895403cfd74d89544eebf54d89542267e54d89542267c54d8954226bc54d895401cfe73d8954004fd73d895401cfc73d8954226bf43d8954226ee42d8954014fe71d8954004fd71d8954014fc71d895400cfe70d8954004fd70d895400cfc70d8954226bf40d8954006ef6298954005fb705895426df87058954006ed621895403cfd741895401cfe7318954004fd731895405cfc731895405eee42189541c6ed4218954014fe7118954004fd7118954014fc711895400cfe7018954004fd701895400cfc7018954014fe76d8554276f661d8554024fd75d855403cfd74d855401cfe73d8554004fd73d855401cfc73d8554146bf43d855405cfe72d8554004fd72d8554276f651d8554276f641d855400cfe70d8554004fd70d855400cfc70d8554276f4615855400cfe76d815426efa60d8154024fd75d815403cfd74d815401cfe73d8154004fd73d815401cfc73d815405cfe72d8154004fd72d8154014fe71d8154004fd71d8154014fc71d815426efa50d815426efa40d815426ef
  | 38 => 0x200000000004001000000200000060000019000000700000010000000000c00a00100000000001000c00000000000000004000c009000000000000000004000000800000040020000000000c0000004000000000200000060004000000400000080000000003000000300040000000002000800000000000000002000000000100050000000002800c00000000000002000c0050000003000400000040010004008002c00100040000000001000c00000080040014000000800400040000000000002c00000100000000004000800100000000000000000800300000010000000002c000000400e00080000014002000000000040000000000000c00b000400200000000000001000400e000400500040020018000000000200000030004000000800000000080014002000000100000000000001001400100000000014002000c00600180000000001002800200040010000007000000000000020004005000400100040010008001000c000001c0040000000000000100140000000002000c000000400100140000028000000800300000030008002000000200000010000000001c0040000000000000100040000010000000000000000000004000000000000080060000002000c0000008000001801100200000004000000c00000040020000000000800200200000000000000000700100110008001000000000000060000010000800100000000000000004800400000000010007000800100040010000001000000500000000004000000000000040010000000000c0060018000000000100000000018002001400000000000008002001400100080050004007000400100040010000000002000300000010000000000000200000000004000001c00000500020014006000c00800000000018008000c000000000100100010000001000000200080050020002001000e0004004000400000000070024005000000500140000008001000400200000000004004000000b001c0000000003000800000240020008004001c00100000000000002000c00b000c0000004003000400c00040010020000000000000140020000000000000300000010000000000400100000020000000000c000001c0000000001000000500000000000001000400000000000000000002c0050000002000400000040020008004000000300040000000000000c00100000040014004000000000180010010003000c0070008001000400100000050000000000000000000040010005001c0000014000001000900080020008009000000200180010010000000400400000010020007000400d001400300080040000007000800f0000002000000000040000000000000400000000000000003002c000000400000040000008000000000200000010010001024fe755
  | 39 => 0x6001401400000020000000002c00100040010000000002000500200010004001004c0070004001000c000000000c0004000000800000100010020000002c0010018002000000d000800000040030000000000000000140010018000000000200080020000002001400c00000010000000000000c003800d00000060040000001c00200180000008000000800000000000008000002000300140100000001000c007000c0010000000002400000040010000007000400000000050004000000400000040000000000000400700000000008002000000000040020008000000c00100000000000001000400000000000008005000c00000080020000001000400500000010034004000000400100070000000002800000000030004000000000000040040008001000000e0008000003400200000040004003000000000000000040001000000000000000000000000000400000000004002001000000040030004002000c0040000000000800300000030000000000400000080010000000000000300000000010000000c008000400000040000000000001000000040010010001000000200080060004000000c000000000400000000018000000c0020010006000000300180000000000000000000040000004001000000000000000008000000800100040040000000000c00100040020010000000c003000400c0000000000400000040030014001000400d00000080000001000000000000050004002000400100100000004001000000400200030004002000000000000000004005000000100000010030000001c001000000100080020000003000000000200010000001000801200080000008003000400a000400000040050000000000400000100020000000001000a000000200040000000003000c001000000600080030004005000000000040000040000000000200040040010000000000100280010008003000c007000000e000c000000800f0000002000000000000010000002001c0010018002000000000040020000000000800200140010000001004800100040000030004000c00c000400100000000000003001c00000200000010004000c00000240000000000000c00100000000004000000000000180000000000001000000000060000001000400000040010000001000000000000050008000000000200000020000000000800800040010000003002800100000000004003000000a0008002000800000000040020004000800000000030018001000c00000100010004000001000100000010000001000400000080020000001001c0030018002000000600000030000004003c0040004002001000200000040008009003c0000000002000c00400080020008000002800000000020004001002c00300080000004
  | 40 => 0x40010048004000000d00000000000000000c000000c001000c001002c0000008001000c00100700000000003000400100140030010000000400100040010008000000c0000004004000800000180010010001000800300000000004004000400100080000008000000800d0008002000000100040020020000000000100040000018000000000000000010000001000400800140030000002001400000040090010003000800300000000004001001000000000010000000000000200080040000000000c0040000000000000a000400000000000000001000000500000070004001000000c00040030000008001800100080010000001000000300000010004000000000200040000004003000400100080030000000000000300000020008003002400000040010010006000c0000000001001400200000020004001000000000080030004000001800000000000008000000000200040000000001001c002000000000000000000000000c00c0008000001000100000000000003002800200000020014002001400100080000000000000c0050000006001c01300080020004000000400000000000008002000c000000800f0004009001800300000040004000000c000000000000000000000002000000000000040004003001400100000070004000000c0030008000000800100080000010005000801800000020000001001800300000010018000001c00100040000000000000000200040020000007000000000000000000000000000100100000000000000000100000000008000000000b001400000000020004001000400000000020020000000400100100030000000000000000040000000001000800000000060014000000000200100030008006000c00000180120000000000000000040000014001000400200140010014002002400300080010008000001400100000020040002001800300040020004002000000400080040010003000c002000400500040020000001000400000040010000011000000300140000000000004c00400080000018003000000500040050000000000c0000000001000c0000004000000000100180020000000002000300100000008005000000000200000018000000800b00180000080004001800000000020004005000c00000080010000000002000000100000000000000400000000000018000000000100000000000000001c0010000002000c002000400000080030000000000c0040000004000400200000010000004000000400000000004000001800200180000004003002c00100000030004003000000200000020008006000800000100000000001001c0000024000000800200040000008000000c000001000100000000004000000000a00040020004000000800100040060028010
  | 41 => 0x4000164c7ad00000000000000000000016225f715da347a4e200000000000000000000000000005aa003e0000000000000078d8e120000000000000000000000000000000001a45e08cc000000028c24a20d8800099b80000000000000000000000005182b5a00000008eb9d3e0000000000308600000001af18568530c3eca3043c7a100007321356a0c903a0df000073020d43d1800000021100002dd4000000000000007fd00000001fae00000004a382a069ab0ec0000000000320400000008a6000078c2d742d302b400008e6c258a7e3aa8000000000000020365e69776000100a0000f6e72e30bab8100008d320060002d42000000000031080001bc01fc80007d7310a0000000000139e00003a46f9800013faa04000000021804a600000000c980004429c98a531104515962ac051e7200080000000009001000000080010008002000c0000004000000c00000000010000000000400000000040000002000400000040060018000000c000003000600180000018000001c00700100090004002000800100000010000000000000200000000004000001400000000050000002000000100000000000000000c003001800000000000000000000c00300180010000000003800000000000004001000000000100000004000000c00100040000000000000c001006000000000010004002000c0000004002000000000000010000000000000400080000004004000400100000000000000000000100000010000001000000300000040020000000c003000800100040000000000000000200000000004003000000600080000000001000800100000000004004001c0090008001000400600000000000000000000200080000000002001800000000000000001000c003000800100040030000002000000700000000000008002800000280010004000000400000000010008000004800a0000000002c00200000010000001002000000140020004005001000500100000004004000c001000000000000060004002000000a0018002000c003000000000000000010000001c006000000000080010010003002c00200080000008000000c00000000000000000000800100000000008000001000000000100004001000000700000000010002001c00a0018000000000c000000200000010000000000000000000000000001000000300000020000002000400100080000014001001c00000040020010005000400200000030000000000c00900000000034004001000200080000000000000000000000030000003000c0110008001000000000000010000000000400000000000000004000000000300000004000001000a0000010000400200000020010000000000200000030014000000800100040030000010000000400100000008002000
  | 42 => 0x2dba30e00021660000000756a70a0000000000182a00005500002f7a60687127b98000000316c00016f200007a200000000001b401ea800000000000c406fa105aaea433800000000004bb0000000000000024da658aa96000000058c02f40000b32b8fb1f8ab20000000000042180002e700000003088000000000007bc00003ae000000000000000001c32000221a0000000157800080a123ca948000000000094b21f4aeb8000000000000000000000fe29a99ba694213d40000000000133e0000000000127a44902bc6a19264401806c00006309dc0000000069a000025c000000000000000000000afd0000000150824b0000000212000019c200012ba000000000000000000000000303628f9d50722a0ae0d2a81402602423db000000000000002e3a5512f940000000000000088b2edcab78000000000000012341a700000000000000000000001a881c8000000000000000003982feec82ab28bb205a00000792691000095a80000000c8600021ca000000029080008ad0000bab28ca00000001c90000094032c54628e000027260000000000131a0002418957a846000083ac378000ae8aeb862b00000000000252002000003160000000c778000af2800000022c8000325c45331d40000000acc0000677000082600000000000ca90000729800000000000000000000000000000003c99b30109800094e0000000000030d000031729ac9409f02c1700000000000000000022d800020c000000000000001be40000000ae0800074d85fc8e4000000023462148000000000000000000000000572194415980000000000000132c9d193b87c88f30366800000005ce0000f8c000000021b89e20771416c9f040205880000000000000059200027620000000000000000000009e780000002da8657800000000000d4a6000000000000000000000000000a6000029700000000000000058c875400027ba00000000001f960280dd8000258a0000000a00800021e8d964bf08503f5a112884000008f95a846d80009d90000a23182000000000d71b9e7a7957c63f22362ec08e2271b02c000026047e21540000312241831a00000001b6800057b80000001a84b20a6600001c444003060000000000000000000000a3a96f43ae8000351190c8fe8a0248aa65684f062c56618c400000000001472000225a000000014a000000000004e70128be3000058b154a0002da6067240e14690820000000a4c000000000000002652974b0c41179edc00000000000000c8a00000000000893000000026ec50d15165cd0000c508000bfd00000000a4000000000001d56c8eae6400028f240a800000024c4b94205c00022ce066800000000000000000c9a000091600002cd8000c8c13e80002b38ba50000bd7800036c971c1de8000377000000014d
  | 43 => 0x311a98829de00021944782332ae11a5400000000001e7a871a7ea852a75c13900000002accbba84e036b0ea05619990661a7e6aecac84b1b167e00018c20001cc4150175cc7f80000001c680dc2c600000000000000000006a4a5893500001566bc6894e0001948a0b80000000000000000000028a0000231a23100000000d2651290749d08024b4715ce3d81e203dd1a8e93f2528c15a89c2859dc600000001c2000000000000000000000000000000005cd9ada00001564269cb05ae8000000000000000000001bee00000000002c30a978000000000000011126210cfc74e068831900000000000a7bb07606e800047f0000000323c00000000000d500000ae6b0810700000000535a188be9142435380ca723000000000000000000565800000006e40000000c358000a3b800017d1a6e00022328be9a361400e7ec0d0a141590000000000002ca7a00000baa0000000000000000000001b28000000000000000004daaa5c00000000000eb88258000a869f58000000000024ac0000ef60000000ae90eb6000163e2cfa2cc32280006cf80005f606fc000000000022fc00001f0000000000000000000000b700000a158e162d680008570000000000000000000000000009800012d87780001b06000000000000000001c829739e620000000217000076d1180000000000029900000000a1100000001e06000000000014124fd0000c238000000000093d80000000000810933a7552f9a621800000000000000fd0000000078f0000a920fb04bf800016788d4623b22c0000000c791a5abd415387a48000b9b867ec9b0000abd85d800000000000000915b27e000000002500006b0a654443000000000000002d0aa918516000000000000002288e964a68f827b500004478000000000000000000000000c859026274afe604900000000000000213a00000000000000000000000000000000bfa00000000001ee270b800075200003dd800000000000000000000000069cb018bec00005121f14000071a6dc80d0796000025721a44718000765a44c26823926919c2800006d81a0152686c257a53819404c41dd655bae68061142eacb9f5ac4a2ad64752062b9b0bec9118000c978134000182c74480001ae856e0000000000216e4fe22d2c5f28b2a56800000009903afa1aab7c9b2600022ea0000000486a492ba99ce8336800000000000000000c6d00000000b7c586a6fab3c2822000000087798f244d9f041a98000000063a00000000001f1e0002db412180000001bba81d00000001e385861b5e0000000893b1c60002376493151c3e80da6000027c6902182000228479d9fb022f9dacb86a1d41239952a10800092a885a95816427642d623311f0a00025fa73a800000000000002b883b80130b9500000002e8c00
  | 44 => 0x2d020000a2e5ba8000000000000000000000000000000000000000001d10a8b8000000000008e1f46000000000000007498000000297a0001f7c000210c5f980000eb3188c75800000000002f68000000049e2e60000000000081212a00000000c572c96a96000000026da0000000000000000000000000000450882800000000000000a4f203800000000001b3c244800000007203e28d040000000b6505fa466099e00000008dcb2140002b0c000000000000000000000525225472025de4a122d6229171092e80002fc178c61b00000000000000000071480000002498bcc800000000000000c040000000000000000000006a50000334b28842501c448a32921cd87504b28f24000213e32482d82ae2a8600000007b1a0080000bc293029202c92524000299c000000009280000001f48abc000000008a867e800000011f40688000aa631305c3800000018f478e872c00000000000e62000026a000152435a00006a282febd8800000024321c09eb00000c2000000001339fe40000da869d80000001938000000000021a0000000000013e2c14823a839851c000197e2e1836aaff31aa000320c8df0972000098eca9845200000000000b425f917da34f17ecad919607de15bcbb3978a96c9c5aba28d364728000c020000000075ea9aae46c73155400021ba204889aaa49b1a000000000000000002b3e00000005b900008c980001668000501a2e81280e40bcd8382000000049c00000002f46000000000030feb772ac04ef00006ce0000afc1c2aa1dabd066700086fb0ecc00013720000a507b5b26000000000000d220000000b4c077e0001a382a0000000000003e580000002ad800a00000000caa5268c020000000000000000000000000000000000000000000000000c510000047800000030240000802b499cba0000cfa00000002fa0694785044673b0000814a62c5d6a66200031ba878ade46c48372c27ac0a432801000011020000000000176e1e32126c152d960000000c9580000000000611800000018ec44a117e00000000000000000283800008d8000246e00000000000e7a76c80000000de00000e3e0000000000244a8580000000136000025881b8abd800000000002ea24a50000077932a7aaa90cb5a29b8267012a0cc1492000000055da80e1c6000000000007fe8000000148a28680000001b3687da9920001f32a4125a48589662a4425da502af400002d842f22cac4c2000000300004de2d3c2ae8000000000082503145cb2ef600000000000000000000000000000000000000000050f09a60000000a3114140000000000000057500000a000003428000000000000023d600031da8008e2e00000000000000000000000000000000000000000028400001fe8000252b24000000
  | 45 => 0xbb000000018ea000000000000003852c3c0000aa600007d4000000002000005340a4600000007deae2e052800032e800000000000000000000000028008c6a9d2e9a4618000c5c00000002a700000000000000000003ce094813e0000000000000000000000000000a3d0000000000000000003cda0e86a9000000000001f9150e00000006de87c600000009a82f4c00000008941db08b98000000068600009ee00000008da800000000006258000782859c59702680000000000105800000001bd8892000000000006266e880000000000000019482129f819baa5468d0958c4d00007e6000083f8000000000000000000000000000000000000000000000000000000031c0b040000c250000000127e000000000000000000000131000000000000000dbc6bc9f6e000318c780209a735000000000000000c46000000000000006f422f626b80002c280000002e220001ca865680007db080e000000000000000002cdc0b000000000a54000000000000000000000000071eaba0000000086a000000000000000000000b529eca25680000000000000000003b000000000005328000a9ea6c20002e842c80dfa0002db00001f4200000007bd800000000000f6a698000000044a952c000295095728e4590000000000000000000000000011380007a0ad4e95d0000180143a00000007770cb660e00000000000449800000000002251496762183e0000000000269c000000000030ce00000000001f54000226000000000000c0a00000000002fe229e173a9b7a01c000000000000000002460c86204e000174606b800014e00006358000000309800023e6091800000009c40af9998a6ba99a73fa23c000000000000000002bc60001b1c00010aa00000000000ce4000000000000000000000000000000020a20000000634b28e0000000000060ac16800000000000128000393000000003183258000b5ca818ad225acc4fad508fd908aae530384518c526d9aff63ba9152000000000c80001a8800000000000002060bd3ac660000000000000000000000001e8aabb3066898939212b9548070042c8992be067486ec477a566628a4bca338000446adf42b10e2c27380000002526000000000031ca000000000000004c1800096c1f9032c2faa45816a4304000007980009e300000001510a0f8000000168a000169000021b8000000000000000000c4e7e88000ac8a7880002bce7782be215a00000000800000039a26f984c9b21c704f20d240000000000163800011ac00000008628cb2b2497829932ee0a7687747aeaa3c46e2aae8d9142800022188808000000034e0000000000000017b00004688000076800000000000000000c3900000002354660800000000000000000000292e0000000000216a0a98c08000232c000000000000000
  | 46 => 0xc8f80006d09abc5fa1870c8e141e45caea8a0680000000000c73859677d80005280000aa717a610a8d12c2b80b80002ed80000000b3c980e0000000a9c8000000106402d8ea62a889e80000000b2e00000000000a1303880000000b1e9bce000189caed0000379248494180000002b3c0c32f420000000a538a080000000a340000000000000000000000dd60000000890b1fa00014a63f39688c78800000000000001eec0168ba44bc2dacb9e80000000000c87afc22a40c9800000002d20a6e579a45e4dd324a73c800073786280000000b3ba8e600000000000000000000000018c00002db6000000057580007a380000002f7800014ba0001aec00012bc0002cc893a80000000000000235ac0400000002cbe00004dab9fb0c631810c444c1ec000030a000018882a1a68e452806243f13fe2c001d8410a00a00000003ec80001df20400000000000000000012b200000006240000000000000000005b7a1f20000748000254a00007721a10dccaaa146200014809821750a8e04ea7e80000ca100000002f000000000000000000000000880504b3a00000000000ad09f600000d8644c800000000000000000000000022c9de80002b9c82300000000000c5c80000001ba451a0ef09ea89300000000000000000027e400000000001274000000000028000000af09da00004b4191c81c0b100000000000143e000005e53eb15e0000000b138000000034c0002548000000051b00c8000100e10f8190c160000235800000004060001dc01538056a1800000001486000289a00000000000000000000000017fe0001b0000000000002dbca2d800000000000000c4c0002c1222d000000009f2000000017c8000737000000026502769e161429cd8000000000000000000000000308200000007f19aac000000000000006f20000000000030e800000000000000000000000000000000002bc200030ac0000b1400000007a58000a4b00009b030ee00030cc2e830443749bbc3141c9e62c2152c7d80000000db403380009bb856a7842cc6357828c0a90bbc0002d0c7839a7400005e40000000000000000004c80000b04c6780000000000b9e10141d000000001d2800000a89d11966000125aa7b1c760000000b2000007f51c4ac4831c20001218166000000017140001ec80001e4c000000091f8000000000098100000000000974000078ba4b81d3aaa4000292200000009049d601e20000c4b968200024446fc92581f7151e000003a0000000392008e9018b0637f0d724ea2220000145211d0000000000000000000000000000000000000000000000000036e2ad000000000000000b0c000303a6cc800064a14902b5aa80000050610ba0b60001b7e86110b60bf17ca00006c0000000005b800060780009be04a201183f00000
  | 47 => 0x147a6958e68b7180000002ed486d301e39981b80000000000000000002ce00019d0270984890a298c2b706026fc01380d80fc46058000969800038a00006751454000000000000006c7ae5a9a480008b080008aaab5c5d98000bf72bc000025be0000000c30134abd819803b100003c18c840002fce000087c59e000044200006980000000012c0000000000000000017d492fabd400014f4c1d0f880000000b1c00000000000c270000b0084600001fb6a86000048980000000000000000071024b607d90a8000229067c9f061cc0a3800000000000000000000000000000000000546953c683875600000003b021dc0000000000000000018b4000000000021fc00000000000000000000011300008b900000002462000000000000005430890000000090d881c12a80000000dec0002e100000000000030e00000008a8a5101999e34000000000031a62f380000000000000000000000000000000acc991a00000001f60d4069220b02450e1eb66028200018e6000000000000006eb800017c00006cd0d2823f80000000b1670800000000000000240aadb80000c2a46c6591956000136600015b4c139de435a80005a39a782ce15f40001256c4c800000000000000000000000000030e60000fd200000006d800000000a3c00000000000fde0001d3000100000000000000000000000000000000000000000000000001ed000000000000000000049600000006a416c29dd04a4aafa49c9fdb0201dd94b8951201469a21f81711254b38197c4f81d9a2fd80000d780000000000c808ca80e18000700b18226a206c00000004b9000099d0000000000000000008db325800019c00000000aae000023c821abf18000000000000015b0ae61dde000000000028ac70c000000008c8a8526aa0000a880002ede00012cc4890000602800051f800000000000d9088a00020f64e68000bd52f8e00020c60000000a3e8000000000000004a80000000a6c864e00000003d1000000000009468000000293eb459ede5951be0c012f6a7288f1000014bc0000000000000000000000000d666e127fe00000000002f049ae236200000003a6083684a8fc815680004e5000000000000002ce20001f345540dcec418000bcb80000003030000073e00000007380000000000091e800000004b46888b787b68000a93800019b03e25ac0534000000088000000000000af7000000000007610d9c00000005928e1c00015000000000000000000022b8000000005a800087311923092c2400030780002de20000924000165e00000000001baa000000000008040000000ac71ed800000005578182156067211c8000000000000000005601e4200000000000000ae780005fe800000000000000000c9c1a7c10e000066b032200000000000000000000000012a6
  | 48 => 0x29d98a482c97cc083ad9ea968c8cb560e58000000000000000000000000000000030a8a01000090d1ccc0ae2512c6cb090a1002b278685ca00000009e98000384248a0000000021000051610c034c2ca4000166e86d800083f0000000000000023a49ca8000000000084d8e4200000000002f1498600000001f9a08b1b140000c8000028a205c000000028ba0a6093400006329631aaa25000000000000be00a260fba85c00000000221ace0000000000000071e00006a30000000000000000000001798000000000026f20002e569c1829201300007bf800004e8ae872f80000000000966000056429244e800006d5800000000003ff8710c37223e00000005a729a600009680000f0ab4e81e4adc80001c8800000014361f88000000000000000000002306000000000002280000000c7b00000002cba0ac000005f800002b0fecacb2cf60002dd0000000010d800067d00000000000050000000000000000000751800000000000000ba200000007e0133c00000003e51cda0001d44958af4a54d8000b83942aa5b000027580007210c26a44ae8256103000001dda8f405305cf92dc0409dfa8ca072e0000a7c000000052da5407f6000079800006fd800000000000002da02e30000000000000014c6618aec64b680002b90000000208e00000000000000abc80000001f2640b000047c800008129e60001f3c000194e000324e00000004b81e547f78644000000000006c20002bdaa0300009ab00004ad80007e38c062aca1ce0000a9400000009a4225c913937c6000562717800000017d021b00006e0a68614bab18c94a81e739849c0ca3254000000000003c094f09e021580005820ce653e29385ea0d8e592194a0000000aad8000a9f0000ab428c25c2800000000000000000000228ac94000000000000000000af200000000fac70680000000000c55a39c9d80000137800000006340001e5aa3511d6000000080300000000000740800000009f0c59231e00000000000000000087800011d200013c40b597ae812ac9c000000063e11ce840955a04da6fe5071bb490c000069700006e425fc30525f0000268000022be95513ae00000007a41dc4b0616fe540800000000000000000000221e47eac0662300000000fe6536160cae38ce0000000000000002128000ae2800000000007219d9e6f587967e70f1a3002a22196103c2e0841e92399a04800cf8138a2f06bd96c85e3afbebf5a19c2b2206e4c300002d7000000010c800000003530bcc0000b8ead88000686b12a17403d400000000000000000000000005c2000149800000006070886b5b91da03c232000012f24ca2d063a38000000000000000000000c7a00024828160000000113e000a6c4000211e8ad800000002d4000000000000000001ffe46210da6fea83000000003d6
  | 49 => 0x25ae000144250880000000030c991c8e44180000001b6859c972e000000000000006ac0cfe5790000bdd0000000106872a80000681ca0682275eb2292c4b80800038f0000000314617000528ee8000976322a7af25c8c8d98b212c897447a0b720ff8000a7f00be13a000000000000002488062ac7828a045c000079c8cf000000000000000000bc5914e000000093980000000000000000000000000358000000000059a800000000000000000914000092300009cb000000000004e3800000000000000000000000033ca734000000000000000000000000000029600000000000000000000000002f980002fca1fe0000f640000000a438000be40edc1be00001f2000000016bc0001ab82fb840c0000000000000094728f8add2faea69126e31aab7a1b397560000000c8d00008c1112227f02e07c8000047d80000510000000175800000008f180000418000000000000000008c608ba0001dd08e88000000296a0002c420000f48620800035faf1c00013d2000000000000002ca8d8a0001ab20e013e400006cc00026448f3000072680008d980006e282960001fd0c2f8000000078e0000000000000000000000000a82ab1a2805f4a6b633d000077d202400016646d49ee8c4e862a0002a1e00000000000000000000000000005ec80001d4800000016ca5761b4c3862b002b029280002af44668ef2000000083e2ac400000000000d62000000000021685778000b2384c613dac321fd80000002b920001ed2c8716cc0000000c9aab447428000a75b198000000000014b26761b940002fca00014a40000dc200000000001c600000000000000000000009908d38a40985c00000006e000000000000000000098f80000000000000000000000000000000a8c000000016ce41a990649480000000000000283600000005f1232a00000000000000000000000000001e900000000d48b53000043a800027b00000000000015294a61e923a00015ecab80000000000000005a60e289f80000000000000000024c60000000977165623399764382cd26fe2b90000000ab5f873c5d8949c07b2f840000000000247c70d00000001994c2c041c56e800000012f4000232e000000040f97a27078e200aeae6611daaaa0000000000176ac438000ad3867a000000000000000000c1637da7863112776bc600003b1800080d1f2a0532478000000036a88c206c0000000079a00000004909280c0ba9f27e2ab3a9ff0e540001e66601000011205869ba0000052000000029fe85e80000001fca485318012480000000000bed10a03c38d8817300000000670a240b18155048243c000000029c6476105e68180001bb97b46988000c13000068600000000000000000005500000001dc8000000000004f871f24fe000000000003960002c8c9b3800
  | 50 => 0x6200008820000aa880a8000000000036e80000001f4a00000000001f86ba81898000000074807c200000000000000000000000000006f5257000000009ac80005b9a10e45580009568000254800000025640002f0c30895200002c389ca000000020ba000000099c8000000150667aad040000bfe0000000000000000000007d32b34000000000000005a59196b4380000000000000000000011cc000000024a000000000001d8000047c0ba6a82866a874000000000000001e9a0fd00001d100000002b6a00000000000000000000076e8000000143863e8000991a0bcbb685be19f02faa50b1d0b2d000000000000000000000000000000000001370000000078a800054b8cd6bfc0000000168c0002aee01000008a3000000015342da8000a8380000e40000a4d1f164a780009b7225e0000000ac423d40000000000000000000005e92948bf3081a00026480002622000000000000001b7aa12000207e0001b160001e22000137a000282a517a3368d70000000040e84b1f0e0e880009731acc2b280001b4ade0000000049100000000000000000000000000000000000204c0000000000000030c8000c6d80001ca28e8000211a00000000000000ca006160001c100000000000000000008e40000000c1880001dc1926000000000000000000000000197200000000000000000000000025941baa4f2a1d00000000000aee063c0002ffc000000016d2c0800000000000c2eb920000000000000028b06610dc40000000528800076a000000029b42111b9cc780000884832a492004e2c7a2dc3580a200e9852a09f800000004445c88000000217643080001b1aee42af800000000008f4800000000007da8000a6189769152f382dc2d60c838000000000000027a896d92d4000000000000000000000000000084c955c4d68000000000000018744510adeb3b0188ad81e8c6e496aa803b03c68314ec00031f0000217800009780002958348000026180000000000a5b80006bb800000015b69c3157a0002dfc637b1a2a17800000000008698000000038c00027b84080000000000000020448e300000002f725b593520000000c410b461e800005dea83c000000000000000002ac2be19644000000000b8a9ac488bf4501050833300000001002000286e6018000000233a00000000000bb40000000567000000000000001eb2000206470004280001872000147068c00000000000000000034680007c7000002c206a00000000000000000000034f800000000000002eee000031c5fa8000000000017500003d4000000000000000000000000000000000000000000000000029f67f580000000000000000076494c2a279f4007b8000000073a0002d78444000000016680000a64000306c9a78000000000080c8000c1a95e800008840000fdc00
  | 51 => 0x5e800000004a88ad00000b6c82f9ebe2b68324bf80af445a2150704b1ae0000e9c0002a106519824000058453d801c82900000300a34a3d8000000000000000005ad00004ef84302a90000000000000000000002896375000000000000000000000018c0000000000000000004004c5800000000000002b400000000000123e5ef0000000000048193b400000003a6800043e8000000104c83889ba9a22eca75b04ca00004083df00000fa0eca000000000028920002aa02a4841495d9384119000000000004198dc84be00000000000b4d8000000000064211e28de2a76b55316e0001b8c0002d5a95e10d62fe1cf48e225bc00000000001e64000000034a800017e00009411a9c00000000000000000000000022d800013ac54c2dfaba5996a00000000000000000011600000000000000a62940c5581f523571afe4340cbc000000097f81962080000000245a0c80b3c0848f7248288ca00031f4c47805c00006d00000000633800000000000000000a8204b0000088000022224090000b6b967c97c86687222ee627528f0c7610e413c8e805a10000b7a1d686ad1ff80001b2200025f80000f3c00005a4000303280bac3aa4ab26e74b83e0abe1670000000094c0000a3719304cba7ca12e801400018be000000000000000000000b03000000000000000000644846a4b61d14b069cf6b3d0000000282876e0000000073400000000000306000000000015f27f08000bbe000000000008340000c7b9ea80000000000000000000000002854b9c00000000000a20000015e80008e60000000000001d920289200000000000000000000000003e41418c11af6c61280000001a880001540685960e0000d4ac6e0000a638000000000089580000000000000220a00000000002bf20720d5a00006143b39af4582800000000000000000000057c20e17168f907f80fca34014400000000000000000073380009f40000b98b00c57f15f000000000000000000000000000005df00363f8127872424e000000000001d3a00000004f5a9720000d7c00020b4000180c0000000083300626f0000c9300000000738000217400012f60000b8400019e4aa3161ca5a122e64008243c0aebea218d741200a6a3992eb4000000089100000000000000000000000009c1147c2ab27a2bc91daeb848ce2585a5caaff800000018a67e532a052d1612250808c91c263826a80000000936000028600000000000000000000000000000000000000000000000000000000000054400000001ea0000000000000000000000000000000075f80007d38000a16000000024b40000000000070aa6a800019e16020000bd60000000000000000029880000000000039420f202200000004c38ee48fd000099698e06f28000000000000000006a9b09200001c2000000088511
  | 52 => 0x6540000a4e80000fd9daa4fc00960001f0800000004cd000019800000002ff82ba97c8000000000024480000000a8a800092ba05428b000089a000083900005ef800000d2a9e0ec85186d200004ad0000565000000006b08f71b7853a9f3a0001e5e1f3800017d8304000219eadb16e2af12c22c820e8c186000004014460f91d40135ac26c309e1c44b8000522000005180002130bdea7880002ee80000001c0c0000000000055616b973800026120000000000000000025904d031143678000aa6800000000009519dfcb9f0e7caec18e414f9016848ae1c5c9800000000000002ef40001d00bef00007170dee000000000021802b182dc0000000763b1664dd80003892dc2ad32fde3e60000b298000000000000023ee000000036e00003fc8c9e6d70c6240c075a429800000000000002bbe62b90f40002a1c00000000002e362e48c880000000000166c000000000000004398ede054a7a400000000001ee07059c9400000000000000a750000870800069e80006711eae89c03a000000000000000000000000000009f5800000019b2000000000007c0000097ab5e8000000000000002e400000000002c0e42799b80002ca23030956000098aa168f2894d905000000003d0a6a2a94235006c800000012d60602d76075800000025ec5df800000012380002c4c750800000000009df8000b351dd4c36948c00000000002bf86a601e200180006892c9a6c100000002c1e0000e3a0000000000000051e00007ca1ae2000000000000000000000b76800012f8000000000060e8000000321000014f200017d600025923c1302200015f6a55041213b80006ae80007b30000a580000711800068480007bd21986768bae1ae00004e58000ca1800000000000000000c320000000028471900000000b96a578000000070e000030885925c000000000000000000000048800000000000908800048580000000000000000000004bc5320000000000000000000000b541342b16833800000028de3a88000c99800000000000000b50000000000000001228000000000074d000096e987e0000000227000000000004fb800038e0a5a3302cd061ba66615e2ed00000f7800003c600000009fa327400019580baa384000000000004e66a5a3b2000000056b0bac9a09d58000314a93280000001114ae1800053f000000000009a28488b0b21a843a00000001f0c680996c975a3b40000000381800000000000002d8600004420001aa888e8a3a702a8242ce80008c500007f22ab49cc284e7728000000000000000000000a04a95800000000001838fba0000d7a0000000000000000003a823d0000000000000000007fb1c560db21ae00000000ef0000bdd8000a728ee26db80003bea33e2b815c2aeb015eb3ea7e003181260000000b16a916b85ab760
  | 53 => 0x86381505bb0e520002c6e377811a413a3e8234800000000002be0f2c06900006550faa00018d8c6f000000027ae00022de0000d900001b7c64b88324350000000000085632240000000000267043ca2f207f0000000122c5608086a1a800070d9da20000000a8a0c5e2790000000264060d0f4a9962d12a5f8000c6595a20001bb08fc8ff00001880000033c00012be9f0ad007d12d4896580003df800000000000000000b489934a19000000005b0000226e00000006a0028e3ac156a000000000000000000000a6d80008ef00005b410fe0000d327570000434afc01ee8000000000000000000228f923ce80003a18b0e74f0000a1e069200001044b000003ce00008e68a360002cfcb4b985a94f8000000000000000003ed0000000000000000000000000554800000020900002ab200011a80000000997307a0b30560000154226e1018be7800000000000000b4e00000009a9000068a0b261958000b5f19740001646a040d1c1c9890893d25a24070000ac2838e00000009f622820000000000000070e00007d98000c2916209d387da000185859d2ee808a800073c0000b63018e33c117614f000050400000002a3400000000000000000000066b800000000001f580000000000a318000000125ca6a0000000000000031680001568a499b8836daf28000256c00000004ba92e2000267a9c60a840002a82000317ebc88b2c7f70000894aa2c00000007430000299800000015be000000000027be00024900000000b9100005c09ce2c6a00000000000b37800086f80005b18000000167a07280006f482ca9c0984e33b08f07970cee0000000a688000249834000000007a20c1285c14822c48704000144425f9a64c1908d00000000a9f80000002a6000000000000000000000000000001ab88b00ab80007ab2812c10061227d8f6a000000078f98080001326bbc85ee7d59e28b90800000000001f1000000000000000ed200025ea0000de61b1148460623307fc9854a2e0000805800000011ec08f16f80002bfa5b600001b5800000000000000000126a40c46428c804200000000000c120092000000000000000000000000000000000000000b741ad00000002e740001af0000216c0d50000000271a000058a6c61b6c99fa238000004808d85d200013ce73f00005b68000ac7800000026d8b598cc83da0000bc982220000000c1088340002e6a0002e58000273ca85a07a765099642e2f580000000a5f000000000000000000000243a0000000000000000000000002e0c000000000000009458000447000000000002e50af200000000000000000000000012220001f5e89d80000000ca20001c961fa86e6000000033700008a1800056e0f185130a22000000000004407b09298000000038a800000000002b30e22000000000000000000
  | 54 => 0x76c41f8000000000000000000000000000000000027407e9854c0000000000000071080000000000000047e00000000002ce69f50000000000000010623bf80000000338000000000000002e7800000027c49daa4740002c4803b80000000000000000000003ba9850000000005831d0000319aed2259b1b0baaa3ca42385e0c382b1215099fcb638000901082200000002d116d21e28350c1f288ab6e8fea31b285200012364ec1844ba906b2000199280eaeec807829e9db287a9c0189aa999d1a76729f49791d82000000000017b01498000000000000000000001fd20000f9c6ad9e8611a23565588000851800000019c84830000000000000000008aa0000000000000000000000000a78000007a0f1cbf600000001a5e5d080000000000000000000028d89db8000a3f00eac8983d0000000031f1cd27f0000000011940000000000000099d95a60000000a80107200012720000000000304a0460eec83b8000000000000000001e1800000000000002b6802b8000000109c0000000b5a8000000050e5678000000000000011fe1fb800000000000000c7638d00000000000000198e0860000000291a0001dc21ee11a40002e06000191e3ff00007dc8000000000000000007f88e6e00000000000a32bae80000001da43328000000000036918e24370000000299800000003f180000002338000000000000000000000000025e0000000c6800007418000000000035526d400031f20002caa000000000000000000000000000000000008cd17fc94c9bf40000000000000000026e600000000001c6600000005caa7f0ba70000759000091000000000000c1b80009f20000c910000000087600030720000000000249642b81429cd96b20001d5eb68abccbc184580000fd8081953e5e81ac877996a6b309e048d2800024c80000000e0800000001af8b084fca8a60748000a902190000024e4bb8000000054886499b00598e6aa1f97b8000149e7188000b85000067c0cea09680005489aca00026ae00000000001ff629d000000025d4282aaba63715148832fb6c2d8000747221c00009ac00000000002e245e11b0cc1780000000000778a06843e00000001a529e485725ea884800000009b3087e7e1052cb4e13623f0800000000007ee8000902000000029068f01fe8000294468b8aee73591c468800000001cf8000000000000005f19fac00000000001c7a4ed9056000000000018d4000000077e0b1a93900008be11ea0000000000000000000000000000a020000000000058a26baa7720a8000140042f30ca8c298266ba1240b8c31125eda4807959532706000000017e00fb1dee000000082800000ed07fc00000000001ba000013020000c6e7270000000000000000005d91bdea2fae08187abe88c5a7b45f8a3a0203047089f165a
  | 55 => 0x271c000000000026249d408a0afa807a2380000c5d00000001bda000000000002debf40cbe00024b00000000000000083a899a09c00000002894c589312a1980000000000c3c000000000002da2f6eb80251e689820ac0aa57c00000000000000000048c35b1d784fe8000000000000000000e12550395a0c29d4b0e8bdf9e74b55915e4df91b479a110e1928000000136400000000310cc21fd2f8a4e200002600000a89000087b300a00011a669c2ae63810c3066322e27a52bd623b0000b0a00004f786e800000000fe2e38421222a00010b04ab800015c00000000000000311000000000000000000000000000003f904629c38000978800000013983b524943438ad452380000001f8200004ec00000000000000000000000000000000000a93254e0001be27fc000099f00001820b7a9e5280a33799ba6b4000000000009fe000037c90a200000005b800000000000b7a90e261e00a2987a9d00000000000000000026bc00a800060092e8bfe8000000000046e80003c48000bdf1060787a5520000b3478c80006dd311cb3aa6d6000000036003c20000beaa3023c8000000000000000000434058000034e94a80000000a12a0a600008dc0000000000000034d000000000004c8251811422940002c9400013680002c7600002160000000000000000000aac00938a0ee00000000000a73971ead78000000000014e80008f8918c00000008e5800070b000000000006cb8000881aa68adf800083e800000000009e40000a070eda12b00000000000000000000000003e11b8e6b980009df0000000000091d832e8460000000000000000000001c7400000000000fa60000000bdc00000001ce4c4d80000000000000000000017ee000106eaef1b549e39770000000000000000000000000000000028d2000000000007b06d3800000000006ee065c0000000000106c04514747c6a2660299a2a0001a502b48ec200014b00002b0200024c8b0a8f0c000000000001f875ab2720000bd20001d4c000000064f80000060000ab500000000000bbc0000a90824409600000002eae066076eb75b0f21ff9572000000000000000000000000000000000009baa4680002e0a000189460b852240a0000000237e00008180000000000000000000000b209465898000000271457e05ba5cc03fab54a4724b218bc0000000361000000023b8000000000000001451d2c673888c0001e260001d166afadb89348000000236eab3b1160000000223800000000008fb0000000126a000000079b115cb05162e8e00000000000049f09640000000000000000000007cb800000000000001c72a650674000000000000002f0000038c800008b80e6000000000014f000000005de000000000000000e1a0000000631800087b80003d30000a9e0f4e0000000000
  | 56 => 0x215a5e48c5433a27c01d8ae9e5d1118e63a0466265178698700000c794645d30be026300bc06d8fee59d9f92000000057280006050000000000000000000e60d824e9a0b800000000002a204c6093ca0809e600012040000a4a35b9338000000000019de8ac000083c80f289e000000000000001ef8000160400003aa90680006ec8aaa000185e00000000000000000000000000009058000000000000000002a3a6fc000000000000000002974000000001404b80000000000024800000000000000000328a204000067800009cfb07e89b19044eca50a45683740870e000000000a09aba000000007138000b518000000100400000000002c8600015aac3f2394000263c45f000000015280003126c34800096e1d72000037a0000000000000040e262e0002d7000000005e21600b0d0b8015d1ea20000f3ebda00b40001ec400012e6b2d8000b728000caa000029380000000f52000080616500000002a0c000230cc5800007601ece000053677b0000000231c0108000402213000000000cd97de3700000bd4ad5e044800021080003e880000002fb8000044a000000084a00008362ae400000000002e1850b0000000064679380009939d1e0002a4a00000007918c1c6ea3152b4f9d70351807024fa5c205e091e5cf1aea06a99e8474000009900000cc965071b0000000000000009c09b9128600000001968000a7c0000130000000000000000358b98060600001760000000000000054e8f2e000329891914e800000000730000000000089aad2c00000000002a88a70800048200003ab000000011c21a400007cd8000000000000000009051230000061080f8000bb8800e00000001921780500ac72bc4800000000000002f3000009a4c5da2464f28c4a0000b22000000075f272022f314c6688132000279a0002c4a089050c6ab80000000f5e000000057e8f66000000000000000000000ad289fe93e2374000047800032aa000000000000000000000c351fda00013224b78000422000089e800095faefc4b081226ed80004040aa00001a660001cac791000041f279c9dca9be000287211582265fe2908b30000000000007ed14dc082288e96aa01200010f600000000000000000000032d00004b3af2c983a7b220b003c966992c7c4ad9ca60a708b9280000000000000000021c9ac68472a6e14780000000000b62800000020aa0001afa0000000000045a29490b49f48240abf0790b280000000000000006620000000bca8288000000000000000000582000000004b8640936286831e00004150000000000000000000000000836a952b5000000000000000000080600008758000b8f00000000000000042000027de8d0a7b0a22000000000000eda1005a8824c6788000982ae880000000000000074880000000000000000
  | 57 => 0x1683c188a0002c7e26100001f7896e6b60000000000045a80009b1a1b20000a8c000000000005d6000219600000000000c720001b9aa74a1c499b12ac38d8000624a2e00000000216000000000000000000000324663c0000000186000000003d6abbac5e1ea4937b22ebbeb27a76f1cca8efa302c431120b7d89dc815a49a73407144e4193ab9380000000000000000016e01b40000000000000000000007adacfe0000c9c96380000000000000000000019fe57186766458efc955a09eb2b901e3c20000a46000031a01bc930994200000009b800005a61720b481adca898e8a4e008b88a3a4ce3061b0a9e2af480841e800002f8839419364ff0000202800084ba5a838c00008ec311885588749070074000105a6718784b0db18e0000dc61d7027a8fe12106c22e4c00000000000000000000000000000001212000000003e256e000000000000000002dd8000000000000fa0001ef09600000b4aa83a571000066280002eda6ca0c08c4042900000001cb4000000000004103ba000000000000000000000009a00000000001c245b700007dc000000000000000a6200000000001f383b98000585000000031e80f4800000003b000016941a7800000029365559e127cc0afc0000000a4000002d28da0a7a811c00000000000c5800013e600000002d7aec20002c6a00000000002a3e000000000000000001a2c000000000000000000000b8d000000000000000000bcfa324b15800000009d0000000000000004aa800000000002e227100000000a12317a0000000c3ea2fe237800000002f87248000703b29c00000002510000287800066900000000f5c0002a02bad8000000170c00000000001a0060c0000c6280000000000ca431fcc099bc277300000001c58b721d76000000000000000002aa634523ea3038000000000000017329f70000000000052b0000000238e27d2f5c0000000614954e68c800000024a4000328200000000a89e503c7800048c8f7ac6505c8b2a1db60002d149481bcc50c056c00000004560000000135e8e1ad100a2846e000000000029969ad191818d88ee6328d783c50fa40000d52b07007800000000000000ca50df0329800000000000000b90000000000015d2a610c2800000006e580008380000000000000000005e700d400019cc00031ac000157483b05461a80c2c333aabc000010e6d100000002c4496080000ba14e2c070b300000900ac920266d1800043b00003f5260c293000000018a800000000000000000023200000000000000b8b1dd200000006e6113837e000000013aa1c593822ca2df000009b0000000000014ce0001ade0001706297063e00000000000dda35600000002fec00001ce65a000000000003efab14310a8d6000000072d800000000001b80afe0000000000000000000de00
  | 58 => 0x949c08000000057a800090faffe8a905aa94ba77a7822d449cc80000001e24a7907cc9281922be4ae8e24700006caaf9c00013dc000000000000001da99320000000000000000000007f1000001a8000b262b520000000152a2c4183186a1d1a1d2000000000026d00000898979800018900004fd800000025860002e2a0048000aea000000000000001fce0000000ade04241c00000811a71e32b9a1c816883e1b500001aa95e268f91180000000c288d94bc2000000017480000000000308c00007e60000c9a02e9b8601800001950000abe8000000047a00000000000000000000000018680000f8e3d0272226d035a853b1503898c360002172000129602793c04770a5e6b520ac5f012d20002f0a9330000824800046c944e0000000820131c00000380000be4000072ab4d2ab00002b560a41f6201f0000000210600000006b0000000000000000000bc381fe00022307cf8000c8680007da000000025229c900e016d80000001e7874a971a3251a82b118ca4493a2928322ed64598000a730e5a3d500008a2000000019ec65c113c0000d0c13c000000002140000000754996e000015a000129027214ee13f000000018fe24800004c2800000012b000006fe41d8000000000000000006b580000000266000000062a80003e19e6e00005800000970aa4000000015fe0000000b4227968f629664faa39e0000000000000071500002ac0000bd92ff23f6aa8e7fbb1922d580004c1000000000000002efe69613a20000c823bd0000000011000000000001eb80000b6600010480001dceab7091023000005e58000000016400000000002dde00000000000000000230800014c48f3a07800000000000dbe0001c6e98d0000634090200b0000000000018800000000000000098200000003e022a61ebaf020000000bf4800000000003a080008271b2c64387b4b058000a3b1154b6f8000000000045b80000198000b978000935800066faf5a40300000001f8c00014fe553000000000000000000afd800000000006042e90000001600027ec0000826000217eabf800064a919c0000cd0b970000bf5280600000007ef80009e09b6a37f800000000000001e48000089e8d80b58ae9802200000000000000000309a0000000000000000005ac0000000b35800022b121e8960000bf919b446b920e6939d7a60cb16a0002a94be980000000000000235800000000000000adc252a411ab58038a1863be014e0000000000000000000000000000000000000000000000db00000000000000020a80000000000000000006780004a30a56171969e0000000000000000000009a5afc800002b6000000000008e8000000021180000d19408350800051b8000537800000000005ba0000000000000000000000000000000090e30f68d380000001e1800027
  | 59 => 0x7ba8000000000000018c800000000000000519800000000001e082da0001c7e00016a0000329a7c621080000000000000000018224d326f034b800000005da000000043b99ee000000000000000002be6b1400001d9091a00023120000dca43602e681f0c1a000052413480001409bea0000c3cbc8000028906960ff08145b0174e0e7194c2b6155803a0000b170e88283800000000008d11f74095235e000062e13eb0d800000008311300b1896b8000007e3159ac40002aa26f1a3c4328000000000000000000000000000001f200000002730000000000019400001da000000000000000000a4500000000000000000000000001c30000000000052a80001f2acf8a291012645000032b000000019e6753868c00000005948000aab0000000310220bb242000000031c31247098000000000050c8d7600000005fd17680752a364c5062293410cc000164ec0580008891b020002296000000000000003fe80000000000b2c98366b80000ac80000000163a39c00008b40000000000000014be00025c40002e32000000000000005d027fa00000005690000000000000025b490b93c65098174479a13816c82d20bd800000000008798000bf10000000000000001722bb0ea492a0f3256280008ab8000000000023a8000000000017780007052cb000011340000000a680e4a32e00000000a708b680007e905e60f300000000000b478b6000000000ce99ca0002b0400000009e124203241e9800000006ca000011b00004f680007ee0000000000000006f266f0000000000093eab8c1e62d9a81400007628000ab8800009e0000000000080400000e4800000019109d6156c0000e9e00004221480a980000000ab2a7cc6a815a031f95d0440000000016580de2c580002e200002754b7f8000000000000000000001cfa60a000000000000002d1a8ea9e2cc641760000208ac211f24437afba5c2147600000002d9214000000000000000000145c0001a4c0000706a2080000002d820000000000275a0000ed85bd91be10e8e0ebe820deacd809c000000000000000000000499970000000000000f620002c7492789b697191b04cca6b0b8a159a00009885af80000000868000000072c800079c000000007e0842a3489de000000000000000000000085e77c103669099241b22a067088ed6000000061d9e02506800000000005e50d08c9890341770b1c000000000028bc000000037885a2b730f2a77c90526bf07b22ff000000000000000000000018681da14493c2cd8821983c3350000c38800000000001a63158935000000000007fa800000000005fc000000000004940000000000039700000002980266000051000000000cc666a80003a1000027e800000000008f82d3298980008af2e860002d88b49163c0001c6a2b8993c00000001
  | 60 => 0x6dd80005a000000000000563145a6d628aaca5800000000004b19da6229ad64c80000050800000002684000000000007d2a47800000000005ad865e16380000001092a0d000015fab960000a6c1622ccc929800000000000001e7e00025e0000037e16a09de2b082c6b192fb299288fc0001b640001344000250066a1bdc000000000000005ee800000000000000000345b19c40c80000002272667a748a678000144974a0001b504ee99d65ab8000000000044b00000000b9a0000000283161e23dac9000000006d287be0000000b222dec8330000000329e000000000000000000000284a19a5e4246a0000b76000078000000000001fe60001fbc000163400020dca723276ab496249d2800000000fe242895e56c8000000000039780000000000bcd27c60000000000000000000000002b8000000000001b7029ca1c00000000b0b90960000000000000000000000000454000000000002c20000000462ad8086f0eb20b1035689f94c06c80a6800023de8dc03c8000016c0000000000168600032060000000a1f00005bf0000000000000000006480494a98aa320000000bd9834824e8000b102bd255faf82b6c9a3cbac8000000000000031c899a8000614255813d04d846830b247024021261a7e97d081e8900f162e29ef2b1790783fd1d9893a0be239122160bc268c09b000063b8f9e80b2d28b0102ac4e922a06a4b07000000000000000c0683be0290a9e00000006a8b21215721ea5dc800056b80000001ca4a1c1342000126800028b446f00000001a04ad9868242c800048700004a900000000dae344229c5039bfc33630f4c4b24522be9ad2c40150a25b0e94a6f00007142cda68285feac9a37ab1a01fa1a28000048300e1aa308a0001bfe0002baa58401d087a000047232a28e2919e5c60000562000000029c48bb98b800000001e7976c00004842100d6424e1a3a3eb96ac00031864cd8000af7800013700000000ff60000bbe17884d48578bd03ed9c3c7bf0000000068ead500004fb3012000000000009608631efa00028ae2f2a17c000000000000000aa9d0800000006879f2c00021420002d5c77f817c0000000000001e4261866c4f0000539800000000007bb8000000000090b22ca5f080007a99bbe3ab80009c480000000a4400000002530eb441ea59cbc417ac000000066219f800000000001f64a5d8fcc0000000a5185908b18000000000000000000000000497a2b25be82743558000741000077a80000000eee00000000000b028fc229e00032200000000000263647b95e029eaec45c4a6d2afb9116000000037a00000000000a7e800000000000000000000250c00013240368000000013c6659ee400018da0000000000000000000003a48000000000001b800000005bc0000fc0a5580000000f2200000000000
  | 61 => 0x800081780cc0001d4a0000000000000000000009d318cc00000003ea31be70100000003080095aa6c9eb0000be61f500000000431810c9d9800070e80005980000b7b80000000334563a01a000124a000000000016c400000007e22dd200000000000000c2980006ce800054aa3da97b8000a4c80000000000a5e000000024108e98b7e58d80000000000000000039c9cee000000086b2f1e0000000000000000000000003148a1880000b42d9214c800024617285a683686c90a18000232299a0000000000000000002432400a0b064c88d2feaad400000001af825f00007e79dbe8eb21f036615924522e1e0001354889800000030500000000000263045d00000001dd80f7000034194cc3aa000000012fa71310ac1991f101c723a8236b1d20002b08a591cc2000000000000000000000bea000000000000000000be8874cc69000021518b687680000000000000000094eae9809c9184190800022597240570000000000000000007122de633d8000412800015da7e2834957097daa6400000000000000000117a45c00000002f963b2084e7a7210481989d826c95461ab0aae0002cce03d8418000010a00003ca0001ae400000009e0281695c96060000bb8b5b00000000000c2f0000000039ec00190ac5390405fca898000220ec5693d0000325a8b5086292c8000c3ab1545d4a7983c000000000000000000000000004202b2a00001be00026be98a80003af0000a33227409b8000000000000000000000000000000006b00000000000000229a80000000001386000134842402e24f31d18adf199a00000004919022186a9c06a68000b27800000031ea0000000945000045b00007598000000095400030686f100000001b107ff000000001c6bd59fe01f4000087e9d6200003d800000009218000000000054131c40d08000000096aa142c0076811502412a3a4a71f7e0308000000241e0001512460aa440000000000000000007f000017ce24b800000000003c8000007d0000b3900002438c1e01914d2340800000016922d01b6200004cc0001cae0000000c2e02a869b000000000000002d1800028da3fe30d0b9003665368000876000000023c2981ae76000134e950800000007940000000b8980004a280000000000000020200000000bc8000000000000029e80000000000000000000820000000000000000019f60002bec3461e6a0000c5a0000000000189e7ec80000000000368800000000002d89e0c87900000002da400000000000d8c99900000000000000290a8eda6168ff11aa0cfa7f46282030b7e000000000004c780000000000000222862e8000707000003f2e527dda0c0669adc4c4e1b0e0001902aa1263a0002b0e0003232000061c0002ec0459238200010440000fb80002e926d69faa0000a060000fe8ae6b184
  | 62 => 0xbd1187c40680009a520d600000009680000000000000000000000000000000000024ec000000000000008688000a570000380800065e800061087a600000009372dce000000000030b490f0000a3f8000743892200008f800000000000a9c0000000000000000030f85d78000000126c0000dea0001260000108c2ec80000002e80b312208000000042e8000000263257300001b70f56000000000007b6a6ea67808d029411f00007f322ec000037600000000000d2c0000000beb00005bc000074900000000f9aa6c01682ad9262000000000000000000000000000000022f4a4709620002fda37d000000000000000000000000000007660000e6cb1500006fa0000c920e740002b461012134bb3224a000000000000000000000130800083d0230000000000000004f08000832800000023fe6f61c060002e72000000052b80006840000000127655e00905bb80000000abc00002ee00000000000000000000000000003b40000000000097a0000000040a01a0ba851a800065716d40000c481fb19780878bd421c1e4000000000001d6e000272e9ce9cbc0000bc6011081629208645d5092a0a72b06b642f3c8d4a4248220fbc00000000000000c2a8c38287203c17a8000a7600009bd000000000009d5800000000000000ace374000000010be1fa265eaf92bb65fd80009098a2a07ab22200000000000000570269a75d18640000d0000000000000000000000088b8f34000074a00018400000e460002c3e0698c2a0000000c9e00000000000000242a4cc0000000138c9f6b19a0f78000820966600024660000b5266d800000022c0000000000000004ae0000000000000000000001e520f982768ae875800000f4272800068500009842124383102ec5000dc000000020231dc01c8e4e000000000000000000000000000000027f25140000000245c8010000268a1c80560c8e0000a8a00014e488109500988000000000000006380000000000000000000000000000baf1774000000010c92a8000000000000003828000792a7380d10f7000003ea000000000000009bd800096780004f600000000000000000000028a8577156403480008c0256815489ea1630bd8000000000000000000000aa2a6024d187ac0001d86c0a0fca36481920a6a7ce8521a9e22b9d32000000000000000f580000002cbc000000079f0000bcea7b60000e76000000047900001cc81e00002cca73180000000000000258493b80000f100000000000000000000018f6000105c000231022224420000bc4986aada4d713584a4a1142199d8ca2125341ad9a4a5c126a80002020000136e00027ee7ea0000000286c1bd00006eb000095329400000000000074235c00000002eb070fb03ea38a2ac000000039e0490b1f00000002c528da02001068000ac69288943
  | 63 => 0x2daa2648e90c7988aa0390bdc5e780002bd86f0000017a4a08b2e7a8000000000000000604000000000000004db000000008fa98a000000000002a580000002fe844e80000000000036181200027bc00000000002116878000024580000000000000000000000009b89f00000000000000000001140000000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8ec8758942440010ff0abb4648801e1f215768c9100045fc22ed19220048bc845da32440031e90cb8c648800a3e219708c9102a4bc42ae11922053dd0315c232440010ff0abb2648801e1f215764c9100045fc22ec99220048bc845d932440011bf06bb2648802e3721d634c91005d66412c699220018f686dc53244001b6481ba2a28808edc203545451011db8402a8a8a2007c7476d4d51440476e101a9aa28800a5d21d535451003e3a3b2a6a8a2023b708054d51440476e101a92a28808edc201525451011db942ee0a8a20019f280dd54144001ae0a1baa82880063d2197550510014da43a86a0a2004cb47650d41440033e501baa42880035c143754851000c7a432ea90a20059d4835d52144001b6481ba242880063d219744851002cea41ae890a20839d687dcd21440019a8edb9a4288003351d8734851002e6a39ec690a200b8f48758d214400174b083124288002f160c6248510005724328490a2005dc4738c92144001d8ec7192428800a7921d324851000762b1a6490a2000dd073dc121440472f30fb2ea0881fe5ee1d54d4110014f840ae7a82203d97b8754b50440ad7a10690ea0881f65ea1f75501104063c3b6eaa02207ec78761d540440a9a75083aa80881f74e610755011052e9c320eaa022054d5a831d540440a9ab3063aa80882974ed0875501102a6b9408eaa022054d71811d540440fb8f6c23aa80881f75cd84755011052eb9208eaa0220a5d71411d54044001ae6623aa80880035c0c47550110006b9108eaa022000d3875d9140440033710eaa2808800a7ca0773501100069c3aa84a022000d7075dc540440a9ae0eaa8a8088003cc5515150110006b83aa42a022055bd0834854044001f428490a808800a3e219744c1102a4bc42ae898220019d88754d304401f7a102a9a608803ef4205434c11001c7c43ac4982200fbd0814c930441497a507b8a60880027c21d514c1102a6b83aaa29822005bd0835453044001ea2a6a8a6088016f420d414c110007c8a1a829822005bd0834853044001f826490a60880d65ea1f75481100063c3b6ea9022000c78761d5204406bad3043aa40881535ca0475481102a6b8c08ea9022035c7b611d5204406bae6c23aa40880035c9047548110006b9988ea9022000d70311d52044001ae4423aa40880036c90774481100147c432e89022054978855d120440053e503b9a408814f740c773481100147c432e69022054978855cd20440035e303b1a408802e3e21d6348110005b4c28c49022000ba98418920440a9ad0eb2924088002ea612524811000cf443aa49022000b69859092044001ae0ebb8a40881535c1d55148110007b0a92a29022000d70755052044001f4284a0a4088006bc2192148110016783b2429022000d707548520440a77a10690a408802fb81892148110
  | 1 => 0xec32a609000f361d9434c120005b4c28e49824000ba9841c93048001753092926090003d254d524c120005b4c2c849824000f894350930480033b10e992609002f361d9324c12005ee43926498240019d983dc530480075b507b0a60900f71e9db65c812003e3d3b0cb90240009db835c7204800187ae92a6ca880029d60654d95100053cc04a9b2a2000a5d83153654400917d0fba2ca880030fdd474595100043fc3aca32a2000a3c8459465440010ff0ab96c88801e1f21572d91100046fc1ae5b2220038dc835cb6444001878c83aac88801e1fa1f75591100061e3aee8b22200487e859db54440051f3013b6a8880021fe1d65d51100251e422cbaa22000a3d85d9354440031e90cb8ea8880032dd9171d51100043fc2aecaa220008bf845d954440090f90eb2aa8880128f21165551100147d436e0aa220028f9809db53440070f90abb6a6880022fe1176d4d100245e422eda9a20018f4865c753440a9ae0a0b8ea6880022fe117654d100245e422eca9a20008ef825d953440171d904bb2a68800e1fa1f6554d1000c7b436e2a9a2000d7050dc553440051f50db82a6880021fe157650d1003c3e42aeca1a20008ef825d943440171d904bb2868800e2fa1f6450d100246e43ac6a1a200fcd47158d43440031ed0db8a86880022fe1175d89100245e422ebb12200087f855d3624400f0f90aba6c4880122fa1f74589100061fbaee8b122000c3c75dd1624400187eea3a2c4880030f1d4745891001c6f43ee6b122000c5f75dcd62440018b8ebb9ac48800327dd373589100064e3a6e6b122000c5f751cd62440018b8ea39ac48800327dd073589100064e3a0e6b1220018fa87dc1624401795cc4ba0c4880023be1d621891000656ba2c4312200bc6f205d462440018da40ba8c48802f2bc8574189100065690ae8312200bcaf205d0624400195a40ba0c48802f33c85731891005e6b10ae63122000ccd215cc62440179aa42b98c48802f36881731891005e6c902e6312200b87e859db52440051f3013b6a4881128f21165d491000c7a432e3a922000c3e74d9652440031e90cb8ca4880035c14171949100147c432e1292200087f855d9524400117f08bb2a4880122f21176549100046fc1aeca9220038dc835d952440170f90eb2aa4880f28f21165549100147d436e0a92200787c855d8524400117f08bb0a4880122f21176149100043ec3eca29220018f4865c452440a9ae0a0b88a48800a3e219701491005c77414ed2122044c3c649d6424400187cebb248488012ab211629091000c7a432e321220028f8865c242440010ff0abb2848801e1f21576509100045fc22eca1220008df835d942440071b906bb2848801e1fa1476509100043ec28eca1220038de831d942440011bb063b2848802e2f21d64509103d51e42ac8a122004
  | 2 => 0xf421952003c3f4386432a400087d870c8654800147d08190ca900028f61032195200053b4086432a4000a75810c8654806b4f500190ca900d69ea0241195200053cc048232a400787e8710465480010fb0e208ca9000297a0c41195200052ec188232a4000a6e8210465480014db04208ca900d69ea0041195200053cc008232a4035a7a808c465480014f301188ca9001e1fa1c31195200043ec386232a4000a3e840c4654800147b08188ca900029ba08311952000536c106232a4035a7a800c465480014f300188ca900d69ea0221195200053cc044232a400787e8708465480010fb0e108ca900028fa1021195200051ec204232a4000a5e8308465480014bb06108ca900d69ea0021195200043f43ecab22400087e87195644800f0fd0fbaac8900031e1d770591200243e42aedaa24007c6c659cb54480031d90cb96a8900021fe1576551200047dc02ecaa2400487e87d95544800947d09b2aa8900021fa1f6558d200043f438cab1a400787e87dd563480070f90abb6a69001f1b19672d4d20004d6c24e5a9a40018ec865cb53480010ff0abb2a69000e1fa1f6554d2003c3f42eeca1a400087d85dd943480010ff0abb2869001e1f2157650d200047bc0aeca1a40028f4815d9434800717d0fb22869001237a1f6350d200061fb2ae9292407ac3c655d2524800f4d90b3b4a4902778b19674949203d71632ae92924000d2f655d25248001a58caba4a49002f2bd81749492005ed5b02e92924000daa305d25248001b5420ba4a49029a5b61f549492000536432a9292403dc7870d95524800f8d8edbaaa4901a6cba1375549201eeb4386eaa92403dc6c76d95524800f8d8ec32aa4901a74b953745492003e363b6a6a924007c6c7654d524800f4d90ca90a4900021fe1f65909200043ec3ecb212400787f8719642480010fb0e32c849029a5b61e759092005e37b02eb212400bd6b605d64248001ad460bac84900035a8417590920004b7c3ecb212400096d871964248001c5885b2a84900d71e1c065509200063c32ee0a1240018ec865d5424807b8d8edb2a84900038b19365509201ae363b0caa124000b2e85dd1424800135d0faa28490002aba1b545092000697baea8a124000aac8650d4248009958eca1a84900063e20175d85200043f43ecab0a4000c3c74d9561480018b8e7b2ac2900021fa1c65585200061e3a0cab0a4000c5c73195614800187ecbba2c2900030f19774585200062fb2ee6b0a4000c5c65dcd61480050f90abb6a29001f1b19672d4520004d6c24e5a8a40018ec865cb514800f4d90ca96a29000a1fa1f655452003d36432a4a8a400787e85dd941480010fb0bbb2829001e1fa17764c5200043ec2eec98a4000c5c73d9521480018b8e632a429000317d9773485200062e32ee690a4000c7876d9530480018f
  | 3 => 0x4992600be4e85189324c017c9b0a312649802fa3a10624c93005f46c20c4992600bec681189324c00159b02312649802fb1604624c93000562c08c4992600beca80189324c017d9300312649800237e1d32d85300143e42aeda8a60018dc865cf514c00f4b90ca9ea29800a1fa1f655453000c6f436e6a8a6000c5f65dcd514c0072b90ea9aa29801e97219535453000c6f436e6a0a600399c8750d414c0010ff0abb6429801e1f21576c853000c6e432e790a600bccc764cb214c0171f10cb86429800e3720c76485300066b188ec90a60018de86dcd214c0073990e9924298003331d9324853005c3f43ca8b2e4000c3f7495165c80014bb062a2cb900121f21576d53200043ec3ecbaa64004a3e84d9754c801717f0eb26a9900028fe1564d532005e57392c9aa640018ee82dd954c80090fd0fb2aa9900128fa13655532005c3e43acaa9e40008f7815d943c80051e902bb2879002e2f21d6450f200246f43ec6a1e40a796d87d5252c807b6d100aa4a5901b74b9537454b2000cf4402eaa16400baae86d5142c8001a5eebaa2859002eab2194350b2001c6f43ee6b0e4000cda20dcd61c80011bf06bb2a39000e3720d76547200143e43acaa8e40008df835d941c80071b906bb2839000a2f21d64507200046fc1aec98e40028dc8758d31c80171e90eb0a63900030f5d254d952000536c14a9b2a4000a5e8315365480014bb062a6ca900028fa1053d95200051ec20a7b2a4000a5e8399365480014bb07326ca900028fa1263d95200051ec24c7b2a4000c3f749d365480014bd073a6ca900029760e74d95200061eba0e9b2a4000a6e821d3654807b4db043a6ca900028fa1273d95200051ec24e7b2a403da7a801cf65480014f30039eca900021fa1c43d95200043ec3887b2a403d87e87d0b65480010fb0fa16ca9000297a0f42d95200052ec1e85b2a400087e870cb65480010fb0e196ca900028fa1032d95200051ec2065b2a4000a76810cb65480014eb02196ca900f69ea0032d95201ed3d400e3b2a4000a79801c765480010fd0e20eca900021f61c41d95200052f41883b2a4000a5d8310765480014dd0420eca900029b60841d95201ed3d40083b2a4000a798010765480010fd0e18eca900021f61c31d95200051f42063b2a4000a3d840c765480014dd0418eca900029b60831d95201ed3d40063b2a4000a79800c765480010fd0e10eca900021f61c21d95200051f42043b2a4000a3d8408765480014bd0610eca900029760c21d95201ed3d40043b2a400087f8759465480014bd07320ca900029760e64195200051f424c632a4000a3d8498c65480014dd05a18ca900029b60b43195201ad3d4048632a4000a798090c654800f0fd0e218ca900021f61c431952003c3f43e8432a400087d87d0865480014bd07a10ca900029760
  | 4 => 0x25000187cecaa4a4a00030f950765494000c5e432e82928007c3c655d0525008927f0eaa0a4a001e8f219541494005c7c432e02928000d39545c052500f5878cbbaa84a00062f21975509403f51f436caa12807fc3c76d9542500fb878ec32a84a01eb0fa1c65509403d61ec38caa12807ae1e8319542500f5c3b0632a84a01fb0fdc865509403f717b90caa1280a9e38701954250153c5e4032a84a02a78b480655094054f1d080caa128000e2c65d894250001c5eca31284a00038e19770509400043fc2aed192800787c855da32500fd87ce832c64a00062f219748c9400061e32ae9192800787e85dd932500010fb0bbb264a00021fa1f65585400043f438cab0a80a8c3f7419561500ff0ff0abb6a2a000a1f21576d454000c5e432e9a8a8007c3c655d3515000f4790caa6a2a001e1f21476545400143f43ecaa8a8007a3c865515150001878ecaa2a2a001e1fa17764c5400043ec2eec98a800087f855db215000f0f90abb642a01fb0f9d065c854000c5e432e990a8000c3c655d32150001c58caa1642a001e1fa1776485400043ec2eec90a80038de839d921500011bb073b242a0003171cf65485400062e398ca90a8000c5f65dcd21500018b8cbb9a42a00038b19542485400061eba4a9b2a6000a5d83953654c0014bb062a6ca980021fe1d651953003e1f32ae832a6000c3d655d0654c0010ff0ab96c89801e1f21572d913001c6e41ae5b22600787e87dd5644c0090fd0b3b6a8980021fe1d65d513000c6e432e7aa2600087f855d9544c0090f90eb2aa89801e2f21d645513001c7d436e0aa26000b1d84195534c00f1b90eb22a698003875915454d3023dac402a8a9a60018dc865d5434c001c3ca9b2a86980123721d6550d300070eb2aa8a1a6045b9880551434c0010ff0aba6c49801e1f21574d893000477c3ac43126000c5e435d4624c0178de40ba8c4980031b481751893005e57902e83126000cad205d0624c0018baeaa18c498013279d143189300066a18ae23126000cd7835c4624c0019a906b88c4980033590d71189300066aa1ae2312600bcd7325c4624c0179cc64b88c49802f354c9711893000672992e2312600bcf2205c4624c0179e240b88c4980023761e31189300066ab8c623126003cd9708c4624c0170fd0b3b6a4980063721973d49300061f3a6cb29260018dc865ce524c0018becab9ca49802e3e21970949300245f420eca9260008bd841d9524c0170f90eb2aa4980021f61f651493000c6e432e6292600b8f8865c0524c0031b90cb9c849802e3e219709093003c3f428eca12600087d851d9424c0171790eb2284981ea8f215645093005d56412c8a126000c9c7650d424c0031b90cbaa649800637219744c93007cea40ae8992600bace86d89324c00178b023126498036b3a1c624c93005e67438c
  | 5 => 0x80032b4817498b500043fc3aa9316a004c3e7455262d400f0fd0bba2c5a80f28fa137654b501e43ec36e8a96a03cc3e64dd152d40170fb0abb485a80061fa177650b5005c5ec26eca16a07ac3f54dd942d40010ff0cbaa85a80065e2017550b500043fc32eb196a004c3c7455161d40010ff0cbae43a800237e0d764875001c6e41aec90ea00487c855cb645406b0fd0db92a8a800e2fa1f6450d500251e432a8a1aa07f87f855d362540011df0eb10c4a82be9be1562189500043ec3ea8312a004c3e74d5062540890ff0eaa0c4a81121f21974d49503ec3f436e8a92a00b87c859da42540030f90cbac84a80061f219755095000cbc402eaa12a00baae82d91425410147d0daa284a80021fe15768c95000c3e432eb192a0048be84dd9325400117b09bb264a82079c14361545500043ec2eec98aa00087f855db21540030f90cbae42a800e37a0e76485500046ec1cec90aa000a3d8414f655015d47b0931ecaa02028fa1273d95405751ec24e7b2a807fa3d841cb65500010fd0e196caa00021f61c32d95404051f42065b2a8000a3d840cb65500014ed02196caa00029d60432d95403fd3d40065b2a8000a79800cb65500ff4f50038ecaa02029e60071d95400043f43863b2a800087d870c7655010147d0818ecaa00028f61031d95400053741063b2a8000a6d820c765500ff4f50018ecaa00029e60031d95400043f43843b2a800087d87087655010147d0810ecaa00028f61021d95400052f41843b2a8000a5d8308765500ff4f50010ecaa00029e60021d954056e1fbaee8b2a800087f87594655000f8b8cab98caa001e8f21276195400062f3b4e632a8000c5e765cc6550001a3ae8b98caa02b28f612631954055d3cc04c632a80a5a7980984655000f0fd0e190caa00021f61c32195403f51f4206432a8000a3d840c865500014ed02190caa00029d60432195403ed3d4006432a8000a79800c865500fb4f501188caa00029e602311954003c3f4386232a800087d870c465500fd47d08188caa00028f6103119540005374106232a8000a6d820c465500fb4f500188caa00029e60031195403ed3d4044232a8000a7980884655000f0fd0e108caa00021f61c21195403f51f4204232a8000a3d8408465500014bd06108caa00029760c21195403ed3d4004232a8000a798008465500ff878edb2aa8a001f0f1d865551400058ec18caaa2800087e87d9563500010fd0e32ac6a000e1f21576d4d4000c5e432e9a9a8007a3c8655353500070fd0fb2aa6a001e8f2195454d4054e1eba0cb312800087e87d9562500010fd0e32ac4a02ab1edc0655894000477c3ac4312800b87c855db52500031790cba6a4a002e2f21276949404061f3a6cb29280018bc865d2525000187ecaba4a4a01eb0f19574949400249fc3aa92928007a3c865525
  | 6 => 0x46ec1eecaa242008df835d954484071b906bb2a8908023ee01765512100c7c402ecaa2420487e87d95544840f17d0fb22a8908021fe1570d8d2103c3e42ae1b1a42008bf845c3634840917908b86c690802a7a1265d8d210054ec24cbb1a4200a5e8599363484014bb0b326c6908b771dcb71d8d210054f424ebb1a4200a9d849d763484014bd0b3a6c6908029761674d8d2100567410e9b1a422dacd821d36348401c3ea92a6c69080237a1c54d8d210046ec38a9b1a422d8de87d0b63484011bb0fa16c69080297a1742d8d210052ec2e85b1a4200a5f855c363484014b90ab86c690802a7e1170d8d210054e422e1b1a422dad6811c363484015ab02386c69080237a1c50d8d210046ec38a1b1a4200a9e84143634840153b08286c690802b3a0850d8d2100566c10a1b1a422dad68114363484015ab02286c69080237a1c40d8d210046ec3881b1a4200a5e8510363484014bb0a206c690802b3a0840d8d2100566c1081b1a422dad68110363484015ab02206c69080237a1c20d8d210d46ec3841b1a4200a5e8508363484014bb0a106c690802a7a1020d8d210054ec2041b1a422dad68108363484011bb0f328c690802a7a126518d210054ec24ca31a42008df8759463484011bb0f320c69080297a166418d210052ec2cc831a42008df8759063484015ab03300c69080e1fa1676d4d2101d2e41acba9a42008df835d953484070f90eb2aa69081e37a1f6354d210046fc1aeca1a42008f7815d943484071790eb22869081237a1f6350d210064e31ae92924200c9e74d8e524840193ae9b1ca4908031718e75909210062e31aeb2124200c5e75d8e42484018baebb1c84908033518f71509210059742ee8a124200aae86d514248401b8c63b9a84908b7331db635092141e663b0c6a124200e8c6418d42484015590ca1a8490802b3219438c92116e6a38ec699242028ec865d13248407998edb9a64908b7711c7734c92116e663b6c6992421acd476d8d31484015a90ca1a629080f351d9434c521005d2c20e498a4283dc7731c9314840178b072126290803e150d424c521014ea43a6498a420bcd4764c93148417b88e4992629080af121d324c521156e243a6498a4202bc6864c931484057890c992629080fb1219324c52101f63bb26498a421adc4764c93148407d88ec9926290802f1e11324c521005e2c226498a4200dc532dc13148417b8c64b9e429082f71dcd32c852141e6a388c7b0242018f4815cf604845b1b90db9ac09080237a1f63581210062fbaec6b024200c5c75d8d604840193ee9b1ac090803271d363581210046f438c6b024200c5f7518d60484018b8ea31ac09080327dd063581210064e3a0c6b02420487d85dc964d40071790eb2287a81fa8fe195450f500246e43ac6a1ea000e1d5458d43d401795e40ba4c5a
  | 7 => 0x7c865d54354401878ecaa286a88023be1d62189510043ec3ea8312a204c3e74d5062544890ff0eaa0c4a88021f61e50189510051ec20a0312a200a6d8214062544890f90cba6a4a89130f19174d49510143e432eb212a20287c865d54254479878c8baa84a888e5e201755095105d57416c8a12a20287c865d632544018baebb1c64a880a1f219754c95111c3ec3ea9b02a27e87f875536054409878e8aa6c0a888e1f61f52d81510043fc3aa5b02a200a3d8414365504014db04286caa08029d60450d954158e1fbaee8b2a820087f8759465504010ff0ab86c6a081e1f21570d8d4101c5e422e1b1a820387e859db53504070f90eb2aa6a080e2f21d6550d410070eb2aa6a1a8203c9e7350f62504011df0eb10c4a08021fe15701894103c3e42ae0312820b87c855db52504051790cba4a4a080a2f219741494105c7a432e229282028bc865d2325040933f0ea1c64a080ea7219438c9410145e432e89928200a3d84141654c4014db04282ca988021fe1d65195310243f42cedaa262018fa809d9544c4011f3013b2a8988121f21d65551310251e422caaa262048dc87595434c401c3acaaa28698a0e37a1b7250d31014ea40ee4a1a62029d687dc5434c4011df0eb10c498ac2b3e0d62189310062f21aea312620bcaf215d0624c40195a42ba0c498803175d543189310264f3a2863126283ad48150c624c4019b486b80c4988033650d701893105e6d992e0312620bcd9325c0624c4019b462b80c498803360c5701893105e7910ae0312620bcf1215c0624c4170fd0b3b6a49880a37219739493105c7a432e3292620b87c87595524c4174d904b2aa49880a37219731493105c7a432e229262028dc865ce424c4171e90cb8c849881e1fa1476509310043ec28eca12620b8bc87591424c41755904b22849880a37219744c931014ea40ae8992620787f875d7604c4018bc86baec098803175d543d81310264f3a287b02625dad48150f604c50187ce9286cb908028f61050d97213f61f3a0a1b2e4200a6d8214365c84170fd0f2a2cb908030fdd254597210052ec18a8b2e420487c855db54c84010fb0fb2ea9908128fa1365d532105c5fc3ac9aa64200a3f8559354c84011f700bb2a9908063e20176553210243f43ecaaa64204a3e84d9554c84010ff0ab86c79081e1f21570d8f2105c3e43acaa9e42028ee82dd943c84171790eb22879081237a1f6350f2116e6a38ec6a1e420baae86d5142c84175590ca1a8590802e9e054350b2116de240a8719642029e4815d132c840f0fd0fbaac1908028f61050d952100536c10a1b2a4200a7581143654840187ecaba4ca9081f0f195749952101c6f43ee6b2a420087f8759465484071bd0fb9ac890803351cf71591210243e42aedaa242008df835db54484071b906bb6a89080e37a0f76551210
  | 8 => 0xea382caa10021fe1d65195420053c402ca32a843c93d87d97545087947b0fb2ea8a10030f61f65d51421c4d7434e5aa2840bcae869cb545080135b03396a8a10026b60272d51420043fc2ae1b1a840787c855c363508070fd0b3b6a6a102e2f61276d4d423d61faa4eda9a844aa788059753508070f90eb2aa6a111e9e2016554d4202477436e4a9a8400d2f541c953508071790eb2a86a1116ae2016550d42024ce43aa6a1a8400e1d6554d435080171904a9a86a102e6ba1f7250d42174d7430e4a1a840bcae861c9435080135b0239286a10026b6007250d4205c9e42ae9a92843cc3e74596525087b4f100b2ca4a102e6b20974949421e49ec3ea92928438c3e76d525250889a5ce9a94a4a10030fd9774549420043fc3aca2928435a7880594525081787ec53ac84a11134bd8a759094205e9790ceb212840bd2f209d64250817b4e42b8c84a102f6ac8170909420047dc02ebb0a84018f8805d76150801d2a8798ec2a10021fe1570d854203c3e42ae1b0a84008f7815cf60508051e902b9ec0a100237e0d71d814201c6e41ae3b028400c78601d5605090187ce9286cb190028f61050d96323f61f3a0a1b2c6400a6d82143658c8170fd0f2a2cb190030fdd254596320052ec1ca8b2c6400a5d83151658c8090f90abb6a9190021f61f65d52320251f426cbaa4640b8bf87593548c80147f0ab26a9190023ee01765523200c7c402ecaa4640487e87d95548c80947d09b2aa91901237a1f6550e320070f2a2caa1c6400e1f65551438c8631bb0db92871926b27dd94350a3203c3f43eeab046400c5e43dd5608c8018beeaa1ac119013271d143582320051ec20a1b2a6400a5d83143654c8014db04286ca990021fe1d65195320147b43ee2b226400cd7731c5644c8090f90abb6a8990023de0576551320147a40aecaa264008fb805d9544c8031f100bb2a8990121fa1f65551320251f426caaa2640bd8c325d2524c817a9864bac849901237e1d648c93216d6a40ac919264038dc865c6324c85b9a8c2b8c649902f71c85718c9320043fc2ae1b0a640787c855c3614c8031b906b8ec09900e37a0f72593510046ec1ee4b26a20387d85dc163d44050fd0bbb287a880e2f21d6450f510246e43ac6a1ea200e1d5458d43d4401c3ac8a9a87a882f2bc857498b510065690ae9316a20bcaf205d262d44010ff0eaa4c5a88130f9d15498b514061f3a4a1316a23c87d86dd152d447987cc9ba2a5a881f0f9d56490b510143f42eeca16a20b8bd84dd942d44f587ea9bb285a889a5e2017550b510143f42eec996a22687c8755160d444d0f90ea92c1a880237e0d72d915101c6e41ae5b22a204a3e86d915454489878c9b92a8a88130f1d154d8d5101c3e42ae1b1aa2008bf845c3635440917908b86c6a88028f61050d8d5100536c10a1b1aa2028
  | 9 => 0x7058e520051ec20a0b1ca400a6d821416394817958e4b22a7290032b5937254e5205c5e43ac8a1ca404a3f86551439480187eecaa287291121fe1974d4a522261f322e9a94a400a3d8414161948014db04282c3290030fdd664582523f61e3acc8b04a400e3a505916094817d5640b22c1290f61fa1f54582523f43e43aa8b04a404c3e74551609487b0fd0fa92c1290f69ea0352582521e61fbaec8aa2a49dd2c54dc9545487927d093b6a6a90f21f61f64d4d521e61f3a6c9a9aa44a87c865c353548010fd0db82a6a901237a1f6350d5203cae43aa6a1aa403a5c8654d435480f0fb0fb24a4a90f30f9d3649495203c3e432e1292a43dc78605c25254817ad640b84a4a900a1f21570d85520046fc1ae3b02a4038dc835c760548171790eb2286291128fe195450c5205c6e43ac6a18a400e1d5458d43148790fb0dba2a4290f30f99374548520261e3a2a8b08a40287d85dc1611486b0f90eaa2c0290d61f21d52580521ad3c402a4b00a40be6b2054960148174dd0530ccb2102e9ba0a609964203c3f4386332c840087d870c6659088947d0818ccb210028f610319964205d374106332c8400a6d820c665908014f50018ccb210029e600319964203c3f43e6132c840087d87cc2659088947d09984cb210028f61330996420053b40c6132c8400a75818c2659080f0fd0f884cb210021f61f10996420052f41c2132c8400a5d83842659080147b0829acb210029ea0251596420053cc04a2b2c840ba6e82941659080147b08282cb2100297a0c50596420052ec18a0b2c840ba6e8214165908014ed02282cb210029d604505964205d37414c2b2c840ba6e8298165908174d904b9acb210f28fa1073596420051ec20e6b2c840ba6e829c565908014db0538acb210029ea0271596420053cc04e2b2c840087e870c565908010fb0e18acb210f28fa1031596420051ec2062b2c840ba6e820c565908014db0418acb210029ea0031596420053cc0062b2c840ba6e829c165908014db05382cb210f28fa1070596420051ec20e0b2c8400a5e831c165908014bb06382cb2102e9ba08705964200536c10e0b2c8400a76811c165908014eb02382cb210021fa1f30596420043ec3e60b2c843ca3e84cc1659080147b09982cb2102e9ba0a305964200536c1460b2c8400a76818c165908014eb03182cb2102e9ba08305964200536c1060b2c840087e87c4165908010fb0f882cb2100297a0e10596420052ec1c20b2c840ba6e8284165908014db05082cb2102e9ba08105964200536c1020b2c840787e85dc163908010fb0bb82c72102e3b2097654e4205c3e43acaa9c8400c6d65dc9539080f0fd0bb82c3210021f617705864205f35902cab048440a3e855d3655080147b09286caa10028f61050d954200536c10a1b2a84018fa87dc165508018f6
  | 10 => 0xb06a60bcac625d26254c0195ae9b14c4a98023be1d62189530043ec3ea8312a604c3e74d506254c890ff0eaa0c4a98021f61e50189530051ec20a0312a600a6d821406254c0147b08286c2a98029b60850d855323c3ec3ea9b02a604c3e74d536054cfd0ff0eaa6c0a98028f61050d95430052ec18a1b2a8600a6d821436550d6587eebba2caa18021fe1d651954301ccf41ee4aa28603a9c865515350c09938ecaa2a6a181f871955454d4301d8e43aa8a9a8604d1c875515350c0763d0caa2a6a180ec72195454d4303f0e432a8a9a8607e1f765515350c09a3cecaa2a6a1813471d95454d4303f0e3b2a8a9a8600b1f825515350c0163f02aa2a6a1a7ec7a015454d434fd8e402a8a9a860499e841c95350c01a3aa8392a6a1803475537154d4301caec2ee0a9a860499e84dc15350c01a3aa9b82a6a18023be1d62189430043fc2ae0312860787c855c06250c010ff0ab86c2a181e1f21570d854303e2f3aaa7b028603c9d7454f6050c01c3aa8a9ec0a19121f21d6454f5223c3ec36e0a9ea40b87c855d943d48071790eb2287a90123721d6350f5203cae43aa6a1ea400e1d6454d43d48071bd07b8ac1a90023760f715835205d57414c1324a400a3f869426494801c74c1284c9290024f61c50992520051ec30a1324a400b2d82142649481755d05202c929002ce201755925205d57414c0b24a480c3f76941649480127b0e282c9290028f618505925200596c10a0b24a400abb805d5649480157100baac9291028fa1473592520051ec28e6b24a440a3e851c5649480147b0a38ac929002a7a0c71592520054ec18e2b24a40baae821c5649488155b0438ac929002aea0071592520055cc00e2b24a40baae82945649480155b0528ac929002aea0251592520055cc04a2b24a4008be870c5649480117b0e18ac9291ea8fa1431592520051ec2862b24a40baae820c5649480155b0418ac929002aea0031592520055cc0062b24a40baae829c1649480155b05382c9290028fe1570592522051f428e0b24a400a3d851c1649480153d06382c929002a760c705925205d57410e0b24a440aad821c1649480156d02382c929002ad604705925205d57414a0b24a400aad82941649480117d0f982c9290022f61f30592523d51f42e60b24a400a3d85cc1649481755d05182c929002ab60a30592520055b40c60b24a400ab5818c1649481755d04182c929002ab60830592523d51f42e20b24a400a3d85c41649480153d07082c929002a760e105925205d5741420b24a400aad82841649481755d04082c929002ab60810592521e61f322edaa4a404a3f86593549480187aecb26a9290f30f99172d525200656b26e4aa4a404a3f86591549488187eecb22a9291130f99372552524ee97ba6e4aa4a404c3e74551639480917d09b82c7290022f613
  | 11 => 0xab071a251d68a194b0000000398a72420609dc1701ec0578b7ae82ba0120c69222510ba9c70282fa8ba09f8e0a7627204a03783b07213500018b29ba190000000002de94980000020013e00401c84baac1d304e0c48001c6a1d8952a805c96e00a8d89d2aff8e30ad007a278c1af921380000000992108a2092bf09e25ea280bd00000000000020600000024e94e0202f69b896b2a580d17880000013c0001f20e88000c59372fb0001db8b08a315d0000000000818001180002e60f19efac3266a7f97c8000000fb80000000029a8000be0000000001850000008000000080180a0000080000b0000100500b020000020040020040c81500a0000080200a03800015008000010070020200483c002008040020060640581d0100080480300c01001800000000010000040540200900a02c0000d00a01c018000020000600000c0000000400c01400000002000018030200000500501803c008180000000083501c0040500100000000800018008018070020340002d00c01c0700001e004018010000200080f02000c030010020000204b000010000020140000100b0020280b00003001802800006008000060020140000001c0040600400000000004000008058040080280180202c0080200a0060000300b008004000040020000680400600c0b000018000000070020440280700001c0380a002000000110100000080d00402c02009024008040000080000a80e00201c0400005200001023000044018010020140200100002800002000000000240000340380b0240000380600e0040680602e0080000100c1280080101c0000000000e020010020020840101000e0080180702c05007804004068018030000000280403c0180200501c0080700000200c00802022004008010020380003c0160100a003002000030020000240080e04208c04003006000000040000080280100c010020000040080180800000400000000000030100000140000b000004048040d60100080201c000008000080080100700600000002002008008010560180101d00e028000110000040080c00000004005014000020050000d80180300600001801004000008040140240101902803000001012014000000000000000e00c0a00000101a000018020200040080000a000018000100040500a0100440280400600c0580a00001c058030120040000700000407802008010040020000000300300001c0000200200000008000004078220300000580a0020180200102e040078030000c8020000040300181e1fa177058f5403c3e42ae1316a80787e85dc161d51010ff0ab86c6aa2cf1b5d7629895400477c3ac4312a88087f855c062551010ff0ab86c2aa02f2bc817498b530043fc3aa9316a604c3e7455262d4d0187ce9284c5a98130f1d154587532543e43aa8
  | 12 => 0x65a3f80000000000012385e2fc05a1c92bb150197a169ac00000012a00019c8002db0000001a0a8026211100000000018000015f0002530a29019091fe976a4fa8d21597217d04381e0cd10426a84c2830650000002360530a08001398001a317702f80012b87288e1358988da212a322da8000000000f51a12bc1011078dc0000bcaf986e21c87fa4e1cb06b8588000001b680e80015a02200000024000025b8002eb0002d38001f517a9c62670000000002879000002ca8421e0a288001a700023e890ab6af528200000000000026b82ca6f841000000000000000023a0a9a5a681240ef24c2ce00005c04d27128f93a1230001d019280026903f084ad980b0002da0842161af255a74929af48cc0001ca000259187a1b8d60000000f900020e0ec0000700df1adaa68edac120280014a8001492b10a504ea9d24718c21a8000000000001b78001160f400000020b98d0a59f602a1ad2551c59599c08000540118000001be2a287e0000000000000580000000000002d60001541fd80000011200009600000010480007700000000017e957ad780000017fa409c8a7a0339c289a927156a0585590085b84d9531902518969762ee0059ac90c0dd00001f19c1d3afb8890000de8000670000001fc99a93f19f1470a01a68000179d40002cf8871af88121421e0fc19d8cf99692193102e8000520f68b100f8000001369bb00015820c0002c20002d59f90000ce9daae3000211996173a678061f81b51b00000002352262e5a18a940000000779e12780d79f02ab000233948068286239ab800022c2ed04093884900021a2fa250a3a000155a910001e61ed1e28000002a486ca870ae98aaa900023f11086000016600015e16412480022908d9ed94d8002900711030002a1800000000236aea2d40000000000001780a10000938000001ee82c00000000027e2980bc111a7a9dd8001d206699a03daf8914a4d94a02883196fab61610a804f230ad30f000206d81d9f725782e0d48b3800000116800006838264953a32a2e17b80e0001410002588d4061912821ae718927f0000000000182828001a81080170f3aa702d92c05082602687c8002978452808000db81b0000c393316d1511d498f9361e485aa469df0fea050dc8000b90002bda818918e980000000027b2ef152954a738002cc91a0eb2c180000010619828daf7231a48aa41588001058c207d8e79a511500016b8000000002a62240000251b701306d28b04489999b03618e0002232be252a482ad800221ad8a068698d393b9461b926d8000f71848e108380015d9941e59ecab210a2fd0000002eda020150c78000df95b0739deaf282724a9b491f0ecafe1c110a80a18e8000c0ac7927a928001bd08f875a1513b0d3063a2b035a6d300175a29a9f82f05e81120b2af0bb09e967115a44
  | 13 => 0x38320310ad821102254092940270a8aa9919211d9ee0c8a958f804b0001841909d5a6ea0095e8000002cb1fd23894e8c724522fa448640780538000000000000000001c4ad21fba72ad29261bfa131eb87519ba3b80011324a12d88c13087b800000000000268a7191d0001f10000852210002dd1650142e6a881392fd8259c803508c8d283419880027593d9e311aaa09d199114b92501d0d1269946970a8119f9ab2428f590c931a9c0001e192d0742271f68000001ef0000000e38000000002f609113e8ca90d2890000000000e180011880003aa778000001b3a100002dba650000000730000000001288bb8000000000c00e807980005d86f0fe0f61b80002458000590002bf96a10fab500005f8ce2df9698001c01f996200008889b8300001190f11731931f2964ab325e12c8000000002e016308602d2600b808ea8a06b1958ddab78000948d929a2dc0002c70002c42520af0000be8299680001d615c28f0002042dc845934971a370cc80021f9e69889ea9cf8000da9e40572b409d30225a8e21bb8001a6051a7c80baa786600026606c0402f30e481e8001a22238549818ea00023917da198000001df8000002460fa91b1a90348f28000b5ac69e89141ae86f8eb8000001f59bf1ae0002d4a14a5da0a05b1db0c2ac483896c1e714c1fa0001859ba04315622ea3d84a98caca0a922a8a20000000002f580000009f2e9a030000cb0002b48b28002cba939e200001600000000005f0002aba7ea111f09fe2ff13f9a18d524306eace8f30611420488822c08332bd17406900c800078a9181f8001fc15aa500002d81a48001792b930100016687b0002fe80c12f9b327daf82fc9f78b70050f088a90dab39c224cac518b9711880ff261089aa3af225c24f05d10e9198048100002d10000000688000000000001ff0000e900000020d00025c8550ea80016f17480000029880029d89c0002a880020da998a397787c2220000fca740002d7000000000000000294a9f2569972e880007a03706580025b002aa98d1a59a380090bd8aa2e796a9e017f00008b9cd80020886a90b80021ea5613caac960a90a1d2582840468001b100022029e93280000000026323b0002300001551ba9be8001eb00028c1099f480000001a8002f78e28808001a411ba03836a478000002f18002aa1b6003ac02e10630000921d112082b8000002ea8001431d080020c9ff8e62310001292de0ca1b1948905296a43aec8190002792ec20100007e95fa2a1440a79f3217a86ad003094580000000021082780019980000023c0000002f02dd85000027d0002d080022d01a0ee23ca4181c00022d8d080129c9bc03c98f01b99e8d68001d894500000027996e8ee97a0bfaa503ea0700000000025fa83a04aad0000c514492ea6416926a0b888800025a0f21c18941
  | 14 => 0x2b595c9678002770070000002018fd1aaa0f09b1cb832ad91301d51b58000001bdadf0cf02aa2580002b2c81268978470970a9a208b98292549b2a3d18682497b18392a8198e511e03a0001898001c98000128002079100000001e98003008000b32b0ac38000002b02e21c391eabea4103c0930001d715b8002ae800161800087a4d1a88000e00fb1e92f40d58002c9a1c00005100016291792f23321b2bb8002658000002eb8aaa700b20000000560000478002f09ce00014f26e1521a9acf00017e0000002c6151a89a269860442a011c8791039228d007a9cc04faee9dca8e8188f991f8c30f489927329709816cabc8599aba751e508d15925d2d18c422c89d87d16dacda9516018306a28ca2f04c9a7acc1870b18089139a023e074906ab8ac58b519d1ea1948d2082acd143a8e09a14d10e039052a249d81339990ff9822e091c29e1dd14f9508018000628a49faa4b8b6824085ae526c0000ab8003018001e39378800000000c626f12b00028592e0c98000000001918d993a8000000000c819e0002c280022ba228f880000009c8000a40e58001259d9a769e80f78569fb0900498002960000cba78a7c03d2d69b08001750b60008002b18002498000af8a69b40460d80ae1c42e900026cae3a849f428ba340000001d90e403f800193902a1813d1638001342a10000000000000c90001aa20f9cc80000da6b00024900021f000020aba9478001b21072d50e6941800000067870a358de1320002e49688000000000ac8000001de0000b48418bf1a38ed2172a30001380760002e18649f89828158c10830db1cf000000010800076a618001c79da0000620000000000002570000149f38000000000000002f38002a21428000001a2a122ae00000028890b0001282ef8001b98002c9108a080d70001bcac880000008f18a0002608ef9c302315727ba348b003e00f0229cd2e40000480002e2a4b00817c0000000000000fd8169170000959d78e7180aaa8ac1ceab725f0869409c5013ab98cd88b179a379951f1a3aa099812b28b42afa922628429e787f18d8a88a6000120172a0e90f29b0fa14caf11caa9303ba85003263a5
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x89ba54ed160f46000000000e9c00e40006a00fb65478380480000c600002e000d01862b480a660800900000a8643430b2ea441b7048a165614c8e224ca8008013215e68101800410001063c0082800002542460122447e61541c95350cfd11f985537054d430060edd8805d5649493b82f7660850592524fd862416554d43508014719118075581423f40fe5d84143658c80182e7460850d963202507a5f65551438c80941c975955450d3100534245435c0624c401499940c5701893100532648315c0624c4fd03f9761050d97210060b9d18214365c84016849650d424c521014b1259844c9314840f81c7660c65551403f40f26276552525000105d981cc654854000525650315c4624c0014959420d711893000531648835c4624c0014c59290d7118930005076547650d424c00181f7460e74d95200040fe61741d3654800106d97a0b431952000568646305d2524800158993841749492000558646305d642480015499384175909200050b648641d56444001531941437154d100055864850dc5534400153194141719491000558648505c652440015319414375505100055864850dd541440015319414375485100055864850dd521440012c593219424851005d3125d634c92144001171980c475501100054c650311d54044001561920c4755011011d4c25d545454044001950831d52150110007481d542485404401f3509854d514c11011d5425d53545304401f3909850d414c11007cf0261324853044001171980c475481100054c650311d52044001561920c4754811011d5825d525452044001950831d52148110
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x2000140cd1eec402eab24a4008546a4831d52150110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x4
  | 4 => 0x5
  | 5 => 0x94c
  | 6 => 0x94d
  | 7 => 0x6
  | 8 => 0x98a
  | 9 => 0x98c
  | 10 => 0x98d
  | 11 => 0x3
  | 12 => 0x150a
  | 13 => 0x150c
  | 14 => 0x150d
  | 15 => 0x9ca
  | 16 => 0x9cd
  | 17 => 0xa0a
  | 18 => 0xa0c
  | 19 => 0xa4a
  | 20 => 0xa4c
  | 21 => 0xa4d
  | 22 => 0x198a
  | 23 => 0x198c
  | 24 => 0x198d
  | 25 => 0xb09
  | 26 => 0xb0c
  | 27 => 0xb0d
  | 28 => 0x1549
  | 29 => 0x154c
  | 30 => 0x154d
  | 31 => 0xb49
  | 32 => 0xb4d
  | 33 => 0xb89
  | 34 => 0xb8c
  | 35 => 0xbc9
  | 36 => 0xbcc
  | 37 => 0xbcd
  | 38 => 0x19c9
  | 39 => 0x19cc
  | 40 => 0x19cd
  | 41 => 0xcc9
  | 42 => 0xcca
  | 43 => 0xccd
  | 44 => 0x15c9
  | 45 => 0x15ca
  | 46 => 0x15cd
  | 47 => 0xd09
  | 48 => 0xd0a
  | 49 => 0xd0c
  | 50 => 0x1609
  | 51 => 0x160a
  | 52 => 0x160c
  | 53 => 0x449
  | 54 => 0x44a
  | 55 => 0x44c
  | 56 => 0x44d
  | 57 => 0xd49
  | 58 => 0xd4a
  | 59 => 0xd4c
  | 60 => 0xd4d
  | 61 => 0x1649
  | 62 => 0x164a
  | 63 => 0x164c
  | 64 => 0x164d
  | 65 => 0x1a09
  | 66 => 0x1a0a
  | 67 => 0x1a0c
  | 68 => 0x1a0d
  | 69 => 0xe89
  | 70 => 0xe8a
  | 71 => 0xec9
  | 72 => 0xeca
  | 73 => 0xecd
  | 74 => 0x1a49
  | 75 => 0x1a4a
  | 76 => 0x1a4d
  | 77 => 0x1049
  | 78 => 0x104a
  | 79 => 0x104c
  | 80 => 0x1a89
  | 81 => 0x1a8a
  | 82 => 0x1a8c
  | 83 => 0x98954
  | 84 => 0x94e
  | 85 => 0xa0954
  | 86 => 0x198954
  | 87 => 0x209
  | 88 => 0x8a
  | 89 => 0x1409
  | 90 => 0x128a
  | 91 => 0x16c9
  | 92 => 0x1449
  | 93 => 0x168a
  | 94 => 0x12ca
  | 95 => 0x1849
  | 96 => 0x1489
  | 97 => 0x180a
  | 98 => 0x130a
  | 99 => 0x14c9
  | 100 => 0x134a
  | 101 => 0x9c992
  | 102 => 0x3c9
  | 103 => 0x128d
  | 104 => 0x409
  | 105 => 0xd4995
  | 106 => 0x1709
  | 107 => 0x1889
  | 108 => 0x8d
  | 109 => 0xd5515
  | 110 => 0x138c
  | 111 => 0x124c
  | 112 => 0x8c
  | 113 => 0x128c
  | 114 => 0x18c9
  | 115 => 0x1789
  | 116 => 0x180c
  | 117 => 0x130c
  | 118 => 0x17c9
  | 119 => 0x134c
  | 120 => 0x138d
  | 121 => 0x124d
  | 122 => 0xd0e
  | 123 => 0x168d
  | 124 => 0x12cd
  | 125 => 0x749
  | 126 => 0x14d
  | 127 => 0x1949
  | 128 => 0x134d
  | 129 => 0x124e
  | 130 => 0x140c
  | 131 => 0x3ca
  | 132 => 0x140d
  | 133 => 0x40a
  | 134 => 0x170a
  | 135 => 0x188a
  | 136 => 0x20c
  | 137 => 0x20d
  | 138 => 0xe8b51
  | 139 => 0x18ca
  | 140 => 0x178a
  | 141 => 0x184c
  | 142 => 0x148c
  | 143 => 0x17ca
  | 144 => 0x14cc
  | 145 => 0x16cd
  | 146 => 0x144d
  | 147 => 0x194a
  | 148 => 0x14cd
  | 149 => 0x5ca
  | 150 => 0x74a
  | 151 => 0x2cc
  | 152 => 0x2cd
  | 153 => 0x40c
  | 154 => 0x188c
  | 155 => 0xe95d1
  | 156 => 0x170d
  | 157 => 0x188e
  | 158 => 0x3cd
  | 159 => 0xece91
  | 160 => 0x194c
  | 161 => 0x17cd
  | 162 => 0x74c
  | 163 => 0x5cd
  | 164 => 0x249
  | 165 => 0x14955
  | 166 => 0x98d55
  | 167 => 0x150d55
  | 168 => 0x75491
  | 169 => 0x74d11
  | 170 => 0x15515
  | 171 => 0x149d5
  | 172 => 0x74e91
  | 173 => 0x1a9951
  | 174 => 0x194e91
  | 175 => 0x45651
  | 176 => 0x3d5d2
  | 177 => 0x1a9952
  | 178 => 0x1a9954
  | 179 => 0x1a0d55
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 2251
  | 6 => 6486
  | 5 => 1541
  | 4 => 58
  | 3 => 2
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
  | 8 => packedAt gbK8 (1700+((h/20+packedAt gbK8 (1560+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (93037+((h/750+packedAt gbK7 (83287+(h % 750)*13) 13) % 5261)*13) 13
  | 6 => packedAt gbK6 (341596+((h/2162+packedAt gbK6 (311328+(h % 2162)*14) 14) % 12533)*14) 14
  | 5 => packedAt gbK5 (96562+((h/513+packedAt gbK5 (90919+(h % 513)*11) 11) % 2035)*12) 12
  | 4 => packedAt gbK4 (4193+((h/19+packedAt gbK4 (4060+(h % 19)*7) 7) % 77)*7) 7
  | 3 => packedAt gbK3 (164+((h/1+packedAt gbK3 (162+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfe3ffe70e1f8fc0ff1c0e0707c8219f1b3993
  | 1 => 0xf0fc70180fe1f1ff03e00ffff810c66c25c1fc
  | 2 => 0xff801ff001fe0003fff007ffe71870c60e1f
  | 3 => 0xff00001ffffe000003fffff800381f80f80fe0
  | 4 => 0x1ffffffffffc000000003fe000fff000
  | 5 => 0xffffffe00000000000000000003fffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x12090c1060282421b04223111800085091991
  | 1 => 0x1064214002209092092004925080422c0140b4
  | 2 => 0x89020a1001240420494004a603085046020a
  | 3 => 0xaa000495ad5400085292a96001381580b80d40
  | 4 => 0x8800081ec999492ce000c040223da000f6a000
  | 5 => 0xccd24f008110003080030180c43eff7a000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfefefeeafeeefce0fefefeeafeeefce0fefefeeafeeefce0fefefeeafeeefce0fefefeeafeeefce0fefefeeafeeefce0fefefeeafeeefce0fefefeeafeeefce0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36398
namespace PEqualNP.Outside.L_meta_36398
open PEqualNP.Outside.L_meta_36398.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 10 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_32 : Interval s0Atlas 3 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 60 := (concat bs0_3_0 bs0_3_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_32 : Interval s0Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_64 : Interval s0Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_96 : Interval s0Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_128 : Interval s0Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_160 : Interval s0Atlas 4 160 5 := block_range (n:=5) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 165 := (concat (concat bs0_4_0 (concat bs0_4_32 bs0_4_64)) (concat bs0_4_96 (concat bs0_4_128 bs0_4_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 50 := (concat bs0_5_0 bs0_5_32)
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
theorem bs1_3_0 : Interval s1Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 8 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_32 : Interval s1Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_64 : Interval s1Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 92 := (concat bs1_4_0 (concat bs1_4_32 bs1_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_32 : Interval s1Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 44 := (concat bs1_5_0 bs1_5_32)
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
theorem bs3_3_0 : Interval s3Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 6 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_32 : Interval s3Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_64 : Interval s3Atlas 4 64 2 := block_range (n:=2) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 66 := (concat bs3_4_0 (concat bs3_4_32 bs3_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 10 := block_range (n:=10) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 42 := (concat bs3_5_0 bs3_5_32)
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
theorem bs4_2_0 : Interval s4Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 5 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 25 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_32 : Interval s4Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_64 : Interval s4Atlas 4 64 27 := block_range (n:=27) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 91 := (concat bs4_4_0 (concat bs4_4_32 bs4_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 44 := (concat bs4_5_0 bs4_5_32)
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
theorem bs5_4_0 : Interval s5Atlas 4 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 4 := bs5_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 1 := bs5_5_0
theorem alls5 : ∀ k ≤ 5, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 2 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 26 := block_range (n:=26) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 58 := (concat bgb_4_0 bgb_4_32)
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
theorem bgb_5_1536 : Interval gbAtlas 5 1536 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1541 := (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat bgb_5_288 (concat bgb_5_320 bgb_5_352)))) (concat (concat (concat bgb_5_384 (concat bgb_5_416 bgb_5_448)) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))) (concat (concat bgb_5_576 (concat bgb_5_608 bgb_5_640)) (concat bgb_5_672 (concat bgb_5_704 bgb_5_736))))) (concat (concat (concat (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928))) (concat (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)))) (concat (concat (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)) (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312))) (concat (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)) (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 bgb_5_1536))))))
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
theorem bgb_6_6464 : Interval gbAtlas 6 6464 22 := block_range (n:=22) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 6486 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat bgb_6_288 (concat bgb_6_320 bgb_6_352)))) (concat (concat (concat bgb_6_384 (concat bgb_6_416 bgb_6_448)) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))) (concat (concat bgb_6_576 (concat bgb_6_608 bgb_6_640)) (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 bgb_6_768))))) (concat (concat (concat (concat bgb_6_800 (concat bgb_6_832 bgb_6_864)) (concat bgb_6_896 (concat bgb_6_928 bgb_6_960))) (concat (concat bgb_6_992 (concat bgb_6_1024 bgb_6_1056)) (concat bgb_6_1088 (concat bgb_6_1120 bgb_6_1152)))) (concat (concat (concat bgb_6_1184 (concat bgb_6_1216 bgb_6_1248)) (concat bgb_6_1280 (concat bgb_6_1312 bgb_6_1344))) (concat (concat bgb_6_1376 (concat bgb_6_1408 bgb_6_1440)) (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 bgb_6_1568)))))) (concat (concat (concat (concat (concat bgb_6_1600 (concat bgb_6_1632 bgb_6_1664)) (concat bgb_6_1696 (concat bgb_6_1728 bgb_6_1760))) (concat (concat bgb_6_1792 (concat bgb_6_1824 bgb_6_1856)) (concat bgb_6_1888 (concat bgb_6_1920 bgb_6_1952)))) (concat (concat (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048)) (concat bgb_6_2080 (concat bgb_6_2112 bgb_6_2144))) (concat (concat bgb_6_2176 (concat bgb_6_2208 bgb_6_2240)) (concat (concat bgb_6_2272 bgb_6_2304) (concat bgb_6_2336 bgb_6_2368))))) (concat (concat (concat (concat bgb_6_2400 (concat bgb_6_2432 bgb_6_2464)) (concat bgb_6_2496 (concat bgb_6_2528 bgb_6_2560))) (concat (concat bgb_6_2592 (concat bgb_6_2624 bgb_6_2656)) (concat (concat bgb_6_2688 bgb_6_2720) (concat bgb_6_2752 bgb_6_2784)))) (concat (concat (concat bgb_6_2816 (concat bgb_6_2848 bgb_6_2880)) (concat bgb_6_2912 (concat bgb_6_2944 bgb_6_2976))) (concat (concat bgb_6_3008 (concat bgb_6_3040 bgb_6_3072)) (concat (concat bgb_6_3104 bgb_6_3136) (concat bgb_6_3168 bgb_6_3200))))))) (concat (concat (concat (concat (concat (concat bgb_6_3232 (concat bgb_6_3264 bgb_6_3296)) (concat bgb_6_3328 (concat bgb_6_3360 bgb_6_3392))) (concat (concat bgb_6_3424 (concat bgb_6_3456 bgb_6_3488)) (concat bgb_6_3520 (concat bgb_6_3552 bgb_6_3584)))) (concat (concat (concat bgb_6_3616 (concat bgb_6_3648 bgb_6_3680)) (concat bgb_6_3712 (concat bgb_6_3744 bgb_6_3776))) (concat (concat bgb_6_3808 (concat bgb_6_3840 bgb_6_3872)) (concat (concat bgb_6_3904 bgb_6_3936) (concat bgb_6_3968 bgb_6_4000))))) (concat (concat (concat (concat bgb_6_4032 (concat bgb_6_4064 bgb_6_4096)) (concat bgb_6_4128 (concat bgb_6_4160 bgb_6_4192))) (concat (concat bgb_6_4224 (concat bgb_6_4256 bgb_6_4288)) (concat (concat bgb_6_4320 bgb_6_4352) (concat bgb_6_4384 bgb_6_4416)))) (concat (concat (concat bgb_6_4448 (concat bgb_6_4480 bgb_6_4512)) (concat bgb_6_4544 (concat bgb_6_4576 bgb_6_4608))) (concat (concat bgb_6_4640 (concat bgb_6_4672 bgb_6_4704)) (concat (concat bgb_6_4736 bgb_6_4768) (concat bgb_6_4800 bgb_6_4832)))))) (concat (concat (concat (concat (concat bgb_6_4864 (concat bgb_6_4896 bgb_6_4928)) (concat bgb_6_4960 (concat bgb_6_4992 bgb_6_5024))) (concat (concat bgb_6_5056 (concat bgb_6_5088 bgb_6_5120)) (concat bgb_6_5152 (concat bgb_6_5184 bgb_6_5216)))) (concat (concat (concat bgb_6_5248 (concat bgb_6_5280 bgb_6_5312)) (concat bgb_6_5344 (concat bgb_6_5376 bgb_6_5408))) (concat (concat bgb_6_5440 (concat bgb_6_5472 bgb_6_5504)) (concat (concat bgb_6_5536 bgb_6_5568) (concat bgb_6_5600 bgb_6_5632))))) (concat (concat (concat (concat bgb_6_5664 (concat bgb_6_5696 bgb_6_5728)) (concat bgb_6_5760 (concat bgb_6_5792 bgb_6_5824))) (concat (concat bgb_6_5856 (concat bgb_6_5888 bgb_6_5920)) (concat (concat bgb_6_5952 bgb_6_5984) (concat bgb_6_6016 bgb_6_6048)))) (concat (concat (concat bgb_6_6080 (concat bgb_6_6112 bgb_6_6144)) (concat bgb_6_6176 (concat bgb_6_6208 bgb_6_6240))) (concat (concat bgb_6_6272 (concat bgb_6_6304 bgb_6_6336)) (concat (concat bgb_6_6368 bgb_6_6400) (concat bgb_6_6432 bgb_6_6464))))))))
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
theorem bgb_7_2240 : Interval gbAtlas 7 2240 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2251 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 (concat bgb_7_480 bgb_7_512))))) (concat (concat (concat (concat bgb_7_544 bgb_7_576) (concat bgb_7_608 bgb_7_640)) (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 (concat bgb_7_768 bgb_7_800)))) (concat (concat (concat bgb_7_832 bgb_7_864) (concat bgb_7_896 bgb_7_928)) (concat (concat bgb_7_960 bgb_7_992) (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088)))))) (concat (concat (concat (concat (concat bgb_7_1120 bgb_7_1152) (concat bgb_7_1184 bgb_7_1216)) (concat (concat bgb_7_1248 bgb_7_1280) (concat bgb_7_1312 (concat bgb_7_1344 bgb_7_1376)))) (concat (concat (concat bgb_7_1408 bgb_7_1440) (concat bgb_7_1472 bgb_7_1504)) (concat (concat bgb_7_1536 bgb_7_1568) (concat bgb_7_1600 (concat bgb_7_1632 bgb_7_1664))))) (concat (concat (concat (concat bgb_7_1696 bgb_7_1728) (concat bgb_7_1760 bgb_7_1792)) (concat (concat bgb_7_1824 bgb_7_1856) (concat bgb_7_1888 (concat bgb_7_1920 bgb_7_1952)))) (concat (concat (concat bgb_7_1984 bgb_7_2016) (concat bgb_7_2048 bgb_7_2080)) (concat (concat bgb_7_2112 bgb_7_2144) (concat bgb_7_2176 (concat bgb_7_2208 bgb_7_2240)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 60 := (concat bgb_8_0 bgb_8_32)
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 7 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 20, 52)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 6 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfefefeeafeeefce0fefefeeafeeefce0fefefeeafeeefce0fefefeeafeeefce0fefefeeafeeefce0fefefeeafeeefce0fefefeeafeeefce0fefefeeafeeefce0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4278124266 * 2 ^ 32 + 4277075168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36398.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,1]⟩,⟨.or,[2,4]⟩,⟨.or,[1,2]⟩,⟨.and,[0,5]⟩,⟨.and,[6,7]⟩,⟨.or,[9,10]⟩,⟨.and,[3,8]⟩,⟨.and,[4,5]⟩,⟨.or,[12,13]⟩,⟨.and,[8,14]⟩,⟨.or,[11,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124266 * 2 ^ 32 + 4277075168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124266 * 2 ^ 32 + 4277075168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36398

open PEqualNP.Outside.L_meta_36398 in
theorem PEqualNP.Outside.L_meta_36398 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124266 * 2 ^ 32 + 4277075168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124266 * 2 ^ 32 + 4277075168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
