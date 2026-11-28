import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36240.Model
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


end PEqualNP.Outside.L_meta_36240.Model

namespace PEqualNP.Outside.L_meta_36240
open PEqualNP.Outside.L_meta_36240.Model
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

def SBf (j : Nat) : Nat := [5, 6, 7, 7, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36240

namespace PEqualNP.Outside.L_meta_36240
open PEqualNP.Outside.L_meta_36240.Model
def s0K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (i*5) 5
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (6+((h/1+packedAt s0K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xfc07ffc07ffc0783fffffc0ffe07ff007f9e7c
  | 2 => 0xffffffff81fffffc0fc07ffffff81fff98ff8f
  | 3 => 0xfff81ffffffffffff0007ff03fffffffe0e3ff
  | 4 => 0x1ffffe0007ffffff80003fffe001ff03f0
  | 5 => 0xffffe000000007ffffffffffc0000001fffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x2530c4471448a980b2ca9c854e43390c2b8e3c
  | 2 => 0xa85108890c9122940552251992c90a54983685
  | 3 => 0x10a255122122852950284aa4251654a960c15a
  | 4 => 0xa2c59a24483b36ce69b3030939e58831dd03e0
  | 5 => 0xc3061c3871c3c7738e3c73ce018610c1f6f800
  | _ => 0
def s0Atlas : Atlas := ⟨4,rawDecor 62 s0Pos s0Neg, 0xfcccf0c0fc00f000fcccf0c0fc00f000fcccf0c0fc00f000fcccf0c0fc00f000fcccf0c0fc00f000fcccf0c0fc00f000fcccf0c0fc00f000fcccf0c0fc00f000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36240
namespace PEqualNP.Outside.L_meta_36240
open PEqualNP.Outside.L_meta_36240.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0xc018000f10008024a40520000e00c04000b00734000980bf43de43bd43dd439d43bf42bd42df32dd32bf41bd41df31dd31be40bc40de30dc30
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xe61a0044823080145a801c28600081e91002298a0208c2747552438fa92871f5150e38a0a1c754f429aa8e851d54ccaaaa39947551328ea9e832d52d063aa998d354b318eaa2631d531025aa4204d544408faa4611d540c29aa4185554430
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x4061000855875250e0d62d4543835885050e156114143
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 17
  | 3 => 21
  | 2 => 4
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*5) 5
  | 4 => packedAt s1K4 (i*16) 16
  | 3 => packedAt s1K3 (i*27) 27
  | 2 => packedAt s1K2 (i*38) 38
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (6+((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s1K4 (297+((h/5+packedAt s1K4 (272+(h % 5)*5) 5) % 27)*6) 6
  | 3 => packedAt s1K3 (602+((h/7+packedAt s1K3 (567+(h % 7)*5) 5) % 26)*6) 6
  | 2 => packedAt s1K2 (156+((h/1+packedAt s1K2 (152+(h % 1)*4) 4) % 9)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x87ffff0ffffc1ff83ffe0fffc1fffc1f9cf3cf
  | 2 => 0xf8783ff0f07fe1ffc707f0f0fe1e1fe3eb4d33
  | 3 => 0xff803fff007ffe1ff807ff00ffe01ffc738e3c
  | 4 => 0x3fffff80001ffff80000ffffe0007c0fc0
  | 5 => 0xffffc0000000001fffffffff000000007ff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x80000100000020000008011000220400001045
  | 2 => 0x1212522244a90309434290a252144943294512
  | 3 => 0x2124a4442952103298852a04a5409298528a28
  | 4 => 0x7557388aac1b555cedd18888f999c0c97c0f80
  | 5 => 0x466630ecce63999f36e7ccce311103127fe000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaafaaafaaafaa0faaafaaafaaafaa0faaafaaafaaafaa0faaafaaafaaafaa0faaafaaafaaafaa0faaafaaafaaafaa0faaafaaafaaafaa0faaafaaafaaafaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36240
namespace PEqualNP.Outside.L_meta_36240
open PEqualNP.Outside.L_meta_36240.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x100b0b921aa13043488a151844c9f0c3c513103800b3c1d2ab0aa819d2c40e004e840004600129008000000012090060000006c0070013806072c50012c41ccff43fe43fd43fc43ff42bf42fe42ee42fd42bd42ed42ad42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xd648238ac784f0a00000262f8800a002a800487c00114ce62108c4b813370001a00118005c280e804527115044d800211807e00001740000001fc184a0c83c047b1b8e0da731a12cbc6132868121f1114c7a753b8ccb4270d91800762d9e00007200004a54000e8f2000b000000039000000000104005222000004c000c8d418050c000001c800002f00140d03527010e87d31924de1c40040ac0e1f1f8a259019e80c170015c3c2d040d8d2660a848000000000e04305800584d1d960006401008100840201038280008080058000800100008089800b8a84010382018004000f0e0a0001870000000a5b94b43b6a96877651d0eeaa3a1db94843b6a90873d5490adaa9214b55242d7a9285af5450b5e86a16b90d42d6a1a85ac4350b5ea6a16b94d42d6a9a85ac5350b5ea2a16b94542d6a8a85ac5150b5ea0a16b94142d6a8285ac5050a7ca8215b94842d6a1085ad42cca7ca9194f55232d6a146576518caeaa3196b509329f2a0653d540cb5a84195794f41aea9e836e52d06daa5a0eb50b41d6a1483ad42506dca420db54841d6a10833e54cc67aa998db94b31b6a9663ad42cc67ca918cf55231b7294636d528c75a8518eb50931d6a1063d5310c67ca990cf55321af29e435d53c875a8590eb50a21d6a12433e540867aa810eb50821b7296816d52d035a85a06b50a40d6a12815e53102baa6205b94840b6a9081ad42102eca2205d54440d6a1661ad428c27ea8984f15130b7a92616c524c35a84985dd4530ba28a613e540c27aa8185b94830b6a9061ad420c2eca2185d544309f2a6413d54c835a85906b50a20d6a12413e540827aa8105794c20aea9841ad42082eca2105d54420d6a1621ad428427ea8884f15110afa9a215c53442dea4885b14910d6a12213e540427aa8085794c10aea98216e52042daa4086b50810
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xd8a92192098800c801e09078014138f02181605801b000d00110e860b83a11f8015080000129d8019800008800014a19ca00f971a001d0e1a9c029e95849b8080030401850000000a10130c000986801196870b1f17800110800400042093c00004020400000042810024082a99874350aa561d0d42a99875350aa561d4d42a99865350aa56194d42c354c5350a8e63d4542a358f5150a8e6394542a358e5150b255114542a3d8d5050a8c6354142a9d855050aa46154142a398c5050a8d6314142a99845050aa56114142c950a518cb254254632c394d42d070d5350b418b58a54cc62d6494b318bd9542cc62d6550b318b58a548c62d6494a318bd95428c62d6550a31e1509310c70e5350b21c354d42c870e5350840c354d42103254294440c9509511022d62151308b590524c22e65509308b195424c32542d4530c9508514c22d62950308b592520c22f65508308b595420c3254294430c9509510c22d6255020c394d420830d5350820c950a510832542544208b588544422d64149108b995424422c6550910c3d4d424430c53509108b58a540422d64948108bd95420422d6550810c394d420430d5350810
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 45
  | 4 => 129
  | 3 => 68
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
  | 6 => packedAt s2K6 (6+((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s2K5 (810+((h/15+packedAt s2K5 (720+(h % 15)*6) 6) % 60)*7) 7
  | 4 => packedAt s2K4 (3827+((h/43+packedAt s2K4 (3483+(h % 43)*8) 8) % 170)*9) 9
  | 3 => packedAt s2K3 (2738+((h/22+packedAt s2K3 (2584+(h % 22)*7) 7) % 90)*8) 8
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffc3fffffff03f07fffff07fffff23f1ff
  | 1 => 0xf83e0ffc1f0f83ffc7f870787f870f0fdd4e93
  | 3 => 0xffc00fffe00ffc3ff8007f807ff80ff0e18f1c
  | 4 => 0xffffff0003fffff80007ffff000fe0fe0
  | 5 => 0xfffff0000000003fffffffff80000000fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x8000040000000000000808800090100001025
  | 1 => 0x128c9488ca152612c348345134822a2e4d4692
  | 3 => 0xa195ad1146aa627558c45d425d504ce2e18b18
  | 4 => 0x85294a22948348a9ad9508046a64e044b60dc0
  | 5 => 0xc6318c3b18cc733e36e66e670c408888fbe000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeeeaaaaeeaaaa88eeeeaaaaeeaaaa88eeeeaaaaeeaaaa88eeeeaaaaeeaaaa88eeeeaaaaeeaaaa88eeeeaaaaeeaaaa88eeeeaaaaeeaaaa88eeeeaaaaeeaaaa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36240
namespace PEqualNP.Outside.L_meta_36240
open PEqualNP.Outside.L_meta_36240.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x44004800084e0000011930098219360042400580053454592503000000000004e28b8106007803e00000227400040006800050f2504015a9540032c20007000e6018000000008300000000200000ff43fe43fd43fc43ff42fe42fd42fc42ff32df32fe32ee32fd32dd32ed32cd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x1a8366f2490cdc7b081fca446129e464000007cd6752011c2a00000005e050000000000018cd2703f024004a369c4005d20954003b2215800000c1cc741200000000000000007d299900065000784400268184200041c800000d1500000000d8560e00000ec041e93800242d000a20000178b662098002e28001981a3e000004e00228003a3f001e05a33001206014130a4180000000d85900160025c1e12cbe231a130ce070c980e8570b000840a08870c2002780000803d1dc0035000e46e00000b04003001a01650000e01e2a17008627c070080020980010003800081820281808100070081030200800084030001828880010005820601820480005b94a43b6a9487765190eeaa321db94843b6a90875e5390abaa7215d94642baa8c855e5310abaa6215754e32b6a9c654d538cb9ea49973d0932e721265cd424cb98849973d4d32e7a1a65ce434cb9a86997310d32e7aa265ce544cb9aa8997315132e7a8a65ce514cb9aa2997314532e7a8265ce504cb9aa0997314132af298656e520cb9a64195794f41aea9e836e52d06daa5a0f34cb41af29c835d53906dca520db54a41e699483cd325079a6420ed504419f2a6633d54cc6dca598db54b31e699663cd328c79a6498db94831b6a9063cd320c67ca990cf55321af29e435d53c879a6590f34ca21e6992435e53086baa610f34c821e699681cd32902bea6a05714d40b7a92816c525039a64a05dd4540ba28a815e53102baa6205b94840b6a9081cd32102eca2205d54440b7296616d52cc39a6598734ca30e6992613e540c27aa8185b94830b6a9061cd320c2eca2185d54430af29e415d53c839a6590734ca20e6992413e540827aa8105794c20aea9841cd32082eca2105d54420e699621cd328427ea8884f15110afa9a215c53442dea4885b14910e6992213e540427aa8085794c10aea98216e52042daa408734c810
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x20099c000706209d9193038a159b8d179b1a8d9f878f800010a18000160006800e80139e80080c8280151f00968c110412091280001a001c8018001d000005831484801882198000000b800a80191e0b0010000897050f0000000180000e1400210001008022007810414000002838c1a282030200200b1986424cac56190932b1986434cac56190d32b1987544cac561d5132b1986544cac56195132c3550544ca8e64d4532a3593514ca8e6494532a3592514cb455114532a3d91504ca8c6454132b1d85504cac46154132a3990504ca8d6414132b1984504cac561141329358a53d064d6394b4193d9532d064d654cb419358a539064d6394a4193d95329064d654ca41e14c9411070e544cb31c355132cc70e544cb21c355132c864d6214d409358c525024e654c94093195325034532d4540d14c8515024d6294c409358e521024f654c8409359532103453294440d14c9511030e544c830c3551320c3453294430d14c9510c24d6254c20c3951320830d544c820d14ca5108345325442093588534424d631491093995324424c654c910c3d51324430c544c9109358a530424d639481093d95320424d654c810c3951320430d544c810
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
  | 6 => packedAt s3K6 (6+((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s3K5 (825+((h/15+packedAt s3K5 (720+(h % 15)*7) 7) % 79)*7) 7
  | 4 => packedAt s3K4 (3827+((h/43+packedAt s3K4 (3483+(h % 43)*8) 8) % 187)*9) 9
  | 3 => packedAt s3K3 (2738+((h/22+packedAt s3K3 (2584+(h % 22)*7) 7) % 99)*8) 8
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xfc3ffffffffffff03f07f07fffffffff223fff
  | 1 => 0xffc1f0f83e0f83ffc7f87f870e0f0f0fddd293
  | 2 => 0xfffe00ffc00ffc3ff8007ff80ff00ff0e1e31c
  | 4 => 0xfffff0003fffff80000ffff000fe03e0
  | 5 => 0xffffff000000003ffffffffff0000000fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x4000008000000000000800900110100000425
  | 1 => 0x2894611194551512c3283282268a2a2e4cd292
  | 2 => 0xb10caaa28d6a517558a45b504ba84ce2e16318
  | 4 => 0xa3a94cc5294359b9adb50a408dcce844f603c0
  | 5 => 0xc2318886318c622e36c66c64e1008088bbb800
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeaaaaaa8a8eeeeeaeaaaaaa8a8eeeeeaeaaaaaa8a8eeeeeaeaaaaaa8a8eeeeeaeaaaaaa8a8eeeeeaeaaaaaa8a8eeeeeaeaaaaaa8a8eeeeeaeaaaaaa8a8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36240
namespace PEqualNP.Outside.L_meta_36240
open PEqualNP.Outside.L_meta_36240.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x900000000001951d245800b00013804aac01c0430022003930a368c0000020b8f26a0d140801485009019800780200e65089007ca911a3c0000084040000040003ff43bf43fe43fd43bd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31f631fd31f531fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0xe617e52cc2faa59877ccb30ee996617e51cc3eca3985d94730bea8e61f551cc2eaa39877cc730fb18e61dd31cc3ea6398754c730bfaa4617e548c2faa9185f15230bea9c61bf438c37a87185f94a30bea9461de328c3b865185f94630bea8c61f6318c3ea63185f94230ef98461fb308c2fea8985f95130beaa2617c544c37e86987790d30dea1a61dd434c33a86985fd4930be29261df324c3ba64985fd4530be28a61df314c3ec6298774c530fa98a61d5314c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf29861bf430c37a86185f94830f7290616e520c2faa4187b54830b6a9061de320c3b864185f94430fb2886176510c2faa2187d54430baa8861f6310c3ea62185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20dfa1e41bd43c83dc85907b50b20f719641ed32c82fca3905f54720fb18e41f531c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20dfa1c41bd43882faa5105f94620bea8c41f631883ea63105f94220fd18441f930883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20dfa1a41bd43483dc84907b50920f719241ed32482fea2907dd4520bba8a417c51483e8a2905d14520fb18a41f531483de42907b48520fd18241f930483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20dfa1841bd43082fca4105f94420fb288417651082faa2107d54420baa8841f631083ea62105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10dfa1e21bd43c42fea5885f94b10bea96217c52c43ec83887d50710fb18e21f531c43ec43887d48710bfaa4217e54842faa9085f15210bfa9c217e53842faa7085f14e10dfa1c21bd43842fea5085f94a10bea94217c52842faa3087dd0610fa20c21f631843ea63087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a217e53442faa6885f14d10dfa1a21bd43442fea4885f94910bea92217c52443ec82887d50510fb18a21f531443ec42887d48510fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c530437e86086f50c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf28821f741043e882087d8c410fa98821f721043e842085f94010fb88021fa10043ea20087e44010
  | 1 => 0xe548c6faa918df15231bea9c63bf438c77a8718df94a31bea94637e518c7ee8318fd90631faa0c63f4418c7be6318fdcc631bf284637d508c7eea918fd95231faaa463f4548c6eaa718fdd0e31dba1c63f6438c7ea8718ed50e31fa21c63f7528c7eca518fd54a31fa29463f7428c7ec8518fd50a31fa21463f7328c7ec6518fd4ca31fa19463f7508c7eca118fd54231fa284637f544c6fca898df55131be2a263bf434c7bc8698ef50d31eea1a639d434c6fea498df14931ef19263dc324c7ee8298fd90531faa0a63f4414c7ee6298f78c531bfa82637c504c7eea898fd95131faaa263f4544c7eea698f5d4d31fba1a63b7434c7ec8698f590d31faa1a63b5434c7aa8698e550d31fa21a63f7524c7eca498fd54931fa29263f7424c7ec8498fd50931fa21263f7324c7ec6498f58c931fa99263f4324c7a86498fdd4131fb28263f5504c7e8a098dfd5031bf2a063be540c67ca818df55031deaa0633d540c6f8a818df94c31dfa1863bd430c6fca418df54831bf2886376510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c86faa790df14f21dfa1e43bd43c87ec8390fd50721fb18e43f531c86fca190df54321bfaa4437e548877ca910cf95221beaa443bd548867aa910df15221bfa9c437e53887bca710d794e21bea9c43dd53886baa710df14e21dfa1c43bd43886faa510df94621fba0c43f441887ec6310fd4c621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21dfa1a43bd43487ee8290fd10521fb18a43f531487ee4290fb88521bfa82437c50486fea810df95021beaa0437c54086fea610df94c21bea98437c530877e8610ef50c21bf290437e51087ec8210fd50421fb18843f531087de4210fd88421f690843f521086fca010df54021bf29e817d53d037e87a06f50f40bf296817d52d037e85a06f50b40bf28e817d51d037e83a06f50740fb18e81f531d02faa9205f94e40bea9c81bf439037a87205f94a40bea9481be429037885205f94640bea8c81be419037883207d8c640fa98c817e509037e81207ed0240bfa9a817c535037e86a06f50d40bfa92817c525037e84a06f50940bfa8a81f751502eea2a05f14540fa28a8174515037e82a06f50540fb18a81f531503f680a06f90140bf2a0817e53103bca6205794c40bea9881dd53102baa6206fd0c40dea18817e52103dca4205b94840bea9081ed52102daa4206f90840de210817e51103eca2205d94440bea8881f551102eaa2206f90440de20881f631103ea62205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330dfa1e61de43cc37a87987750f30cea1
  | 2 => 0x801004000001800000400400000000c00001000000000c00400001800000400000000c00000000000000401000000000400000400800c000004000000014000000000006fca5a1df54b43bf28e877d51d0efca1a1df54343dfa9687be52d0f7aa5a1ef14b43dfa8e87be51d0f7aa3a1ef14743dfa8687be50d0f7aa1a1ef14343beaa4873d5490efca721efd0e43efa1c877e5290efaa521df94643fb28c87765190efaa321fd54643baa8c877e5090efaa121f7d0d43df21a877f5250ef8a4a1dfd4543be28a877f5050ef8a0a1efd4d43cfa9a87bf5250f7ca4a1ef54943de29287bf5150f7ca2a1ef54543de28a87bf5050f7ca0a1ef54143de282877e5410e7ca821df94c43dfa1887de4310f7a8621f750c43bf290877d5210efca221fd94443bb288877d5110feaa221dd54443bf280877d5010efca7a17794f42af29e857d53d0bbaa7a15754f42dfa1e85bd43d0afca3a17d94742bb28e857d51d0beaa3a15d54742bf286857d50d0afaa9215f94e42bea9c85bf4390b7a87215f94a42dfa1485ef4290afca3217d94642bb28c857d5190beaa3215d54642bf284857d5090afea6a15f14d42dfa1a85bd4350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e5310afaa6216fd0c42dea18857e5210b7e84217b90842dea1085ed4210afca2215f54442bf280857d5010afea9995f95332df2a6653e54ccafaa9996f553329eaa6657c54ccb7e87996f50f32bf28e65f651ccaeca3995f54732faa8e657551ccafca1995f54332bfaa4657e548cafaa9195f15232bea9c65bf438cbbc87196f50e32eea1c659d438cafca51977cca32f7994657e518cafaa3195f94232bea84657f544cafca8995f55132be2a265bf434cb7a86997bcc932ef192657f514caf8a2995fd4132be282657f540cafca8196f950329f2a0657d540cb7aa8194f55032be2a0657e530cb7e86197790c32dea1865dd430cb3a86195f94832ef99065ee320cbba64197b4c832bf28865f6510caeca2195f54432faa886575510cafca0197e94032bd280657d500cbf2a0195e54032bf29e837d53d077e87a0ef50f41bf296837d52d077c85a0ef10b41bf286837d50d06faa920df94e41bea9c83bf439077a8720df94a41bea9483bf429077a8520df94641dfa0c83f741906fca120df54241bfa9a837c535077e86a0ef50d41bfa92837c525077c84a0ef10941fba0a83be41506fea0a0df14141bf2a0837e53107bca620d794c41bea9883dd53106baa620efd0c41dea18837e52106faa420efd0841dea10837e511077e8220fd90441dea0883f5411076a8220df94041bea80837f54cc6fca998ef953319f2a6637d54cc77aa998cf55331be2a663bf43cc7bc8798ef50f31eea1e639d43cc6fca598df54b31ef19663dc32cc6fca198df54331bfaa4637
  | 3 => 0x178a1a2babc0108005aa9c80000000000000000000000ef0001b81f93a17a000000452c42b8000748622e4b80318003d4b8800261000000f58264ec0c4000000000015fae10000001d80058215c000005b6000000003faa345c8b72c00000000000021d6032f000000002f700000000000000001bca38398001b23570000005b000000000000000009780000000000000000000ae92d840564d78000000e8000100005de00000000000560e50060000000000008e000000004425e00028b18600054000000000002b60320c9749252c800019a09000000000822bc5d0001e10000009a00000000000000000000002440007492380005e25000000000a8d8b8006580000000007a0000025327e76400000000000b1b2000000000000000000000000de000003782880000001d000001078f4000000000000000002400013a000000c50be0000027f000001400005f8000003373960000000006c7740036f00000186800000000000001c4000000846100009e0000000000000015c0006d93b6b0000000000000002336d662150000270000000019a00000000000000000000000a2000000fa6d8000000000000000001e000000001900000011d00000032800000594001b02b4598aa00015a16200000000552790000000000000005b5488e400000000ce80000043e000000000000000000046e000001a95a80009380000000000000000000002fb000000000000000001a0000000000000032a0012c8000009680000000069197377646259a12466cec640000000000000000000b3400000160d1d8e000000000000000000006e822000000000f84ce1340000045e000000000000000035a000000000000003a18c0005e8044958000000000000017097d9c82b00000000000802800801000000400000000000400000000400400c00001800000400000000c00400c00c00000000000001400401800400400800000000000000000000000800001000401800400000400800000400400400000400000800400000c00801c00000400800000000000401400c00800400400400800000002c00000000000000000c00000400800000000000000000400000400000400000800400000000c00000400000000000000800400000400000000c00c00000800000401000000400003001c00000800800800400800000000401000c02400000400400000001400000000000000000001401c00400001800000000000000401001000c00000801c02800c00000801801000000400000000000001400400c00000000000401000002000000400000000400000000000000001800400400800400400000000000400000400000401000c00000000000c01000000000400000401400000400001400000000c0000000000000000040000040040080100100000040
  | 4 => 0xd700062ca494d4c600119a8a000000000000000000016600022400000060989378d20006fda032736801cdc0000007dc9a939000319212680006486b26a04a480002c60ee5580000000000000000000000500004d2c740031e10c3b0b616d502000000000306dc0000030434c00000000000de800000000000000001240000000000051800000000002240007b93c80041000030146148adc6f8000000000000001a0000014f14c000950001b0404d31f167a0000033f64a001b500000000000000000000561936440014733e000000000000000000000002c000000000000003e8000000000000066c0000026415400000000000a6087800138000000003c62f40000000091518996000ac00008d590001241f90003c400000000000000001a28ec0000020a0fc00000000b98f3800000001bb06400086c000003b00d4cfb3b01ed0c81b1055a000000000000017d25c1ecbcd948001060000024d000600000000007b03980041a48400000354000002702442899a800000000d9a875126c800000506000000000000000006e00000000000000520000002f63980000000000139aa0000000001e900000114b330002c8000000883940000000000000000000a9c70800000444000003de000000ed00000077000000240a09550007e80000000043800000000000000004a0001a9800204798e30004a20000000014a000000004f60011e87f6546519591800057d4980000000000000000d3980892000714000000000002987a0005143d800000000000002700000000068c45cb524000000000000000000001da00041ced800212ba0000000000000034b25a12c841850000e1218006e00000000000000000024000000000000000000000052e738212840000000000017c000000790ca0003ab4d000b3c000000000000000000000075aab000000479cd000000000ab0000015cb694fa56c0027e00084400000000000000005fcb44a5114000431690ba0000009300017600000000000b64000000009e8000000000016c0006422bc8e800116b4000000000000002c900055c000000006a18dad35bc2f0b4b320bcbc8980000463dc000000ce000351590000002e00000029c0000057a000000002fa0000017e54c0015c000000d7000000650000bc9c70006f0a18005d6000000000000000000000033527b1328e00125800380001482910cc72400000000924d290b000c1584a8c000000000c85da90400000000000700de152000000000008c0e40e7000d14000000d6185001620820000026e6d000060a86000aa80b8000005dc1e0000000004a8000008f882311100000ef8ef000000161c100006c0000031000000000000000000005b813c272130e41a00000042e000000004560014cb544684917ea07000aec001d70008fc000f20003f40000
  | 5 => 0x4e97c196244d38003020014f0011e0ab80030e00000187802000001aca035fe0000000051e2d42900059c309250000000000000000000000257000000002710000000000000000000000000000000000000000026c26e95436000660811b2800000dd400000000000000000000b425000000000000000000000020111c154ce99e2e67704d0093380000000011800096000424000001ba000858003440008a8000001aa000000000002cc002230b08310a00c12e00000348000000000000000000f800000000000003ea0013e00030e0000000000068800000000220000bf1a8874000000000013c1310004ccd78001ead44d70004ea00196800000000000006180000e1320ec0000000036c0280000022cd28b413e388788000000000e442af9000000718002a2000001bb000454228003f63cd05800000001b9800510000830000000000011900046800000000000899e82a8000141530000214a0c701c7c1030504ca6c18325d2960017725852c5fd7a8000004b800000220000001290000000005a000745029b900000000227000000000000000000032413ca70c180013e001010004da0011330a6e4d6ce800000000142b07000000000004a800116000000001ab23c45c000000000000005a0000006b00021545a0000010d0000004c800000d49270001360006800046c5d40007c236684cd800000000003140000000035500000000000214795358005c83240000000000000000000300000000009dc150fe0000017500046a00000000000000000000001e09b00032ed3c00000000b9c00000000000000000000009d000000860a60006e24f4d680058add0000000000000000000000000000000000000005c6538001fc0e0000000000000e98d0000b20000000000000000000346000080000006240000000000000000246000b2a2200000000000356000000000000014d1d543800000000000540001c3000a48e11cf0000000000064c00000000000500002b30000013035d0000000000000000161800000000001fe682d980000000a0000000000000000112000000a11b120000000056142a85af98f000000000005b4000662cb4cc000000000005ac00000000d318b2250520016f800000000090000000000000046447d4d800000001b10000000015f11c000000001995ec24c7fa955d8000003506dc5490700000000189000000000003154987d95a8002dec0cc70006080010ca20000001b19280000000000000875000000450000000370000000980000000000000000000c88000006f8000000000000000069200000000000000f90d95847ccb896e000cd07500007c618da80000000000000000a7c000000007fcb38002ec02c000005780000006905c0000000000000000000308000000003c0310000005ba0000030b00000000
  | 6 => 0x4149580031f130a88000030000017c2101c80000000000000000000000660000710000000021e000000fc0003da000000000003ecc5282000abc000005ac000b81d602aa940a0da2c22b5b08fc678000002c70000006700000033c000000000000011e000000978005ae1747c80010200000000000948261a0562000001d3000068000000001b5563003e86300000031a0017280067000021b6b00000000000000c09
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x5200832d5448020d354d200836551480209ed95200835953480209798c54c425d63153108f99253c423d6494f108f99053c423d6414f10c794d43c431d5350f108f99352c423d64d4b109798f52c425d63d4b108f99252c423d6494b10cd15141c4355538c710d5d4d31c4395434c710ad59221c42d563887109798c548425d63152109b988548426d62152108f992538423d6494e108f990538423d6414e109b988538426d6214e10c794d438431d5350e108fd91528423c6454a1097d8d528425c6354a108f990528423d6414a109798c528425d6314a10cdd5041842d56310610d594d3184355534c610e550d31842b664c86108f58f544423e64951109dd85544425e63151109758c544423e6515110a758c544431e63151108f58c544431d63151108758c544433561151108f992534423d6494d109d586534423f6454d108f191534426f6254d109b189534423e6414d108f59053442766114d108f997434423c65d0d108f995434423c6550d10c794d434431d5350d108f992524423d64949108fd91524423c645491097d8d524425c63549109dd8552442766590510cd15241442746550510cd1514144337548c510cd1523144274654c510cdd513144334544c510d5d4d3144395434c5109d99621442b56488510cd15221442d563885109d19521443345448510cd152104425e63d50109758f540426e62d50109b58b540423d65950108f58e540423f6355010cd185540423e64150109798c540425d63150109b988540426d62150109d984540423e64d4c108f593530426e62d4c109b58b530423e6494c108f592530425d6594c10c7952530431d5494c10c7992530431d6494c10d598653042756154c10c7951530431d5454c10c7991530431d6454c10d5985530423e6414c108f590530425e6314c109b988530426d6214c109d984530423f65d0c108f597430431e53d0c10c754f430423f6550c108f595430431e5350c10c754d430423e64d48108f593520425e63d48109758f520426d6594810cb952520432d5494810d394e520434d5394810cbd0e520432d4394810cb951520432d5454810d394d520434d5354810cbd0d520432d4354810d9185520423e64148108f590520425e63148109758c520426e62148109d984520427565d0410cd553410435553d0410d954b41042756510410cd55041042d56310410d554c410436552104109d5963104336548c410cd5523104355538c410d994a3104365528c410cd9513104335544c410d594d3104355534c410e550d3104366524c410d9549310427565c8410ad993210433554c8410d554f210436552c84109d59421043355408410d554c21043655208410cd553100435553c4010d954b100427965840109dd9510042b46444010cd55110043555344010d9549100427b6544010
  | 1 => 0x823e6494f208f59253c82766194f209d58653c823e6414f208f59053c82766114f209d58453c831f5350f20c714d43c82e56190b20e350e32c823e64947208f59251c825e63947209758e51c8357534c720d514d31c8395434c720f18c931c82ad64c87209dd85548827461552209798c548825d63152209d984548827561152208f992538823d6494e209d98653882756194e208f990538823d6414e209d98453882756114e20c794d438831d5350e208fd91518823c6454620d594d3188355534c620e550d3188399434c220f44c5308823d63d51208f992544825e63951209758e544827661951209d586544825f63551209718d544827761551209d185544823e65151208f58c544832d6215120c7d53534831c54d4d20c7d93534831c64d4d20d5d87534835461d4d208f992534823d6494d209798e53482766194d209d586534823f6454d208f19153482776154d209d185534823e6414d208f59053482766114d209d584534825e6514d20c7d50534831c5414d20c7990534831d6414d20d358853483566114d20d558453483596014d208f997434823c65d0d20c7d4f434831c53d0d208f995434823c6550d20c7d4d434831c5350d20cb15242482e561909209b195424834c538c920e350e324826c654c920cdd53514833454d4520d5d4f514835453d45209d58f514833743d4520cd50f51483375414520cd15051483575314520d514c51482756314520cdd0c514833543145209d9963148274658c520cdd523148334548c520d5d4e3148354538c5209d9953148274654c520cdd513148334544c520d5d4d3148354534c520e550d31483c6324c520ab593214836451c8520d614e30483ca328c1209e1953048399434c120f24c930483d1314c1209798f540825d63d50209d987540827561d50208f596540823d63950208fd8d540823e64150209798c540825d63150209b988540827661150209d584540823e64d4c208f593530827661d4c209d587530823e6494c208f59253082766194c209d586530825d6594c20c7952530831d5494c20c7992530831d6494c20d598653083556194c20c7951530831d5454c20c7991530831d6454c20d598553083556154c208f990530823d6414c209798c530826e6214c209d98453082756114c209e980530823f65d0c208f597430831e53d0c20c754f430823f6550c208f595430831e5350c20c754d43083365494420cd55251083565394420d554e51082756394420cdd0e51083354394420cd95151083355454420d594d510835553544209dd8d51083374354420cd50d5108277658c4209d5963108336548c420cd5523108356538c420d554e3108277654c4209d5953108336544c420cd5513108356534c420d554d3108395434c420cb553200834d53c8020d9547200835953880209bd9
  | 2 => 0x5210840d594e51103555394440d994a511036552944409d58e51103374394440cd50e51103565354440d554d51103665254440d954951102776354440cdd0d51103354354440cd909511033442544408f596411031d5390440cb54a41103355190440a758c411031d5310440cb548411033551104409dd963110275658c440d594e3110355538c440d994a3110365528c4409dd953110275654c440d594d3110355534c440e550d3110366524c440d9549311031d53d0040cb54b401033551d00408fd95401031d5350040cb54940102b46150040cd545401027b65500409d98754cc27561d5330c798e54cc27661153309d58454cc2d56190f30c795143cc29f6550f30c7d9543cc31d4394b30a759332cc2d561ccb30cd95251cc3355494730e550e51cc3374394730cd50e51cc31d4354730cd95151cc3355454730e550d51cc3374354730d590d51cc3354354730d550d51cc3154354730a759331cc31d54cc730cd95231cc335548c730e550e31cc31d544c730d594531cc336544c730cd55131cc397434c730e550d31cc2d7654c730d5d9531cc357544c730e595131cc355544c730e555131cc315544c730d594931cc27761552309d185548c26e62152309b588548c27661152309d584548c23f6454a308f191528c2776154a309d185528c2d9600ca308fd91518c23c6454630e550d318c26f62551309b189544c27761551309d185544c27661151309d584544c29d6490d30b5586434c25c6550d30c7d95434c31c6550d30e6d81434c3986050d308f990524c23d6414930c750c524c27661149309d584524c25e65cc930a7593324c2d561cc930c750f514c23e64145308f590514c29d64cc530b558e314c395438c530e5d0d314c395434c530d5d51314c355544c530d5149314c3d3604c530f4181314c39943cc130f44c7304c26e62d50309b58b540c27661d50309d587540c23d65950308fd8d540c23d63550308f990540c25e63150309b988540c26d62150309d984540c27561150308f992530c23d6494c308f597430c23f6550c30c794d430c32e5494830cb552520c32f4394830cb50e520c32e5454830cb551520c32f4354830cb50d520c25d658c830c7552320c34d528c830c7550320c34d520c830b6580320c3365494430cd552510c3665294430d954a510c3374394430cd50e510c3365454430cd551510c3665254430d9549510c3374354430cd50d510c3563254430d50c9510c275658c430cd952310c335548c430d994a310c365528c4309dd95310c336544c430cd551310c356534c430e550d310c366524c430d9549310c31d54cc030d354b300c35551cc030da54a300c25f654c030c7551300c34d524c030d5545300c27b654c030da549300c27661d53209d58754c825e63953209758e54c827661953209d58654c
  | 3 => 0x431d5945310c677654c431cd951310c735544c431e550d310c65e63953219758e54c869d6395321c798e54c863d6395321c758e54c861d6395321cd58654c863f63553218f99353c863d64d4f218f99253c863d6494f218f99053c863d6414f219e98053c86796014f218fd9743c863d65d0f218fd9543c863d6550f21c7d4d43c871c5350f21cd95241c87365450721cd95231c8735548c721cd95131c8735544c721d554d31c8795434c7219798f548865d63d52218f58e548863f6355221cd185548865e63152219758c548863e64d4e218f593538863e6494e218f592538871e5494e21c7552538871e6494e21c759253887566194e21c7951538871d5454e21c7991538871d6454e21d5985538863e6414e218f590538863f65d0e218f597438871e53d0e21c754f438863f6550e218f595438871e5350e21c754d438873554d0621d554f41887355410621b558c41887555310621cd9523188735548c621d554e3188736544c621cd5513188756534c621d554d3188795434c621ad993218873554c8621d554f218865e63951219758e544867561951218f992534863d6494d219d586534863e6414d218f590534871f5350d21c714d434867665d05219d99441487355410521b558c4148674654c521d5d4d3148754534c521e550d31486e4624c521ad993214863e64141218f590504865e63141219758c504867661d50219798c540865d63150219e980540867960150218f992530863d6494c218f990530863d6414c219d984530867a6014c219e580530871e5350c21c754d430863e64948218f592520863e64944218f592510865e63944219758e510867565904219dd95410873454504219d5963108755538c421b958a3108757534c421e550d31086b56488421b558e210866f65484219dd95210863f64540218f19150086766194f409d58653d031d53d0f409d98652d02756194b40a758f42d02b561d0b40d594d31d0355534c740e550d31d02766194e409d586539031e5350e40c754d439025f6354a409718d52902776154a409d18552902b66190a40a758c4190356534c640d554d3190395434c6409d98453502756114d40c7d4d435023e65d0940a758f42502b561d09409d58f515033743d4540cd50f515025e63145409758c51502d56314540d598c51502756314540d558c51502556314540cdd0c51503354314540cdd08515033542145408f997415033451d0540cd1454150276658c5409d1963150276654c5409d1953150395434c540cd14640502766194c409d58653103566194c40d5586531031e6454c40d598553103556154c40c754f431031e5350c40d394e521034d5394840cbd0e521032d4394840d394d521034d5354840cbd0d521032d43548408f596421031d5390840cb54a42102b66190840c754c421032d
  | 4 => 0xd94941106b46050441cd505501071e6395331c795143cc69f6550f31c7d9543cc71d4394b31c755232cc69d640cb31c755032cc74d520cb31b658032cc71d43543319b98b548c66d62d52318f992528c63d6494a31cd151418c7355410631ad993318c6b564cc6318fd91508c63c6454231b558f548c6e662d5231b958b548c7355415231b558c548c7976350e31ad993528c6b564d4a31ad992528c6b56494a31d9548528c67665d0a319d597428c6d663d0a31b558f428c6766590a319d596428c6b664cca31ad593328c795438ca31ad990328c6b5640ca31e550c328c7c5320ca31bc980328c6f1600ca31add91508c6b46454231ad990508c6b56414231b9988508c6e562142319b98a544c66d6295131a7592434c6d66190d3197195434c71f6550d31c7195434c7976150d31e5185434c63e64d49318f593524c71d4314931a7590324c6d6610c931b6580324c67665d0531b598f414c79543d0531e550e414c6746550531cd151414c7954350531cd550414c6d66310531e550c414c6b664cc531ad593314c79543cc531c750f504c63e64141318f590504c66e62141319b588504c6d56395131b998a544c6e56295131b5d8d544c7355415131b5593534c6d662d4d31b5583534c79753d0d319d996434c6b56490d31b5996434c7566590d31b5592434c6956490d31b598a434c6d56090d31e5d8d434c7975350d31b5995434c6d46550d31e5d91434c7975450d31e5151434c6d46250d31b5d81434c7976550d31e5995434c7956550d31e5195434c7976250d31e5989434c7956250d31e5189434c7976050d31e5981434c7956050d31e5181434c6766510d31ad990434c6d66310d31e550c434c6b664d4931ad593524c79543d4931ad992524c6b56494931e550e524c7954354931e550c524c76552149319d997424c67565d0931b598f424c6d563d0931e550f424c67665909319d596424c7954390931b5d8d424c6d46350931e550d424c6d66310931b558c424c79543109319d997324c6b664cc931ad593324c79543cc931e5d0e324c795438c931b5d92324c6d5648c931b598a324c7c7528c931f114a324c6d5608c931e550d324c676650c931ad990324c6b5640c931e5d0c324c795430c931bc980324c6f1600c931b5994324c756650c931b5d90324c796640c931b5590324c795640c931a5590324c6d6620c931f1988324c7d2600c931b5580324c7d1600c931b4580324c79543d4131e550e504c6b76454131ad191504c7954354131b9d89504c6e46254131ad990504c6b56414131e550c504c6e66214131b9588504c67661d50318f596540c63e64150319798c540c67661150318f992530c63d6494c318f597430c63f6550c31c794d430c7374394431cd50e510c71d54cc431cd952310c735548c43197d95310c71d544c
  | 5 => 0x5050e3f6550c4397d954310f1e5450c43cdd0e5110f354394443cdd0d5110f564354443cd50d5110f5543544439d98653d0a756194f42d598653d0b556194f42c799153d0b566154f42d558553d0b1d53d0f42c794d43d0b565394742d554e51d0a756394742cdd0e51d0b354394742d594d51d0b5553547429dd8d51d0b374354742cd50d51d0a766194e429d5865390b1d5350e42a758f4290ab561d0a429798e5190a5d6394642b558e5190b5663946429d58e5190b5563946429558e5190b374394642cd50e5190b3742946429dd8d5190b374354642cd50d5190a766114d429d5845350b1f5350d42c714d4350aac6250d42ad9864250a5e63141429758c5050a7661141429d5845050a766194c429d5865310b1d53d0c42ab58b4310a9d63d0842ad5874210a3f65508429bd954210a7761540429d1855010a7661d53329d58754cca7661153329d58454ccb365494732cd55251ccb374394732cd50e51ccb365454732cd55151ccb374354732cd50d51cca7661d52329d587548ca7661952329d586548cad56190e32c7d95438cb1c6550e32e3d89438cb8c6250e32a7593328cad561cca328f992518ca3d6494632c750d518ca3f64542328f191508cb1d43542329dd85508ca7461542329d987544ca7561d51329758e544ca7661951329d586544ca3e64d45328f593514ca3e64141328f590504ca7661141329d584504ca7661d50329d587540ca7a60d50329e583540ca3d6595032c798e540ca3e64150329d984540ca7561150329e980540ca7960150328f992530ca3d6494c328f597430ca5d6590c32a7592430cacd6290c32b5586430ca3f6550c32c7951430ca9f6550c32c7d95430cb1d4394832a7593320cad561cc832e350e320ca5f654c8329bd95320cb8f434c832cd952510cb355494432e550e510cb374394432cd50e510cb1d4354432cd951510cb355454432e550d510cb374354432d590d510cb354354432d550d510cb154354432ce952500cb395494032e650e500cb725194032dc546500cb3b4394032ce50e500cb1d4354032ce951500cb395454032e650d500cb725154032dc545500cb3b4354032d690d500cb394354032d650d500cb194354032d6cc9500cb6a3254032d64c9500cb693254032c754f43d06b66190b41c794d439071d5350e41a758f42906b561d0a41c7d4d43506b46150d419798f525065d63d4941ad986425063e65109419798c505065d63141419b988505066d6214141d5986531071e6454c41d5985531071d53d0c41ad587431071e5350c41a758f421071d53d0841ad587421063f6550841c754d421071d53d0441ad592411075553904418fd95411071d53504419dd9541107555350441add9541107376550441add8d41107965350441cd54d41107955350441c554d41106b76250441c
  | 6 => 0x830a1f44ec5b853c97851241480801222c0a6a5297c0001403840000000967ec12400000083e9480f80004d81767c023488853032a1b45e40000003063f61422b06321d00000007a24fa4549649e267095221a0001a442c0000002a60908ea1a80009607aa5262d42380004b05d060a08293e5220306f66681ac0764560000000000000004a800100000d01400000000100000100600300800200000000001100400100000000800000900000000300300100000600600301000100000300000200000000000a00000000100100100000801000100200100000000000400000000f00100000000200501200b00200200000100200000400000400300100300300000300101a01c00000000100300200300500300200200d00300000100100300400200100000200900000100000900000700400100600300000900400800000000100100000a00800000200000300000000500100000000000000000000000100b00100900000000000000000000000d00200100000500700100500000100700600000200b00000000000800000b00400a00000000000300500000000000300001200500f00b00200400000600000000600000800300300700600400000601100200000300200000100300000300300000200300000000100600300400000000600200001500000300000200000b00200d00000200000200400600000000001600200500400100000300200a00300200201b00000600500200600000900000000100200000c00600000000100900101800000200000900400000000100000000300400200000200300100100000000100900000600000100000000000100000100300e00000500400000400500300600500600000000500000700000200700600300001700600800100200000200000900000000000200000100000000200000000400000700000100000100a00000100100300000700700b00100900000100a00400600200600700100100000800d00a00300000800000000500600100200000000000100000600600200000400000000400500000000100200100d00400000300200000c0060000010000020000000000000000000000010000000020020030000049d98652d0e756194b439dd8550d0e746154343ad98752d0eb561d4b43ad98652d0eb56194b43cb54852d0eae62d4743ab58b51d0f355114743add8550d0eb46154343ab98850d0ead6214343ad98450d0eb56114343cdd0e5190f374354643ad9864350eb56190d439d9875250e7561d49439b9885050e6d62141439d9845050e756114143a798b5350e9d61d4d43a75835350eb661d4943ad5875250eb66194943ad5865250f2d5214943ab98a5150ead6294543cd5445150eaf6254143ab1895050eb76154143ad1855050eae6214143ab5885050eb66114143ad584
  | 7 => 0x726a4603873600055c33400000032c1688141be23e05600000088e3ae7840000002ac0a40000009561300800008200000004b400000000000028000000021e9be7e000000000000000000002e000000466a344440be9ee00000068c68e0000000002a20004be00043c3e26208800360001560000000009c60007e200092c4e82764d48449ca0004a000058c0745620008fc0003f294400097200016400067440c7f6248a425f60002bc7440004169420002b40daa4a25237692e4c65ca4e011c0005ce0004f018e00083897e5d84ce2c67406926e46ee3dc39a50a0004400d402095c0000000001ca94e5004ba90444c0000000000007ee00000000000000019800000048099045c2640000002be9c40000008fe05c90200464e3ca16e00000000000089ea40a2c4727ba0b07800e000092000000000000000014e262000a2a53800057600000086446200000000000025c2d20000004485fa1f00648e46b26786dc54800034000000078225075a4f62403702106d200049692a00000000005a64aa145240000000006bc7ce1de00096e8900000000007520006a600096a0000003de8e84941a058856c1e800081c00000000054000000000000000023a00000000020896c16c0000008de1e02707b28e640200037200084a7d80000000000002b600053e00004873800065259a000000a160006d40000000009080000000002240000fa0000426060788a6a6e0001d800000051801c0000000008ca33e00004e2c8556a0200073221498c0007d40dc3b274247c5a287c67c46e0003da0002ee000706298a50000998460a6a8ee4820003b436c13e016000000000778000000a300005ee0008d006689c79e3540000000000000000007c29bc0007702ec0000000000000000005108f433c0008660005944ca9da08e2423a676a8c0a7449a64c97678c8789740000003e800071602428e0003b65c2618000a0600043031e0005da0000000004ee00000027c0000000005b00000002ce0000000000000003680000000000004084f443200060e8160000000005be6ac6e898e61600000000000095a4e20003a070024a48e0000000000000c640a00082600078800000018600065a2b80000c400054c00028a18886023632e5162860000000006808d2542a264c00000004207300003125446ce7100000006f80ea64804a2ba9d661c00040e7fc4d65800f200000044660800029c9e82e46c8602a6c00000000000075c000506192000000000000294a1e1a685029a1965a653673e0a20c07503d66963c654a47891c906a568bc2f236e9b40007869d400080c9180000004a49944106d00009d20005840008565fe5e078a56e3d41180000009a00000000002025820000007ae18000024c5340008620007e89fc76600000000000000063494a6e269e6002d038
  | 8 => 0xc28d63a41360007c463a6d64580542f01b89a47a40de71842844e7621bc82270431a2785f00148b6498a3281e8f04043789dc6ba71e4e48f617868a0000002320000007a6356714a200000f600032299c000000150000000992000000a5e00c5b40729ae3d215e0008925787560000000e200084e0007f000000085409c8e28340003a80000003240008ba2465e20008326306fc4ea71255e0001d64dc1dc00035e03c2685dc23027e1ae0000005720000980000000000000008364c20001ce2fe00016a7f453a3ce65032818a67a94c00086c5c019a09e3265ac8103bc00062c5e800000000004ca1c0001c830849000000000000000000000019ea380006c658e00000067295e9f428c3ee90c80e3525b682e34200000000056873a0005aaa5498415400049c5988c86886b40002c200000086e57442e7be5700005f28ce15c12643a9c2612702132000a620000946140007601483ec20e00080a2d88ec0000000004f81aa79c274a1a8f22da5e60000a04420080000004640000003003c820096600076800000000000000000000082c5465bc00067e0000d200076c4d08a0a4e0444e620a9a622291a1943160000000c80000000004129580000000004b800043400000000071c00000069a66623c76e3466be3b05c670c6869a84de93c0000000004180ee00a00000080413439e9fe0000005086c000006a00000030400000000066a000a00520a5a0000000000000000000000000000001ec7d03d87fe0000000009e4a487b40fe0000868b055041e5cc0000000000000c20000001a25f42ae5de2f87b01eea1000008a17287400010e7469e03a28840606b012c0002120005ea5a88768863806b68b8000000260a0a6ec00079a0000000003be00024e00081a22e954000a040009288da1fa22655aa5c9120006a8120000000a648dc1e60221b20009d01745ec10c00000090e72a06e42a38235c0000002fc5b254e1b636a8fa52a00000074845e058a581c471a0000000003cc5d470849e5966cc9fa6600107a86249620000000000000000000000000000000ba45a00041a3580003e00002de00087a0009cc0000000000003e633057c0000008960000004064bc0001d400059226677c000a220002f600038e00000002c0004706c20d698a0009aa63674a00064200000000030c11e72c6589ce22a00012243819c08c7760006829502a000074e0000008ac0000000b600048a0000000000006f000000000000000064057a0007b60007dc0008520000009a20000002ca00081200000005e91ea7600000048800002800062a8c209a0002560007cc3aa26a60c1384c8a0c0000000ac1149469880006a413c0000000000003ea7280000000008b40000000009dea3e8aa00069c97a0005f88a20000007741c227233a0a80001528a482800090a2cc
  | 9 => 0xc1440000f47bc00000077ea089f60009103965520000000000000000000000000000000000000005589327f21f6000800a126de19012aa3a39214a2e80626ae0cc3ac0000005d200011a000000000000000a0e06c0006a284c0000000008582fa0009704240000009ba3741127e63c000093830e66c00089479412e0000000000006ca7c80000002060001c073434a79659e8820007546a00b21da4860000000d00000003e486a1d2104a2e6649227922205a033603a1fc58a00065400000031c50c000422000a6865e00e0008be0003b80000004c40000000000007e400048c00085c00034499a9b268400052c64600010800000000008445263c18c1fe0520009f21822dc51c89a11620c30293a5601ba0000000000006380000000000003ba2b200002600063e26c8c41ea2846564cc18472e0000005c800060425e85e0009e66623f400029e84270e25850207e4ac9861cc39455481837e00083088a00000017e0000000000003fe13a41c24400000056a6fa59c3666c46b86fe6f443e9b64a200000000034e2e60ec02a2920007729b083c9160b86da0000004d20002a45320003480004b227a17c72275882a3fca664aa7b83865fca722889d80000bc6f23f80003fa6220063c478e0000006900920007a00000000885ba1c60ae0ce00037a0000000009ec16657e03400000058600000000000070a00000000000001a83a000000000a2400000006800000061e00000000038c0000002542c07d60502969c00000ca0000007ea2f40009820000001708c63f000069400038a73c03e00046887085a37c0000000000000000000002e20001062aa59035a4269301029c851431087e000a367da00044a0006765644360000008466440008b27ca3909f87f84fe72400062800000000007a0aa3620003640000005d62161b03204fc46c35000000000049293647e0004a60000007984f204686821839c980a445ae0e615a0000000000000000009f07c60006269b82040000005a40000006d800046a00000089810a4841109ea2a800062e4b60004ae33200277a90000000000000099e76400000000001800000039800075e282000000a6096894017a000000000000a3c50426e0007de6e600000000000066e6ea0006aa52e5c49347d200034c5661f82d600000052816200000088c47a9260700002ea2e00000000000000000000000004008a807c74c14c0008021e42901600004768ae0000004da00000061033899600045021c00000000000050e000a281582c48403187ac8488d40f02286e00e80d83d04740b401e0000000000008e01e2720000000914000000000a1800000065c00025a0000000007900000001f29240000008d8000000000a4c9ac00003214651e7faa708060000000e451a6981280401003608cc82461a0000000008f88723
  | 10 => 0x3140f
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x98c977650f524c782a1aa4292638599543d0931c2acaa1e8498e156550e424c6c239286a12638599543cc93192ee8b046498c9576d0c324c748a1cc019263a4d0d600c931d2286b006498cd170d90324c64abb4c819263a4592600c931ca4cab006498e9264580324c748b22c019263b0989600c931d0a87b12a098e8543189504c64bbb28628263a150e6214131d0a86b10a098e167158e54c870ab8ac72a6438558d6195321a32e029a8790d157395241c868ab9ca8a0e43455ce548c721a2ae72a26390d157550d31c868ab98c2aa443855516310621a2ae72a26310d157494d318868bbaa8698c43455d5434c62192ae73264310c3776553218870b322a790c43855516310521a2ae829a6290e146550d3148742a18c498a43255ce64c85218aae730ea810c1d73992520868ab98a8a08434c5c0545042183ae6322a010c557398652d028ab8ca6a1c81255ce6190a40c2ce8b18a2a06157458c515030ab1e8628a818558d4314540a2ae7a10a2a061563d08515030ab1a8428a81455cc51d0540a2ae628a82a06166550d315028ab98a320281455c65350c4092ae730c8420615539864210312a94c3210818558d4394440c1ac6a90822061563544411030bb2a8698881c150e524c440e0a86a92622049573185401030aa98c2a0081895486150040a2ae232a869858972181434c30aa1ac229261511c9544c530a2ae829262985c172181314c30caa2c019061545c03254430a2ae929a62185177550d310c30bb2a8698861c150e524c430e0a86a9262184557398754c828ab88a6a1e41455d0534c7208aae630aa9105157194d438820eb98c8a8c41455d2534c620c2ec9b0ea69061564584534830cb22c029a41925896014d20ca2c2b00a6905157114d43482863aa87192418558d4314520a2ae62a262905157414d314828b3aa8698a41451d5434c520c2ccaa1a62906146550d314832232c6498a4186195434c120ca0ca98a609061564586530830ab22c2a9841455c65350c20c2ac6a1ca21051573951310828aba4a69884145dd5434c420a2aeaa1a62106176550d310830ab2a8698841075ce6494b10a2ae62a283886175458c418428aba4a698c21255ce64c8610c2ce2b18a8886157158c544430ab1ac22a221455c65350d10838eca9a868850c7254d434420eb9cc929221455cc5490510a2ae62a2828851573152314428ab98a898a21459d5434c51086aec2a4428851573152214430a2a2c710a21455cc5448510a2ae62a4208851573185540428ab8aa6a18218555163104108aaeca98820864563548410428ab9ca898821455d2534c410a2eeaa1a62085157550d3104382a1ca498821c150d524c41092ae7326420843776553210430b322a7908218999152c841092ae6322200843476551100430a322a688021891915244010
  | 1 => 0x2600092000cc5a0013101204600000d8b02a31d1600472546a1f3d800009600000003429800000d0000000000000000002d9f0460000001902f00000a0c9000000000000a000000000000b5000000087000000010000000085000000000000013a00000000000448006205000640000209700000000fd36820001816212e80000ae3a80036006e2a9c00a3180000002cad0eec10200000001c800002a000000000000013200002794ed9000ada8af0000000000006000a100001980000000000033800006b0000000946d38852000000000005e000e800220000000001890c0000308003c2180000cd00000000000001080000000003200000000000001625f000455ac500000186929001be0000001aabe6d8000000001cc000000000000000000000063348fe4800000d04f41a3552000000000790033800000080058002c0014cc40b0000000600000e00000018637000e8aa0000000000025800000017001481200000006601a4c0000000000000000f84400440000017000009c00000000000000014400329840000002fdae003780034000000000000000000ba001240000001f4008a002ad94003200000003000800003d00000000000000000000084000007000001380000470025c004c000000000003840000000011800003596c00000014600268000000000000000120c0000067ab000000000176d86880164381280000004d1f800000015c26000032c00bd0023c0000000000000000007600000000000001c9a600002e04000289b8b46d000000100400000000000000002000020060000e008000081400000000020000002002000000000002000008000000200006008000000000002000000000000800018000000201004000060000000008008000000400000000060200400800014957198b5350e4bb8ac1a9a87455c65350f42c2ac6a1ca3a16167458e5190b0aba2c728c858558f4394642a2ae7a14a32161563d0a5190a8ab88a6a1a85255ce61909428aae630aa02161543d85508cb88a1aa32806546dd54354032e228728aa01971143545500caa4b9486a8065545c64354032a32e9992a01955171cc9500cb84a1c64a8065c2d0d325403292ae730c85a0c95739864250686b94c8a9883515ca6154c41c2aa6b0e8620e1553587421070bb1aa6a088385d955350441c2ceca9a8220c9573d89411070aa9ec4a0883255cc6050441c2aa63028220ca572181411070caa2c01966392549600cb31c2aa8b18a918e9143580328c760992c019463439cb6550d31a28eaa1a8298c957498b534c64bba2c1a9a63319ca6550d31b0ce5b2a8698d8572d95434c6c3394caa1a63615ca6550d31c2aca32a8698d1675d89434c68b3acc4a1a63a15886250d31b0ee4b028698d8472581434c68b3a8c0a1a63619c86050d31b0ae430286
  | 2 => 0x294bc714f83c00b9002dc00000000094000f000ac0000000000000340003604000000000000000000000000000000007850000000048801021d001c02a3d00000d40004b7800a80003800000005166002280000dd001d9388000
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0xe20006821961600a9035400c8aa05829d16394642a05829d95350441c05535c86050441a05829c563953218158799153c8621a05829d16314540c057354a6190840c05735486150040a05829c563151108158715163885108158799153c8410a058399152c8410815871915344010a05831915244010
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 890
  | 4 => 1340
  | 3 => 227
  | 2 => 14
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
  | 7 => packedAt s4K7 (6+((h/1+packedAt s4K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s4K6 (788+((h/14+packedAt s4K6 (704+(h % 14)*6) 6) % 63)*7) 7
  | 5 => packedAt s4K5 (27582+((h/296+packedAt s4K5 (24030+(h % 296)*12) 12) % 2079)*11) 11
  | 4 => packedAt s4K4 (56272+((h/446+packedAt s4K4 (50920+(h % 446)*12) 12) % 2139)*12) 12
  | 3 => packedAt s4K3 (11873+((h/75+packedAt s4K3 (11123+(h % 75)*10) 10) % 581)*9) 9
  | 2 => packedAt s4K2 (860+((h/4+packedAt s4K2 (840+(h % 4)*5) 5) % 17)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfe3ffff0f87ffff830ffc3ffe1c1ffff18f0ff
  | 1 => 0x3fc3e1ff007878ffc0e1fc787e01e38f974c93
  | 2 => 0x3ffc01ffff807f0fff01ff807ffe03f0e78f1c
  | 3 => 0xc00001ffffff800ffffe00007ffffc00f80fe0
  | 5 => 0xfffffe000000000fffffffff80000000fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x2000010008000000002008800402080001025
  | 1 => 0xa498d3223534b189c870e451720d492e934c92
  | 2 => 0x8094444501140125101490224940262258518
  | 3 => 0xa1a29988a44412acaab4204459299804d80ac0
  | 5 => 0x3133110ec66664cf3cd9b26710311048fee000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfaeafaeafaa8faa8faeafaeafaa8faa8faeafaeafaa8faa8faeafaeafaa8faa8faeafaeafaa8faa8faeafaeafaa8faa8faeafaeafaa8faa8faeafaeafaa8faa8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36240
namespace PEqualNP.Outside.L_meta_36240
open PEqualNP.Outside.L_meta_36240.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x550193800f80084c014006c027000078000000000000000440000900000240e0000000a400c026801730ac000000040b4c00011000031200150800000b0050a8800008c1800474f0014012801a0070081000808100040020400002ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21f621fd21f521fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xe617d51cc3be6398774c730fb10e61f521cc2fea9185f95230beaa4617c548c2faa7185f94a30bea9461bf428c37a85185f94630bea8c61f6218c3ea43185f94230ef98461fb308c2fea8986fd51309faa2617e544c2faa8985f15130de2a2613c544c3bc86987750d30bfa9261ef524c2dea4985f14930f6292616c524c37e84986f50930ef99261dd324c2fea2987dd4530bba8a617c514c3e8a2985d14530ef98a61dd314c3ec42987d48530fd98261de304c2fea8185f95030df2a0613e540c2faa8186f550309eaa0617c540c2fca6185f94830f7290616e520c2faa4187b54830b6a9061bf420c37a84185f94430fb2886176510c2faa2187d54430baa8861f6210c3ea42185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c82faa7905f14f20dfa1641ee42c837a85907b50b20d6a1641ee32c83da65905f94720fb28e417651c82faa3907d54720baa8e41ef21c83ec43907b48720fa90e41e521c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5106fd0a20dea1441ef32883d865105f94620bea8c41f621883ea43105f94220fd18441f930883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20dfa1241ee424837a84907b50920d6a1241ee32483da64905fd4520be28a41ef21483ec42907b48520fa90a41e521483f460907e4c120fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4106fd0820dea1041ef32083d864105f94420fb288417651082faa2107d54420baa8841f621083ea42105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10dfa1621bd42c43ec83887d50710fb18e21f531c43ec43887d48710bfaa4217e54842faa9085f15210bfa9c217e53842faa7085f14e10bfa94217e52842faa5085f14a10dfa1421bd42842faa3087dd0610fa20c21f731843e863087d88610fa90c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a217e53442faa6885f14d10bfa92217e52442faa4885f14910dfa1221bd42443ec82887d50510fb18a21f531443ec42887d48510fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c520437e84086f50810bf28821f741043e882087dcc410fa18821f621043ea42085f94010fb88021fa10043ea20087e44010
  | 1 => 0xd548c77aa918cf55231be2a4637d538c6fca518fb94a31b7294637d528c7daa518db54a31dfa1463bd428c6fca318fdd0631fa20c63df318c7ee6318df94231bea84637f544c6fca898df55131be2a2637f524c6f8a498efd0931dea1263f7414c7e88298fdcc531ef18a637f504c6f8a098dfd5031bf2a0637d540c6f8a818df94c31bf290637d520c77e8418ef50831bf28863f6410c7ea8218f7cc431fb18863dd310c7ea6218df94031bea80637f54c86fca990ef953219f2a6437d54c877aa990cf55321be2a6437f53c86fca790df54f21be29e43bf42c87dc8590ef50b21f6a1643ad42c87de6590fb0cb21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510efd0a21dea14437e51887ee8310fd90621faa0c43f441887ee6310fd8c621fa98c43f431887de4310fdc8621bf284437d50887eea910fd95221faaa443f454887eea710fd94e21faa9c43f453887ee8710fd90e21faa1c43f443886eaa510fdd0a21dba1443f642887ea8510ed50a21fa21443f732887ec6510fd4ca21fa19443f750887eca110fd54221fa284437f54486fca890df55121be2a2437f53486fca690df54d21be29a43bf42487dc8490ef50921f6a1243ad42487de6490fb0c921fba0a43f641487ea8290fd10521fb98a43f631487ea6290fd0c521fb90a43ee21486fea090df14121fbaa243f654487eaa890fd15121fba9a43f653487eaa690fd14d21fba1a43f643487ea8690fd10d21fba9243e752487ee8490edd0921fb21243e642487ea8490ed50921f2a1243a542487e88490fdcc921f399243f632487ea6490fd0c921f219243f750487eca090fd54121fa282437f54086fca810ef950219f2a0437d540877aa810cf55021be2a0437f53086fca610df54c21be298437e520877e8410ef50821bf288437651087de4210fd88421f690843f521086fca010df54021bf29e817d53d037e87a06f50f40bf296817d52d037e85a06f50b40bf28e817d51d037e83a06f50740fb10e81f521d02faa9205f94e40bea9c81be439037887205f94a40bea9481bf429037a85205f94640bea8c81be419037883207d88640fa90c817e509037e81207ed0240bfa9a817c535037e86a06f50d40bfa92817c525037e84a06f50940bfa8a81f751502eea2a05f14540fa28a8174515037e82a06f50540fb10a81f521503f680a06f90140bf2a0817e53103bca6205794c40bea9881dd53102baa6206f90c40de218817e52103dca4205b94840bea9081ed52102daa4206fd0840dea10817e51103eca2205d94440bea8881f551102eaa2206f90440de20881f621103ea42205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30dfa1661bd42cc3be6598774cb30bf28
  | 2 => 0x20040080800200400004004018008000180000080100a0100280100001c000080060080280800c0140480200201c008080060000000900c0040080100001000000004002fca5a1fb94b43b7296877d52d0fdaa5a1db54b43bf28e87f651d0eeca3a1df54743faa8e877551d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321fd94643bb28c877d5190feaa321dd54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43bf290877d5210efca221df54443bf280877d5010efca7a15f54f42dfa1e85be43d0b7a87a16f10f42bf28e857d51d0afca1a15f54342dfa9e85be53d0b7aa7a16f14f42dfa8e85be51d0b7aa3a16f14742dfa8685be50d0b7aa1a16f14342beaa4853d5490afca7215f54e42bf29485bf4290bde85215f94642fb28c85765190afaa3217d54642baa8c857e5090afaa1215fd4d42be29a85bf4350b7c86a16f50d42de21a85ef4250b7c84a15fd4542be28a857f5050af8a0a16fd4d42df29a85bd5350b78a6a16fd4942d7a9285bf5150b7ca2a16f54542de28a85bf5050b7ca0a16f54142de282857e5410a7ca8215f94c42bea98857e5210b7e84217b90842dea1085ed4210afca2217d94442bb288857d5110beaa2215d54442bf280857d5010afea9995f95332beaa6657c54ccb7e85997b90b32dea1665ed42ccb5a85995f94732bea8e657e50ccafaa1995fd5232bf2a465be548ca7ca9195f55232deaa4653d548caf8a9195f54e32bf29465bf428cb7a851977cca32f7994657e518cbeca3195d94632bea8c65f5518caeaa3195f94232bea84657f544cafca8995f55132be2a265bf424cb7a84997bcc932ef192657f514caf8a2995fd4132be282657f540cafca8196f950329f2a0657d540cb7aa8194f55032be2a0657e530cafca4196fd0832f721065bd420cbda84196b50832ef99065ee320cbba64197b4c832bf28865f6510caeca2195f54432faa886575510cafca0197e94032bd280657d500cbf2a0195e54032bf29e837d53d077c87a0ef10f41bf296837d52d077e85a0ef50b41bf286837d50d06faa920df94e41bea9c83bf439077a8720df94a41bea9483bf429077a8520df94641dfa0c83f741906fca120df54241bfa9a837c535077c86a0ef10d41bfa92837c525077e84a0ef50941fba0a83be41506fea0a0df14141bf2a0837e53106faa620efd0c41dea18837e52107dca420db94841bea9083ed52106daa420efd0841dea10837e511077e8220fd90441dea0883f5411076a8220df94041bea80837f54cc6fca998ef953319f2a6637d54cc77aa998cf55331be2a6637e52cc6faa598efd0b31dea1663f641cc7ea8398df94331bea86637f548c6fca918ef952319f2a4637
  | 3 => 0x10e05e90c00000148000000000000000012b6d69600000000000000000000a4400000596dd8001e8000001b980022a61561aa32e23f400307266000000000007b5690001c842c000d0296d60000000000015d000000424ee80062a0a0000000000018a148000380a906a308000002fb67200086800000ac8000000000012a8140220700000043a8387b8863b600164000000000953310000180000064a000000000766b40017051c464cb0cd000000000fc2f00008500d0005bd4a8003166d44d8006d000184a64374c08002e0000000000000000015a80000000179b6d056000000006825295a0005f0000000005c22942012e2740005d8000000000000000005800000000000000eb566a09760000000159580000000000000000000f886100822cd417c45c3c0cb89a5628b4000000000000000000002400000000000000003ceb6412000000728002c00e09bc0000050261d5b8000900f104a575d2ad8ba1a063000000205434119742fd15e0002d24a65a001528005e01440017a1a2588b40002fea718f800000001340c250a4580000000000103860382000000005408f90686b00098c00000556000000005080006d28d228000d600019c000000005b60000c219000001b1a984a8c38378172e6644b71d30004f800138000000000000004c000015000000001cf4d80012e800506bd0cf80069a5907c9060d84980000043e29d9b8003a21e80036767c3898789529cc70002702ac00000b743e8000001545328cc9da9f4680e9120ea330be40000068c0013b00000027c000000002ac0026100000000000000d94000004240000000062689d818194a0540d3a110267f43fa4e00060c0813f0bc934000121d8000078b06de0000018900000000027000000128e14423d400000000000b08932b832c001be2faaa000000112790d2000000000001b33140011d8010000080000000001e008028050000000000000400402800008024000010040080100000e00000000000004010010000080100100001801000006024000000060180100000c008000010020100080400000001005004014000010000000000100600000800000000008000020000000000e01000002004004000010020000000100800c00801000000020000040000000100201000800000004000010020040100100e0000000000000003001004004028030000040080000200000001000004030030000040300000a000010020020000080000002c008000060140180600200c01807000000018030000080000500a02c0280100000000006000004000060000080100000c000010000000000000000600400003006018000000140000000100a00000000004000018040000040000e0000200280200200000000002020060000040180000000802800803002008000010
  | 4 => 0x33a361982690000009e252610578001510006f0001b66e46319eb1717200000000000c641fb7831e000000000007f80020808a0005ea0214220c001f72882e12319457000000000000000000006cca68002350002340019a0000000019957a7e000000000000000002c6bf000000000d64000000827ad6480000000000306000164000004eaa6c1c2b00000000016b60a378000914be2b01705f3fe000ec80017400000066000b4c180e6262d5c001d2000000001cc0000001b992000000000000000008380000000167975000ced3c9a926400079a786dc1dd66a5a66a7990a2d10d0078002fe362698ef88721031000000000160d09aa20800000000364a4c002770e600000000000000fa80051e000000000000002b000484404b934c1327783399017c9014a34738c00117800000c8c7400029e3ed51000138001850000000012400000000000000000000f980c09c000000a900000000370664ca00000035e001350000000016a90368a00000000000001650000000000e85b000758df8000001f43a8b20000000023c00000000000000000800000000010b0000000000011e000000000d4180000bb800000000000000000011d14605a00115ac24e24890b9f637ad3800273346000002c10009fc192bb3c4de5759d53440000000000086c00105000000000005108d8acb4300000000000000af800000000c58001ef06a000000000007093a00000031c000e723a408bcaa4000000002d63360013f0000000d8000004ce00000000000001310000000000022a66c000e00f4130c90000005ec000b68006a60014600000000000000000000001810880000036a00000000000000001370000000000035a0dc000258070006e051800000000002dd6ea001060002d843c5700000000000351000000000000008f400000000000000000000005a000000899ab000000c68000000000000000000000001a13000594001391d20008608a690bb89400063c0019089d0c810cdd8000000019522900086000000000000718000000014f03e0000018d80000092c239da15adb1030c957e9440020f4f40009b143000829a780062019400000000c44661e30003b4c998809e1e53e1101b8bfc7b14d420a74001550004a56809000059d4b0001b60000000065ed498580b0008c1331c9110001790001b2b9c0011b1e49255632c48a00186a040e82a07285300000000000000000938003c28c4e82591f40010e253000b386a80000000000326000d00fd00000028000000000000000000007e4000000fc0016c000042c74abb386b6c0553800000dc41eac60c64d52f05c0002580007b000000000004fa001bb80000000000000000000000006aa96ce718e000000000264acaf04f0000000a40001b0005f956aa9000000ce0000000000001a0001b527ac700
  | 5 => 0x920000026d0000000000000000000000000001160001a471497a001ac58000000000a400000016c0017896600030c0000043cbe8c126b1e20000008109a000003225ca7b80000048e0017208f0000014000000079492995000ae400072000cb865000000ccc0002c444000100ee00000000082000a98000000f8001a101f25a72c513343aec811cb6412ea5d768b75889709a1760000016f8001fe00000232000000001fc00080c0000029200062800000000000000840000000036e00000000696c10002d74880002a28a0008dc002ef06247c3880034a00000000000000001210001740000000021000000284029b000000000090000000000001ab3e00203b000000530000000aa000000696a0000000000000008c0003d80006f8000007340011a000001629c41624dc002230000000000000037400000000000001dc000000bd8004824459f8c6000000000c1000a18000000000000000000070d71945000000a0800598b518615d19e00000362000000ea0000006e56e287600000a0000000000f505222e8e0000780005611f9803d20017b8000000000004a36800112af500082c0000064e00000000000000002e249800150800000000000b317e00000000118000000000000006422867400077892000980000006bcab89205006851c5e00000000000000516000002aa51200000000000000000d35bc994d8000000a485300011c000e41ae2b4000003490460000015f3b0da4401c705444cc30222a67c87c32927acf00711c5b4000550000000000027b0000005a96a6a8d10b49230ae001afaea0009c9102e600000026039066000000000000004a0850004b0010006c2001ae0000000000019e31a000001e03f600000062000854000fe55ed74000002b60006bb1269444900800
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x5200832d5448020d354d200836551480209ed95200835953480209b98854c426d62153108f99353c423d64d4f109b98b53c426d62d4f108f99253c423d6494f108f99252c423d6494b108f99052c423d6414b10cb94942c432d5250b10cd15141c42b5648c710b958a31c43655288710d9d4921c43a542487109798c548425d63152109b988548426d62152108fd91538423c6454e109bd89538426c6254e108f990538423d6414e109b988538426d6214e108f992528423d6494a108f990528423d6414a109798c528425d6314a10cb949428432d5250a10cdd5041842e56210610ad99331843665248610d954921843a542486108f58b544423e64951109dd85544426e62151109b588544423e6515110ab588544432e62151108f588544432d62151108b588544433561151108f992534423d6494d108fd91534423c6454d109bd89534426c6254d109dd85534423e64949108f592524427561949108fd91524423c645491097d8d524425c63549108f990524423d64149109d984524423e65d09108f197424423e65509108f195424432e5250910cb54942442766590510cd15241442746550510cd1514144276658c510ad5923144334548c510b958a3144274654c510cd15131443375488510cd15221442746548510cdd5121443345448510d9d4921443a54248510cd152104425e63d50109758f540426e62d50109b58b540423d65950108f58a540423f6255010cd185540423e64150109798c540425d63150109b988540426d62150109d984540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c10d5185530423e6414c108f590530425e6314c109b988530426d6214c109d984530423e64d48108f593520425e63d48109758f520423e64948108f592520426d6594810cb952520432d5494810d394e520434d5394810cb992520432d6494810d998652042756154810cb951520432d5454810d394d520434d5354810cb991520432d6454810d9985520423e64148108f590520425e63148109758c520426e62148109d984520423f65d08108f597420431e53d0810c754f420432e52d0810cb54b420423f65508108f595420431e5350810c754d420432e5250810cb549420427565d0410cd553410435553d0410d954b41042756510410cd55041043555310410b9588410436552104109d59731042b664cc410cd553310435553cc410d954b3104275650c410cd5503104355530c410d954831042756588410cd95221043355488410d594e21043555388410d954a21043365448410cd55121043565348410d554d21043665248410d954921043a54248410cd553100435553c4010d954b100427965840109dd9510042b46444010cd55110043555344010d9549100427b6544010
  | 1 => 0xc3355448430d9949210c3655248430e9509210c31d54cc030d354b300c35551cc030da54a300c25f654c030c7551300c34d524c030d5545300c27b654c030da549300c27661d53209d58754c832e62953209d98454c827561153208f99353c823d64d4f209d98753c827561d4f208f99053c823d6414f209d98453c82756114f20b958642c832e5450b20abd9542c832f6550b20cb94d42c832c5350b20ab59232c82e5618cb20cd95251c83355494720e950a51c83374294720cd50a51c832d4254720cd95151c83355454720e950951c83374254720d990951c83354254720d950951c83254254720ab59321c832d54c8720cd95221c83355488720e950a21c832d5448720d994521c83365448720cd55121c83a74248720e950921c82e76548720d9d9521c83675448720e995121c83655448720e955121c83255448720d994d21c836453487209dd85548827461552209798c548825d63152209d984548827561152208fd91538823c6454e209dd8553882746154e208f990538823d6414e209d98453882756114e20ba580328823f64546208f19151883a54248620ba18930883cb324c22097d8d544825c63551209dd85544827461551209d984544827561151208fd91534823c6454d209bd8953482776154d209d185534823e6414d208f59053482766114d209d58453482ad6490920b9586424826c6550920cbd95424832c6550920cb94d424832c5350920ead8142483a860509209b99632482ad648c920b9586324826c654c920cb50b514823e64145208f59051482ad64c8520b958a21483a54288520e9d0921483a54248520d9d5121483655448520d994d21483645348520f8d8121483e06048520ea50a30483e1218c1209e19530483a9424c120f24c930483e1214c120ea50b20483e121c81209798f540825d63d50209d987540827561d50208f596540823f62550208f589540823e64150209798c540825d63150209b988540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7951530831d5454c20d3189530823e6414c208f590530825e6314c209b98853082766114c209d584530827a6014c208f992520823d64948208f597420831e53d0820c754f420823f6550820c794d420831d5350820cb949420826d65cc820cb553320834d53cc8209b594320832d540c820d354c32082e9600c820cd95251083355494420d594e51083555394420cdd0a51083354294420cd95151083355454420d594d51083555354420cdd0951083354254420d9cc9510836432544209d59621083365488420cd55221083565388420d554e21082776548420cd95121083355448420d594d21083555348420d994921083a54248420cb553200834d53c8020d9547200835953880209bd9
  | 2 => 0x5250840d594e51103555394440d994a511036552944409d58a51103374294440cd50a51103565354440d554d51103665254440d954951103364354440cd10d51102776254440cdd09511033542544408f596411031d5390440cb54a41103355190440c754c41102ad6210440cb548411033551104409dd9621102756588440d594e21103555388440d994a211036552884409dd9521102756548440d594d21103555348440d994921103655248440e9509211031d53d0040cb54b401033551d00408fd95401031d5350040cb54940102b46150040cd545401027b65500409d98754cc27561d53309b98a54cc26d62953309d98654cc2756195330b558643cc23e6494b308f59252cc2766194b309d58652cc38d42ccb308f99251cc23d64947309b98a51cc26d6294730a759331cc3a54248730f1cc921cc27761552309d185548c26e62152309b588548c27661152309d584548c23e6494a308f592528c2766194a309d586528c32e5250a30cb549428c23f64546308f191518c3665248630d9549218c3a542486308f58b544c23e64951309b98a544c26d62951309d986544c27561951309bd89544c26c62551309dd85544c27461551308f994544c31d63151308f588544c31c5490d30b5586434c25c6550d30cbd53524c32c54d4930cbd93524c32c64d4930d9d87524c36461d49308f990524c23d64149309d984524c2756114930cbd50524c32c5414930cb990524c32d6414930d9984524c3656114930da580524c23e65d09308f197424c32f52d0930cb14b424c23e65509308f195424c32f5250930cb149424c34c52cc930e350b324c33754d4530cd153514c36752d4530d914b514c27562d4530cdd0b514c33542d4530cdd50514c3345414530d9d48514c36452145309d588514c3374214530cd508514c29d64cc530d5147314c27665885309d196214c3375488530cd152214c3675288530d914a214c27665485309d195214c3375448530cd151214c3675248530d9149214c3a54248530f1cc9214c26e62d50309b58b540c27661d50309d587540c23d65950308f58a540c23f62550308f990540c25e63150309b988540c26d62150309d984540c27561150308f992520c23d64948309d986520c2756194830cb952520c32d5494830cb992520c32d6494830d9986520c3656194830cb951520c32d5454830cb991520c32d6454830d9985520c36561548308fd97420c23d65d0830cb94b420c32d52d08308fd95420c23d6550830cb949420c32d5250830cd952510c3355494430d994a510c36552944309d58a510c3374294430cd50a510c3365454430cd551510c3665254430d9549510c2776254430cdd09510c33542544309dd96210c2756588430cd952210c3355488430d994a210c36552884309dd95210c2756548430cd951210
  | 3 => 0x121cd55054486b664d4d21ad59353486b66494d21ad59253486e56294d21b9d8953487555314d219d997434867565d0d21b998b43486e562d0d219d99643486756590d21b9d8943486e46250d21b998843486e56210d21b959352486e663d4921b958352487a752d09219d99642486b56490921b999642487666590921b959242486a56490921b998e42486e56090921e9d8942487a75250921b999542486e46550921e9d9142487a75450921e915142486e46350921e9d0d42487a64350921e950d42487a44350921b9d8142487a76550921e999542487a56550921e919542487a76350921e998d42487a56350921e918d42487a75350921e994d42487a55350921e914d42487a76050921e998142487a56050921e918142486766510921ad99042486e66210921e950842487a742cc921e950b32486e665cc921b919732486e764cc921b959332487c753cc921f114f32486e560cc9219d99632486b6648c921ad59232486e6628c921e950a32487a5424c9219d99432486b6640c921ad59032487a7420c921e950832486f2600c921bc58032486e6650c921d999432486e7640c921e999032486e5640c921e959032486a5640c921b998c32487c6630c921f898032486e5600c921f858032486e1600c921e950b50487a54294121add9150486b46454121b5d8d50486d46354121e950950486b66414121ad59050486d66314121b558c50487a542141219d987540863d65950218f990540866e62150219d984540863e64d4c218f593530866e62d4c219d987530863e6414c218f59053086766114c219e98053086796014c218f992520863d64948218f597420863f6550821cb94942087374294421cd50a510872d54c8421cd952210873554884219bd95210872d5448421d994521086776548421cd95121087355448421e950921086766194f409d58653d02ad62d0f40ad58743d02766194b409d58652d032d52d0b40d994921d03655248740e950921d026f6254e409b18953902776154e409d18553902b66190e409d98652902756194a40cb949429032d5250a40ab58841903665248640d954921903a542486408f99743502ad62d0d40ad587435027661149409d584525032f52509409d58b515033742d4540cd50b515026e62145409b58851502e56214540cdd0c51503354314540d998851502756214540d958851502656214540cdd08515033542145408f997415033451d0540cd145415027665885409d196215027665485409d19521503a54248540cd146405023d6590c40c754e43102b66190c40c754c431027661948409d586521034e5394840d354e52103666194840d9586521034e5354840d354d521032e6454840cb90d521032c4354840d998552103656154840c794f421031d53d0840cb54b421031e5350840c754d421032e
  | 4 => 0x954941106b46050441cd505501066e62953319b58a54cc6ad6295331cb98a54cc63d6295331cb58a54cc62d6295331cd58654cc63f62553318f99252cc63d6494b318fd9742cc63d65d0b318fd9542cc63d6550b31cd95241cc73654507319b98b548c66d62d52318f58a548c63f6255231cd185548c66e62152319b588548c63e6494a318f592528c72e5494a31cb552528c72e6494a31cb592528c7666194a31cb951528c72d5454a31cb991528c72d6454a31d9985528c63f65d0a318f597428c72e52d0a31cb54b428c63f6550a318f595428c72e5250a31cb549428c73554d0631d954b418c7355410631b9588418c7655210631ad993318c73554cc631d954b318c66e62951319b58a544c67561951318f990524c63d6414931cbd49424c72c52509319d997414c6766510531cd550414c6e56210531ad993314c63e64141318f590504c66e62141319b588504c67661d50319b988540c66d62150319e980540c67960150318f992530c63d6494c318f992520c63d6494831cb949420c72d52508318f992510c63d64944319d596410c6776550431cd151410c6b5648c431b958a310c65f654c4319dd95310c63f64540318f191500c72e62953218f99353c863d64d4f218f99053c863d6414f219e98053c86796014f21cb95142c86af6550b21cbd9542c872e5350b21cb14d42c872d54ccb21ab59032c872d540cb21d354c32c86e9600cb21cb50950c865e63d52219758f548863e64d4e218f593538863e6494e218f59253887345450621cd55041886b664cc621ad59331886b6648c621ad5923188755530c621ad99321886b564c86218fd91508863c6454221b598f54886d563d5221b958b54887355415221b958854886b664d4e21ad59353886e562d4e21ad99253886b56494e21d554c53886e56214e219d997438867565d0e21b998b43886e562d0e219d99643886756590e21e9d8942887a542cca21ad99232886b5648ca21ad99032886b5640ca21e950832887c5320ca21bc98032886f1600ca21add9150886b46454221ad99050886b56414221b598c50886d563142219798e544865d63951218f993534863d64d4d218f992534863d6494d21ab59242486e661909219b195424872f6550921cb195424872e5350921cb14d42487a76150921e9185424866e65cc921ab59032486e6610c921ba580324867665d0521b998b41487a542d0521e950a41486746550521cd15141487a54250521cd55041486e66210521e9508414867665cc521ad99331486b564cc521e950b31486b6648c521ad59231486e6628c521e950a3148674654c521d514d31486e4624c521e950931487a5420c521ad99321486b564c8521e950b214872d42d41218f990504863d64141219798c504865d6314121b598e54486d56395121b958a54486e76255
  | 5 => 0x43d0b1d5310f429dd8550d0a746154342ab58b53d0ab661d4f42ad58753d0ab66194f42ad58653d0b1d5314f42ab58853d0a9e63d4742a758f51d0b355114742add8550d0ab46154342a798c50d0a9d6314342ad98450d0ab56114342cdd0a5190b3742546429d9875350a7561d4d42ab98b4350ab661d0d42ad5874350ab66190d42ad5864350b1c5350d42ab1894350ab66190942ad5864250a5e63141429758c5050a7661141429d5845050ab661d4d42ad5875350aad6294d42ad9865350ab56194d42abd895350b1d5314d42ab98f5250aad61d4942ab5835250a9e6394542a758e5150b355114542a7d8d5050a9c6354142add855050ab46154142a798c5050a9d6314142ad9845050ab561141428fd954210a6f6550842cb9514210b374294442cd50a5110b374254442d99095110b354254442d95095110a7661d53329d58754cca7661953329d58654ccae56190b32cbd9542ccb2c6550b32e3d8d42ccb8c6350b328f99251cca3d6494732cb50951cca3f64543328f19150ccb2d42543329dd8550cca7461543329d987548ca7561d52329d984548ca756115232cb553328cb365494632cd552518cb374294632cd50a518cb365454632cd551518cb374254632cd509518cb6732546329d987544ca7561d51329b58a544ca7661951329d586544ca3e64d45328f593514ca3e64141328f590504ca7661141329d584504ca7661d50329d587540ca7a60d50329e583540ca3d6595032cb98a540ca3e64150329d984540ca7561150329e980540ca7960150328f992520ca3d64948328f597420ca6d6590832ab592420cacd6390832b9586420ca3f6550832cb951420caaf6550832cbd95420cb2e5350832e350b320caad648c832b9586320ca5f654c832e3d09320ca6f654c832cd952510cb355494432e950a510cb374294432cd50a510cb2d4254432cd951510cb355454432e9509510cb374254432d9909510cb354254432d9509510cb254254432ce952500cb395494032ea50a500cb725194032dc546500cb3b4294032ce50a500cb2d4254032ce951500cb395454032ea509500cb725154032dc545500cb3b4254032da909500cb394254032da509500cb294254032d6cc9500cb6a3254032d64c9500cb693254032ad98643d072d52d0b41ab58b43906b561d0e41cb949429072d5250a419b98b535066d62d4d41ad986435063e6510d41cbd4942506b461509419798c505065d63141419b988505066d6214141ab58b43106b561d0c418fd9543107666194841cb991521072f4354841cb50d52107666154841cb54b42106b561d0841cb949421072d52d0441ad592411076552904418fd95411072d52504419dd9541107655250441add9541107376550441add8d41107365350441add8941107a65250441cd54941107a55250441c
  | 6 => 0xd83b03c2648e39540158c780022d0651e3a5780016b87a0ac8e31cc0d214802e80001d80028087980009910399a0001d9a5f06122b83ca7680014e0d980580000000902d0119b48ed96d1eba1e2892629560690d90000f60578001c283123d8260000c51241081fd01a22f8c90000da80000019d10e00018e8001671711d327411189e18a8000001a11ee02a80000000d2540ec8468f5863a7f9c329100022387795a9b10b69468e59120a71d68002771b516f99007c1b913189b9698e980000c0a20080200800400c038130120000b83102e0041980100201800000000010040020660dc0202000000c020020020480701d0020400000100200000800004000008050200ac02000006084008000020040000d05000400000032000080200020100180200203001003000000020040200040b80e002000000000020000a00201a054128020200000081500a00400002014004018070000880b01e0180140082f0260081100c02a00401814002050000070020040780000005c0200200801800000000050018110020380180301608c01001002000010020060000080002805c0000200002c0d80408400c0000c0040000000000c0f406003002014030240060040480e00200c018230340200000900e01c008120000140181f000030000040000040080601800002815002004000030000200001d008038050020200280000500c014070040000081280600400c010090000040000009a01800039002000000000040000400a038004008050020281d00000a04c0500000202800807018010000240020301902d0120100100300400c0000100004400000012020018000c2038090020680000180e0000040101405601000801004044008000040000d819000004010050040000500200c00001808004004030020040180500b0040040601200a050218010040081284a00c034008310060040000202009c0080000004c01800010020148010020501682200000c050010080000000700800405025026000080090280040600501a07c0000102a0080001e016010058000460b40400101002c0100200e0280080401200000012004004010260060140080502e0080480000001c0180b9d98652d0e756194b43d998652d0f656194b43cb99152d0f666154b43d958552d0f665294743d954a51d0e756294743d994951d0f6552547439dd8951d0ead62d0e43ad5874390e766194a439d5865290e6e62946439b58a5190ee56294643cdd0e5190f6662946439d58a5190f6562946439958a5190e776254643ad9864350e7661149439d5845250e6e62141439b5885050e7661141439d5845050ead62d0c43ad5874310e3f6550c4397d954310e7661948439d5865210e7761540439d1855010e766194f429d58653d0ab661d0f42ad58743d0ab66190f42ad586
  | 7 => 0xe92b02b1ab8c397582da5fa8691d82118498e09715580c13c8000002479d409d8000f10f28b983f9660c11e59191010c88001af1971850001ed90b000033814906a158e60001b080009a00008793b99c8eb9dca178ff0ae9dd2050001a41bba5600000000f0f48b72070c680023fa7e81d00025d86800888129a84b00010720893d9f40001eb1e7919a3092d0822079048361c381f0000a58d3a7493a9dda019532838cf80500014e9578951d180007e21a93601a9898a194308680014980000608b8df8b28000001e200000000010182f8841fa14003309180e0d29f49fea978c41c50470af9d11931bc1348539159c89de23c2368988560cea5215f25c1611689e417714d1411c68ba0711502279e3113017996a4d16c8e1a0427500026927f1040c196a87302f1fba9d8000458b12268000138522790001791a796a0d48e123a83f035a7b08f9f201f83aa990000bb2400e28d80db0100000001599050b39058e885a0920001259d50851e49b386a95a0c724125809408a0ee0f01640581a00da16f123024a921ee80027a953a5380003e14f9e9800118a1f1378f991d0ec10d252a271f01210e00000d59fc1859a88001aa0f086c8309228002569170000001f68598000e91d3848a7d26c20200000000000023d0001911d20a40001078ea07d0001f90000ee8592421801339d90ad0d1a4406e80180b00020623e26b00026217209b0c49718131708ce02512a0000a3285263a4c0c308c28717c06591f0000000cba299c18000b88002101f88000000000000dc00004e04d2350002721981f10ffa6890210c9328c29c62518e81ffa499e62899282321f391e9ce11a80006608b0412940002391e022a2129a38020168f7a8b14a000000234864245208233a09a9b0122668de0001f1a0908c80f8df18617d2572932988289461f7a610b223722801c9998219bf9768670a2a388dd9c085f1938fd85320492518188e1f70baa5b8901161ae0ea9b722127e00112093d1af8e6a8e9ec00014380006b99d80011ba9c25b00009c1742928512240081ba00026e80018d04780005518b81705e9990379568dc9ba99600013002b84b87f26320a9da00024287c9351a51b221f8f319524605690e89f26592b8c5909a3286d8b780007407700000018700020f80000000022597e8769691bb17b80007195d03714c93084a1331e6a490b01380ed00028307000a1752510001d600013c26992c91013f0000549aaa9380018900003202c106000284202a2c15e9c4a4318797f80006f8c80af25e0b18000fe1bc9390000a91a725d1d098c80398c1639d48000389009518481b30000be1ae9450fa15f8c20cf0fc844a3f0002608000000000e42758000b3000080a4080014299f9dc19400000000012900021b96d948a2c8000000001521d8a9a1faa801ec90
  | 8 => 0x85a41a6fa331f629814706007aa1088ea819a9a038bf1b28d09b9a6604910c18f1509c58541810930bc14ba879b7883a8c9449f997291b16223118d9a68190a80c086982400023180b9ac1db04f1271d71cd00000004386a0bc8000b519ba7c8849d784c964928800282a1b03000002e2949b593e0401978000002961ef23e97d9cd992991a700000000889f32591a0a25188a72a1880000009d000095800000025a6189a9510000f180017e192093a548b827a1c016b05b9e10000db962a1121806480018f800000015000032a8f80007484c20580000000019580005e00000000000000014d80000005880027ba6ba468001d02340bf8ab14180008f0002671820001ab2229f580da9ca4e2360231809149588002810000000a624d8b4a5e9bd10f02a07385b1cb97f004a382010a201e2130500222888d30e498304f9fe182a2006d08605d20e1218a3a9987626c8421779bf23a0ef80029500028a066842a71a2217889297397c9320fc15b17800000012e0001608000cd8f4100200052a9d183a190bd8451ca0bba43a0a1cb05a97aa4c9c7a881a200025319b00011406f1ef93a1be12611800009e81819a81996180012a8ab8aa07b14095709690a0078f39c4034a3b03d1601b41029e1a8a955023a5028626d9c106b1b02248ef1cea3c9c20b401c0a509481420c8bea449df80304324f9e88dd0381ad87e90f98a0751590911a280020c0040000571caa0b80006e1678f728f115211a598831c9a1ea821ac80026e09f94f22600000021998b0001cc80020ea1222187d9be83b99e04a8791112602731a315e0128818caa678340e21440440002651650cd11c8001f50d50000002971e800014c1ea0000000000000001a583992217a0001358001989f08001bda4a0630981108b58fe93e800250a3b8d10c98290800d68068f881b09600011c00028b89c89080012e8001528000fa80000005580011f8000000000d6000000041a6a27600019c1a92030d7831a289478000870280fd1762208ca07b8780000001d2875a170bd0a795c03e8000000000508000000000001200618001169ea8002968ad8009b68b925ca8d96e90b9e700000000018426822e9420f801e8a99138cc190882a301b18fb9de83692c24ea6f0268c01459a61129d800c9df02780aa0681b8000f51a48002708d404ea1c0ac186a6a849a7882c80713100021693b1490001e512d9fb12f1da91a1880b0a95a3599f24886c1ed2739a81d59cf89786084d87f95ba8c16c03d9398d02900d8a2f0b600021ca0d85d80022b15c80005c168277a398000aaa4f26413880002700017b07293fa2e020000000078a4719ea7d9f808983a0000dea918001ad20f2780f90720000460000a88298518001f280014a8ae0000e722310a994a4b9731ff08aa0d1db8a48eb00021d214903
  | 9 => 0xf211e0679b881614b0a1124a90a8d1e288816e25a0e7a9b84088d800255a5a870958085a7985ca150fb24808901896308d0000cc917a0b0a092f80015d8099cf27102085f8350629340001b82458028229e08e5039258a138109268001c9000099966a4b0110000000000001278000cb21627c2849088001370621fca4a9299c80f68c6237974a2d90921a068a551798d71369fd954a8e0e08a68a026d21da00a141701a19c71659b622aa291e9123a
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x90c2e7694d42486923aa84a0a43295d2628c52194eeca146290ca574189314871232a8498a43c114d424c52194ae5326a690ca57498f5248653ba2c1a9243319ce6550921a4ceba1a8490e846350d42486c339ecaa1243615cf6550921b0ce732a8490d85739954248712b28caa1243499d76350921a4aebb1a8490d267598d4248692bacc6a1243a158c635092194ceda9a8490ca67694d4248652bb4a6a1243c154c5350921b0ee6b028490d847358142486933a8c0a1243619cc6050921b0ae63028490ca57499732486333aec99924329dd160cc921c4ccaa146490ca576d083248750a14c019243a8d09600c921d4284b006490ce170d903248652bb4c819243a8592600c921cc4cab006490ea2645803248750b22c019243b098d600c921d0ec6a12a090e84635095048653bb28428243a198d4214121d0ac6a10a090c657298653d0252b94c321c81495c65250a40a4ae5a18a2a0626745885150312ba2c428a8189d0d6214540c4a86b10a2a062562d085150312b128428a81495c851d0540a4ae428a82a0626655092150292b90a3202818554e6190c4094ae530c86205267190d5210292b8ca4a1081895894294440c1aa6b108220625625444110313b2a8490881c194d4248440e0aa6a124220615531854010252b90c2a00818954861500408cae530ea99846572185548c292b8ca4a14610b5c86454630a4ae9292431862764d87524c312b22c2292618a5916014930cc2c2b00a49852571149424c2863aa8599261895894214530a4ae42a2429852574149214c2933aa8490a61491d54248530c4ccaa12429862465509214c32232e6490a61895916194830c4ac8b0aa41852571949420c312b128528861495ca5448430a4ae9292421852775509210c292baa849086189d954248430c4acaa1242185257114d42c8292ba0a690e41495c46550920a4ae229a84905897318142482a239aa890a41495d05348520b82e6302429062865509304833032a42982418a551600c820c92a6b006410561700c95108292ba4a49084149dd54248420c4ecaa124210706535092108382a9a84908410b5ca6494f10a4ae42a28388627545884184252b94c998c21495d25248610c4ce2b10a888625715885444312b12c22a2210b5ca6494d10a4ae3292848842c76549424428639aa4a1221495c85490510a4ae42a28288435761523144292b90a918a2189151628c510a4ae42a26288525721522144292b90a890a21499d54248510a4ae42a42088525721855404292b8aa4a1021895516210410c8aa6b108208465765484104252b94c9988210ddd954cc410c2cc8a9e62086266454b3104292b94a890821495d25248410a4eeaa12420852575509210438329a8490821c154d424841094ae4322200843476551100430a322a688021891915244010
  | 1 => 0xa0005eb23cb2c00002c9dd5abe23801326e47a0844a85a1d8946f3c1a0e20c66aed2e9630b383c9d0014c0000408ac20096e8c0f49808800a24e00039be5400278087011b3ca42420b893e441d1fd00aa3a80000000fb456e00000014a650028c006c3a0016a1c422f0040012a9878260030c9239160b5205f0020d66ae0a9700000001145087000b936431f2fcaa060380032351b0f50c274a280fcc12604836a2002488cb80032000ca000000200000dc00bd4aa3452de6e1a5b0c05080c163f6a80110000016db4d64599cbc000b80112420034d349c6d93da491582ac666a6390090a91c1cd26d0472e9624d521c840b9300014e6b63074ae562c33062b60d2b01ee004199848c05191a800579b4b42a3e8580a8a3e35d92213d8d0006300365c2500003588322ea1426620c314004b1d80e120602804000100c1619070101224028280200058080e05038140201108981c1d138000401018040004008000e0c0001c1600000981416028007226000003605020080009050103802008004217008083a060052572d0e5190f133a2c528c87895d16294643c4e86b14a321ca5729864350e32b90c2a8087295ca6194f4294ae331686a14a5711894350a52b94c3a9a85295c663d494294ee2b06a4a162542d8550ccb90a12a3280654add54254032e428528aa01972142545500caa4b9c84a8065585c64254032e1285992a019529748c9500cab0b8c64a8065c2d09325403294ae530c87a0ca5729864350686b9cc8a9083495c74354841a8ae730aa420e25525874210652b96c6a088389d895250441c4ecaa928220e26765494110713b1aa4a0883255cc605044194ae43028220e2552181411071338ac52a663895c56295331c4ac4b0ca998d257295241cc692b94a8a0e63495c86155231c4aa8b108318ca572993318c61bbb2a998c638999152cc631c4aa8b108298ca572993314c692b90a8a08634c5c0545043185ae4322a018d297014d42c8714aa2c0196439254d600cb21c4aa8b10a910ca5729925388750a12c019443b04c9600ca21a1ce7b2a84
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x22900c42403581a000000018e0500202ca1a05839d16294643a05839d95250441c05735486050441a05839c562953318258799152cc631a05839d16214540c05535ca6190c40c05535c86150040a05839c5621511082587151628c510a058299153cc4108258799152cc410a05821915344010825871915244010
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 890
  | 4 => 1340
  | 3 => 227
  | 2 => 14
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
  | 6 => packedAt s5K6 (802+((h/14+packedAt s5K6 (704+(h % 14)*7) 7) % 90)*7) 7
  | 5 => packedAt s5K5 (27286+((h/296+packedAt s5K5 (24030+(h % 296)*11) 11) % 1719)*11) 11
  | 4 => packedAt s5K4 (55826+((h/446+packedAt s5K4 (50920+(h % 446)*11) 11) % 1609)*12) 12
  | 3 => packedAt s5K3 (11798+((h/75+packedAt s5K3 (11123+(h % 75)*9) 9) % 273)*9) 9
  | 2 => packedAt s5K2 (860+((h/4+packedAt s5K2 (840+(h % 4)*5) 5) % 24)*5) 5
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x3ffffff0f87ffff830e1ffffe1c1ffff03f0ff
  | 1 => 0xc3c3e1ff0078f0ffc0fe38787e01c78f9d4c93
  | 2 => 0x3fc01ffff80ff0fff003f807ffe07f0e18f1c
  | 3 => 0xfc0001ffffff000fffffc0007ffff800fe0fe0
  | 4 => 0xfffffe000000000fffffffff80000000fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x400010008000000000408800404080001025
  | 1 => 0x9898d32235316989c8721c51720c952e8d4c92
  | 2 => 0xa10955445412889a59102d4234940662a18518
  | 3 => 0x8228888a0402224a2a4800449293004560ac0
  | 4 => 0x3233110ec664cccf3cd9366710302448fbe000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeaafaa8feaafaa8feaafaa8feaafaa8feaafaa8feaafaa8feaafaa8feaafaa8feaafaa8feaafaa8feaafaa8feaafaa8feaafaa8feaafaa8feaafaa8feaafaa8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36240
namespace PEqualNP.Outside.L_meta_36240
open PEqualNP.Outside.L_meta_36240.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x3a9c72d000c6241281f803278a220c98b3a000002b34002800441f2e24d4528582079778e0f847294007643519b0084a9102f40005401a0000cd89c76000300001b0b5edc000524c0180e000800112040822600b830005183040048001ffd5007fe5401ff55007fc54027fd4c097f53017f94c09fd53005f54c05fc5301ffd0c05fe4301ff50c05fc43027fd4803fe52027f54803fc5201ffd0807bf4200ff90807fd42006f50803fc42017fcc803fe32007f4c803fc32027fd4409fe51027f54409fc5101ffd0407fe4101ff50407fc41017fcc401fe31007f4c405fc3100ffc8401fe21007f48403fc21027fd4009fe50027f54009fc5001ffd0007fe4001ff50007fc40017fcc001fe30007f4c005fc3000ffc8001fe20007f48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a200fff19510025f8ca8803f7c65440093e32a200effd9110075fec888003bf64440015fb22200eff9911001dfcc88803bfd644401d7eb22200eff1911001df8c88803bbc64440075e322200effd5110077fca88803bfd544401dfe2a22000ffd8d10005fec688037fe63440057f31a2000ff58d10005fac688037fc63440057e31a200fffd4d1007efea688037fe534401ffea9a2000df54d1006ff8a68803bff434401bff21a200eff50d1006ff88688003ff62440017fb12200cff9891000dfcc488003fd62440017eb12200cff1891000df8c48803fff5244019ff292200fff54910067f8a48803bff424401ddfa12200cff90910077fa8488003bd4244019fe212200dffcc910067fc6488003fd3244019fe192200fffd451002ffca28803ff6514401ffea8a200ffd5451002ff8a28803bff414400bff20a200efd90510077fa828803bf5414400bfe20a200dffcc51002ffc6288003f63144001fe98a2000fd4c51002ff86288033ff214400bff10a2000fd88510007fa4288003f5214400bfe10a200fffd411007ffca08803ffd504401ffe282200effd0110077fc808803bfd404401dfe202200dffcc110007fc6088003fd304401bfe182200cffc8110007fc4088003fd2044019fe1022005ffc411002ff62088003fe1044001fb0822006ffd941002dfeca08017fe65040097f3282005df99410024fcca08017fd65040157eb282005df59410004faca0801bfc650400b7e3282006ffd901002dfec808017fe64040077f3202005ef9901001d7cc808017fd64040137eb202005ef590100057ac80801bfc640400b7e3202009ffd501004ffca808027fd5404013fe2a02006ffd8c1002dfec608017fe63040057f3182005f798c10015bcc608017fd63040017eb182005f758c10005bac60801bfc630400b7e318200affd4c10056fea608023fe5304015fea982000df54c10047f8a608027ff4304011ff2182009ff50c10047f8860801bff620400b7fb102005ff9881000dfcc408017ee6204003773102005ff58810005fac408017ed620400176b102006ff1881002df8c40802bff520400fff290200aff5481003ff8a408027ff4204013dfa102007ff9081004ffa8408003bd420400ffe2102008ffcc81003ffc6408003fd320400ffe1902005bf9841002ffea208017fe510400bfea882005ff1441002ffe8208017fe410400bfea082005ff1041002ffe6208017fe310400bfe9882005ff0c41002ffe4208017fe210400bfe9082005ff0841005dfcc00802bff500400dff280200aff54010037f8a008027ff400400dff2002009ff50010037f88008023ff300400dff1802000ff4c010037f8600801fff200400dff1002000ff48010037f84008017ff100400bfb8802006ff8401002ff42008017fd1004001fa8802005fe44010
  | 1 => 0x3ff4048031ff2024018ff501200c7f8809005fff3048001ff1824000fe8c120007fa6090003f9304802ffe1824001ffc812000ff64090007fe2048001f71024001ff0812000fd84090007f8204800bffb2e2005bfd971002ffccb88012fe65c400bfeb2e2016bf5971002ff8cb88016fc65c400bffb262005bfd931002ffcc98800efe64c400bfeb262015bf5931002ff8c988016fc64c402bffaa62015ff953100affaa988057fc54c400bffb1e2005bfd8f1002ffcc78800afe63c400bfeb1e2000bf58f1002ff8c788016fc63c402dffa9e2016dfd4f100a7fca78805bfd53c4001bea9e2014ff14f100affe8788053fe43c402bfea1e2014ff10f1002ffec588016ff62c400bff3162001bf98b1002ffac588002fd62c400bfe3162005bf18b100b7fea58804ffe52c402dfea962013ff14b100affe8588057bf42c4027ff2162015ff50b100077a858804ffc42c4029ff9962013ff8cb10007fa658804ffc32c400bffa8e2005ff9471002feca388017fd51c402dfaa8e2005ff1471002ffe8388017fe41c400bfb20e2005ff507100afea8388017fc41c400bff98e2005ff8c71002fec6388017fd31c4001fa98e2005ff0c71002ffe4388017fe21c400bfb10e2005ff48710007ea4388017fc21c402dffa862016ff943100b7faa18805bfc50c402bffa062015ff903100affa8188057fc40c4029ff9862000ff8c310007fa6188053fc30c4027ff9062000ff88310007fa418804ffc20c400dffb2c2012bfd9610097fccb08012fe6584025feb2c2012bf59610037f8cb08012fc658400dffb24200bbfd921005ffcc90800efe6484017feb24200bbf59210037f8c90800efc6484017ffaa4200bff9521005ffaa90802ffc548400dffb1c2000bfd8e1008ffcc70800afe6384001feb1c2000bf58e10037f8c70800afc6384025ffa9c2012dfd4e1008ffca70804bfd5384001bea9c2011ff14e1005ffe8708047fe4384017fea1c2011ff10e10037fec508002ff6284021ff3142001bf98a10007fac508002fd628400dfe3142001bf18a10097fea508043fe5284025fea942010ff14a1005ffe850802fbf4284021ff214200bff50a100077a8508043fc4284023ff9942010ff8ca10007fa6508043fc328401d7eb0c2012ffd461002ffca30804bfd518400bfe28c200bffd061002ffc830802ffd418400bfe20c2011ffcc61002ffc6308003fd318400bfe18c2010ffc861002ffc4308003fd218400bfe10c2005bf98210097fea10801bfe5084025fea842006ff1421005ffe810801bfe4084017fea042006ff1021008ffe610801bfe3084001fe9842006ff0c210087fe410801bfe2084001fe9042006ff0821002ffe2108003f7108400bfd884200fffd951007dfeca880037f65440013fb2a200fff99510025fcca8803ffd654401f7eb
  | 2 => 0x3002df8c29807fff514c03fff28a601fff545300fff8a29807bff414c03dff20a601eff505300f7f8829800bff314c005ef98a6002ff8c530017fa6298003dd314c005fe18a601dffc8530007fc4298003fd214c03bfe10a6002bfd81300fffea09807ffe504c03ffea82601fff141300f7fe809807bfe404c03dfea02601eff10130017fe609800bfb304c005ff1826000f78c130017f8609800bdc304c005fc182601dffc81300eff8409801bff65880397fb2c401cff99620025fccb10073fd65880397eb2c4006ff19620025f8cb1001bff64880377fb24401bff9922001dfcc91006ffd64880377eb244006ff1922001df8c91006fff5488037ff2a4401bff552200dff8a91001bff63880017fb1c401aff98e20015fcc710003fd63880017eb1c4006ff18e20015f8c710073ff5388039bfa9c401aff94e200e7faa7100037d5388035fe29c401bffd0e200d7fc871006ffd4388035fe21c4001bf58a2000ffea510007fe5288003fea944001ff14a2000ffe8510007bf4288003ff2144001ff50a2000f7a8510007fc4288003ff9944001ff8ca2000ffa6510007fc328800dffb0c4000ff9862002dfcc310003fd61880017eb0c4006ff186200e7fea310073fe5188039fea8c401cff146200dffe831006ffe4188037fea0c401bff106200d7fe6310003fe3188001fe98c401aff0c62000ffe4310007fe2188003fe90c4001ff0862000dfcc110073ff508800dff284401cff54220037f8a11006fff408800dff204401bff50220037f8811006bff308800dff1844000fe8c220007fa6110003f9308800dfe1844001ffc822000fde4110007fb208800dfe1044001fe082200cffeca90066ff6548033ff32a4004bf995200cffaca90066fd6548033fe32a4004bf195200c7fec890062ff6448031ff3224003bf991200c7fac890062fd6448031fe3224003bf191200c7fea890063fe5448031feaa24018ff15120007fec690002ff634802fff31a4002bf98d20007fac690002fd634802ffe31a4002bf18d200cffea6900677f534802fff29a4019ff54d20006faa69005ffc5348031ffa1a4017ff90d200c7fa869005ffc43480037fb124001ffd492000ffca490007ee5248003fea924019fb5492000ff8a490007ff4248003dfa124001ff9092000fdc8490007fd4248003dea124018fb509200075a8490007fc4248003ff9924001ff8c92000fdc6490007fd3248001f69924001ff0c920007fec290002ff6148001ff30a4000ff58520007f8c290016fc6148033ffa8a4019ff945200cffaa290067fc5148031ffa0a4018ff905200c7fa8290063fc414802fff98a4000ff8c520007fa629005ffc3148003ff90a4001fbc852000ffc4290007fd2148001f690a4001ff0852000dfec090067ff5048033ff2824019ff541200cff8a09006
  | 3 => 0xea9a4200df54d2111ff8a690893ff4348447ff21a4224ff50d2111ff88690816ff6248403ffa924201ff9492100ffaa490807fc5248403ffa124201efd092100ffc8490807ee4248403fea124201ef50921127da8490803ad4248403fe2124201ffcc92100ffc6490807fd3248403fe1924201bfd852112ffea290897f7514840bff28a4225ff5452102ff8a290897f45148449ffa0a4205ff90521127fa8290817fc4148447ff98a4205ff8c521007ec6290803fd3148401fa98a4205ff0c52100ffe4290807f7214840bff10a4205fb8852102ff84290817ec2148403fa10a4200ffd8121005fec090803fe6048401feb024200ff18121005f8c090897ff504844bff2824225ff5412112ff8a090893ff4048449ff2024224ff50121127f8809088fff3048447fe1824201ffc812100fde4090807fc204840dffb2c6022bfd9630117fccb18012fe658c045feb2c6022bf59630037f8cb18012fc658c00dffb246021bfd923010ffcc91800efe648c043feb246021bf59230037f8c91800efc648c043ffaa46021ff9523010ffaa918087fc548c0057eb1c6002ffd4e30016fea71800bfe538c005fea9c6002df54e30017f8a71800bff438c005ff21c6002ff50e30017f8871801bff628c041ff3146001bf98a30007fac518002fd628c00dfe3146001bf18a30117fea518083fe528c045fea946020ff14a3010ffe8518087bf428c041ff2146021ff50a300077a8518083fc428c005ff9946002ff8ca30017fa651800bfc328c00dffb0c6000ff9863002dfcc318003fd618c0017eb0c6006ff18630117fea31808bfe518c045fea8c6022ff1463010ffe8318087fe418c043fea0c6021ff10630017fe631800bfe318c005fe98c6002ff0c630107fe4318003fe218c001fe90c6020ff08630015fcc11808bff508c00dff2846022ff54230037f8a118087ff408c00dff2046021ff50230037f8811800bff308c005ef9846002fecc230037f8611800bf8308c041ff9046006ff082300fffeca9807eff654c03fff32a6004bf995300fffaca9807efd654c03ffe32a6004bf195300f7fec89807aff644c03dff3226003bf991300f7fac89807afd644c03dfe3226003bf191300f7fea89807bfe544c03dfeaa2601eff15130015fec69800bff534c005bfa9a6002ff94d30017bca69800bfd534c005bea9a601ff754d30006baa69800bfc534c005ffa1a6002ff90d30017bc869800bfd434c03deea1a6002ff10d30007fec498002ff624c03bff3126001bf98930007fac498077fc624c0037e312601fffd49300effca49807ffd524c03bfe292601effd09300f77e8498077fe424c03dfea126000ef509300eff8849800bff324c005ef9926002ff8c930017fa6498003dd324c005fe1926000ffd8530005fec298003fe614c001feb0a6000ff185
  | 4 => 0x80bfc308c459ff904622cff0823115ffeca988aeff654c457ff32a6204bf9953115ffaca988aefd654c457fe32a6204bf19531157fec8988aaff644c455ff3226203bf99131157fac8988aafd644c455fe3226203bf19131157fea8988abfe544c455feaa2622aff1513102dfec69880bff534c405bfa9a6202ff94d31017bca69880bfd534c405bea9a622bf754d31006baa69880bfc534c405ffa1a6202ff90d31017fa869880bfc434c401ffb126200bfd893114ffcc498806fe624c401feb126229ff1893100df8c4988afff524c453ff292622bff5493114ff8a4988abff424c455dfa126229ff90931157fa8498803bd424c453fe2126202ffcc931017fc649880bfd324c405fe1926202bfd853115ffea298817fe514c457fea8a6205ff14531157fe82988abf7414c40bff20a622aff5053102ff882988abf4414c405ff98a6202fdcc53102ffc6298817de314c40bfe18a6205f70c531017e862988a7ff214c40bfe10a6200ffd8131005fec098803fe604c401feb026200ff18131005f8c0988afff504c457ff282622bff5413115ff8a0988abff404c455ff202622aff50131157f8809880bff304c405ef9826202ff0c13114ffe40988a7fc204c40bffb2c4205bfd962102ffccb10812fe658840bfeb2c4228bf5962102ff8cb10816fc658840bffb244205bfd922102ffcc91080efe648840bfeb244227bf5922102ff8c910816fc648844fffaa44227ff9522113ffaa91089ffc548840bffb1c4205bfd8e2102ffcc71080afe638840bfeb1c4200bf58e2102ff8c710816fc6388451ffa9c4228dfd4e21137fca7108a3fd5388401bea9c4226ff14e2113ffe871089bfe438844ffea1c4226ff10e2100dfac510807ff5288403ff2944201ff54a2100ff8a510807ff4288403dfa144201ff90a2100ffa8510807bd4288403fe2144201ffcca2100ffc6510807fd3288403fe1944205bf9862102ffea3108a3f7518840bff28c4205ff5462102ff8a310817f4518840bffa0c4205ff9062102ffa8310817fc418840bff98c4205ff8c62102fec6310817fd3188401fa98c4205ff0c62102ffe4310817ef2188403fb90c4205ff0862102fe84310817ff608840bff3044200bf9822102ffac110802fd608840bfe3044228ffd4221147fca1108a3fd5088451fe2844227ffd022113ffc811089ffd408844ffe2044226ffcc221137f86110807ff2088403fe1044225ffd952112dfeca90897fe65484097f32a4225ff5952112dfaca90897fc65484097e32a4224ffd9121125fec890893fe64484077f3224224ff59121125fac890893fc64484077e3224224ffd5121127fca890893fd5448449fe2a24200ffd8d21005fec69088ffe63484057f31a4200ff58d21005fac69088ffc63484057e31a4225ffd4d2112efea69088ffe534844bf
  | 5 => 0x954219778caa1003bf6350863df31a8400ef58d4218f78c6a10cbbf53508659fa9a8431ef94d421977aa6a10033d5350863de29a8401efd894200d7ec4a100faf6250803dfa928401ef9494200f7aa4a1007bc5250803df9928431ebcc94200f7c64a1007bc3250803d61928400efd85420077cc2a1003bd6150801de30a8432efd45421977ca2a10cbbd5150865de28a8431efcc54218f7862a1007bf2150803d790a8401ef085420077ec0a1003be6050801deb028400ef181421977ea0a10cbbe5050865dea828432ef1414218f7e60a10c7bc3050803df9028401ebc814200f7840a10c3ff654c8617fb2a6430ff99532025fcca990c3fd654c8617eb2a6430ff19532025f8ca990bfff644c85f7fb22642fff9913201dfcc8990bffd644c85f7eb22642fff1913201df8c8990bfff544c85fff2a2642fff5513217ff8a899006ff634c805ffa9a6402dfd4d32017fca69900bfd534c805bea9a6402ff14d32017fe869900bfe434c805fea1a6402ff10d3200dfec499007ff524c803ff2926401ff5493200ff8a499007ff424c803dfa126401ff9093200ffa8499007bd424c803fe2126401ffcc932017de6499007fe324c803ef1926401ff0c93200fb86499007ec324c801ffb0a6400bfd8532007fcc299003fd614c801fe30a6405bf18532187fea2990c3fe514c861fea8a6430ff1453217ffe82990bffe414c85ffea0a642fff10532017fe629900bfc314c803ff90a6401ff08532007fec099002ff604c801ff3026400ff58132007f8c099002fc604c861ffa826430ff94132187faa0990c3fc504c85fffa02642fff9013217ffa80990bffc404c805ff9826402f7cc132017f86099007ff204c803f79026401ff0813202ffecb18816ff658c40bff32c6204bf9963102ffacb188bafd658c40bfe32c6205bf1963102ffec918816ff648c40bff3246203bf9923102ffac9188b6fd648c40bfe3246205bf1923116ffea9188b7fe548c45bfeaa4622dff15231015fac71880bff538c405bfa9c6202ff94e31017faa71880b7d538c405fe29c6202ffd0e31017fc871880bfd438c405fe21c6205ffd8a3102ffcc518806fe628c40bfeb146200bf58a3102ff8c518816fc628c45dffa94622cff94a31177faa5188b3fc528c45bffa14622defd0a31167fc85188b7fd428c401dea14622cff10a31017fe651880bfe328c405fe9946202ff0ca3102dfcc318817ff518c40bff28c6205ff5463102ff8a318817ff418c45bfba0c6205ff9063102ffa8318817fc418c40bfa20c6205ffcc63102fbe631880bf7318c40bfe18c6205fd0c63102ffe4318817fc218c40bffb046205ff98231005fcc118817fd608c4017eb046205ff18231177fea1188bbfe508c45dfea84622eff1423116ffe81188b7fe408c45bfea04622dff10231017fe6118
  | 6 => 0xa28dc9f822b1d7833a0890787d9c4184175a8b05c1500001a402110502d25b9550629ca20582593ba6c0e3917819a071f4938209255a1b901a4b96f9e280d95318b80008498605000000028c8001889a89a0a880ab8570079c7a728002941bb25122380000009c023a03a241fe00010e80007415e800191a508850001ef8000001ea00000014f17c1e38c58e20950cd01e8030000000000c0020000000800e018000070000080200000e0000180600200400005014020008000040040581800400000803000004028010040000185600a0380080801400c000000020100300401800401816002064000080020200000300000001800000084028000000000300100c0cc00001000000068000140080100402400c000020080600080600c0780c8080020540000401207c0180100003400001004000008030400080380100605c0b809016000010000240100280f00a0080480000a0000080c000000000030000100f8020120480980300800c00001002010040000020380180e000008008010000080100100e0340680000001000000004008018020260080780d0020000000100408c0000203800c068000080000481b0120140180501201c0000800804c0000d00c00401000018000040130120100181600e03c1b80702a0000181101803c000030220000080200403c0100200801000010064008048000000480a00301a0080381100a0840100400200c0000000a0240280600400c0a0000000000700005600008001000000008020000000080300800001004000008000030080980000100c0540a005012000028020000300380d00a00c0080a0200000080e00000800005046030098010020100080500a0040a00200002c000050220280181500e0040280f0040180300700c00c0e00b00a0240081101e03c008010000000280200602c0400a0100080480000e0080001001e0080480d0080080000500204c0800c004010018110020000181601c01802800000000008010060080180000003400800016000008050900080000202000c048070120040280901e00400001002044040000000080080302200869bfb22a634df991531a6fac8a98d37c6454c05bfb1aa6029fd8d53026bec6a980b7f4354c05bf21aa602df50d53016f886a98037f6254c67bf312a600df5895319ef8c4a98d37f4254c699fa12a633df909531a6fa84a98cf7c4254c05bf992a602df8c95319ebc64a980b7c3254c05ae192a600dfd8553006fcc2a98037d6154c01be30aa634dfd05531a6fc82a98d37d4154c69be20aa602dfcc553016be62a980b7c3154c67bf90aa633df08553006fec0a98037e6054c01beb02a600df181531a6fe80a98d37e4054c69bea02a634df10153016fe60a980b5f3054c05be182a633dfc815319ef840a98cbbf6550865df32a8432ef5
  | 7 => 0xc1118400000000001c986a0479db9e90000000000001da28220c0ad80a1149218000000000000000a71378000000000000c419d82e8001622758000588001f698a25a8e19d809a0001b21418519fc06c80000000005621d0000000002538220d62280002700a41a203e8540002438000002098000ec17ba0796195a0000001cf0a923a0000002a98000000000b9a4e00007c0ac0000138859858000a20001f7a0480005e0001fb00022228c2461ee2788000830c980007681b26c8e80000bf83a9e68000f8a38a528000001538e580027d86180023591d0002762742968001dd88720d9308cf21226d99687092f1629b70e701e2378fa1609c8902a479e525e9568e60439c1954a3603125321029d17e9441fa113a4310b233a5704485689683e18a800234827a7221a83313e1680520002368e400015d00000012b80022f0000000000001838228c000000019589d8001930001710cc00000000011f8788d0a5d94010d8190de11a997a151f323222ca41a0225900925214528a80008208089f1d31049ac26b1af1d3a8904500013d0000000949430000d208e8701520000019fe92100007e9e71021a01ff8f78fda450001c70000001f9994a02a7ba128778001580b79e31f59b080027c80020e00000022e84a0000e8a1d85f0b52391ce1b31261f601c9038000a580000000005913a80000000000000008603680006d08aaad80000027b1100000f62408000000b903424122318216900011816b1c30888ca8c70761869a691983f96719c10e0000d40178000000000000000001f712b00000000010400110f0000002951aa8928002068001a925caaa8000000002768001161bc1f8a160fd10ba040002879630ea8000a78f01fa80021c0000000ae8001030f82a0aa528599b1a61a324599986216a1e1a8007b170a2ba818000000b387128e0b100028d9348468001249200000c6a9c0088f323e97690a28fa6294a07584e12288b03a03c87c8dd19090c9af9b58000ae08680014f8000a080001d8508a68d196480012900000e82e1b3a22a8100000019a8578002301bd88d9bf2199518fc80003086d80026a8001c58b80002980c10001cd80029f9ba0000001c005d0bc80029314d00000004f8000000000baa00a3303280004b80000000008f0000000a513618f1d709800005e9f08000002860c89d524f94c18999620c92504d9f51731951129f9105a2104ca578c490c1209141a3a6613eab202ca8319e8802b11b60f100b23d0be1a5073093997132a6183d11d821a60280a74849a9019a149030000000071a2f9478d31b015928ea518001611db03224f00012a0001f194e2159660770fc218a0b25f19405a944a548430bd0aa256a080ab13da6992c9ef1830002001d000021b1bc9658a480026426e1e62690ce8188020b8a9f18fa0a18d8
  | 8 => 0x96897810114e9ad800125950a2486393500025d18e28a1e5889a848119a18000000798000102719b1826290a632af8c2a852138688c91b6a6084f17608c0bf0fe80017d86c14a96f04b15c80000000000014800000000e1fc8000001cd0001d68d78b6a620140071498001d2aa22731eb18498029b15f1be2610649da84c1489a2a7c1d900004427d0bda1f85b9589ea96799291e9c601a16d849127a7a815982a268f18ed00023a8e79a12381cc0000181468d995f9d60201462a78001238059b880002711100000000006691c80025998c1409330eb82423c12e8ef1698ed9b48f429208822703502a19800000011e0fe23096b99d0c183b1ec8549e40c31df80000000000000000013c0d021e0000001e21ed037a5c0002708000651ff2a605f82a9cb95789c80006e86a92d00015b0bbab2855aacaa5a99a2097283617416c8959850a88dc16aa1704722a84094b1e880a8da263872980aa49bd0be8fb96407901a85d98e80c0d3a370e68050290e50002351d119f80000001600026f07f0002491c68002a700021e8000001221560eb00000021084280001c09a8640ca03d8e30000002328db2650f50001b281e97d26780000022980021c9cf8000000001d48961d41e48532af045a429cb0001c81c2a3b14ba119871e003923faa32258000000000ee06920300009d0000f480009b8608000000002290001fba190ba177a3d80016ea710f20d88d500018d11085995c2a380003c2ac0002841d200000f800000000258825002a6d07baa199c899000116a4708e02f1311540f995e14dab180000029889000000013f80026692e000000069a399fd8000000cd8d11651420000001a71c200020f00000000029e8000000000068000000002420000670001d8a140a81598979668000ac8001e99ec0000000d81390002ae0002750658000000890de80022d0000002310000e00000af2400cc8f5a64a5b22881f934000000173a869130ee826a3b89980000000012f8000c809417500000017f06f1be99206b02983488a0001c080010895a9bf96c1ab00007e26b80d1b780000000019f28392684e8780511528b58001ee8038b19a789e90d00009203f00000000000022780000000000000000000013201480027ea8b8cb0aaa0197b0358281b121f00000000018b000135aa68528ff8b28a18750d580000000002312300007a0e48df80024811c1de1788fa87d1b42342778289ca9300c225801326f8af88792a80008c8a000001092413f0ce0ea08d1de97a18c80020d29497901b9081c11bbaae812287061163915a0a8480248412771289d999390f9b500028f01127a1458da8bb1772ab05a073a4e97c9a58601e7a9d9f384d19b95b9dc9ad04a81d0389c3a4406f80f1b98041c5292a0e8cb8000000c62958371720000001370ff0000000000b
  | 9 => 0x1069718001d08d68001d5aa90002168b080496e27f17480005802c2971819410ef809a178919dd1001cc80010701724986e1f28000399e800ca5a24a0000000df20ba2d97e155883a5e142a6e8a625509f8f708112d8678000e9a9626a27813a244a9c80000009300022605c80015116d2798e091500008280021310a8d91008000030001cea4d800081a9e0550001e10000002a41a4a5012c1388000420002a28001c900000000010607f8002b091f00027f999074a1486b8f2a3e0000000000000000000000000000fb0722a128d0001ae89b07a909a4a80019029b9f123f133a488ad0002ad0cf98911b2010f3a1a22012819885b1eba89a73a670a31ac9188e2a5f82da31a560b4a181471602ab82f8f90e92a80db9b922a2978000908b71319298381a9a4691a0002110000000000b60000001192aa031a4d29aa689fd1f40000970630c0a939ab82b0d71ba9aa2888002918000b205397f97aa050c391700b88401522180022e00013c9f00dd80022c00080013b0000128000001a823c8e10002790f080624ca6588bab00001090000001ed8b40c51810001120d280000020615d8208000000b30000000002250000000000ec8169ae12700000019e1f20002828002541df00004180014c8a381f1c489e0b003b8001dc0460001878002a015729a0001e080000014388f86829918820f848aa88001d19b8139a911700000000660d48a999109111ba681368a127e0f68c780002b89880824b00024c179
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xd7458810006ad7458810006ec7458810006ef5458810006ee5458810006ed5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef53588100066f5358810006ee5358810006ed53588100066d5358810006ec5358810006ef4358810006ee4358810006ed4358810006ec435881002eef715881002eee715881002eed715881002eec715881002eef515881002eee515881002eed515881002eec515881002eef415881002eee415881002eed415881002eec415881002eef315881002eee315881002eed315881002eec315881003eef7058810036ee7058810036ec7058810006ef5058810036ee5058810006ed5058810036ec5058810006ef4058810036ee4058810006ed4058810036ec4058810006ef3058810036ee3058810036ec305881002eef105881002ee71058810036ee105881002eed1058810036ec10588101bdbf7650810006bf7650810004bf76508101bebe76508101bdbd7650810006bd7650810004bd76508101bebc76508101bebf6550810196be65508101bf3e65508101963e65508101d6bd65508101bf3d65508100063d65508101bebc65508101bebf635081018ebe63508101bf9e635081018e9e6350810006bd63508101bf9d63508100069d63508101bebc63508101d73f53508100073d53508101cdbf725081004faf72508101bebf625081000ebe62508101bfae625081000eae625081003ebd62508101bfad6250810006ad625081000ebc62508101c7af325081003fac3250810007b771508101bfb471508101bebe61508101bfaf21508101bfad2150810086be605081003faf20508101bfb710508101bfba10508101bfb91050810004ff764c810034fe764c810004fd764c810034fc764c8101867e654c8100067d654c81017ebe644c810006bd644c810016de634c810006dd634c81000eee624c810006ed624c81008cff764c0100fe7e654c0100067d654c0100f6be644c010006bd644c010016de634c010006dd634c0100075d534c0100eeee624c010006ed624c010084ff76480100ce7e65480100067d65480100c6be6448010006bd64480100bede6348010006dd634801000eee6248010006ed6248010007ad4248010035f77644010006f77644010004f776440100077775440101b7747544010036f765440100377665440101b6f56544010037756544010006756544010007b774440101afb47444010036f76444010037b664440101aef56444010037b56444010006b56444010036f76344010037d66344010006f56344010037d56344010006d563440101b7775344010007755344010036f76244010037e66244010006f56244010037e56244010006e562440101afb74244010007b54244010035f7704401002ff37044010036f66044010037f26044010
  | 1 => 0x8c1002cfe7158c1002cfd7158c1002cfc7158c1002ede3158c1002edc3158c10014ff7058c10034fe7058c10014fd7058c10034fc7058c10036de3058c10036dc3058c1002ef71058c10006df7558c10006de7558c100065e7558c10006dd7558c100065d7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c10006de5258c10006dd5258c10006dc5258c10006df4258c100069f4258c10006de4258c10006dd4258c10006dc4258c1002edf7158c1002ede7158c1002edd7158c1002edc7158c1002edf5158c1002ede5158c1002edd5158c1002edc5158c1002edf4158c1002ede4158c1002edd4158c1002edc4158c1002edf2158c1002ede2158c1002edd2158c1002edc2158c10046df7058c10036de7058c10036dc7058c10006df5058c10036de5058c10006dd5058c10036dc5058c10006df4058c10036de4058c10006dd4058c10036dc4058c10006df2058c10036de2058c10036dc2058c1002edf1058c1002ed71058c10036de1058c1002edd1058c10036dc1058c101dd7f7654c100067f7654c100047f7654c101de7e7654c101dd7d7654c100067d7654c100047d7654c101de7c7654c101de7f6454c101a67e6454c101df3e6454c101a63e6454c101ee7d6454c101df3d6454c100063d6454c101de7c6454c101f57f7354c100575f7354c101de7f6354c100167e6354c101df5e6354c100165e6354c100467d6354c101df5d6354c100065d6354c100167c6354c101de7f6254c1019e7e6254c101df6e6254c1019e6e6254c101df6d6254c101de7c6254c101ef3f4254c101e75e3254c100475c3254c10007777154c101df747154c101de7e6154c101df5f3154c101df5d3154c1008e7e6054c100475f3054c101df771054c101df7a1054c101df791054c10004ff7558810024fe7558810004fd7558810024fc7558810004ff745881001cfe7458810006be745881001cbe7458810004fd7458810006bd745881001cfc7458810004ff7358810014fe7358810014fc73588100067f53588100067d5358810034ff7258810036ef7258810006ef525881003eee5258810006ed525881003eec525881003ebf4258810006ef4258810006af425881003eee4258810006ed425881003eec4258810006ef325881003eee325881003eec325881002cff715881002cfe715881002cfd715881002cfc715881002eee215881002eec215881000cff7058810034fe705881000cfd7058810034fc7058810036ee2058810036ec205881002ef71058810006ef7558810006ee7558810006ed7558810006ec7558810006ef7458810006ee7458810006ae7458810006e
  | 2 => 0x2cf67684110035f77584110215f57584110007776584110207746584110035f7748411020df57484110007b764841101ffb46484110035f77384110005f57384110207775384110007755384110035f77284110005f572841101ffb74284110007b54284110035f67084110036f7608411002ff360841100067f74594100067e74594100067d74594100067c74594100067f73594100047f73594100067e73594100067d73594100067c73594100067f43594100067e43594100067d43594100067c43594100067f72594100067e72594100067d72594100067c72594100067f42594100063f42594100067e42594100067d42594100067c42594100067f32594100067e32594100067c325941002e7f715941002e7e715941002e7d715941002e7c715941002e7f415941002e7e415941002e7d415941002e7c415941002e7f315941002e7e315941002e7d315941002e7c315941002e7f215941002e7e215941002e7d215941002e7c21594100567f70594100367e70594100567d70594100367c70594100067f40594100367e40594100067d40594100367c40594100067f30594100367e30594100367c30594100067f20594100367e20594100367c205941002e7f105941002e7710594100367e105941002e7d10594100367c1059410006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf53590100063f5359010006be5359010006bd5359010006bc5359010006bf7259010004bf7259010006be7259010006bd7259010006bc7259010006bf5259010006be5259010006bd5259010006bc5259010006bf3259010006be3259010006bc325901002ebf715901002ebe715901002ebd715901002ebc715901002ebf515901002ebe515901002ebd515901002ebc515901002ebf315901002ebe315901002ebd315901002ebc315901002ebf215901002ebe215901002ebd215901002ebc215901004ebf7059010036be705901004ebd7059010036bc7059010006bf5059010036be5059010006bd5059010036bc5059010006bf3059010036be3059010036bc3059010006bf2059010036be2059010036bc205901002ebf105901002eb71059010036be105901002ebd1059010036bc1059010004ff7558c10024fe7558c100067e7558c100247e7558c10004fd7558c100067d7558c10024fc7558c10004ff7458c1001cfe7458c10004fd7458c1001cfc7458c10034ff7358c10036df7358c100467f5358c10006df5358c100065f5358c10046de5358c10006dd5358c10046dc5358c10006df4358c10046de4358c10006dd4358c10046dc4358c10004ff7258c1000cfe7258c1000cfc7258c10006bf4258c10046df3258c10006de3258c10046dc3258c1002cff715
  | 3 => 0x7428c510007b5428c510035f6708c51002ef7608c51002ff3608c510014fc764c5100067f654c51015e7c654c510006bf644c510156bc644c510006df634c510016dc634c5100075d534c51002fd4314c510005fb704c510005f8704c51006df4764c510016f4764c510014f4764c510275f7754c510275f5754c51000777654c51026774654c51026df7744c51026df5744c510007b7644c510156f6644c510156f4644c51025fb4644c510156b4644c51002df7734c51002fd7734c510007d7634c510016f6634c510016f4634c51006fd4634c51006f77534c51006fd6534c51006f75534c510267d5534c51000755534c510005f7724c510006f7624c510006f5624c51025fb7424c510007b5424c510007f3704c510035f4704c510007f0704c51002ef7604c51002ff3604c51006fd7304c510005f6768851002ef6768851002df77588510255f57588510007776588510146f66588510146f4658851023f74658851014674658851002df7748851024df57488510007b76488510247b4648851002df77388510005f57388510006f76388510006f5638851023f775388510007755388510065f5728851000ef6628851000ef46288510067b74288510067b54288510035f6708851002ef7608851002ff3608851000cfc76485100067f654851012e7c6548510006bf6448510126bc6448510006ef624851000eec6248510007ad424851002fe42148510005fb7048510005f87048510065f4764851000ef4764851000cf47648510235f77548510235f5754851000777654851012ef6654851012ef4654851022774654851012e74654851022df7744851022df57448510007b7644851021fb46448510005f77348510005f57348510006f76348510006f5634851022777534851000775534851002df7724851002fe77248510007e7624851000ef6624851000ef46248510067e46248510067b74248510067e64248510067b5424851021fe54248510007a54248510007f37048510035f47048510007f0704851002ef7604851002ff36048510067e720485100a4fe768c1100067f658c1101167c658c110006bf648c11010ebc648c110014ff764c11006cfd764c11002cfc764c1100067f654c1100fe7c654c110006bf644c1100f6bc644c110006df634c110016dc634c1100075d534c110005f7714c11002df4714c110007d5314c11009cfe76881100067f65881100e67c6588110006bf64881100debc648811000cff7648110064fd764811002cfc76481100067f65481100ce7c6548110006bf64481100c6bc6448110006ef624811000eec6248110007ad4248110005f7714811002df47148110007e521481100067f65841100967c6584110006bf648411005ebc648411002dfa708411002efb608411002df67684110036f67684110
  | 4 => 0x4d1007f5f7354d1006e7f6354d100167e6354d1006f5e6354d100165e6354d1006e7d6354d100075d6354d100065d6354d100167c6354d1019e7e6254d1019e7c6254d102af3f4254d102b75e3254d1006f5c3254d10007767154d10007757154d102af764154d102af754154d1006f5f3154d1006f5f3054d101df7b1054d1000cfe76d89100067f65d89100067c65d8910075bc74d8910006bf64d8910006bc64d8910066ee62d8910004ff75d8910024fe75d8910004fd75d8910024fc75d8910004ff74d8910006bf74d891001cfe74d8910004fd74d891001cfc74d8910006bc74d891001cbc74d8910014fe73d8910004fd73d8910014fc73d89100067f53d89100067d53d8910066bf42d8910006ef32d8910066ec32d891002cfe71d8910064fd71d891002cfc71d8910066ef21d8910034fe70d891002cfd70d8910034fc70d8910066ef20d89100057f755891007d7c75589100067f65589100067c6558910005bf7458910075bc7458910006bf6458910006bc6458910005df735891006ddc7358910066ec6258910004ff75589100067f75589100047f7558910024fe7558910004fd7558910024fc75589100067c75589100247c7558910004ff7458910006bf7458910004bf745891001cfe7458910004fd745891001cfc7458910006bc745891001cbc7458910004ff7358910006df7358910004df7358910014fe7358910014fc7358910006dc7358910014dc73589100067f53589100067d5358910064ff7258910006ef7258910066bf4258910066ee4258910006ed4258910084ff7158910006f7715891009cff7058910006fb7058910006bf7650910005be7650910006be7650910004be7650910006bd7650910005bc7650910006bc7650910004bc765091029ebf65509100073f65509100063f6550910196be655091029ebd6550910196bc655091029f3c65509101963c6550910006bf635091018ebe6350910006bd635091018ebc635091029f3f53509100073d5350910065bf7250910077af7250910066bf625091000ebe6250910067ae625091000eae6250910066bd6250910007ad6250910006ad625091000ebc62509102a7af3250910067ac3250910007b67150910007b5715091029fb6515091029fb55150910067af2150910067af20509101bfbb1050910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c9101867c654c910006bf644c91017ebc644c910005f6768c51002ef6768c51002df7758c510295f5758c51000777658c51028f74658c51002df7748c510285f5748c510007b7648c51016ef6648c51016ef4648c51027fb4648c51016eb4648c51006df5738c510016f6638c510016f4638c51006f77538c51006f75538c510005f5728c510006f7628c510006f5628c51027fb
  | 5 => 0x75be76d9110076be76d911001cbe76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006be63d9110006bc63d91100073f53d9110005bd72d9110006be62d9110006bc62d9110007b771d9110077b471d9110007b651d9110007b551d91102bfbb10d91102bfb810d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d91100063f53d9110006be53d9110006bd53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110004bd72d9110006bc72d9110006bf52d9110006be52d9110006bd52d9110006bc52d9110006bf32d9110006be32d9110006bc32d9110006bf71d91102bebe71d9110076bd71d91102bebc71d9110006bf51d91102bebe51d9110006bd51d91102bebc51d9110006bf31d91102bebe31d91102bebc31d9110006bf21d91102bebe21d91102bebc21d91102bebf70d9110076be70d9110076bd70d9110076bc70d9110006bf50d9110006be50d9110006bd50d9110006bc50d9110006bf30d9110006bc30d9110006bf20d9110006bc20d91102bebf10d9110076bd10d91102bebc10d9110014fe76d8d1007d7c75d8d100067f65d8d100067c65d8d10006bf64d8d10006bc64d8d1006ede63d8d10004ff75d8d100067f75d8d10024fe75d8d10004fd75d8d10024fc75d8d100067c75d8d100247c75d8d10004ff74d8d1001cfe74d8d10004fd74d8d1001cfc74d8d1006e7f53d8d1000cfe72d8d10004fd72d8d1000cfc72d8d10006bf42d8d10006de32d8d1006edc32d8d1002cfe71d8d1006cfd71d8d1002cfc71d8d1006edf31d8d10034fe70d8d1002cfd70d8d10034fc70d8d1006edf30d8d100057f7558d1007d7c7558d100067f6558d100067c6558d10005bf7458d10075bc7458d10006bf6458d10006bc6458d1006edc6358d10005ef7258d10065ec7258d10004ff7558d100067f7558d100047f7558d10024fe7558d10004fd7558d10024fc7558d100067c7558d100247c7558d10004ff7458d10006bf7458d10004bf7458d1001cfe7458d10004fd7458d1001cfc7458d10006bc7458d1001cbc7458d1006cff7358d10006df7358d1006e7f5358d1006ede5358d10006dd5358d10004ff7258d10006ef7258d10004ef7258d1000cfe7258d1000cfc7258d10006ec7258d1000cec7258d10006bf4258d1008cff7158d10006f77158d100a4ff7058d10006fb7058d100067f7654d100057e7654d100067e7654d100047e7654d100067d7654d100057c7654d100067c7654d100047c7654d102ae7f6454d100073f6454d100063f6454d101a67e6454d102ae7d6454d101a67c6454d102af3c6454d101a63c6454d1006d7f735
  | 6 => 0xd7458a1001cfc7458a10004ff7358a10014fe7358a10014fc7358a100067f5358a100067d5358a10036ef7258a10086ee5258a10006ed5258a10086bf4258a10086ee4258a10006ed4258a10086ee3258a10086ef2158a10034fc7058a10036ee2058a10036ec2058a10006bf7650a10006be7650a10006bd7650a10006bc7650a102e6bf6550a10196be6550a102e6bd6550a10196bc6550a10006bf6350a1018ebe6350a10006bd6350a1018ebc6350a102e73f5350a100073d5350a10085bf7250a1005faf7250a10086bf6250a1000ebe6250a10087ae6250a1000eae6250a10086bd6250a10007ad6250a10006ad6250a1000ebc6250a102dfaf3250a10087ac3250a10007b77150a10007b47150a10066bd6150a10087af2150a101bebe6050a10087af2050a101bfbb1050a10004ff764ca10034fe764ca10004fd764ca10034fc764ca10016de634ca10006dd634ca1000eee624ca10006ed624ca10014ff764c610034fc764c610016de634c610006dd634c6100075d534c610005fb704c610035f8704c61000cff7648610034fc764861000eee6248610006ed6248610007ad4248610005fb7048610035f87048610044ff764c210036df634c210036dc634c2100075d534c21003cff7648210036ef6248210036ec6248210007ad4248210035f576c421002ef576c4210036f765c42102d6f565c4210036f764c42102cef564c4210036f763c4210006f563c42102d77753c42100077553c4210036f762c4210006f562c42102cfb742c4210007b542c4210037f260c421007d7e76d951007e7e76d95100247e76d95100067f64d95100067e64d95100067d64d95100067c64d95100073c64d95100063c64d95100057d73d95100067e63d95100067c63d95100067e62d95100067c62d95100073f42d95100077771d951007f7471d95100077641d95100077541d95102c77b10d95102c77810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100047d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100063f42d95100067e42d95100067d42d95100067c42d95100067f32d95100067e32d95100067c32d95100067f71d95102c67e71d951007e7d71d95102c67c71d95100067f41d95102c67e41d95100067d41d95102c67c41d95100067f31d95102c67e31d95102c67c31d95100067f21d95102c67e21d95102c67c21d95102c67f70d951007e7e70d951007e7d70d951007e7c70d95100067f40d95100067e40d95100067d40d95100067c40d95100067f30d95100067c30d95100067f20d95100067c20d95102c67f10d951007e7d10d95102c67c10d9510
  | 7 => 0xcb1002df6714cb1002df7764c710046f7764c710335f7754c710335f5754c71032df7744c71032df5744c710156f6644c71002ef4644c71002fd7734c71002fd7634c710016f6634c71002ef4634c71002fd4634c7100a777534c7100a7d6534c7100a775534c710327d5534c71000755534c710005f7724c71002ef7624c710006f5624c71031fb7424c710007b5424c710035f4704c7100a7d7304c71002df7764871003ef77648710315f77548710315f5754871012ef6654871002ef4654871030df7744871030df57448710005f77348710005f5734871002ef76348710006f5634871030777534871000775534871002fe7724871002fe7624871000ef6624871002ef4624871002fe4624871009fb7424871009fe6424871009fb542487102ffe54248710007a54248710035f4704871009fe7204871006cfd768c310035f4718c310014ff764c31002cfc764c310016de634c310006dd634c3100075d534c310005f7714c31002df4714c310007d5314c310064fd7688310035f4718831000cff764831002cfc764831000eee6248310006ed6248310007ad4248310005f7714831002df47148310007e52148310034ff75d8e10024fe75d8e10004fd75d8e10034fc75d8e10034ff74d8e1001cfe74d8e10004fd74d8e10034fc74d8e1008cfd73d8e1008e7f53d8e1000cfe72d8e10004fd72d8e10034fc72d8e10006bf42d8e10036f571d8e10036fa70d8e10036df30d8e10014ff7658e10036dc6358e10004ff7558e10024fe7558e10004fd7558e10024fc7558e10004ff7458e1001cfe7458e10004fd7458e1001cfc7458e10036df7358e1008e7f5358e1008ede5358e10006dd5358e1008ede4358e10006dd4358e10004ff7258e1000cfe7258e1000cfc7258e10006bf4258e1008edf3258e1008edf3158e10034fc7058e10036de3058e10036dc3058e100067f7654e100067e7654e100067d7654e100067c7654e102f67f6454e101a67e6454e102f67d6454e101a67c6454e1008d7f7354e100975f7354e1008e7f6354e100167e6354e1008f5e6354e100165e6354e1008e7d6354e100075d6354e100065d6354e100167c6354e1019e7e6254e1019e7c6254e102f73f4254e102ef5e3254e1008f5c3254e10007777154e10007747154e1006e7d6154e1008f5f3154e101de7e6054e1008f5f3054e101df7b1054e10034ff75d8a10024fe75d8a10004fd75d8a10034fc75d8a10034ff74d8a1001cfe74d8a10004fd74d8a10034fc74d8a10014fe73d8a10004fd73d8a10034fc73d8a100067f53d8a100067d53d8a10084fd72d8a10086bf42d8a10036f571d8a10036fa70d8a10036ef20d8a1000cff7658a10036ec6258a10004ff7558a10024fe7558a10004fd7558a10024fc7558a10004ff7458a1001cfe7458a10004f
  | 8 => 0x7ad424c120007cd324c1200bfd8304c1200efe8204c12000df8764c120016f8764c12000cf8764c120105fb734c120007db734c120007db634c120016fa634c120016f8634c1200bfd8634c1200bf7b534c1200bfda534c1200bf79534c12037fd9534c12000759534c1200bfda434c120377d9434c120007eb724c12000dfa724c12000df8724c1200efe8724c1200eefb624c1200efea524c12037fe9524c1200efbb424c1200efea424c1200efb9424c120377e9424c120007a9424c1200efdb324c1200efea324c1200efd9324c1200bfe9324c120007c9324c1200bfdb314c120007d9314c1200efeb214c120007e9214c120035ef758812036ded7588120035ef7488120365ed7488120035ef7388120005ed738812035f6f53881200076d5388120005ed7188120035ee7088120037ea7088120036ef608812000feb6088120037ea3088120007e93088120004ff7558f10024fe7558f10004fd7558f10024fc7558f10004ff7458f1001cfe7458f10004fd7458f1001cfc7458f1002edf7358f100a67f5358f100a6de5358f10006dd5358f10004ff7258f1000cfe7258f1000cfc7258f10006bf4258f1002cfc7158f1002ede3158f1002edc3158f1002ef62158f100a6df3058f100067f7654f101de7e7654f100067d7654f101de7c7654f101de7f6454f101a67e6454f1034e7d6454f101de7c6454f101f57f7354f100b75f7354f101de7f6354f100167e6354f101df5e6354f100165e6354f100a67d6354f101df5d6354f100065d6354f100167c6354f101de7f6254f1019e7e6254f101de7c6254f1034f3f4254f103575e3254f100a75c3254f101df767154f10007757154f101df764154f1034f754154f101df5f3154f101df763154f101df5d3154f101df762154f100a75f3054f10004ff7558b10024fe7558b10004fd7558b10024fc7558b10004ff7458b1001cfe7458b10004fd7458b1001cfc7458b10004ff7358b10014fe7358b10014fc7358b100067f5358b100067d5358b1002eef7258b1009ebf4258b1009eee4258b10006ed4258b1002cfc7158b1002ef63158b1002eee2158b1002eec2158b1009eef2058b10006bf7650b101bebe7650b10006bd7650b101bebc7650b101bebf6550b10196be6550b1033ebd6550b101bebc6550b101bebf6350b1018ebe6350b10006bd6350b101bebc6350b1033f3f5350b100073d5350b101cdbf7250b100afaf7250b101bebf6250b1000ebe6250b101bfae6250b1000eae6250b1009ebd6250b101bfad6250b10006ad6250b1000ebc6250b10347af3250b1009fac3250b101bfb67150b10007b57150b101bfb65150b1033fb55150b101bfb63150b101bfaf2150b101bfb62150b101bfad2150b1009faf2050b10004ff764cb1002cfe764cb10004fd764cb1002cfc764
  | 9 => 0xc63509203dfaf53509203df2f53509203d7ae53509203dfad53509200072d53509203d7ac5350920007af7150920007ae7150920007ad7150920007ac71509203dfaf51509203dfae51509203dfad51509203dfac51509203d7af31509203d7ac3150920007af7050920007ab7050920007ae70509200c7ad7050920007ac7050920007a8705092000faf605092000eaf605092000fab60509203dfaf50509203dfae50509203dfad50509203dfac50509203d7af30509203d7ac30509200bdec764c920016ec764c920014ec764c9203cdef754c9203cded754c9203c5ef744c9203c5ed744c92000def734c92000fcf734c920007cf634c920016ee634c920016ec634c9200bfcc634c9200bf6f534c9200bf6d534c920005ef714c920007eb704c920035ec704c920007e8704c92000eef604c92000feb604c9200bfcf304c920007ad42d8520004ff75d8520024fe75d8520004fd75d8520024fc75d8520004ff74d852001cfe74d8520004fd74d852001cfc74d8520014fe73d8520004fd73d8520014fc73d85200067f53d85200067d53d8520086bf42d8520086ee42d8520086bd42d8520006ed42d8520006ad42d8520006f741d8520006f441d8520086f621d8520086f521d8520034fe70d8520007ad4298520006f76198520065f970985200057f75585200cd7c7558520005bf74585200c5bc7458520005df73585200bddc7358520007ad425852009dfb70585200c5be7418520005bd7418520007ad421852002ef66118520006f56118520004fe768c520004fd768c52002cfc768c520006df638c520016dc638c52000dee728c520005ed728c520007ad428c52002ef6618c520004ff764c520004fe764c520004fc764c5200075d534c52000dee724c520007ad424c52002cec76485203bdef75485203bded75485203b5ef74485203b5ed74485203aeef64485203aeed6448520005ef7348520005ed73485203a76f53485200076d534852000def714852000fe77148520007e7614852002eee614852002eec6148520007e461485203a7e751485203a7e45148520007e63148520007e53148520007eb7048520035ec7048520007e8704852000eef604852000feb604852039cfe768c120035ec728c120007ad428c120037e8208c12039dfa768c120396fa768c1200edf9738c120016fa638c120016f8638c1200bf7b538c1200bf79538c120037eb728c12000dfa728c12000df8728c120037e8728c120036fb628c120107ea528c12038fe9528c120107bb428c120107ea428c120107b9428c120387e9428c120007a9428c120107ea328c1200bfe9328c120107eb218c120007e9218c120014ff764c12000cfe764c1200ecfd764c12000cfc764c120006df634c120016dc634c1200075d534c120005ef724c12000dec724c120
  | 10 => 0x8620066f5215862002cff7058620034fc7058620066ef2058620036f61058620036f4105862002cff768c620034fe768c620004fd768c62002ef6618c620006f5618c620004ff764c620004fd764c620034fc764c620016de634c620006dd634c6200075d534c620005ef724c62000dec724c62002ef6614c620006f5614c620035f9768c220036f9768c22000cf9768c220016fa638c220037da638c220037d9638c220036f8638c2200d77b538c2200d779538c22000dfa728c220037ea728c220037e9728c220035f8728c220107bb428c220107b9428c2203fcff764c220036df634c220036dc634c2200075d534c220037d8304c2203fdfb764c220416fb764c220037db734c220037db634c220016fa634c220016f8634c220037d8634c2200d77b534c2200d7da534c2200d779534c22040fd9534c22000759534c2200d7da434c220407d9434c22000dfa724c22000df8724c2200efbb424c2200efb9424c2200efdb324c2200efd9324c2200d7db314c220007d9314c220014fe76d8d200bede63d8d20004ff75d8d20024fe75d8d20004fd75d8d20024fc75d8d20004ff74d8d2001cfe74d8d20004fd74d8d2001cfc74d8d200be7f53d8d200bede53d8d20006dd53d8d20006df43d8d200bedc43d8d20034ff72d8d2000cfe72d8d20104fd72d8d2000cfc72d8d20106bf42d8d20106bd42d8d20106df32d8d20106dd32d8d2002cfe71d8d20004fd71d8d200bedc31d8d2000cfd70d8d200bedf30d8d200bedc6358d203fdfb7058d20004ff7558d20024fe7558d20004fd7558d20024fc7558d20004ff7458d2001cfe7458d20004fd7458d2001cfc7458d20104ff7358d20006df7358d200be7f5358d200ecff7258d20006ef7258d200eebf4258d200eebd4258d20004ff7158d2002cfc7158d203fcff7058d20006fb7058d200067f7654d200067e7654d200067d7654d200067c7654d203ee7f6454d201a67e6454d203ee7d6454d201a67c6454d203f57f7354d200cf5f7354d200be7f6354d200075f6354d200065f6354d200167e6354d200be7d6354d200167c6354d200bf5c6354d200165c6354d2019f6e7254d200076d7254d2019e7f6254d2019f3f4254d2019f6e4254d2019f3d4254d203ef6d4254d2019f5e3254d2019f6e3254d2019f4e3254d2019f5c3254d201de7c6154d200bf5f3154d2019f6f2154d2019e7f6054d200bf5f3054d2019f7b2054d2019f6c2054d2019f782054d200c7af765092001eaf76509200c7ac765092001eac76509203e7af75509203dfae75509203e7ad75509203dfac75509203dfaf65509203dfae65509203dfad65509203dfac6550920007af73509203d7ae7350920007ad73509203d7ac7350920007af63509203d7ae635092018eae6350920007ad63509203d7ac635092018ea
  | 11 => 0x57d75185300075d531853002ef66118530006f5611853002cdc764c530455df754c530455dd754c53044edf654c53044edd654c530445df744c530445dd744c530005df724c53043f9f424c5300079d424c530015df714c530017d7714c530007d7614c53002ede614c53002edc614c530007d4614c53043fd7414c53043fd4414c530007db704c530035dc704c530007d8704c530016df604c530017db604c530004fe7688530004fd768853002cfc7688530015de7388530005dd73885300075d5388530006ef628853000eec628853002ef66188530007d53188530004ff7648530004fe7648530004fc7648530015de7348530005dd73485300075d5348530007ad4248530007d53148530035df758c130435dd758c130035df748c13042ddd748c130005dd728c1304279f428c1300079d428c130005dd718c130035de708c130037da708c130036df608c130017db608c130034ff75d8e20024fe75d8e20004fd75d8e20034fc75d8e20034ff74d8e2001cfe74d8e20004fd74d8e20034fc74d8e200ecfd73d8e200d67f53d8e20036ed72d8e20106bf42d8e20106bd42d8e2002cfe71d8e20004fd71d8e20034fe70d8e20036fa70d8e20036df30d8e20036ef20d8e20014ff7658e20036dc6358e20004ff7558e20024fe7558e20004fd7558e20024fc7558e20004ff7458e2001cfe7458e20004fd7458e2001cfc7458e20036df7358e200d67f5358e200d6de5358e20006dd5358e200d6de4358e20006dd4358e200eebf4258e200eebd4258e200eedf3258e200eedd3258e20004ff7158e2002cfc7158e200d6df3158e20034fe7058e20034fc7058e20036de3058e20036dc3058e200eeef2058e200067f7654e200067e7654e200067d7654e200067c7654e2041e7f6454e201a67e6454e2041e7d6454e201a67c6454e203f57f7354e200e75f7354e200d67f6354e200167e6354e200d75e6354e200165e6354e200d67d6354e200075d6354e200065d6354e200167c6354e200076f7254e2019f6c7254e2019e7d6254e2019f3f4254e2019f3d4254e2019f5e3254e2019f5c3254e201de7e6154e200d75f3154e2019e7e6054e200d75f3054e2019f6f2054e2019f7b2054e2019f782054e20036f76198620036f461986200057f75586200e57c7558620005bf74586200ddbc7458620036f46158620004ff75586200067f75586200047f7558620024fe7558620004fd7558620024fc75586200067c75586200247c7558620004ff7458620006bf7458620004bf745862001cfe7458620004fd745862001cfc7458620006bc745862001cbc7458620004ff7358620014fe7358620014fc73586200067f53586200067d5358620066bf4258620066bd4258620006f65158620006f55158620006f64158620006f54158620066f6215
  | 12 => 0xc7654d300265c7654d304875f7454d3047f5e7454d304875d7454d3047f5c7454d3047f5f6454d3047f5e6454d3047f5d6454d3047f5c6454d300075f7254d304775e7254d300075d7254d304775c7254d304775e6254d3019e5e6254d304775c6254d3019e5c6254d3047f5f4254d3047f1f4254d304775e4254d3047f5d4254d304775c4254d300075f7154d300075e7154d300075d7154d300075c7154d3047f5f4154d3047f5e4154d3047f5d4154d3047f5c4154d304775f2154d304775c2154d300075f7054d300075b7054d300075e7054d300ff5d7054d300075c7054d30007587054d300175f6054d300165f6054d300175b6054d3047f5f4054d3047f5e4054d3047f5d4054d3047f5c4054d304775f2054d304775c2054d3000cfe76d89300075d53d89300eeee62d8930004ff75d8930024fe75d8930004fd75d8930024fc75d8930004ff74d893001cfe74d8930004fd74d893001cfc74d893000cfc73d89300d67f53d89300d67d53d8930006ef52d89300eeec52d89300eebf42d89300eeee42d8930006ed42d89300eeee32d89300d6ed32d893002cfe71d8930004fd71d89300eeec21d8930014fd70d89300eeef20d89300075d53589300eeec6258930395fb7058930006bf7650930006be7650930006bd7650930006bc765093046ebf6550930196be655093046ebd6550930196bc655093018f9e73509300079d7350930106bf635093018f3f535093018f9e535093018f3d535093046f9d53509300071d53509300edbf72509300f7af72509300eebf6250930007af6250930006af625093000ebe625093000ebc62509300efac625093000eac62509300ef9f325093018faf325093018f8f32509300efac32509301bebc615093018f9f31509300efaf21509303febf605093018fbb305093018f9c305093018fb830509300efaf20509300eddc764c93000edc764c93000cdc764c930465df754c930465dd754c93045ddf744c93045ddd744c930015df724c930017cf724c930007cf624c93000ede624c93000edc624c9300efcc624c9300ef9f424c9300ef9d424c930005df714c930007db704c930035dc704c930007d8704c930016df604c930017db604c9300efcf204c9300075d53d8530004ff75d8530024fe75d8530004fd75d8530024fc75d8530004ff74d853001cfe74d8530004fd74d853001cfc74d853008e7f53d853008ede53d853008e7d53d8530006dd53d85300065d53d853000cfe72d8530004fd72d853000cfc72d8530006bf42d8530006bd42d8530006f751d8530006f451d853008ef631d853008ef531d85300075d5398530006f7619853006df970985300057f75585300fd7c7558530005bf74585300f5bc74585300075d5358530005ef72585300edec72585300a5fb70585300fd7e7518530
  | 13 => 0x812109ebd42d8121006ed42d8121006ad42d8121006f631d8121006f531d812109efa20d8121007ad4298121006fb60981210057f755812112d7c7558121005bf7458121125bc7458121005df735812111ddc7358121007ad425812112d7e75181210057d7518121125be7418121005bd741812111dde7318121005dd7318121007ad4218121006f96018121034ff7518121024fe75181210367e75181210247e7518121004fd75181210367d75181210047d7518121034fc7518121034ff741812101cfe7418121036be741812101cbe7418121004fd7418121036bd7418121004bd7418121034fc7418121014fe7318121036de7318121014de7318121004fd7318121036dd7318121004dd7318121034fc73181210067f53181210067d531812102cfd721812103ebf421812103ebd4218121036f57118121036ef2018121036fa201812103ef9201812100cff7658a30036ec6258a30004ff7558a30024fe7558a30004fd7558a30024fc7558a30004ff7458a3001cfe7458a30004fd7458a3001cfc7458a300be7f5358a300be7d5358a30106ee5258a30006ed5258a30106bf4258a30106ee4258a30006ed4258a30106ee3258a300beed3258a30004ff7158a3002cfc7158a30106ef2158a30034fe7058a30034fc7058a300bedf3058a30036ee2058a30036ec2058a30006bf7650a30006be7650a30006bd7650a30006bc7650a3048ebf6550a30196be6550a3048ebd6550a30196bc6550a300079f7350a3018f9c7350a300eebd6350a3018f3f5350a3018f3d5350a30105bf7250a3010faf7250a3000ebe6250a30107ae6250a3000eae6250a30106bd6250a30007ad6250a30006ad6250a3000ebc6250a3018faf3250a30107ac3250a301bebe6150a30107af2150a3039ebe6050a3018f9f3050a3018fbb3050a3018fb83050a30107af2050a30036f76198630036f461986300057f75586301157c7558630005bf745863010dbc7458630036f46158630004ff75586300067f75586300047f7558630024fe7558630004fd7558630024fc75586300067c75586300247c7558630004ff7458630006bf7458630004bf745863001cfe7458630004fd745863001cfc7458630006bc745863001cbc745863006e7f535863006e7d5358630004ff725863000cfe725863000cfc7258630006bf4258630006bd4258630006f65158630006f55158630006f64158630006f5415863006ef6315863006ef53158630034fc705863006edf3058630036f61058630036f4105863002cff7688630034fe7688630004fd768863002ef66188630006f56188630004ff7648630004fd7648630034fc7648630005df7348630015dc734863000eee6248630006ed6248630007ad424863002ef66148630006f561486300ff5f7654d300265f7654d300ff5
  | 14 => 0x1a67e6454d214ce7d6454d211a67c6454d213f57f7354d2112f5f7354d2111e7f6354d210075f6354d210065f6354d210167e6354d2111e7d6354d210167c6354d2111f5c6354d210165c6354d210076f7254d2119f6c7254d211de7f6254d2119f3f4254d2119f6e4254d2119f3d4254d214cf6d4254d2119f5e3254d2119f5c3254d21007777154d21007747154d2119e7f6154d2111f5f3154d2119f772154d211df6e2154d211df6c2154d2119f742154d2111f5f3054d2119f6f2054d21127af765092101eaf7650921127ac765092101eac76509214c7af75509214bfae75509214c7ad75509214bfac75509214bfaf65509214bfae65509214bfad65509214bfac6550921007af73509214b7ae7350921007ad73509214b7ac7350921007af63509214b7ae635092118eae6350921007ad63509214b7ac635092118eac63509214bfaf53509214bf2f53509214b7ae53509214bfad53509210072d53509214b7ac5350921007af7150921007a771509211bfae7150921127ad71509211bfac7150921007a4715092100faf615092100eaf615092100fa761509214bfaf51509214bfa751509211bfae51509214bfad51509211bfac51509214bfa451509214b7af31509211bfae31509211bfac3150921007af7050921007ae7050921007ad7050921007ac70509214bfaf50509214bfae50509214bfad50509214bfac50509214b7af30509214b7ac30509214adf6768c52102ef6768c52112df6758c52102df4758c52116ef6648c52116ef4648c52114df5738c521016f6638c521016f4638c52111f77538c52111f75538c52100df6728c52102df4728c52102ef7628c52102fe7628c521167b7428c521167e6428c521167b5428c5214a7e5428c521007a5428c521005f5708c521167e7208c521014ff764c52100cfe764c52114cfd764c52100cfc764c521006df634c521016dc634c5210075d534c521005ef724c52100dec724c521007ad424c52100df4764c521016f4764c52100cf4764c52112df6754c52112df4754c521156f6644c521156f4644c52102df7734c52102fd7734c521007d7634c521016f6634c521016f4634c52111fd4634c521016d4634c52111f77534c52111fd6534c52111f75534c52149fd5534c52100755534c521007e7724c52100df6724c52100df4724c52114fe4724c52100de4724c52102ef7624c52102fe7624c52114fb7424c52114fe6424c52114fb5424c521497e5424c521007a5424c521005f7704c52111fd7304c52114fe7204c521007ad42d8121004ff75d8121024fe75d8121004fd75d8121024fc75d8121004ff74d812101cfe74d8121004fd74d812101cfc74d8121014fe73d8121004fd73d8121014fc73d81210067f53d81210067d53d812102cfd72d812109ebf42d812109eee42d
  | 15 => 0xf3258e2114edd3258e2102cfe7158e2102cfc7158e2102ede3158e2102edc3158e21004ff7058e21034fc7058e21136df3058e2102ef71058e210067f7654e211de7e7654e210067d7654e211de7c7654e211de7f6454e211a67e6454e214ee7d6454e211de7c6454e211f57f7354e211475f7354e211de7f6354e210167e6354e211df5e6354e210165e6354e211367d6354e211df5d6354e210065d6354e210167c6354e2119e7d6254e2119f3f4254e2119f3d4254e2119f5e3254e2119f5c3254e21007777154e211df747154e211de7e6154e211df5f3154e211df763154e211df5d3154e211df6f2154e2119f772154e211df742154e211375f3054e2102df7764c6214e6f7764c621145f6754c621145f4754c621156f6644c62102ef4644c62102fd7734c621016f6634c62102ef4634c62113777534c621137d6534c62113775534c6214dfd5534c62100755534c62100df6724c62100df4724c62114fb7424c62114fb5424c621005f7704c621137d7304c621034ff7598221024fe7598221004fd7598221034fc7598221034ff749822101cfe7498221004fd7498221034fc7498221014fe7398221004fd7398221034fc73982210067f53982210067d5398221086bf4298221086bd429822102cfe7198221036f6719822102cf67198221034fc7198221036fa7098221036fa2098221086f92098221036f7109822102efb1098221036f81098221004ff7558221024fe7558221004fd7558221024fc7558221004ff7458221006bf7458221004bf745822101cfe7458221004fd745822101cfc7458221006bc745822101cbc7458221004ff7358221014fe7358221014fc73582210067f53582210067d5358221066bf4258221066bd425822102cfc715822102ef63158221006f5315822102eef215822102eed215822102efb7058221066fa205822102efb105822102ef81058221014fe76d8d2111ede63d8d21004ff75d8d21024fe75d8d21004fd75d8d21024fc75d8d21004ff74d8d2101cfe74d8d21004fd74d8d2101cfc74d8d2111e7f53d8d2111ede53d8d21006dd53d8d2111ede43d8d21006dd43d8d2102cff72d8d2102cfd72d8d21166bf42d8d21166bd42d8d21166df32d8d21166dd32d8d2100cfd71d8d2111edf31d8d21034fe70d8d21004fd70d8d2111edc30d8d21166ef20d8d2111edc6358d214d5f77158d21004ff7558d21024fe7558d21004fd7558d21024fc7558d21004ff7458d2101cfe7458d21004fd7458d2101cfc7458d21164ff7358d21006df7358d2111e7f5358d2114cff7258d21006ef7258d2114ebf4258d2114ebd4258d214d4ff7158d21006f77158d21004ff7058d21034fc7058d2111edf3058d2114eef2058d210067f7654d210067e7654d210067d7654d210067c7654d214ce7f6454d21
  | 16 => 0x4d3150f574154d311df5e4154d3150f5d4154d311df5c4154d3150f544154d315075f2154d311df5c2154d310075f7054d310075e7054d310075d7054d310075c7054d3150f5f4054d3150f5e4054d3150f5d4054d3150f5c4054d315075f2054d315075c2054d3100cfe76d89310075d53d893114eee62d8931004ff75d8931024fe75d8931004fd75d8931024fc75d8931004ff74d893101cfe74d8931004fd74d893101cfc74d893102cfd73d89311367f53d89311367d53d893114eee52d8931006ed52d893114ebf42d893114eee42d8931006ed42d893114eee32d8931136ed32d8931014fd71d893114eef21d8931034fe70d8931004fd70d8931136df30d893114eec20d89310075d535893114eec62589314fdf77158931006bf7650931006be7650931006bd7650931006bc76509314f6bf6550931196be65509314f6bd6550931196bc65509310079f735093118f9c73509311bebf635093118f3f535093118f9e535093118f3d53509314f79d53509310071d535093114dbf7250931157af725093114ebf6250931007af6250931006af625093100ebe625093100ebc625093114fac625093100eac625093118faf325093114fac3250931007b77150931007b471509314d6bf615093118fb731509311bf9e31509311bf9c315093118fb4315093114faf215093118f9f305093114faf20509310075d53d8131004ff75d8131024fe75d8131004fd75d8131024fc75d8131004ff74d813101cfe74d8131004fd74d813101cfc74d813102cfd73d81310a67f53d81310a6de53d81310a67d53d8131006dd53d81310065d53d813100cfe72d8131004fd72d813100cfc72d8131006bf42d8131006bd42d81310a6fa30d81310075d5398131006fb60981310057f755813115d7c7558131005bf7458131155bc74581310075d5358131005ef725813114dec725813115d7e75181310057d7518131155be7418131005bd74181310075d531813114dee7218131005ed7218131006f96018131034ff7518131024fe75181310367e75181310247e7518131004fd75181310367d75181310047d7518131034fc7518131034ff741813101cfe7418131036be741813101cbe7418131004fd7418131036bd7418131004bd7418131034fc741813102cfd73181310467f53181310467d531813100cfe7218131036ee721813100cee7218131004fd7218131036ed7218131004ed7218131034fc7218131006bf4218131006bd4218131036f57118131036df3018131036fa3018131046f93018131004ff7558e21024fe7558e21004fd7558e21024fc7558e21004ff7458e2101cfe7458e21004fd7458e2101cfc7458e2102edf7358e211367f5358e21136de5358e21006dd5358e21006df4358e21136dc4358e2114ebf4258e2114ebd4258e2114ed
  | 17 => 0x36be741813201cbe7418132004fd7418132036bd7418132004bd7418132034fc741813200cfd7318132036dd73181324167f53181324167d5318132014fd7218132036ed721813239ebf421813239ebd421813202cfe7118132036f6711813202cf67118132004fd7118132036f57118132004f57118132036df3018132036fa3018132416f93018132036ef2018132036fa201813239ef92018132004ff7558a31024fe7558a31004fd7558a31024fc7558a31004ff7458a3101cfe7458a31004fd7458a3101cfc7458a3111e7f5358a3111e7d5358a3102eef7258a31006ef5258a31166ec5258a31166bf4258a31166ee4258a31006ed4258a31166ee3258a3111eed3258a3102cfe7158a3102cfc7158a3102eee2158a3102eec2158a31004ff7058a31034fc7058a31166ef2058a3102ef71058a31006bf7650a311bebe7650a31006bd7650a311bebc7650a311bebf6550a31196be6550a3151ebd6550a311bebc6550a3114ebd6350a3118f3f5350a3118f3d5350a311cdbf7250a3116faf7250a311bebf6250a3100ebe6250a311bfae6250a3100eae6250a31166bd6250a311bfad6250a31006ad6250a3100ebc6250a3118faf3250a31167ac3250a31007b77150a311bfb47150a311bebe6150a311bf9f3150a3118fb73150a311bfb43150a311bfaf2150a311bfb62150a31167af2050a31034ff7598231024fe7598231004fd7598231034fc7598231034ff749823101cfe7498231004fd7498231034fc749823108e7f539823108e7d539823100cfe7298231004fd7298231034fc7298231006bf4298231006bd429823102cfe7198231036f6719823102cf67198231034fc7198231036fa7098231036fa309823108ef93098231036f7109823102efb1098231036f81098231004ff75582310067f75582310047f7558231024fe7558231004fd7558231024fc75582310067c75582310247c7558231004ff745823101cfe7458231004fd745823101cfc745823106e7f535823106e7d5358231004ff725823100cfe725823100cfc7258231006bf4258231006bd425823102cfc715823102edf315823102edd315823102ef6215823102efb705823106efa305823102efb105823102ef8105823115f5f7654d310265f7654d3115f5c7654d310265c7654d315175f7454d3150f5e7454d315175d7454d3150f5c7454d3150f5f6454d3150f5e6454d3150f5d6454d3150f5c6454d310075f7254d315075e7254d310075d7254d315075c7254d315075e6254d3119e5e6254d315075c6254d3119e5c6254d3150f5f4254d3150f1f4254d315075e4254d3150f5d4254d315075c4254d310075f7154d31007577154d311df5e7154d3115f5d7154d311df5c7154d31007547154d310175f6154d310165f6154d31017576154d3150f5f415
  | 18 => 0xd72981420c5ad729814252ebf62981420dfaf6298142007af329814252fac32981421bdbe7198142005bd7198142006be6198142006bc619814252faf2198142525be7098142006bf6098142007bb609814252faf2098142005bf75581420073f75581420053f7558142195be7558142005bd7558142195bc75581420073c75581421953c7558142006bf6558142006bd6558142005bf73581420079f73581420059f735814218dbe735814218dbc73581420079c735814218d9c7358142006bf6358142006bd63581420073f53581420073d5358142545bf7258142007af72581420ddaf7258142546bf62581420c7af6258142007af3258142547ac3258142005bf7158142007b77158142005b771581421bdbc7158142007b47158142005b47158142006bf6158142006bd6158142547af2158142007bb6058142006be6058142547af205814253dbe7618142005bf7518142195be75181420073e75181421953e7518142005bd75181420073d75181420053d7518142195bc751814218dbe73181420079e731814218d9e7318142005bd73181420079d73181420059d731814218dbc73181420073f53181420073d531814201dbf721814200dbe721814201dbd7218142537ad721814200dbc7218142526bf6218142537af6218142007af3218142527ac32181421bdbe7118142007b67118142005b67118142005bd7118142007b57118142005b57118142006be6118142006bc6118142527af211814252dbe7018142006bf6018142007ba6018142006bd6018142007b96018142527af2018142527ba2018142527b9201814202cfe76d85321857e75d85320057d75d853217dbe74d8532005bd74d8532004ff75d8532024fe75d85320067e75d85320247e75d8532004fd75d85320067d75d85320047d75d8532024fc75d8532004ff74d853201cfe74d8532006be74d853201cbe74d8532004fd74d8532006bd74d8532004bd74d853201cfc74d853200cfd73d85324fe7f53d85324fe7d53d8532014fd72d85324d6bf42d85324d6bd42d85324fef631d85324d6f621d8532034fe70d8532004fd70d85324fedf30d85324d6ef20d8532006f7619853202ef66118532006f56118532004ff75d8132024fe75d8132004fd75d8132024fc75d8132004ff74d813201cfe74d8132004fd74d813201cfc74d813200cfd73d81323967f53d81323967d53d8132014fd72d81323febf42d81323febd42d813202cfe71d8132004fd71d8132396fa30d81323fefa20d8132006fb60981321857e75181320057d751813217dbe7418132005bd7418132005f67118132005f57118132006f96018132034ff7518132024fe75181320367e75181320247e7518132004fd75181320367d75181320047d7518132034fc7518132034ff741813201cfe7418132
  | 19 => 0x4d420073d7054d420073c7054d4218f3f3054d4218f1f3054d4218f3c3054d4219f3f2054d4219f2f2054d4219f3c2054d42005bf75d8542195be75d85420073e75d85421953e75d8542005bd75d85420073d75d85420053d75d8542195bc75d854218dbe73d8542005bd73d854218dbc73d85420073f53d85420073d53d854201dbf72d854257faf72d854201dbd72d8542566bf62d854257faf62d8542007af32d8542567ac32d8542007b651d8542007b551d8542567af21d8542567b621d8542567b521d8542005be70d8542005bd70d8542567af20d854256dbd76985421bdbf7598542195be75985421bf3e75985421953e7598542005bd75985421bf3d75985420053d75985421bdbc7598542006bf6598542006bd659854218dbe73985421bf9e739854218d9e7398542005bd73985421bf9d73985420059d73985421bdbc7398542006bf6398542006bd63985420073f53985420073d5398542575bd72985421bfad7298542125ad72985421cebf629854213faf6298542007af3298542577ac32985421bdbe71985421bebf6198542007b761985421bfaf2198542005be7098542005bd7098542577af2098542005bf7558542195be7558542005bd7558542195bc7558542005bf735854218dbe735854218dbc73585420073f53585420073d535854256dbf7258542007af725854213daf725854256ebf6258542127af6258542007af325854256fac3258542007b761585421bebe615854256faf2158542005bf7058542005bc705854256faf2058542565be76185421bdbf7518542195be7518542005bd75185421bdbc7518542006bf6518542006bd651854218dbe7318542005bd73185421bdbc7318542006bf6318542006bd63185420073f53185420073d531854201dbf721854200dbe721854201dbd72185421bfad721854200dbc72185421cebf621854255faf6218542007af3218542557ac32185421bdbe71185421bebf61185421bfb661185421bebd6118542007b56118542006b561185421bfb65118542007b551185421bfaf21185421bfb62118542557b52118542005be7018542005bd7018542557af2018542005bf75d8142195be75d8142005bd75d8142195bc75d8142006bf65d8142006bd65d814218dbe73d8142005bd73d814218dbc73d8142006bf63d8142006bd63d81420073f53d81420073d53d814201dbf72d814254faf72d814201dbd72d814253ebf62d814254faf62d8142007af32d814253fac32d81421bdbe71d8142005bd71d8142006bf61d8142006bd61d814253faf21d814253faf20d814253fba20d814253fb920d8142545bd7698142005bf7598142195be7598142005bd7598142195bc759814218dbe7398142005bd739814218dbc73981420073f53981420073d539814252dbd7298142007a
  | 20 => 0xff5f63581530057f72581530076f72581530056f725815319d7e725815319d7c72581530076c725815319d6c72581530067f62581530067d62581530073f42581530075e32581535d75c32581530057f71581530077771581530057771581531dd7c71581530077471581530057471581530067f61581530067d61581535d75f31581530077b60581530067e60581535d75f30581535cd7e76181530057f74181531a57e74181530073e74181531a53e74181530057d74181530073d74181530053d74181531a57c74181530257f73181530157e73181530257d73181535c75d73181530157c73181535b67f63181535c75f631815319d7e72181530076e721815319d6e72181530057d72181530076d72181530056d721815319d7c72181530073f42181530075e32181535b75c32181531dd7e71181530077671181530057671181530057d71181530077571181530057571181530067e61181530067c61181535b75f31181535bd7e70181530067f60181530077a60181530067d60181530077960181535b75f30181535b77a30181535b77930181535adbe76d8d42005bf75d8d42195be75d8d42005bd75d8d42195bc75d8d42585bd73d8d4218ebe63d8d4218f9e63d8d4218ebc63d8d4218f3f53d8d4218f9e53d8d420079d53d8d4201dbf72d8d4200dbe72d8d4200dae72d8d4201dbd72d8d4218fad72d8d4201dad72d8d4200dbc72d8d42596bf62d8d425a7af62d8d425979f32d8d4218faf32d8d4218f8f32d8d425979d32d8d42597ac32d8d421bdbe71d8d42005bd71d8d4218f9f31d8d42597af21d8d42005be70d8d42005bd70d8d4218f9c30d8d42597af20d8d4259dbf7658d42005bf7558d42195be7558d42005bd7558d42195bc7558d42595bf7358d420079f6358d4218ebe6358d4218ebc6358d4218f9c6358d4218e9c6358d4218f3f5358d42585bf7258d42007af7258d4258daf7258d42586bf6258d4217faf6258d4218faf3258d42587ac3258d42005bf7158d421bdbc7158d42587af2158d42005bf7058d42005bc7058d4218f9f3058d42587af2058d420073f7654d420073e7654d420073d7654d420073c7654d4218f3f7354d423f53f7354d421971f7354d4218f3f6354d420071f6354d4218f3e6354d4218f3d6354d4218f3c6354d4218f1c6354d4219f3f7254d420072f7254d4219f3e7254d4219f3d7254d4219f3c7254d4219f2c7254d4219f3f6254d4219e3f6254d421a72f6254d4219f3f3254d4218f2f3254d4219f3e3254d4219f1e3254d4219f3d3254d4219f3c3254d4219f1c3254d4219f2c3254d4219f0c3254d420073f7154d420073e7154d420073d7154d420073c7154d4218f3f3154d4218f1f3154d4218f3c3154d4219f3f2154d4219f2f2154d4219f3c2154d420073f7054d420073e705
  | 21 => 0xd72d855319d7c72d85530073f42d85530075e32d85535f75c32d85530077641d85530077541d85535f75f31d85535f77631d85535f77531d85530057e70d85530057d70d85535f75f30d85535fd7d76985531dd7f74985531a57e74985531df3e74985531a53e74985530057d74985531df3d74985530053d74985531dd7c74985530067f64985530067d64985536057d73985531df5d739855315d5d73985531f67f63985531775f639855319d7e72985531df6e729855319d6e72985530057d72985531df6d72985530056d72985531dd7c72985530067f62985530067d62985530073f42985530075e32985536075c32985531dd7e71985531de7f61985530077761985531df5f31985530057e70985530057d70985536075f30985530057f74585531a57e74585530057d74585531a57c74585535fd7f73585530075f73585531755f73585535fe7f635855315f5f63585530057f725855319d7e725855319d7c72585530073f42585530075e32585535ff5c32585530077761585531de7e61585535ff5f31585530057f70585530057c70585535ff5f30585535f57e76185531dd7f74185531a57e74185530057d74185531dd7c74185530067f64185530067d64185530257f73185530157e73185530257d73185531df5d73185530157c73185531f67f63185535ef5f631855319d7e72185530057d72185531dd7c72185530067f62185530067d62185530073f42185530075e32185535e75c32185531dd7e71185531de7f61185531df7661185531de7d61185530077561185530067561185531df7641185530077541185531df5f31185531df7631185535e77531185530057e70185530057d70185535e75f30185530057f74d81531a57e74d81530057d74d81531a57c74d81530067f64d81530067d64d81530257f73d81535df5f73d81530257d73d81535ce7f63d81535df5f63d815319d7e72d81530057d72d815319d7c72d81530067f62d81530067d62d81530073f42d81530075e32d81535cf5c32d81531dd7e71d81530057d71d81530067f61d81530067d61d81535cf5f31d81535cf5f30d81535cf7a30d81535cf7930d81535d57d76981530057f74981531a57e74981530057d74981531a57c74981535bd7d73981530075d73981530fd5d73981535be7f63981531175f639815319d7e72981530057d729815319d7c72981530073f42981530075e32981535bf5c32981531dd7e71981530057d71981530067e61981530067c61981535bf5f31981535b57e70981530067f60981530077b60981535bf5f30981530057f74581530073f74581530053f74581531a57e74581530057d74581531a57c74581530073c74581531a53c74581530067f64581530067d64581535d57f73581530075f73581531155f73581535d67f6358153
  | 22 => 0x24026001000001c010004014801800c00000481ec05600000000180120040020000000000009800400400600c000000200f0058014000000000001c00200400000080140150010000040000010800401e01d00c000800601c0048074020005009000001a000000802401a00d000804800e0010030000000000001804801c00000080400080000008004002004004000400e005000800400c01e0230060002000003004801200f001807400402b000000400a00300e801009a017004000000a0000020008038002002807c008007003800800200b01e80c8000000009001401000000e0000000002000802400000100080380000000020004054006000000c004003011000400200000300040020070018028006002003801c026003006000400000000480000080100000108006006009801401a00e010800000e045005000000200900000240040100130004002003000801000601200a000001402f0000004000000000000000403800d8014062001000003001a00500000980120080010000004013000802c000008004000000e00000780040000020020000000003000000002e012000801003a004000000001a0080008008004024001003002800c016803003c00600b002800400000880040020040090024006001008800002200600000480140130028014030001000000804a00700200200220050070000012013017003403800000b000000000400580000040010228014002000017800003c00000380300040270018000000001000801c00a001001800400000a000000000e00419d7e76d89530057f74d89531a57e74d89530057d74d89531a57c74d89530257f73d89530157e73d89530155e73d89530257d73d895319f5d73d89530255d73d89530157c73d89536267f63d895362f5f63d895319d7d72d895319e7e62d895319f6e62d895319e7c62d895319f3f42d895319f6e42d89530076d42d895319f5e32d895319f6e32d895319f4e32d89536276d32d895319f5c32d89531dd7e71d89530057d71d89536275f31d895319f6f21d89530057e70d89530057d70d89536275f30d895319f6c20d895319d7f76589530057f74589531a57e74589530057d74589531a57c74589536157f73589530075f735895361d5f73589536167f63589531875f635895319d7f72589530076f625895319e7e625895319e7c625895319f6c625895319e6c625895319f3f425895319f5e325895319f5c32589530057f71589531dd7c71589536175f31589530057f70589530057c70589536175f305895319f6f20589530057f74d85531a57e74d85530073e74d85531a53e74d85530057d74d85530073d74d85530053d74d85531a57c74d85530257f73d855360f5f73d85530257d73d85535f67f63d855360f5f63d855319d7e72d85530057
  | 23 => 0x4000800000c00c002000400000e002800c00000301c800001805c00500000000070030000000000000000c01400301b800801c000009002808800d002003000000000c0060002018001000003600f008806401000000a000000000400200ac010000011800001400b0050018072000000003801202a021802000200c000003c008004003011c014005001005000000300a8000002024005000400c004007800000e000000804400a00c0030000000009001001400a0000068038000047017000801c027001000c00e00000000680020130028048042004001000c008000001804c002033000800000a00c004804400400d001000000a00900b00c800e002000801c0280040000030008012000007000400b0018064004000000001c000000005001000000100180000020000000064018000000005800002100e8068002021001000c0000030000068014002000000001e000000001c0060090018050000003006801400000e000002000000000080040040030130000004000002804002a011000800000009b021800803a008018000007200d003805c006000001003c02e004000005800a007008000400001100000dc00600200000000020020038004012000003806c01200f020006000600100f800403200e002000000a004001801801203400000080180060010008000009007000400000d000800400800e0028088000000001000800200b00400180460000018004054000003002c00200302f80340320010138098002006000000c00000000000300340010020028000002000006000c00b0078014000029000000406001500f00bc00200000e0028010006000002800800500f00040020090000034030001006000802a0020020004008003003800c022002006800c004011003802804c01e007000c00000e001000000000c00900380100070010000012036000003c000000001002c0040010058000000009006000400000a0000004002005000003401e00000e804c02e00000000240220010080118000002000003c012001000003005c0140000000016021001001402000a00000240080010010030022009008800800002600b000002e0050060010004018000802401a00101a80a400a00b000002001c003003000c01e024001801000a0010038000000003002801000400e000000000000f006009c0100020098000030011016803c048003001000400401a001800001800200200080000020058000006009001802402600b0020060000000004000c00600900d009400200100200540420080000038002002002800802c005002800800000e000001c002055005003000c000002007401c00100101080060080010004008005000002c020006001005400600001e001c0100030038008028000000005000000900080180440160
  | 24 => 0x16e000000086a04b214117491a3ea0000fd878e000293dc545d900022953ec8bd2ea0d447a0b7b32916ec736459000000067894e1632c71c38df439800001cc2af000378c5e05c16a500003ccab50000000782a203b31811a686b908b00002ac53c0cb1f2074605b42f9e780e62ef19da0b1a8c6bb687b239a5a01f68a8c00cc63e05ae9b00000c8f000000087ac130cd000000000015e3a74d00079000000196874c0002ea92327880001a705687c174880000000000b29e740001051a1928dcca3444310000e30455000037cc747bd16908f495097652810a535200010ba0f800024156d80000008600003548a1800038d9d78000e022390f7d7e66b34c42d5800080e0dc1e31d940000638c79136e1b0003201b048e158c1965438523546185933e6fa43e2dc00003ac00000009d09c42b8bb08b18ef360b00000005ef344946036297821d2a05cba36c0480a20800cc6496b6742c813714b1d5d332931000000176ac073561d5825ea855d9b8b4ea897500000013604e92c19a555a2dc048508a80001e9000000195857031a1d8432e00069eb58d2261862322f3cd2690247c24ecb98a6a245a57531e53f4b89634286a8e4491e60000bd42acae85008b9b6d200000000000c1800032abfb13ea23c1e89201ea17c57d82401f8293547625f6bc9250ed663f58180cd1201a71552ba82be5550000a4d81eb9a52123e8910a65000150049a11471284d13bc81d2b4ad143ce5ee00039111680000000001d8600056433700000100034014009004800000000300480080020040008000000003004001016c00100900c00040010140128010009000807400a004007800c00000100680400000020000018004000006001001c018001000401e008004000c064003000000000200c000004404400000000140140220018018006000002800000c0000088094016000000001c0020050060038006005001002c01801a010000802c0060000000016000002000000c00001b801000600000100080000020008008002001000801802603600000200700000000008000000001008000e0020050008004017003804c0020060000004012002006000001e007000800000a00300080100100030140000012000000003c0040280018008002000003803400000001b000000000600000300360070000008012005000801c022011000000005a01a001000408600c00d001403a00f00280000000010000000020003002800c00400501d000000000000a800400e002006803c006013001801002000000600000120000100010008003006801802400600000280060060000004010003000001c0560040010020052004004800c006009001802804800200300300200060008008048001000803c0020040018094010003007001800e039005800402201900000fc
  | 25 => 0x13e67c650e84a1712c5c51a80006340006219d70b7a00005b1450e26000415ab8400009a000000000000038e800162473758fa1580008bb2419194ea6d2a3ec1125128cef26500015501c30001fb9ab24a40ba0000f649520000bd9280b672d12a519421fc45a87240880001418001bba23429301d4d9668a1b5a6e9ca89bd0000000afc79944e0000c3459c0000000000406000361d5b200055880016da000195072c000cf600007507187fa0be9bc00001ae6f7a6286a6a370003901458cb31b50a91bdcbef00010407f0dda0002cd8f02646142b2f5c4200063b0e84a38e7e000042125cb080000998aae37e0003764f0c8ef1908000ae85e83f080003ca9f70f8aeb4dba4ba14100006740000000109908e0a60fa220000e9768d000157859924e2e2800000000024e4000000000000013800000034dc000b1d69d96e913a7f543893249347147239ea000000075782a440ee6c0c8a9bd7cc56f01581797c45b15afab5c10013a4a5a4c9674aeb6eb346d3380001e42f68000d196c33085750a4071e80000005df00039c9300591161188cf70ba9140a5ec7cc9c1596a49905a3244c19a1506c80123b0f3424cee8753233110409d45c96612bed096c635a547c7e40fea5a9ad893730a3b889443fb195b70d4fae3c30e2215d5410a04d8cc192a4b70179efd73e27c55fb4e8e86de50568be92e461114c3ab033c00000013806c0e0f76e9181d56e9b7112da10f063b66739c19d08763e98b210527f0636965c3d072c19a3475d14ce71bb14c5bd237b1b7a84ca5ae2671c21b87b27771dbb96d5522b53ac2cd57186a000000e944aa0e17e2645c62d8a4d299b0e4ab7d011a8886504e30000448500c390af1eb53dc102556123cbc207001505ccdc80001670a98ec0d1040f8000000b3e59da7a9b609073141885b7c1b435c2ec530a631003298872a0000002bcc0002510518384a1200027e22900005502f2a6a81c6741000202427082338035ddbc47a045900007168544202d293280ec5e4080504496731600000001ac127b48c31eddf225acac00016000027ec95a00037f03715ea0c256b27e5b62a100000920f4645c61414f571a5eb63a38cd8283d30928e353feacc50c2bf53969ad6c19a79d0a5562411c90000de01a41de4cfa9d564d956c02c6af11a84cc8d4cdf067afdc9c253800036f1daaaf246e313527ccb60da8000efea450000001d6200000007ad18e54f2780000c7a2eb00013dcf58ed85c5a2dddd4000039084d180000012aeb051a0000003481246a61000269c9e600735ea4b0000b9600036040000004cd80015a8bba63cb94c68a5db15b05ec000b1100034bc0004932d2913000000070c000045c0006623459a90c992c3000000042012c8524b169cd54989891b400013b32616cc0000000000a0e6a133a0001d88
  | 26 => 0xc9dc66c85dcdbc5e74b02e08fda6421b08b28732b0e3a51edc66e2ee5699e34194005385a4902301a335ab831c7c43740c91105aa5f51ef31e988c41128114ed646a876aa000157240c7730ec84c2163617ba585c0c0628220c587c00062bb668ee64925a80d6cdc4b1348a1774000bdf424adf8000000000000136e22b4c205d9b72d3e10c000000000050a26c57e879f218800000000066297900000f20000000000e8c55a3ad9a428e8063084090a0007313128000957237a625b8447c00020cd87a668374000000000000018ccc6a0004582a3d9c60003ee97fc0b01ab1ed24499fa34e0ebb3955c69a05f08001cf8a02711b0f152ccf93fe000074c9df2792dd063854a000000171c0e4562b31c17a46914613e094c00066d87840008386e2000180888347a97080000000000000fbe95a00030700002cb000000034868740f0001d9868c294bbc48481bc49e1c40cf0a2165c83041e658828d94192b08fe0000035aca2d9381009c6dc18048401418dc4d527b109dcc6e0362a8aac0007cc37b9ca06063b11f211185d035216a03699da6f337f8821cae8ff3a112c0d288e303fb514ea46431bd13110842691860e09c5c6c54018470e0c12e0d2bacd230d0e0a0a8b4ee491b2a19a452b6ae2000000000052531f173d0aec7053212f40000fc267a3088bc32531e202c0000003820b406ea81123815e52086ed10d0e5cdea00049d1594c4c0824c62030d48c6c5e985b93986974618d94d044bb4cba34403095e0001cf515a5b320faa018ceed22a2b1ccff68002bb8d1db44ec11f780000008d80001c0cbd22e62ed00008b4a8400015080009270ec803926cb2f1bcb09d686cfb6af0c203d40513cb35f81aa0004888a6489c7832068000000443473894144e00000034004726e30e383946a80004b30048ccc80a74a34fd980c596d31505144bd05178e450c8ae4749af90766a1732fb124ee84c624fb2200001096933725ac0e170ae86ec00000042f00000000fd000000005a0004640e4149c00023589ddd8a7de1d7b729a4e2f25ea841d74000022b0778000e8f2df8000f6cd801f6268dd4414773026d06e81425e1270d9869860000001cbee1d33810ec44c44a5820cc82166a66a03a1000000001e0211be62285dd80013ae00050680009beb320002f6c7340006ae0001da07703191df04b60003470000000d7f000000197e0000a58000000a480001cf940200072caf1400038a00000019940002338001bfe000000000127aa51000000088e0000003479260ebf00039492c6a884711ce95be6a7009a9d9d9e07a4f693f561a7366d40519c8ab3f20e1f994163ca45480000005bc4f12c004468ee52b9a95d0e56129b10f1db20000b38000e780ba043b0391cce9048f0000edc295629267416200074309c9b96d3603b1ba8f38dba73a
  | 27 => 0xe1a6c27e2702612c6ced4ca90ac2f346202335b71dd4b3c7b01acabd8000000524b2080001f0000000179cb9401b8000c70acf7418170774ed7000000014ca29258abf06faaff6d4b5c18c60003bf0000000c3200030298ac6e0068a0d400000020700009a20002d82c55060000036adbc22e7853fc8ef40009434781b352de6764132a1977eb580000008adc0005df1e25a04e515913a70ab4aa03491758a2c60a1340468ad04c83d289b91160004b080019440b2104a60464462a00000013c2bb9000000140c5ce640b6dd9507af59ca511c1a0d34df02916a645214e2d497b20002450000484000000262dcfe5c92cab5880007f24659928188ec86ccafb92a8df021a2f186acc6626d9978586b863b8ab610f472d3ee3985c9636d492990406c0003f88000fec2df6388404000b9100019f976c05d00021b40004543828295984cba531aa95d80aa40001a7dba03a830983c12a2d4d1a5b5c4332d7d74d0b885f2cd2326b235dacb755ce203c9022212fc1ff856255c4c382ecfd4da356e9c55bccc2459c01196045826e32b791a800001800004d6e55148919857407d2548fc5d921e00bfb3314c0b2e666a51c88248628986dc0006ae55f28458de000361000119ea442681088000b4f5c90fdd1c8b87118140cfd0cbc0001d18ef6aee010a06d9e63c344c154c8dc0ab53c96009321825d1b65dc748d0476a9b5b8accb06a10e58625c50000000e4484f64320f11087446a8287cbfa1aa00513e81123f54d637ac730cde4bcab0916c7be259b02c3f050b7248474cb015a025092c544e4833e37b0e4e3b9014aedc3c42714f42e4134c4090b684ac1bcd6b6d6803007e08c0e739a108a549451833812642f45c2f2d7ec7ff5b6278d9906a2594822d2164383b2b420e3ea786c7000054e7b172d000199ec5e33529c4b723fd0000c9cc1aa042a60001c0e4d647e0f7181a1201a602d4abc81a26a005d0a210e2b631389dac5d6460cbcbf68750000000d54b810b0b51cc48b7c00026a0be4b635252b34a1ac645d8187909cabd0680dc50ca0cd10a00c89ea9ce20a1afda866c8275a311dbe2ea0000814000dc100000000000005da14a80003332aa38ecc9085a26e1bb164e5854a42bed83009136703e87548aa09633dc21a2db6ec09510e60ea7252c5c00090e2a3a6d554c4175aba978ac60085eb2b55b2c4161eeb73c00025a259367c12a62f417012c3ea2537781681d9ace011fb6fca2ec0071800014b87a902682bc000b1627f800055c1be771966d576000346b04932cc7f36a00000001d361b2c64ce600013d1bec168498236840d2aadab6043544e6217e5cf23ac6c8000242362cf14c2e4b69b6c00045d5932ac844e75a6aab0ad19492b39c8000d6c6904a30fe4b528fb0fcb49031820343ba0098846370c4b9e8b943bb0b10c18e9
  | 28 => 0x7801b53d27f8700e2412e28155a465d394b00d10eb42333a0e4f44e011df0be0e9624455180007da2110319300a9ad7a00002cd89803b316887000046337b00017e20001c99df48041450001be49c800000000006a00001a080000001150001954000b34197194d2d20004b4000000038e0b803a40009b200e0000000d8d443373853c5280002b183d821f0003a64abad5a4631fd000072b4790000000d881768064000ce64912b8078e00000005a053476871b30e1450e0e1451a05b40dd100025fcf806ef3b62ae8e5c08107d88282882453eb88b0710c3768ba82425a6fc2e903b51823cc1252524f9453e15991dc0000560000b5cbc0c65000217128abe30eb191cfd2edc201a2b86d2b4c29c8961678b013430000ef40000738f9d9d4caa00028cd55c84b2df0bd52e668360d0490f4800002d000146412359e9ff400011f18a252800065134eb79c000290101000000088134cb6d5a88af11a30e492546d6243af611ee3ee63f0000da400064e000000044d2920000000b4b30591e56542a0152a4717d4c0c6fc0bcccfe993302a1d050c0003622b1d9b437837e800000001a3128000796d074b100000007d238719c4000b8f17a0001680d4c000000135e00000014200005c41ff0a380f026577081ac7060ee1f52fc954211b6770ce1cea8462059641ab650e3b1b4047882fd25cae997641df3b3bb6c5d8e34000000108259f472b21c67a1214c7010c5ba8966e906382527c438d08800e80a70d08afc42cb540000e740005760290f3c1609b33080000e4c140683057000053200033e04d4bfd0001c45c9e34f1d4b55c91cee741b87d1ade9214223120e180000000ec0222ebb5e4abbcb140005e09cfc000e2f22d86c14342c52132d659126c13afa40c3101941ea87dd5b84915d2b50800000000000009f239f00000000006bc65225f000000015806e5b30a986b390140001a8004992592c000740ac24000c772b3b8dd0b0dfc57c34152dc13933104a8b96eb7546a2450424aa000224cec84012dc04d543623860ba1fd4e870f6d096d17060000000000000d4e585b35800056b5d72748474bff06c1e40afe2bd1509fdd3e89a4303000000071e0000000c443e500000000003156101d890cc6d9000000055200046b1369b3600024e9488a02eb037a02e0f2a64422c13b109a7345bcaca13e49ec30bb2503145482672d8411ee0842c86480004714b2b004264ca523e8000000d7628a80005a61a93eb311d96a31200000008fe9fa25b10d50d227e0003075bd0c296be098000000018d8811b540407770001ccce1f30c8001d3c17a59806147a4b5e52b2ef552488e3dd28fd04ace41f91734d4662e2d7182509450a3c8ad6c1ee7d551c8c044322562f5295065272a36aba2c44a52b446b649d686c7497b1c9690b0f6d90e24f8eb1e0c
  | 29 => 0xc7108d6caa6743198c0c00eb80000800f2e6cc1d7055077e90d5358001b669f10000000000c8b00039cd06873367f85e4d646600f1a0e8ea241200009b0000000433a4401280006afbab5cdc3b43f7b2c00009d66a58001162b85648b140b46a9d14b9855d3e3b80a40a2c47c43f18c2ebc0ca814754101c99a5d3282a609bf6cc97508c0913e0102f1814d2fc0000002a24cdcb1a0a53a348640033421fe0e422753841f3800020d3da8000000dac000254d5960000003575a502376a49809b28000000171c486000464b918c6cc111bb947d9fc2293d584f821843301a1610be649647019aca344ee0002ab45ce06c74a86fd748a5f0573959956d901b3b4e4524a4626c32c4576620769b0418a81c118c860595a3eb3919ba5d129ef56d02e40984cb64f96b0000ba23bb00006089fc3f18001934c6037892300000884150c5c7d062b390000057cc300002750ba2e2b3c20001b4e7cf2558599498a4b28813bc00000066aa8300005580001348c960c01fe16dca3256a045296548657d4828c252eeb6a3b78150d86d6418380001b2000000000000099000014bd5867c540921ec01664005509544ae00062db114eda5921a522cda1a25e3cd27454fc1ba4ed00012680002ca2f1d7da8ab7161ee45bcd7577a175c390ac93138e517f8a7f72f27242f81f638681b8af03c9017071481e42500000019200006bd904da701b33d50aa11fa000734b6947f4d1f4e780000000000000000000df600005d4a661272f80001d469d048e800046c5211af143c000d123a7b5d00000000000000bda000000000000060175f2a0882a0000001e3c0000d220f32b984ac5a0d68001b986721d12d10000ecb000000000095c000131c3640000003844ca8d3c24d8001c2aa6e33280000000004e400000000003c10b054b03a40001c482d6249000035c000d842e00000000000630b35053652063c181d5f214e6c8b3f000000000000000004f100000000000000002e209ca0002cd08540001a230da45c000e285050001ae485d562193807286c5901f44fb45d80ff8000000000347a535924c0932835b40006f863511840009dd09ea90527e0004a083e00007593eca11d3423872e4279907e0000ac8000a8c0001238000f78c930f73a08fd644000030a932adae00032740000002e33784cf202460a8cfc00067700000000007e50e036d8da2d566da3a38f84a3d0c81e6cdb42d840b8df0c1ec0525601dcd10ace09da3c4000c9e555a41843abdd24f19310e0de4037ad911a6d14000179919ccdd0000ba47c4061560334dc824ea51239414f656429800018040000002820260e7830e80008a281300024a52180000000e1455868b3651314b4c78b00036ec0005b20b612858960112888000000c8a0000001b1228f72c28b819620b4f005c88e648d59889e02
  | 30 => 0x6c4b930000f452e0e760e509751a40a80003344b2c2a376a2284f689280000001c2600009100017ea0005b000011e65604669d1d72e0001eb80002ae9bc49c00016d6d85714b54d5fc3a0732117cd6e7075512eadd109bf19620152e8b372d202fcf5cce90e6306439a0486862d3461a1932fb28980fce715780cd80b23725f03858388be76f92c1d614a3a69ab8e57e0a5d65c37c515ed9c5a3a9483dadd544b8eb53b0b985fd3a61ad020647b0400000b25356924109000000015ec00035d38ca1a13700920001684c723f604f800142a3e15ce8d548e87cb1b981c59d60000b48000000c2d0000fd000047e25aa1bc498a34273a79531aeae29a2ef18ea349000308c508c5365d800047687d132281c00034d25c0b3d4e696b57d335c30e3a72c4b89d5065f4185afe1858e670020000000e1e0c6a8c1a143ff000237c5a2bd2480a2fda3841d5732a7809269a205266173200045625e983c33e0e91d14cdebca1968718e642fb46f1a6036c09e118bbc802acf46b333c9c08198474b8654ea2c40ee1e49c0aa725e22f78000b623ad8000baa0000cfa2f9d784a069714b8aa20003a003bc3e6daf51b3770dc27550348e94cacbf90001789ba6445613152cbf2d0b6e3b80168c6be06180000008725dc0d98a6a9160ff083db26c69064bbac62c0982da9068626df526e9598106bfe4e027c03e46e66898848738c3576394e876ab7f57bb34004c4ae6dc34101fc00023d28594620005bb000021e2674fe8b3155e30561a3b18198d2c3a82cccc3000003e214db2a65c0500cc4f92dfa000000092e06732ba8a99c48993a4a36d4d07932c0953870c9d976f39a861c4212ff147400082765b92d1dda97d00033607ac69614ea278af49db07132f93840572d40ac8bd8c85306134c9e814d10f22287024be76709385b4ab074008f058e1361168bf9a06c971a11b4d7ca0621850768f4c44255c0b3476c7e767d0a1c9825125c22a4145658f75482dd1e80f56fba80100c06672604405ac335000390c9c4041215b84136c9f844600010768200000e112849ca2579ceda4a70100000501c06b400010f88f065b7270f8c6b840852aaad829e81046b83152987a70002455648000670b4c4fc4d78322b7217d637f33a8bddc249d3027114c57229f33d03a156e2b8000b17c00042d0eaad3901a08638b1f3405094f0340b00f0e9ae5d389fd72aaf40bc0001d7400000011b141ea1e00023b08904756e68c8c0c8dfe000054d0a4a9a7761e518c45270000374cb4c6b0002da477800003d8000000caf0001de0bb8d4f13989195166646980001bd4396000375d1aae776b0b1f1a44a382db03d96a20f957380002326ee0002fa400003500f00001d60004dca6ed2d82e4660ab400004626f6bb90b4e0001eda64803abd10ce8d7cb561c254a90d9b3c72f2
  | 31 => 0x6b980000004194ac8001c7e2e35e61779098e5c00000f9536df9117800000000038e0001200000737b3c000016f0001549940c83187bad507ad114e32f5cbf42633758154f761a00f78da0860c7b1a039ed60a47b4f38740ed200f1ac2b0400082f736a10d356861753b8c926a00000006980000003d9af0d9e2ae538496b4e2eb5c54cb63cba090906b074514ea692baa059a56a3c4e3ad54c3e4fe5960001432e793683111bbc2ff620b8d49ae2e13a6823800000026f2f002aa89a00000009ccebd08216bc64ce421b180000006d71f4800154e99a4e287747b0252627a2006e042e21438194f800013da29878a1315ad22a00005aa00039ac000e7d3e8198400000000031a0cf6b140001b70e14c1b010000103057352d80002a00476200fcd34419b05e0f01d400ac6949b614eeaca487a9c007a6cf1060610dca66955518a4dce815676000039e58761d2bb0a6e81c2ce821587ea9c2a200010d6113178a88dbfa05f41414b06401fa35d0115010b7761db29dda220e0003ac8b26562000025d7d09eb76d000063a000336b86900e964699b144836489364aacc4646b16a0993c0000007702dc8fe66ab5b89f6c000b0c000356073cea475c8d680006a900014002987a108325580d421b46c947898674867abb954b44a74a83880142b490002de15141db576b9356e68bc5ee076123e2b742d8a245920be63e8000d60a475092c848a0ca32e19cd40006df54bb0882d4b4104c8088c1cea5548836c4e857c2af8c7c444ca60d789bc8ae9e968c34c986642a136a15411a2943042c180c089500013ecf8648045000e0000b7a2278b94000a6c3541bc9406ee9000184880818b1d580015d2e0b06400011d44cc0000c4400000054f92f00000000f215c809e00019c80015d099e000000000000041202882a48dd0163751620a536edb85037a87e1ab97dc8d07807048f0844815b07f8ab42e2dbd1e703c506473830197f1112c581e332c89b28f93aea1e5d24a666b7000118a7e00fd925400000008f000006200025292fd2660002b69b1800027900035a88309e421605457009f57778e3c
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8bf825d9420400195f04bb284080032bcc9765081000656192eca102037cb4815d9420406f95e42bb284080df2b485765081000657902eca102037cb7105d9420400147f06b2a84080e70fdc9655081000717b92caa102000e2f325954204001c5864b2a84080df8d1c565508101bf1790acaa102037e2d215954204001c5e40b2a84080df8dc4165508101951f42ac6a102000e1f5358d420400155f04b1a8408006ab209635081063747992c6a1020c6e8c3258d4204001c3d0ab1a840800387615635081000747c12c6a102000e8c8258d420407393ee4b1a8408003a3dc963508101bf4a38ac6a102037e8f2158d420406fd1a42b1a8408003a3c8163508101bf4b882c6a102000a3f8654d420400147b0ca9a84080030fdd953508100061ebb2a6a102031e1e6354d4204001c3ac6a9a84080cf8b98953508101e786192a6a102003aae87589420407395d0eb1284080df2b61d625081001d5643ac4a102031aae83589420406355906b1284080038bd4d625081000716a9ac4a102001aaf81589420400355b02b1284080dfa91c5625081000d57c02c4a102001aad80589420406fd4e20b128408002ad61b71508100065abb6e2a102000e3565dc54204001d2ac7b8a8408003a958b71508100346e41eec99020068ec82dd9320400d1b90eb1a640801a3b21d624c8100052fc32a69802000a5d8654d30040238beeca9a600823f87991534c0100070eb22a6980208ee4e6254d3004001c9aa6b126008002abe19424801000556c32849002010caf7650920040f7c5ccaa1240080038b59542480103d74731a849002000e8d6350920040018e8ebbb220080032d1d376440100063bc2eec8802000c7485dd9100400196f09bb220080032d21376440100063ba9eec8802000cb742dd910040018eeedbaa20080029da1d65440101b53a43aca8802000e347459510040014ef06b2a20080038dd0965440100363bb82ca8802005e7370595100400196eedba220080038d59774440100055b43ac88802035ab4875911004001c6eeab2220080038d1d564440100071ba9ac88802000ab782591100400d96ee0b222008017acdc164440100072ba9ac68802000e568558d1004001cab0ab1a200800395dd563440100072a3aac68802000e977458d1004001d28e8b1a2008003a5d0963440100366bb82c68802005ed37058d10040012e90ea9a20080029d61953440100063bbb2a68802000e356454d1004001caac6a9a2008003a9d09624401000733baac48802000e64755891004001d4d08b122008003a9611624401000753ba2c48802000ea4745891004001ccea6b1220080039954d624401003673b82c48802005ee37058910040013690ea122008002ad61942440100065bbb2848802000e35655091004001d2ac6a122008003a95894244010
  | 1 => 0x902bb2a6080ef17cc57654c101de2e98aeca982000c5f305d953040778ee20bb2a6080fb0fdcd6454c100070fb9ac8a982000a3f825915304001c3c64b22a608003870c96454c101df1a38ac8a98203be1f315915304077c3a62b22a60800387cc16454c101df1b882c8a982004a5e8758d530407d8bd0eb1aa6080ef1761d6354c100252e43ac6a982033a5e8258d53040674b904b1aa60800387d096354c100152fc0ac6a982002a5d8158d5304077ca8e2b1aa60800a97e016354c100152ec02c6a98203be571058d53040014eb0db8aa6080031d5db7154c100071ab26e2a982000e5563dc5530400717d09baac4080022f613755881000c7ac0eeab1020378bd879d1620406f55b053a2c4080163d20574588101cd57c12e8b1020038be84dcd620400117b09b9ac40831f0f9d353588101a61f3a2a6b102000c5f7354d62040058b8e6a9ac4080f3938c953588101e726192a6b1020068ee87d49620400159d07a92c408002b360f52588100347643aa4b1020068ee87d09620407395d0fa12c4080038bd4f425881000716a9e84b102039ea710d09620400d1d90ea12c408016b920542588100347743e64b102000a6e85cc962040014db0b992c408002aba13755881000556c26eab102005ae681dd5620400f5cb03baac408002b3a0e755881000566c1ceab102000aae841d5620400155b083aac4080e7a9c42745881000573c0ae8b102005ae4815d1620400195f0eba2c408003a9e0574588101bf5240ae8b102037ea7105d16204001c5ea92a2c408002b9e05545881002d7240aa8b102000aae84dcd620400155b09b9ac4080029ba16735881000536c2ce6b102000cad749cd62040014dd0a39ac4080029b614735881000557420e6b102000aad841cd620400195ae839ac408016b9a04735881003d72c08e6b102006aea801cd620400f5d30039ac4080038b9d3535881000716ba6a6b10203ee6710d4d62040774db0b29ac40800393d4e535881000573c0aa6b102005ae48154d6204001c5ce8a9ac4080038b5d1535881000727c1aa6b102000e4f7354d6204001c98e6a9ac40800399e0553588101df3240aa6b10203be4f3154d6204077c9a62a9ac4080ef99c4153588101f537428a6b1020008ee87d0d62040011db0fa1ac4080029ba16435881000536c2c86b102005ae68190d62040015cb0321ac4080029ba14435881000536c2886b102000a6e85cc162040014db0b982c4080039354f305881000d56416eca102000caf72dd9420400187ea7bb2840800e2fe0b765081000657c16eca1020038bd82dd9420406f95905bb284080032bccb765081000656196eca102037caf21dd9420406f95a43bb284080032bc83765081000557c12eca102000caf725d9420406f56902bb284080df2d1c576508100061fa9aeca102039
  | 2 => 0x320594100061fbaceab2020cbab7815d5640400b56902baac808002aba0b735901000556c16e6b202000a3e859cd640400147b0b39ac808016ada0673590106555ac0ce6b202000a3e851cd640400147b0a39ac8080fb8dc4353590101dd1ec2ca6b202000e1f5394d640400156f02a9ac808016ad20553590100061fa9ee4b202039cb710dc9640419356f02b92c808016ad20572590100054f41ea4b202000a9d83d49640400117d0f292c8080022f61e525901002d5b40ca4b202000ab581949640400117d0e292c8080022f61c52590100051f42e64b202000a3d85cc9640400117d0f192c8080022f61e32590100045f43864b2020008bd870c9640400147d0a192c8080028f614325901002d5b40864b202000ab5810c9640400d57500192c808002ae60032590100051f42e60b202000a3d85cc1640401317d0f902c8080022f61f20590101dc3ec3ceab18203ba5d839d5630400b1e902baac6080fa97e0d7558c100243f42ee8b18200087d85dd163040051eb03ba2c60801a37a1f5358c100062fbaea6b18203ec5e87d4d630407dcae21a9ac60801a3721d5358c1002d6a40aa6b1820068de87d0d630400159d05a1ac608002b360b4358c100346e43a86b18200487e85dc963040010fb0bb92c6083230f9d74258c100070fa9e84b1820068de878c9630400153d09192c608002a76123258c100062fbaceab18203ee57109d563040015af02baac608016b52057558c100062fc3aeab182000e57815d56304077ca902baac6080ef95c417558c100052f42ee8b182000a5d85dd1630400b5ad03ba2c608022b56077458c1000567414e8b182000acd829d163040014bd0a3a2c608002976147458c100070faa4a8b182000ad781551630400b5a902aa2c60800297a177258c100052ec2ee4b182000c5d759c9630400153d09392c608002a76127258c100052f428e4b182000a5d851c963040018baea392c608002a7a107258c100054ec20e4b182005ad6811c963040115ab02392c60801ab6a007258c100456cc00e4b1820008de87d4963040011bb0fa92c608002a7a125258c100054ec24a4b182005ad68194963040015ab03292c608002a7a105258c100054ec20a4b182000e1e75d096304001c3aeba12c6080e7a5c434258c101bd4ec2484b182000ad781509630400b5a902a12c608002a7a132058c100054ec2640b182002a5c83dd953040018bee7bb2a6080121fe0f7654c100062fc1eeca98200487d83dd953040778b907bb2a6080030fd0b7654c100062f196eca982000c5c32dd953040778be63bb2a6080ef174c77654c100062f986eca982000a5f835d953040018bee6bb2a6080ee9d2057654c101de3a38aeca98203e87f835d953040018bf06bb2a6080030fd097654c100062f192eca982000c5c325d953040778e
  | 3 => 0x498a20028f487589314405556908b12628800ab520d624c5100072aa9ac498a2000ab4865093144063968eca126288003c554d424c510006d3b928498a2000ea5625093144001ea2a7b826288003d454c704c5100065a324ed10a20d0a7686d962144001c68cbb2442880a29d21763885101453a42ac710a2001ae48258e21440014e90ca9c4288003555cd53885100072ab1aa710a2058e6421d9521440afd4843b224288002aba194248510005564328490a2000e2f65509214412fc58caa1242880036a50b704851012d3b436ca90a2000c7476d952144001cc8c5b2a42880032d1db64485100071a32ec890a2000ea462d91214400d1e90cb9a42880969d217634851000c7a43ac690a2025a748558d21440035c904b1a42880029d219534851019e3a3b2a690a2000d577354d2144001caac6a9a428800399197624851000753c328490a2000ba68650921440017490ca124288003a9219424851000f53bb28490a2001ea4765092144001e4ecaa12428825fa999542485104bf5232a8490a20cff2465509214412fc48caa124288003a9d8d424851000752b1a8490a20cff27535092144001e4aa6a1242880dfa9d8142485101bfd1b028490a2000fa142dc12144001f4284382428800297a19534c1100052e432a69822002c5f7654d304401b8baeca9a608800387d91534c11047f0e322a69822000c7465dc53044001aaaa7b8a608801a7521d314c1100356a432629822087e94644c5304400d7a10098a6088002aba19424811000556432849022001caf76509204401995aeca1240880038bd9542481103df1632a8490220068f686dc52044001968c9b8a40880036950b7148110034f243a429022006ae48648520440e9cc8ca90a408801af820121481102c63b3b6cb0822057cb676d9210440014e90ca9c208800b1d9d95384110006aab9aa70822000ab48650a104400396ceca142088003695c942841100061fba4e8b2820cea77815d1650400b4e902ba2ca080fb1dc4373594100062fb9ce6b2820cda77815cd650400b4e902b9aca080029ba0b435941000536c1686b28200087e8790d65040010fb0f21aca080169da0643594100053ac0c86b28200087e8710d65040010fb0e21aca0800297a0f72594100052ec1ee4b282000a3e849c9650400147b09392ca080169da0672594106653ac0ce4b282000a3e841c9650400147b08392ca080030fdcf42594101cf1b88684b282037a3d8490965040014ef02a12ca080169d20542594100043f43e64b28200087d87cc9650400147d09192ca080028f61232594100043f43864b28200087d870c9650400147d08192ca080028f610325941002d3b40864b282000a75810c9650400d4f500192ca080029e60032594100543f43e60b28200087d87cc1650400147d09902ca080028f61
  | 4 => 0x24400155b053b284880030fd4e76509100045ec14eca122000cad829d9424400195e653b284880032b0ca76509100065790ceca122000caf209d9424400147f0abb284880ca8f21576509100054fc1aeca122031a9c835d9424400155f04bb28488002ade0576509100045f430eca122000c3c651d9424400187ea63b2848800e2fe08765091000657410eca1220038bd821d9424400195b043b284880032bcc8765091000656190eca122000cb5811d9424400196ca23b284880032d544765091000657908eca122000cb6211d9424400196a423b284880032bc8076509101951f436caa122000c3e76d954244001878edb2a84880038b98b65509100051ec1ecaa122000e2e82d954244001c5b05b2a84883530fdcb655091000717b96caa122000e2f32d954244001c5865b2a84880038bc87655091000717906caa122032a3c85d8d424400355d05b1a8488002ab60b635091069f46196c6a1220008bf8758d42440011790eb1a84880028fe1563509101951e42ac6a122000aaf8258d424400355904b1a84880028fa1953509100051e432a6a122000c3e7654d4244001878eca9a84880c78798d53509100070eb1aa6a122033e2e6254d42440ade1864a9a848803a6b21d6250910006563b2c4a122000e2f655894244001c58cab128488152e320d625091000657c3ac4a122003aae8758942440075590eb1284880032b21d625091001c5643ac4a122000e2f855894244001c590ab128488003a3e0d625091018d5741ac4a122031aac835894244001d1906b1284880c6a320d625091000717a9ac4a122000e2d53589424402155f02b128488003a9e05625091009d57c02c4a122000eab80589424400156d0d38a84880032d1da71509100059ac2ce2a122000b95839c5424408b74b0538a8488002ad21971509100065a3b2e2a122049ba7825c542440090fd0bbb264880021f617764c91001c5f426ec99220008bd84dd932440010ff0abb264880121f215764c9100045fc22ec99220038bc845d932440011bf06bb264880023be09764c9100063a32ced18a2000e3464d9631441a556d0db2462880b6ad213628c51016d5a422c518a2002ad48358a31440015690ca146288003695c9428c51000752b128518a2058e5431d9531440014bd0ca9a628800297219534c5100070fb22a698a20a1e1c6454d3144001ab2a7b8262880031d1db654c5100071a326ca98a2000e5463d95314405556d0db2262880032d1db644c5100074a326c698a2000e578654d31440016ad0ca9a6288002d5219534c5100072a432a698a2002e577654d3144005ca8eca9a6288003c5d91534c51050f2b322a698a20a1e546454d31441a3e28c8a9a628828785191534c51068f8ba12a698a203be576054d3144077ea6c0a9a62880aaad213624c5100072aa9ec
  | 5 => 0x800317cc47654d100063b188eca9a2000c75311d953440018be603b2a6880d28fa1b6454d100061f3b6c8a9a2000c3c76d915344001c3cc7b22a68800387a0f6454d100070ec1ec8a9a20d5c3f73d915344001c3ee7b22a6880028f60b6454d100070f196c8a9a2000e1c32d915344001c3e63b22a68800387cc36454d1007cae43ac6a9a2000c5c7658d5344001c3ec8b1aa688003871916354d102b5a6412c6a9a2000c5f8758d53440094bd0eb1aa6880129721d6354d100062e43ac6a9a200485c8758d5344001c3f08b1aa688003872116354d1000727c12c6a9a2033a5e8258d53440674b904b1aa688003932096354d1019d26412c6a9a2000e1f4258d53440234bf02b1aa68800395e056354d100a52fc02c6a9a2000e5b8058d53440014ed0d38aa6880031d1da7154d100059ac24e2a9a204eb55839c553440016cb0538aa6880029d2197154d100063a3b2e2a9a2052b57835c55344001878e9b2ec4880030f1d065d89100052ec18cbb1220008bf845d7624400717908baec4880163d20575d891000556c16e9b122000aad821d3624400117f08b9ec48800e2f21173d891063e1e3a6a7b122034c3c7454f62440058bce6a9ec488003175cd53d89102b726192a7b12200487e86dd562440010fd0fb2ac4880030f1d365589100062e39ecab12200087e871956244001878e832ac4880029760c65589100062e398cab1220038be86dd1624400187ecbba2c4880030f19774589100045f43ec8b122000c3f75d916244001878ebb22c488003271cf64589100045f438c8b122000c3f751916244001878ea322c488003271cc64589100062fb2ee6b122000c5c65dcd624400193ec9b9ac4880032719373589100243f43eeab12200087d83dd5624400187e85baac4880030f50b75589100045fc22eab1220038bc845d562440011bf06baac48800a3720d75589100043f438eab1220038be87dd1624400187eebba2c4880030f1d774589100043fc2ae8b12200487c855d162440011bf06ba2c48800a3720d74589100047bc0ae8b1220008be871d1624400187eea3a2c4880030f1d474589100146f43ee6b122000c5f75dcd62440018b8ebb9ac48800327dd373589100064e3a6e6b122000c5f85dcd62440018b90bb9ac48800327d0b73589100064ea16e6b122000c5f751cd62440018b8ea39ac48800327dd073589100064e3a0e6b12200087e87d4d62440090f90fa9ac4880030fdd3535891063e1e3a6a6b122000c5f73d4d62440058b8e7a9ac4880021fa1d53589100043e43aa6b122000c3f7454d6244069878e8a9ac48800317dcd53589100162e39aa6b122000ccc73dc962440071d90ea12c4880c7331cd42589100065a3a6e2b122032a3e85dd9424400147b0bbb284880022fa1a76509100061e32ceca122000cae629d94
  | 6 => 0x45ec3e63b222000a3e85cc7644400147b0b98ec8880022fa1f21d91100045ec3e43b222000a3e85c87644400147b0b90ec8880022fa1c50d91100745ec38a1b222000a9e83143644400153b06286c888002aba0850d911000556c10a1b222057ab681143644400156b02286c8880028fa1730d91100051ec2e61b2220008be870c3644401d17b0e186c8880028fa1430d91100051ec2861b222000aae820c3644400155b04186c88815eada0430d91102bc5f43e41b2220008bd87c83644400117d0e106c88803a2f61c20d91100051f42841b222000a3d85083644400153d06106c888002a760c20d91102bd5b40841b222000c3c75d936344001878ea326c688002ab60864d8d100052ec1eebb1a2000a5d831d763440010ff0aba6c6880121f21574d8d1002c7a40ae9b1a200087f855cb63440090f90ab96c6883230f1d742d8d100043f43ecab1a2000c3c74d9563440018d8e5b2ac6880021fa1c6558d100061e3a0cab1a2000c6c72195634400187ecbba2c6880030f1977458d100045f43ec8b1a2000c3f75d916344001878ebb22c6880032b1cb6458d100045f438c8b1a2000c3f751916344001878ea322c688002ab6086458d1000656390c8b1a2000c6f65dc963440018d8cbb92c6880032bd937258d1000656326e4b1a200487e87dd5634400117f08baac68800e2f2117558d1000477c12eab1a20018ec825d563440011ef02baac6880021fa1c7558d1001c5f43ee8b1a2000c3f75dd16344001878ebba2c6880030fd4f7458d100061ea9ee8b1a20008bd82dd163440010ff0aba2c6880121f2157458d1000477c12e8b1a20018ec825d1634400117d0e3a2c6880030fdd47458d100061e3a8e8b1a20048dc8754d6344067998e4a9ac6880063ba1f7258d1000637baee4b1a2000c6c75dc9634400195ee9b92c6880032b1d37258d1000657c26e4b1a2000cac84dc963440018dea7b92c6880031b54f7258d1000637ba8e4b1a2000c6c751c9634400195ee8392c6880032b1d07258d1000667b98e4b1a20008be87d0963440071790fa12c6880030fdd74258d106461e3ae84b1a2000caf72d096344003958e5a12c6880031d1d77158d101a51f426eca9a2000a3d84dd953440010fd0d3b2a6880030f1927654d100062f31ceca9a2000a5d839d953440010fb073b2a6880031760e7654d100061fa14eca9a2000c5e329d953440018b8653b2a68800317cc67654d100062f984eca9a2000a3f845d9534406947908bb2a68800297e0d7654d1000537c12eca9a2033a6c825d953440014ef02bb2a6880021fa187654d100061e320eca9a200487f831d953440018bd063b2a6880121f60c7654d100062ec18eca9a2000c3f421d953440018bc643b2a688003170c87654d100063ac08eca9a2000c76411d953440018ea823b2a68
  | 7 => 0x6e82d0f65440014db05a1eca880021fa1e43d95100043ec3c87b2a2058a768190f65440014eb0321eca880021fa1c43d95100043ec3887b2a2000a3e849cb654400147b09396ca8800297e0d72d95100052e41ae5b2a2000a3e841cb654400147b08396ca881629da0472d95100053ac08e5b2a2000c3d73d0b65441af47b09216ca880021fa1f32d95100043ec3e65b2a2000a3e848cb654400147b09196ca880021fa1c32d95100043ec3865b2a2000a3e840cb654400147b08196ca881629da0432d95100053ac0865b2a2000a7a800cb65440014f300196ca880da9ea0371d95100043f43e83b2a200087d87d0765440010fd0f98eca880021f61f31d95100051f42663b2a2000a3d84cc765440010fd0f90eca880021f61f21d95100051f42643b2a2000a3d84c8765440010fd0e206ca8803e1f61c40d95100052f41881b2a2000a5d8310365440014dd04206ca880029b60840d95102c53b40881b2a2000a758110365440b10fd0f986ca880021f61f30d95100043f43861b2a200f87d870c3654400147d08186ca880028f61030d95100053741061b2a2000a6d820c365440b14ed02186ca880028fa1320d95100051ec2641b2a200087e87083654401f0fb0e106ca880028fa1020d95100051ec2041b2a2000a5e8308365440014bb06106ca881629da0420d95100061f3b6cbb222000a3d83d97644400117b0f32ec8880028fa1665d91100045fc3acbb222000a9e83197644400153b0632ec8880028fa1865d91100061f3b0cbb222000b1d831976444001c3d0632ec8880028f60c65d91100070ec18cbb222000a1d831976444001c6b0232ec8880028fa1663d91100051ec2cc7b222000a3e8518f644400147b0a31ec8880028fa1b53d911063e1f3b6a7b222000c3f655cb6444001878cab96c8880028fa1662d91100051ec2cc5b22200e8bd8718b644400195ae4316c88803aada1b71d91100071a32ca3b222000c3d751d7644400153d063aec888002a760c75d91102bd5b408ebb222000ab5811d7644400147d0b39ec8880028f61673d911000557c12e7b222000aac825cf644400147d0a39ec8880028f61473d91102bd5b408e7b222000ab5811cf64441ad47b0b29ec88800387d4e53d911000657b94e5b222000c3f535cb64440af56d02396c888002ad60472d91100054f41ea5b222000a9d83d4b644400117d0f296c8880022f61e52d91102bd5b40ca5b222000ab58194b644400117d0e296c8880022f61c52d91100051f42e65b222000a3d85ccb644400117d0f196c8880022f61e32d91100045f43865b2220008bd870cb644400147d0a196c8880028f61432d91102bd5b40865b222000ab5810cb644400157500196c888002ae60032d91101ad5d406e3b2220008be87d47644400117b0fa8ec8880022fa1f31d91100
  | 8 => 0xca9a63880ef95219534c7101deabbb2a698e2008e577654d31c4143cacc8a9a63880ef95191534c7101df2bb12a698e20daf174254d31c40055a906b1263880039554d624c7100078aa9a8498e2000da77250931c4001d4ac4a126388006b92096348710006abb9aa690e2000e556354d21c4001d4f0ca1243880dfa921942487101bed3bb28490e2007ea77650921c412fd4ccaa1243880dfa919542487101bf53b1a8490e2000ea56350921c41b3e4ea6a124388003c954d42487100162fbb2a69862000d5553dc530c400395eeca1241880036950b71483100045fc22eab1c20038bc845d563840011df04baac7080063b2097558e100346e43aa6b1c20068dc8750d63840014bb073b2a7080028fe117654e101a51e422eca9c2000a5f835d953840014df04bb2a7080ce9b2097654e101a51f420eca9c2000a3d841d953840674dd043b2a7080029b6087654e100152fc32c6a9c2004a5e8758d53840094b90eb1aa7080ce97a096354e1019d2e412c6a9c2000e1f4258d5384001caac7b8aa7080031d9d87154e100072ab18e2a9c2002c5e7354f62840018bae6a9ec5080021fe157458a100243e42ae8b1420008df835d162840051b906ba2c50800317dcd5358a100162e39aa6b14205de4e3254d628400d1d90ea92c50801a3b21d4258a1000556c14eca142000a3f855d942840654790abb28508002a7e0d7650a1018d4e41aeca142000aaf825d9428406547d0a3b285080028f6147650a1018d4f418eca142000a9d831d9428400355d05b1a8508002ab60b6350a1000557c12c6a142001aac8258d42841b1d1e64b1a85080c78798d5350a100070eb1aa6a142033e2e6254d42840bbe1864a9a8508006abe196250a1001d5743ac4a142003aac87589428406355d06b1285080c6ab20d6250a1000717a9ac4a142000e2d535894284001d4ac5b8a85080032d9d87150a1000752b10e2a1420068dc8758d328400d1d90eb12650800b17dd9534c61006f2ab0aa698c2000d5953dc1318400395eeca124308033a95854248610006d4a16e090c2008c5f7654d308400f95eeca1241080039558d53c421000752b1285884200087d8799365440010ff0eb26ca880029ba0864d951000536c10c9b2a2000b2d821936544001c5d04326ca880028f60864d951000716c10c9b2a2000a2d821936544001c6b02326ca880030f19173d95100051f424c7b2a2000a3d8498f654401f0fb0e31eca88003175cc63d95100051f424c5b2a2000a3d8498b654400147d08316ca880028f61062d95100051f43685b2a20c8c3e76d0b654401f4ed0db8eca880038d19241d95100061eba0e9b2a2000a6e821d365440014db043a6ca881629da0474d95100053ac08e9b2a2000c5f739cf65440018bae639eca881629da0473d95100053ac08e7b2a2000a
  | 9 => 0x534c5200062e3b2a698a4033d4e7254d314800195eeca1262900032b1d9424c52000786a9a8498a40068ec865cd2148001a9ee6a9a4290002b92193148520007a2a9a6290a4000bc9831c121480e795ceca1460900036ae1d428c120006d443a851824073daa7650a30481c3d54eca146090003e2e0d428c1203d7c441a85182401dda97350a3048063d54c6a1460900c7aa18d428c1203d795a9a85182407af295350a30480017970690c60900cf179d9534c1200162e3b2a69824033d4c7254d304811de9040a9a60901ff2bdd9424c12000e563b2849824031e8c635093048001e1aa6a1260901ebe20c1424c120034e643a649824006acc864c9304800d79100992609000396e19534c1200072c432a69824002e5b7654d3048067ab0eca9a609000b961d9534c1200162c3b2a6982408ef4a8254d3048001e9304a9a60900cf569c9534c12019eac392a6982408ef487254d3048035cb6c4a9a609023bc6d09534c120477a5212a6982408ef194254d30481c1e9284a9a609023bd2c85534c120007a4a9ee49824000dab875093048001b510ea1260900076a9d9424c12000ed43b284982401dea8765093048003950eca1260901ebe2a0d424c120007c4c1a849824020dab735093048001f16e6a126090003e2d8d424c12018f5531a849824031ea86350930480f5f10c6a1260901ebcad4d424c1203d7c529a84982407af295350930481bff12a6a126090003c254d424c1203d7c598a84982401dbc8874c93048003b910e992609005ef2219324c12001764432649824002ecb764c93048003b94ec9926090007721d9324c120017643b26498240debcb854c930481bd7930a9926090376f2e11324c1206ede4c22649824000bcb814c93048001f128498a6090002f260d214c120007a4a9a429824000fc131485304800db9460b9c4090003535cd5388120004b7c2ae310240009af845c6204800db96e69844090003d254d308812002c6e43aa6b1e2034a3e84dd953c400147b09bb2a78800a9720f7654f101dd3b40eeca9e2000a5f835d953c40094bd0eb1aa7880129721d6354f1019d2f412c6a9e2033a5c8258d53c4001c3e84b1aa7880ef958856354f101de3a3b2e2a9e20dcb57835c553c40018bee6a9ac58800b171cd5358b1002c7643a84b162032a3e85dd942c400147b0bbb28588006ab20b7650b101bd5b40eeca162000aaf825d942c400155f04b1a8588006ab2096350b1018f0f31aa6a162000e1d6354d42c4067c5cc4a9a85881abc30c95350b1001d5743ac4a162003aac8758942c406355d06b1285880c6ab20d6250b1000717a9ac4a162000e2d5358942c406fd4c62b1285880df2d1d97150b106ddd3c12e2a16200487e85dd932c40010fb0bbb2658800e2fa13764cb100045ec26ec99620068f681dd932c4001caf
  | 10 => 0xa9a4034a3c845d953480014bf06bb2a6900029be097654d200053bc0aeca9a403ba74815d9534806947d083b2a6900028f6107654d2000727190eca9a4002a5e86d8d534806769905b1aa69001297a1f6354d200252e43ec6a9a4002a5e82d8d53480054b905b1aa69039787d0b6354d2072f0ea16c6a9a4000a5d81d8d53480674bb01b1aa6900029b2197254d20006363b2e4a9a40e4b4f835c9534800155d0db9a8490062ab61b735092018f4631ee6a124000aaf865cd42480015590cb9a84901eb631cd7350920005d5c02e6a124000ba8805cd42480e755d0db1a84901feeae01635092000717c32a6a124000e2c8654d4248069c5eeca9a84900d38b1d953509203f597c1aa6a12407bf0f8354d4248001e1ee6a9a84901ebc31cd535092000787b1aa6a124031e2e6354d4248063c58c6a9a84901ebc318d535092018f0631aa6a12407af0f3154d4248067c5ec0a9a84900cfcad8153509203d787982a6a12407bb2e85dc5424800165b0bb8a8490002aba1a715092000556c34e2a124027cac769c542480f765d0b38a8490002cb61671509203d5c741ce2a124000b8d839c542480017550138a8490002ea602715092000557c32e2a124000aac865c5424800175700b8a8490002ea201715092000557430e2a124018aad861c54248157958ec38a8490003695c4715092001d57c36e0a1240a9cac76dc142480037510db82849038f6a1db7050920006d5baee0a124000da975dc1424800175307b8284900036adcf7050920006d4b9ee0a124000f2b53dc14248001e52a7b8284900036adc77050920006d4b8ee0a124003aae869c142481497550138284900036adc2705092052d57430e0a12407bb2e851c1424800165b0a38284901eae3a0c7050920005c6c18e0a124000ba6811c1424800174b02382849029eeaa1c7050920006d5438e0a1240a5baa861c14248001d550c3828490003caa14705092000794c28e0a124000f8a831c14248001753063828490003e260c7050920005c4c18e0a124000f2b531c14248001e52a63828490003e8a047050920007d0c08e0a12400096d85dc5324800135b09b8a649000b171cd53d852001e573a285b0a40abcaf8750b614815f9590ea16c2900c72b9cd42d852018e5639a85b0a4000e2f5350b6148001c5aa6a16c290003a9e0542d85200075240a85b0a4000ea542d0761480015cb0420ec290003a950841d8520066d4b828530a40189ac875096148001a5eeaa12c2901ef4b1d54258520006c7b9a84b0a407ad8c735096148027b56e0a12c29038a6be1d42185200047bc3ac230a4000ab4845846148001d4a84b08c2900163da06768c5200043fc2aed18a400487c855da314800195ceca1462900032b5d9428c52018f4631a8518a40038be841d9314800117b083b26290003179d9
  | 11 => 0x4c11fa38e8a9ac29823b531c953585300a6adb82a6b0a6000d4d53dc9614c1d12bf0ea98c2980023de1d61185300053a42ac230a6000e5553584614c001b1ee4a126298002f2608704c53002c7b40ced10a60008bf845da214c00717908bb44298003179d953885300062ebb2a710a6033e4c6254e214c0090fd0a3b242980021f61476485300346e432e690a6000c5f7654d214c0018b8eca9a42980032b9d94248530006563b28490a6031d8e73509214c001e1aa6a124298003351d93148530007c2a126290a6006dca205ca304c001b1ae4a14609800257e15718c130004cfc22e3182600087f855c763880090f90ab8ec7100022fe1171d8e2001c5e422e3b1c40008bf845d5638800717908baac7100023de057558e2002c7a40aeab1c40068dc8754d638800d1b90ea1ac7100029760e7654e200051fc22eca9c4034a3c845d953880014bf06bb2a7100029de057654e201dd3a40aeca9c4034a3e841d9538800147b083b2a7100ee9da047654e200053ac08eca9c4002a5f8658d53880094bd0eb1aa7100129721d6354e2073f26392c6a9c40e7e1f4258d53881cfc3a84b1aa71000297e056354e2073f27902c6a9c4000e4d63dc953880090fd0fbaac3100021f60f75586200061fa16eab0c4000c3d42dd561880018de41baac3100022fe11755862001c5e422eab0c4000a5d831d5618800717d0fba2c3100030fdd774586200061e3aee8b0c4000caf20dd161880010ff0aba2c3100121f21574586200061fba8e8b0c4000c3c751d1618800155b043a2c3100021fa1f53586200243e43ea6b0c4000c3f74d4d618818f878e9a9ac3100021fa1d53586200043e43aa6b0c4000c3f7454d6188069878e8a9ac31000b179cd53586200263a3aca2b0c40068f4875456188007968e920ac31001a3d21d41586200043fc2aed18c400487c855da318805b56908b0c63100021fe15764c6200243e42aec98c40008bf845d9318800717908bb2631000317dd9534c6200062ebb2a698c4033d4c7254d3188077cacc2a9a631001a3d21d614c6201555a422c298c4000e555358531881058beeca9a611000396e19534c2200072c432a698440e6d5b7654d3088105cb6eca9a6110003d2e09534c220477a4412a69844033d5a7254d3088067ab0e4a9a611005f96589534c2204778da12a6984408ef194254d30880017970498a61100021fe1574d8d200243e42ae9b1a40008f7815d3634800b1e902ba6c69001237e1d53d8d200043fc2ae3b1a400487c855c7634800117f08b8ec69000e2f21171d8d200045fc22eab1a40038bc845d563480011df04baac6900023de057558d2002c7a40aeab1a400087f855d163480090f90aba2c69000237e0d7458d200047bc0ae8b1a40058f4815d16348001c9c65bb2a6900029760e7654d200051fc22ec
  | 12 => 0x3a950961486300052f436e4a9a601fa5d86dc9534c067c98c5b92a69800297e197254d300052e432e4a9a608ed4c725c9534c0016b700b92a698002d62017254d3047d8f426e2a9a6000b1d84dc5534c0014bd0d38aa6980029761a7154d301762e3b4e2a9a608fb1e849c5534c00163b0938aa69823ad3a0a7154d30005a6c14e2a9a6000b5a809c5534c0016b30138aa69800297e197154d300052e432e2a9a6000b5b805c5534c0016b100b8aa69800297a187154d300fd2ec30e2a9a60bdc5c761c5534c001aaae238aa69801297e1b7054d305de2e3b6e0a9a6002b5886dc1534c1d9ab0edb82a69800356dd37054d30006acba6e0a9a6000b5982dc1534c001ab6e5b82a698003565cb7054d300078da16e0a9a6000d5b71dc1534c001ab2e3b82a69801297a1a7054d305b5ad404e0a9a6000d5b709c1534c16f4bd0c382a69823ec7a107054d300058ec20e0a9a608eb4e821c1534c00169b04382a698002d5a047054d30005aac08e0a9a60b9b5a871c1534c001ab50e382a6982ded6a187054d300072d430e0a9a6000f1a841c1534c001e3308382a698003d2a087054d30005acc10e0a9a6000f49821c1534c00169304382a698003c6d087054d30007a9408e0a9a6000f51811c1534c0678bceca9ec49823b9398953d89300045fc22ebb1260038bc845d7624c0011ef02baec4980163d20575d893000566c1ea5b1260038ef8750b624c0010ff0ab8ec4980121f21571d89300045fc22e3b1260038bc845c7624c0e5ab6e0a9ac498003a3ccb765093000556c14eca126000a3f855d9424c0654790abb28498002a7e0d765093000557c12eca126000ab7815d9424c06f56902bb284980ca8fa1476509300051ec28eca126000e8f321d9424c0015390cb9a8498003271d9735093075dc7c12e6a126032e1f8654d424c065c390ca9a849800387dd953509300070e3b2a6a126000f0f8254d424c11de1904a9a84983ab47dc9535093047f87b92a6a126033e1e6254d424c067c38c4a9a849823bc3189535093019f06312a6a12608ef0f2154d424c001e3700a9a8498003c6201535093018f0fb02a6a126031f1b6054d424c11de1e40a9a8498006aba1b62509300edc641ec4a126000f0d53d89424c00755d0fb12849800eab21f625093000d5741ec4a126001aac83d89424c1d3c5ea7b1284983a78b54f625093000556c0ec4a12601daad80d89424c0012bb0bb8a649800267613714c9300262f3aaa7b0a60bdc5f8754f614c1838b90ea9ec2980cf179c953d853019e2e392a7b0a6000e578154f614c001ca902a9ec2980038754f42d85300070ea9a85b0a6001cac7250b614c0015ab07a8ec2980039554f51d85300056ac18a3b0a6000e5553147614c01bab2e0a9cc2980039554f61985300fcae43aa6b0a6000d1f7454d61
  | 13 => 0x7c231a8498a4231e8463509314852de4ea6a126290a5be194d424c5214b792a9a8498a42eff85535093148401e0aa6a126290a5be1cc1424c521006aaa9ee098a42019e482dc13148401b4a85b8262908063d60775d81210162e39aa7b024203cae7450b604854d95f0ea16c090aa72b21d42d812118e5739a85b024231cac7350b6048401c5ea6a16c0908038b54d42d812100752a1463b024202cd4734c76048401caaa698ec090803a950931d8121066d2b8a8530242249ac875096048401a5eeaa12c090a5f4b1d54258121006c7b9a84b024296d8c735096048421b4ee2a12c090bba6be1d42181214be973aa843024200d2d75508604852db1ce6a10c090803635cd42181210047dc3ac0302420087f835d4604840187e84ba8c0908030f509751812103637902ea3024206c6d205d4604840d8ee20ba8c09081b1d441751812103657902e83024206cad205d0604840d96e20ba0c09081b2d44174181210062f42ae63024200c5d855cc604840193e84b98c09080327509731812103667902e63024206cda205cc604840d99a40b98c0908033648173181210366b882e63024206cd5105cc60484090ff0fa98c0908021f61f531812163e1f3a6a63024200c3d74d4c60484058bce7a98c090803175cf53181213f63ab8ea6302420087f8754c60484010fb0ea98c0908d30f9d153181210061eba2a63024202c5e7354c60484018bae6a98c0908021fe157458a300243e42ae8b1460008f7815d1628c00b1e902ba2c51801a3b21d5258a300347643a84b146000aad829d9428c00147f0abb285180ca8f2157650a3000557c12eca146000ab7815d9428c06f56902bb285180ca8fa147650a300051ec28eca146037ab6811d9428c00156b023b28518006abe196250a3001d5743ac4a146003aac87589428c001d1ee6b1285183b7a31cd6250a3076f17a9ac4a1460ede2d53589428c00155f02b1285183b7a3cc16250a300243f43eeab0c6000c5f30dd5618c00117f08baac31800e2f21175586300052ec18eab0c60038be87dd1618c00187eebba2c3180030f1d774586300061fa9ee8b0c6000c3d53dd1618c00117b05ba2c31800327cc374586300043fc2ae8b0c600487c855d1618c00187eea3a2c3180030f1d4745863000556c10e8b0c60008be87d09618c0071790fa12c3180030fdd742586306461e3ae84b0c60008be87509618c0011790ea12c3180030fdd542586301961e3aa84b0c6001cae72509618c0098e8eb28ac31801a3d21d515863001e5a3a482b0c60068f487505618c00117f08bb4431800e2f21176886301453a42ac310c600087f855d9218c0090f90abb243180022fe11764863001c5e422ec90c6000caf76509218c00195aeca1243180c7631cd42486301bf5330a8490c60068f487585218c04b4e90ab0a4318
  | 14 => 0xc6358d424853574f02b1a84908038be19535092100716432a6a124234e2f7654d4248469c58eca9a84909facbe0d53509214bf87c1aa6a124200f0f7354d424852de18e6a9a8490803c3d8d535092118f1731aa6a124231e2c6354d424852de18c6a9a84908c78318d535092100793c0aa6a124200f248154d4248467c5ec2a9a84908cfc9d8553509214b78798aa6a124296f0f3054d424840755f0db8a84908df2b1db71509214bd9742ee2a124200b2d85dc5424846f74d0fb8a8490806e921b71509211bed33b6e2a1242f1da476dc5424852f74d0bb8a8490803c9a1771509214bd9342ee2a124200f2585dc5424852f7490bb8a8490802e960f715092100793a9ee2a124200f2553dc5424840174b01b8a8490ab2e9a1c71509211bed3438e2a1242aeba6861c5424846fd4d0c38a8490a5ee9a1471509211bdd2428e2a124200da7751c54248401b4aea38a8490802e960c715092100793a98e2a124200f25531c5424840174b0038a849080369dc770509211bd57434e0a124200aad869c14248437958ed38284908dee9a067050921005d2c0ce0a124200aaf865c1424846f5590cb828490802cbe1570509214bd9642ae0a124200b8f835c1424852d71906b828490802e9e0570509211bdd240ae0a124200da7715c1424840155d0c3828490892ab6187050921536563b0e0a124297b2e851c1424840165b0a3828490a5ae3a0c7050921005c6c18e0a124237ba6811c1424840174b02382849080369e1d428c5211bed243a8518a422dea78650a314846fd490ca146290a57699d9428c5211bf533b28518a4297da67550a314846fb48eaa1462908a7695cd428c52118f5331a8518a4231ea46350a314852de4ea6a146290a5bc954d428c52112cba42ae118a4200da5425c231484678bceca9a629080b171d9534c52119ea6392a698a429acaf765093148403958eca1262908c7a318d424c52100786a9a8498a4202ad686d8d314844baaf0ea9a62908975521d534c5210072bc32a698a4200e548654d3148405caeeca9a62908cf551d9534c5210172a3b2a698a4202c547654d3148543cacc8a9a6290a8795191534c521007a3c12a698a42a0f448254d3148467aace4a9a62908cf551c9534c521507a2392a698a4233d447254d3148477caec4a9a62908efd1d89534c5215078ba12a698a42a0f464254d3148541e2a84a9a6290bc3d1509534c521507a3902a698a42019e687dc93148401e8aa7b92629080369e1d424c521006d243a8498a422aea7865093148455d490ca126290807699d9424c52100ed23b28498a4229ea4765093148403948eca126290a5f699d5424c5214bed23aa8498a4200f8783509314852df0906a1262908df69dcd424c5211bfc3b9a8498a4200f87635093148463d4cc6a1262908c7a918d424c5214b
  | 15 => 0xea9ac09880347dd1535813150e8e3a2a6b0262a0d4c7254d604c423aaee2a9ac0988035354f72581317acafc3aa630262a1d1e7454c604c401a3ae8a98c098a83539c95318131006a6a9ae430262008fb87580604c40d8be60ba8c09881b174c175181310363b882ea3026206c75105d4604c40187ea6ba0c0988030f54d74181310045fc12e83026206c9f305d0604c40d93a60ba0c09881b2dc4174181310365a882e83026200cae845c8604c40195b08b90c0988031bd4d721813100636a9ae43026206ccf305c8604c40d9d460b90c09881b334c1721813100674982e43026206ce7105c8604c40d9ca20b90c09880e2fe1f42181310045ec3e8430262c8c3e75d08604c40187aeba10c0988072b9cb421813100656b968430262eacb571d08604c40117f0ea10c0988022f61d42181311961f3aa843026200c3d75508604c40395ce4a10c0988032b5c9421813102c7a40aeab1c420487e85dd163884010fb0bba2c7108163721d5358e2102d6a40aa6b1c42058de87d0d638846947d09bb2a7108028f6137654e210152e41eeca9c4200a5f835d953884774e902bb2a7108ef1d1c57654e210252f43ac6a9c4204a5c8758d53885e9c3e84b1aa710bd3875096354e211df2a38ac6a9c4200a5f8058d5388477cae20b1aa7108039558f7154e21146abc3aa698c423bd548754d3188401caf0ca9a63108ef95219534c6211deabbb2a698c429ce577654d3188543cacc8a9a63108ef95191534c62119eab392a698c4233d547254d3188447caac4a9a6310a83c5d09534c6215078aa12a698c4200d5553dc1318847d8ece3a9cc11080b179cd53982210062eb9aa7304423bc767154e608840117f08baac11080e2f211755822102c7a40aeab0442038be87dd160884af95e43ba2c11095f2b487745822100556c10e8b044200c3f74d4d608858f878e9a9ac1108030fdd153582211a61e3a2a6b044202c5e7354d6088455968e898ac1108039554d315822101c5f426ebb1a42008bd84dd7634840b1db05baec6908063d60775d8d210246fc3aa7b1a42038df8750f63484010ff0ab86c6908121f21570d8d211a51f426eca9a4200a3d84dd9534846947d093b2a6908028f6127654d210052ec1ceca9a4200a5f835d953484054bd0db1aa69081297a1f6354d210252e43ec6a9a42f3e4c72d8d53485e7c3e85b1aa690bcf8750b6354d2119d2ec0ec6a9a4200a5d80d8d53485e7c9e41b1aa6908ee9ba1b7254d2100727b1ee4a9a4233a7686dc55348401caec7b8aa6908031d5d87154d210072bb18e2a9a4200d67721c5534840155d0db9a8490892ab61b73509215a6563b6e6a124231e8e63dcd424840155f0cb9a84908deab219735092117e563b2e6a124231e8c635cd424840174f02b9a84908dee920573509214ad57436c6a1242f2e8
  | 16 => 0x29823100656b92853046237cb67150a608c4090fd0fbaac11896317cc775582312c62e98eeab046200a5d831d5608c4010ff0aba2c1188121f215745823102c7a40ae8b046200c3f75d09608c591878eba12c1188030fdd542582311961e3aa84b046201cae72509608c4014bd0db92a6988ae9761b7254d3162e2e3b6e4a9a6233e4e62dc9534c4014bf0cb92a6988ee972197254d311862e3b2e4a9a6233e4c625c9534c4016af02b92a6988eed52057254d310252fc36e2a9a623bc5c76dc5534c54363d09b8aa698802c76137154d311ddab43ee2a9a6202b5486dc5534c477aacedb8aa698bdf551db7154d3150dab426e2a9a6200f1684dc5534c54362d09b8aa698803c56137154d3150daa426e2a9a6200b5582dc5534c401e2e85b8aa698802d56037154d315f5ab438e2a9a623bd56871c5534c5816ad0c38aa6988ef95a187154d3150dab420e2a9a623bb54841c5534c4016ab0438aa698803c5d087154d31005aac00e2a9a6200d5771dc1534c4774bd0d382a6988029761a7054d311162e3b4e0a9a623bb56819c1534c4016ab03382a69880297e197054d311dd2e432e0a9a6200b1f845c1534c54363908b82a698802d3e097054d31505a6412e0a9a6200b57815c1534c4776a902b82a69880355dc57054d310052f430e0a9a622ba5d861c1534c5718b8ec382a698a86c7a107054d310058ec20e0a9a62a0b4e821c1534c40169b04382a6988eed5a047054d31005aac08e0a9a6233c5e7654f624c541c9cc4a9ec4988121fa1774d89310043ec2ee9b1262028f581dd3624c4091df0ea96c49880e3be1d42d89310045fc22e1b1262038bc845c3624c541c98c4a9ac498a7f55dc553589311951f42eeca126200a3d85dd9424c46547d0b3b284988028f616765093100556c14eca126200aaf825d9424c46f53d0db9a84988cb87e1953509311970e432a6a126200e1f7654d424c401c38eca9a8498803c3e09535093150786412a6a1262ead1f7254d424c543e1ee4a9a84988cf87989535093119f0e312a6a1262a0f0c6254d424c467c18c4a9a8498803c5e0553509310078a40aa6a126231e1f6154d424c463e2ec2a9a8498a83c3c85535093150787902a6a126201aae86d89424c401e1aa7b12849880eaba1f625093101d5643ec4a126200e8f73d89424c5edd18e7b128498bdb8bd4f62509317b716a9ec4a126229aad81d89424c40155b01b128498bdba3cc3625093118d5b436e2a126200f1553dc5424c401d4ec5b8a84988032d5d87150931006cbb98e2a126200f15531c5424c401d4ec438a849880a3d60774d81310262f3aaa7b0262b8c5f8754f604c5778b90ea9ec0988cf179c953d813119e2e392a7b026200e1d53d0b604c401c3aa6a16c0988072b1c942d813106eaab8aa73026200e5953d82604c4572b90
  | 17 => 0x2843293f87d4c605080127b0fa98c0a10c7479cf53181420068eb9ea6302847ed2e72d4c605098fa5ae5a98c0a10024fe1d53181420049ec3aa63028431d1e7354c6050801a3ae6a98c0a13f7c30c9531814218cd7c3e6430284009ad87cc860509f9a5ceb990c0a10034b5d7321814218ec739e643028400d8d73cc86050801a6ceb388c0a10034d5d67118142006cb39ce23028400d95739c46050801b4ae5388c0a10034dd4e71181420069aa9ce23028437da6829c4605086fb4b05388c0a10e72dd8a7118142006d3b14e23028400da7329c46050801b4865388c0a100369c827118142006d390ae23028400d36755c46050801a6aeab88c0a1003659cd7118142006cab9ae23028400da5725c46050801a6ea6b88c0a10034d54d7118142006d3412e23028400da5825c4605080196ec4b88c0a100369d897118142006d3992e23028400da4325c46050801b4e40b88c0a10022f61e61181420061ebacc23028400c9d73984605080196ae3308c0a10030f5d461181420064eb98c23028400cb571184605080187aebb00c0a1003275cf60181420065ab8ec030284fbba982980605080117f0eb00c0a10030f5d560181420064eb9ac03028418cad72580605080156902b00c0a10032d5c56018142004ddc3ac030284fabab82580605080717d09baec2990022f61375d85320043ec3cebb0a64f9a5d839d7614c8090ff0ebaec2991fa1fe0d75d853219c3ec1aebb0a6400c3f425d7614c80187a84baec29900317cc175d853200637902ebb0a640487e85dd3614c8010fb0bba6c2990022f61e74d85320061f3ace9b0a6400c3d759d3614c9f155b053a6c29900e2fe1d74d85320061f3aae9b0a6400c3d755d3614c80187ea6ba6c2990030f54d74d85327545fc12e9b0a64318bd825d3614c80193e60ba6c2990032bc8174d85320047bc3ac230a64008fb87580604c8fd0ff06ba8c0990ce1f60d75181320061fa12ea3026400c3d425d4604c80d8be60ba8c09901b174c1751813203637902ea3026406c6d205d4604c80187ea6ba0c0990030f54d74181327545fc12e830264318bd825d0604c80d93e60ba0c09901b274c1741813203657902e83026406cad205d0604c8018eea6b88c0990031d54d71181320065ba12e23026400cb5425c4604c80d9ae60b88c09901b354c1711813203673902e23026406ce5205c4604c80717d09baac5188022f6137558a3102c7a40ae8b146200acd83d49628c40b1d90ea12c518816b92054258a311951f42eeca146200a3d85dd9428c40355905bb28518802abe097650a311bd5a40aeca146237cb4715d9428c40755d0eb12851880eab21d6250a3179717a9ac4a1462f2e2d53589428c46fd48e2b128518802abe016250a311bf53882c4a146200ea562dc5428c47396ce3a14c1188072b9c94
  | 18 => 0x86335f0f994c0a10026b61f329814218ec739e653028400d8d73cca605080127f0ab8cc0a10ca4f215719814271ed4b96c1302843293e87dd5605080127b07baac0a10030fd8b755814200697b16eab028400d2c32dd56050801a5e43baac0a10034bc83755814200696906eab02840099f835d5605086333906baac0a10026be097558142004dbc0aeab0284379b4815d5605080127d0e3aac0a10cb0f1d765581421945e43acab02843199e87dcd6050801a3eebb9ac0a1003471d773581420068fc2ee6b028400d1c85dcd6050801b1d05b9ac0a10036360b73581420064fb16e6b028400d8f62dcd6050801b1e43b9ac0a100363c837358142006c6906e6b028400d1f751cd6050801a38ea39ac0a10c7271cf635814218e4e39ac6b02840093e87d4d60508652790fa9ac0a100347dcf535814218e8e39ea6b028501d2f72d4d605080127d0ea9ac0a10024f21d53581420068fb9aa6b028431d1c7354d6050801c3ec6a9ac0a120f4bdc9535814280786192a6b028400d2f75dc96050801a58ebb92c0a100363dcf7258142006c639ee4b0284009ae87cc960508633590f992c0a1062aba1b325814200697bae64b0284fcd2c75cc96050801b1ee7992c0a10c7631cf32581420069bbaee2b028400d3475dc56050801b2ee7b8ac0a1003651cf7158142006d3b96e2b028400d3753dc56050801a6aa7b8ac0a100369e0b7158142006d2416e2b028400cb762dc56050801b4ec5b8ac0a100369ccb7158142006d2196e2b028400da720dc56050801b4a41b8ac0a10034ddd471581420069a3a8e2b028400d97731c56050801b28e638ac0a100369dc871581420065bb28e2b028400cb5651c5605080196ec638ac0a10032d58c71581420069ba98e2b028400d35531c5605086fb4d0438ac0a10df6960871581421ce5bb10e2b028400da7621c56050801b4e6438ac0a1003690c87158142006d3900e2b028400da5201c5605080117d0fb0ac0a10028f61761581421be5a38ec2b028437cb47158560509ffb56e5b02c0a10032d1c6605814218ccf41eea302840099d83dd4605080335d05ba8c0a100e6b60b75181421bcdb40eea30284009b581dd4605080127b0f3a8c0a13fb4b9ca751814200696b94ea302843293f875d46050801a5ae4ba8c0a10024fe0d75181420061fb12ea3028400d2f625d46050801a5864ba8c0a10034bc85751814200697902ea3028400d1e759cc6050801a3aeb398c0a1387639ca7318142006c6b94e630284b19af825cc6050801b1864b98c0a10c667e1d73181420068f3aae63028400d1d755cc6050801b1ae4b98c0a100347a1573181420068ec2ae63028400d8f825cc6050801b1904b98c0a100327d897318142006c7b12e63028400d8f215cc6050801b1e40b98c0a1003668817318142006cc902e63
  | 19 => 0x24f61d53d854218e8e39aa7b0a8510f0c3254f615095f35d0f996c2a100e6b21f32d85427e6973ae65b0a8400d2d75ccb615080174b03996c2a10cb4d9d651d8542005d2c14a3b0a84329b787547615083135b05386c2a106e6be0970d85420049fc1aeb30a8439c3f625d66150801a5ec4bacc2a10034b0c975985421be9a30aeb30a8437d2f215d6615086fa5a42bacc2a10034bc8175985421be9b882eb30a8432c3e75d96615086517f0eb2cc2a100347a1573985420068ec2ae730a8400d8f825ce6150801b1904b9cc2a10e727d897398542006c7b12e730a8437d94615ce615086fb1e42b9cc2a10df634857398542006c7902e730a8437d97105ce615086393ce7b1cc2a10c7279cd63985421949fc3ea730a840093d87d4e6150863a3ce7a9cc2a1003475cf539854287e96b96a730a840093f8754e615080127b0ea9cc2a10c7479cd53985420068eb9aa730a8400e1f6354e6150933a5ae4a9cc2a143bc30c9539854218cd7c3e6530a84009ad87cca615084f55d0d994c2a13f34b9d7329854200696bae6530a8431d8e73cca6150801b1ae7994c2a10034d5d76198542006cab9ec330a84f1da572d86615080135f04baac2a14374bdcb53585420068fb9aa6b0a8431d1c7354d615093ba5ee4a9ac2a1433c30c95358542004d743e64b0a84319ac87cc96150801b1ee7992c2a10c7631cf32585421bd5b436c2b0a850bda772d85615086527d0a382c2a10024f614705854218ccf418e0b0a840099d831c1615086517b0fb28c2a10cb0f9d7651854285656b96ca30a8400ab581d946150a1395ae4b28c2a10038d945651854258cd7c12e630a84318bd87d8c615080156b03b18c2a11fb4b9cb531854263e96b96a630a8431d1e7354c6150801a3ae6a98c2a100387d8d531854284786192a630a84319af87cc8615080135b0f990c2a12aeaba1b3218542005d2c0e6430a84009b7875846150a0f74f04b08c2a10deade1d61185420065bc3ac230a8400ab785584615080156f06b08c2a10038dd4d61185420071aa9ac230a8439ab7825846150801d4f04b08c2a10dfa99c961185421bf52b92c230a8400ea7325846150a0dd4864b08c2a1002ad201611854283753902c230a8400ab5865446150801c6ecaa88c2a10626b60a70185420049fc2ae030a843293c855c0615080196ac2b80c2a14166be0975d81421945ec3ecbb028432c3e75d97605096335f04b9ec0a10c62f61f63d814218e4e39ac7b0284c7d2f72d4f6050863a38e6a9ec0a100387d8d53d814282786192a7b0284a99ae87ccb60508073590f996c0a12a6aba1b32d814218ec639e65b0284279af825c7605086f17b0fb0ec0a10028f61761d8142004d6c16eb3028503d2d72d4e6050863a3ce6a9cc0a1003475cd53981423ee96b92a73028502f0c3254e605
  | 20 => 0xdb40eebb1a84009b581dd7635086533f0ea9ec6a1002e3e0953d8d4219ec7392a7b1a84019ae825c7635080335d05386c6a10626b60a70d8d420049fc2ae1b1a843293c855c3635080335d04b86c6a100363cc970d8d42004d7c12eab1a8431a9e86d8d6350a3db1ee7b92c6a1477a318f7258d421949f42ee2b1a840093d85dc5635086527d0a382c6a10024f6147058d421bcdb408e0b1a84009b5811c1635080165b05bb2a6a1003c30cb7654d420059b40eeca9a8400b3581dd9535080187eed3b2a6a1002c760e7654d4200786194eca9a8400b36819d9535080166b033b2a6a1002c7e0d7654d4200597c12eca9a8400f0c325d9535080187aec3b2a6a1003c30c87654d421958f43ec6a9a8432b1c87d8d535086363d0db1aa6a10c787a1b6354d420070fbb6c6a9a8400e1c76d8d535086763d05b1aa6a10c7c3a0b6354d4218f86c16c6a9a8433b1c82d8d5350a37e18e5b1aa6a146f87d8b6354d428e787b16c6a9a8400b1d81d8d5350a37e1e43b1aa6a1002c76036354d428df87906c6a9a8433b2e87dc95350867a5d0fb92a6a10d2cba1b7254d421a596436e4a9a8400d2e76dc95350801a58edb92a6a10cecba0f7254d4219f8741ee4a9a8433b0e83dc95350867e1b07b92a6a10cecb20f7254d428d697b9ee4a9a84fcf0f73dc95350801e1ec7b92a6a146bc318f7254d4200596c0ee4a9a851af0f31dc9535080165b01b92a6a146bc3cc37254d420051f436e2a9a8400a3d86dc5535086765905b8aa6a1467c30cb7154d420051f434e2a9a8400a3d869c5535093d63b0738aa6a10cecba0a7154d4200596c14e2a9a8400d2f729c55350a31e186538aa6a128ec7e0d7154d4200597c12e2a9a8433b2c825c55350a2fe1864b8aa6a10cecba087154d4200596c10e2a9a8400d2f721c55350a2de186438aa6a10034d5c47154d4219d96416e0a9a8400d2f72dc15350a2be1865b82a6a1236c760e7054d4219d97414e0a9a8400b2d829c15350a29e1865382a6a10028fe197054d420051e432e0a9a8491b1f835c1535080165f04b82a6a10cecb2097054d4200697b92e0a9a8513f0c325c1535080166f02b82a6a1002cd2057054d420051f430e0a9a8400a3d861c1535086765d04382a6a1002cb6087054d4289786190e0a9a8400b36811c1535080166b02382a6a10024f61e75d85420058ec1cebb0a8400d2f729d76150a23a58e53aec2a14166be0975d854200cd6412ebb0a843293f875d76150801a5ee4baec2a10024fe0d75d854200697c12ebb0a8400d2c825d7615080187ec4baec2a10034bd8975d854200696192ebb0a8400c3e615d76150801878c2baec2a10034bc8575d854200697902ebb0a84b19af825cf6150801b1864b9ec2a10ca4fe1f53d85420049ec3ea7b0a84c7d2f72d4f615080127f0ea9ec2a10
  | 21 => 0x748c96054e39a38e9192c0a980353dca325815319ea639464b02a600d3774dc56054c01a68e9b8ac0a980355dcf7158153006b3b96e2b02a600d6472dc56054c01aaf07b8ac0a98035520f71581530063bb1ee2b02a600d5763dc56054c01a6e85b8ac0a9803558cb7158153006aa196e2b02a600d5730dc56054c01aaa61b8ac0a98034ddd071581530069a3a0e2b02a600d57731c56054c01acee438ac0a9803591c871581530063bb20e2b02a600c75641c56054c77aad0638ac0a98ef5560c71581531f63bb18e2b02a600d57631c56054c018eec438ac0a98031d58871581530069ba10e2b02a600d56321c56054c01aa86438ac0a980355cc07158153006aa980e2b02a60087e87d856054c0147b09b0ac0a98ef1d1c761581531de3a38ac2b02a722d5b73d816054c018e8e3302c0a980a57a0f7418153024aec1ee8302a63396e82dd06054c012db05ba0c0a98ee5da077418153004bac0ee8302a60093d879d06054e43a3ce73a0c0a9803475ce74181531a49fc3ae8302a600d1d735d06054c0187ec6ba0c0a980347d8d74181530049fc12e8302a600d1c325d06054c01a3e62ba0c0a980347cc17418153006973a4e4302a600d2d749c86054dcda9ce7390c0a9803535ce721815361cafc1ae4302a600d4c325c86054c672df0eb90c0a98034b9d1721815300696ba2e4302a600d4d735c86054c01a5d08b90c0a98034b6117218153006a7c1ae4302a600d4c835c86054c018dec6b90c0a980353d8d7218153006a798ae4302a600d4f305c86054c01ad460b90c0a98035a4c172181531a49fc3e84302a60093d87d086054dd5a3ce7a10c0a9b23475cf421815319e9739684302a600d2d72d086054c672bf0f190c0a98025761e32181538e68f3a464302a600d1d748c86054c67a9ce5190c0a9803535ca32181530069b3a4e2302a600d35749c46054c01aaae7388c0a9803599ca7118153006b2b94e2302a63bd56839c46054c77aab07388c0a98fb1dd8e7118153006abb1ce2302a600d37429c46054c01aac65388c0a9803550ca7118153006ab984e2302a600d57315c46054c01a6ce8b88c0a98034d5d17118153006aab9ae2302a600d66725c46054c01acae4b88c0a980355a0d7118153006aac1ae2302a600c77635c46054c01aaec6b88c0a98034dd097118153006ab192e2302a600d54325c46054c01aae60b88c0a98021f61e61181530061eba4c2302a600c6d729846054c018eae3308c0a98030f5d0611815300636b90c2302a600c75711846054c0187ae9b00c0a98031b5cb60181530063ab8ec0302a720b59839806054c010ff0eb00c0a98030f5d160181530fe2eb9ac0302a600c6d725806054c014e902b00c0a98031d5c56018153004bdc3ac0302a71fb5b835806054c0335d05baec6a100e6b60b75d8d421bc
  | 22 => 0xb94c2a980353d8d72985531deb230ae530aa63bd4f315ca6154c77a9a62b94c2a980353cc172985531deb3882e530aa633c6e72d8a6154c678dce4b14c2a98d24fe1f42985530049ec3e8530aa72cd1d73d0a6154c67a5ce5a14c2a98034b5cb429855319cafc3c6530aa60095d878ca6154c5d4bd0d194c2a9c73479d232985530068eba46530aa633d4e728ca6154c01a9ae5194c2a98034d5d361985537beaab9ec330aa600d6572d866154c012bf06ba2c2a9caf47dcf4258553004af43c64b0aa63395c878c96154c01a9ee5192c2a98cf531ca32585531dd3b436c2b0aa72ad5773d856154c6927d08382c2a98024f610705855319cb7410e0b0aa60096d821c16154c690fb0fb20c2a98d30f9d3641855394e2eb9ec830aa600a7581d906154e518bae6b20c2a98038d905641855361cafc1ae430aa63387d87d886154c014eb03b10c2a9bab479cf42185536468eb9e8430aa63395f878c86154c012bb0f190c2a9af697a1a3218553005aac0c6430aa600977875846154e4f6af06b08c2a98ee9de1d61185530063bc3ac230aa600a77845846154c7d4ef06b08c2a980395e0d61185531df2b39ac230aa63be55735846154c014ef04b08c2a98038dd0961185530072b192c230aa726e54325846154c014e900b08c2a9c9b95cc161185530053ac328230aa600e37645046154c3f2bb07380c2a98024fe1170185531a49e422e030aa600c75615c06154e4b2bf06ba6c0a98d21f61f64d81531a61f3a6c9b02a6c395f835cb6054c670fb0fb16c0a98cf1b1c962d81536468fb9e85b02a6bb95e878cb6054c092b90f196c0a9aee97a1a32d815319ea639465b02a62e95f835c76054c770fb0fb0ec0a98028f61361d8153004aec1ee9302a724d1d73d0a6054c672bf0f194c0a98025761e329815319ea739465302a600d4d728ca6054c0127f08b8cc0a98d24f2117198153766acb9ec1302a63493e87dd16054c0187ec7ba2c0a980347d8f74581530049ec16e8b02a600d1c32dd16054c01a3e63ba2c0a980347cc374581530068e986e8b02a60095f835d16054c012df04ba2c0a98ce5b2097458153004bbc0ae8b02a63b974815d16054c0127d0e3a2c0a98d30f1d364581531a43e43ac8b02a600d1f74dcd6054c01a38e9b9ac0a98ce5ba1f725815300697ba6e4b02a600d2c74dc96054c01a9ee7b92c0a98034be13725815300696426e4b02a600d4e83dc96054c01a9b07b92c0a98031bd8f7258153006a7b1ee4b02a600d4f31dc96054c01a9e61b92c0a9803534c3725815300697ba0e4b02a600d2c741c96054c01a9ee6392c0a98cf1b1cb625815319e36392c4b02a60093e87d096054c692790fa12c0a9c8f47dcf425815300697b9684b02a633d2c72d096054c012bd0f192c0a98ce5721e32581530fd2f43464b02a600d1f
  | 23 => 0x300000000000000000000000040030004006001800000000010004001000000300040000008000000000100000030000000000c001000400200000020018000000c000000000000040000000000000800300000020000001000400200080010000000000c00400080100004000000000000000010000003000c0020000000000800600040000000003000c00300000040000000001000000040010000001000400000000060034004000400300080000018000000400100040000000000000400000000020000001000000000040000000000000000100000010008003000800000000000000000001000200080000004000000000000000000000000000000100180010000000000000200000000004000000000000000040008003000000100000000008000000000000000000000000000800200080000000002000400000040010000001000000000000020008001000c000000000000040010004002000000000040000000004000000000000000000000000000100000000004000000000000000020004000000000000000030000000000000000140020004002000000100000000004000000000100080020000000000000500240020004000000000000000000000000000800000000030000000000000000000000004000000c00500140070000000001c052bd07ba6c4a98125760f74d89531dcbb40ee9b12a60097581dd36254c692df0ea16c4a9802d3e0d42d895319ea739a85b12a60295e835c76254c052bd07386c4a987e5760e70d89530049fc22e1b12a63493c845c36254c052bd06b86c4a9803538c970d8953004afc1ae8b12a72fe4c62dcd6254c674dd0db12c4a9cbb53dcf62589531a49f426e2b12a60093d84dc56254c6927d08382c4a98024f61070589531dcbb408e0b12a600975811c16254c0127b0f3a6c2a980347dce74d855396e8e39ce9b0aa600b2d829d36154e4b2bf06ba6c2a980a5720d74d85531a49fc3ae9b0aa600d1f735d36154c01a3f06ba6c2a98034720d74d85530061fb1ae9b0aa600d1f635d36154c0127f04ba6c2a9803470c974d85530061f30ae9b0aa600c3c615d36154c01a3e62ba6c2a980347cc174d855361cafc1ae5b0aa600d4c325cb6154c6927f0fa16c2a98024f61f42d85536468fb9e85b0aa6c195e878cb6154c092b90f196c2a9c73479d232d85530068eba465b0aa600b55818cb6154c69a6ce920ec2a9802d560e41d85531a4bbc3a83b0aa61f95d839c36154c452bf06b86c2a98fb0fd8d74985530068fb1ae930aa60093f825d26154c01a3864ba4c2a98ef4d18574985531de8f98ae930aa63bd1d315d26154c01a3e60ba4c2a98ef4dc4174985531a61f3a6c930aa63487f875926154c01a5d08b94c2a98034b6117298553006a7c1ae530aa600d4c835ca6154c7d8dec6
  | 24 => 0x10004001000000000080000008001000000000000000004000000400200040000000000000400000000000000000000000000040010004001000400000000010000000000000200200010004001000400000000080004003000400000000010008001000000100000010008004000000000000000000000000800400080000000003000000000000000008000000400000000020000001000400400040020000001001c00200200000004001000000000000000008000000c001000000000000000000000000000000080010004001000000500000010008000000800000000040008000000400100000010000000000000000040010004001000000300000000000000000000200080010000002000000500040000014002000000000080000000000000400100000000008001000000000100000004000000400100000000000000000400000000010000003000c000001000100080020000001000c0000000002000000100000070004000000000200000000000003000000100000020000009000400000040010008006000000400000000004000000c000000000000000000000000000000100000000000001000800200000000000004000400200200010000002000000000000000008000000000000000000000000000c00000000030004001000c00300000050000001000000000080010000007000000300000000000000000000000000010000000000400000000000000000000000000000000000000000000100040000004009000000000080000010000000400200000000000003000400000000010000001000000000000000014000000000000040040000004000000000100020008000000000200000000000000000000200000020014000000000000000010000000000800300000000000000000400000000000004002000c0010010000000400000000020000003000c000000c002000400000000000000006000000000040010000000000400000000040004001000000100000030004006001000800000000004000000000000000010000002001000000040040008001000800000000000000000000000000000000000000000000200040000000000000400100040050000000000800200140000008001000c003000800200000000004000000000300080020000001000000000000000000000000800000000000004001001c0000000006000400000000010000001000400000000000000000000000300100030000000000400000040010008000000400100000040014000001000000080000000001000000000080020008000000c000000c00400000000004000000400200080030000002000000000000020008002000000400000000010000000400000000000000000000400000000010000002000400000040
  | 25 => 0x4900000000000000000aac0000005291fec00000000000000000000000000000000000044cc7a000000000000000000000000000005dd16280000000000c2c09a0001c62ce40005f600000000000005e590ac3e86ee00001317548b300000005c66060a90cc40000000000000000c2e00000000000003bd889949aa0c0000000000000000000096e0000000000000000094800068a1c7531118101c1ae0000000000154000000000000008c80018269b3000000062a27e000176800000000000018f254d30d05100000000002055934000000183c000000000000005601830e80000000003f424cc0000000000000632a5a00028b80000002f08040000ace044800000080b00000000002320000250000c4f173a91c00000000000000000000001fb400000000000000000000000000000000599000000016f00031c0ef215d00000002f200038f1ac4000000000000017400000011f53540001089cad66865e247210869e07c000000186885d000000000000000000000000005fe0000000a8e000000000000008600004b6736000300c000c940000000000b4a00000000000000002788990000283800105e00003300014be78a48c800189a9e6371253c00000061f95ac0007150001c3c000000000242c47273a3d687240001e600000000000000000000b1c00000000001c42ba1e600000000000000000000000404a56400027a000000000000000000000000003f00000b02000000000000000000000010a800000000006200005cd0000000a78000000046e2dd0000000000000000000000000061695d4cca00000000000000000000000000cab000000000000000000000005e700000140000000970684c1600000017a80000672cf8001000800000000000000000002c003000000100080070000000000400200080000000000000000000040010000000000000600000000004002001000000000010000000000800100080000000000000000100000000000004000800000040010000004000000000080030004002000000600000000004001000000100000020000003000000100000000008000000000300000000000005000000000000020020002000000100000000000001000000000080110000001000c0000000000000400000000010008001000c0070010000000000000000000000002002400000000050000001000400000000000000000001c001000000100000000000001000000400000000000001000000200000000008001000000000080010000001000000100040000004002000800000000020000005000000000000000000000000000000000000008000000000200000060004000000000000000000008001000000100000000008009000000000000000018000000c001000000100000000008002000800000180070
  | 26 => 0x22c8d704703cc0000000000000000b251668000000000000000000070a0000000a2283e0c1800058e9c63bb25bc000c6d00000000e400000000000003cd0000000c027c40000fc837a39c09b00000000000000000000000000000000042800000006787c8000000000004e00000000000002f1000000000057e8000f24000000000114200000f9f7000064100000000000004cd0d9000000000025500000004610c480000092a88000ac000051aa7c16908920001d7c00000022600000000000002fc800000000025f400000000000003d200000000001540000000000e6a0003d4800000000039295280005a4000000012259a000000155c000000000000000046f0000ff8000016000013e00009f25292a00000fd800000079402f062c0006f10001634000000000000122e0000000000e100000001998c44000000000000000000023240000000000000382000000325cab0922427800000093d62f947835a3ed25c00013320004e78000f7258900000000000000002b647ca44308e0fc40000000002edc000000000000000089f00009e400049700900000003240000000e0c00008800000000000002f980003bc1bf000000000000000005a8000000223800000000000014a2000000000000000000000000000006068000476000000000000000000000008bc60250302140000004b687840000000000b64ad21f900027800000006470ee081400000000018b09e4480a3ecf0c4870000000000000000000000000000000000000000001a8800000000000005d00003c198541a00000002a2c00000000025800000000000000000000063000054e0003b68000000b8b00007512eab92287000000000000014698d60000000000000000000000000000000000000003d000000000000005c780013627df00006c400000000000000000000000be0be80004489d6c0f4b6f03c0e4400078005200014b617f000000000000000027f8000000388800000000000000002300002df800000000000000015be00000029140000d60adb20caee8595a0800000094500000000000002460000000000324800070e49109b80014bc000471000000000000023d80000000000000000a7a0002f240000000000e84000000508aed80001e700018c90a600050e000000000000000000001f0000000090000043800000000000002eb800000010b80000007fe000000155a00010f80008f00000000000000aa500000015e400000000017888b24a400000000000000000000000000000000092e000000000000000000003bc000000200556200048a000000000014f0ba800040e0000c0c00000000022200000001d8000000000000000013ba00064980000000002ad8000000000000000000000000000006ac00000000003fa0000000f580003df000329c0002
  | 27 => 0x114a000000000068e00011aa54800001400008cc00000000500003c4b08000180c0000000002d348f60002b9124c00000002098d80d000035980000008d0000000000000000000016e800000000012746bf36a000011e07d000000159400027d0c04e900005be000188000027a80000000005b98ea8000000000000074e0000be906c000ca332c000136400000000000006ab58faa300005555cc8000000000000000055a47227e0af02c60004f78000ec01b5000000000044a000255d8363880002a2000000000000010c00000000000c96000000134400000004600000000003b58000000a9000000000003e90000000000000000000000000050a80000000001d90000000000000000000052100007f96ac0000000000000000000000000016122aa4100000000000000cf40000000000000000000000175e00041083f420a0004b113e0db400000008c000065900000018427bf000000017a0ab26a000000000037794fc0007ef1d580000000004d480000000000a2a9e4f2005c2532bac0000000000000000000000099800000000000018d200000000004e25b6000000108c000000000000055700000000009a60c29e5c00000001a13811de4f400000000000005e0804c00000009500000000002eb9ef16780000433248000000000000086e00000000000005fa2950000a58000149000000000000000006a85740000be89d600000016bc0005d10000000746000000000013c000000000000000000031c5336000000000000000000000000000000002f480002541049bf521020106005d41109c72ec00018b641700026d80000000000570b36a283388000000c1f4182b845fe000487abb800000000000000006a64930d9c0000000000000bee0003438000ee856100027e80000003a7ab2d830ab3000244d48400000029a12767880000d004f60002e930dc0000000002fdc0009db00000000000000002c70000000000000000000000032c45be660000000083e00000004ec00000000000000000004418000ea45b40002d7cc4a0000d59c050ac0b9228960948c3a800000000004c00001ec80000001209f980006f90000000f5c0000000d4430c171000000000000000000000000000000000000000294b03d0b80000000e551ca56c00014155b000027b2be157870e60eaee511e00000000000007030a791c0000bff00000000009a7462986c71a40d4b316599080005d2a3440000005800000000000000000107000057f0000e7a00032414480a4000000000000000028180000007b60002941834000278a49ca181cc0000000996000000000000037100000000000000f400014e8000164800000000015e80000000000000000000000058136c000000000103c0007e200000007520000001454000000000289c0004500000
  | 28 => 0x1397048540000000000ede00000000012b026f00000000000001c30000000000585800000002e000000190e000000000000000000000018e600026197a043c0003de80000006840000000e18000574000000000000000016ae43a44312802600793eda1a06fe0000bd800000021a2c8000000000034f8001000a9206f00000007ac0000000034000000000172a00000003b400000000000008ea00000020b400000b538000000000000000000000000000000000000000000000000000028c40000000000000000ab0253800049a00035f000000000009000011b400000000000000000000000000aa210b000000000000024417b000000000000000000000000000431000000000000000000012ec0000002040000000148000000000000000000000003eb8ff922400063d8000fd60000000000000903001afe5188bbf02b000000000011ea0e800093226f860400086c0002fec3d800016700000000b500000000000000002d78000000000000000091522a00000000000000000000a89000000125a0000001194fb400000032e40000000000000352b7a5100000000000000000000000019a80000000001c9a2d400063c10c9508a9e19f0001c5c0000000000000000000000000000000000000000000000002f8400000000000000000000000000b5a000000000063e0000002fc16b400000029980000000000000ca21eb0002838000000000000047c0002ce8001218000000000116e6af000000174e18204102100000000000000000000000000193ac7e2b8800193084d00014a11ac6564f6185c7d03ae21c0001970000110800173e0000000000000a300c40b100000000000c100000000000000c50000000311800000047f800069c43b0d602953bc000510800000000000029003a46201b52db140200000012f170668a000024d92a000000309c000a950002b9c70220e0000001686000000000000000000000009ce0005b500000000000000000000000000000000000000000000000000b3a674480aa9000000000000000000000000002f786680005fe00000001644220000690000000547865422a7aa00000000000000388000d0082c0001a940001f200032c800000000000011f40000ee800000000034110b42d800000000000000000000000000000000000000080f000127000000000000000000000002bc00000000000000000295505062519404b0de00000000000000000000000000216000000000000000000000001284e1200028680016567d147ba5c800000000007380c48110001eec00000000000000008ad0000000000000403800000000000000000006b95b390140000000002afc000000000225800000000000000000000000000000a0b263251c000bb1611a47800020a00019d8032b4c0760418e24
  | 29 => 0x4bf44e8000000000273000000c1690000ba421000000000000000000000000000000000000000000000013f816cc542518000000000000000000027c38d32dc0000001cb00000000000000000000a070b280000000001d9800000028000024188d200000000553860001e3800000000007c800000000000000000000000df0000000bd70002138af496a0d98f1452c2a54c60000000a9a00000000000000000000000204000000060c0000001c3460a35f2fc000005005956084bc24400000000000000005160001200610011288c86a62b00000003962516100000000b6e0000000000000000130800064a54380000007fa00000004d00fc0000d494dc73c2d8800000000013f80013448a62f59c7ce0e863000170000000000013c00000000a0041c0000000000000000000046a1c507a1740001ae80007e90408f5c00000000000000000000000001912a172d7000162400034c98b17140003f600000000000dc00000000004c019acdc60000000000000000254053963c00000000000000000001b000008315aa80002ae0000001364b7200000000000000e156612ac000000000000000069a0000000000000211ac540000000000000958b7e0000c08290000000000000000000012500000000001dcc0000000000000000294000000166600000000000000001ba120c40e31356d800000000000000000008e9000091c0000000001e340000001bc800000014b00002bcfc20005710000000000000000000000000000000000000000000000000000032400048a00000006bc9d42710000762b7f0000000000000000000000000000000000007a012f000000045925896e8e4c76311d1a700001ea00000000000000c60000000222000241400000000000000000001cd800000034c0001bcc00000000000000000000000000000000000000000049d04800011e03600000000cd20001b42140000808529a5e01685b700000000009af230800177a474000000000000033a8000446000000323c000000000190800000000000000000000000000000cbb1fd80000000000000000000c6a560000000000042280017be000000000000000021492c80c2b4e654000000000000007f173822a5fd0d7431ec741602460dac06f24d015c0007370000001752b05000000000010200000009760002ca13716a400000026f41e00002e400000004580000468bf600025e968400000015a8a252e04e100000004a400000000000000000000000248000000000058a42c00000013ec50a34430c40000004ae000000072233200000000000000000afc00000000000000003d78e48000b3100000000000000001d4c00000000029fc5468a200000000000000000000d86812000013c000000000034400065d000113c0000000000000c700000000fc0b7c000592
  | 30 => 0xb119c5b842e634000000000000000000000005e000a80000000002d003dc000000000132e0003df000000000000009a4000048000000000000000003740004131b92fa400000051d9148000000000000083c6ec00019e000000000000011a80000000000000c5500022d0b4a37b000017400000000000004000000e20634000000000000174031e39f00000000000000000000bd6000000000000040d800000062a00010bc00007000000011fa00000028116f0a690868000000548000076000067e44500000004ba0000000f22c9b348800028c0000000000d5c00001b000000000000000000001b22e68f100004850000ad8b9ec99000000137800000000000000005b4000000000000000000007a1000000000000000000000000004dd276000000000000000000001610000000bcf09f8000000000000000000000036b8000000a490000000ea26520001cbc0000000000f610868e61120000000b5c3f9a43507200000024a048454e00000017e800000000940000004ef8000fa400000000000aab420000190000000000000097c4822f480000008970000000b100000000000000000000000000000011b0001572000000000000098200000017681010002194a002930000000be61dc15098f8000000000000000000000000000000000000000000ba24cc0bc400000000000000000000000c9c00043f000000000000019f80012d214a00011cc00000000029d40000001f980013a2000000000000030e65e87b43540000000320daa6d10000000d126f82e6000000000000000000006d80001b480007f70000a90000bf35450f980008931868000610be8000000000000006b950140a0002d800012f80000000b4d7d47ea000000067c00000000000008f91101f2571081d1b30000000000000158c00000045019887125cb3900000000000000000000025316788418180000002428a7474b00000016e400000004cc5c8000010a2402085910589e14000000351ab5800000000000000008fe0000000000000000000000000030c80000000002b380000000000000000000b5100006280002f0000000000000000000000001d60000000000000000030d884a390000000000000000168d7c65863e3800000020f0ff91dcd482bb5750001170b194d2af9d3d600060592790d404501a89a88ec2702f892885fa721000000040a00000000000000000000001452bf15cb800000000000015f0ba057836500004be58c000000172200011591fd86c0000001a180002970a6800000000000000000000000001100000b1700023f0000a1b0000000000000000006c12c0000ce877c0002810000a1c0000000070001346000000319400000000000000000870001d5c0004d80000000000ba1000000000000000b0d647ee0000000000000000000000000
  | 31 => 0x3ec96f400000004e800000023c33b8000000000000049400000000000000000000000000000a5c0001d300008b6000000000061e20c8f7466e56551130a168e79c3751488000a610000000000cbc4260000000702000000000037000000000007ff3759a8400000000000000000000000540000c822840001820000000000000000065800007487e400000007e8000000000196c0a1000000000000055d0000000000466000000000000000009a400000000000000000001d900000000001248afa0000001f40818000000000000000050b000000000035d8f8000000000000003c0ac9000000000000028e996c26436f3780000000000373800168aa645d980000000000000000bbc00000000009e400045c857800024c00015c01ec000000000000000000000000000003fa00001840ee2ee80000000000560000000ae500027a54646bc1fb2078c4c00042da9f526c58b0000000f18000000149400000034b000000000000009d80000000000a6cde46a927f951474a00000028213680000000000000977000000123a0001162ca00000005a82d90000000441000000000000000c480400000017c82840000e10000568a6c00009640008c721e8d400000004460000e940000002200682000000000152c000155000072e8ae2a18f9ccfe71300000018ec0000001ae04869530000db0000000000000187852700000000000005508000dbca77000000081005b0be0000d1aaa43e127140009110000000000964262800141e000000000000000000000010181ca3e00fe800000000000000000000000000d6800000000003ec00000016a400000061c9d58df40005e6ae5800077000000005ea94200000000007b30000860000000000000092a00000000000001ef0002e5000072d0890000000cb500017640008db00000000000005c600000000004d713244ac7cc000000000000060b28f853a00000000009de9d00000000c182da563100496000000000011a473b0001394000b0329a800000000033a27b400000006d99bc0000000000000000559000000000000000000000000e600000006440000001510000000000000000026d0001e4d9687a749080017a00004b19a4879e00052a8000000000000000000000020d24f964c9da5c680000000004d2000084e0000003190cbe0000002964ca600000000015e627700005b8000000000000000000000018000000002fe123d66c000554000000000000018c5254049601109800000017a29bd6d20000000eec000000000199c6d60000888000d9a000000287c0000000000000000000000000118200020300007040000000000000510000000015a00055da95c00000000000001060000000000000000000000000000000000000005660000000000000596000000000000024a4f6a81a1d
  | 32 => 0x1470f165e600032fc00092f4a1800000000053285dd17a0bb26780000000000000e740000004c5ade40000000000000000000122000000000000000000005970940e64000000000000076ea0d0002ddc000c85137063878c00014429c41e4bca308800104a0000000000000000000000176a3af1e0add967c0000000000000000139800000000000000000000000003199808000367298d65a0000002e8c0000003c086fc000000000000000000053b000000000000000005aa78e0003018c8600000000012d00004a700000000003cf000016e433000187c15c00034a8000dc06c700000010ea000000238c2f09cc4dc80000000000800000d92000000000000042149899715ea000000000000000000000001be21b00000016b68b019400017d6000000000000000000000000005e04103125052000000000000000000000000009a037d9c6c0008aa460000000000000025110964683ee8c3c00032f1ff93e414c6073118a080000004560000000000000000000041600000019520000000000a7c000000189119c5c90cb0f44d84b803d8146ce9a77e4aa8a3cea000000027f531e0950000744000bda000131d67000000000000000000002b1c0000000000000000bdc00000000000a006c0cc80002a000014dc00000000025ec0000000000df40000000000001570ab600000000000005a980012bc00000000000005a80958000000c0a0002c84c74a100000000000c5d000000042a31d657b1c93f25644d594c00000000000000000000000000000000000000000000004a59ca079c000561049c00000000000009e646e161a26d2fc0001a1a1453ce18700013589727ca00000001520000000db98ee000000000150c00000000007d45685e98000000329000000000000000000000000002bb112d7b2a6d00000000460000002d8800016400008080000005fc00005fc000000177c000000184a1d85f6063000056564400046a8000d640000850000000000000000180ac19059a86400000000000000000000001ba0000c07406963cba6b5824c00000007d5000000000000049e00009160000000000000000127000000000000000000000000002c1c0000321f08000000000000000154600061d1a6c22e0005d680005e400000001100000000000000000000000000000030c2ff85048920004028000000a9936c80000008ed00000000006540000000bac0000000000f4a00000000000000000002b3c00028c00008fc0dc000000000000000021e000000052b1280000000000000000000000000000007a4c004031dfc3ee0ef30b00001fe841631a0d800000000027e00000000000000c280005b5947d7ec000000000000000000000000000000000830000000000000000000000000018660000000000a760002ce000000000000000000
  | 33 => 0x40c0000000000000000000000068800044d328909200040ba41ce9c69400000000000000000000c381a600000012b6000000215c65a000000000000000000000003a000058980000004c4000000173000000000000000000001d50000b040000000506000487000062e00000000007b6000644000000000000000001c600051d1c906220005a200000002d002d066482a53c33500000000002aa000185e5b23dc21b8cf8a840000d60b883be0002e740000d30002a8000000012b80000005d500000005640001dc8000000b7b00023340000000000000a9813a00000000000000001f0c9ae0002c018b946e000000054c0000000c8000000000052222fc000000000000000000000000000000000000000b44000415ab34da0898302b1700000000000000f8a000000000000000000000000000000000000000000000000000000000004506e64a90000001302000000113800000000000015588a923c9d10a7277c0000f8d032b3b06a31657ca96e2310000c9c0004a00000dfc4ad0000ff400098700026340000002268000bd80000000000000bde0000d8400000041f9d9c000afa56b80012ca60a4e980004260004762cbc0000004cb1f58000000527b05d0480300000000000c1e1f60000d82000000000000000000000016969cb000000000062f00000000007e50000cd8b8a0000000000b76730000000000000000018dc00000000000014ac97f0002eed26800000000000ee0000000000000000000315c000000000010cfb088b0000680f4c000000000000001e5018d5c2e4c9e00013f40000e70000000000000000000000021c31a99000000000000000000c45000000000000000006880008340000000000000006000000000000021d0ef4000000000000000043f80000000001338e2800016a157a9ac0da9d50001ad400000000000000004e300000000000000ab209d966000000000000000000000006ec0000000000c4200000000cc0001c300000000000003b3000000000000000000000006088d1969e0004c19c8c38c000000000000000048d00000007400000000b060000002b1558600000000000000fb1170bbd3e61b400021690d20000000000330a9b33600000008ea2e1814d7ea00018c0000000000000000000000000015240000000000000e280000002c2400000026e842d0fc3774f28000000000000000100400000000000000000001d14ada0003a480008380000000000000000000000000000000000014d400051509158dc71c0002f6c00000000022e80000003a3aa7cbb89490002bdc658ab23b10000000000409800000000000000010882a617b00000004f75b000000000000001ca400000000030240000000000000d024cc14700000000003ac80002d650956e8ef4d160003c3aec827a00000013049d00000
  | 34 => 0x33e8000000000000292c000260000000000010f4f50000000076000277000000000000012827101e4800000000000001600000005880b18000000000000000077100019c000000000027040000000000000000000000000000002d44a800178400000000000000002f81e8800000000000008c60006258001888000000017cd960000000000000000000000000000000000013ee000347800000013c1ee1b192ba00000001185cc000000127c7f00000c90000000ac80000d9400016200000000000006601d68000000000000000000018b0f5400014900000000001b600016b01b42b700000000000000000000000782000031c000c4a02800000000004b9800177c2f9000239006e0004fe21780000000002e1ca4600000000000000004cf80000000000000000bc800000000000000000000000000000000000041000054032a800000000025d000000000000004aa9922570000dee0000000000e5886b00023b94b0a8d48b13b070000049c00000000001f5a9cd2b43b55aa00000000003678974000000000000000000058b21dc08400000000000000000000a2817c00000000000000000001334000000000000000041d0000000f8c99500000000000000000000d88000000000000000008d82fc00000000000000002c10729ce590c0000bf076800000043c00000000003a30000d60000000000000086d000000000058400000000002d64e10000000b0d000069400000000000000000000000000000000000219000000000000000ea000000000000000000890257c0a025e39a140700000000000000000330b230000000000000000000000400000000000000000b660a70000000000bd40000000d5400000011080000002d58000000000339b1380003c80000000262496000000000000000000000000003d1800117c7f81e011e80003830002f188b800000000005c00000000000000000000000033800047c020000000000000012d60003fb13788480000fd000000069300000000000000000e7c0000000000000dc267b57b00000000000002eb05620002298000000000000000000000000007cc0000004ec8a44e0acac00000000000000000000000000000000000000000000018f0000304000000062900000000000001178f2800011f00000000002860000000808000000000000000020c064d1460003a10000000000000000114e3de0000d5400046b00000000000000000000000000000000000000000000f80008e1142a21549873157f80000000000dc95fc00050f0002af4000000223000000096c22d31bc000000000140800000000000004240000000000598c7c61e80000004866298d2800000000000ec0006df000000000000000025e594c0005730000000aaf319a18800000000000000000000002c180006dd0001664
  | 35 => 0xd5a400000000000000000001b208720000000000000000457800000019e000000000000000000000005ed000000000000000023c8aa000000029756c200000000000000003e0b12000081600000017c800000000000008b100001286f00000000000e86000283089c000a9700024b000033800007645ca0003e9800000065500030040006ad3cf80000007cf656818081600000000011020004ce00007a60000000001856000000237000000000000000000000002b10822704000000000038f38e800000000059480000000006071198bfa0000f8aa9828e000000207188e0002af800179800016d952c0000000130000000000000000000000000000000000002971e64ffa000000000000000000018fcde80002b50000000a1d50480000000000001464c980000000000000000000211c0000000000000af60003d400000000f460a000131c51600025c40000000002728f3600000018100005c73090d7000000000000000000000000a340000002de0b440000000000000000000000000000044800000000009cd0cd800000000000000000000001ec800000000000011c4a48ca138c183860ea3f06583ac9f60011c816547841385c487547967775dc2b900000002e300000480000000e3800032a0b982f0000000000000000000041500008c80a25d22ead4940001d323ac48c68e2720001028000203800000000001000007ea6e537e0d2c00087d00000000000005fe800000000000000003b6ca00000650000000000000000000026980000003ee00000000000000000bdc000000000000000000000000000000000001e7400000032200000007682a38000000b82000248c00000000000007b400000000004e49ce1971a74000000000000000000018d8000000000000000000000000000016362ca2e7109567e7723b28000f1200000000000007b700000000000005e19df400000000026b4000b750000000000000000000000000051e80a442891f00023d4f6815800000000000000001ce0000b860000000000000000000000050100000000008a84ddab5543400057a000000000000000015d88d80000000e009d700000000000002b79f5152600000028bc000000000000000000000024e53fe8d3000093c0000004020000000000000000000000000000e80000000000000000000000000138826b2c98000000cba14f9558000000000000000000000000000000000003090000000171222400069700000000000000000c80a820000002c81078b1d00000000006b700000000009b055ba849530ae0000221caa64364338c949d400000021480001cd09a86ec000a2500027b8000000000000000052d00025580000005d429ece4e53d0f203558a20000000000000000000048caf2000000000000076a00000000001d70000000000000
  | 36 => 0xc5016f0b48bf2000000000000000000000000008dd00024dcf2a0002749bd4000716000000127e68301ea0cc5da1340000000b0e00000000000000003f700001a40000000000000000000000168c000198000030800035b1a9d0cc0c500000000000000000000000000000329539000000000005600000000001916000609212171c00000000010aa0003aeae7800000022d935400000000028900000000000000000000530000000000000010c000089e0002b400000000000000000000000126c00000039a00008de00013600000000000d7b29106e0000002aa821c0004468000000000000122000000059500000d400000000000000002ea00016280000b400000000000002b70000bb04c21040a70a262ae286000000000000000000000000000ac40000000000000b85000208857e00048d80007280000000000b40930000000000000022200000000000001b14000432000292000000d4a6148050828b00000013ea6ff0001d840000000001db00000000002ad0a2e0000002ce8d980005e700015f86a826800000000001d100004c855a4d400000000003f89fc12a2000190acb80800002da80002b4c3813a80000000000000000eaa0000000ce50e468c000000000000034f000000000000100000000001e1afb853800019d800000082300000000001c001c8000000645065048400000000000000000000001fd400000000000bc00000000000000009c0000000000000000000011760001640000aa40000001eac13600000000004b80000001b6d0f40001258600eb000063112d00001ba00000000000000000000ef023100026dc00000000000000000000000000000000000000000047c0000ee8000000555800000000048e026400000008e800029833a4659ca93201cf00018ec0003ad0002fbd61e6bd074800087c00000000000000005f6000000000000000004522a800000002aa46c5b31968000000000000150a0000000000000ad10000bcd1beb9b00025841b2000593800185883200000000008c322b80000004a500000000000000e2800000000000000000000000000000000bd10000000a280000001db800000000000000009b500007e0000000000000000000000000000005e3621800000000004b80000003624e4800000009800000013c68940000000000000336800000029800000018986790000000206573000000007846a00017d4fce00041da39c0000005b68001506000131000000044130c13b80003840002519006c8d18e0000000258553819443a00000000005d80000000000000000000000000000060400011c0879000000147059200e82e00000000000001852a3c0000000c8c0004a6800027200000000000001b700000000000000000000f1e2e10fa9574a4c00040c207
  | 37 => 0x2866800000000014a80540000d240005ca64b00000001d324c80000000000000000000a365be80017082be437800000000000000000000004c52d240009d60000000cd0000492000000000000012d8000b810002a7021237500000000000000000000d40000000000000000000029387340003c203356022cb49a98c14ce000000108055c5ee0000000000000000000000000000000007300006480000000000304a128c4e5040002f1400000046300018600f500000000000003d20000f9c0001b4800000000000000017fc09c0c880000000000000000b0a9e80000d340000000000e78e6479a00000000000004c8800025800000000000000002b700006660000000000cdc00000000000000000000000000000000000000000000009846142780002d740f600000000000000003cc1d04000000191800034e000578800000049000003f800000055f0000000489000000000000000000000e6000023aa0869000000027d000037a46c9290000000000000000000028c00014860002550834146c3e0000000000000587000130c000000080c7f2000000000000000000000010be00063f993400000000022700000000001cfc00097a1d600000000000000bac1f448d00029f8000cc1124000166a00008f27c400000000000000000a8000000055800000016600000000000000000000000000000000000000002ecb63000000000000000000000000004558000000000000000000012d0000000000c6c00000000000000002264bca00000000018441e322383718b44ed1a12c086c600013e80000000000002b68000000000000000060d000000187646d0002a440005db64e0001618000000274983829a57780000000004c4000000063453e000143c074000193c000000045065c0000001058ae400000020180000000000000000000536000000000000000016980000000001fe4000000000000000000000000000004da0001ab000000022f8000b4e0000000df000000045e1dd553a0000001e585aec810001ba446800000000000000005b88db505000020a000121232b3dd2100fbcb232af2dc064c00034c00011e800000000009088cf03600002e0000000000000000029a000163000000000001ee000000033800000000000000009206150001468000000068d95cb902090f88000b652d52408000bc81fe2cc0a5ea4100000000000000d4191cc2631425a92cd5a887c37685b58eaaed00000000005b80000000000000000000000000000027c93c2000000000000000000000000000000000000000000000249504c7cd53900017ba00000003317da0000000000800000000000000000000000000000000001ec48ba0005158a880000000002028ebc0000000000000ab54ca000000000000000002c0c800000000000000630800000000
  | 38 => 0x47099e316a320ce406911284989020cf000000018800000000000000000002ba400000000200000000000288a640000002898000b840000000000000c260000000000ba600013288680e8000000000000000000008ac000516951813400003f32287c80000002b8c000be2000000000071900000000002b33f1a57c000c5e00003e000024a000000000030000000000000000000000000000000000000000000021ec0000000000000000000000000000000000026e00000003b4acdc0000000001b4c88a25a39980002be0004df8d4cf9600000027ec4e800000023cc00000000005e9342c60000038003800000000018fa2635c9a29000022837200007de6f6007a3c4000000000000000000029980000000000d80bf0000993285a2100009851168c680000c12cf0d687a800050a2bed25600000000000000000000e2c000000000000000000032b8000000cbe00000000002651c2b27c0000000000000000c2500026f80000000000000000000000310400053119e8000000ade00000000000000002be40004af00000010c2000000000000000054f000000000000028cc0000000000000000000000000077ea940003158768000000000000000032800fc00075c00000000000000002c680000000000000e5c00000000000000000000000000c520000794fe40000000000000000000000135863900000000009893730544db80000000000000000348000000000000000008fc00000001fc0000000000001622a0000000018f40005ac80002cc8e816c000192235b00b8bb812400000000000000000000000cc60000000aa40000001d0000000ea814b380018ce00007880000000000000000000000000000000000059e800105cbd5000000000000000000000000000000000000c3543980001160ea072284c99c70b0000000000000299000000014300000000000006192b4c0001c800020d40002b8000000000006b00000000000005de0000000000000000000000060aac
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x1a0c83d9562509100048ba6065589424400182c8719562509100058364c655894244001a0c83195625091001c2ba6387589424400182c87e1562509100060b21c85589424406328e98e0d62509100062321f83589424400188f8720d62509100062321c835894244001a0f8520d62509100068321483589424400122e98d4d625091063e0b21f535894244063a0c83d4d62509100048b26153589424406982c8754d625091018e8320d535894244001834766167150910006251d9839c5424400145593196768c5100058964864d9631440018a4865c9428c51016ca92616250a314406368493589428c5100058964864d95314400168592193634c51050d85a538654d3144001a1464a19534c51050d85a5b6454d3144143a148454f624c510004952615358931440058548754d624c51050e85211535893144001a148654d424c5100062921b7250931440552a498589424c51018d2925d62509314406368493589424c5100078154d6250931440014a59219276885100058564c65d922144001854865cd5388510144952616354e21440676449258d53885100058564c65d91214400185486dcd534851012c952616354d21440674549758d534851019d912496354d21440016459319762485104bd89a57865092144001a2465a1942485104bd89a5b655092144001a2486d9542485104bd892576350921440012a49858d424851000d2925d63509214412f6249558d424851000589259535092144001e056354d42485100051564c65dc530440014549654f714c1100052964864dc520440014a49650b7148110006152197354e10440018a4865c942841100051564432dd95304001459900cb7654c1000515644325d95304001459900c97654c1000585644325915304001619900c96454c10007035d07354d6204079645911cd53588101e5926407354d62040014a5910cb76508100052a64032dd942040014a5910c976508100052a640325d94204001625910c965508100058a640325954204001a0d852096350810635a16448258d420418d689902096350810006830cb8654d4204001a0c326195350810007030cb7654d4204001c0c325d9535081019d832496354d4204063a0c8354d62508100051564c75dd910040014a5921d376440100051564c85dd910040014a59221376440100060d21c745951004001625921d165440100060d21c755911004001615931d564440100051525d8558d1004001255981d56344010007051d47458d1004001685921d163440100041d25d8654d10040018348759153440100061521d6354d1004001645931d562440100052925d8458910040012a5981d16244010007091d47458910040014649754d62440100042d25d8650910040018348759542440100062521d6350910040018a4875894244010
  | 1 => 0x6e060e811c142480019a2876047050920006c8615811c14248001b8183604705092018f031cd5350b61480012a4985096118520007031d9535093148001a448654d314852019f031d953509304800545a97e19534c120005922598254d3048001a4886609534c12000d2aa5b8750930480015889760d424c1200066221d835093048001d0b8754d424c1200074221d535093048001e0b9654d424c12000782259535093048063e0b7654d424c12019f429d9535093048067d087654d424c12018f821d9535093048067c087654d424c120004d2657814c9304800138994e05324c12019d832496354d42c4063a0c8354d6250b1050d85a538654d31c406368493589424c7100078154d6250931c40676449258d53487104bd89a578650921c4001e056354d424871019d832496354d4284063a0c8354d6250a100068960981193654400142d9219173d95100048b64a8498f654400105f985cc73d95100048b64a84cc7654400105f9361f21d95100068560d81197644400141d9319572d91100048764e8598b64440010af9261f31d91100048764e85c87644400182c7560864d8d100060bdd582191634400182c756086458d100042ba6064dc9634400142d921927654d1000515644329d95344001459900ca7654d100050b648641d95344001455918c87654d1000516640321d95344001855836047654d100058324983d91534400121d988cb6454d100048766032d915344001615910cb6454d100058664032d91534400121d98cc76454d1000417a607658d534400184c821d96354d1000487a636458d534400181c87d916354d100068320b6458d534400121e981916354d100060721c6458d534400160d921916354d10006832086458d534400905e98e1d6354d100060721f8458d534400181c872116354d1019c93a638258d534400184c87e096354d1000613e1c8258d534400184c872096354d1000683e108258d5344001a0c842096354d1000487a634258d534419181c87d096354d1019e8320b4258d5344001834766127154d10006191d9829c5534400181c7460c65d8910006071d183195624400105d981cc65589100050764c65dd1624400105e9819773589100050764c659d942440014a5910ca76509100052a640329d9424400141d93194765091000529647321d942440010ad980c876509100052a640321d942440018a58260476509100058324d82d95424400122d98ccb65509100048b66032d954244001625910cb65509100058a64032d95424400122d98c876550910006830ca8654d4244001a0c322195350910007030ca7654d4244001c0c321d95350910194872616354d424400141c9758d535091019d832496354d42440010ae981d962509100062320c76589424400122e98d9562509100060b21f655894244
  | 2 => 0xc54331798d0b7154d3150cc5251801c5534c46724c9261a7054d3150cc5251819c1534c47785486dc57054d31006071d9841c1534c40184c766087054d31006151d9811c1534c46521e98dd9535093100583a5b8254d424c5f9a0c86e09535093100545a5f8154d424c40170592205535093119e83a1953d89424c467c0c7254d42d813150d85a538654d3188543c147454d31582214bcc9a57815cd424846942e97e19535092100583a5b7354d4248639c0c76dcd535092118d83a5b6354d424840182c766177150921005c164e85dc5424852f32798617715092100649a1d85dc5424852f32798d4f7150921004c9e6153dc542485311a598dd47150921006c160d531c5424852f32495600715092118ca324d869c1424852f3249560670509211be2921b715c1424840182c766147050921006231d9831c142484018a47660470509214bd49a578750a314852f92485509708c52119f031d953509314840545697e19534c52150d85a538654d314840154697e09534c52198e5121f8254d31484679468754f724c52100d29a5b87509314852f52695e1d424c521005a1a5b835093148661a8486e0d424c52118da1a5b63509314852fd079754d424c5214bf4125d535093148401d078754d424c5210074121d535093148401e079654d424c52100781259535093148543e078654d424c52150f81219535093148463e077654d424c52119f419d9535093148467d047654d424c52118f811d9535093148467c047654d424c52119e5120953dc13148401d055350b704c52118f031cd5350b6048463c847350931d81210078154d424c7604840141d931d774586300050764c751d1618c00182f7560874586300060b1d5821d1618c0070ac985d942486304be8921542585218c001349922017154d3000515259711c5534c00151994dc77054d3000646a1d841c1534c00194a876087054d30006c2a11821c1534c001b09846087054d30006c2a51821c1534c001b09946087054d30006c260b421c1534c001b4182a047054d3000654a1d811c1534c001b11846047054d30006d0609811c1534c00160e96e095350930006c2e0b8054d424c00170992201535093019e83a1953d89424c067c0c7254d42d85300049526153584614c0018578754d6118530007031d953509214c001c847650931485300050764c75dd1618800141d931d474586200060bdd5821d1618800182c756087458620024172617654d3188143a148454d614c62000583a5b7354d424806360e96d8d5350920004e264c805c542480014a4965c4715092000742dcd53dc1424800152995dc770509200064aa1d851c1424800198a8760c7050920006c2a15831c14248001b098560c7050920006c2a55831c14248001b099560c7050920006c260f531c14248001b098354c705092
  | 3 => 0x4219cc3249839d9535080130d980ca7654d4200543a5c329d95350801705910ca7654d42005c2640329d95350801b0432a067654d42006c10c9819d95350801705910c97654d42005c2640325d9535080103f985d87654d42004c3a60321d9535080150e970c87654d4200583a58321d95350801c0d760c87654d42005c1644321d95350801709900c87654d4200585a4776d8d5350801526919db7254d42004c366363dc95350801c0c76d8f7254d4219cc3a4d81dc9535086730e936037254d42006830ca86dc55350801a0c3261b7154d42006830ca869c55350801a0c3261a7154d420060ba1b729c5535086712d98dc87154d4200549647721c55350801527925c47154d4299f410c9711c55350801a0c32e197054d42006830c8865c1535080182c86dc97054d42006c10cb815c15350801927722057054d42006c10c8815c15350801a0c32a187054d42006830c9861c15350801b0432a047054d42006c10c9811c15350a2390c7260e75d854200543a4f729d7615080190d83dca75d854288c4ba63725d7615080150e93dc975d854200543a4f825d7615080112e980c975d854200549644325d76150801529900c975d85420044ba63215d76150801585910c973d854200562640325cf615080190c32e1d53d8542006430c98754f615080112f985d732d85424c6499d5829476150801525910c975985420054a640325d6615080158591209739854200562640825ce615080190c32e1d5398542006430c98754e615080181f87d8d5398542006295c981d94615086341d97d8d5318542005856476354c6150801a178354d6118542997810c95358461508012a698cc961185420048d6548058461508012959320161185420052c241615c06150801525910cb75581420054a64032dd5605080158591a0b73581420056264282dcd605080190c32a1d5358142006430c88754d605086750e92dcd53581420060721f6354d60508011a6980cb71581420074154c32dc560508015a1900cb715814200705d8d531c560508014a696cc8715814200469660321c56050801d05530c8715814200568640321c5605080183471617615814200549644325d46050801529900c9751814200561644325cc605080190d85209731814200561644825cc605080158990209731814200562643215cc605080190c32e1d5318142006430c98754c60508011a5980ca71181420074154c329c460508015a1900ca711814200568642825c460508011a5980c971181420074154c325c460508015a1900c971181420060d5d4815806050801895732056018142006295c881580605080141d939d674d85320060b60a759d3614c80182d825d674d85320050764e755d3614c94331694e057254d31006071d984dc5534c40170592a137154d3150cc5e6184dc5534
  | 4 => 0x82f600000000000000590b10d000000117000000000ab2821208b0690007ccc280000000000000392680470000ce42000077000000ac0b33961248d9ae2a61547d16d37a80c27936122000f290611a7a0bc1af306728ff98128a1e0e08111d87a8b71390ea314000b001c6981610f0ca484c58e306804c438023ea000b8800184000148003625441581d224150141e33be000738003bc000000900003600013c0000002c0d11f6000db14e000000eb8003103c01200010805c860700000fcfb0c30000008f06f244184aa12c000000001e6332000000da0000000000000058c209920001ec001c001227c000a43ce340a58aa34e0c0920002d664ce68a52262a0001a102a000c00573b4000621ec0006cced8000000009e800000088e7146000000000002982b4ce00004c1b8d68000002bc211203720005a1a20a64404284b1e21b4198000000e020030180200c00000000040001c0103c020080100001000000040700007000000000b0700602c000200802815000090040100801028010140b0000600c00000010001202c0602c010240100000000000002a008030000000800000010040a0000004c010000602c01024180000000010008010240000c020080102401000050100101402000000140101406000000000000c010100400800038120040006c000140702c14004150040500018004060ac000240e00408004030240503c000140400009018070000600801004060040101002000020000150e92dce74d855300643dcd829d36154e5b90c7360a74d855396c47a63735d36154c0150e92dcd74d855300543a4b835d36154c0111e980c974d855300545644325d36154c01519900c974d855300447a63315d36154c01545910c972d855300552640325cb6154c0111f985d232d8553516459d1839076154c01515910c9749855300546640325d26154c015459120d729855300552640835ca6154c0185573607641855300495a62325846154c0123594201611855300499648805846154c014709058570185530054564432dd16054c01519900cb74581530055164683dc96054c0154990a0f725815300455a6032dc56054c01551900cb715815300515a5a321c56054c01155980c8715815300554640321c56054c0183471613615815300545644325d06054c01519900c9741815300551644325c86054c0190d8420d721815300551644835c86054c015499020d721815300552643315c86054c01155980ca711815300554640329c46054c0155190a0d711815300455660325c46054c01551900c971181530060d5d0815806054c01855732056018153006195c8815806054c6330c9360b7654d42004c366032dd9535080160e960cb7654d42005c164432dd95350801709900cb7654d42006c10ca81dd95350801b04326077654d
  | 5 => 0x384ce8731f07545107e000004190000004c0001ed000364ad0b60345704784c402228929f43040484b1fc228740b2800000000f902f2505a09785f28452005196170408000a01fe67ce19f81d64fcc50b70086a48f94031e320ad9b54046c01a8e0288528268002066780198c27c2784608001e5c05d10508e000311c53285a8870de0000001b84400034c00072146468a908904e3701501c1c87705d90d0365cc0018d40e07c7f0071f2000eb1d11b6750ac86b3561e44c8bf104114c813a1de7844197704602cec14330e574000001724d00016634a35c8c99803016400000354588839571ee3d4f109a1243b8fd115136824669862704b8570f23e23a40000c23a5a40000039059c3b0d5262790a394f3646382d0060003ccaf1fd000250001c20a2080560003c0000000003fc1f427137378084c883c1825c8001d32c0000128bd0c0000650950f4218691043984044e800000000ca8a9000000d207f0bc540000cb000764f59791ec000f48c92926243192a062000001d20000005f02d06c460000e80007ece79dd2ec0f84c06a01a5b0dd0711ac3b42320a238318171ee14e5f4da200000284440ea00000000000334444000c7028300df05d24c610671a80cc8200017c3de000ba8741c4814ab2062004d4458001a800032155080710dc1c7216000fb97a0000006f8e5126000848380004c8bf0f4000584000001f80001d8000004b42901e2fe000001270000e44092b000000e315f0000f40017412e0009986c3580002d87c32e66c2e16f000015020fd0002d4001a3000128df85036e2700014d074000218000004282b12919e7e40c800000000661bb3e0590730101780000b12314c0006e80027600
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xa8400ac068032a077654d4200460b5219303bb2a6a1002b01a00c981dd95350801182d486540ceca9a8400ac068032a067654d4200460b52193033b2a6a1002b01a00c9819d95350801a02bb322190eca9a8400d025d9900c87654d4200601b303b6c7b92a6a100220da90ca86dc55350801504d0065436e2a9a8400a816843261b7154d42005413401930db8aa6a1002a05a10ca869c55350801504d0065434e2a9a8400a816843261a7154d42005413401930d38aa6a1002a05a10cb865c15350801504d0065c32e0a9a8400a03a9c322197054d4200540b421910cb82a6a1002a09a00c8865c1535080118354865c0ae0a9a8400ac068032e057054d4200460b5219102b82a6a1002b01a00c8815c15350801502d0865430e0a9a8400a8268032a187054d4200540b421930c382a6a1002a09a00c9861c15350801182d4865408e0a9a8400ac068032a047054d4200460b5219302382a6a1002b01a00c9811c15350801086d4865c3aa7b0a8400a4268032e1d53d854200520b421930ea9ec2a1002909a00c98754f6150801482d0865c3aa730a8400a4268032e1d539854200520b421930ea9cc2a1002909a00c98754e6150801218d2920b0ae030a840092468c90585701854200520b421950ea9ac0a1002909a00ca8754d60508014075306443aa6b028400a416843221d5358142005213401910ea9ac0a10031069854c32dc56050801a80a9b20196e2b028400c41661530c87158142006a02a6c806438ac0a100310585644825cc6050801482d0865c3aa63028400a4268032e1d531814200520b421930ea98c0a1002909a00c98754c6050801882cc2a6194e23028400d4054d900ca711814200620b30a9864b88c0a100350153640325c46050801806c9b053ace9b0a6497941aa78754d424c52150d40d51cb2a6a1262908cec06a7e59535093148401406d18eac10e8b0c6000a0368c75608745862019d8154fcb2a6a126090002a05a10ca8654d4244001504d0065432a6a122000a8268032219535091000580b42194eca9a8488002c09a00ca7654d4244001206d48643b2a6a122000b02680321d953509100060190ec98cab12848800220da920c655894244001502d10c9432a698a20009812a553589424c51050e40930a9ac4a1262880c74049754d625093144001502d18cb4328490a20979812a56354d424851000540950b1aa6a1242880cec04a758d535092144001502d0865c32a6a102000a8268032e19535081000540b421930ca9a8408002a09a00c98654d4204001602d0865bb2a6a102000b0268032dd9535081000580b42192eca9a8408002c09a00c97654d420400181243b243a2ca8802000c0521d931d5644401000502b503a8e8b1a2008003404756487458d1004001812cc0ea3a2c48802000b0168c751d16244010
  | 1 => 0x18d089100000005000f00001891ca5340098ac281c0194016c6400000114f400000014000000442c0000000000000001280000000000907000200d74000171380000000000e800040000000094240000d53cc8f83c0000e00154ec00000038b841780000d85964fc8cbd58812000680008000000000074017d8031310c5d859001246cdc34b19c0000015c000000c49d2c0001a05568000100b4c0858d4d614461080078481000cc7d4800000105984d40a9180150a0e408000018000800021802020432000000060200001a00080600020200000206000000040090c6909058570185530048c344482c2b80c2a980310584644835c86054c01182d486540eeca9
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x200005005b81d5921d163440100060059868c751d16244010
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x4
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x2
  | 6 => 0x1
  | 7 => 0x4b
  | 8 => 0x4c
  | 9 => 0x4d
  | 10 => 0x4e
  | 11 => 0x124d
  | 12 => 0x94b
  | 13 => 0x94c
  | 14 => 0x94d
  | 15 => 0x94e
  | 16 => 0x124b
  | 17 => 0x124c
  | 18 => 0x124e
  | 19 => 0x138b
  | 20 => 0x138c
  | 21 => 0x138d
  | 22 => 0x138e
  | 23 => 0x98c
  | 24 => 0x98d
  | 25 => 0x98e
  | 26 => 0x128c
  | 27 => 0x128d
  | 28 => 0x128e
  | 29 => 0x9cb
  | 30 => 0x9cd
  | 31 => 0x9ce
  | 32 => 0x12cb
  | 33 => 0x12cd
  | 34 => 0x12ce
  | 35 => 0xb0c
  | 36 => 0xb0d
  | 37 => 0xb0e
  | 38 => 0x140c
  | 39 => 0x140d
  | 40 => 0x140e
  | 41 => 0xb4b
  | 42 => 0xb4d
  | 43 => 0xb4e
  | 44 => 0x144b
  | 45 => 0x144d
  | 46 => 0x144e
  | 47 => 0xccd
  | 48 => 0xcce
  | 49 => 0xd0c
  | 50 => 0xd0e
  | 51 => 0xecb
  | 52 => 0xecd
  | 53 => 0x94055
  | 54 => 0x94056
  | 55 => 0xd0a
  | 56 => 0xd0054
  | 57 => 0x188a
  | 58 => 0xd0056
  | 59 => 0xeca
  | 60 => 0xec053
  | 61 => 0xec055
  | 62 => 0x1a4a
  | 63 => 0x124955
  | 64 => 0x124956
  | 65 => 0x95255
  | 66 => 0x95256
  | 67 => 0xb0955
  | 68 => 0xb0956
  | 69 => 0x94b15
  | 70 => 0x94b16
  | 71 => 0x140956
  | 72 => 0x140955
  | 73 => 0x95415
  | 74 => 0x95416
  | 75 => 0xb4955
  | 76 => 0xb4956
  | 77 => 0x94b55
  | 78 => 0x94b56
  | 79 => 0x144955
  | 80 => 0x95455
  | 81 => 0x144956
  | 82 => 0x95456
  | 83 => 0xd0956
  | 84 => 0xd0954
  | 85 => 0xec955
  | 86 => 0xec953
  | 87 => 0x130a
  | 88 => 0x134a
  | 89 => 0x139255
  | 90 => 0x139256
  | 91 => 0xd1254
  | 92 => 0xd1256
  | 93 => 0xed253
  | 94 => 0xed255
  | 95 => 0xb1395
  | 96 => 0xb1396
  | 97 => 0x138b15
  | 98 => 0x138b16
  | 99 => 0xb5395
  | 100 => 0xb5396
  | 101 => 0x138b55
  | 102 => 0x138b56
  | 103 => 0xd1396
  | 104 => 0xd1394
  | 105 => 0xed395
  | 106 => 0xed393
  | 107 => 0x128996
  | 108 => 0x99295
  | 109 => 0x99296
  | 110 => 0x9c995
  | 111 => 0x9c996
  | 112 => 0x12c995
  | 113 => 0x12c996
  | 114 => 0x150c
  | 115 => 0xcb
  | 116 => 0xb0996
  | 117 => 0xb0995
  | 118 => 0x98b15
  | 119 => 0x98b16
  | 120 => 0x98cd5
  | 121 => 0x98cd6
  | 122 => 0xd0994
  | 123 => 0xd0996
  | 124 => 0x98d16
  | 125 => 0xec995
  | 126 => 0x1a4b
  | 127 => 0x168b
  | 128 => 0x9d295
  | 129 => 0x9d296
  | 130 => 0x8c
  | 131 => 0xed295
  | 132 => 0x12c9d5
  | 133 => 0x9d2d5
  | 134 => 0x9d2d6
  | 135 => 0xb49d5
  | 136 => 0x9cb55
  | 137 => 0xb49d6
  | 138 => 0x9cb56
  | 139 => 0x9ccd5
  | 140 => 0x9ccd6
  | 141 => 0xd09d6
  | 142 => 0xec9d3
  | 143 => 0xec9d5
  | 144 => 0x9ced5
  | 145 => 0xd12d6
  | 146 => 0xb4b15
  | 147 => 0xb4b16
  | 148 => 0x144b15
  | 149 => 0x24b
  | 150 => 0xd0b14
  | 151 => 0xd0b16
  | 152 => 0xb0d16
  | 153 => 0xecb15
  | 154 => 0x16cb
  | 155 => 0xb5416
  | 156 => 0x20c
  | 157 => 0xed415
  | 158 => 0xd0b56
  | 159 => 0x154c
  | 160 => 0xecb53
  | 161 => 0xecb55
  | 162 => 0xb4ed5
  | 163 => 0xd1456
  | 164 => 0x10b
  | 165 => 0x130b
  | 166 => 0x8d
  | 167 => 0x180b
  | 168 => 0xa0b
  | 169 => 0x150d
  | 170 => 0x28b
  | 171 => 0x20d
  | 172 => 0x184b
  | 173 => 0xb8b
  | 174 => 0x148b
  | 175 => 0x154d
  | 176 => 0xe8b
  | 177 => 0x170d
  | 178 => 0x18cb
  | 179 => 0x178b
  | 180 => 0x15cd
  | 181 => 0x58b
  | 182 => 0x14c
  | 183 => 0x134c
  | 184 => 0xce
  | 185 => 0x198c
  | 186 => 0xa4c
  | 187 => 0x168e
  | 188 => 0x2cc
  | 189 => 0x24e
  | 190 => 0x19cc
  | 191 => 0xbcc
  | 192 => 0x14cc
  | 193 => 0x16ce
  | 194 => 0xd4c
  | 195 => 0x15ce
  | 196 => 0x1a0c
  | 197 => 0x170e
  | 198 => 0x4d14
  | 199 => 0x1a4d
  | 200 => 0x188e
  | 201 => 0x5555
  | 202 => 0x4b55
  | 203 => 0x59d5
  | 204 => 0x4b16
  | 205 => 0x56d6
  | 206 => 0x5856
  | 207 => 0xd0b095e
  | 208 => 0x14a
  | 209 => 0xecb495d
  | 210 => 0x10a
  | 211 => 0x94d14
  | 212 => 0x95896
  | 213 => 0x95a55
  | 214 => 0x94ed5
  | 215 => 0x94d16
  | 216 => 0x124d14
  | 217 => 0xd0b139e
  | 218 => 0xecb539d
  | 219 => 0x139415
  | 220 => 0x139456
  | 221 => 0x9c98cdd
  | 222 => 0x9c98cde
  | 223 => 0xd09c99e
  | 224 => 0xec9c99d
  | 225 => 0xd1514
  | 226 => 0x99555
  | 227 => 0x150995
  | 228 => 0x995d6
  | 229 => 0x12ced3
  | 230 => 0xed693
  | 231 => 0x9ced3
  | 232 => 0x9d6d6
  | 233 => 0x128d14
  | 234 => 0x188c
  | 235 => 0x9d715
  | 236 => 0x1689d6
  | 237 => 0x98d14
  | 238 => 0xb1515
  | 239 => 0xd0b4b1e
  | 240 => 0xecb4b1d
  | 241 => 0x154b15
  | 242 => 0xb0d14
  | 243 => 0x144ed3
  | 244 => 0xb4ed3
  | 245 => 0xb5696
  | 246 => 0x140d14
  | 247 => 0x16cb56
  | 248 => 0x154d14
  | 249 => 0x16ced3
  | 250 => 0x9295
  | 251 => 0x8995
  | 252 => 0x170d16
  | 253 => 0xec113
  | 254 => 0xd1516
  | 255 => 0x151295
  | 256 => 0xeca13
  | 257 => 0x1a5295
  | 258 => 0xed313
  | 259 => 0x1a4995
  | 260 => 0xed813
  | 261 => 0x1a0d
  | 262 => 0xb8293
  | 263 => 0x21415
  | 264 => 0xec293
  | 265 => 0xd4d
  | 266 => 0x164d
  | 267 => 0x155415
  | 268 => 0xecb93
  | 269 => 0x1a5415
  | 270 => 0xed493
  | 271 => 0x1a4b15
  | 272 => 0xed853
  | 273 => 0xd1556
  | 274 => 0x14d14
  | 275 => 0xa4d14
  | 276 => 0x134d14
  | 277 => 0x198d14
  | 278 => 0x2cd14
  | 279 => 0xbcd14
  | 280 => 0x14cd14
  | 281 => 0x19cd14
  | 282 => 0x1a0d14
  | 283 => 0x18ced3
  | 284 => 0x15ced5
  | 285 => 0x188d14
  | 286 => 0x1715d5
  | 287 => 0xd2d6
  | 288 => 0xc9d6
  | 289 => 0xed695
  | 290 => 0x1692d6
  | 291 => 0x1892d6
  | 292 => 0x1889d6
  | 293 => 0x18ce
  | 294 => 0xbc2d4
  | 295 => 0x25456
  | 296 => 0xe8e
  | 297 => 0x178e
  | 298 => 0x16d456
  | 299 => 0x189456
  | 300 => 0x188b56
  | 301 => 0xed6d5
  | 302 => 0x1715d6
  | 303 => 0x1a4ed3
  | 304 => 0x15cb55
  | 305 => 0x170b16
  | 306 => 0xecb829b
  | 307 => 0xbc2cd1c
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 64
  | 7 => 1382
  | 6 => 3829
  | 5 => 3266
  | 4 => 523
  | 3 => 105
  | 2 => 2
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
  | 2 => packedAt gbK2 (i*92) 83
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
  | 2 => gbHint (packedAt gbK2 (i*92+83) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 9 => packedAt gbK9 (16+((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 2)*1) 1
  | 8 => packedAt gbK8 (1811+((h/21+packedAt gbK8 (1664+(h % 21)*7) 7) % 84)*7) 7
  | 7 => packedAt gbK7 (56194+((h/460+packedAt gbK7 (51134+(h % 460)*11) 11) % 1824)*12) 12
  | 6 => packedAt gbK6 (200380+((h/1276+packedAt gbK6 (183792+(h % 1276)*13) 13) % 4595)*13) 13
  | 5 => packedAt gbK5 (207926+((h/1088+packedAt gbK5 (192694+(h % 1088)*14) 14) % 8399)*13) 13
  | 4 => packedAt gbK4 (38350+((h/174+packedAt gbK4 (36610+(h % 174)*10) 10) % 690)*11) 11
  | 3 => packedAt gbK3 (8785+((h/35+packedAt gbK3 (8505+(h % 35)*8) 8) % 183)*8) 8
  | 2 => packedAt gbK2 (186+((h/1+packedAt gbK2 (184+(h % 1)*2) 2) % 4)*2) 2
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xe07ffe0c0e07fffff0701fffff09118f03f0ff
  | 1 => 0xff8783f00ff870783f801e1e1f36e9749d4c93
  | 2 => 0xfff803fff0007f803fffe01fe0c70e78e18f1c
  | 3 => 0x3ffffff80003fffffe000f80f80fe0fe0
  | 4 => 0x3ffffffffffc000000000fff000fff000
  | 5 => 0xfffffc00000000000000000000ffffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x88000000080880010020200000001001025
  | 1 => 0x6a850a7086c83450bc80d4545e1269348d4c92
  | 2 => 0xb350129590405d4115254019c2470258a18518
  | 3 => 0x804212a2b9500022a4a99c004b80d80560ac0
  | 4 => 0x124043cfcd666e678403009088efb000fbe000
  | 5 => 0xdc66780301840804080c110110fddfee000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefaeafeaafaa8feeefaeafeaafaa8feeefaeafeaafaa8feeefaeafeaafaa8feeefaeafeaafaa8feeefaeafeaafaa8feeefaeafeaafaa8feeefaeafeaafaa8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36240
namespace PEqualNP.Outside.L_meta_36240
open PEqualNP.Outside.L_meta_36240.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 1 := bs0_4_0
theorem alls0 : ∀ k ≤ 4, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_2_0 : Interval s1Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 4 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 21 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 17 := block_range (n:=17) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 17 := bs1_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 1 := bs1_5_0
theorem alls1 : ∀ k ≤ 5, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_32 : Interval s2Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_64 : Interval s2Atlas 3 64 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 68 := (concat bs2_3_0 (concat bs2_3_32 bs2_3_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_32 : Interval s2Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_64 : Interval s2Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_96 : Interval s2Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_128 : Interval s2Atlas 4 128 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 129 := (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 (concat bs2_4_96 bs2_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 13 := block_range (n:=13) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 45 := (concat bs2_5_0 bs2_5_32)
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
theorem bs3_3_0 : Interval s3Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_32 : Interval s3Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_64 : Interval s3Atlas 3 64 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 68 := (concat bs3_3_0 (concat bs3_3_32 bs3_3_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_32 : Interval s3Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_64 : Interval s3Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_96 : Interval s3Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_128 : Interval s3Atlas 4 128 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 129 := (concat (concat bs3_4_0 bs3_4_32) (concat bs3_4_64 (concat bs3_4_96 bs3_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 13 := block_range (n:=13) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 45 := (concat bs3_5_0 bs3_5_32)
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
theorem bs4_2_0 : Interval s4Atlas 2 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 14 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_32 : Interval s4Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_64 : Interval s4Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_96 : Interval s4Atlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_128 : Interval s4Atlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_160 : Interval s4Atlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_192 : Interval s4Atlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_224 : Interval s4Atlas 3 224 3 := block_range (n:=3) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 227 := (concat (concat (concat bs4_3_0 bs4_3_32) (concat bs4_3_64 bs4_3_96)) (concat (concat bs4_3_128 bs4_3_160) (concat bs4_3_192 bs4_3_224)))
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
theorem bs4_4_128 : Interval s4Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_160 : Interval s4Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_192 : Interval s4Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_224 : Interval s4Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_256 : Interval s4Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_288 : Interval s4Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_320 : Interval s4Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_352 : Interval s4Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_384 : Interval s4Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_416 : Interval s4Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_448 : Interval s4Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_480 : Interval s4Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_512 : Interval s4Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_544 : Interval s4Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_576 : Interval s4Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_608 : Interval s4Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_640 : Interval s4Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_672 : Interval s4Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_704 : Interval s4Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_736 : Interval s4Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_768 : Interval s4Atlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_800 : Interval s4Atlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_832 : Interval s4Atlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_864 : Interval s4Atlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_896 : Interval s4Atlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_928 : Interval s4Atlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_960 : Interval s4Atlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_992 : Interval s4Atlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1024 : Interval s4Atlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1056 : Interval s4Atlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1088 : Interval s4Atlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1120 : Interval s4Atlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1152 : Interval s4Atlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1184 : Interval s4Atlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1216 : Interval s4Atlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1248 : Interval s4Atlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1280 : Interval s4Atlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1312 : Interval s4Atlas 4 1312 28 := block_range (n:=28) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 1340 := (concat (concat (concat (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 (concat bs4_4_96 bs4_4_128))) (concat (concat bs4_4_160 bs4_4_192) (concat bs4_4_224 (concat bs4_4_256 bs4_4_288)))) (concat (concat (concat bs4_4_320 bs4_4_352) (concat bs4_4_384 (concat bs4_4_416 bs4_4_448))) (concat (concat bs4_4_480 (concat bs4_4_512 bs4_4_544)) (concat bs4_4_576 (concat bs4_4_608 bs4_4_640))))) (concat (concat (concat (concat bs4_4_672 bs4_4_704) (concat bs4_4_736 (concat bs4_4_768 bs4_4_800))) (concat (concat bs4_4_832 bs4_4_864) (concat bs4_4_896 (concat bs4_4_928 bs4_4_960)))) (concat (concat (concat bs4_4_992 bs4_4_1024) (concat bs4_4_1056 (concat bs4_4_1088 bs4_4_1120))) (concat (concat bs4_4_1152 (concat bs4_4_1184 bs4_4_1216)) (concat bs4_4_1248 (concat bs4_4_1280 bs4_4_1312))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_64 : Interval s4Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_96 : Interval s4Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_128 : Interval s4Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_160 : Interval s4Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_192 : Interval s4Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_224 : Interval s4Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_256 : Interval s4Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_288 : Interval s4Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_320 : Interval s4Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_352 : Interval s4Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_384 : Interval s4Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_416 : Interval s4Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_448 : Interval s4Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_480 : Interval s4Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_512 : Interval s4Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_544 : Interval s4Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_576 : Interval s4Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_608 : Interval s4Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_640 : Interval s4Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_672 : Interval s4Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_704 : Interval s4Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_736 : Interval s4Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_768 : Interval s4Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_800 : Interval s4Atlas 5 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_832 : Interval s4Atlas 5 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_864 : Interval s4Atlas 5 864 26 := block_range (n:=26) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 890 := (concat (concat (concat (concat bs4_5_0 (concat bs4_5_32 bs4_5_64)) (concat (concat bs4_5_96 bs4_5_128) (concat bs4_5_160 bs4_5_192))) (concat (concat bs4_5_224 (concat bs4_5_256 bs4_5_288)) (concat (concat bs4_5_320 bs4_5_352) (concat bs4_5_384 bs4_5_416)))) (concat (concat (concat bs4_5_448 (concat bs4_5_480 bs4_5_512)) (concat (concat bs4_5_544 bs4_5_576) (concat bs4_5_608 bs4_5_640))) (concat (concat bs4_5_672 (concat bs4_5_704 bs4_5_736)) (concat (concat bs4_5_768 bs4_5_800) (concat bs4_5_832 bs4_5_864)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_32 : Interval s4Atlas 6 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 44 := (concat bs4_6_0 bs4_6_32)
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
theorem bs5_2_0 : Interval s5Atlas 2 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 14 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_32 : Interval s5Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_64 : Interval s5Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_96 : Interval s5Atlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_128 : Interval s5Atlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_160 : Interval s5Atlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_192 : Interval s5Atlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_224 : Interval s5Atlas 3 224 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 227 := (concat (concat (concat bs5_3_0 bs5_3_32) (concat bs5_3_64 bs5_3_96)) (concat (concat bs5_3_128 bs5_3_160) (concat bs5_3_192 bs5_3_224)))
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
theorem bs5_4_384 : Interval s5Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_416 : Interval s5Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_448 : Interval s5Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_480 : Interval s5Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_512 : Interval s5Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_544 : Interval s5Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_576 : Interval s5Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_608 : Interval s5Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_640 : Interval s5Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_672 : Interval s5Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_704 : Interval s5Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_736 : Interval s5Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_768 : Interval s5Atlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_800 : Interval s5Atlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_832 : Interval s5Atlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_864 : Interval s5Atlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_896 : Interval s5Atlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_928 : Interval s5Atlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_960 : Interval s5Atlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_992 : Interval s5Atlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1024 : Interval s5Atlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1056 : Interval s5Atlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1088 : Interval s5Atlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1120 : Interval s5Atlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1152 : Interval s5Atlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1184 : Interval s5Atlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1216 : Interval s5Atlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1248 : Interval s5Atlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1280 : Interval s5Atlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1312 : Interval s5Atlas 4 1312 28 := block_range (n:=28) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 1340 := (concat (concat (concat (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 (concat bs5_4_96 bs5_4_128))) (concat (concat bs5_4_160 bs5_4_192) (concat bs5_4_224 (concat bs5_4_256 bs5_4_288)))) (concat (concat (concat bs5_4_320 bs5_4_352) (concat bs5_4_384 (concat bs5_4_416 bs5_4_448))) (concat (concat bs5_4_480 (concat bs5_4_512 bs5_4_544)) (concat bs5_4_576 (concat bs5_4_608 bs5_4_640))))) (concat (concat (concat (concat bs5_4_672 bs5_4_704) (concat bs5_4_736 (concat bs5_4_768 bs5_4_800))) (concat (concat bs5_4_832 bs5_4_864) (concat bs5_4_896 (concat bs5_4_928 bs5_4_960)))) (concat (concat (concat bs5_4_992 bs5_4_1024) (concat bs5_4_1056 (concat bs5_4_1088 bs5_4_1120))) (concat (concat bs5_4_1152 (concat bs5_4_1184 bs5_4_1216)) (concat bs5_4_1248 (concat bs5_4_1280 bs5_4_1312))))))
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
theorem bs5_5_576 : Interval s5Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_608 : Interval s5Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_640 : Interval s5Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_672 : Interval s5Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_704 : Interval s5Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_736 : Interval s5Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_768 : Interval s5Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_800 : Interval s5Atlas 5 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_832 : Interval s5Atlas 5 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_864 : Interval s5Atlas 5 864 26 := block_range (n:=26) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 890 := (concat (concat (concat (concat bs5_5_0 (concat bs5_5_32 bs5_5_64)) (concat (concat bs5_5_96 bs5_5_128) (concat bs5_5_160 bs5_5_192))) (concat (concat bs5_5_224 (concat bs5_5_256 bs5_5_288)) (concat (concat bs5_5_320 bs5_5_352) (concat bs5_5_384 bs5_5_416)))) (concat (concat (concat bs5_5_448 (concat bs5_5_480 bs5_5_512)) (concat (concat bs5_5_544 bs5_5_576) (concat bs5_5_608 bs5_5_640))) (concat (concat bs5_5_672 (concat bs5_5_704 bs5_5_736)) (concat (concat bs5_5_768 bs5_5_800) (concat bs5_5_832 bs5_5_864)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_32 : Interval s5Atlas 6 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 44 := (concat bs5_6_0 bs5_6_32)
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
theorem bgb_2_0 : Interval gbAtlas 2 0 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 2 := bgb_2_0
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
theorem bgb_3_96 : Interval gbAtlas 3 96 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 105 := (concat (concat bgb_3_0 bgb_3_32) (concat bgb_3_64 bgb_3_96))
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
theorem bgb_4_512 : Interval gbAtlas 4 512 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 523 := (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 bgb_4_224))) (concat (concat (concat bgb_4_256 bgb_4_288) (concat bgb_4_320 bgb_4_352)) (concat (concat bgb_4_384 bgb_4_416) (concat bgb_4_448 (concat bgb_4_480 bgb_4_512)))))
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
theorem bgb_5_3264 : Interval gbAtlas 5 3264 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 3266 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat bgb_5_288 (concat bgb_5_320 bgb_5_352)))) (concat (concat (concat bgb_5_384 (concat bgb_5_416 bgb_5_448)) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))) (concat (concat bgb_5_576 (concat bgb_5_608 bgb_5_640)) (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 bgb_5_768))))) (concat (concat (concat (concat bgb_5_800 (concat bgb_5_832 bgb_5_864)) (concat bgb_5_896 (concat bgb_5_928 bgb_5_960))) (concat (concat bgb_5_992 (concat bgb_5_1024 bgb_5_1056)) (concat (concat bgb_5_1088 bgb_5_1120) (concat bgb_5_1152 bgb_5_1184)))) (concat (concat (concat bgb_5_1216 (concat bgb_5_1248 bgb_5_1280)) (concat bgb_5_1312 (concat bgb_5_1344 bgb_5_1376))) (concat (concat bgb_5_1408 (concat bgb_5_1440 bgb_5_1472)) (concat (concat bgb_5_1504 bgb_5_1536) (concat bgb_5_1568 bgb_5_1600)))))) (concat (concat (concat (concat (concat bgb_5_1632 (concat bgb_5_1664 bgb_5_1696)) (concat bgb_5_1728 (concat bgb_5_1760 bgb_5_1792))) (concat (concat bgb_5_1824 (concat bgb_5_1856 bgb_5_1888)) (concat (concat bgb_5_1920 bgb_5_1952) (concat bgb_5_1984 bgb_5_2016)))) (concat (concat (concat bgb_5_2048 (concat bgb_5_2080 bgb_5_2112)) (concat bgb_5_2144 (concat bgb_5_2176 bgb_5_2208))) (concat (concat bgb_5_2240 (concat bgb_5_2272 bgb_5_2304)) (concat (concat bgb_5_2336 bgb_5_2368) (concat bgb_5_2400 bgb_5_2432))))) (concat (concat (concat (concat bgb_5_2464 (concat bgb_5_2496 bgb_5_2528)) (concat bgb_5_2560 (concat bgb_5_2592 bgb_5_2624))) (concat (concat bgb_5_2656 (concat bgb_5_2688 bgb_5_2720)) (concat (concat bgb_5_2752 bgb_5_2784) (concat bgb_5_2816 bgb_5_2848)))) (concat (concat (concat bgb_5_2880 (concat bgb_5_2912 bgb_5_2944)) (concat bgb_5_2976 (concat bgb_5_3008 bgb_5_3040))) (concat (concat bgb_5_3072 (concat bgb_5_3104 bgb_5_3136)) (concat (concat bgb_5_3168 bgb_5_3200) (concat bgb_5_3232 bgb_5_3264)))))))
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
theorem bgb_6_3808 : Interval gbAtlas 6 3808 21 := block_range (n:=21) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3829 := (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat (concat bgb_6_224 bgb_6_256) (concat bgb_6_288 bgb_6_320)) (concat (concat bgb_6_352 bgb_6_384) (concat bgb_6_416 bgb_6_448)))) (concat (concat (concat bgb_6_480 (concat bgb_6_512 bgb_6_544)) (concat (concat bgb_6_576 bgb_6_608) (concat bgb_6_640 bgb_6_672))) (concat (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 bgb_6_800)) (concat (concat bgb_6_832 bgb_6_864) (concat bgb_6_896 bgb_6_928))))) (concat (concat (concat (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024)) (concat (concat bgb_6_1056 bgb_6_1088) (concat bgb_6_1120 bgb_6_1152))) (concat (concat (concat bgb_6_1184 bgb_6_1216) (concat bgb_6_1248 bgb_6_1280)) (concat (concat bgb_6_1312 bgb_6_1344) (concat bgb_6_1376 bgb_6_1408)))) (concat (concat (concat bgb_6_1440 (concat bgb_6_1472 bgb_6_1504)) (concat (concat bgb_6_1536 bgb_6_1568) (concat bgb_6_1600 bgb_6_1632))) (concat (concat (concat bgb_6_1664 bgb_6_1696) (concat bgb_6_1728 bgb_6_1760)) (concat (concat bgb_6_1792 bgb_6_1824) (concat bgb_6_1856 bgb_6_1888)))))) (concat (concat (concat (concat (concat bgb_6_1920 (concat bgb_6_1952 bgb_6_1984)) (concat (concat bgb_6_2016 bgb_6_2048) (concat bgb_6_2080 bgb_6_2112))) (concat (concat (concat bgb_6_2144 bgb_6_2176) (concat bgb_6_2208 bgb_6_2240)) (concat (concat bgb_6_2272 bgb_6_2304) (concat bgb_6_2336 bgb_6_2368)))) (concat (concat (concat bgb_6_2400 (concat bgb_6_2432 bgb_6_2464)) (concat (concat bgb_6_2496 bgb_6_2528) (concat bgb_6_2560 bgb_6_2592))) (concat (concat (concat bgb_6_2624 bgb_6_2656) (concat bgb_6_2688 bgb_6_2720)) (concat (concat bgb_6_2752 bgb_6_2784) (concat bgb_6_2816 bgb_6_2848))))) (concat (concat (concat (concat bgb_6_2880 (concat bgb_6_2912 bgb_6_2944)) (concat (concat bgb_6_2976 bgb_6_3008) (concat bgb_6_3040 bgb_6_3072))) (concat (concat (concat bgb_6_3104 bgb_6_3136) (concat bgb_6_3168 bgb_6_3200)) (concat (concat bgb_6_3232 bgb_6_3264) (concat bgb_6_3296 bgb_6_3328)))) (concat (concat (concat bgb_6_3360 (concat bgb_6_3392 bgb_6_3424)) (concat (concat bgb_6_3456 bgb_6_3488) (concat bgb_6_3520 bgb_6_3552))) (concat (concat (concat bgb_6_3584 bgb_6_3616) (concat bgb_6_3648 bgb_6_3680)) (concat (concat bgb_6_3712 bgb_6_3744) (concat bgb_6_3776 bgb_6_3808)))))))
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
theorem bgb_7_1376 : Interval gbAtlas 7 1376 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1382 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 (concat bgb_7_192 bgb_7_224)) (concat bgb_7_256 (concat bgb_7_288 bgb_7_320)))) (concat (concat (concat bgb_7_352 bgb_7_384) (concat bgb_7_416 (concat bgb_7_448 bgb_7_480))) (concat (concat bgb_7_512 (concat bgb_7_544 bgb_7_576)) (concat bgb_7_608 (concat bgb_7_640 bgb_7_672))))) (concat (concat (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 (concat bgb_7_800 bgb_7_832))) (concat (concat bgb_7_864 (concat bgb_7_896 bgb_7_928)) (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024)))) (concat (concat (concat bgb_7_1056 bgb_7_1088) (concat bgb_7_1120 (concat bgb_7_1152 bgb_7_1184))) (concat (concat bgb_7_1216 (concat bgb_7_1248 bgb_7_1280)) (concat bgb_7_1312 (concat bgb_7_1344 bgb_7_1376))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 32 := block_range (n:=32) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 64 := (concat bgb_8_0 bgb_8_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_9_0 : Interval gbAtlas 9 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_9 : Interval gbAtlas 9 0 1 := bgb_9_0
theorem allgb : ∀ k ≤ 9, ∀ i < count gbAtlas k, checkRow gbAtlas k i = true := by
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 24, 26),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefaeafeaafaa8feeefaeafeaafaa8feeefaeafeaafaa8feeefaeafeaafaa8feeefaeafeaafaa8feeefaeafeaafaa8feeefaeafeaafaa8feeefaeafeaafaa8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277074666 * 2 ^ 32 + 4272618152) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36240.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,4]⟩,⟨.and,[2,3]⟩,⟨.or,[1,6]⟩,⟨.and,[0,8]⟩,⟨.or,[7,9]⟩,⟨.and,[1,6]⟩,⟨.or,[5,10]⟩,⟨.or,[3,12]⟩,⟨.or,[0,11]⟩,⟨.and,[13,14]⟩,⟨.or,[10,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4272618152) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074666 * 2 ^ 32 + 4272618152) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36240

open PEqualNP.Outside.L_meta_36240 in
theorem PEqualNP.Outside.L_meta_36240 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4272618152) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074666 * 2 ^ 32 + 4272618152) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
