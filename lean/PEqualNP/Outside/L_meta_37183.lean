import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37183.Model
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


end PEqualNP.Outside.L_meta_37183.Model

namespace PEqualNP.Outside.L_meta_37183
open PEqualNP.Outside.L_meta_37183.Model
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

def SBf (j : Nat) : Nat := [4, 8, 8, 6, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_37183

namespace PEqualNP.Outside.L_meta_37183
open PEqualNP.Outside.L_meta_37183.Model
def s0K3 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (i*3) 3
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (4+((h/1+packedAt s0K3 (3+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffbecf
  | 2 => 0xffffffffffffffffffffffffffffffffffdf73
  | 3 => 0xefbc
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffff4205
  | 2 => 0x2412
  | 3 => 0x1828
  | _ => 0
def s0Atlas : Atlas := ⟨3,rawDecor 14 s0Pos s0Neg, 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37183
namespace PEqualNP.Outside.L_meta_37183
open PEqualNP.Outside.L_meta_37183.Model
def s1K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K6 : Nat → Nat
  | 0 => 0x120008023287522e54000005634c092c38d8a26300154e8839f5e0c0100018880329532d02a50005810d081e5ce210a2c0283c040080100082d2e0492c3280ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31df31fe31fd31dd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30de30fd30fc30dc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x617e510c2faa2186fd0430dea0861df310c3bc6218774c430ee188617e500c37c80186f10030ef98061fa300c3ba60187e4c030efaa061de540c3baa8187715030efa9061de520c3baa4187714830efa1061de420c3ba84187710830efa8861de510c3baa2185754430ee28861df410c33e82187790430eea08619d410c3b8821877c8430ef10861dd210c3b842187794030af28061da500c3be80187790030cf20061dd400c3b880186710030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c83bca7905794f20bea9e41dd53c82baa7905f14f20bf28e417d51c837e83906f50720ef98e41dd31c83de43907b48720df20641bc40c83bc6190770c320bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3106fd0620dea0c41df31883ba63107b88620f610c417e508837c81106f10220ef18441dc30883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20bfa8a41f751482eea2905f14520fa28a4174514837e82906f50520ef98a41dd31483de42907b48520df20241bc40483bc6090770c120fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20bea98417c53082fca4105f94420bea8841bf410837a821077cc420ee98841ee21083d842105f94020df20041bc40083bc6010770c020f790041fa20083da40107e48020bfaa6217e54c437ca9884f95310beaa621bd54c427aa9885f15310bfa9e217e53c43bca7885794f10bea9e21dd53c42baa7885f14f10bfa96217e52c42faa5885f14b10dfa0e21bd41c43be6388774c710df20621bc40c43bc6188770c310bfaa421bf548427ea9085f95210beaa4217c5484378a9084f15210bfa9c21df53842bea7085f94e10bea9c217c53843b8a7085714e10bfa94217e52842faa5085f14a10bea8c21bf418437a830877cc610ee98c21f721843e843085f94210df20421bc40843bc6108770c210fd10421f920843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910dfa0a21bd41443be6288774c510df20221bc40443bc6088770c110fd10221f920443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf28821bf410437a820877cc410ee98821f721043e842085f94010df20021bc40043bc6008770c010fb88021fa10043ea20087e44010
  | 1 => 0x721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21dfa0a43bd41487be6290f74c521fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf290437e510877e8210ef50421ef98843dd31087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e81de53d02bca7a05f54f40eea9e815d53d02fca5a05f54b40bf28e817d51d037e83a06f50740ef98e81dd31d02faa9205f94e40bea9c81bf439037c87206f50e40de21c817e52902faa5206fd0a40df21481bd429037885205f94640bea8c81bf419037c83206f50640de20c81df31903ba63205f94240dfa0481fb409037ea7206f94e40dea9c81bc539037ea5206f94a40dea9481bc529037e65206f8ca40de99481bc329037ea3206f94640dea8c813d5190378a3206fcc640cf98c81be319037a6320674c640de18c81bf219037c43206f48640de10c813e50902fea6a077d4d40afa9a817c53503b8a6a05714d40bfa92817c52502fea2a05f14540dfa0a81bd41503be62a0774c540fda0281be40502fca8205f94c40bea9881bf431037c86206f50c40de218817e52102faa4206fd0840df21081bd421037884205f94440bea8881bf411037c82206f50440de20881df31103ba62205f94040dfa0081fa401037a80207e50040dfa9881be531037aa6206f14c40dfa9081be521037aa4206f14840df99081be321037a64206f0c840dfa8881be511037aa2204f54440de28881bf311033e62206f8c440de988819d311037862206fc8440df10881bd211037842206f940409f28081ba50102fea9985f95330df2a6613e54cc2faa9986f553309eaa6617c54cc2fca5985f54b30bf28e617d51cc37e83986f50730ef98e61dd31cc37c81986f10330bfaa4617e548c2faa9185f15230bea9c61df438c3bc87187750e30ee21c617e528c2faa51877cca30ef19461dd328c3b865185f94630bea8c61bf418c37a831877cc630ef18c61dd318c3b863185f94230df20461bc408c3be61187ecc230efaa461de548c3baa9187715230efa9461de528c3baa5187714a30efa1461de428c3ba85187710a30efa8c61de518c3baa3185754630ee28c61df418c33e83187790630eea0c619d418c3b8831877c8630ef10c61dd218c3b843185794230efa0461de408c33c81187750230ee204619c408c2fea8986fd51309faa2617e544c2faa8985f15130de2a2613c544c2fea4985f14930bfa8a617c514c37e82986f50530ef98a61dd314c37c80986f10130fd98261de304c2fea8185f95030beaa0617c540c2fca61877d0c30ef21861dd430c3b886185f94830bea9061df320c3bc6418774c830ee19
  | 2 => 0xcbbe65197bcca32bf28c657d518cafca1195f54232bfaa265bf544ca7ea8995f95132beaa2657c544cb78a8994f15132ef21a65dd434cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf29865df430cbb886195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef90f41dea1e83bc43d06fca5a0df54b41dfa1683be42d077a85a0ef10b41bf286837d50d077ea7a0ef94f41dea9e83bc53d077ea5a0ef94b41dea9683bc52d077e65a0ef8cb41de99683bc32d077ea1a0ef943419f28683bd50d0778a1a0df552419eaa4837e53907bca720d794e41bea9c83dd53906baa720df94a41bea94837e519077e8320fdd0641bf284837d50906fea6a0df14d41dfa1a83be435077a86a0ef10d41bfa92837c525077e84a0ef90941dea1283bc42507ee82a0ef90541bfa82837c505077ea6a0ef94d41dea9a83bc535077ea4a0ef94941dea9283bc525077e64a0ef8c941de99283bc325077ea2a0edd4541dfa8283be505077aa0a0ef141419e282837e541067ca820df94c41ef298835e53106faa620f754c41aea98837e52106faa420df94441dfa0883f6411077a8220fd50441bf280837d50106fea998df95331beaa6637c54cc7be8798f790f31eea1e63dc43cc6fca598df54b31ef99663de32cc7ba6598f70cb31dfa0e63bd41cc6fca198df54331efaa663de54cc7baa998f715331efa9663de52cc7baa598f714b31efa1663de42cc7ba8598f710b31efa0e639f41cc7bc8398f750731cea0e63dc41cc7bea198f794331af28663dd50cc7b8a198dfd5231bf2a463be548c67ca918df55231deaa4633d548c6f8a918df54e31aea9c637e528c6faa518df94631dfa0c63bd418c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c7be8698f790d31eea1a63dc434c6fea498df14931ef99263de324c7ba6498f70c931dfa0a63bd414c7ee6298f78c531bfa82637c504c7bea898f795131eeaa263dc544c7bea498f794931eea9263dc524c7be8498f790931eea1263dc424c7bea298f5d4531efa0a639f414c7bc8298f750531cea0a63dc414c7bea098f794131eea8263dc504c6b8a098dfd5031bf2a063be540c67ca818df55031deaa0633d540c6f8a818df94c31af298637e520c6faa418df94431dfa0863bd410c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21dfa0e43bd41c87be6390f74c721bf286437d50c86fea910df95221df2a4433e54886faa910ef552219eaa4437c54886fea710df94e21ef29c435e53886faa710f754e21aea9c437c53886faa510df94621dfa0c43bd41887be6310f74c621f790c43f
  | 3 => 0x1ccfad60707652404045a25976999146e5d352fc0c21f0198006acb191d8db0005b13405466a059d6ada00011d170003aeebc0037d424f58e681a74a925023c425e6c58d9a4130a3189853000799ab8d9532891392590fce9d0a00069c6c84e1242a8f64001f968a3850ab383161f53abee370d100010d02258c38bc838efc801b2f24e8fd7929d00046817aac2d4a680abeb1b4fc1e608b386598c503e2061192b14f4aebe800000000b8cd40bd2dc01846000036000770006400017c8000006f5543091cc00c0240b8030120280384700006c00006000000020000160080680200e000000040160080000a00c000000020040080080b0060200080b0060200880700000004009000008008040060040c00f00200c00829010000040130100080180600e080020040000000100a07a0240480e00203c008230240300c00500202c040010000000380100200001814000004020010120000600201c02800011002040018030220540380001802806804004050038050080100681c01e0340180702200404803000088020080000000980003a0080c0050160000000000005000800012000138020480100100800600c00012008004028020080180001200a00001034004014028000020d40100200003c030030000040d00400e01c010020100180300000a000008040000200000001a018000020160001280f01801c0480006e0040c80901c038000070340140000500a00c190000380040000002200c018030040000200001204c0000701e01408003002014000020340180000503000410012000000028010060a800005000030008000000241d8080000140100000404c0100100401c0000000000011800000020090000260000000b02e044010000000140200400c0980780400e0080080300c03c09002000018005f94b43bea96877e51d0efaa3a1df94343bea86877d5490efca721efd0e43efa1c877e5290efaa521df94643bea8c877e5090efaa121f7d0d43df21a877f5250ef8a4a1dfd4543be28a877f5050ef8a0a1df95043bf29887bf4310fbc8621ef50c43eea18879d4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857e5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a85df5350abea6a15f14d42ee29a855c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42ef298855e5310afaa6217754c42aea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa71977d0e32ee21c657e528
  | 4 => 0x8834000083222d01100035caa8a5b10000379e7b7708800161bb100000037800000b88cc289000c9c99b9f56c7b11c2b51ba0008e800134408208000262f9bc3831742a42d83d102000ab2be0c613d62aa3714e6d402197c43112004d230ea8b43291d62187888f404e30380e0466449e0af166ce212e86a1fc2003d9d2616d90f982b732da0821161264e0429d04da56069a4c0a42c86c1ce5ea9504f8ae6bc000ae800000904781f66382900006e52c78c092674d855c0000a000a980029e4120002ab1451c0004d8052b84155931d71e5bd81194752e55940b12500b9668955562853f8004360007b26b3caf85599b306eeac5e35841c7e13e0ca2f6c10e885e00000102a527800010b8696e02290e9e45aa4ec4f21e27cf81c29ba0fe3d4963f73405413c0004e6b7c7e3325ce784fa89d016e00af92666835807a857ce621ea81f77cc1c558587d0d19d33a8238a494b8bf442ad06312e4f6f74988ea300001c4a0b4227189935c0789997292501c619b2899222d9d1e8c8226508f421657a5c1de1b90323bc001231ca37d2f10c2b6b4d9e2a075cf2565ac7794afca605c6902813214e04c3e91f18123cb40a2bb60000c483000000f956c0e240e79c270720cc0000036e000705d1974660c64f70002ec9d8119c239e01daf814784b71d093714c66df98c27b89808fb943aca099f93a772f14f51610000ed46a4b3c47c84a24a7a25e53718d46a041c59d81209dc102702821b55c02a0002c1d000034a8980036c000eccffaf84c6669c984864ce69062887085546e32a25afa49c9ab5601897f2186de0014d8ac6102953a000000ab80eb4a54400143bce522c602e92b106ba19234228ca1001000000c15ba98200000132b000004f0000006aa4392c0007a45440031f2da000342e600039c9abdf440520f68cc33890d3d28b62a1ac3a9be44a774de0b335e0000000d0005f1b593d36c7c1aebbd00030c000350007e85401e5fa6ec4680021e0017fab91e8b280028f000c94db80011259c00114320000cb8ce59072480000000fa8fba3776e5fd149445e05c853a81000000d32bc000911b930c696d44f7800642221cb00054a00198bed5a86580010800000000000000678a9a980009c43295e000df06810911c001193ac2d2001083123aa1442b10131e96d79bdb764001238006ec0000000402ee74b5bf152a0006a80053e00021aa935a989b50d2244a71dd8b7000000fdb0e5ec76cfa3f55d22482b8f900009dda9297b000416800786c686bad949c529aa079030de4e208438ac0c5c2d1548a9d76000242c34120001040017b9cb78cabc002e13268b1ac8f8398001b690b6fe31d6d9ca7e80009b2ee4aad4d211d3144c058f1785143c8108aa0b468934bf64a23001a000060ac40004b0009f40035b000e49b98ad7c60019d0b57c84
  | 5 => 0x1da227000001e998c0d8000a4b7a0e8128001dc7746b1ce38e474000f497a29a564000001fe000048000004c03213f15e3b5608e955a17c3b94049a16588b9e000b3c000000003b0ef8007ae721722935bc82937b2b2fcf40ea3b00748d843bb82681e9ad3235a4cb4f03615884a98b20378e32c1fac22a43cd77a0f7bc5c5ed25f000cf40032e5989f922b74446e41a7a28000f98c180062e0c8df800000889830000001ccd38e343eb74003810000000007856e769c327974484d1c845308000002466f6030bab7e2c0000bb800454440d521a36834430000084f340000049e51d5d2343e2971648002b468cd8000214d992d34070ee447ba001723f462800000b5dc11150a000100989000614a1ace676000001171a8fb1cc3bf576a50d4b0a478a84c91eb5c0000001197defe17d80061e8181434c18200000349000125481c0000da46484c058001758003428bd280006e22d9a6b520000014333e038000489954560d800339506000000002ca000002ea0008c06698e000f2d30b6366eb00740294a60000032236a779a38762c8e3433839000094beb2c462000fe91b3f8000000001f6ccc002f41c87f8ce800176d044b8002c4d80c3bd4438d89a19202e6d4067a0874
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0xc40842b56110210c7d52308431c548c210b5586308431f540c210c715030842d5610c210f808620842f06148210f8c85208423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544423e60151108f180544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c7150534425e6014d1097180534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109dd85524426e6514910cbd50524432c5414910d3d4c524434c5314910da580524423e65d0510c7d4f414431c53d0510cbd4b414432c52d0510ae983414423c6550510c7d4d414431c5350510cbd49414432c5250510ae181414425e65cc510c7d53314431c54cc510d3d4b314434c52cc510b6983314425c654c510c7d51314431c544c510d3d49314434c524c510e550531442d8604c5108f996404431f5390110c714e404432f5290110cb14a404423e6510110c7d4c404431c5310110cbd48404432c521011097996304431f548c110c7152304434f528c110d314a304425e650c110c7d50304431c540c110d3d48304434c520c110da14a20442786548110d914a104425e63d50109758f540426e62d50109b58b540423d65950108fd85540423d61550108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c1097d85530425d6154c108f990530423d6414c109798c530426e6214c109b588530423e64d48108f593520425e63d48109758f520426d6594810cb952520432d5494810d394e520434d5394810cb951520432d5454810d394d520434d5354810d9185520423e64148108f590520425e63148109758c520426e62148109e980520423e64944108f592510425e63944109758e510423d65d0410c794f410431d53d0410cb94b410432d52d04108fd95410431e5350410c754d410432e5250410cb549410425d65cc410c7953310431d54cc410d394b310434d52cc41097d95310431e544c410c7551310434e524c410d3549310436552c84109d594210423f65900108f596400431e5390010c754e400432e5290010cb54a40042b561900108fd94400423d6510010c794c400431d5310010cb948400432d5210010ad584400425f658c01097596300431e548c010c7552300434e528c010d354a30042d5618c01097d94300425d650c010c7950300431d540c010d3948300434d520c010b55843004398400c0109e596100436952840109dd9510042e462440109ed9510043695244010
  | 1 => 0x8398400c2208f587544823e64951209798e544825d63951209d9865448275619512097d8d544825c63551209dd85544827461551208f994544823d6115120c7d53534831c54d4d2097587534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209dd8553482746154d2097994534831f5414d20c7150534825d6114d20cdd53514833454d4520d5d4f514835453d4520cdd93514833464d4520d5d8f514835463d45208f990514823d64145209798c514825d6314520cdd5051483345414520d5d4c51483545314520cd99051483356414520d598c51483556314520dc580514823e65d05208f197414831f53d0520c714f414833751d0520cd147414823e65505208f195414831f5350520c714d41483375150520cd145414825e65cc52097197314831f54cc520c7153314835751cc520d5147314825e654c52097195314831f544c520c71513148357514c520d5145314826e65c8520d9147214836451485208f996404831f5390120c714e40483375190120cd146404823e6510120c7d4c404831c5310120cdd444048334511012097996304831f548c120c71523048357518c120d5146304825e650c120c7d50304831c540c120d5d443048354510c120e61003048364518812097d8d540825c63550209798c540825d63150209d984540827561150208fd91530823c6454c208f990530823d6414c209d98453082756114c208f992520823d64948209798e520825d63948208f992510823d64944209798e510825d6394420cd94541083355150420ae1814108356514c420d554531082d8604c4209b59621082e960084209bd9520082e46148020ea10120083c830480209ed95200825e63d53109758f54c425e63153109758c54c423e64d4f108f59353c431e5494f10c755253c431e5454f10c755153c423e6414f108f59053c423e64d4b108f59352c425e63d4b109758f52c423e6414b108f59052c425e6314b109758c52c431e53d0710c754f41c431e5350710c754d41c431e54cc710c755331c431e544c710c755131c4395414c710c794e40c431d5390310c794c40c431d5310310c795230c431d548c310c795030c431d540c310e610030c433561d5210ce983548425e63952109758e548425f63552109718d54843356115210ce980548431f54d4e10c7153538435561d4e10d6983538423e6494e108f592538423f6454e108f191538431f5414e10c715053843556114e10d6980538423e6494a108f592528425e6394a109758e528423f6454a108f191528425f6354a109718d528431f53d0610c714f41842ba60d0610c7d4d418431c5350610ae181418431f54cc610c715331842da60cc610c7d51318431c544c610b618131842f16008610c7d4e408431c5390210ad586408431f5310210c714
  | 2 => 0x605063097994418c25d651063097996218c25d6588630a7992218c29d648863097994218c25d6508630a7990218c29d6408630b6980218c2d96008630a7586408c31d5190230a7584408c31d5110230e6980408c23d61d51308f992544c25d639513097d8d544c23e65151308f584544c23e64145308f590514c23e65d05308f197414c23e65505308f195414c25e65cc530c7d53314c31c54cc530c7d51314c31c544c530d5d45314c23e65901308f994404c31f548c130c7152304c26e62150309b588540c27661150309d584540c23e6494c308f592530c25d6590c30c7151430c25d6510c30c7550430c23f64548308f191520c29f644c830a7191320c29e640c830a7590320c34d520c8308f992510c23d6494430cd945410c3355150430ae181410c35551cc43097596310c29e648c430a7592310c29e640c430a7590310c29e64cc030a7593300c25f654c030a7d91300c29c644c0309ed95300c2da60d5030c7550540c2ce6215030b3588540c2d66115030b5584540c2da6015030b6983520c29f6454830a7191520c29e6414830a7590520c34d5214830b5984520c2d56114830b6980520c2da6090830b6582420c25f655083097195420c25e651083097594420c2da60d4430a7992510c29d6494430a7990510c29d6414430b3988510c2cd6214430b6980510c31d51d0430a7983410c25e659043097596410c29d6490430d5546410c3555150430b6d81410c2d86050430e5d85410c3965150430c7545410c3955150430c5545410c39b6050430a7181410c3986050430a6181410c25e651043097594410c29e641043097996210c25d6588430a7992210c29d6488430d5546210c3555148430b6d81210c2d8604843097994210c25d6508430a7990210c29d6408430b6980210c2d96008430c7d06500c31d4194030d6982500c39b4194030e6506500c25d65d0030a7586400c31d5190030a7982400c31e5090030e6942400c25f6550030a7584400c31d5110030a7980400c39a6010030c7940400c39a50100309798f54c825d63d53208f58654c823f61553209798c54c825d63153208f99353c823d64d4f20c795253c831d5494f209758653c831e5454f20c755153c825f6154f208f99053c823d6414f208f99251c823d64947209798e51c825d63947208fd9741c823d65d0720c794f41c831d53d07208fd9541c823d6550720c794d41c831d5350720ae18141c825f65cc7209759731c831e54cc720c755331c825f654c7209759531c831e544c720c755131c82d8604c720c794e40c831d5390320c794c40c831d5310320c795230c831d548c320c795030c831d540c3209798f548825d63d52209798e548825d63952208f993538823d64d4e208f992538823d6494e208f992518823d64946209798e518825d6394620ba580218
  | 3 => 0xe40c7d4e53902ba6014e40a798f529029d63d4a40ae983529029e6394a40a758e529032f5294a40ae980529023f654ca408f195329023e650ca408f59432902ba60d4640a798e519029d6394640a798c519029d6314640ab98851902ad6214640ae980519031d51cc640a7983319023e658c6408f5963190397614c640c7545319029c604c6408f994319023d650c6408f996219023d6588640a798e219029d63886408f994219023d6508640a798c219029d6308640ae98021902b9600864097587535025d6114d409798c515025d63145408f997415031f53d0540c714f415031f5350540c714d4150337515054097997315025c65cc54097995315025c654c540c7d4e405031c5390140c754c431025f63548409718d521029f6350840a718d421029e6310840a758c421032d52108409798e511025d6394440cd547411023d6590440a798e411029d6390440a798c411029d6310440d59453110355514c440b6181311029e63d0040a758f401023f6550040a7d8d401029c63500409ed9540102ba60d4c40c754c53102ae6214c40ab58853102b66114c40ad58453102ba6014c40ae983521029f6354840a718d521029e6314840a758c521032d5214840ad98452102b56114840ae98052102ba608c840ae582321023f654c8408f195321023e650c8408f59432102ba60d4440a798e511029d6394440a798c511029d6314440ab98851102ad6214440ae980511031d51cc440a7983311023e658c4408f596311029d638c440cd5463110335514c440aed8131102b8604c440e5d853110396514c440c75453110395514c440c5545311039b604c440a71813110398604c440a6181311023e650c4408f594311029e630c4408f996211023d6588440a798e211029d6388440cd54621103355148440aed8121102b860484408f994211023d6508440a798c211029d6308440ae98021102b96008440c7cc6501031d3194040ce982501039b3194040e64c6501023d61953308fd8554cc23e64947308f59251cc23f65d07308f59741cc23f65507308f59541cc2b86050730c795331cc31d54cc730d554731cc31e544c730c755131cc26e62d52309b58b548c31e5450e30c7d50438c23e6494a308f592528c29f644ca30a7191328c34e524ca30a7990328c29d640ca308f992518c23d6494630a7992318c29d648c630d5545318c29e640c630a7590318c29e64cc230a7593308c2ce62d5230b358b548c2da60d5230c7d52548c2da6015230a7993528c29d64d4a30b6983528c29e6494a30a7592528c34f5294a30b6980528c25f6550a3097195428c25e6510a3097594428c2da60d4630a7992518c29d6494630a7990518c29d6414630b3988518c2cd6214630b6980518c31d51d0630a7983418c25e659063097596418c3976150630c7545418c29c
  | 4 => 0x7590524c74d5214931b5987424c6d561d093197d95424c65c655093197994424c65d6510931e5d47414c69e60d053197996414c69d6490531e5d85414c7975150531a7181414c65e6510531a7990414c69e64d4131a7593504c69f6454131a7191504c6cf6254131b3189504c71f4114131c7504504c65e63d50318f596540c63e60950318f181540c63e64150319798c540c63e64944318f592510c63d65d0431c794f410c63f6550431c794d410c71e54cc431c7553310c65f654c431c7951310c71d544c4319dd95310c756534c4318fd91500c63c645403197d8d54c865c63553219798c54c865d63153218fd9153c863c6454f218f99053c863d6414f21e550531c863f64543218f19150c865f63543219718d50c865e63d52219758f548863e60952218f181548865e63152219758c548863e64d4e218f593538871e5494e21c7552538865e6094e21c7951538871d5454e2197181538863e6414e218f590538871e53d0621c754f418871e5350621c754d418871e54cc621c7553318871e544c621c7551318863f64542218f191508865f63542219718d508865f63551219718d544867b60551219e181544865e63151219758c544863f6454d218f191534867b6054d219e181534863e6414d218f590534863e64d41218f593504865e63d41219758f504865e63d50219758f540867a60d50219e583540863d65950218f982540863c60550218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c2197982530871e5454c21c7551530865c6054c218f990530863d6414c219798c530867a6014c219e580530863e64944218f592510865e63944219758e510863d65d0421c794f410871d53d04218fd95410871e5350421c754d410865d65cc421c7953310871d54cc42197d95310871e544c421c75513108795414c4219bd9521087a54148421f14c521086776548421ce95250087395494021d694e50087595394021ced9250087386494021d6d8e50087586394021ced0650087394194021d6cc6500875931940218fd91500863c645402197d8d500865c6354021ce95150087395454021d694d50087595354021ced9150087386454021d6d8d50087586354021ced0550087394154021d6cc550087593154021dac85500876921540219758653d025f6154f409798e51d025d6394740c794f41d031d53d0740cd54741d031e5350740c754d41d025f65cc7409759731d025f654c7409759531d02d8604c740c794d439025e6394a409758e529029f6350a40a718d429032e5250a40a798c429029d6310a409798e519025d6394640a798e419029d6390640cd545419029e6310640a758c419029e63d0240a758f40902ae62d4e40ab58b53902ba60d4
  | 5 => 0x51cca3f64543328f19150cca7a60d52329e583548cb1f5410e328f992518ca3d64946328fd91508ca3c64542328f587544ca3e60d51328f992544ca5f63551328f994544cb1d63151328f584544ca3e601513297996434cb1c5490d3297195434cb1c5450d32c7152324ca3e64145328f590514ca3e64d41328f593504ca3d65950328f586540ca3e6095032c718d540ca3f61550328f181540ca3e64150329798c540ca5d65d0c32c7553430ca5d6510c32c7550430cb1d54cc83297d95320ca9c644c832c7551320ca6f654c8328f992510ca3d64944328fd91500ca3c6454032c754c43d065f6354b419718d52d069f6350b41a718d42d069e6310b41a758c42d072d5210b4197d8d50d065c6354341ad58753d071d5314f41ab98853d06ad6214f41ad58453d06b561d4b41a7d8d52d069c6354b41a798c52d069d6314b41cb54852d06b56114b418fd9532d063c654cb418f99432d063d650cb41a798f50d069d63d4341ab98b50d06ad62d4341a7d8d50d069c635434197982539065c6054e41c794f419071d53d064197d8d509065c6354241c714d435065e63149419758c525069f6350941a718d425072c5250941a798c425069d6310941a798e415069d63905419798f505065d63d4141ad58653506af6254d41ab18953506b76154d41aed8153506b86054d41c754c53506b56194941a7d8d525069c6354941add8552506bb6054941ae181525069e6314941a758c525072d5214941ad98732506b561cc9418fd95325063c654c9418f994325063d650c941a798f505069d63d4141a7d8d505069c6354141abd8950506ac625414197982531065c6054c41c794f411071d53d04418fd95411071e5350441c754d41106776550441cd951411065f63540419718d501066e62153319b58854cc71c5450f31c755043cc63f6454b318f19152cc69f644cb31a719132cc69e640cb31a759032cc74d520cb318fd9150cc63c6454331b558754cc71d5415331b398854cc6cd6215331b558454cc6d561d4b31a7d9152cc69c6454b31a799052cc69d6414b31d354852cc6d56114b3197d9542cc65c6550b319799442cc65d6510b31a798341cc7976150731a718141cc69e64d4331a759350cc6ce62d4331b358b50cc71f4194331c750650cc69f6454331a719150cc63e60952318f181548c71e54cc631c7553318c63f64542318f191508c66f62551319b189544c67b60551319e181544c65e65d0d3197195434c71c5450d31c7550434c63e64149318f590524c69f644c931a7191324c74c524c931a7990324c69d640c931a7992314c69d648c5318f993504c63d64d4131b5586544c6cf6255131b3189544c6d76155131b6d81544c6d86055131c7550544c6d56194931a7d91524c69c6454931b5d85524c6db6054931b6181524c69e6414931a
  | 6 => 0x340aa1f69d887494a9eb2708d411420815e18c8e08bc05601413d193a7f0491148159782949c280f27129d8e004a1b58118a8a599b000021a8041688002631a419d03ea8e0778001339b1a86265250a260f680027c1ec80000000000012382c8000000391ac1700510a51bd1aa8000270001f600700024ca0b8bb22a8001ce91091d9ba0000000a09e699c8002041eb8000000001ea0669538000000000b19ed8000000018050100180300b00e01c0000a0000040000d01c06808801002034000010040000180001e00c060000000580a0010020240180801602c000030080040300600a06c01801000000020000140000000100a0000200800c000068000040142700b014000008000060200000000001800002000040000110100000700001204c0080b000014070060020040001e004000010140020040000b0080000000e002038008390000040f80301000c1080003a02401000000004028030160280c000004004018090040000180c004020028020040041800105803804000034004000080060000080200c00c000060000080180001600400005002008048100000280400100000000001010008000000040000080c00600c028000000380000000a0040080000604c0080700c0000100301000000816016000008010020040400100800805800004008030010020480080100408402002000004018020100000081300a0080000102202c008020040080000001402c020060200140280200401c1980900204000007002068000000080040f80800200c070020100000000101600c030010000000780100e05800021004000050000020a8000010060580381c004014008000060040180001801c000030140040000500202407000030060010100180800300300202c0800700800c0f80100c000020000020440080501e0580184800001c0000000001c00002004000008000000040000301803408805020014040020080000300100000000000026008008010060040000100a0100480c0020080000100200c0000101a00c0000000c0000f80601e0000400301a004010040060000a001046024038010000069d6490c438fd954310e5f6550c43a7d954310f1f6550c43a71894310e9f6150c43a71814310f1d4354843c750d5110f1d43940439798e51d0a5d639474297d8d50d0a5c63543429798e5190a5d639464297d8d5090a5c6354242975875350a5e60d4d42975845350a5e6014d428f9974350b1c53d0d42c714d4350b1c53909429798c5150a5d63145429798f5050a5d63d4142975865310a5e6094c4297d855310a5c6054c428f5964310b1d5390c42c754c4310b1d53d08428fd954210a9c6350842c754d4210a6f65508429798e5110a5d639444297d8d5010a5c63540429d98454cca756115332c715143cca3e64947328f592
  | 7 => 0x80c98f80e100000000005c1e40ea8410a00002248a3864a7691c8000001a09da9fa048a779dd1c200009780000010e1be00005f86f1fa8000000000001230000cda5293a00000010a0001a600000018c26da819198002478001bb93989f98fa31069a9b00280000015e8001a51c000012d949a88000095a1a0000000738cf0148000000000ff87690e8060000001731fc00012e9c300008a8ea0539ee0891228001c40002732418002430038c800017aa0b1259512321de89080022d88ea2f1a703d238a5403e00009491a0239299908000000000530d680000000a0002168000000ca8169f48000fb0de08700004e8fd80011012c08d0109d58399bf1d4a07289a7d00005b28d9e380019923f25f1db8000a901f8841c920a80000025d9858e9a5100000009a12b0000002a00f88f600017a284a139f18000000000180e919716b83604800025880000009104d86b03a21c24981380000000012a0000099bc87180024499199fa638b2a7490d10489f02880027708f080153239a390619f902690880020082c1e200c9d517d0000000001a90e61020000c48670c109d05e8b50001649ff99a01d0f78db0848438000000002912908b421700029692880022080000013107121d02f00000000016325609ca870d3170a4b1118369a59a78fa1b2a7b83316680001288f94e28c17f0000000090002330000001d100000000000000000020e8001e28440001652158ca002280a5aa9928ba8a19415913600004b27a08b8a802200023d89515a8000af9f003829a00f91aa7b250154909160a1e9349f08a229e95f15d8ac10b00021202a87a07287ea7c9c70f18000002290001280001c81b90000000001bc10c8a58fc0be8001cf868a9c9ef13700021f21b84183d8000ba22ea72a610e200009418b80000000016a92a8002678c68d60a680018e80005427400019999685c8000001f305e0001250000000001ce148a270d100014380020297900b1af8c88249cb9911ad18200006aa35a7600011300022f96d0000001ab1860000f307c8b600000000000000019aa700000af00da3a9cd19b20918080000021194423b1b89c180e00010f1788001740000cc80000000008a0d018e00017b8000002128000e800027192b94b14b9e80000001570000001e11352360001ab8000eb24d9b08000000878bc91e0e40000980cd24a00000000000000001b00021f8000fe80024e87d89d82500006b9200d70298000001802211078be085000000185103000000098800279a9f1828001d80002750051cda079fb03f0eba619f105215d25fa5c1f7a56a2c0002930a71d3268a670d7a1e1071408001f585095605a136a970002738a325802e9519729598881aea3516b19c0d501e85d1ad961117a5719d8000000000f58001c39069ac8f380003880d000000251a6e0
  | 8 => 0x22529a9df8000000058348000001bd93e87fa8e9550000001770000c40000000000bd28100000007223e80000007b1e5a6f1290000000b09978d901e1410e39a00001a28929d029fa8ca3c85690d9460ba9b52530000939949b40c605f242a401a31c880013f1b30000000002559e700000023000022795a22b8df00000020603288991280003c00011b27da201d19690b69b6a691582268198ac88c96203f8780422280460f027f84098114c93423e06814f05013a9738ee96605982d1a80ae2458c508b0171f88d8000012234a140cf8000001f38000001478601cc9000709889080691f98fc8918278fd21d863126a57a4f1880ec8002068130019e08000650ef96816d8000001169158e795c88113290a8d20429a1a698001e61428002011f813b9589188000e704b8000001e9a0180002400000000000004aa538229be8da92780016718f21096c800082075255030011096a5e28f0002440000001cc0000000629898920e30001d728401026b835285a1810194a0001b48799721cf0b20459c60cc14c25d045203075a93a9297d85499ea439321e90aaa950a1264a7a8dc17982b10383c9cb0901378dc95fa5e96183a83784d18417b1c99c511106ea309879fd9ae02e27916f04c0ce28d00b98d9e487e28fa6c99006e19b87895799f2658002988001a98ce9bb0f9800000000232800105a83a88a238231f290106a18b06217100004f80005b902a920c28161678a7821960065a4e08280000000000000021887700011900017f8b597c9060fe0ae8bd82a1d900000026fa160000a29d224729780000000000000015ba230000002410d380020f84020a00026a9138468fb8dd1c587300012729e0002491b21dc8cb962857a998970000608000000e298389a80025c8518d4a95a3c0002420000a18a481ba4d0e587600025216f8b79fe0b70371779849d980001529b80e8001f51b722e0448000000000b480009619516394507016598d1bfa94121a7804714d9b994707a9490ff2021358200002489391b78ab93d9f71a4a960a606c0002130f40000002590000001ca8001430000000001891099120f10ad94026b1de0088641c086c80000000009c21516e8c78bf02119282080011c2668da18705281c20d88c1b60d8a219e00a98809e50001719c68000000000b980492206d00023b8188000bb93080000013b11f920a0c8dd9ed0bf98aa8293f8fa803225a86a6e89b21988607c03b1768002481ff0f216e0001819df14e8322919db21784c91602da642891eea3824690c0001af27200020c12e1a22341261170ab0f91388d98819ec21ca4b81a00788e0ed85708585881f19e0db80015c26d27590411f27886397e14817495012c8b3a098c59380b90d283ba110de84e0c004323718a2288e19fc80011b88880000019621b1b3a851b
  | 9 => 0x19223695b0d1800000260000031826205900a800000000001330e500029d13e0f282b9418000000611dd9ef82f8c19da0001318000660000f48000000000000001e89a880022d1761a101911d00000000004f0a424c00023d02900000003100000000006fa3a0001d60001c49f41aa00011500015400000000022280025b8000001520000b822980000000824aa8b14f80007f2148c90001529ea9180ee06d93c81a9420d09469981ca14d00aa2ca6c07d1249301b1006a338000000f511e9958c09d3a8aa4609b9568b022428301c92f00010518300000016c07b8990581fd0d580000029800000019300000008323f893150a7ea048009c7a622608e489992400000013c1a69d6a102050b88002629869d0a03a820c322a0000001989d78000df9d41a385912f800067a5b22200029c0001fba6600110b847a190ed1ba849a54a37a408001f2033a452000f09dc0558cb000231a4f8e6a0e26a09e9210f717c17e81da680ec16420f0868001449e78ef17529003080010f8c382820d09e22b0b116a1fe8b305a81788380000025a000175879000155a089e180005527e0258000000000358c21c10ad00012d08d9d280000c0740000c728785d9458000e89e3169800
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x2000006003cdcca00000082d85668bc0000b4007000449472a41a380c00a000ce00a65248b600000074006e90044c784ab2c8be62928e28c0d02e3022d4cc84008a26427cc6a2980a0034c4ded6ba2432462aac1cd25a000000000086b81e0000009a5c766c00000000405818007e505e882c54c23e8caa80ae0e006400969e9c0000000000206ada66a8140016000000000036000008b07a10603a004e00000012000b0202010000020b0000010304040107040400000101010302000b0000080e2905020000a2ee2a1aa221d187050e5010e8ab88a8a1e65469c35410e32838ecaa2641960d6354842d0706a9ac429e838358d5214b41c18c629284a0d0c7254c535068c382a629a83255c66314941a18e6a90a4a0d2870548525061c382ca19283435c85450f31c1ac8a906598e0d5458854cc706b22a429663431c95410d31a30e0aa08698e0c64149324c686392a82a263461c1541513192ae3320a498d0c74548524c6a4382a429263161c16510931a30e0a08a098f11414c55008790a0a42a8043d04c52154021a2ae329a83a060c639494290287396a729c81439cf5294a40c1ac6a908420651511813110306a9ac4298818554d6114c40934e1b1aa42060d635485210312a92c2290810d5c4654c840930e0b1ca220631511813110388a8ec09888185544604c440e22a2302622069251181311030ca88c098881a4544604c440c22a230262204987058e211030ab1aa310881455c6544c730a1ce5aa0871860c64949328c287396a92a461439d35294a30a1ae42a2861851571151430c306b22a4190618c5446050430c1aa8b10a81861554584540c24d386c8a9061835915214830c8aa4b08a41845571195420c24c382c928861945446050430e22a3b02821861551181410c388a88c0a0861a49446050430c32a2302821869151181410c308a88c0a0861261c16488430c2ac8a8c421861561544400c28ab8ca6a0e418694c6050720a2ae32a2639061a5418131c83882888018241a81844048020d80c2182401061853181418430c2a0c098c2185d4d6110210c2ea8b0861084e276c85208430c298c0a0a218a1486050510a28eaa0a62886146550531443822928298a21641c1414c510c30a83026288648521813144348a08c098a218554d6110010c4aa4b088008615545843004322a92c218021465d4400c010c32ca20060087095210030042c8b888018021a4584400c010
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x400000089004800538cc01403a108058d5188440a10805915188430a118194c6050720a1181950604c720d00521c1414c510e0052504604c510c11655c4400c010d01525c4400c010c1175584400c010e0152584400c010
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 48
  | 5 => 1017
  | 4 => 1345
  | 3 => 112
  | 2 => 10
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s1K7 (i*5) 5
  | 6 => packedAt s1K6 (i*16) 16
  | 5 => packedAt s1K5 (i*27) 27
  | 4 => packedAt s1K4 (i*38) 38
  | 3 => packedAt s1K3 (i*49) 49
  | 2 => packedAt s1K2 (i*60) 60
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s1K7 (6+((h/1+packedAt s1K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s1K6 (864+((h/16+packedAt s1K6 (768+(h % 16)*6) 6) % 58)*7) 7
  | 5 => packedAt s1K5 (31188+((h/339+packedAt s1K5 (27459+(h % 339)*11) 11) % 1221)*11) 11
  | 4 => packedAt s1K4 (56038+((h/448+packedAt s1K4 (51110+(h % 448)*11) 11) % 1776)*12) 12
  | 3 => packedAt s1K3 (5784+((h/37+packedAt s1K3 (5488+(h % 37)*8) 8) % 162)*8) 8
  | 2 => packedAt s1K2 (615+((h/3+packedAt s1K2 (600+(h % 3)*5) 5) % 17)*5) 5
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffff81ffff83f07ffff83ffc1ffc0fcf9f3f3
  | 2 => 0xf07fffe0fffffff81f07fc3ffe1fffff463c7f
  | 3 => 0xff81ffff03ffc3ffe007ffc3ffe1ff0387cf9c
  | 4 => 0x1fffffc0003fffff80003fffe0003f80fe0
  | 5 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x210c08c42890400165098044c022425818d1b1
  | 2 => 0x44109102412221280a422429121494a1422446
  | 3 => 0xa22522481a440652a084ca8265412a0a854a98
  | 4 => 0xcb59c4929076ab9cd3d06223b9980c33e80f60
  | 5 => 0xc61871ce38733e71ce77330311030c3f7b000
  | _ => 0
def s1Atlas : Atlas := ⟨7,rawDecor 61 s1Pos s1Neg, 0xfaaafaa0faa0f0a0faaafaa0faa0f0a0faaafaa0faa0f0a0faaafaa0faa0f0a0faaafaa0faa0f0a0faaafaa0faa0f0a0faaafaa0faa0f0a0faaafaa0faa0f0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37183
namespace PEqualNP.Outside.L_meta_37183
open PEqualNP.Outside.L_meta_37183.Model
def s2K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K6 : Nat → Nat
  | 0 => 0x1a704243c580005080014001c0002a980023a24022002c000000001f5aa40061c8c999006c52a183d0805c0000056101925e60d2c4a44027025c8000a001400000000002c048002800c00ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31df31fe31fd31dd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30de30fd30fc30dc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x617e510c2faa2186fd0430dea0861df310c3bc6218774c430ee188617e500c37c80186f10030ef98061fa300c3ba60187e4c030efaa061de540c3baa8187715030efa9061de520c3baa4187714830efa1061de420c3ba84187710830efa8861de510c3baa2185754430ee28861df410c33e82187790430eea08619d410c3b8821877c8430ef10861dd210c3b842187794030af28061da500c3be80187790030cf20061dd400c3b880186710030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c83bca7905794f20bea9e41dd53c82baa7905f14f20bf28e417d51c837e83906f50720ef98e41dd31c83de43907b48720df20641bc40c83bc6190770c320bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3106fd0620dea0c41df31883ba63107b88620f610c417e508837c81106f10220ef18441dc30883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20bfa8a41f751482eea2905f14520fa28a4174514837e82906f50520ef98a41dd31483de42907b48520df20241bc40483bc6090770c120fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20bea98417c53082fca4105f94420bea8841bf410837a821077cc420ee98841ee21083d842105f94020df20041bc40083bc6010770c020f790041fa20083da40107e48020bfaa6217e54c437ca9884f95310beaa621bd54c427aa9885f15310bfa9e217e53c43bca7885794f10bea9e21dd53c42baa7885f14f10bfa96217e52c42faa5885f14b10dfa0e21bd41c43be6388774c710df20621bc40c43bc6188770c310bfaa421bf548427ea9085f95210beaa4217c5484378a9084f15210bfa9c21df53842bea7085f94e10bea9c217c53843b8a7085714e10bfa94217e52842faa5085f14a10bea8c21bf418437a830877cc610ee98c21f721843e843085f94210df20421bc40843bc6108770c210fd10421f920843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910dfa0a21bd41443be6288774c510df20221bc40443bc6088770c110fd10221f920443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf28821bf410437a820877cc410ee98821f721043e842085f94010df20021bc40043bc6008770c010fb88021fa10043ea20087e44010
  | 1 => 0x721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21dfa0a43bd41487be6290f74c521fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf290437e510877e8210ef50421ef98843dd31087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e81de53d02bca7a05f54f40eea9e815d53d02fca5a05f54b40bf28e817d51d037e83a06f50740ef98e81dd31d02faa9205f94e40bea9c81bf439037c87206f50e40de21c817e52902faa5206fd0a40df21481bd429037885205f94640bea8c81bf419037c83206f50640de20c81df31903ba63205f94240dfa0481fb409037ea7206f94e40dea9c81bc539037ea5206f94a40dea9481bc529037e65206f8ca40de99481bc329037ea3206f94640dea8c813d5190378a3206fcc640cf98c81be319037a6320674c640de18c81bf219037c43206f48640de10c813e50902fea6a077d4d40afa9a817c53503b8a6a05714d40bfa92817c52502fea2a05f14540dfa0a81bd41503be62a0774c540fda0281be40502fca8205f94c40bea9881bf431037c86206f50c40de218817e52102faa4206fd0840df21081bd421037884205f94440bea8881bf411037c82206f50440de20881df31103ba62205f94040dfa0081fa401037a80207e50040dfa9881be531037aa6206f14c40dfa9081be521037aa4206f14840df99081be321037a64206f0c840dfa8881be511037aa2204f54440de28881bf311033e62206f8c440de988819d311037862206fc8440df10881bd211037842206f940409f28081ba50102fea9985f95330df2a6613e54cc2faa9986f553309eaa6617c54cc2fca5985f54b30bf28e617d51cc37e83986f50730ef98e61dd31cc37c81986f10330bfaa4617e548c2faa9185f15230bea9c61df438c3bc87187750e30ee21c617e528c2faa51877cca30ef19461dd328c3b865185f94630bea8c61bf418c37a831877cc630ef18c61dd318c3b863185f94230df20461bc408c3be61187ecc230efaa461de548c3baa9187715230efa9461de528c3baa5187714a30efa1461de428c3ba85187710a30efa8c61de518c3baa3185754630ee28c61df418c33e83187790630eea0c619d418c3b8831877c8630ef10c61dd218c3b843185794230efa0461de408c33c81187750230ee204619c408c2fea8986fd51309faa2617e544c2faa8985f15130de2a2613c544c2fea4985f14930bfa8a617c514c37e82986f50530ef98a61dd314c37c80986f10130fd98261de304c2fea8185f95030beaa0617c540c2fca61877d0c30ef21861dd430c3b886185f94830bea9061df320c3bc6418774c830ee19
  | 2 => 0xcbbe65197bcca32bf28c657d518cafca1195f54232bfaa265bf544ca7ea8995f95132beaa2657c544cb78a8994f15132ef21a65dd434cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf29865df430cbb886195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef90f41dea1e83bc43d06fca5a0df54b41dfa1683be42d077a85a0ef10b41bf286837d50d077ea7a0ef94f41dea9e83bc53d077ea5a0ef94b41dea9683bc52d077e65a0ef8cb41de99683bc32d077ea1a0ef943419f28683bd50d0778a1a0df552419eaa4837e53907bca720d794e41bea9c83dd53906baa720df94a41bea94837e519077e8320fdd0641bf284837d50906fea6a0df14d41dfa1a83be435077a86a0ef10d41bfa92837c525077e84a0ef90941dea1283bc42507ee82a0ef90541bfa82837c505077ea6a0ef94d41dea9a83bc535077ea4a0ef94941dea9283bc525077e64a0ef8c941de99283bc325077ea2a0edd4541dfa8283be505077aa0a0ef141419e282837e541067ca820df94c41ef298835e53106faa620f754c41aea98837e52106faa420df94441dfa0883f6411077a8220fd50441bf280837d50106fea998df95331beaa6637c54cc7be8798f790f31eea1e63dc43cc6fca598df54b31ef99663de32cc7ba6598f70cb31dfa0e63bd41cc6fca198df54331efaa663de54cc7baa998f715331efa9663de52cc7baa598f714b31efa1663de42cc7ba8598f710b31efa0e639f41cc7bc8398f750731cea0e63dc41cc7bea198f794331af28663dd50cc7b8a198dfd5231bf2a463be548c67ca918df55231deaa4633d548c6f8a918df54e31aea9c637e528c6faa518df94631dfa0c63bd418c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c7be8698f790d31eea1a63dc434c6fea498df14931ef99263de324c7ba6498f70c931dfa0a63bd414c7ee6298f78c531bfa82637c504c7bea898f795131eeaa263dc544c7bea498f794931eea9263dc524c7be8498f790931eea1263dc424c7bea298f5d4531efa0a639f414c7bc8298f750531cea0a63dc414c7bea098f794131eea8263dc504c6b8a098dfd5031bf2a063be540c67ca818df55031deaa0633d540c6f8a818df94c31af298637e520c6faa418df94431dfa0863bd410c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21dfa0e43bd41c87be6390f74c721bf286437d50c86fea910df95221df2a4433e54886faa910ef552219eaa4437c54886fea710df94e21ef29c435e53886faa710f754e21aea9c437c53886faa510df94621dfa0c43bd41887be6310f74c621f790c43f
  | 3 => 0x3d2e00039a00188346000000000000008711c800378000000bf24a56c002f0000560000001a60017a3520baa3919b74652000003ab296001039860d44980021a07e000c2a06000e1c2a2da5960019035d46c6953b84777cacdd884156823453869000ce8672981565f1e20b3000030012ff730cf40038b3340000b844426844003020000c800000358001dc2e71300016f0d444680c5baaf578000002ed7468e998bcd0003e0003281f6001818cc4d600000367000000018000002887a9693fe52930800000000008000000020080300300002401800006058008010000040380e0000500a80200a0580081b00001000000014024018130100080080303c00403001004008090010000000000500202800000018000020000060041300a0000000080000400802000000088060000020180000d0380000080b0160000080001200c0400400203c00803014004008000000140500201600c03000018024000010000340000002a038000010100040080100400c0180d016010030000000040000100000804802000000018000160280080a0060000600101800002003002000000000000000080004c000038070000140300800a00c0100000201c0080d00c0040000000400003007000000068170000500681b00004c0080100003c0000200603c0480100a004000120020a40001900c000028000000100800000e02800816010010020000000001700800000000000000008050020000000000200004c0000600200c08801000008070000000000300d00200c0000801001801000012000008010040180280100202c000000040000080000600c030140000100000400a00803000000000000030040200180200a0140281c0000080000200a004018000080080a80000e004008100040180100000202c0180001c000025f94b43bea96877e51d0efaa3a1df94343bea86877d5490efca721efd0e43efa1c877e5290efaa521df94643bea8c877e5090efaa121f7d0d43df21a877f5250ef8a4a1dfd4543be28a877f5050ef8a0a1df95043bf29887bf4310fbc8621ef50c43eea18879d4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857e5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a85df5350abea6a15f14d42ee29a855c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42ef298855e5310afaa6217754c42aea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa71977d0e32ee21c657e528
  | 4 => 0xc000000004ece847ba7b632f99bc80054e000001bb0c04bd3e1ce3c29a9ed1a03609fc0014c22000077b5e6c6dd40028f000001399f4390db800278540918002e86e6a2ca49a8094c9815000738b59bf90457c000002022de001b00001e2e553a99570c318021d3000000000003140000000000055dc529a000425008c2120a1c5f26f7a6a208b80076e6a4002120008fc00000000b00000000003a1e4a2d3ca1901e192000000549db320a5d519d50007295eac74181f8b516820e001788003dc685412940000015214600000000000000000bc000074001252171b60000039b4be001f037238ab70000000000000000000000133800226765a8bad62c00095068000000f78000003100000053200088b182b296474a1941c47c0e0de0f8000a72fd08687dd30000566446bb3f6cc96c0884b000ecd9ab851c8f91e33a8764000bd8000000010d8001cc1389d0e200000169a0972e2bc000ea6361f40008622a3d173000000000f43645c8690000a4718000001643848a40033800000000356000990d9000196000001082161d8a200000000185800000000001ba26ac5c000000688555b1180328c41395e7e8000000ec0000000016c1aabf9462370001e44780076a000000006960007197324449c00198000fb97639d000360532c30acc74770a57de0b52c1707403c0a413f6a68416492326e2056bbd65721dc8734728ada0daa472e42144a3cf2c0001a12b7000001e89610006203d800000ec000000000dc0001f90001d141a2a61408da18fd09e508692160e42eca6800000500508006f09005a365118f14c780069a04c79ba7356281171d72a40996f9e630693c6cac4000c502d99600033c0018c070000003ba02a00000000786000000002a87ec00020610a354e2bb724000c70c7000000dbac206226de10001c020035af87e4c444e19f2a03ade90b858ca003994173c000800c35d2d50003825c2b897d80000089805036678000f88e5000b3df687a23a55400000000000f5000000db0000006080000012b5a800156000440ee41e8510000002e06c000000000000000000024c000000d69fd000a597b00043afac1100066600032a0f000001db25e5263e4f4b9f33a001d291e00023800000000774448001ec000001637bc0000000021e001bbb99658000581307ecb1412800258b44001a3000c945932a63ecbcad14f75272c000001da000003c7000000003db000484970080c6374c0aad0e0000001f3000fc1108006c20000035c00000030a2749a4a0368007a0000920000000000005843c0000030f232e3d390b900a5b9222381627599a28100027c8d2c103e70de43aa4e2d68b68006b0001f9a414864c8563bf55022000000708b28000004ca000ec04d2ba5ac488ae00000000000478000552a66460d4243d547ab6dc71d14a27
  | 5 => 0x1a2d544a8004d8db40000033ca40003dc3d6000b885f0c4001b880000092df198725a57cfaa9f2b8ac0418334aae8989ad92407c80031c000000000000004049e800270001bf270000000001023c6ce5af800000d385401000065df3ba41900c0ef1fe37a37cdf82e2f2a85f10c055cc00439af444a14fc0cd6aef2c6e37c5f20748b114312eb01f05e5445d4b11c95ca0015f91c52a048001d4698ba856acd5dcc25a0000688e0c6818d476a495ab214ae815f2a3e7349a12b200490f30519e000077c000b500016482bae7e2000ce09e35454cb2a79574b8134b896d4894179e436c000000005d6b3197000000000002b2000000e0b125f4df4b301e60251cee0842528d59130c41a00000000000701ef99927206944b8d43046c0004900000000000000000002ef00094800000000000c98e10b4b60000005f80005e2e30fe154ab2b17ea000000000007c1a78ca634000d10000008200017f0007f115bea36200000286000000e3057000000290140000008527d4fc6000030d000000000c1000cd9191da3ee00000000036000bebce00079c000001ac00006a5a0008bc000004a6da5a5000000c543c0390581980032d60a0004e80005200000349132fb0002627ee001c0a910004ec000003883c80010c06e001282d5000730d3151304f749b0e721a000001be48a0015c0536767485b0002e86d1053e80846e5a2bc02fc001d7800000000228716a00383780027c3f014009000000000217b2000000004a80013a09a2621b983b6b0005d9ad8002f4001bd2424929b9e51ec53601805af2048cf8d993c458e51c800053c3f94e88a77a25c203bc0000000037b000001549d07a898d1a1c77222480c25d000001799842ce938fd0c50000000008b7f02096eb0e000e21e08c9554f5cf1000174d880b0ff5ea9805eb2b01ee01021a700062d14000000dd800327000001cb177000cdc002d00004482826d2061303a8da3709e803800286b480000007600000000776f8400133590e4c9a00000000152a0b428000499ae660004002ab0000000006708c001da0006de00000000000890fb000690001ec3595140004b19b000000f68fa4ccd04ca324460c79423e959c001990005ee4180000060
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xc40842b56110210c7d52308431c548c210b5586308431f540c210c715030842d5610c210f808620842f06148210f8c85208423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544423e60151108f180544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c7150534425e6014d1097180534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109dd85524426e6514910cbd50524432c5414910d3d4c524434c5314910da580524423e65d0510c7d4f414431c53d0510cbd4b414432c52d0510ae983414423c6550510c7d4d414431c5350510cbd49414432c5250510ae181414425e65cc510c7d53314431c54cc510d3d4b314434c52cc510b6983314425c654c510c7d51314431c544c510d3d49314434c524c510e550531442d8604c5108f996404431f5390110c714e404432f5290110cb14a404423e6510110c7d4c404431c5310110cbd48404432c521011097996304431f548c110c7152304434f528c110d314a304425e650c110c7d50304431c540c110d3d48304434c520c110da14a20442786548110d914a104425e63d50109758f540426e62d50109b58b540423d65950108fd85540423d61550108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c1097d85530425d6154c108f990530423d6414c109798c530426e6214c109b588530423e64d48108f593520425e63d48109758f520426d6594810cb952520432d5494810d394e520434d5394810cb951520432d5454810d394d520434d5354810d9185520423e64148108f590520425e63148109758c520426e62148109e980520423e64944108f592510425e63944109758e510423d65d0410c794f410431d53d0410cb94b410432d52d04108fd95410431e5350410c754d410432e5250410cb549410425d65cc410c7953310431d54cc410d394b310434d52cc41097d95310431e544c410c7551310434e524c410d3549310436552c84109d594210423f65900108f596400431e5390010c754e400432e5290010cb54a40042b561900108fd94400423d6510010c794c400431d5310010cb948400432d5210010ad584400425f658c01097596300431e548c010c7552300434e528c010d354a30042d5618c01097d94300425d650c010c7950300431d540c010d3948300434d520c010b55843004398400c0109e596100436952840109dd9510042e462440109ed9510043695244010
  | 1 => 0x8398400c2208f587544823e64951209798e544825d63951209d9865448275619512097d8d544825c63551209dd85544827461551208f994544823d6115120c7d53534831c54d4d2097587534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209dd8553482746154d2097994534831f5414d20c7150534825d6114d20cdd53514833454d4520d5d4f514835453d4520cdd93514833464d4520d5d8f514835463d45208f990514823d64145209798c514825d6314520cdd5051483345414520d5d4c51483545314520cd99051483356414520d598c51483556314520dc580514823e65d05208f197414831f53d0520c714f414833751d0520cd147414823e65505208f195414831f5350520c714d41483375150520cd145414825e65cc52097197314831f54cc520c7153314835751cc520d5147314825e654c52097195314831f544c520c71513148357514c520d5145314826e65c8520d9147214836451485208f996404831f5390120c714e40483375190120cd146404823e6510120c7d4c404831c5310120cdd444048334511012097996304831f548c120c71523048357518c120d5146304825e650c120c7d50304831c540c120d5d443048354510c120e61003048364518812097d8d540825c63550209798c540825d63150209d984540827561150208fd91530823c6454c208f990530823d6414c209d98453082756114c208f992520823d64948209798e520825d63948208f992510823d64944209798e510825d6394420cd94541083355150420ae1814108356514c420d554531082d8604c4209b59621082e960084209bd9520082e46148020ea10120083c830480209ed95200825e63d53109758f54c425e63153109758c54c423e64d4f108f59353c431e5494f10c755253c431e5454f10c755153c423e6414f108f59053c423e64d4b108f59352c425e63d4b109758f52c423e6414b108f59052c425e6314b109758c52c431e53d0710c754f41c431e5350710c754d41c431e54cc710c755331c431e544c710c755131c4395414c710c794e40c431d5390310c794c40c431d5310310c795230c431d548c310c795030c431d540c310e610030c433561d5210ce983548425e63952109758e548425f63552109718d54843356115210ce980548431f54d4e10c7153538435561d4e10d6983538423e6494e108f592538423f6454e108f191538431f5414e10c715053843556114e10d6980538423e6494a108f592528425e6394a109758e528423f6454a108f191528425f6354a109718d528431f53d0610c714f41842ba60d0610c7d4d418431c5350610ae181418431f54cc610c715331842da60cc610c7d51318431c544c610b618131842f16008610c7d4e408431c5390210ad586408431f5310210c714
  | 2 => 0x605063097994418c25d651063097996218c25d6588630a7992218c29d648863097994218c25d6508630a7990218c29d6408630b6980218c2d96008630a7586408c31d5190230a7584408c31d5110230e6980408c23d61d51308f992544c25d639513097d8d544c23e65151308f584544c23e64145308f590514c23e65d05308f197414c23e65505308f195414c25e65cc530c7d53314c31c54cc530c7d51314c31c544c530d5d45314c23e65901308f994404c31f548c130c7152304c26e62150309b588540c27661150309d584540c23e6494c308f592530c25d6590c30c7151430c25d6510c30c7550430c23f64548308f191520c29f644c830a7191320c29e640c830a7590320c34d520c8308f992510c23d6494430cd945410c3355150430ae181410c35551cc43097596310c29e648c430a7592310c29e640c430a7590310c29e64cc030a7593300c25f654c030a7d91300c29c644c0309ed95300c2da60d5030c7550540c2ce6215030b3588540c2d66115030b5584540c2da6015030b6983520c29f6454830a7191520c29e6414830a7590520c34d5214830b5984520c2d56114830b6980520c2da6090830b6582420c25f655083097195420c25e651083097594420c2da60d4430a7992510c29d6494430a7990510c29d6414430b3988510c2cd6214430b6980510c31d51d0430a7983410c25e659043097596410c29d6490430d5546410c3555150430b6d81410c2d86050430e5d85410c3965150430c7545410c3955150430c5545410c39b6050430a7181410c3986050430a6181410c25e651043097594410c29e641043097996210c25d6588430a7992210c29d6488430d5546210c3555148430b6d81210c2d8604843097994210c25d6508430a7990210c29d6408430b6980210c2d96008430c7d06500c31d4194030d6982500c39b4194030e6506500c25d65d0030a7586400c31d5190030a7982400c31e5090030e6942400c25f6550030a7584400c31d5110030a7980400c39a6010030c7940400c39a50100309798f54c825d63d53208f58654c823f61553209798c54c825d63153208f99353c823d64d4f20c795253c831d5494f209758653c831e5454f20c755153c825f6154f208f99053c823d6414f208f99251c823d64947209798e51c825d63947208fd9741c823d65d0720c794f41c831d53d07208fd9541c823d6550720c794d41c831d5350720ae18141c825f65cc7209759731c831e54cc720c755331c825f654c7209759531c831e544c720c755131c82d8604c720c794e40c831d5390320c794c40c831d5310320c795230c831d548c320c795030c831d540c3209798f548825d63d52209798e548825d63952208f993538823d64d4e208f992538823d6494e208f992518823d64946209798e518825d6394620ba580218
  | 3 => 0xe40c7d4e53902ba6014e40a798f529029d63d4a40ae983529029e6394a40a758e529032f5294a40ae980529023f654ca408f195329023e650ca408f59432902ba60d4640a798e519029d6394640a798c519029d6314640ab98851902ad6214640ae980519031d51cc640a7983319023e658c6408f5963190397614c640c7545319029c604c6408f994319023d650c6408f996219023d6588640a798e219029d63886408f994219023d6508640a798c219029d6308640ae98021902b9600864097587535025d6114d409798c515025d63145408f997415031f53d0540c714f415031f5350540c714d4150337515054097997315025c65cc54097995315025c654c540c7d4e405031c5390140c754c431025f63548409718d521029f6350840a718d421029e6310840a758c421032d52108409798e511025d6394440cd547411023d6590440a798e411029d6390440a798c411029d6310440d59453110355514c440b6181311029e63d0040a758f401023f6550040a7d8d401029c63500409ed9540102ba60d4c40c754c53102ae6214c40ab58853102b66114c40ad58453102ba6014c40ae983521029f6354840a718d521029e6314840a758c521032d5214840ad98452102b56114840ae98052102ba608c840ae582321023f654c8408f195321023e650c8408f59432102ba60d4440a798e511029d6394440a798c511029d6314440ab98851102ad6214440ae980511031d51cc440a7983311023e658c4408f596311029d638c440cd5463110335514c440aed8131102b8604c440e5d853110396514c440c75453110395514c440c5545311039b604c440a71813110398604c440a6181311023e650c4408f594311029e630c4408f996211023d6588440a798e211029d6388440cd54621103355148440aed8121102b860484408f994211023d6508440a798c211029d6308440ae98021102b96008440c7cc6501031d3194040ce982501039b3194040e64c6501023d61953308fd8554cc23e64947308f59251cc23f65d07308f59741cc23f65507308f59541cc2b86050730c795331cc31d54cc730d554731cc31e544c730c755131cc26e62d52309b58b548c31e5450e30c7d50438c23e6494a308f592528c29f644ca30a7191328c34e524ca30a7990328c29d640ca308f992518c23d6494630a7992318c29d648c630d5545318c29e640c630a7590318c29e64cc230a7593308c2ce62d5230b358b548c2da60d5230c7d52548c2da6015230a7993528c29d64d4a30b6983528c29e6494a30a7592528c34f5294a30b6980528c25f6550a3097195428c25e6510a3097594428c2da60d4630a7992518c29d6494630a7990518c29d6414630b3988518c2cd6214630b6980518c31d51d0630a7983418c25e659063097596418c3976150630c7545418c29c
  | 4 => 0x7590524c74d5214931b5987424c6d561d093197d95424c65c655093197994424c65d6510931e5d47414c69e60d053197996414c69d6490531e5d85414c7975150531a7181414c65e6510531a7990414c69e64d4131a7593504c69f6454131a7191504c6cf6254131b3189504c71f4114131c7504504c65e63d50318f596540c63e60950318f181540c63e64150319798c540c63e64944318f592510c63d65d0431c794f410c63f6550431c794d410c71e54cc431c7553310c65f654c431c7951310c71d544c4319dd95310c756534c4318fd91500c63c645403197d8d54c865c63553219798c54c865d63153218fd9153c863c6454f218f99053c863d6414f21e550531c863f64543218f19150c865f63543219718d50c865e63d52219758f548863e60952218f181548865e63152219758c548863e64d4e218f593538871e5494e21c7552538865e6094e21c7951538871d5454e2197181538863e6414e218f590538871e53d0621c754f418871e5350621c754d418871e54cc621c7553318871e544c621c7551318863f64542218f191508865f63542219718d508865f63551219718d544867b60551219e181544865e63151219758c544863f6454d218f191534867b6054d219e181534863e6414d218f590534863e64d41218f593504865e63d41219758f504865e63d50219758f540867a60d50219e583540863d65950218f982540863c60550218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c2197982530871e5454c21c7551530865c6054c218f990530863d6414c219798c530867a6014c219e580530863e64944218f592510865e63944219758e510863d65d0421c794f410871d53d04218fd95410871e5350421c754d410865d65cc421c7953310871d54cc42197d95310871e544c421c75513108795414c4219bd9521087a54148421f14c521086776548421ce95250087395494021d694e50087595394021ced9250087386494021d6d8e50087586394021ced0650087394194021d6cc6500875931940218fd91500863c645402197d8d500865c6354021ce95150087395454021d694d50087595354021ced9150087386454021d6d8d50087586354021ced0550087394154021d6cc550087593154021dac85500876921540219758653d025f6154f409798e51d025d6394740c794f41d031d53d0740cd54741d031e5350740c754d41d025f65cc7409759731d025f654c7409759531d02d8604c740c794d439025e6394a409758e529029f6350a40a718d429032e5250a40a798c429029d6310a409798e519025d6394640a798e419029d6390640cd545419029e6310640a758c419029e63d0240a758f40902ae62d4e40ab58b53902ba60d4
  | 5 => 0x51cca3f64543328f19150cca7a60d52329e583548cb1f5410e328f992518ca3d64946328fd91508ca3c64542328f587544ca3e60d51328f992544ca5f63551328f994544cb1d63151328f584544ca3e601513297996434cb1c5490d3297195434cb1c5450d32c7152324ca3e64145328f590514ca3e64d41328f593504ca3d65950328f586540ca3e6095032c718d540ca3f61550328f181540ca3e64150329798c540ca5d65d0c32c7553430ca5d6510c32c7550430cb1d54cc83297d95320ca9c644c832c7551320ca6f654c8328f992510ca3d64944328fd91500ca3c6454032c754c43d065f6354b419718d52d069f6350b41a718d42d069e6310b41a758c42d072d5210b4197d8d50d065c6354341ad58753d071d5314f41ab98853d06ad6214f41ad58453d06b561d4b41a7d8d52d069c6354b41a798c52d069d6314b41cb54852d06b56114b418fd9532d063c654cb418f99432d063d650cb41a798f50d069d63d4341ab98b50d06ad62d4341a7d8d50d069c635434197982539065c6054e41c794f419071d53d064197d8d509065c6354241c714d435065e63149419758c525069f6350941a718d425072c5250941a798c425069d6310941a798e415069d63905419798f505065d63d4141ad58653506af6254d41ab18953506b76154d41aed8153506b86054d41c754c53506b56194941a7d8d525069c6354941add8552506bb6054941ae181525069e6314941a758c525072d5214941ad98732506b561cc9418fd95325063c654c9418f994325063d650c941a798f505069d63d4141a7d8d505069c6354141abd8950506ac625414197982531065c6054c41c794f411071d53d04418fd95411071e5350441c754d41106776550441cd951411065f63540419718d501066e62153319b58854cc71c5450f31c755043cc63f6454b318f19152cc69f644cb31a719132cc69e640cb31a759032cc74d520cb318fd9150cc63c6454331b558754cc71d5415331b398854cc6cd6215331b558454cc6d561d4b31a7d9152cc69c6454b31a799052cc69d6414b31d354852cc6d56114b3197d9542cc65c6550b319799442cc65d6510b31a798341cc7976150731a718141cc69e64d4331a759350cc6ce62d4331b358b50cc71f4194331c750650cc69f6454331a719150cc63e60952318f181548c71e54cc631c7553318c63f64542318f191508c66f62551319b189544c67b60551319e181544c65e65d0d3197195434c71c5450d31c7550434c63e64149318f590524c69f644c931a7191324c74c524c931a7990324c69d640c931a7992314c69d648c5318f993504c63d64d4131b5586544c6cf6255131b3189544c6d76155131b6d81544c6d86055131c7550544c6d56194931a7d91524c69c6454931b5d85524c6db6054931b6181524c69e6414931a
  | 6 => 0xf700014b80001381d098981a82096a8e00017019419b2592729951e18a884e23b1729fe876a859b4016a9a9349cd1fa19580016785a08596da1382486a9998db9e2000a072831dc83f1b500004d00003a8001a40000000000000001260750001968c717080027a09028f0ef13107400015584209702180000016491f1bc161a1b80d81e12b0000001128001530000000002559570002468521d2a0024b86f9db12c16980000c0120003c8070000340a00001400405800000000000150020201e80500a020000080060480c80003403400004006004000340200200880001c0000000201a0100082d002000010010060040501a0060180180d00200c00007030004008000000400000a00a008000290020380a0010420cc060000000100000f01603c048040360bc058140000000604b00e0180400003602c0880000000c0080e0040000700d0160000f00200400001804020008010020140400600900c030030050080440e00200002c0000000e058028210020180100100c034090120020100f00c0000200500600a0100c000002038338020000340280200a0080200000a004000000060040b007002000068010020040402402c0080701b01c0080b0100020002600a01a00c0000d00005c0080000802400021008000000000460040700300800c0c00202a0480100400600c03801002008000020040000180107c01c038000020740181d0040340081201009800005030000000150020400680d00c00c0080100001404006004000090010000e00180300407c06811010004008000040300180f004028030010220640200e00202c0100a0000000000200000c0380107a0e8008000260041a00002404c000020020000c001016010008020060000b8040120240480401a0440380807200c0081200400c0580000000008004014018028070000040900a0000040600001c01002009056000020140000a8008070000080b80d00c0080000f0040000000001c0140000f0040001080100004c0281102200c0080001601c0001600e07802800010008018010060000080b0080900000b00200401000000070000010420069d6490c438fd954310e5f6550c43a7d954310f1f6550c43a71894310e9f6150c43a71814310f1d4354843c750d5110f1d43940439798e51d0a5d639474297d8d50d0a5c63543429798e5190a5d639464297d8d5090a5c6354242975875350a5e60d4d42975845350a5e6014d428f9974350b1c53d0d42c714d4350b1c53909429798c5150a5d63145429798f5050a5d63d4142975865310a5e6094c4297d855310a5c6054c428f5964310b1d5390c42c754c4310b1d53d08428fd954210a9c6350842c754d4210a6f65508429798e5110a5d639444297d8d5010a5c63540429d98454cca756115332c715143cca3e64947328f592
  | 7 => 0x324f1cca529e017d83980009e8000002288d6a6b29c8001658dfa2c1f41050470aa00006b80000000018280012a800000023228270245a271d80000000000200000001328d39cb19a25b2368e300003600000118b203a81a662750002120a58000000d09a30002010e09d080007c9bc91300007a80018a2560c20d18000000b300014628114925314d9f8a689d126d113a8b9f484898d29e98e0cd1b08e224a0e39c283896b9408d88000a68b70038baa4196295a93595da9b8002298000d01269bb08e9441070778191b79ad97a10fa358ef90297123a0ed8000af247975a6ba5480014725f8f0a7e8f903b8298d79398990208e813ea2a8222411aa8922949b81f214b07b00027624816a1239bf0d30a706491c1eb1fe23e80026213300009d974034a11a14a2f80e0000d80000620d600017b90b1cf9650fb1e30eaa3e2578180ae1b3269044227a9780c9c505f11e8000b68c00000001a60099d22789178001cd8001101a026481f20e11410d9920641088238c886018aa1a1de1a90ab1c4168850a32280a1f1e124e10d0bda130be86d25f26f04d84c1270a498992092201589b0daa9304f058a8416929c0b500b8b417210921b1820bc89f2919769b198c87e0e181b1fca191e72550e900024fa26a0c93f0000a18000698701199f900000021e8d28001248000001810e4a2b09ba6d92fa6c05486e25a05ba8294390f22b9fa8000571578c416810319e8000aa8001f39308000c80f98808a10481c22801880910001c01c300aa169d79ed9a689501d9d68002420000002748000000cf800173037192a0d81225000008891680016a8000000001322580000c900008b1511be266a24a078b380817793a21c2209910a21fc20423a80d1c1a171be91f9f711b94113b201a891948bf26aa7d00014a158a7c8f48dc8c591516b01c0c627da0d03421596619d8418c10828c09ee15b0002710000818de84ba408a78100958df1739009ce01600021e00001309c800000290830000116000000000000000197a9a1ac00000011c89d0002258001a5141a8500018f9d41d98369c7a7912b91114284a9bd80025ca32a879ab87d8000e2a898490e885a94e87590a9a39ea8000b9a1a9ae0000000ec9b49b39af0c30998821e9a6a1a280f0110291fb8000841bf85585500013d0000e70540189538ed1048718681c0a2127796c05c9038d40ce09a0c49d525884609e07102e28605b19e00199f20b1098ec28d1eb8f69f09ca80012a16081a28a12d24888a99f83921000008781f80003e8452758ff808a1422d2440e400007f83d1c116f15e8002060ad0f10f01a98000001f80560cc87800026f8000002051919da862a3d95094880c0e006c9f7a8c14300000029980028492588a0001e813c1b71ef9318000be03287ba6e27091d80019009483c9c68000
  | 8 => 0x1a18fe00007f08525196685393a88486a0a41620002618eb80200014c1ef0000000000001a20000a605d80000000019ca6c9de96e9189fd8bb18524317c8f817e21824722515c0ca1e794598304a05c1200000da0d115023808325c293a95a311808f20bd086861a2d892963a7f12189788806f05e1600251ff87e8339a71cf0728db27e017042a610001ac8002348000000fc00000024513700000004780000015920993b80a24c16c93d9ba1d70ce800155216007800079a0498582f8002650b213e279827a0b83e28d8e6800049a0e8050000e5800000000000107a4d99329114c9f01719868e60c983a15b95f0001b10001e90eb27206c1000a285300618f0511d49b62260001df000012a739c928680000023980029f0000001d1a508002718a922300018b8001bd0b129d105831a83a882940c69db8d58468b88dc0000b090409a8000000000b782402d9f11ad0c18002351eca3613416f80019b92e0a511086903d95203c0380119211970bc10c18d80029d94680000e866a1d8000fd9c81ce86e94f0000000861670000ee8000000b59230000001389790000001ed242a960000000000d48d700021895a00000028b2109480770659c391a2542598ba2781e0a9f8ac12782584480000018400000013f8a0a5d2928671f600004ea128330cb1ab27424d20920c1e61d59b2a491878960d20000000000288350ca83b18015185d1fd17c10a1250000000fb80588c92c9b8a63154a308630029a12218211c70650a3873a08852a49a8a8000001182080fc929a65990a400c525389408f84085990615e1b00000001378fa8ada2a20202b80025b9d8a5e976063a9026382c0a99a486d8438cf0608e98b1a968f3115901a461240789b91610228320f50001f986897f9c594a8000000001121f69b20001f28001fb00000000028ea009f523899907c0a302f0000000002390918000b28f616d08380000000002680000020580004014e0000d926729205790c9799bb83799c14d222a378199af93815688f0312950dd90808e12d84f8b9139276a031dd26810e8fd17f24b29b1839960ab8519338000000c78000d99631541dda4e9cc15288709f8000ea0000f405908019a80017e8000001361599a80ae9e88bfa9880700010e1ae92ea3d25a8b601b9df97889c1290678e5045a888f78fea57220188a7b2150280041aa02a0931171938ff23c1ea1228cc140014a5110ba7c2068f5a6095ca2902b0760ac98e88b9f191d1119c49ff1021560358f280017488100011b2a02981e59b99d923c9da25d8721849eea301e41c622e8d50f1947a2226001aa871b68f3a1f8e79d388d9d0136a43a5217505e9988c2a7b806a6ea029a58b002c98c28c8909f317b06617a8270c393009823322f02e88d079000061000244a97149a341e3a319f5914a640f880
  | 9 => 0x15f80000000014480012800000004320f07087d26780008913516414200004c85820f81094506b0a80569c8800269a0a219a5e1cba23893a1ca1121d07a18711e017a3ba370b823397d15d05f99d1010090b48411ca1d62240ee1a7830a17a9e0000dd1890899e280028f83f8748048001dc27f85029911aa7a84b01e8af82613c9a09e496e00000001c8bba7726282a9ec256a0a8731e50e112888c0a024a98600f94f80022c92f01423f1772731068cd9e69c98150cb80000000015817822e24c9b59baa3f99802d1a88fa1d30001190de00b
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x200b2a0ae2a064cbcc4d24a1ea48e1acc92947cda2c00620000d6428a0000de0000000c000000742e98acbed45a84083e780a0e90304020569a2826366c70220000005800ce327e505e82004e8c3400000048000000969cc6000000a2001ca86a006638aa0000007a0000c05c88006000c21880b600ba00005400000000c83cdc160400d86400760068a644cad0b000122472b886004610003a0000b49e0014526e0101000004041203010101090a000301080a00010b00000102000206030a0c09010d000001a2ee2a1aa221d187050e5010e8ab88a8a1e65469c35410e32838ecaa2641960d6354842d0706a9ac429e838358d5214b41c18c629284a0d0c7254c535068c382a629a83255c66314941a18e6a90a4a0d2870548525061c382ca19283435c85450f31c1ac8a906598e0d5458854cc706b22a429663431c95410d31a30e0aa08698e0c64149324c686392a82a263461c1541513192ae3320a498d0c74548524c6a4382a429263161c16510931a30e0a08a098f11414c55008790a0a42a8043d04c52154021a2ae329a83a060c639494290287396a729c81439cf5294a40c1ac6a908420651511813110306a9ac4298818554d6114c40934e1b1aa42060d635485210312a92c2290810d5c4654c840930e0b1ca220631511813110388a8ec09888185544604c440e22a2302622069251181311030ca88c098881a4544604c440c22a230262204987058e211030ab1aa310881455c6544c730a1ce5aa0871860c64949328c287396a92a461439d35294a30a1ae42a2861851571151430c306b22a4190618c5446050430c1aa8b10a81861554584540c24d386c8a9061835915214830c8aa4b08a41845571195420c24c382c928861945446050430e22a3b02821861551181410c388a88c0a0861a49446050430c32a2302821869151181410c308a88c0a0861261c16488430c2ac8a8c421861561544400c28ab8ca6a0e418694c6050720a2ae32a2639061a5418131c83882888018241a81844048020d80c2182401061853181418430c2a0c098c2185d4d6110210c2ea8b0861084e276c85208430c298c0a0a218a1486050510a28eaa0a62886146550531443822928298a21641c1414c510c30a83026288648521813144348a08c098a218554d6110010c4aa4b088008615545843004322a92c218021465d4400c010c32ca20060087095210030042c8b888018021a4584400c010
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x413000040ca43812504a108058d5188440a10805915188430a118194c6050720a1181950604c720d00521c1414c510e0052504604c510c11655c4400c010d01525c4400c010c1175584400c010e0152584400c010
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 48
  | 5 => 1017
  | 4 => 1345
  | 3 => 112
  | 2 => 10
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
  | 7 => packedAt s2K7 (6+((h/1+packedAt s2K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s2K6 (880+((h/16+packedAt s2K6 (768+(h % 16)*7) 7) % 69)*7) 7
  | 5 => packedAt s2K5 (31188+((h/339+packedAt s2K5 (27459+(h % 339)*11) 11) % 1477)*11) 11
  | 4 => packedAt s2K4 (56038+((h/448+packedAt s2K4 (51110+(h % 448)*11) 11) % 1615)*12) 12
  | 3 => packedAt s2K3 (5784+((h/37+packedAt s2K3 (5488+(h % 37)*8) 8) % 162)*8) 8
  | 2 => packedAt s2K2 (612+((h/3+packedAt s2K2 (600+(h % 3)*4) 4) % 13)*5) 5
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffff81ffff83f07ffff83ffc1ffc0fcf9f3f3
  | 1 => 0xf07fffe0fffffff81f07fc3ffe1fffff463c7f
  | 3 => 0xff81ffff03ffc3ffe007ffc3ffe1ff0387cf9c
  | 4 => 0x1fffffc0003fffff80003fffe0003f80fe0
  | 5 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x210c08c42890400165098044c022425818d1b1
  | 1 => 0x44109102412221280a422429121494a1422446
  | 3 => 0xa22522481a440652a084ca8265412a0a854a98
  | 4 => 0xcb59c4929076ab9cd3d06223b9980c33e80f60
  | 5 => 0xc61871ce38733e71ce77330311030c3f7b000
  | _ => 0
def s2Atlas : Atlas := ⟨7,rawDecor 59 s2Pos s2Neg, 0xeeaaee88ee88cc88eeaaee88ee88cc88eeaaee88ee88cc88eeaaee88ee88cc88eeaaee88ee88cc88eeaaee88ee88cc88eeaaee88ee88cc88eeaaee88ee88cc88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37183
namespace PEqualNP.Outside.L_meta_37183
open PEqualNP.Outside.L_meta_37183.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0xf38000c00300b00234a00905000020610714121520df43be43bc43dc439c43bf42bd42df32dd32bf41bd41df31dd31be40bc40de30dc30
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0xe00280b01928004a30088060000010404794e438ea90871d5110e3ca021c714d428e2a6651c544ca38a6a0c7153318e2a2631e539023ca9184715030
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0xd000808558454cca0d621533183588540c2156115030
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 17
  | 3 => 13
  | 2 => 4
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (i*5) 5
  | 4 => packedAt s3K4 (i*16) 16
  | 3 => packedAt s3K3 (i*27) 27
  | 2 => packedAt s3K2 (i*38) 38
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (6+((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s3K4 (297+((h/5+packedAt s3K4 (272+(h % 5)*5) 5) % 25)*6) 6
  | 3 => packedAt s3K3 (371+((h/4+packedAt s3K3 (351+(h % 4)*5) 5) % 22)*5) 5
  | 2 => packedAt s3K2 (155+((h/1+packedAt s3K2 (152+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffff07fffc1ff83ffff07ff07ff07fe7cf3cf
  | 1 => 0xf07fff83fffe1ffc1f07f87ff87ff83fa33cf3
  | 2 => 0xff83fffc1fffe1ffe007ff87ff87ffc1c3cf3c
  | 4 => 0x3ffffe00001fffff80007fff80001fc0fc0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x8108111084820000a5090089008902940c5145
  | 1 => 0x24112209091030940a42485248525028a12492
  | 2 => 0x4222442052210329408495049504a501428a28
  | 4 => 0x6b5b894a43b555ce73d0c447e660318df40fc0
  | 5 => 0x8c630e739c3999f39ce7e660c440c631fbf000
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeaeae8e8e8e8e8e8eaeae8e8e8e8e8e8eaeae8e8e8e8e8e8eaeae8e8e8e8e8e8eaeae8e8e8e8e8e8eaeae8e8e8e8e8e8eaeae8e8e8e8e8e8eaeae8e8e8e8e8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37183
namespace PEqualNP.Outside.L_meta_37183
open PEqualNP.Outside.L_meta_37183.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0xd804e20000003d32a00000195a4c58e343000000000000000014147162f482401000ac105000141200b86874060200007801d00540232e000a12c00180000000000a52804400000000000000440003e00006000000080020008608082860000001ff43fe43be43fd43fc43bc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x4617f544c37ea8984fd5130bf2a2617d544c2f8a8986f151309e2a261df434c37c86986f10d30ee21a619c434c2fea4985f14930dfa1261bd424c3be6498774c930bfa8a617c514c37e82986f50530ef98a61dd314c3f680986f90130de20261f8404c37080987ecc130ef182617f540c37ea8184fd5030bf2a0617d540c2f8a8186f150309e2a0617e530c37c86186f10c30bf290617d520c37e84186f50830bf288617d510c37e82186f50430bf28061be400c378801877cc030fd18061dd300c3f26018764c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c82faa7905f14f20df21e41bc43c837e85906f50b20bf28e417d51c837e83906f50720f790e41ed21c837c81906f10320bfaa441bf548827ea9105f95220beaa4417c5488378a9104f15220bfa9c417e53882faa7105f14e20df21c41bc43882faa5106fd0a20dea14417e51882faa3106fd0620dea0c417e508837c81106f10220fd18441f930883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a417e53482faa6905f14d20df21a41bc434837e84906f50920bfa8a417c514837e82906f50520f790a41ed214837c80906f10120fd18241f930483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20df21841bc43082fca4106fd0820dea10417e51083eca2105d94420bea8841f551082eaa2106fd0420dea08417e500837c80106f10020f790041fa20083da40107e48020bfaa6217e54c437ca9884f95310beaa621bd54c427aa9885f15310bfa9e217e53c42faa7885f14f10df21e21bc43c42fea5885f94b10bea96217c52c437e85886f50b10dfa0e21bd41c43ec43887d48710df20621bc40c42fea9086fd52109faa4217e54842faa9085f15210de2a4213c54842fea7085f94e10bea9c217c538437c87086f10e10bfa94217e52842faa5085f14a10dfa1421bd42842faa3086fd0610dea0c217e508437c81086f10210fd18421f930843f441087e48210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea6885f94d10bea9a217c534437c86886f10d10bfa92217e52442faa4885f14910dfa1221bd424437e82886f50510fb10a21f5214437c80886f10110fd18221f930443f440887e48110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c530437c86086f10c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810dfa1021bd42042fca2086fd0410dea08217e500437c80086f10010fb88021fa10043ea20087e44010
  | 1 => 0xa500c6faa018fe54031bca80637f54c86fca990ef953219f2a6437d54c877aa990cf55321be2a6437f53c86fca790df54f21be29e43be43c87788790efd0b21dea1643ee32c87da6590efd0721dea0e437e50c86faa190dfd5221bf2a443be548867ca910df55221deaa4433d54886f8a910dfd4e21bf29c437d53886f8a710ef90e21de21c437d528877e8510ef50a21bf28c43bf418877a8310fd8c621fa98c43ef21887ee4310df94221bea84437f54486fca890ef951219f2a2437d544877aa890cf55121be2a2437f53486fca690df54d21be29a43be43487788690efd0921dea1243ee32487da6490efd0521dea0a43f631487ea6290fdc8521f710a437f50486f8a090dfd5021bf2a043be540867ca810df55021deaa0433d54086f8a810dfd4c21bf29843de53086bca610df54c21eea98435d53086f8a610ef90c21de218437e520877e8410ef50821bf28843bf410877a8210fbc8421fb10843ed21087ea4210f948421bf28043fa50086f4a010df54021fca80437950086fca7a05f54f40df21e81bc43d02fca5a05f54b40dfa1681bd42d02fca3a05f54740dfa0e81bd41d02faa9205f94e40ef29c815e53902faa7207754e40aea9c81bf439037c87206f50e40de21c817e52902faa5206fd0a40df21481bd429037885205f94640bea8c81bf419037c83206f50640de20c817e509037e81207ed0240dfa9c81be539027ca7206794e408f29c81bd539033aa7206f14e40dfa9481be529037aa5204f54a40de29481bf329037c65206f4ca40de19481bf519037ca3206f546409ea8c81bc519037e63206f8c640de98c81bc319037e43206f88640de90c81bc219027ca1205fd4d40be29a81be435037886a05fd4940be29281bf425037a84a05fd4540be28a81bf415037a82a07ed0140df202817e54102fca6205f54c40dfa1881be431037a86206f10c40bf290817d521037e84206f90840dea1081bc42102fca2205f54440dfa0881be411037a82206f10440bf28081bf40103f480206f50040fca0081bf531037ca6204f94c40dea9881bc531037ea4206f94840dea90813d5210378a4206fcc840df19081bd321037864206fd4440df28881bd511027aa2206f14440df98881be311037a62206f0c440df90881be211037a42206f08440df280813e5010374a0205fd5330bf2a661be54cc27ca9985f55330deaa6613d54cc2f8a99877d0f30df21e61bc43cc3b887986710f30bf296617d52cc37e85986f50b30ef99661dd32cc2fca3985f54730dfa0e61bd41cc3be6398774c730df20661bc40cc2fea9185f95230df2a4613e548c2faa9186f552309eaa4617c548c2faa7186f90e30de21c617e528c2faa5186fd0a30dea14617e518c2faa3186fd0630dea0c617e508c3f681186f90230de20461f8408c370811877cc230fd98
  | 2 => 0xb7ea2a14fd4542df28a85bd5150b78a2a16fd4142df28285bd5050b78a0a14f14142bf2a0853e5410afca6215f54c42df21885bc4310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0215fd5332dfaa6653f54ccafca9995f55332be2a665bc54cca78a9996f90f32de21e65bf42ccb7a85995f94732bea8e657e50ccafaa1995fd5232bf2a465be548ca7ca9195f55232deaa4653d548caf8a9195f54e32df21c65bc438cafca5196fd0a32dea1465df328cbde65195f94632bea8c657e508cafaa1195fd5132dfaa2653f544cafca8995f55132be2a265bc544ca78a8996f90d32de21a65bf424cb7a84997bcc932ef192657f514caf8a2995fd4132be282657f540cafca8196f950329f2a0657d540cb7aa8194f55032be2a0657e530cb7c86196f10c32bf29065bf420cb7a841977cc832f719065dd320cbda64195f94432fb2886576510cafaa2197d54432baa88657e500cbf4a0195e94032bea8065f9500caf2a0195f94f41bea9e83bf43d077c87a0ef50f41de21e837e52d06faa5a0efd0b41df21683bd42d077885a0df94341bea8683bf53d077ca7a0cf94f41dea9e83bc53d077ea5a0ef94b41dea96833d52d0778a5a0efccb41df19683bd32d077865a0efd4341df286833e50d077aa1a0ef14341beaa4833d54906fca720df54e41df21c83bc43906fca520df54a41dfa1483bd42906fca320efd0641fba0c837e50906faa120dfd4d41be29a83bf435077c86a0ef50d41de21a837f52506f8a4a0efd0941df21283bd425077884a0fdd0541df20a837f50506f8a0a0efd4d41df29a83bd5350778a6a0cf14d41dfa92833f525077ca4a0ef54941de29283bf325077c64a0ef4c941de19283bf515076ea2a0efd4141df28283bd5050778a0a0cf14141bf2a0833e54106fca620df54c41df21883bc43106fca420df54841dfa1083bd42106fca220efd0441fb20883bd41107ea8220df94041bea80837f54cc77ea998cfd5331bf2a6637d54cc6f8a998ef153319e2a663be43cc7788798df94b31bea9663bf42cc77a8598f7ccb31ee99663bf41cc77a8398df94331bea86637f548c6fca918ef952319f2a4637d548c77aa918cf55231be2a4637d538c77c8718ef10e31bf294637d528c77e8518ef50a31bf28c63bf418c77a8318f7cc631fb98c637e508c6faa118dfd5131dfaa2633f544c6fca898df55131be2a263bc544c678a898ef90d31de21a637f524c6f8a498efd0931dea1263df324c7ba6498efd0531dea0a63f7314c7bc6298dfd4131be282637f540c6fca818ef950319f2a0637d540c77aa818cf55031be2a0637e530c77c8618ef10c31bf29063ee520c6dca418df54831f6a90636d520c77e8418ef50831bf28863bf410c77a8218f7cc431fb18863dd310c7ea6218df94031fd280637
  | 3 => 0x5881c72000000000000081262c18025e6a60000c21e22820be6ec66c0cc7ac06469e22c2126b43b83442f83e82a239600851c0000000000000005047760000001ec7543a23001b85b20000002a075863000015e60638c28c1a63b408a40c00c034000020080100000100c000000030080040080000200c1d0080080140000300e0080100a0000040180100a01c010030060000680000200c000030000340200100a004010040020000000000a01c0000100803c00804000004020000000000000101200800800004000000050000180300200202c0080a00000800004002004008000000040380200400800806002000010090000040000600601002000012004000030060180700a010004000020020240180d0020040080000c000000000000040280900400c008000040600f8000000040000000200001806004000000010020100300900000001000000000000010140040100400002000801000000008010180040100100e0000000000000000001004000000000000080200100e008000120060100000d0080040000402800003000014004000060160000100000e02402000000008008000000040600000001c008000040000001c0000000000200000c0000000002c06000000010010080020080280100400c0180200600000000000000000000020180000001000800808000000080010000180300000c00000001024014008000040000200000004c00003006098000020000100300800a00c0100000a008008000000000300100000c0000000e008008040040080200abf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121fe94243bd284877d5090ff2a121de542439f29c87bf5290f7ca521ef54a439ea9487bc5290f7ea321ef94643dea8c873d5190f78a321efd4243df284873e5090f74a121ce94243dea8487b95090f78a121f7d0d43df21a877f5250ef8a4a1dfd4543be28a877f5050ef8a0a1df95043bf29887bf4310fbc8621ef50c43eea18877e5210efaa421df94443bea88877e5010efaa021ef94c439f298879e5310f7ea421ef94843dea90873d5210f78a421efd4443df28887bd5110e7aa221ef14443dfa8087be5010e7ca021ef54043de280877e53d0afaa7a16fd0f42df21e85bd43d0b7887a15f94742bea8e857e50d0afaa1a16fd4f42df29e853e53d0b7aa7a16f14f42dfa8e85be51d0b7aa3a14f54742de28e85bf50d0b7ca1a14f94342dea8685bc50d0afaa9214f55242bf29c857d5390b7c87216f10e42bf29485bf4290bde85215f94642bea8c857e5090afaa1215fd4d42be29a85bf4350b7c86a16f50d42de21a85ef4250b7c84a15fd4542be28a857f5050af8a0a16fd4d42df29a85bd5350b78a6a14f14d42dfa9285af525
  | 4 => 0x64800005e808617674c0006c465e29e00070a52c6cc3d473a0006b80000ec3360004ac4040005020d200000048e5d20ca1286ea00000028413c00002600048a6380500004347860000007660000000a439c05a5e000055a0005ea3dc0002420000003e410e0e42cc58a0000e05503c61cc6b60003c84de66274e02855c8226540003400683c064a0000001de0000000a600000066408c2467fc37a0007687c800014e0000040006244362d04bc3a04582687b67ec0000000006786f600004a0000d657800069c7f85a200000028615c4380000000000101c21c46021be0004446344f857471800000051000000048800065a0f200032031a0000000001d019c0002b221c78042607620a27c00035a7d419a3e000028854e2ac37e00010611c32c0004320004100000002160000924ee47048200010005e7be00000077c0005f834a00075c0000b85b823410a00017a56821e6903880000004c04b42de03a19000000025072c00009800000000000013600000039e0706362205420000004242ea0000000000000002e80dc00000000058e7fe0006440006c803000033c2f645271c1d806c1fc6fe0fe2064d00c80001447aa2d26aa07800000000000007e0006c626000000012e0005cc4e846677481644c56027e06207c0000000480000002be22a3d25a04d25260005d40000000000005d059445a41e00008200009623c0000000000006fa0007d00006d254a00000060847a2fa0007b87f20002ae0001b415400000049a5aa2700006da17423e42c0007c640e0fa7da00072a56e6d40000004f634800017225a4ae2221660003780005980005240000005724460000005ec0001180ea5302a800000006a0740001244e400000c0000003da0000000006b26ca3a46ce2c601e0b64dc6886e65ee4900c07e03900000002aa6f07384fe53200000008e00000000000000081e50c00000080802e3240000001f82d81b263267c62246c00000041c7841843cc61e3d81103843120003ec1a43a80000000006201940002365564b00004620000000d00000000000002ca3860000e83ce21065c4000002260000005a876a3725880000000000002fc0000d871a59e5ae8142f07a227a4720000004080000008003ca4141ac20467e0140000000001c80544407525c00000007ba4c67e444257c02200011a0da4504b80005402e20000000005ca1ca5124020160003140f80000000005f26a429435e0001162dc7bc0004200000000000006bc1c65dc0005f01e800079000000000000000000000000056432a1f40000000000b244a0000002ce3767b404c7cc13e72824e19600000000000000061200052e66a0366ac3580002bc6745be7360000000407984c430c00000000019837079633850a5fe80400000000034e0000003427827f40006a836c43c05c0001
  | 5 => 0x17c35062a2923b67400000000ae6a23a610c05600063c0000004b60003e60000000000002d681800038a7d600000016c7341047480000006843b253e1da0001642440000000000000000002c40006180003c26be4ec00001c55e3d600079a6460000007f04aa00078c0461081380800000900000000000002e03620001ae7ee00009a0000a25960005700000000000000000000000000de36e0000007221bc15615a0000000000006de2b06560e62185143ee00000000013202a0000000000000840020000001ea0003561ce4c82240180000004b20000001024ba2143aa5c24a00001f60000002e47600000007641924ca00000071e3fe0004f40aa00000000025616a00000000000000000000000006e0004fc00061a00000000069822e0003660008066ae0000004120000000000007504d600000055800079e00000000023000000019e3fc44e7260001b60003f05ac0006b07b06603f400000000000014000000042a5220000000006c200064000004471201a00000000051e00063e18c3bc00053429a00044834c03c0003d052830a62e5b40000005060000005626f25c60b000041a54c00029c63a02c00000000052a77875e54600020077207266841800000030200050800000000000031e00080a17000035c1e67ca0007ae5445d839870860a46820200043a0000fc70c0000007d25540003185160005903220a847468a0000a03c400000000000082414c4be00000046a6c01a02286520382800000000006003742c216e0000002ee7ea00068c00000000000014266e3460001aa0000000000bc00025258461600000000043000007a0000002c00000007e26f42f40000d40000000004c261400000000000037c5bc58600e39a56c00049c5921c068273c0000000002960004a61d27a63606f84160004f00007a80006e07b26941262da0000000000000002c80007c27000ac0007880000000000000003b00001f252000073e0000000005ba12a2fe00017800000075a0007941a833223a1346e23061680002900008020000002d42ba4e671639282000074216018e4e05c40000000000000002ec47e0007a43ba6287065d67e600000000000000000030400076c1b00000006ba00000016265833a0ce4ea67a40a25c57a0000000000000c466674a6d62480002a600071000014a27478e3105366e800a0004a44cc79213a1ee1ba00000076200031c0000005a464e0940604602640003ea00069600067000000004232e0000000000000ee1fe72e5fc00081000000000000000000000069a00078a5f423200012c70277a53c1822b46863f800053876e00057e00061002426e7140000000f47e820e1e44d400059a00038226c00000038e18a0003fa21a56a3301467c02e643e0883947320f00000000003ae6dc0007ce2720001500004563f
  | 6 => 0x6664845e04e0005827dc3ac02033e0004ce26a00000060400000000060e70400020c36a4840004943641d42382987462760000004fa00050e77028e0000000006760002580000000000000000001f00007564543f230e42881a27800000000000000018820849e5b00007246e47a00e23801120003285b60000004d800003e0000341522627306ee46e59c3341dc4962a46925ce80e77e57670e4788267f680c0525005e224c3084e200000068e0000007de5c800051a1fa64c5da2f26d04986a04da61c11e0001a228a5fa1483e23160583265527fa0000121e02543684a249246448c45c5185660f65e440662609c24a58c0b40000003521221200000006500001866d809e67247c47664260c6fc0000000007c40000062b80005a62401d64f23de4220ba0007444860000000000004a80002665483540000006800c60000001305de00079c3be17e7d811400058042e5f65e60000000320002b600000000000053a000
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x3538423d64d4e108f992538423d6494e108fd91538423c6454e108f996438423c6590e10ae982438423e6510e108f194438431e5310e10c754c43842ba6010e108f992528423d6494a108fd91528423c6454a108f990528423d6414a109798c528425d6314a108f997428423c65d0a108f995428423c6550a10ae98341842b86050610a798e40842b56190210ad5844084338548c210ce1513084358534c210e610d308423e63d51108f58b544423e64951108f994544423e63151108f588544423e60151108f180544423e64d4d108f593534423e6494d108f592534423f6454d108f191534426f6254d109b189534423e6590d108f19643442ba6090d108f994434423c6510d10ad58443442ba6010d108f992524423d64949108fd91524423c645491097d8d524425c63549108f990524423d64149109798c524425d63149108f997424423c65d09108f995424423c65509108f99741442ba60d05108f19541442b860505109d195214436452485108f996404429e63901108f9944044338548c1109e1953044338544c110d614d3044398434c110bc18530442786548110f8485204425e63d50109758f540426e62d50109b58b540423d65950108f98e540423d62950108f18d540423f62550108fd85540423d61550108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7d92530431c6494c108fd91530423c6454c10c7951530431d5454c10c7d91530431c6454c108f990530423d6414c109798c530426e6214c109b588530427a6014c108fd96430423d6590c10c794e430431d5390c10ae982430423f6510c108f594430431e5310c10c754c430423e64d48108f593520425e63d48109758f520423e64948108f592520426d6594810cb952520432d5494810d394e520434d5394810cb992520432d6494810cb90e520432c4394810cb951520432d5454810d394d520434d5354810cb991520432d6454810cb90d520432c43548108f990520423d64148109798c520425d63148109b988520427661148109e980520423f65d08108f597420431e53d0810c754f420432e52d0810cb54b420423f65508108f595420431e5350810c754d420432e5250810cb54942042b860508108f992510423d64944108f597410431e53d0410c754f410432e52d0410cb54b410423f6550410c794d410431d5350410cb949410432d52504108fd96400423d6590010a798e400431e5390010c754e400432e5290010cb54a40042b561900108fd94400423d6510010c794c400431d5310010cb948400432d5210010ad584400436552c40109e59610043595384010da54a10042776544010d954910043b240440109ed9510043595344010da54910043b14144010
  | 1 => 0x823f64546208f191518823e65d06208f195418829e6390220ab58a40882ad6210220ce1523088338544c220d614d3088398434c2208f98f544823d61d51208f992544823e65151208f98c544823d61151208f993534823d64d4d208f992534823d6494d208fd91534823c6454d209dd8553482746154d208f996434823c6590d20ae982434823e6510d208f19443482ad6210d20ae980434823e65d0920ae983424823c6550920ae181424823e64145208f590514825e63145209758c514823e65d05208f197414823e65505208f195414836451485208f996404829e63901208f9944048338548c1209e1953048338544c120d614d3048398434c120ba189304825e63d50209758f540827661d50209d587540823d65950208f98e540823d61950208f18d540823f62550208f589540823f61550208f990540825e63150209758c540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7d92530831c6494c208fd91530823c6454c20c7951530831d5454c20c7d91530831c6454c208f990530823d6414c209798c53082766114c209d584530827a6014c208fd96430823d6590c20c794e430831d5390c20ae982430823f6510c208f594430831e5310c20c754c430823e64948208f592520823d65d0820c794f420831d53d08208fd95420831e5350820c754d420823e64944208f59251083365494420cd55251083565394420d554e51083366494420cd59251083364394420cd10e51083374294420cd50a51083365454420cd55151083565354420d554d51083366454420cd59151083364354420cd10d51083374254420cd509510823f65d04208f597410831e53d0420c754f410833651d0420cd547410823f65504208f595410831e5350420c754d41083365150420cd54541082b860504208fd96400823d6590020a798e400831e5390020c754e40082ad6290020cd946400833551900208fd94400823d6510020c794c400831d5310020ab58840083365110020cd544400836551c8020d654e200837151880209bd9520083655148020ea901200827b6548020d654d20083a94248020dc545200823e63953108f58a54c423c63553108fd8954c423e64d4f108f59353c423f6454f108f19153c423e6414f108f59053c426e6214f109b58853c423f6590f108f59643c42ba6090f108fd9443c423d6510f10ad58443c423e64d4b108f59352c423e6494b108f59252c423e6414b108f59052c425e6314b109758c52c423f65d0b108f59742c423f6550b108f59542c42b86050b10d914921c429e63903109798f548425d63d5210a798f548423e63d5210c798f548421e63d5210c758f548423d62d5210cd587548433a60d52108f98c548423d6215210cd584548433a60152108f99
  | 2 => 0x62d51308f587544c33960d51308f992544c23e65151308f98c544c23c63151308f588544c23d611513097997434c2da60d0d308f996434c29e6390d30ae982434c23e6510d30c7d50434c29e6510d30c7994434c29d6210d30a7584434c39b6010d30a7980434c3986010d308f990524c23d64149309d984524c27561149308f997424c23c65d09308f995424c23c6550930a718d424c2b86050930a7193324c29c644c930d3149324c2d8604c9308f990514c23d64145309b988514c26d62145308f997414c23c65d05308f995414c23c6550530a718d414c2b86050530a7193314c29c644c530d5145314c2d8604c5309e997404c2da63d0130e610f404c23e6590130a798e404c2ba60901308f994404c33b5410130e6d0c404c3984310130ae994404c33a6510130e6d8c404c2ba6310130e618c404c2b96210130e6cc8404c3993210130ae584404c39b3110130e64c4404c2ba64cc130e610f304c29e648c130e6102304c25e63d50309e983540c23e63d5030c798f540c21e63d50308f58b540c23d61d50308f983540c33a60d50308e983540c26e62150309b588540c27661150309d584540c2ad6215030ad584540c23e6315030c798c540c32e62150308f588540c32d62150308b588540c33661150308f584540c33561150308d584540c23e6015030ce980540c23e6494c308f592530c2ba6090c30c794c430c2ba6010c308f992520c23d64948308fd91520c23c64548308f997420c23c6550830cb949420c32d52508308f992510c23d64944308fd91510c23c64544308f997410c23c6550430cd945410c33551504308f992500c23d6494030a798e400c23e65100308f194400c29e6310030ce940400c31c54cc030ce152300c2d9638c03097d95300c31c544c030e6901300c398404c0309ed95300c338544c030e690d300c398434c030b6d95300c35b654c030e6d91300c398644c030e6d51300c35a544c030d6151300c398544c030c6151300c359524c030e6d09300c399424c030d6545300c39b414c030e6505300c23e63953208f58654c823c63553208fd8554c823e64d4f208f59353c823f6454f208f19153c823e6414f208f59053c82766114f209d58453c823f6590f208f59643c82ba6090f208fd9443c823d6510f20ab58843c823e64947208f59251c823f65d07208f59741c823f65507208f59541c82b86050720a798e40c825e63d52209758f548829e63d52208f98f548831e63d52208798f548831d63d5220cb58b548823d61d5220ce983548823e6315220cb588548823d6115220ce980548823e64d4e208f593538823e6494e208f592538823f6454e208f191538823e6590e208f19643882ba6090e208f994438823c6510e20c794c438831d5310e20ae98043882ba60d0a20ae181428823e64946208f592518
  | 3 => 0x640a798c519029d6314640c794c51902ae6214640ab58851902ba60146408fd97319031e53cc6408f996319023d658c640c794e319023f654c6408f195319031e534c6408f994319023d650c640c794c31902ae620c640ab58831902ba600c640ae580319023e65c86408f597219031e53c8640cb54b219023e65886408f596219031e5388640cd546219023d6548640c794d219032d5248640cd545219023e65086408f594219029e6308640a758c219031e5308640e948421902ba6008640ae580219031c5390d40ae982435023e6510d408f997425032f52509408f99741503375150540a798e40502b96090c408fd95431031e5310c40c754c43102b96010c40cb54b421023d6590840cd547411023d6590440b658e401023f65500409ed9540102ba60d4c408f58a531023d6194c40ce982531031d5314c40ab98853102ad6214c40ad98453102b56114c40ae98053102ba60d48408f18d521023f6154840a798c521029d6314840ad98452102b56114840ae980521023f65cc840c794f32102ba60cc840ae583321023e658c8408f596321032d528c8408fd95321023c654c840c794d321032d524c8408f994321023d650c840ad98432102b5610c840ae98032102b9600c840ae983511023c63544408fd89511029e6314440a758c51102ae6214440ab58851102ba60144408fd97311031e53cc440ae98331102b960cc4408f996311023d658c440cd546311023f654c4408f195311031e534c440cd545311023e650c4408f59431102ae620c440ab58831102ba600c440ae580311023e65c84408f597211032d52c84408f996211023d6588440cd546211023d6548440cb54921103355148440aed8121102b860484408f994211023d6508440a798c211029d6308440e948421102ba6008440ae580211029e6394040a758e501031e6394040c758e501033a6094040e698e50102b96394040e658e501029963940408f58a54cc23d6195330c718d54cc23f62553308fd8554cc31d54d0f30ae98243cc2ba6010f30c799443cc31d6510f30a758843cc29d6110f30a798043cc39a6010f30e658043cc23e6494b308f59252cc23f65d0b308f59742cc23f6550b308f59542cc29c6350b30a719332cc29c644cb308f99251cc23d64947308fd9741cc23d65d07308fd9541cc23d6550730a718d41cc29c64cc730a719131cc29e63903308f58a548c23d61952308fd89548c23f6155230ce181548c23e6494a308f592528c23f65d0a308f597428c23f6550a308f595428c2b86050a308f992518c23d64946308fd97418c23d65d06308fd95418c23d6550630ae181418c33954d0230a798e408c29e6310230ce994408c2b96510230ce594408c2ba6310230e698c408c3996310230ae588408c2b96110230c7953308c2ba64cc230c758f544c23d
  | 4 => 0xb19532486e4614c921ab58b414863f65505218f59541486af62505219d19531486e4624c521f14c9314863e64d41218f593504863e64141218f590504865e63141219758c504865e63d50219758f540867a60d50219e583540863d65950218f98e540863e60950218f18d540863c60550218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21c7d92530871c6494c218fd91530863c6454c21c7951530871d5454c21c7d91530871c6454c218f990530863d6414c219798c530866e6214c219d984530867a6014c219e580530863f6590c218f596430871e5390c21c754e43086ba6090c218fd94430863d6510c21c794c430871d5310c218f992520863d64948218f597420871e53d0821c754f420863f6550821c794d420871d53508218f992510863d64944218f597410871e53d0421c754f410863f6550421c794d410871d5350421d354f21087555388421b958a210866f6548421d354d21087a74148421e950521086776548421d554d21087a74248421e950921086e76548421d9d9521087a66448421e959121087a65448421e955121087675348421f194d21087655348421f154d21087455348421e990d21087a44348421ce95250087395494021d694e50087595394021f8486500873b6494021ce192500873a4394021ce10e500873b4294021ce50a500873b4194021ce506500863f64540218f19150087652154021ce95150087395454021d694d50087595354021f8485500873b6454021ce191500873a4354021ce10d500873b4254021ce509500873b4154021ce505500876b2154021dc88550087692154021dc48550087612154021ae98243d031e5310f40cb54b42d033551d0740c7d92539031e53d0e40c794e439031e5350e40c754c439031e53d0a40c754f429031e5390a40c794d429031d5350a40cb549429031e5310a40c794f419031d53d0640c794e419031e5350640c754d41903355150640c794c419031e53d0240d654f40902ba60d4e40c7d4e539023d6294e408f586539031f6294e40c798a539031d6294e40c718a539031f6194e40c7986539031d6194e40c7186539031e6094e40c7182539031f6554e40ae980539029e63d4a40a758f529031e53d4a40c754f52902ba60d4a40c794e529031e5354a40c754d529023c6354a408fd85529029e6314a40a758c529031e5314a40ad98452902b56114a40ae980529023f65cca40c794f329023e658ca408f596329031e538ca408fd95329023c654ca40c794d329023e650ca408f594329031e530ca40ad98432902b5610ca40ae98032902b9600ca40a798f519029d63d4640c794f519031d53d4640ae983519031e5394640c794d519031d53546408f18d519023f6254
  | 5 => 0x548c63c6055231ae982438c63e6494a318f592528c63f65d0a318f597428c63f6550a318f595428c69c6350a318fd91508c63c64542318f58b544c63e60d51318f992544c63e65151318f588544c63e60151318f996434c6ba6090d318f994434c63e64149318f590524c67a60149319e580524c63e65d09318f197424c63e65509318f195424c63e65d0531a798f414c63c6550531a718d414c63e64d41318f593504c66e62d50319b58b540c67a60d50319e583540c63d65950318f58a540c63e60950318fd89540c63c60550318f990540c66e62150319b588540c67a60150319e580540c63f6590c318f596430c6b56190c31ae982430c63f6510c318f594430c6b56110c318f992520c63d6494831cb952520c72d5494831cb992520c72d6494831cb90e520c72c4394831cb951520c72d5454831cb991520c72d6454831cb90d520c72c43548318fd97420c63d65d0831cb94b420c72d52d08318fd95420c63d6550831a718d420c72e5250831cb549420c63e64944318f592510c63d65d0431cb94b410c72d52d04318fd95410c72e5250431cb549410c74d52cc431d954a310c65f654c431d3549310c795414c4319dd95310c796434c431d9549310c73a5494031ce552500c76a5294031da54a500c73b6494031ce192500c73a4394031ce10e500c73b4294031ce50a500c73b4194031ce506500c63f64540318f191500c73a5454031ce551500c76a5254031da549500c73b6454031ce191500c73a4354031ce10d500c73b4254031ce509500c73b4154031ce505500c75b3154031d64c5500c63e63953218f98254c863c63553218f18154c863e64d4f218f59353c863f6454f218f19153c863e6414f218f59053c867a6014f219e58053c863f6590f218f59643c86ad6290f21ae98243c863f6510f218f59443c86ad6210f21ab58b41c86af62507218fd9150c863c64543218f98e548863e60952218f18d548863c60552218f993538863d64d4e218fd91538863c6454e218f990538863d6414e219e98053886796014e218fd96438863d6590e21ad58643886ba6090e218fd94438863d6510e21ad58443886b561d0a21add85428863f64542218f191508863e63951218f58a544872d62951218f586544873561951218f982544865f63551219718d544867b60551219e181544869c6355121ae181544871f63551218f18d544871c63551218718d544863f6255121cbd89544863f6155121cdd85544873b60551218f181544873860551218e181544863e64d4d218f593534863f6454d218f191534867b6054d219e181534863e6414d218f590534867a6014d219e580534863f6590d218f59643486ad6290d21ad58643486ba6090d218fd94434863d6510d21c7d4c434871c5310d21ab58843486b56110d21ad58742486b761509219
  | 6 => 0xa3d64946328fd91508ca3c64542328f587544ca3e60d51328f992544ca3e65151328f584544ca3e60151328f996434caba6090d328f994434ca3e65d0932a798f424ca3c6550932a718d424ca3e64145328f590514ca7a60145329e580514ca3e64d41328f593504ca7661d50329d587540ca7a60d50329e583540ca3d65950328f586540ca3e60950328fd85540ca3c60550328f990540ca7661150329d584540ca7a60150329e580540ca3f6590c328f596430caad6290c32ae982430ca3f6510c328f594430caad6210c328f992520ca3d64948328f597420ca3f655083297d95320cb8d424c8329bd95320cb8e434c8328f992510ca3d6494432cd952510cb355494432cd992510cb356494432cd90e510cb344394432cdd0a510cb354294432cd951510cb355454432cd991510cb356454432cd90d510cb344354432cdd09510cb354254432d5cc9510cb663254432d54c9510cb653254432ce952500cb395494032dc946500cb715194032ced92500cb386494032ce90e500cb384394032ced0a500cb3942940328fd91500ca3c6454032ce951500cb395454032dc945500cb715154032ced91500cb386454032ce90d500cb384354032ced09500cb394254032d6cc9500cb5932540329e98253d06796094f41ae98243d06b96090f41c794c43d072d52d0b419798e50d065d6394341ad58753d06ba6094f41ae58253d063d6294f418f98253d073a6094f418e98253d07396094f41ad58453d06b561d4b418f18d52d063c6054b41ad58452d063f65ccb418f99632d063d658cb418fd9532d063c654cb418f99432d063d650cb41ad98432d06b5610cb41ae98032d06b9600cb41a798e50d069d63943418f98e50d071e63943418798e50d071d63943418f58a50d071e5390e41ae982439072d5250a418f997435071c5390d41ae98243506b96090d41cbd49425063e6510941ad58653506ba6094d41ae58253506b76154d418f588535063e6014d418f98f525063e60d4941ad586525069f6354941a718d52506b76154941aed8152506b860549418f197325063e658c9418f596325071c538c9418fd95325063c654c9418f994325063d650c941c714c32506b6610c941ad58432506ba600c941ae580325069e6394141a758e505063e63141418f588505063d6590c41ae982431071e5310c41cb54b421063f65508418fd9541106776550441cd951411067a60d53319e58354cc6ba60d5331c798f54cc63d62d5331cd58754cc63e60d5331ce98354cc63a60d5331ce58354cc71e63153318f58854cc73561153318f98054cc6b56190f31ae98243cc6b56110f318f99252cc63d6494b318fd9152cc63c6454b318f99742cc63c6550b31a798f41cc69c63507318f99250cc63d64943318fd9150cc63c64543318f58a548c63e60952318fd89
  | 7 => 0xe0000000e00200c0000e0000040080100a0000080101204c0080601a0240282e0000080083200801000007002038010450080280380a000018020030220000004502c0140e00600a01c010180000100081700202c0d8000000380100a0000100781000001c0480100201c0181600201400000042008008010060000580200202006015000010088020040400f01d0240280480a00a0000080000800000007008084018140000000200e01e0080000300002809010004040020060140100000000202005800032078000000500240700b0180000080600200c0080200a01c04008002004018280060040180b0100080000f094008000000020100180100a0473b6494243ced0e5090f5b4354243ae9835290eb960d4a438fd855290e3c6054a43ad9845290eb56114a43ae9805290eb96014a43ae9835190eb960d46438fd895190e3c6054643ab9885190ead6214643ae9805190eb96014643ced425090e3d62942438f5865090f3b5294243ce94a5090f395294243ce14a5090f3b5194243ce9465090f395194243ce1465090f386394243ced8a5090f3a6294243ce58a5090f386294243ced865090f3a6194243ce5865090f386194243ced955090f3b5254243ce5495090f3b5154243ce5455090eba6090d43b65824310e3f6550c4397d954310eba6094c43ae5825310f1e6394c43ce9825310f396094c43e69825310e9d6094c43e65825310e996094c438fd855210e3c6054843ad9845210eb56114843ae9805210eb960148438fd895110e3c6054443ab9885110ead6214443ae9805110eb960144438f58a5010e3d6194043ab9885010ead6214043ad9845010eb56114043ce5405010e7a6094f429e58253d0aba6090f42ae58243d0b1e5310f429798e50d0a5d6394342ab58b53d0aba6094f42ae58253d0a3d6194f428f98253d0b3a6094f428e98253d0b396094f42ab58853d0a3c63547428f18151d0a9e6394342a758e50d0a3e6394342c798e50d0a1e6394342c758e50d0a3d6194342c794e4390aba6090e428f9974350b1c5390d42ae9824350ab96090d42ab58a5350aba6094d42ae5825350aaf6254d428f5845350a3e6014d428f98f5150a3e60d4542a7d8d5150a9c6354542aed815150ab86054542a798e5050a9d63941428f98c5050a3d61141428f5964310aba6090c42c794c4310a3f65508429bd954210b2e54508429e98354cca7960d5332ae98354ccb1e63d5332cb58b54cca3d61d53328f98354ccb3a60d53328e98354ccb3960d5332c798c54ccb2d62153328f58454cca3e6015332ab58a43ccaba6090f32ab58843cca9e63d0b32a718d42cca3e64947328f59251cca3f64547328f19151cca3e64943328f59250cca3f64543328f19150cca3d61952328f982548ca3f61552328f181548caba6090e328f992518c
  | 8 => 0x26149d408d843bd6911918015b4e816648bccf14e402908cb2142098147c1a83850312010f8a9428d8b429ce584443dc9c5218a840f40c4a9138d578d04a30ef03e4155748000000000d959103455c47854980007bc96c2b15d830d9dc0010003b94d19c8c6d108a5c000c294bce1464cba52a86c40c8000420b0894198001831800098851542d6fcf84b640018240ec3d493c92c5440017e80006740013249a0000e6c000000e3575c6fd55d034db09040010840016442e00000019900000000000009a52ac000000628000468000000f3c000000e40000a040018c4e280000000012800011497f07d40000015c090c16956491d14c69910c3d00006dd538b8166c358cd4689a0cc109291c96148fc9e8af4350ea81410cd8b84e82d00794609bce1044cc60b687609193c5465079361938aa0e7cb4c9dc8299291a8ae14ec27027933c0cd845594dc47702ac0000002fcdb56e035d1e83100885f97a48c46bd9a4b285dd1e07a83e92b00440013ec0004780d44c80016ad3cc8600014497590443cc0016c1390c588595a4dc14951f0ed03795d467c4d000000000178c2a90959e11f8d40dd497c2043f162c3743acd48e8c5e11d4f90000354d15248b0031c0a972165063c9547381b4fd8ac595d560268084d50148d0c224aed6480007e022d87c0007951b98c07b01018f966086d03c934df921d86598c921008e656240b400c050020040001f00f00002c000000300040080100a0000600108e0400000002e088028030020000000300600003014002124020040060000b82001c0000c800002040028090160080a81a00404c02005002004048010340041700502a1100002b00c0600400400802c050030200180000000a03801806006010030010200940100400801c000070180040080000601000000000014058010000500080700000c00818004000320000000000180104a0080480d004000020000080b00480106a0000100100a000000010021d004000016000188220020480300000a008000110000000080e0040080100104c01c038000060040581204a038028100240000f80201400c010330000580300100203c000720020000000003c0740000400a0dc0380202601c0000000c0040101e0000040101001a0000c8030000702d0280080140000600600803002016000000040080100186300e00c010000020542f00006c01c0000000403800000004054000010020100184400a0240381601a0000000102a0200581800002c020040100140200001a028000010020540281a01604802000004110000260100a80780000c0600c806052000018060380040100100002c0300e00c02000000000008068060180400980d006034030030000040000600000c050020040400800100a054008080200000400d0040000400600a0280880300
  | 9 => 0x143586cb10000c0184982c558000b1c000c7c00000000000038c2ec0001e46140012992d07107c50f0000c2c00000185d7e4ee88ec0651dc2555ec8700000000007148a4d0000042c000000a215a8b90f68670000d399000013b15290900000000012c05c40016dd2f00011b0f211d92b8fd14a171507cea11100e01217013d47a0939709419a10d58370000e609095e0a192885f40b8d20a640009c80016100018acfb96cd9b12a4a08880c5c0005051fd104930690000115860e500017847458d1840d690d0fa17f91680000008dc961100abc07d188d6520545c58d65912546cac84a9220a504ecf549712e8848c1c4b8b607c996478cf41668348c08e390d88e07917a0a4c0e4879588a283645b447d1408e41986b41d43e18f4fec2741f8fe46a54103fc3889f4fe19a92fd255634fccdbcc8d1e552000ce046c8cc54c412cda55015250f46a0425128474d3426c984bb93510254dd3200e96bd9984a050053009c5a9164a3861c5101802e8d9d9214f47cc4109b4f0960cc8545469c7f4ffd2ece745bcb40f44a014785a4d80609098b35470be19888684389652f982877c54085106d7b10bd74c8a171c59ce90bd0e2c1dc0582bd00400075d34151800180c09800159cb480002344e47d80013380f0000f9918d8686f4bfc8f16747ac62c03cc4c648bc81e07f09959b59484dc788d9083cf6d4f97b99d5301154cdd0709ed63c0000000002f4000d19851114ee069537cf0d8d41a4ab04408205cc264c202f86d80acbcce48054a34f5845d24cc709e56a96f4a48eb8038e4cb54ad93689fc88d36c7089796a09c08a8a1d5912080019c19f0c68f3935879d8cc00049565c001424c9c000cc0000001744fac000c14000ac018c0212b4000d55430000aac00077475151481c39c40c069904230000588560e0c00074938973000000000024c4198596180017904912dd5700000006ac1ed6213b41f0f700019d0d09924a24578c980000012c44cd2e4acc888948195134bd836c5d1a14df4650e20a61604f016306c0e797ac1d14409f056d6d1170ab40000017e00019180008b170c4fc000de89cd24076c00122c000000244d280014a80012680011815ad41cd1d3e8d78b0d02d91c0000000019ad69c0015e8489878000000ec4000620518b9948c0017d80011ec000000f04ddd7c0508cd8e9d2e098cded0600fd7759fd765958fd4000f798dd4598742d4e89780280398f5d2148e82e439559819c4ac83072d8b01fc0513a43340014f00001756d44f0800b50525585414b14550bd40014cc0000600006d51a00040000000011c4bf54ac5b00018112cc000664034000af8810944341a043b08f87b91a57f40011b4950000df00f81c043d96181ca8c090764000000000125835688000e19820f9cef96806619cc460258c7489c288a6d
  | 10 => 0x4be800074000000000000000158c6240000015b86102c0000d9923c00000021c7804bc000564be4000000cf474c00061834c968a71229144bc557472065400154c0495b040199d8e0000000000e94591380d601ad9f400183c0004b505c7780000002f15100012100018956953288945d528c0010516c50a05e575104023964094d32d97d8a5395740e686cc2dd6785d93a04098fc4f540ccb977c00000190d96d00c6f9789308c0c3a93300000000000000018381f513930c95c000c24e099a00081519093dc79931d76cf110e46e50c5818c94ff572cced6857a8bad1783d92842a4ed97291f539913c4583241900002a01380018d8d5cf5071c80d2508f4640ae56b55e4924f14ce8d4505813c298818dfcab8ea4a994b8d895f88349d04c4ca4e440005acd2d79c04d8a0c64dcd52c06c0011bd6541bc5f19d9194b5c47192c9b8a555547e400015c000af00004297d11d139c001348fdd5a0ee465c84c001a08430000030000000edc01c7680002c40019e919d2744553ac000b9c4802b8cb40000000014500006a8b396b80004d4bb4104000001400000ca0e85a18484c54f4d44d629951968ff80019798f02b4215738000000000000000a101c87e8aa93c81584655497610a833d174d319e43397fcd8cc81224eec0002081c40004149594fc1cc0014b411c0000000000010b50b8000000000000000c3c00044839144509c0400008d4dac00135cafc5752f4f35279638dd887c4a4f759c4ba10c8ebd5d0580000b7000002c5e94750814398bc210db8000000ec8fb57bc000f30000000705600dc80011ad8e47250c0000000011490c04c78a7c0019141196f070c9154d8a147eceb452d57ccf89107f8bbc68c3f517c3b52c8b8c538824000fe8001010b8450ce981b0aa40000015314812d8d3c134000000000f2d16ced46683a164d4897c40b0b74da12a01a15810398713f81b800037d954a400013d0fc89b000063420c5540c09d80005ed5047b40000017c8bf88b817cbed27099cb318848c87fd4c98090e93653705a16f97693f13a8f2853d01c2858046580000006780004b0000000000d74000000094d6c2486ed43c00000041c55cb78f80e2432810cc3184c1290ec7d032c0000001880bc2cc5941710d556d7051853e1698e1d2347c0b3cc51880164b2c0000dd9408086b0528cd000194436800000150d5bc0000000000000013e40248cc000fc4b444f8001259854e00a3ca58ecc73cf94c44571238d1106808d9b96704c13c00000003ec5480018141783c1934fc0f600d05693b88989982957b4884000ad17190a42d9054b6c315898360ef46819ed770c889007190b10195dc7dc5202900013f448d9f920d984000da8000730a68fa97cce5cc40a74dd01d93d92657dc23d25cf654a49d4e54ce18e88555f10149915580000
  | 11 => 0xb8857d7ed0ad8a824051d4b0eac2288055c8684330f4931066c8c1994b7d6c8c180016b046d734754e30a88efd5f40012bd3fd378f7c8901e919967cce46e825c3205c0de0735374250599890d7cad48ad244220fb0144a9d5cca780a414c001384451334218de4ff0000bf00000009a8000000add93c00000112d404000f88ca8cacb5800151c0d8cb19758ecae973c49994ccfc7596e84e14e154005d484261794000d70a2d8886f14281309f91610480006b8308b058c9021231315290fa57113548149ac600b240016a4000cc8a0cd4c5853bcc34ba80000015fcbb00016e4304ccc00000054c00016d26c2014d527c0146e188d609508000001535150e710fc00104c000f19089a014e82c83c483968ceb07a40743c929534ca80638604b197784049e00805b8534c4911c0013456ed29d15c001318f1d4c06448650640008d08b4cbd544bdcbc000000111843583084193011175530555113063000161c0010dc001568fbcec19bc27d468e3c00070153cf8c5fc85cc90a44300729028f24161158d241852d48457256d800112082c0004d80003a40000705c90743f8b9449c0006d17d40001090e11c00a0380c399700008d860d1cc87579989c00097
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x2041f7558c219020fbb4a610c81075da5308640c4aca908432068563484219038329a4210c818694e6008640c34a6b0043206a1215802190306a9ac4298818554d6114c40932e7306a4204357118d521021ab88ca99081265ce60d444085ae431aa22042d72195311020e39aca90881265cc6048440c52a43024220631511812110312b2a4210881a158d2108440d4242b00422049870588434c24c382c221a61469d46010d30b12e4300869859171180434c2a2b88a499261515c8514c530c34ca21e809851a75d8c404c28d3a8c620261625c86310130b22e2318809849873588404c24c3b26420261a25893210130930e6b088098498764c4404c348b0a62202618398d6215030c4ac5308a81861663584540c313312c22a061895896115030c52c5300a81863161980540c21ab88caa10610b5c86550430a1ae42a6601851571153300c294b90a9180614c5c4548c03083cec2a2601850d72151300c28ab88a8980610e9d8544c030a52e42a2601853171151300c28d3a6ca98061269db544c030a34e92a2601854972151300c2a8b88a898061269d8544c030b12e42a2601859171151300c28d3b0a898061869d8544c030e14e42a2601851972151300c384b90a898061425c8544c030e24e22a2601851971151300c388b88a898061445c4544c030a30e8a92601851875509300c384a928498061461d1514c030a30eaa0a601871151505300c20e39acaa0e418658e60d5220a32e7300a91062962980548821ab88ca21c41079ce65d0620a30ea21a61104357119443482163aac421a41515cc5148520a30ea21a60905897210d3048270b88c4982410e9c26395020a34e1b24a61051a70d91530821cbacc1218418654e6090c20952e530486105327090e5108298382c8a88414c9c24354420c32a630282104a9721814108318a88c0a0841079cf659002083aeb31c801041f7694e400820fbb2a7200418598e5190020c2cc6a8c8010625625464008306a9ac420041895895110020b14e72024010721519012008384a9a8490041c85095148020838e6b2a85885457314921c430cb1cc1aa421465ce6015210c62c3300a90842d72194438420f39ccba1421079ce6550a10a30ea21a610841e73980544421d380cb21a210b5c86510d10868eab08868854573149214428c3a88698221645c4434c1109c2e430a608866065485204421d384c72a021469c36494c10a34e1b22a60843975982430430ca9cc1218212c5c66090c10a54e121ca40852870591520429538486a90210e5d46050810c32a63028408629521814204258b88c0a1021079cf659001083aeb31c800841f7694e400420fbb2a7200218398e5290010c1cc6a94800862552586400430aa9ac220021895496110010b24e72022008721529011004388a9a8288021c85494144010
  | 1 => 0x5090f14b10c5284874c9c46294243a62e2314a121d1a731865090e95390c3284874a5c86194243c62c230ca121c3a76d495090e1d3b6a2a84870d5c4605484385ae4302a221e29625405010f18b0aa028087465c25310f42c30a6b0486a143a7098f5150a0f39cc1a8a858698d60d5332a32e1318a99960e6358854cca1cbacc121865629c2434c832a64e121ca21951473591510ca92b9486a88654c9c24354432a4ae421aa219705424c9510cb8321a64a8865469cf6494032a34e7b22a01943a7690d500ca94b9086a8065c25093254032a32e129887a0c3a70d9732d070c29ac121a830e9c263d494183ce7306a4a0c38705963250686b90a6192838514d610c941c30a6b0064a0e1a6358354cc68cb84c62a6638598d6115331874e132e8598c3870595428c61cbacc1218634a9c24394831a18e6b22a418d257190d520c69538486a9063495c4435483192ae231a8418e0c63549420c782a928298863649c2434c431e0c86a926218d1a73d92500c68d39ec8a80630e9da4354031a62e221aa018d1873509500c788a0a62a80630e9c2639532183ce7304a990c3a70d9643c861d384c72a443079ce6095221874e1b2c8710c3a7098e544860f39cc12a2438618f6055121c36c6302a890e1863181544861c382c9a9a430e9c36590d21870e0b288690d197014c434870629ac421a438514d6110d219c2e030a6490c1c735954148670b80c498a43071cd64d4121874e131ca810c1e73982540868d386c9298430e9c36454c21a34e1b22a610c3a70d96430861cbacc1218438694e6090c21c32a73048610f0553d052108782a9a8290843c154f4248421e0aa6a124210d25759912108693baac890843611cd6448421b40e0b224210d6170d4d21086a2baca690843c19515348421e0aa8a9a4210f077454d21087823a2a690843c19915348421e0ac8a9a4210d257590d2108782a9c8690843689c24348421a4aea21a4210f055310d21087a0a9a4328043469cf6494021874ed21ca010c1e73d9150087912a242a8043c85512154021e84a690aa010f4153485500868d39ec8a80430e9da4354021e468290aa010f21414855008791a1242a8043c85092154021e44e890aa010f21744855008791b2242a8043c81912154021e448690aa010f20434855008706b10c529c81459c46294e40a2ae2314a72051a7018a5390287390c329c81435c86194e40c2ac230ca72051a701865390287390c129c81435c86094e40a2ce2304a72051571182539030ca9cc1a9481075da5314a40c2ca7308a520616535845290286b94a6194818594e610ca40c2ca6b08652061a53580329030ca9cc1a8c81075da5314640c1ca7310a32060e53588519028ab8ca618c818394e620c640c1ca6b10632061a53580319020f39ccb90c81079ce658864083ce732843
  | 2 => 0x250ca070130003d0ac0000000024003613f098563f8902800012c000010e2f05a03c00334c02c4001c8003d45b1311a454694b47e1145c0007f4c08c19c2351c793e4a4134005506c000103f48d001403c11636c470006d2d11b0013e450000e8fa00095000f40000050800188d30008309c5031d340007154800038d20fc123bd092b0d53dc5d245242fc000011f000004203e0005232c0017800558005240039400000004740000000000000b8dc0000a1cc000000011800000ea000893b52f020e93112300088000de4ecc20000c4301905c0049c5354c4f014000004e2c0d00808f000d9258540006e40c650002c3e037210870042d0015018ce30f132180d61e01a1001f4852b1214f144442889c128af4a48e018150bcae388353c8b9154da320b8265203b944011282f54b4883810897545113fd0f4b09249821415190d0fc0e48a528b32000d0ec00345253ac85190e12f90415cdf260822d5134f5453ec6f124c9198ce284a50a1460d800000030741826c1100030398b72a07b428314a8b2478ec000ad0010b275011d86a305315347a090f14e0004600000043000000a402000000000035c0017c00409550000006c00000334d53c0000030c0044000538000000b000161d0aa001373cc612e89e000d4000dd001362a4581d5125307d521174e414318a7078cf000e747143418e424c0022c0009422000ab2ece8105074e8e027c0020486000001a06b28d2e314a63307c400000002a505331dc00000001c09a00007000f6000002d83200000164004340b000e80c000081086030c04014050c0d00000018001a000581000000100c1a4b0682c020e0000038340080004500000844030302c62070001030000100c0601048000a0000000622001800160c2589454090080804040000000000200c7600000100e000080c0e000280800000004806160202002040480014050580c020106d327114a5090e98b88a5284874a9c85194243a52e428ca121d2a7218e5090e94b90c7284874c9c46394243a62e231ca121d1a7318a
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x1a000e150f1716133d001000353e282a2f02093f23313c250a0021372714300b2d22391f1c203b2e12050300003a240419010711000c000d3326001e0000002c293436061b38322b181d00000800400d14080810c04010480c0024400d060070a80c21625c46294243c21725846194243a098098d6215332909859c2434c832b028090d3254432a058214d610c941a098214d600c941a118098d6115331a058118d5250831911859c2434c431b028090d524c431911811cd4254031a098014d6210d21a118014d6110d21b0280dd15348421904875915348421b00805915348421921859c24348421d01539c24348421a20865d12154021b00835d12154021b0283d912154021a228690d2154021c05625c46294e40c05725846194e40a058294d610ca40a098294d600ca40a058194d620c640a118194d600c640a078558d2108640a058694d2108640e02534856008640c09735486048440c11735446048440891811c16210d30889821c16110d30891811cd6210130891811d93210130889821cd6110130889821d93110130d01729c4544c030d02725c4544c030d01725c4544c030911811d5424c030909821d5414c030c097358a6015220911811d4434c220911811d4434c120908855c8434c120c09535ca6090c20921829c24354420c09535c86050420c21725446050420909859ce4048020d02735464048020c11735866015210909821d4434c210909821d4434c110910855c4434c110c11535c66090c10921819c24354810c11535c46050810c21525c46050810911859ce4044010d027354a4044010
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 48
  | 5 => 1044
  | 4 => 1671
  | 3 => 343
  | 2 => 65
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
  | 6 => packedAt s4K6 (880+((h/16+packedAt s4K6 (768+(h % 16)*7) 7) % 99)*7) 7
  | 5 => packedAt s4K5 (32016+((h/348+packedAt s4K5 (28188+(h % 348)*11) 11) % 1666)*12) 12
  | 4 => packedAt s4K4 (69625+((h/557+packedAt s4K4 (63498+(h % 557)*11) 11) % 2006)*12) 12
  | 3 => packedAt s4K3 (17833+((h/114+packedAt s4K3 (16807+(h % 114)*9) 9) % 453)*10) 10
  | 2 => packedAt s4K2 (4047+((h/21+packedAt s4K2 (3900+(h % 21)*7) 7) % 79)*8) 8
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xf0fe3ffc1e3c7c7e3c78fc7f1c3871fe1cf90f
  | 1 => 0xff1fc3ffe03fff8fc07f1f8fe03ffe1e6331f3
  | 2 => 0x1ffc3fffc07ff1ff801ff1ffc07fe183ce3c
  | 3 => 0xffe0003fffff8001ffffe001ffff8001fc0fc0
  | 5 => 0xffffffc000000001fffffffe00000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x16028884444898800c182413048910cc0c5905
  | 1 => 0x20441008809020104021088420122410212052
  | 2 => 0x8880111080140029080112049004900828228
  | 3 => 0x42012aa250200925254a400192a50045540d80
  | 5 => 0x8cd1b3039d3a7249fa749e4803060d99fbf000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfee8fee8fce8fce8fee8fee8fce8fce8fee8fee8fce8fce8fee8fee8fce8fce8fee8fee8fce8fce8fee8fee8fce8fce8fee8fee8fce8fce8fee8fee8fce8fce8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37183
namespace PEqualNP.Outside.L_meta_37183
open PEqualNP.Outside.L_meta_37183.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x182aa5400008c48c38b00060a3d0005604f005e74d19045d10d48b4a160040fa14e00580141c41100b8d934a3890006100265418448c0060450020c0004067ff43fe43be43fd43fc43bc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x4617f544c37ea8984fd5130bf2a2617d544c2f8a8986f151309e2a261df434c37c86986f10d30ee21a619c434c2fea4985f14930dfa1261bd424c3be6498774c930bfa8a617c514c37e82986f50530ef98a61dd314c3f680986f90130de20261f8404c37080987ecc130ef182617f540c37ea8184fd5030bf2a0617d540c2f8a8186f150309e2a0617e530c37c86186f10c30bf290617d520c37e84186f50830bf288617d510c37e82186f50430bf28061be400c378801877cc030fd18061dd300c3f26018764c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c82faa7905f14f20df21e41bc43c837e85906f50b20bf28e417d51c837e83906f50720f790e41ed21c837c81906f10320bfaa441bf548827ea9105f95220beaa4417c5488378a9104f15220bfa9c417e53882faa7105f14e20df21c41bc43882faa5106fd0a20dea14417e51882faa3106fd0620dea0c417e508837c81106f10220fd18441f930883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a417e53482faa6905f14d20df21a41bc434837e84906f50920bfa8a417c514837e82906f50520f790a41ed214837c80906f10120fd18241f930483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20df21841bc43082fca4106fd0820dea10417e51083eca2105d94420bea8841f551082eaa2106fd0420dea08417e500837c80106f10020f790041fa20083da40107e48020bfaa6217e54c437ca9884f95310beaa621bd54c427aa9885f15310bfa9e217e53c42faa7885f14f10df21e21bc43c42fea5885f94b10bea96217c52c437e85886f50b10dfa0e21bd41c43ec43887d48710df20621bc40c42fea9086fd52109faa4217e54842faa9085f15210de2a4213c54842fea7085f94e10bea9c217c538437c87086f10e10bfa94217e52842faa5085f14a10dfa1421bd42842faa3086fd0610dea0c217e508437c81086f10210fd18421f930843f441087e48210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea6885f94d10bea9a217c534437c86886f10d10bfa92217e52442faa4885f14910dfa1221bd424437e82886f50510fb10a21f5214437c80886f10110fd18221f930443f440887e48110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c530437c86086f10c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810dfa1021bd42042fca2086fd0410dea08217e500437c80086f10010fb88021fa10043ea20087e44010
  | 1 => 0xa500c6faa018fe54031bca80637f54c86fca990ef953219f2a6437d54c877aa990cf55321be2a6437f53c86fca790df54f21be29e43be43c87788790efd0b21dea1643ee32c87da6590efd0721dea0e437e50c86faa190dfd5221bf2a443be548867ca910df55221deaa4433d54886f8a910dfd4e21bf29c437d53886f8a710ef90e21de21c437d528877e8510ef50a21bf28c43bf418877a8310fd8c621fa98c43ef21887ee4310df94221bea84437f54486fca890ef951219f2a2437d544877aa890cf55121be2a2437f53486fca690df54d21be29a43be43487788690efd0921dea1243ee32487da6490efd0521dea0a43f631487ea6290fdc8521f710a437f50486f8a090dfd5021bf2a043be540867ca810df55021deaa0433d54086f8a810dfd4c21bf29843de53086bca610df54c21eea98435d53086f8a610ef90c21de218437e520877e8410ef50821bf28843bf410877a8210fbc8421fb10843ed21087ea4210f948421bf28043fa50086f4a010df54021fca80437950086fca7a05f54f40df21e81bc43d02fca5a05f54b40dfa1681bd42d02fca3a05f54740dfa0e81bd41d02faa9205f94e40ef29c815e53902faa7207754e40aea9c81bf439037c87206f50e40de21c817e52902faa5206fd0a40df21481bd429037885205f94640bea8c81bf419037c83206f50640de20c817e509037e81207ed0240dfa9c81be539027ca7206794e408f29c81bd539033aa7206f14e40dfa9481be529037aa5204f54a40de29481bf329037c65206f4ca40de19481bf519037ca3206f546409ea8c81bc519037e63206f8c640de98c81bc319037e43206f88640de90c81bc219027ca1205fd4d40be29a81be435037886a05fd4940be29281bf425037a84a05fd4540be28a81bf415037a82a07ed0140df202817e54102fca6205f54c40dfa1881be431037a86206f10c40bf290817d521037e84206f90840dea1081bc42102fca2205f54440dfa0881be411037a82206f10440bf28081bf40103f480206f50040fca0081bf531037ca6204f94c40dea9881bc531037ea4206f94840dea90813d5210378a4206fcc840df19081bd321037864206fd4440df28881bd511027aa2206f14440df98881be311037a62206f0c440df90881be211037a42206f08440df280813e5010374a0205fd5330bf2a661be54cc27ca9985f55330deaa6613d54cc2f8a99877d0f30df21e61bc43cc3b887986710f30bf296617d52cc37e85986f50b30ef99661dd32cc2fca3985f54730dfa0e61bd41cc3be6398774c730df20661bc40cc2fea9185f95230df2a4613e548c2faa9186f552309eaa4617c548c2faa7186f90e30de21c617e528c2faa5186fd0a30dea14617e518c2faa3186fd0630dea0c617e508c3f681186f90230de20461f8408c370811877cc230fd98
  | 2 => 0xb7ea2a14fd4542df28a85bd5150b78a2a16fd4142df28285bd5050b78a0a14f14142bf2a0853e5410afca6215f54c42df21885bc4310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0215fd5332dfaa6653f54ccafca9995f55332be2a665bc54cca78a9996f90f32de21e65bf42ccb7a85995f94732bea8e657e50ccafaa1995fd5232bf2a465be548ca7ca9195f55232deaa4653d548caf8a9195f54e32df21c65bc438cafca5196fd0a32dea1465df328cbde65195f94632bea8c657e508cafaa1195fd5132dfaa2653f544cafca8995f55132be2a265bc544ca78a8996f90d32de21a65bf424cb7a84997bcc932ef192657f514caf8a2995fd4132be282657f540cafca8196f950329f2a0657d540cb7aa8194f55032be2a0657e530cb7c86196f10c32bf29065bf420cb7a841977cc832f719065dd320cbda64195f94432fb2886576510cafaa2197d54432baa88657e500cbf4a0195e94032bea8065f9500caf2a0195f94f41bea9e83bf43d077c87a0ef50f41de21e837e52d06faa5a0efd0b41df21683bd42d077885a0df94341bea8683bf53d077ca7a0cf94f41dea9e83bc53d077ea5a0ef94b41dea96833d52d0778a5a0efccb41df19683bd32d077865a0efd4341df286833e50d077aa1a0ef14341beaa4833d54906fca720df54e41df21c83bc43906fca520df54a41dfa1483bd42906fca320efd0641fba0c837e50906faa120dfd4d41be29a83bf435077c86a0ef50d41de21a837f52506f8a4a0efd0941df21283bd425077884a0fdd0541df20a837f50506f8a0a0efd4d41df29a83bd5350778a6a0cf14d41dfa92833f525077ca4a0ef54941de29283bf325077c64a0ef4c941de19283bf515076ea2a0efd4141df28283bd5050778a0a0cf14141bf2a0833e54106fca620df54c41df21883bc43106fca420df54841dfa1083bd42106fca220efd0441fb20883bd41107ea8220df94041bea80837f54cc77ea998cfd5331bf2a6637d54cc6f8a998ef153319e2a663be43cc7788798df94b31bea9663bf42cc77a8598f7ccb31ee99663bf41cc77a8398df94331bea86637f548c6fca918ef952319f2a4637d548c77aa918cf55231be2a4637d538c77c8718ef10e31bf294637d528c77e8518ef50a31bf28c63bf418c77a8318f7cc631fb98c637e508c6faa118dfd5131dfaa2633f544c6fca898df55131be2a263bc544c678a898ef90d31de21a637f524c6f8a498efd0931dea1263df324c7ba6498efd0531dea0a63f7314c7bc6298dfd4131be282637f540c6fca818ef950319f2a0637d540c77aa818cf55031be2a0637e530c77c8618ef10c31bf29063ee520c6dca418df54831f6a90636d520c77e8418ef50831bf28863bf410c77a8218f7cc431fb18863dd310c7ea6218df94031fd280637
  | 3 => 0xd40000000005ba0007fc04a0000007426a27b400072e00010c7c00ae0567d40003e60001e000013a00046a3805100007144b60006208001043ac7240002b025a16c3a868c00068481e1880000000ce59a00020a14600067600073c6da55e000008000020000040080d002000008000000000200000207000001016000070050040200380300e0000080200e00402000000010018050000000080000c0040080000c0080400500e014000000140040080501400000000004000028000000080200401800c00006018000000000000000000000a0040000600001008002000008010020100200600300001403000004014010010060100000100000c0180000a0080000600e00c008070000040080100000c01001000004000000060000100100201c0000400002c0480200001400017004020020020000080180100c0000000000003c0080600200000805000000000010000180400000400c02002000000008000000040080000000001805008008000010000300000000200004800012010000000040000600000201000004002024000080000080080500a0080080001200c0000000a058000150000100080a0040000081100000000001000020008000000380280300a0100000d00a008000020000140200000600c0000300200000004000008000000000040080300200002800000018020000020080200100a0000000101c000018010080000100300400401803004020040030040080101b000004010010000140000600a00000003006000010010020140100200400000000bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121fe94243bd284877d5090ff2a121de542439f29c87bf5290f7ca521ef54a439ea9487bc5290f7ea321ef94643dea8c873d5190f78a321efd4243df284873e5090f74a121ce94243dea8487b95090f78a121f7d0d43df21a877f5250ef8a4a1dfd4543be28a877f5050ef8a0a1df95043bf29887bf4310fbc8621ef50c43eea18877e5210efaa421df94443bea88877e5010efaa021ef94c439f298879e5310f7ea421ef94843dea90873d5210f78a421efd4443df28887bd5110e7aa221ef14443dfa8087be5010e7ca021ef54043de280877e53d0afaa7a16fd0f42df21e85bd43d0b7887a15f94742bea8e857e50d0afaa1a16fd4f42df29e853e53d0b7aa7a16f14f42dfa8e85be51d0b7aa3a14f54742de28e85bf50d0b7ca1a14f94342dea8685bc50d0afaa9214f55242bf29c857d5390b7c87216f10e42bf29485bf4290bde85215f94642bea8c857e5090afaa1215fd4d42be29a85bf4350b7c86a16f50d42de21a85ef4250b7c84a15fd4542be28a857f5050af8a0a16fd4d42df29a85bd5350b78a6a14f14d42dfa9285af525
  | 4 => 0xa80a7544ca02a4e82605d64660000000001ce00033c00000012e00056000000000052600000041e00000000015200000006208a00019800000080e45a12439a4142d00c00008120000001b000009600000000000000000059404475a6ae6be3922ae71a00015430a4ac2e81722306a06fc6c042c5d25ce3b000000000040e34073e5926700006785ac34400000031e4f637e19e70c00027000077c5240f00005bc00079a5700007260000000000ea68806a0740667dc0000f64e400011800000c72a2180007045f20005066ce0b601e6ca4dc29c0fe0001ac6b200034c52a0003542de00000000051608e0982002ba00000000002e00000049050c3ba0000000000005a446c2ea0722fa00077448627800025200018400000076a1943ec4681a47ae0004523d20002361105560000000d071c3a40002d200068a0000000002c20000000000e869e00000000065c0005685be00044c58c17e00037800013851400069847228062a0003b87de00051a40849827a09a8107925d04c60c800067e4400007c82040540000d43624424b80000002142f27a211a02263400000000000000036e00e00000060232e1c040212000000000076c49c0007aa00039e6a41160004f40000003c80003840001c648479e1e80005da0002220000000000003560000006f80000000000000000fc00054a00000025404c1268180000006b40000000000000007644e60000000000366ac52e00000000000000000000000000000050a4c40000001ae00016018e3280000000006dc6fe69267c7ce0000005ec00005c6a82d80000007a43900005803b479018000000076825e0000005a278e00028233e0004121403cc1e622c6fa6e050e6a63e80002a234e50466c33a6227380000000000000000002261ec20870e5b436800051800064840c32015e0604a65fc7a063e2a04ec2f01a645e3a000004e00002051c4f057e00000000000046e0006e600000041c0005860004ce20c0000003ae1d423849429800068e4180004fa0000000000005a000000035c3f80001f000056c60e82259626e2945901d80002dc4280003860000000000480e200000000011249e0001e22f400000058e0000007723166740340000004d87700003a62280006ec7ca0005b67d82a47e800014257400042000005217c7b677a3740000006080008020000007bc7227065b864c21c48e6d00003465004da0001a21486b06e20004a247c3e20000000be47800036a0000120b41fa48800000078c55a00061c09c0a440645c48c2be70a10e2960cc3221220003606506421864764925986620404640007567c67be0003de6b600839c0062400002441d61b80ba16460c4227345f40000005ca0000000002c600000013050843676600000000000021a5b232c6800001140000003aa00056e2025e20323
  | 5 => 0x2687780000003d662c4fe6c24b44460000007ec00074a00000028672c7d61780004b02f624c2500007c41f800000031c0000000005de3fa5f00001dc0006260000000005c038a0000004743484626f20a848059e55400014c3984be35a7d228800007e6520381a00000a00003000000005a816e00000000000000000007c6f060a7e640071e22a5c21b40006040000000002b80000d800000010a00000007a4300007fa00071657259c01424654c6727e07f03881c80004c26147980000003060000000000000004e06820007622581d23a261a0002e200073a00000055c0000005ea0000a60000f40000000000008245400000ac75c0000000006640000001e40000002c813e00000000000000031064024847e00012a2b20007506246d600071266e1b223a13443863c16856478a1960000003d00000b267a0000000006180002646de0000000000001da66a76e0002900007b80005760000000000000000000000000000000006585c61580004ea7e40000005480882b466634240a73000000043c0005380000000000002a60862162745e481414a0000005360423c441a0644a40bc7881ee6361aa00064e0002ee69c3965d80943940000004cc0000004600000007581763ea5780006e80ee1fe6bc4a80002ca0000000007b27200005fa0000000002127f80006ee00000081600012c79c53c1820843b668600000027647a7600002320240007c200062e7a80000f20004d42fc3f226c0008204b256a6107820fa7084f20002da0000002924d200043e30e0e43720000005e07ea1a80ca0001f24563f681c0281cc2d46ea51261e5f82726122c065e0000ec5ae29e6cc4963506b84040d27286f68084825025cc4aa7b000012800021052c00023e00024e4340264e233048a0502ce2ec44e74c0000003380000002561740826d40c411e00080c2423dc0000000002fe7f403c6c40000e04486c65500000000004de7d028a00000065419c55235e38206879464a09e0000003e424a6f417a7f608c57a7525a62e03c05325e614e2aa0001f40006d80040004bc00045800071000000000070238e00000000000000000000033200000026a42e35836c63000036600008034a74615c4441c40d61be3020006284f800037000000000065a00019a0000100002b653a0701d01c280654e0004263be0f85467440460000763e02c41067fe25c63a11c75e27c2ac4325b063258200000000000041009205e0000000000000003180001000007a60001505dc0b833454400031421e2340006ba00000045458458a81a03a27e0da0000004c00002e40003ca00074838c0001367f201630c2201b60001901ca00000000077600032a0000000000000dc0007da00000069a6444240300000000000007861de06c0000000001fc2060780000000e60006aa00000049
  | 6 => 0x26200001c58800a2246460000003c20001ba00000028c0c20004700000900000000000000000000000003fe0000000000000a257c3b20000003086060006900001560de4507001bc00000000000000000005871828e0006560000001320000000000000003ee61615a37a69603e0025c85e83d81ea01873610244a5423643524c80007ee5c44ba7ba18a4a00004d03c60001f60008046e400019277e00000000014437c13c0aa20e00000016a31a0006380000000000002660005d40004fc06e00000037600000022e0000000005620000000000b023c7ac2e64ee3364d61625587320005ee0004ae5203fc0006d26685660000005aa7cc0007400005fe0003f066005a0000003264165220c679642a0000002840002bc3ce0008262d63f401a0002cc43a00018c0006c83127843da5347e216629a7802f85280000003045f60002a86943bc00053e53000000060000000000000010802c00000017032451e00000074e
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x3538423d64d4e108f992538423d6494e108fd91538423c6454e108f996438423c6590e10ae982438423e6510e108f194438431e5310e10c754c43842ba6010e108f992528423d6494a108fd91528423c6454a108f990528423d6414a109798c528425d6314a108f997428423c65d0a108f995428423c6550a10ae98341842b86050610a798e40842b56190210ad5844084338548c210ce1513084358534c210e610d308423e63d51108f58b544423e64951108f994544423e63151108f588544423e60151108f180544423e64d4d108f593534423e6494d108f592534423f6454d108f191534426f6254d109b189534423e6590d108f19643442ba6090d108f994434423c6510d10ad58443442ba6010d108f992524423d64949108fd91524423c645491097d8d524425c63549108f990524423d64149109798c524425d63149108f997424423c65d09108f995424423c65509108f99741442ba60d05108f19541442b860505109d195214436452485108f996404429e63901108f9944044338548c1109e1953044338544c110d614d3044398434c110bc18530442786548110f8485204425e63d50109758f540426e62d50109b58b540423d65950108f98e540423d62950108f18d540423f62550108fd85540423d61550108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7d92530431c6494c108fd91530423c6454c10c7951530431d5454c10c7d91530431c6454c108f990530423d6414c109798c530426e6214c109b588530427a6014c108fd96430423d6590c10c794e430431d5390c10ae982430423f6510c108f594430431e5310c10c754c430423e64d48108f593520425e63d48109758f520423e64948108f592520426d6594810cb952520432d5494810d394e520434d5394810cb992520432d6494810cb90e520432c4394810cb951520432d5454810d394d520434d5354810cb991520432d6454810cb90d520432c43548108f990520423d64148109798c520425d63148109b988520427661148109e980520423f65d08108f597420431e53d0810c754f420432e52d0810cb54b420423f65508108f595420431e5350810c754d420432e5250810cb54942042b860508108f992510423d64944108f597410431e53d0410c754f410432e52d0410cb54b410423f6550410c794d410431d5350410cb949410432d52504108fd96400423d6590010a798e400431e5390010c754e400432e5290010cb54a40042b561900108fd94400423d6510010c794c400431d5310010cb948400432d5210010ad584400436552c40109e59610043595384010da54a10042776544010d954910043b240440109ed9510043595344010da54910043b14144010
  | 1 => 0x823f64546208f191518823e65d06208f195418829e6390220ab58a40882ad6210220ce1523088338544c220d614d3088398434c2208f98f544823d61d51208f992544823e65151208f98c544823d61151208f993534823d64d4d208f992534823d6494d208fd91534823c6454d209dd8553482746154d208f996434823c6590d20ae982434823e6510d208f19443482ad6210d20ae980434823e65d0920ae983424823c6550920ae181424823e64145208f590514825e63145209758c514823e65d05208f197414823e65505208f195414836451485208f996404829e63901208f9944048338548c1209e1953048338544c120d614d3048398434c120ba189304825e63d50209758f540827661d50209d587540823d65950208f98e540823d61950208f18d540823f62550208f589540823f61550208f990540825e63150209758c540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7d92530831c6494c208fd91530823c6454c20c7951530831d5454c20c7d91530831c6454c208f990530823d6414c209798c53082766114c209d584530827a6014c208fd96430823d6590c20c794e430831d5390c20ae982430823f6510c208f594430831e5310c20c754c430823e64948208f592520823d65d0820c794f420831d53d08208fd95420831e5350820c754d420823e64944208f59251083365494420cd55251083565394420d554e51083366494420cd59251083364394420cd10e51083374294420cd50a51083365454420cd55151083565354420d554d51083366454420cd59151083364354420cd10d51083374254420cd509510823f65d04208f597410831e53d0420c754f410833651d0420cd547410823f65504208f595410831e5350420c754d41083365150420cd54541082b860504208fd96400823d6590020a798e400831e5390020c754e40082ad6290020cd946400833551900208fd94400823d6510020c794c400831d5310020ab58840083365110020cd544400836551c8020d654e200837151880209bd9520083655148020ea901200827b6548020d654d20083a94248020dc545200823e63953108f58a54c423c63553108fd8954c423e64d4f108f59353c423f6454f108f19153c423e6414f108f59053c426e6214f109b58853c423f6590f108f59643c42ba6090f108fd9443c423d6510f10ad58443c423e64d4b108f59352c423e6494b108f59252c423e6414b108f59052c425e6314b109758c52c423f65d0b108f59742c423f6550b108f59542c42b86050b10d914921c429e63903109798f548425d63d5210a798f548423e63d5210c798f548421e63d5210c758f548423d62d5210cd587548433a60d52108f98c548423d6215210cd584548433a60152108f99
  | 2 => 0x62d51308f587544c33960d51308f992544c23e65151308f98c544c23c63151308f588544c23d611513097997434c2da60d0d308f996434c29e6390d30ae982434c23e6510d30c7d50434c29e6510d30c7994434c29d6210d30a7584434c39b6010d30a7980434c3986010d308f990524c23d64149309d984524c27561149308f997424c23c65d09308f995424c23c6550930a718d424c2b86050930a7193324c29c644c930d3149324c2d8604c9308f990514c23d64145309b988514c26d62145308f997414c23c65d05308f995414c23c6550530a718d414c2b86050530a7193314c29c644c530d5145314c2d8604c5309e997404c2da63d0130e610f404c23e6590130a798e404c2ba60901308f994404c33b5410130e6d0c404c3984310130ae994404c33a6510130e6d8c404c2ba6310130e618c404c2b96210130e6cc8404c3993210130ae584404c39b3110130e64c4404c2ba64cc130e610f304c29e648c130e6102304c25e63d50309e983540c23e63d5030c798f540c21e63d50308f58b540c23d61d50308f983540c33a60d50308e983540c26e62150309b588540c27661150309d584540c2ad6215030ad584540c23e6315030c798c540c32e62150308f588540c32d62150308b588540c33661150308f584540c33561150308d584540c23e6015030ce980540c23e6494c308f592530c2ba6090c30c794c430c2ba6010c308f992520c23d64948308fd91520c23c64548308f997420c23c6550830cb949420c32d52508308f992510c23d64944308fd91510c23c64544308f997410c23c6550430cd945410c33551504308f992500c23d6494030a798e400c23e65100308f194400c29e6310030ce940400c31c54cc030ce152300c2d9638c03097d95300c31c544c030e6901300c398404c0309ed95300c338544c030e690d300c398434c030b6d95300c35b654c030e6d91300c398644c030e6d51300c35a544c030d6151300c398544c030c6151300c359524c030e6d09300c399424c030d6545300c39b414c030e6505300c23e63953208f58654c823c63553208fd8554c823e64d4f208f59353c823f6454f208f19153c823e6414f208f59053c82766114f209d58453c823f6590f208f59643c82ba6090f208fd9443c823d6510f20ab58843c823e64947208f59251c823f65d07208f59741c823f65507208f59541c82b86050720a798e40c825e63d52209758f548829e63d52208f98f548831e63d52208798f548831d63d5220cb58b548823d61d5220ce983548823e6315220cb588548823d6115220ce980548823e64d4e208f593538823e6494e208f592538823f6454e208f191538823e6590e208f19643882ba6090e208f994438823c6510e20c794c438831d5310e20ae98043882ba60d0a20ae181428823e64946208f592518
  | 3 => 0x640a798c519029d6314640c794c51902ae6214640ab58851902ba60146408fd97319031e53cc6408f996319023d658c640c794e319023f654c6408f195319031e534c6408f994319023d650c640c794c31902ae620c640ab58831902ba600c640ae580319023e65c86408f597219031e53c8640cb54b219023e65886408f596219031e5388640cd546219023d6548640c794d219032d5248640cd545219023e65086408f594219029e6308640a758c219031e5308640e948421902ba6008640ae580219031c5390d40ae982435023e6510d408f997425032f52509408f99741503375150540a798e40502b96090c408fd95431031e5310c40c754c43102b96010c40cb54b421023d6590840cd547411023d6590440b658e401023f65500409ed9540102ba60d4c408f58a531023d6194c40ce982531031d5314c40ab98853102ad6214c40ad98453102b56114c40ae98053102ba60d48408f18d521023f6154840a798c521029d6314840ad98452102b56114840ae980521023f65cc840c794f32102ba60cc840ae583321023e658c8408f596321032d528c8408fd95321023c654c840c794d321032d524c8408f994321023d650c840ad98432102b5610c840ae98032102b9600c840ae983511023c63544408fd89511029e6314440a758c51102ae6214440ab58851102ba60144408fd97311031e53cc440ae98331102b960cc4408f996311023d658c440cd546311023f654c4408f195311031e534c440cd545311023e650c4408f59431102ae620c440ab58831102ba600c440ae580311023e65c84408f597211032d52c84408f996211023d6588440cd546211023d6548440cb54921103355148440aed8121102b860484408f994211023d6508440a798c211029d6308440e948421102ba6008440ae580211029e6394040a758e501031e6394040c758e501033a6094040e698e50102b96394040e658e501029963940408f58a54cc23d6195330c718d54cc23f62553308fd8554cc31d54d0f30ae98243cc2ba6010f30c799443cc31d6510f30a758843cc29d6110f30a798043cc39a6010f30e658043cc23e6494b308f59252cc23f65d0b308f59742cc23f6550b308f59542cc29c6350b30a719332cc29c644cb308f99251cc23d64947308fd9741cc23d65d07308fd9541cc23d6550730a718d41cc29c64cc730a719131cc29e63903308f58a548c23d61952308fd89548c23f6155230ce181548c23e6494a308f592528c23f65d0a308f597428c23f6550a308f595428c2b86050a308f992518c23d64946308fd97418c23d65d06308fd95418c23d6550630ae181418c33954d0230a798e408c29e6310230ce994408c2b96510230ce594408c2ba6310230e698c408c3996310230ae588408c2b96110230c7953308c2ba64cc230c758f544c23d
  | 4 => 0xb19532486e4614c921ab58b414863f65505218f59541486af62505219d19531486e4624c521f14c9314863e64d41218f593504863e64141218f590504865e63141219758c504865e63d50219758f540867a60d50219e583540863d65950218f98e540863e60950218f18d540863c60550218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21c7d92530871c6494c218fd91530863c6454c21c7951530871d5454c21c7d91530871c6454c218f990530863d6414c219798c530866e6214c219d984530867a6014c219e580530863f6590c218f596430871e5390c21c754e43086ba6090c218fd94430863d6510c21c794c430871d5310c218f992520863d64948218f597420871e53d0821c754f420863f6550821c794d420871d53508218f992510863d64944218f597410871e53d0421c754f410863f6550421c794d410871d5350421d354f21087555388421b958a210866f6548421d354d21087a74148421e950521086776548421d554d21087a74248421e950921086e76548421d9d9521087a66448421e959121087a65448421e955121087675348421f194d21087655348421f154d21087455348421e990d21087a44348421ce95250087395494021d694e50087595394021f8486500873b6494021ce192500873a4394021ce10e500873b4294021ce50a500873b4194021ce506500863f64540218f19150087652154021ce95150087395454021d694d50087595354021f8485500873b6454021ce191500873a4354021ce10d500873b4254021ce509500873b4154021ce505500876b2154021dc88550087692154021dc48550087612154021ae98243d031e5310f40cb54b42d033551d0740c7d92539031e53d0e40c794e439031e5350e40c754c439031e53d0a40c754f429031e5390a40c794d429031d5350a40cb549429031e5310a40c794f419031d53d0640c794e419031e5350640c754d41903355150640c794c419031e53d0240d654f40902ba60d4e40c7d4e539023d6294e408f586539031f6294e40c798a539031d6294e40c718a539031f6194e40c7986539031d6194e40c7186539031e6094e40c7182539031f6554e40ae980539029e63d4a40a758f529031e53d4a40c754f52902ba60d4a40c794e529031e5354a40c754d529023c6354a408fd85529029e6314a40a758c529031e5314a40ad98452902b56114a40ae980529023f65cca40c794f329023e658ca408f596329031e538ca408fd95329023c654ca40c794d329023e650ca408f594329031e530ca40ad98432902b5610ca40ae98032902b9600ca40a798f519029d63d4640c794f519031d53d4640ae983519031e5394640c794d519031d53546408f18d519023f6254
  | 5 => 0x548c63c6055231ae982438c63e6494a318f592528c63f65d0a318f597428c63f6550a318f595428c69c6350a318fd91508c63c64542318f58b544c63e60d51318f992544c63e65151318f588544c63e60151318f996434c6ba6090d318f994434c63e64149318f590524c67a60149319e580524c63e65d09318f197424c63e65509318f195424c63e65d0531a798f414c63c6550531a718d414c63e64d41318f593504c66e62d50319b58b540c67a60d50319e583540c63d65950318f58a540c63e60950318fd89540c63c60550318f990540c66e62150319b588540c67a60150319e580540c63f6590c318f596430c6b56190c31ae982430c63f6510c318f594430c6b56110c318f992520c63d6494831cb952520c72d5494831cb992520c72d6494831cb90e520c72c4394831cb951520c72d5454831cb991520c72d6454831cb90d520c72c43548318fd97420c63d65d0831cb94b420c72d52d08318fd95420c63d6550831a718d420c72e5250831cb549420c63e64944318f592510c63d65d0431cb94b410c72d52d04318fd95410c72e5250431cb549410c74d52cc431d954a310c65f654c431d3549310c795414c4319dd95310c796434c431d9549310c73a5494031ce552500c76a5294031da54a500c73b6494031ce192500c73a4394031ce10e500c73b4294031ce50a500c73b4194031ce506500c63f64540318f191500c73a5454031ce551500c76a5254031da549500c73b6454031ce191500c73a4354031ce10d500c73b4254031ce509500c73b4154031ce505500c75b3154031d64c5500c63e63953218f98254c863c63553218f18154c863e64d4f218f59353c863f6454f218f19153c863e6414f218f59053c867a6014f219e58053c863f6590f218f59643c86ad6290f21ae98243c863f6510f218f59443c86ad6210f21ab58b41c86af62507218fd9150c863c64543218f98e548863e60952218f18d548863c60552218f993538863d64d4e218fd91538863c6454e218f990538863d6414e219e98053886796014e218fd96438863d6590e21ad58643886ba6090e218fd94438863d6510e21ad58443886b561d0a21add85428863f64542218f191508863e63951218f58a544872d62951218f586544873561951218f982544865f63551219718d544867b60551219e181544869c6355121ae181544871f63551218f18d544871c63551218718d544863f6255121cbd89544863f6155121cdd85544873b60551218f181544873860551218e181544863e64d4d218f593534863f6454d218f191534867b6054d219e181534863e6414d218f590534867a6014d219e580534863f6590d218f59643486ad6290d21ad58643486ba6090d218fd94434863d6510d21c7d4c434871c5310d21ab58843486b56110d21ad58742486b761509219
  | 6 => 0xa3d64946328fd91508ca3c64542328f587544ca3e60d51328f992544ca3e65151328f584544ca3e60151328f996434caba6090d328f994434ca3e65d0932a798f424ca3c6550932a718d424ca3e64145328f590514ca7a60145329e580514ca3e64d41328f593504ca7661d50329d587540ca7a60d50329e583540ca3d65950328f586540ca3e60950328fd85540ca3c60550328f990540ca7661150329d584540ca7a60150329e580540ca3f6590c328f596430caad6290c32ae982430ca3f6510c328f594430caad6210c328f992520ca3d64948328f597420ca3f655083297d95320cb8d424c8329bd95320cb8e434c8328f992510ca3d6494432cd952510cb355494432cd992510cb356494432cd90e510cb344394432cdd0a510cb354294432cd951510cb355454432cd991510cb356454432cd90d510cb344354432cdd09510cb354254432d5cc9510cb663254432d54c9510cb653254432ce952500cb395494032dc946500cb715194032ced92500cb386494032ce90e500cb384394032ced0a500cb3942940328fd91500ca3c6454032ce951500cb395454032dc945500cb715154032ced91500cb386454032ce90d500cb384354032ced09500cb394254032d6cc9500cb5932540329e98253d06796094f41ae98243d06b96090f41c794c43d072d52d0b419798e50d065d6394341ad58753d06ba6094f41ae58253d063d6294f418f98253d073a6094f418e98253d07396094f41ad58453d06b561d4b418f18d52d063c6054b41ad58452d063f65ccb418f99632d063d658cb418fd9532d063c654cb418f99432d063d650cb41ad98432d06b5610cb41ae98032d06b9600cb41a798e50d069d63943418f98e50d071e63943418798e50d071d63943418f58a50d071e5390e41ae982439072d5250a418f997435071c5390d41ae98243506b96090d41cbd49425063e6510941ad58653506ba6094d41ae58253506b76154d418f588535063e6014d418f98f525063e60d4941ad586525069f6354941a718d52506b76154941aed8152506b860549418f197325063e658c9418f596325071c538c9418fd95325063c654c9418f994325063d650c941c714c32506b6610c941ad58432506ba600c941ae580325069e6394141a758e505063e63141418f588505063d6590c41ae982431071e5310c41cb54b421063f65508418fd9541106776550441cd951411067a60d53319e58354cc6ba60d5331c798f54cc63d62d5331cd58754cc63e60d5331ce98354cc63a60d5331ce58354cc71e63153318f58854cc73561153318f98054cc6b56190f31ae98243cc6b56110f318f99252cc63d6494b318fd9152cc63c6454b318f99742cc63c6550b31a798f41cc69c63507318f99250cc63d64943318fd9150cc63c64543318f58a548c63e60952318fd89
  | 7 => 0x600400102001401001000000000000000400f0110180080e82b002008008010080180001201e0680900100a04c0181405e00c0181700007c000190220080100500a0f00000e000080080150040003200603c0040c80000c00c0a80000200004808008000018050020100004200600c03803002010000000080000200401e0000380200003c0080200e00c0c8000040100100e00204000002008028010040000183b0030100040200a00801001803024000000010000cc000000000200880400005c0c0010080180080b01c00c0180400a0100080f00c010008090020180080006010409000000008010050020000082100c0840000403c000018030380033b6494243ced0e5090f5b4354243ae9835290eb960d4a438fd855290e3c6054a43ad9845290eb56114a43ae9805290eb96014a43ae9835190eb960d46438fd895190e3c6054643ab9885190ead6214643ae9805190eb96014643ced425090e3d62942438f5865090f3b5294243ce94a5090f395294243ce14a5090f3b5194243ce9465090f395194243ce1465090f386394243ced8a5090f3a6294243ce58a5090f386294243ced865090f3a6194243ce5865090f386194243ced955090f3b5254243ce5495090f3b5154243ce5455090eba6090d43b65824310e3f6550c4397d954310eba6094c43ae5825310f1e6394c43ce9825310f396094c43e69825310e9d6094c43e65825310e996094c438fd855210e3c6054843ad9845210eb56114843ae9805210eb960148438fd895110e3c6054443ab9885110ead6214443ae9805110eb960144438f58a5010e3d6194043ab9885010ead6214043ad9845010eb56114043ce5405010e7a6094f429e58253d0aba6090f42ae58243d0b1e5310f429798e50d0a5d6394342ab58b53d0aba6094f42ae58253d0a3d6194f428f98253d0b3a6094f428e98253d0b396094f42ab58853d0a3c63547428f18151d0a9e6394342a758e50d0a3e6394342c798e50d0a1e6394342c758e50d0a3d6194342c794e4390aba6090e428f9974350b1c5390d42ae9824350ab96090d42ab58a5350aba6094d42ae5825350aaf6254d428f5845350a3e6014d428f98f5150a3e60d4542a7d8d5150a9c6354542aed815150ab86054542a798e5050a9d63941428f98c5050a3d61141428f5964310aba6090c42c794c4310a3f65508429bd954210b2e54508429e98354cca7960d5332ae98354ccb1e63d5332cb58b54cca3d61d53328f98354ccb3a60d53328e98354ccb3960d5332c798c54ccb2d62153328f58454cca3e6015332ab58a43ccaba6090f32ab58843cca9e63d0b32a718d42cca3e64947328f59251cca3f64547328f19151cca3e64943328f59250cca3f64543328f19150cca3d61952328f982548ca3f61552328f181548caba6090e328f992518c
  | 8 => 0xc10ab1900fcd49c070f556ec75821c8180c8fec0017dd61d14d9216357ec6d83a1139038aecf047140011c95f400c89c97186550581c000000530e4cebc67573c09ca2936143817c0e85115dd2fc4c55f96cd75511442507d3210c0a30df4f087e400031d654a3572916d378e2c15c68cbb8e00000c50cd091862461c5bc9b5974e152b81e0575164000ce86347d56d8a005c52840000018000016e8a782d0e886091d58e50bd9f8e9c438e5da10c457c4504d195907d997cbfc4ed7a189803c4e404cbc89c0470d60f4d62c7947f04dcd2c71894c0007ad83070d67588994c838b8800052400000023528cf98000000eb81593000015457782b96b93389995cc440f597944b127c3f8f140008b52f12049a0a9d1446956a881c9e4b556a18bd8c44052a4264bccbf1100dd124ca3c3516f588c8a10d88341c0d9cb3c038000ad9684198a8c5d573158c1f1970224464000c680018dc97957c0006bcf38d095a8de406d99c0010840015654b8d31a18000c8c9ad0357459dd708000b8c80402037548477496c21039cf31638a2c7440017159c5481618f0140059c00026d5509481f8e297d423c0e0dad9900000000001651340000011600016200000000000000002ad530b14000bd8c556d12a12c44857804cc000000d8159800027000156085191d9e80110ad6315c4001790e1192c34cdf88f0abc398b0ce714f83856012700000380301800010000000000010040000500280800000000008002000000070700100a80006e02c000000000001500000a0001680600205c0380000200c0080000c0000200100a0080e80700000c038010120200000001403008808004000030080000280080b0080200b00600200c2e0210040000801400000c0980100207006800086000000210100740001c0000000b80100018801832002004000110040bc0b80500e0041a00000c0880000000a040038000220140700e00c0200480d00c00800004012004008010400001500400c0040001207800000803002018008030140000081d00c00400002022010008040000180280504800800023000008018360060080280000a06c1f006014000008030040180181d0040000582f00006c00801056014000020140280402f0040380000c0020000000100e000018190080480a005000014038060580000000b0140000500103204c00021000008000000000040601600000c0180301c00409002000028068080140740000000a00004806042080000030040f80180f002048038010080000080200400400029024010090000041a0010170080040100001601807802014034038070100e00100b00e0140780603c04c0b00002200c00000030010050060100200200400207c000090020140680502a0380000400000404800000004018020100040180100a0000001300
  | 9 => 0x60a6d5340013240000000000009fd1f83a8b5c2986a99819a8b817640008d106504465c0003705657411a4000b30984ee51dc2e02f9058000454000a04edc000768a746a00000000306ac00000035cb90428a087009e17a4b9c0014fc1dc000000bac0004315b184544800119594400100927554c1e4000d84a1cac99644a48ac0000014e44e801cff800165d5a43ac2b52b533d54172d0a552d860ff0cd4fb40f1738820ab9240b44eb13c81a033c6602147983fd5752101ed18ce7456ca6444939c208914c482805b86e872c0b03d55390414c0584000cf92a96acdc8698d1c001774a940ad1acdc4be804411cd94238a380010b8000940c1d500ba0bd054cc206dd15c0018a90b40012781518cce2509d474000f34c058217242bd32828544460cdcc188001029850000000f680013a12605e8f74b70ae40000005b17b0ec800000171d23400000000002c000000000ac51500000007ed380115880000119308588e4076162450d518000a48ff47883b479d1b85350c800112452c7416c81358588c1010d10828c84bbc1b19e0185a14cad2d8a40fc8db56e4fe9608e640000015ac8a8000304770000ea00014ecd397c8a7199420c000bf873555919d258c158ed9385540011849b15105d05ec62800053d7683bd74d3650e800000000040140c2f095985cc5c000000000000cf446d70587cce404901c2185787fc6580001100012002cd4b1760709190c310ec900000eb44fc0010c5450a6832d811568248000c24d4412841c000d70d787d17b81a455d7706790d50208cc59417000157800106c00073cfe03100017200dc7644d8338e84c958f49c4f2cf949f55216704589a8eccc80c98fd92f5440160c58120024b3482436c4f8c0d8d94943943f43a4f44a1000051c7c4378ce0d5120d91930cb6d68c644f659347105d82ecf618b80b4e353943c82c99480d02942d8ef4b08fc418d3100005ad0555e400135d12ca54b205c125c1c89b8a60aa43ec0000007dc180cb1264d20a50a210193710800005f8c000000015156951280013d947cbed188c18000c2c001108fb8c7800109887101466c001420480000eec811854d585586b4784000a180015289304e126ce9400000000150c000c612d19f4000000af400092d491a04ab57196448ec2547288b06f57f16f8000d2407c4a9314d64b1c0000012e9525914be0d011b000175995ce914e89380757a9391408ef11114295a0908e383141b83d80403453d57e07a413cd6cdd80c4000ea93e56a42791d86852f81d4e217005f4a4c6a58fd3ec6903180010fc27c87800146cb780003248e17fcfa0e798856103408489d82dcdbca453042c457d4dc0f4d897110d159c82cd347bc474000380f8c4a11ed0cc00000000044d1d12214a10e13bc258f4063c5fc001319838890124d0d55d2ec3e0
  | 10 => 0x12ac094afd3c425c140904830cb82a87a979d09442cca090d8d079091c48c10169d04c5608fd77c168cc8be51e8b38b4d8c11f56043c40e4231288274aa03d024038d0915715f1818d409f0a9910d4ad98cdb84d46c0c38fa80011e0f90b2cc40b64b680009c8000000e800007ccb1067d9c040cdd4d741e8d1584c0000840008c4ddc2a132d6dc0cd6909ec8400019cd07000000000000000129983d2b0000bdc000061074894000000000001230000c880000014c40d4000874f7d4a54b548c000ad0adcaa8ed181531d848a850f06140003e83b00016686b800121589c0000000013500004d08881940003f0d5c8c97cc000f216480016500007b00a81488d546069c1b429088d9c95b89547e022097ce059d998976c86c2058b0e1938c22d340c7d224540cb4b7d1803dd6606e570c0b921d0b07e99bc001910b60650348731498cfd2399acca88e8ffd90438822800091158960c330001148f4987590832859929005cda5280e59424ca59587f4498b843cc0594580a54d445014567c0000017503c1998000b754bc60025144d2558f905d048000000000b580014792bc0004b8924000d4cf18000e0996c000410000e3cefc104d989207f8a8000000000103c0006397bc0d871cd7ce99a00001470cdd405004780494081140308994968858bc4e1d7c02610dc7a17f98e85093f4a0d7f4604de8c9c76c05409166c6107c81cc45d53cdfc0014100006e19600016413ac0790892189440000001902697893698a4000fa41c4f88d0400016c19d5ec2006c4014000df000049c6885a43e40000000009752455d51700000004f0000ba58d51bcc6558129400129c548000000ced93ce7d9f00008559fc2b1834af111c000ded5e80012690f44353fd9848d80017e8eac1bc000000000e486180000006d000000000040800000000117d22cf1c00135902428c000000f24ee0ec08094347c037c0006806645707205a13cd9a4e68acc3540012d4a880a01091218c98a19d5584b959d17997b4d28fad8695d156d5c13348dc77d24908cc089bd1c0000001808569548000fbc00141d3848800008a4000cd92dd4183000003699a0c70069229454000d8c490928e313d035814d1993555c80000000014c80016280009cc0000007500003208983340004b44ac0005900000004bc6700013e0050ed8c4cfc01d19293a41ac47c7785800014e0bf4b045e424c000e8c000e6d1e57ad0a8b000011fc0000012e18b57d10513f883cba8fd18904793dc00134d6793441f4000cf0000e0c0004f42a4538c6c990000488a9000100d78cbb54ccbc0a5936c36400054513c4c94f000000075d9ec4619b50010696e00010a0000000a5c8695bc36150880c519968000a14af8754c90704cc08b884d1b5a08b4110400085c0008f40097e4fd40ec139250b24f501790
  | 11 => 0x1431978fdc6ec864ae8668ac00654d8f708616f11a0649158f29464b98f78c34bb19e48849609651798286214d0da16bc980e60738814c757d94f53e8ec4630d5538980410cd915d8000000001130fe4000000ad40001d898da0c2d52080fc0000000000000005f0000b18b500016c0001175785554bd50788f8cc5330f5c0011684150e4654e501fc6cd90c03400102c0002e4000934f6d6585a98405ccef85506d41756d48452c91cd1c4800b299b84c064028963c00400143d2cd6996fcdc00009d13982f495187008d73443ca2568029c0f99547b982ced4ea43915b575d6c5489689030000fb0000c3cccc418f9c9a400137d6b0d3cc298ac0014140000006f151ca7caac4448e400000074c1301a86c80291a964c2e87b511893d0f85c80000c01540013495fd8f0001374db1894b485e06b08bd86c520f0d66478d42d3b400009864c0000000017480000013c06fc421879824da86f99b0468000cbc30c58c3b92e51f000000024462c2fc0bc5dcae145d3b0724f81468ee8748e559400009880196b4f8487d2c0de19240018e123c9dc0019305b4e453b899c5291553a9594000d480882c0f109e895c51580c9f95e14a961450195012c9d4d68f3d3f
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x2041f7558c219020fbb4a610c81075da5308640c4aca908432068563484219038329a4210c818694e6008640c34a6b0043206a1215802190306a9ac4298818554d6114c40932e7306a4204357118d521021ab88ca99081265ce60d444085ae431aa22042d72195311020e39aca90881265cc6048440c52a43024220631511812110312b2a4210881a158d2108440d4242b00422049870588434c24c382c221a61469d46010d30b12e4300869859171180434c2a2b88a499261515c8514c530c34ca21e809851a75d8c404c28d3a8c620261625c86310130b22e2318809849873588404c24c3b26420261a25893210130930e6b088098498764c4404c348b0a62202618398d6215030c4ac5308a81861663584540c313312c22a061895896115030c52c5300a81863161980540c21ab88caa10610b5c86550430a1ae42a6601851571153300c294b90a9180614c5c4548c03083cec2a2601850d72151300c28ab88a8980610e9d8544c030a52e42a2601853171151300c28d3a6ca98061269db544c030a34e92a2601854972151300c2a8b88a898061269d8544c030b12e42a2601859171151300c28d3b0a898061869d8544c030e14e42a2601851972151300c384b90a898061425c8544c030e24e22a2601851971151300c388b88a898061445c4544c030a30e8a92601851875509300c384a928498061461d1514c030a30eaa0a601871151505300c20e39acaa0e418658e60d5220a32e7300a91062962980548821ab88ca21c41079ce65d0620a30ea21a61104357119443482163aac421a41515cc5148520a30ea21a60905897210d3048270b88c4982410e9c26395020a34e1b24a61051a70d91530821cbacc1218418654e6090c20952e530486105327090e5108298382c8a88414c9c24354420c32a630282104a9721814108318a88c0a0841079cf659002083aeb31c801041f7694e400820fbb2a7200418598e5190020c2cc6a8c8010625625464008306a9ac420041895895110020b14e72024010721519012008384a9a8490041c85095148020838e6b2a85885457314921c430cb1cc1aa421465ce6015210c62c3300a90842d72194438420f39ccba1421079ce6550a10a30ea21a610841e73980544421d380cb21a210b5c86510d10868eab08868854573149214428c3a88698221645c4434c1109c2e430a608866065485204421d384c72a021469c36494c10a34e1b22a60843975982430430ca9cc1218212c5c66090c10a54e121ca40852870591520429538486a90210e5d46050810c32a63028408629521814204258b88c0a1021079cf659001083aeb31c800841f7694e400420fbb2a7200218398e5290010c1cc6a94800862552586400430aa9ac220021895496110010b24e72022008721529011004388a9a8288021c85494144010
  | 1 => 0x5090f14b10c5284874c9c46294243a62e2314a121d1a731865090e95390c3284874a5c86194243c62c230ca121c3a76d495090e1d3b6a2a84870d5c4605484385ae4302a221e29625405010f18b0aa028087465c25310f42c30a6b0486a143a7098f5150a0f39cc1a8a858698d60d5332a32e1318a99960e6358854cca1cbacc121865629c2434c832a64e121ca21951473591510ca92b9486a88654c9c24354432a4ae421aa219705424c9510cb8321a64a8865469cf6494032a34e7b22a01943a7690d500ca94b9086a8065c25093254032a32e129887a0c3a70d9732d070c29ac121a830e9c263d494183ce7306a4a0c38705963250686b90a6192838514d610c941c30a6b0064a0e1a6358354cc68cb84c62a6638598d6115331874e132e8598c3870595428c61cbacc1218634a9c24394831a18e6b22a418d257190d520c69538486a9063495c4435483192ae231a8418e0c63549420c782a928298863649c2434c431e0c86a926218d1a73d92500c68d39ec8a80630e9da4354031a62e221aa018d1873509500c788a0a62a80630e9c2639532183ce7304a990c3a70d9643c861d384c72a443079ce6095221874e1b2c8710c3a7098e544860f39cc12a2438618f6055121c36c6302a890e1863181544861c382c9a9a430e9c36590d21870e0b288690d197014c434870629ac421a438514d6110d219c2e030a6490c1c735954148670b80c498a43071cd64d4121874e131ca810c1e73982540868d386c9298430e9c36454c21a34e1b22a610c3a70d96430861cbacc1218438694e6090c21c32a73048610f0553d052108782a9a8290843c154f4248421e0aa6a124210d25759912108693baac890843611cd6448421b40e0b224210d6170d4d21086a2baca690843c19515348421e0aa8a9a4210f077454d21087823a2a690843c19915348421e0ac8a9a4210d257590d2108782a9c8690843689c24348421a4aea21a4210f055310d21087a0a9a4328043469cf6494021874ed21ca010c1e73d9150087912a242a8043c85512154021e84a690aa010f4153485500868d39ec8a80430e9da4354021e468290aa010f21414855008791a1242a8043c85092154021e44e890aa010f21744855008791b2242a8043c81912154021e448690aa010f20434855008706b10c529c81459c46294e40a2ae2314a72051a7018a5390287390c329c81435c86194e40c2ac230ca72051a701865390287390c129c81435c86094e40a2ce2304a72051571182539030ca9cc1a9481075da5314a40c2ca7308a520616535845290286b94a6194818594e610ca40c2ca6b08652061a53580329030ca9cc1a8c81075da5314640c1ca7310a32060e53588519028ab8ca618c818394e620c640c1ca6b10632061a53580319020f39ccb90c81079ce658864083ce732843
  | 2 => 0x41407420565208545ccf0000039c00510001a8000004d11922000000013c06411000a0374951391a000010000021c001ac803052751d2a2984c504c648c000fc0b2d0004e0000986f070001e4e94293a1e081218bf2e847438644f83d150000c8c00c002500db508250c458208ad2e48a000000751149400000004dc00068d41214f3eccd2e068458cb3c89b170be40ce6278ac2f48f0014b2f0fe0000000000000105491c000b0260ce5440022c17440cc3d0603dc000007000008000000014941c1b2c48e478f14d8612910c00000194e4144120d9390007b53909000934488331c710604304c0f168a9000001c8b73a0bb1e9435512f4092b1980000038078440000019c00000e10bc001782808d500e52801884320000ec73258051f000378533140000000024001b42a13c35000c33c0000009105800515040a49c104623a80e0014a4040002800000b34fc0d1fcd01b800000004502b37c000d000000ef27534325215350d474630000029c3e3b86c248574a40428450000e200d2e0011b000fc00120000f93e000114fa000dc000002c80000000454d5164004cc24000000010f0000047c2e00156369060008d000d84f400000d30008c1a4000b0001749717c270b433001132a8ae3081f109464603a3d49a54d353f5002d5320f0205307638ca51012d000e52d8d22a094344493b0752bc0012ce028c0005531358d7148742407e2ac222885555499000894c09f000880500003000490f3310214b11916d0b1f477128ed3fd3b3ad26000ca36400000373d80900804060103814020b028140c00028080804000600c000180008050306c100a0500000000002c0a02000401002000080208000281200000140002000240202010000c02000340c1c0f800160a0001c0000008000007008000a000000c0213028140402020100a030001c0a1500008020001014000001830020009000000002d327114a5090e98b88a5284874a9c85194243a52e428ca121d2a7218e5090e94b90c7284874c9c46394243a62e231ca121d1a7318a
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x70a1e3e1f252c100e33020004001b0000002d0b3f1700000000003600001a302b003a3d371c002f340632263c15010d3500290000004016200318050028132700382e00000c003b00000000002419000f002a23111214083931211d22090126180010804100303811826240800004101c21625c46294243c21725846194243a098098d6215332909859c2434c832b028090d3254432a058214d610c941a098214d600c941a118098d6115331a058118d5250831911859c2434c431b028090d524c431911811cd4254031a098014d6210d21a118014d6110d21b0280dd15348421904875915348421b00805915348421921859c24348421d01539c24348421a20865d12154021b00835d12154021b0283d912154021a228690d2154021c05625c46294e40c05725846194e40a058294d610ca40a098294d600ca40a058194d620c640a118194d600c640a078558d2108640a058694d2108640e02534856008640c09735486048440c11735446048440891811c16210d30889821c16110d30891811cd6210130891811d93210130889821cd6110130889821d93110130d01729c4544c030d02725c4544c030d01725c4544c030911811d5424c030909821d5414c030c097358a6015220911811d4434c220911811d4434c120908855c8434c120c09535ca6090c20921829c24354420c09535c86050420c21725446050420909859ce4048020d02735464048020c11735866015210909821d4434c210909821d4434c110910855c4434c110c11535c66090c10921819c24354810c11535c46050810c21525c46050810911859ce4044010d027354a4044010
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 48
  | 5 => 1044
  | 4 => 1671
  | 3 => 343
  | 2 => 65
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
  | 6 => packedAt s5K6 (864+((h/16+packedAt s5K6 (768+(h % 16)*6) 6) % 58)*7) 7
  | 5 => packedAt s5K5 (32016+((h/348+packedAt s5K5 (28188+(h % 348)*11) 11) % 1666)*12) 12
  | 4 => packedAt s5K4 (69625+((h/557+packedAt s5K4 (63498+(h % 557)*11) 11) % 2006)*12) 12
  | 3 => packedAt s5K3 (17833+((h/114+packedAt s5K3 (16807+(h % 114)*9) 9) % 453)*10) 10
  | 2 => packedAt s5K2 (4047+((h/21+packedAt s5K2 (3900+(h % 21)*7) 7) % 94)*8) 8
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf0fe3ffc1e3c7c7e3c78fc7f1c3871fe1cf90f
  | 1 => 0xff1fc3ffe03fff8fc07f1f8fe03ffe1e6331f3
  | 2 => 0x1ffc3fffc07ff1ff801ff1ffc07fe183ce3c
  | 3 => 0xffe0003fffff8001ffffe001ffff8001fc0fc0
  | 4 => 0xffffffc000000001fffffffe00000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x16028884444898800c182413048910cc0c5905
  | 1 => 0x20441008809020104021088420122410212052
  | 2 => 0x8880111080140029080112049004900828228
  | 3 => 0x42012aa250200925254a400192a50045540d80
  | 4 => 0x8cd1b3039d3a7249fa749e4803060d99fbf000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfee8fce8fee8fce8fee8fce8fee8fce8fee8fce8fee8fce8fee8fce8fee8fce8fee8fce8fee8fce8fee8fce8fee8fce8fee8fce8fee8fce8fee8fce8fee8fce8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37183
namespace PEqualNP.Outside.L_meta_37183
open PEqualNP.Outside.L_meta_37183.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x16e01f20284a78080001c800e00000001d020001b1a0b258c600c22807200600008da4c0000042007a0a50000000011112a206cc215211680000272f5c540268e0000000cc00a0001a80009c03d0001900000140856021bf781c7060091d802e70b0032025110000000004d600000000000040010008001000028400081000000000017f95005fd54017f15005ff43017f90c05fd43017f10c03ff5100dfd4403fe5100ff544037d5100ff14403ff4100efd0403fe4100ff50403bd4100ff10403ff3100ff8c403fd3100ff0c403fe2100ff48403fc21017fd0005fe40006f90005fd40017f10005bc40007fcc001fe30007f4c001fc3000ffc4003fe1000ff44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0xe6001bf98730027fac39802afd61cc009fe30e6001bf18730057fea39802b7f51cc015ff28e600aff54730056faa39802bfc51cc015ffa0e600aefd0730057fc839802bfd41cc015dea0e600aff10730027fe6398013df31cc009ff18e6004ff4c730057ba6398013fc31cc015ff10e600aff48730057f8439802fff40cc017ff2066000ef9033005ffa819802ffc40cc017de206600affc4330057fc219802bfd10cc015fe0866009ffd923004dfec918027fe648c0057f3246009ff5923004dfac918027fc648c0057e3246009ff9523004ffaa918027fc548c00f7eb1c6009ffd0e30027fc8718027fd438c009fe21c6006ffd8630035fec31801bfe618c0037f30c6006ff58630035fac31801bfc618c0037e30c6006ffd4630036fea31801bfe518c00dfea8c6006df54630037f8a31801bff418c00ddfa0c6006ff90630037fa831801bbd418c00dfe20c6004ffcc630037fc631801bfd318c009fe18c6006ff88630037fa431801bfc218c0097f3046009ffd023004ffc8118003be408c013fea046009ff1023004f788118013ff308c001ef9846004fecc230037fe211801bfe108c00dfd0846006ff44230037f2211801bfc108c011ffb226008bfd91300077ec898002bf644c011ff3226002bf99130047fac898022fd644c011fe3226002bf1913004778c89800abc644c011ff2a26008ff55130047f8a898023ff434c009ff21a6008ff50d30027f8869801fff614c00f7fb0a6007ff9853000dfcc29801ffd614c00f7eb0a6007ff1853000df8c29801fff514c00fbfa8a6007ff9453003ffaa29801f7d514c00ffe28a6007ffd053003f7e829801ffe414c00ffea0a6007ef5053003ff88298013ff314c00fef98a6007ff8c53003ffa629801fdd314c009fe18a6007ff8853003ffa429801ffc214c011ffa026008ff901300077c8098023fd404c011fe2026008ef10130027fe6098013fb304c001ff1826000f78c13003ffe209801ffe104c00ffd0826007ff4413003ff2209801ffc104c009ffb206004bfd9030027fcc81800afe640c009feb206005bf59030027f8c818012fc640c00bff2a06005ff5503002ff8a818012fe630c009ffa186004ff90c30027fa8618013fc430c009ffb086004bfd8430027fcc218006fe610c009feb086003bf58430027f8c218006fc610c007ffa886003dfd443001ffca21800ffd510c007bea886003ff1443001ffe821800fbf410c007ff2086003ff5043001f7a821800ffc410c009ff9886004ff8c430027fa6218013fc310c007ff1086003ff4843001ff8421801afe600c00bffa006005ff900300077c8018017fd400c00bfe2006005ef10030027fe6018013df300c009ff1806004fe8c030027fa6018003dd300c009fc9806000f64c03001ffe201800ffe100c007fe8806003ff04030
  | 1 => 0xa6b5b300000374f42709b879c34b8ab4b528468af389c8221611412399164718f200000770005013a000d70c0b8000db1589300000002163dc00348a08c1af744e000258000009823a001d38700000042001e01447e488f8120ae360a98880029086790d30fc00701a14dc037740000100001a04f43a1697260c003cccf0015a20d56029b101000731860cc00496106657d2a1953f50501dc70490a45400614cb31c18000007a139485d9768aa00232689c50010f308000006d2b5b67b98a7ca4e50c002f14773cb9728ff53c00779930ec817f01e2d1c20881a6ec2851a465e0713982e705981d9e20d9db639021b0464ec7921d2f0020e0711300084000642d4575a88a100907d93f000200007539c00998cc6484d5d64a001ba8f1943c07a570ea29438560370c8fb3b84c1c80c1adfa0b5a66b0923d496278005544a1109a001512c1b45040096a2c890a6525a37840000179000c075d45164007959e520c874152599b900098002020002c2e800231332525265cf12b0004c9635d8fc45c410010c001bf0097a2c8472c56c38db800000000a3001190000d01c0d00000058040180100001004010200001c000141902403018040100f0340f0b822018060000200000000000700602c1c03401004220040508c0a0000a0442f0342604405000150000804016028020300200403050130081b0000d0500000c000201f004021180800002024120181903c0d0081300800040030001306c0104c0103402008030240701007048060000e0080b08400008330140000412004050080401402014000041c0cc00070010400200000000100001000000034010000000c0c00007010170041c0200a00020034020000a0777ecb2003bbe659001ddeb2c800eef196400077ec720003be6390001deb1c8000ef18e400777ea72003bbe539001ddea9c800eef14e4006f7ec520036bf629001bdf314800def58a4006d7ac520037bc629001bdfa94800dcfd4a4006f7ca520037bd529001b9ea94800def14a4006f7e6520037be329001bde994800def0ca400677ec320032bf6190019df30c800cef586400657ac320033bc6190019dfa8c800ccfd46400677ca320033bd51900199ea8c800cef146400677e6320033be3190019de98c800cef0c6400677e4320033be2190019de90c800cef086400177cc12000abe6090005dd304800eefd42400777ca1200033e509001ddea84800eef1424007678a120037bf209001bdf104800def4824006f784120033bf1090019df084800cef44240067782120013ff64cc0097fb266004ff99330015fcc998013be64cc0055f3266004ff5933005dfac998013bd64cc0015eb266004ff19330025f8c99802ffe54cc017feaa6600bff15330027fe8798013fe43cc009fea1e6004ff10f30027fec398012ff61cc009ff3
  | 2 => 0x181592f9603112b55c546102f471e659e4063c01015fe0014a0501f44644149346a98067d4210c2b641205f256621df34053064bb920a24195e669d48a9b78e000690fe5f87d52e085a0c1950585512778c8054d2a801f8735ce3ac00608da000e40000083000761ec0002465a2629c4540d9c0e59b040f9076043d965214e525c00039266a234124ef63650001ae9700000000000c66f4e88b8bd3b14c32866000005b8625a4004e144350000007f8513e000001d000748002445f3e935630d52fd744044b535770006f6c8d14c1be001ab7c1a56d4822cc957596b1550428642171295bc00710c38821a5386e1cd070f400604000007b0003c4399100021000780580037973370c91c16200000020cd00000001ea08c0018c001aa360d461000003642669df45c13131477451b0001184401b478ce0f9d55ec4e491a962e280a92c5c64c2dc5b4f2624221213c061a11235a5e5b4ed3a5bc2d8996753623a065fe3e4585e0c47c5405d0d000862
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc20d9130006bf10d9130006be10d9130006bd10d9130006bc10d9130005be769013005ebe769013005cbe769013010ebf65901300073f65901300063f6590130076be659013010ebd6590130076bc659013010f3c65901300763c6590130105bf7290130105bd72901300f6bf629013006ebe62901300f6bd629013006ebc62901300f73f52901300f73d52901300f79f32901300f79d32901300fdbf71901300fdbd71901300eebf6190130066be61901300eebd6190130066bc61901300ef3f51901300ef3d51901300ef9f31901300ef9d3190130045be7090130047ba709013009f3e509013009f3c50901300afbb30901300f7ba20901300f7b920901300efba10901300efb91090130006bf648c13004ebc648c130025fa708c130026fb608c130025de768c130026de768c13000cde768c1300079f648c1300e79c648c1300a5df718c1300a5dd718c1300df5f518c1300df5d518c1300df9f418c1300df9d418c130025de708c130025da708c130026df608c130027db608c13009f9e408c13009f9c408c1300dfda108c1300dfd9108c13009ebf769003009ebe769003009ebd769003009ebc769003009ebf6590030076be65900300d6bd659003009ebc659003009f9e739003009f9d73900300aebe639003009dbf72900300cdbd729003009ebf629003006ebe62900300c6bd629003009ebc62900300c73f52900300c73d529003009dbf71900300bdbd719003009ebf6190030066be61900300b6bd619003009ebc61900300b73f51900300b73d519003009dbe709003009fba709003009ebe609003009f3e509003009f3c509003009f9f309003009fba30900300afb93090030025df764c030006df764c030004df764c0300079f744c03008f9c744c030026df614c03007edd614c03007f5f514c03007f5d514c03007f9f414c03007f9d414c030025df704c030027db704c0300a6de604c030027da604c03008fdb404c03009f9e404c03008fda404c0300079a404c03008fd9404c03009f9c404c03008fd8404c03008f98404c03007fdb104c03007fda104c03007fd9104c03007fd8104c030027db764c030025db764c030006db764c030097db744c0300079b744c03008fda744c030097d9744c03008fd8744c03008f98744c030027db644c030027da644c030027d9644c030027d8644c03008fda544c03008fd9544c03008fd8544c030087db714c03007fda714c030087d9714c03007fd8714c030027db614c030026db614c030027da614c030027d9614c03007ed9614c030027d8614c03007fdb514c03007f5b514c03007fda514c03007fd9514c03007f59514c03007fd8514c03007fdb414c03007f9b414c03007fda414c03007fd9414c03007f99414c03007fd8414c03007fda214c03007fd9214c03007fd8214c030
  | 1 => 0x33006ebc629033015f3f529033015f3d52903300af9f329033015f9d3290330155bf7190330155bd71903300aebf6190330066be619033014ebd6190330066bc619033014f3f519033014f3d51903300af9f319033014f9d3190330145be709033005fba709033009f3e509033009f3c509033009ebe769023009ebd769023009ebf6590230076be659023013ebd659023009ebc659023009f9e739023009f9d739023009dbf7290230135bd729023009ebf629023006ebe6290230126bd629023009ebc62902301273f52902301273d529023009dbf719023012dbd719023009ebf6190230066be619023011ebd619023009ebc619023011f3f519023011f3d519023009dbe709023009fba709023009ebe609023009f3e509023009f3c50902300afbb309023009fba2090230127b9209023009fba109023011fb91090230005dd76cc230026dd76cc2300279e74cc2300279d74cc230116df61cc230116dd61cc2301175f51cc2301175d51cc2301179f41cc2301179d41cc230027da60cc23009f9e40cc23009f9c40cc230045be76d9130046be76d9130014be76d9130006bf65d91300073f65d91300063f65d9130006be65d9130006bd65d9130006bc65d91300073c65d91300063c65d9130005bf72d9130005bd72d9130006bf62d9130006be62d9130006bd62d9130006bc62d91300073f52d91300073d52d91300079f32d91300079d32d9130005bf71d9130005bd71d9130006bf61d9130006be61d9130006bd61d9130006bc61d91300073f51d91300073d51d91300079f31d91300079d31d9130045bc70d91300073c50d91300afbb30d91300afb830d9130007ba20d9130007b920d9130007ba10d9130007b910d9130006bf75d9130006be75d9130006bd75d9130006bc75d9130006bf73d91300aebe73d9130046bd73d91300aebc73d9130006bf53d91300aebe53d9130006bd53d91300aebc53d9130006bf72d9130004bf72d9130006be72d9130006bd72d9130004bd72d9130006bc72d9130006bf52d91300063f52d9130006be52d9130006bd52d91300063d52d9130006bc52d91300aebf32d9130006be32d9130006bd32d91300aebc32d9130006bf71d9130004bf71d9130006be71d9130006bd71d9130004bd71d9130006bc71d9130006bf51d91300063f51d9130006be51d9130006bd51d91300063d51d9130006bc51d91300aebf31d9130006be31d9130006bd31d91300aebc31d9130006bf21d9130006be21d9130006bd21d9130006bc21d91300aebf70d9130046be70d9130014be70d9130046bd70d9130046bc70d9130014bc70d9130006bf50d9130006be50d9130006bd50d9130006bc50d91300063c50d91300aebf30d9130046bd30d91300aebc30d9130006bf20d9130006be20d9130006bd20d9130006b
  | 2 => 0x6dbc7258e40006bf6258e40006bd6258e400073f5258e400073d5258e400079f3258e400079d3258e40005bf7158e40065be7158e40005bd7158e40065bc7158e40006bf6158e40006bd6158e400073f5158e400073d5158e400079f3158e400079d3158e40046be6058e40047ba6058e4009f3c5058e4009dbf7518e40075be7518e40005bd7518e4009dbc7518e40006be6518e4009ebc6518e400adbe7318e4009ebf6318e4009f9e6318e400aebd6318e4009f9d6318e4009dbf7218e4006dbe7218e40005bd7218e4009dbc7218e4009ebf6218e40006bd6218e400073f5218e400073d5218e4009dbf7118e40065be7118e40005bd7118e4009dbc7118e4009ebf6118e40006bd6118e400073f5118e400073d5118e4009dbe7018e4009fba7018e4004dba7018e4009ebe6018e4009fba6018e4009f3c5018e4009f3e769424009f3d769424009f3c769424009f3f639424009f3e639424009f3d639424009f3c639424009f3f719424009d3f719424009f3e719424009f3d719424017d3d719424009f3c719424009f3f619424009e3f619424009f3e619424009f3d61942401763d619424009f3c61942401773f31942401773e31942401773d31942401773c31942401773e21942401773d21942401773c219424009f3e609424009e3e609424009f3a609424009f3f109424009f3e109424009f3d109424009f3c1094240006bf7559330006be7559330006bd7559330006bc7559330026bf7359330026be7359330026bd7359330026bc7359330026bf5359330026be5359330026bd5359330026bc5359330006bf7259330004bf7259330006be7259330006bd7259330004bd7259330006bc7259330006bf52593300063f5259330006be5259330006bd52593300063d5259330006bc5259330026bf3259330026be3259330026bd3259330026bc3259330006bf7159330004bf7159330006be7159330006bd7159330004bd7159330006bc7159330006bf51593300063f5159330006be5159330006bd51593300063d5159330006bc5159330026bf3159330026be3159330026bd3159330026bc3159330006bf2159330006be2159330006bd2159330006bc215933005ebf705933005ebe7059330006bd705933005ebc7059330006bf5059330006be5059330006bd5059330006bc50593300063c5059330026bf3059330026be3059330026bd3059330026bc3059330006bf2059330006be2059330006bd2059330006bc2059330006bf1059330006be1059330006bd1059330006bc10593300adbd7690330046bd7690330044bd76903300aebf6590330076be65903300af3e65903300763e659033016ebd65903300af3d65903300063d65903300aebc6590330165bf7290330165bd72903300aebf629033006ebe629033015ebd629
  | 3 => 0x9c20000011a08b00000018c6d1d60000002302327400111000398d84003a871e9f8001d43a4002522564e00a49600082000000000000f39942900002609f04146a021f739c0b6000000000e8002013b28e00000000000000162224000710191ee5ed10890342000438bc3580000000045c0c80000001e000000d90000003f82c000314001bc8000007406aad66ea000360006fe0000000024c000000000000018000063c1dc00000000f68349bc6cd00003a723380f03f466000b186f0eb7141100000000000003004006010028010020000280000e010068000200000000200a00c00802000024010030040000000900400002801000008008000040180380000400c0000700001407003000010008000060000000800c028000000020000000100000000000002004000000000200080300400003000000008018160000000000300801c0080100200400802000004020050000080000200000c008020000000080000600c0000400600002001010004010020000000000000000c028000000000000000000001007000000030010040000080900400c0080000000000001002000020040000000100c0020080300100001400001004008030000080100000c0000200280000400000000000000000010000080080001202c03806000010008000020000200500803c01005000010038010000000180100000c0080100400c0000b0000140080109dbf75d8e40075be75d8e4009f3e75d8e400753e75d8e40005bd75d8e4009f3d75d8e400053d75d8e4009dbc75d8e4009ebf65d8e40006bd65d8e4009dbf72d8e4006dbe72d8e40005bd72d8e4009dbc72d8e4009ebf62d8e40006bd62d8e400073f52d8e400073d52d8e4009dbf71d8e40065be71d8e40005bd71d8e4009dbc71d8e4009ebf61d8e40006bd61d8e400073f51d8e400073d51d8e4009dbe70d8e4009fba70d8e4002dba70d8e4009ebe60d8e4009fba60d8e4009f3c50d8e40045bd7698e400adbf7598e40075be7598e400af3e7598e400753e7598e40005bd7598e400af3d7598e400053d7598e400adbc7598e40006be6598e40006bc6598e400aebf6398e4009f9f6398e400069f6398e400079f5398e400af9c5398e400adbf7298e4006dbe7298e40005bd7298e4006dbc7298e40006bf6298e40006bd6298e400073f5298e400073d5298e400af9f3298e400079d3298e400adbf7198e40065be7198e40005bd7198e40065bc7198e40006bf6198e40006bd6198e400073f5198e400073d5198e400af9f3198e400079d3198e40146be6098e4005fba6098e4009f3c5098e40005bf7558e40075be7558e40005bd7558e40075bc7558e40006bf6558e40006bd6558e4009f9f6358e400aebe6358e400079f5358e400079c5358e40005bf7258e4006dbe7258e40005bd7258e40
  | 4 => 0x8bc979ae1180008a0a700028800109000000cf0863160010e8b62e6000790ec0005a800000000038000000000927a8000000002c8400ae6440000037200000038000001028001ce0000009b4461c40003735f0001e5e426a0000000040c3352800005e2d00000000d001098552a65b11b141000000c98000004b818a1e0007c48dc29000138d400035a1a27c000000614ef90a3aa0000000022e590591ba46e00000000000000000000008b048931206000000d80001f03b60700000086000006634dcc4d000056908000000000005a38d1e4001492b07fc000000006bae5400000000990f427a06d1201a04a1a8541a00000000e800357462bd01f1da0000021f1008c8641bc436400d280736f65c074000006a4001830000000000005c768880002ae000089a6000158001403d2660e78000672f8370000006880018c1ca0000000000000000000000000f100035b0000015c0000000485b0c2000a89590000e4bf03f8150a84a1bf3a061c17dee0000000015e0e98a400009b7a080e922000076c9520a00060400034389000310d61be5b4380cf000000b800002645ed18000000012400032a528d38650000000000038642c000001ec2f4450001c648c19643025810000000392647d0002ca000d881384e00000000021824000000000005600000041c0a8001fa000000719de00010c001848c0e48d105d1d48c80041c0000b400000294fc83d00f7700019038c4d8c71e500080811c002960005fa3e21c3ec029bb1b891833c002f26d12223b0006f70a00018c00000000000001069a427c1f45517f3704f12602b000268250a00004e88fa3f12451108a1736e1e8dc4001981781cd7609049ca18000b80349495400000000000208110f311ca0c2080019f49c538001050601480016e00000800070ca60008784700093cd50f9304779168002840000000026e2828a947430000000002cc4667e24500000000046000104fe15d226000000004820008400004c000001af1b4000ee8000002e4001f63346da090b1170016da400000530000000e40004a800000000000000000000020b314000e603b2e8000e2c000480005b822c2a6d400a103c6000e20630002a4001fd3e400006c0002e000000003ae000a697205a001110004961e0e99b045413c15c003d63f90e000000000428b5000350e580000000000196194000cca19000489130841e610229a492ac53c3e5d628c000c4247000624001f80003800c09c0052ac000b311e000001ab2293903b00b406000b38001dc1503601d8fc20ca90351a61ac14c000007f8440770e5474002353f40cc0012c38e1a4c315a000458002312c219913933234000af80000000089c000008e4000002f83540bc00000062568000b08480a11b0be8f0000000000580000000009680a5138255463
  | 5 => 0x670e61a71e8c022d5f451a0f3e64d0f503e2481146481042c6103a000055000e890d0613fd269bbade5a4000003d8702618ae23b00021a42000000000b01e07c0280082b6478e143e8ba0001ec003c03c4e0c0001f0000002833a35c00000238000000000001ce259c028a8ac5209e1126c8064a644a00000004859580001be8000000f4db11a0ea0000000056e00000000018000000170300000035900000228000000db08123000000000434084690d00006d6658000fb70e0001f8000003224000040800000000000b899c000000000000000000e0a14746ce0000011c760340000000001e128000000608000df000001262f07d0001e83c24ecf780035512400168000000000002a00000000017400004400494180cd9cd0140005d93015e0000de0c000000e51be1c27ec6e92d14325cc9175240494e41f5000000001771881ec210980a2000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xcb571487644c00117d0e10ec8980022f61c21d91300051f42843b226000a3d85087644c02b53d0610ec898002a760c21d91300075290843b226000aba80087644c0015730010ec8980562fa1f50d91300045ec3ea1b22603a8bf87543644c02b1790ea86c8980028f60850d91300061fb90a1b226000c3d72143644c00147b02286c8980030fdc450d91300061eb88a1b226039a3e80143644c02787ce0286c8980e38e9c050d91301c71cb80a1b2260158be87c83644c00117b0f906c8980028fa1720d91300051ec2e41b2260138bf87883644c0271790f106c8980028f21620d91301bc5fc3a41b22600d8bc87483644c00147f0a906c8980028f21520d91300045f43841b2260088bd87083644c00147d0a106c8980028f61420d91300ad4f41841b226000a9d83083644c00156d02106c898002ad60420d91300ac5f43e21b2260008bd87c43644c00147d0b886c8980028f61710d913009c5fc3c21b2260138bc87843644c0014790b086c8980da2fe1d10d91300645e43a21b226000a3f85443644c0014790a886c8980022fa1c10d91300445ec3821b226000a3e85043644c00147b0a086c898056a7a0c10d91300054ec1821b226000aae82043644c00155b04086c89804e2fa1a76901300061e32ced2026013c9f639da404c01d47d0db2c80980030f9db65901300051fc16cb2026000a3d82d96404c00187ee5b2c80980030f5cb65901300051fc0ecb2026000a3d81d96404c00187ee3b2c80980030f5c7659013009d1f406cb2026013a3c80d96404c06b87ce1b2c80980038e9c365901300ae4f3b6c91826015d9a70d92304c001938e9bb26018003a6103764c0300062fa8eec9806000c5d51dd9300c00193e83bb2601800327507764c0300266cc06ec9806013c9e40dd9300c02793881bb2601800327ddb744c03009dcd406e89806013b9880dd1300c001e30a1ba260180a2e6a1e404c03009ecd43c809806013d9b76901300c001d36ed2026018003c6dd6404c0301a78c3ac809806013b9b82901300c06773305202601804fa6d8a404c0301974cb14809806032f1b52901300c065e32a5202601804ee6e06404c03018dccc0c809806013e9b61901300c061d32c320260180c3c6d46404c0301878ca8c809806004ada87dd9300c0099b50fbb26018003a61d3764c0300056dc0eec9806000ad981dd9300c001cb6a3bb2601800396547764c0300074da0eec9806000e9941dd9300c0517350fba2601804766a1f744c0300aecdbb6e89806000e9b76dd1300c001e36ebba26018003c61d7744c030005cdc16e89806000b9982dd1300c02bd36c5ba26018003a658b744c0300078da96e89806000f1952dd1300c00173703ba26018002e6607744c0300af4db0ee89806000e9961dd1300c001e36a3ba26018003c6547744c030
  | 1 => 0xf04b0ec898002ab20961d91300445ec38c3b226000a3e85187644c00147b0a30ec898002aba0861d913000556c10c3b226000cb571187644c00147d0da8ec8980028f21b51d91302361f3b6a3b226000a3e86547644c0014790ca8ec8981170f9d951d91300074a30a63b226000b98804c7644c00147d0c286c8981130f9d850d913009e9d380a1b226015ab886483644c02b73106906c898003aa18920d91300ad5c43221b226015b9883443644c001d60c2886c898056a7a0f75d91300054ec1eebb226043aba80dd7644c02b57301baec8980030fdd675d91300061eba8ebb226000a3e85dcf644c00147b0bb9ec898046aea0373d91302145fc3aa7b2260418bc8754f644c00117b03b96c89804e2fa0372d91300045ec3ce5b226000a3e859cb644c00147b0b396c8980032be0972d91300045fc0ae5b2260138bc805cb644c00117d0e396c8980028fa1472d91300051ec28e5b226015a9e831cb644c00153b06396c898002ada0472d91300055ac08e5b226040aba801cb644c02b57300396c8980030fdcb52d91300061eb96a5b226000a3d81d4b644c00147d01a96c8980df0f9c352d913006e1e386a5b2260008be8794b644c00117b0f296c8980fe8f61652d913000717c12a5b226000c3f7254b644c00187ae4a96c8980028fe0552d91300051e402a5b226037c3e7054b644c01b878e0a96c8980022fa1c52d91300045ec38a5b22603ea3e8514b644c00117d0f196c8980022f61e32d91300051f42c65b226000a3d858cb644c00117b05b8ec8980030fd4b71d91300061ea96e3b2260138be80dc7644c00117b0f38ec8980028fa1671d91300051ec2ce3b2260008bf825c7644c00187ea4b8ec8980030f54971d91300065bc0ae3b2260138bc805c7644c00117d0e38ec8980028fa1471d91300051ec28e3b226015a9e831c7644c00153b0638ec898002aba0871d913000556c10e3b22603daba801c7644c02b5730038ec8980028f60b51d91300061fb96a3b226000c3d72d47644c00187ee3a8ec8980030f5c751d91300051f406a3b226036c3e70d47644c019878e1a8ec8980022fa1e51d91300045ec3ca3b22603ca3d85947644c00147f04a8ec8980030fdc951d91300061eb92a3b226000e3781547644c00187ee2a8ec8980030f5c551d91300051e402a3b226036c3e70547644c019878e0a8ec8980022fa1c51d91300045ec38a3b22603ba3e85147644c00117d0f18ec8980022f61e31d91300051f42c63b226000a3d858c7644c00117d0f90ec8980022f61f21d91300051f42e43b226000a3d85c87644c00195ae590ec8980022fa1e21d91300045ec3c43b226000a3e85887644c00147b0b10ec8980032d5c621d91300045f43a43b2260008bd87487644c00147d0a90ec8980028f61521d913000656b9243b226000
  | 2 => 0x651593300051fc12a2b266000c3f7254564cc00187ae4a8ac9980038de0551593300061fb8aa2b266000c3d7154564cc00147900a8ac9980022fa1c51593300045ec38a2b26604ba3e8514564cc00117d0f90ac9980022f61f21593300051f42e42b266000a3d85c8564cc00117d0f10ac9980022f61e21593300051f42c42b266000a3d8588564cc00117d0e90ac9980022f61d21593300051f42a42b266000a3d8548564cc00117d0e10ac9980022f61c21593300051f42842b266000a3d8508564cc00953d0610ac998002a760c21593300075290842b266000aba8008564cc0015730010ac9980028fe1570593300051e42ae0b26604aa9f835c164cc00117d0fa82c9980022f61f50593300745fc3aa0b26603a8bc8754164cc00147b04282c9980030fdc850593300061eb90a0b266000a3d8114164cc00187ee2282c9980030f5c4505933024d1f400a0b2660008be87c8164cc00117b0f902c9980028fa1720593300051ec2e40b266000a3c8588164cc01b17f0e902c9980de2f21d20593300051fc2a40b266000a3c8548164cc01717d0e102c9980022f61c20593300051f42840b266000a3d8508164cc00953d06102c998002a760c20593300055b40840b266000ab58108164cc001d5240102c9980022fa1f10593300045ec3e20b266000a3e85c4164cc00147b0b882c9980028f21610593300645fc3a20b2660368bc8744164cc00147f0a882c9980028f215105933005c5f43820b2660008bd8704164cc00147d0a082c9980028f61410593300254f41820b266000a9d8304164cc00155d04082c998002ab60810593300075888020b266000a3f8259640cc00147b04b2c81980030fdc965903300061eb92cb2066000a3f8159640cc00147b02b2c81980030fdc565903300061eb8acb2066028c3e7059640cc001c74e0b2c81980022f61e65d91300051f42ccbb2260008bf87597644c00147d0c32ec8980030f9d865d91300051ec10cbb226000a3d81197644c00117d0db96c8980030f19772d91300061fb2ae5b226000c3c655cb644c00517f0fb16c8980032b5cb62d91300045ec3cc5b226000a3e8598b644c00147b0b316c8980022fe1d62d91300051fc2ac5b226000a3c8558b644c00156f02b16c898002ad20562d91300445ec38c5b226000a3e8518b644c00147b0a316c8980032b5c862d91300055b408c5b226000ab58118b644c00147d0da96c8980028f21b52d91302461f3b6a5b226000a3c8654b644c08f87ceca96c898003a318932d9130005cc40265b2260008be86dc7644c00187ecbb8ec8980030f19771d91300061fb2ae3b226000c3c655c7644c00517f0fb0ec8980032d5c761d91300045ec3cc3b226000a3e85987644c00147b0b30ec8980022fe1d61d91300051fc2ac3b226000a3c85587644c00155
  | 3 => 0xb31c8015a9d87d8e639002793b0fb1cc720002a7a176398e4009f0f42ec731c8000a1e85d8e6390027c3b0bb1cc720057879d76398e400af0ebaec731c8000a9d82d8e639000153b03b1cc72004ea7a036398e4009f4d406c731c8013e1e50d8e6390027c38a1b1cc72004ea721b5398e400068ebaea731c8000e1c65d4e639000187cebb14c7200030f5d76298e4006c5fc3ac531c8000c3e7558a639000187aeab14c720002a7e0d6298e4000656b92c531c800e93f87d4a639000127b0fa94c72000387d8f5298e400049fc3aa531c800093d8754a6390001c3ec6a94c72004ea7a193298e400061f3aec331c8000c3d75d86639001917f0eb0cc7200030f9d56198e400061ebaac331c8000a9f83586639000196ae2b0cc72003a4fe1f5198e400049ec3ea331c8000e1f63d46639000127f0ea8cc7200024f61d5198e400070fb1aa331c8013a9e864c6639000117f0cbaac7200022fa1f6558e400761f3aecab1c8015a9e83d95639008757501b2ac7200562f21d6558e400761e3aacab1c801399e87d4d639002753d0da9ac72000347dd75358e400070fb2ea6b1c8013a9e8614d6390001c3aca29ac7200362f21d6258e4000657b92c4b1c801399c874c9639001bb18e4992c7200322f21d6158e400065bb8ac2b1c801399c874c56390019b28e298ac72004e2f2197518e4009e1e32aea31c80008bd87994639002787eeb328c7201732e9c26518e4006c5ec32e431c8013caf625c863900b7974e0b10c72016b4e9c35218e4006e97392a431c8000d2d7254863900b3a74e0a90c7200322f6197118e4009e5bb0ae231c8058cba7058463900afa74e1a88c7200334d9c55118e400069ab8aa231c8056d3a70544639000187eeb3aac998156a7e0d75593300254e41aeab266000c3d751d564cc00117b03b92c9981522f61e72593300051f42ce4b266000a3d859c964cc00953d07392c99814ea760e725933000657c12e4b2660008bf815c964cc0a517d0e392c9980028fa1472593300051ec28e4b266000c3f72d4964cc00187ae5a92c9980028f60752593300051f406a4b2660008be8794964cc00117b0f292c9981468f616525933000717c12a4b266000c3f7254964cc00187ae4a92c9980028fe0552593300051e402a4b2660008be8714964cc00117b0e292c9981428fa1452593300045ec16e2b266000c3f52dc564cc00187aa5b8ac99813e2f61e71593300051f42ce2b266000a3d859c564cc00953d0738ac99813aa760e71593300045fc12e2b266000c3f525c564cc00187aa4b8ac9980032de05715933026c5f438e2b266000a3e851c564cc00147b0a38ac9980028f60b51593300061fb96a2b266000c3d72d4564cc00187ee3a8ac9980030f5c751593300051f406a2b2660008be8794564cc00117b0f28ac9981328f61
  | 4 => 0xd28001ec2f40000000000000000000000410000a66ccdc0a5000000608000002dc0006d37465c0010a000000b984180011a000001dc58d0c0003020ecff1e120c0000021426871c589d0154664a7a2a2ec3f06807033a5640000046c814000000e470c0000031e000001ae210000219b1000000000000980010300029b5607c98800027800000448478fe0002f469833133142000000dc21e0000010b0d07e43e0000000001a400000000000003c8000001300000009212f0613b0568510fe000094000d80001e55b1c4000000000004b00009900005a000000007780000000052c000f31400c6b10003ea6400000000077c0113d01d6d4ad21a492780000002d600082438aae79c00000452460000cc1be84056241152014c00000b48ec000e01cc1b83895c43c0000002630e5185ca0a0875d4e624e3e207421408058459168003d00006393e0004b41d18d0340000023f0006f0000003968bc00000000000ee0000000012400000026cf58110001bcc296626281c6c1ea342484de94d00008c0000030c54cbf2280f00b8008941f61149e13a0003c0e792511686c0001b0906c80000011e000000d71bc504bd85f0006700008323f001108003fa0f67f0d111280c0080c000020080000002020020000e00000030000900c04000000040200003008000000000600000020020000000006010020000200802090060101a000120000000000000000000a008000000e0200001800008060600403802038000680000002010040000c008040a0020080201804018020080a000020580c0180200000018020400c05802000060001000802000000600e0080400806000120180600808028040000400000030040080a000000080c0080201802010020000a0000e0000202008008000100a0080a0780000000028000701600800020000182800000058100000001000008000000200000010080000e008120000200004038020183000002008020100000802010024fe0975d8e4009e1fb12ebb1c800093f815d7639002787ec2baec72004e4fa0175d8e4009c9e402ebb1c8013c3e605d76390027a74c0baec72003b0f9d565d8e4009e57b12e5b1c8000c3e7558b639000187aeab16c72003a4fe1f52d8e400049ec3ea5b1c8060d3a70d4b639000127f0ea96c7200024f61d52d8e402fe9d382a5b1c8013cb7615c7639000187ceab0ec7200030f5d561d8e400749fc3ea3b1c800093d87d4763900bda74e1a8ec7200024fe1d51d8e400049ec3aa3b1c805dd3a70547639002733906bacc7200030fe197598e400ae8e41aeb31c8015c3f635d6639002b87ac6bacc7200024fe097598e400049fc0aeb31c801393e805d6639002727900bacc7200a30f9817598e400069d302eb31c8000c3d75996639000153b0732cc7200038714e6598e400061eba8c
  | 5 => 0x22500000000177000244001438008d400104470070b29d23ec6bc00191000000000e400000000000000930000000005403b64508c000000000000000015d2ce0fc0008a174001100000003d00007e41e6a8f3000000558000000000000011127208022c353166ec0000002e230000001d000000000000000e496400004c4ba173940c51f19e0005546c8b8000240848002a2000b883587004ed114247445c5b01f472000000bb06500000000000608048b409e8f04fa3715e7943a0bc00069c2d82980c00000041000001000000000000023d4940008e148c32000b8084000000001b625643862800138680b90c33840f0120a401a7350611929d000000000000e69b80032a4ee16821312100f8000110000be1e31e400081000031000000000000000021532c744b0000160000000000006692a0c836800023d6a2be0a0880963e82fcd60da26a1782e8002f200000000084848b717f000000aa12a000000000000003c4a2c00000338000a20000000022e02c8c0e29150ec6907f836829720001070000000014980049c00000102268b40be2000000023100089c000a32401e40006115c15800000000000000001b67e11a00037c2490219f49e374000eb0000f8a70000002d48284b4864a4eb1432c282c2a8ab0007e87c0000944483e9f2446000db94c194000ff9e90ce000749400083bc000001845e1298004662a0538002187bc000001c676400000000201040253805bc7a8c618824c00049180151010003e6238000000000008d8000000000012244c2cc750b2000180000e500000000000000000e2132000000df8003ae60cb686923e4b90098c3a80002c146b603dc002110ee000000004646b4178e131c0000000000e164000000007b8221c10060a20003400021c8e92344400000000000000000000007686900021a048000000000de0022b1a80000000000094109800000214ba18a3a6486000158445328081e2d2000398002345243213f07a76c00000488000ca05010c3e8000cd2901d4c9800018040000001ce0004c000000774a2a5100091c4e90308e7881581781402cf60a60006a000000000254e70000008707e80000068d068003720001824d000548a39381da0d8fd8271ac9486a8634800001c80001c824a50c909a0cc00000000000001840004d80a01943a0000003200003c0005c0001940c11441c42af69982767dce300006e754679133b01ecd587a24c1ad2100011a6a4a54d305266d230150004a0000000005f4b62160c400000000000000a205205432c000004960000000032415c000000d40010f84e000578000000008b0
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xa8b4c4030400015ac40a0f800b011004260d231e016971c74009249041b5400b023c341850064601009d2800e70000004c00a28454864440000020082430021400050b64a7558b6390001435919d561d8e400060720f865d6639002721d9814e6598e4009d0765c53996639000121f97a176398e400048765e85d8e639000121d92a176398e400048764685d8e639002721e90a176398e4009c8724285d8e639000121e95e0d6298e4000487a6363d4a639000121e98d8d5298e4000487a5783586639000121e98d8f5198e4000487a6363546639000141e97d975358e4031586a4365d4d639000121f985945358e400040fe61751d564cc0c341c935d47559330006a160d2108564cc001aa12160021593300060b6097214164cc001835815c45059330006a86052008164cc001aa1824401059330006295c98118b644c0016859118932d91300062960971187644c0016859218531d9130005a864462483644c0016a19218510d91300040fe61751d7644c0018a58748421d9130006a160d21087644c001aa12160021d91300060b60b72143644c00183581dc450d913000706ddb75901300c001c1b76dd7744c030006a2e0962dd1300c001e096254b744c030006a4e0561dd1300c001e1161547744c030
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x5
  | 3 => 0xca
  | 4 => 0x4
  | 5 => 0xcd
  | 6 => 0x12ca
  | 7 => 0x9ca
  | 8 => 0x9cd
  | 9 => 0x12cd
  | 10 => 0x168a
  | 11 => 0x168d
  | 12 => 0x130a
  | 13 => 0x130b
  | 14 => 0x130e
  | 15 => 0x9c0d2
  | 16 => 0xc9d2
  | 17 => 0x9c0d5
  | 18 => 0xc9d5
  | 19 => 0x1
  | 20 => 0x9d2d2
  | 21 => 0x130c
  | 22 => 0x1300d2
  | 23 => 0xd312
  | 24 => 0x1300d3
  | 25 => 0xd313
  | 26 => 0x1300d6
  | 27 => 0x12c9d2
  | 28 => 0x12c9d5
  | 29 => 0x1309d2
  | 30 => 0x1309d3
  | 31 => 0x9d312
  | 32 => 0x9d313
  | 33 => 0x1309d6
  | 34 => 0x1692d2
  | 35 => 0x1312d2
  | 36 => 0x1312d3
  | 37 => 0x12d312
  | 38 => 0x12d313
  | 39 => 0x1312d6
  | 40 => 0x10c
  | 41 => 0x131692
  | 42 => 0x169312
  | 43 => 0x131693
  | 44 => 0x169313
  | 45 => 0x131696
  | 46 => 0x135312
  | 47 => 0x131352
  | 48 => 0x1309c0da
  | 49 => 0x9c0d31a
  | 50 => 0x1309c0db
  | 51 => 0x9c0d31b
  | 52 => 0x1309c0de
  | 53 => 0x9c116
  | 54 => 0x10a
  | 55 => 0x10b
  | 56 => 0x149d5
  | 57 => 0x9d355
  | 58 => 0x10e
  | 59 => 0x9d9d5
  | 60 => 0x9cbd5
  | 61 => 0x9d255
  | 62 => 0x9da15
  | 63 => 0x9cd55
  | 64 => 0x9d295
  | 65 => 0x178e
  | 66 => 0x58e
  | 67 => 0x9c155
  | 68 => 0x14d
  | 69 => 0xbcd
  | 70 => 0x19cd
  | 71 => 0xd4d
  | 72 => 0x1a0d
  | 73 => 0x134c
  | 74 => 0x1692d5
  | 75 => 0x19cc
  | 76 => 0xbcc
  | 77 => 0x184c
  | 78 => 0x168b55
  | 79 => 0xb8c
  | 80 => 0x1a0c
  | 81 => 0xd4c
  | 82 => 0x188c
  | 83 => 0x168cd5
  | 84 => 0xd0c
  | 85 => 0x169a55
  | 86 => 0xbd2d5
  | 87 => 0x19d2d5
  | 88 => 0x952d5
  | 89 => 0xd52d5
  | 90 => 0x1a12d5
  | 91 => 0x992d5
  | 92 => 0x1992d5
  | 93 => 0xbc0d5
  | 94 => 0x19c0d5
  | 95 => 0xd40d5
  | 96 => 0x1a00d5
  | 97 => 0x74c
  | 98 => 0x1a49c15d
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 40
  | 7 => 308
  | 6 => 596
  | 5 => 597
  | 4 => 46
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
  | 9 => packedAt gbK9 (16+((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 2)*1) 1
  | 8 => packedAt gbK8 (1208+((h/24+packedAt gbK8 (1040+(h % 24)*7) 7) % 125)*7) 7
  | 7 => packedAt gbK7 (13116+((h/172+packedAt gbK7 (11396+(h % 172)*10) 10) % 620)*10) 10
  | 6 => packedAt gbK6 (31193+((h/235+packedAt gbK6 (28608+(h % 235)*11) 11) % 1127)*11) 11
  | 5 => packedAt gbK5 (37353+((h/213+packedAt gbK5 (35223+(h % 213)*10) 10) % 1019)*11) 11
  | 4 => packedAt gbK4 (3310+((h/15+packedAt gbK4 (3220+(h % 15)*6) 6) % 62)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfc1fe3c1e0fe0ff8e070383ffc27c39e1cf90f
  | 1 => 0x1fe1fc01ff0ff0ff007fffc0fcda0c666331f3
  | 2 => 0x1ffe1ffe000fff0fff803fff031c307983ce3c
  | 3 => 0xe0001ffffff0000fffffc00003e03f81fc0fc0
  | 4 => 0x1ffffffffff00000000003ffc001fff000
  | 5 => 0xffffe000000000000000000003fffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x240220c060120118211088165800c18a0c5905
  | 1 => 0x9214400890490a100251280a04a0424212052
  | 2 => 0x1254091200092a024a00252801141050828228
  | 3 => 0x4000126532a0000c954a80020aa02a81540d80
  | 4 => 0x3111fb9dccfccc00603018c33ff4001fbf000
  | 5 => 0x9f99803018818880180c0630c3ffbf7e000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeafee8fee8fce8feeafee8fee8fce8feeafee8fee8fce8feeafee8fee8fce8feeafee8fee8fce8feeafee8fee8fce8feeafee8fee8fce8feeafee8fee8fce8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37183
namespace PEqualNP.Outside.L_meta_37183
open PEqualNP.Outside.L_meta_37183.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_2_0 : Interval s1Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 10 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_32 : Interval s1Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_64 : Interval s1Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_96 : Interval s1Atlas 3 96 16 := block_range (n:=16) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 112 := (concat (concat bs1_3_0 bs1_3_32) (concat bs1_3_64 bs1_3_96))
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
theorem bs1_4_96 : Interval s1Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_128 : Interval s1Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_160 : Interval s1Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_192 : Interval s1Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_224 : Interval s1Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_256 : Interval s1Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_288 : Interval s1Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_320 : Interval s1Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_352 : Interval s1Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_384 : Interval s1Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_416 : Interval s1Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_448 : Interval s1Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_480 : Interval s1Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_512 : Interval s1Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_544 : Interval s1Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_576 : Interval s1Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_608 : Interval s1Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_640 : Interval s1Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_672 : Interval s1Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_704 : Interval s1Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_736 : Interval s1Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_768 : Interval s1Atlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_800 : Interval s1Atlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_832 : Interval s1Atlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_864 : Interval s1Atlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_896 : Interval s1Atlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_928 : Interval s1Atlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_960 : Interval s1Atlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_992 : Interval s1Atlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1024 : Interval s1Atlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1056 : Interval s1Atlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1088 : Interval s1Atlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1120 : Interval s1Atlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1152 : Interval s1Atlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1184 : Interval s1Atlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1216 : Interval s1Atlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1248 : Interval s1Atlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1280 : Interval s1Atlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1312 : Interval s1Atlas 4 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1344 : Interval s1Atlas 4 1344 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 1345 := (concat (concat (concat (concat (concat bs1_4_0 bs1_4_32) (concat bs1_4_64 (concat bs1_4_96 bs1_4_128))) (concat (concat bs1_4_160 bs1_4_192) (concat bs1_4_224 (concat bs1_4_256 bs1_4_288)))) (concat (concat (concat bs1_4_320 bs1_4_352) (concat bs1_4_384 (concat bs1_4_416 bs1_4_448))) (concat (concat bs1_4_480 (concat bs1_4_512 bs1_4_544)) (concat bs1_4_576 (concat bs1_4_608 bs1_4_640))))) (concat (concat (concat (concat bs1_4_672 bs1_4_704) (concat bs1_4_736 (concat bs1_4_768 bs1_4_800))) (concat (concat bs1_4_832 (concat bs1_4_864 bs1_4_896)) (concat bs1_4_928 (concat bs1_4_960 bs1_4_992)))) (concat (concat (concat bs1_4_1024 bs1_4_1056) (concat bs1_4_1088 (concat bs1_4_1120 bs1_4_1152))) (concat (concat bs1_4_1184 (concat bs1_4_1216 bs1_4_1248)) (concat bs1_4_1280 (concat bs1_4_1312 bs1_4_1344))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_32 : Interval s1Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_64 : Interval s1Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_96 : Interval s1Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_128 : Interval s1Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_160 : Interval s1Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_192 : Interval s1Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_224 : Interval s1Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_256 : Interval s1Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_288 : Interval s1Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_320 : Interval s1Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_352 : Interval s1Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_384 : Interval s1Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_416 : Interval s1Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_448 : Interval s1Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_480 : Interval s1Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_512 : Interval s1Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_544 : Interval s1Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_576 : Interval s1Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_608 : Interval s1Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_640 : Interval s1Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_672 : Interval s1Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_704 : Interval s1Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_736 : Interval s1Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_768 : Interval s1Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_800 : Interval s1Atlas 5 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_832 : Interval s1Atlas 5 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_864 : Interval s1Atlas 5 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_896 : Interval s1Atlas 5 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_928 : Interval s1Atlas 5 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_960 : Interval s1Atlas 5 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_992 : Interval s1Atlas 5 992 25 := block_range (n:=25) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 1017 := (concat (concat (concat (concat (concat bs1_5_0 bs1_5_32) (concat bs1_5_64 bs1_5_96)) (concat (concat bs1_5_128 bs1_5_160) (concat bs1_5_192 bs1_5_224))) (concat (concat (concat bs1_5_256 bs1_5_288) (concat bs1_5_320 bs1_5_352)) (concat (concat bs1_5_384 bs1_5_416) (concat bs1_5_448 bs1_5_480)))) (concat (concat (concat (concat bs1_5_512 bs1_5_544) (concat bs1_5_576 bs1_5_608)) (concat (concat bs1_5_640 bs1_5_672) (concat bs1_5_704 bs1_5_736))) (concat (concat (concat bs1_5_768 bs1_5_800) (concat bs1_5_832 bs1_5_864)) (concat (concat bs1_5_896 bs1_5_928) (concat bs1_5_960 bs1_5_992)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_6_0 : Interval s1Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_6_32 : Interval s1Atlas 6 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls1_6 : Interval s1Atlas 6 0 48 := (concat bs1_6_0 bs1_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_7_0 : Interval s1Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_7 : Interval s1Atlas 7 0 1 := bs1_7_0
theorem alls1 : ∀ k ≤ 7, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
  · exact alls1_6 i (by omega) hi
  · exact alls1_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_0 : Interval s2Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 10 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_32 : Interval s2Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_64 : Interval s2Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_96 : Interval s2Atlas 3 96 16 := block_range (n:=16) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 112 := (concat (concat bs2_3_0 bs2_3_32) (concat bs2_3_64 bs2_3_96))
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
theorem bs2_4_128 : Interval s2Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_160 : Interval s2Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_192 : Interval s2Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_224 : Interval s2Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_256 : Interval s2Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_288 : Interval s2Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_320 : Interval s2Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_352 : Interval s2Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_384 : Interval s2Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_416 : Interval s2Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_448 : Interval s2Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_480 : Interval s2Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_512 : Interval s2Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_544 : Interval s2Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_576 : Interval s2Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_608 : Interval s2Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_640 : Interval s2Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_672 : Interval s2Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_704 : Interval s2Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_736 : Interval s2Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_768 : Interval s2Atlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_800 : Interval s2Atlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_832 : Interval s2Atlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_864 : Interval s2Atlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_896 : Interval s2Atlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_928 : Interval s2Atlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_960 : Interval s2Atlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_992 : Interval s2Atlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1024 : Interval s2Atlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1056 : Interval s2Atlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1088 : Interval s2Atlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1120 : Interval s2Atlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1152 : Interval s2Atlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1184 : Interval s2Atlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1216 : Interval s2Atlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1248 : Interval s2Atlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1280 : Interval s2Atlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1312 : Interval s2Atlas 4 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1344 : Interval s2Atlas 4 1344 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 1345 := (concat (concat (concat (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 (concat bs2_4_96 bs2_4_128))) (concat (concat bs2_4_160 bs2_4_192) (concat bs2_4_224 (concat bs2_4_256 bs2_4_288)))) (concat (concat (concat bs2_4_320 bs2_4_352) (concat bs2_4_384 (concat bs2_4_416 bs2_4_448))) (concat (concat bs2_4_480 (concat bs2_4_512 bs2_4_544)) (concat bs2_4_576 (concat bs2_4_608 bs2_4_640))))) (concat (concat (concat (concat bs2_4_672 bs2_4_704) (concat bs2_4_736 (concat bs2_4_768 bs2_4_800))) (concat (concat bs2_4_832 (concat bs2_4_864 bs2_4_896)) (concat bs2_4_928 (concat bs2_4_960 bs2_4_992)))) (concat (concat (concat bs2_4_1024 bs2_4_1056) (concat bs2_4_1088 (concat bs2_4_1120 bs2_4_1152))) (concat (concat bs2_4_1184 (concat bs2_4_1216 bs2_4_1248)) (concat bs2_4_1280 (concat bs2_4_1312 bs2_4_1344))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_64 : Interval s2Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_96 : Interval s2Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_128 : Interval s2Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_160 : Interval s2Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_192 : Interval s2Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_224 : Interval s2Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_256 : Interval s2Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_288 : Interval s2Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_320 : Interval s2Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_352 : Interval s2Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_384 : Interval s2Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_416 : Interval s2Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_448 : Interval s2Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_480 : Interval s2Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_512 : Interval s2Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_544 : Interval s2Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_576 : Interval s2Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_608 : Interval s2Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_640 : Interval s2Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_672 : Interval s2Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_704 : Interval s2Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_736 : Interval s2Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_768 : Interval s2Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_800 : Interval s2Atlas 5 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_832 : Interval s2Atlas 5 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_864 : Interval s2Atlas 5 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_896 : Interval s2Atlas 5 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_928 : Interval s2Atlas 5 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_960 : Interval s2Atlas 5 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_992 : Interval s2Atlas 5 992 25 := block_range (n:=25) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 1017 := (concat (concat (concat (concat (concat bs2_5_0 bs2_5_32) (concat bs2_5_64 bs2_5_96)) (concat (concat bs2_5_128 bs2_5_160) (concat bs2_5_192 bs2_5_224))) (concat (concat (concat bs2_5_256 bs2_5_288) (concat bs2_5_320 bs2_5_352)) (concat (concat bs2_5_384 bs2_5_416) (concat bs2_5_448 bs2_5_480)))) (concat (concat (concat (concat bs2_5_512 bs2_5_544) (concat bs2_5_576 bs2_5_608)) (concat (concat bs2_5_640 bs2_5_672) (concat bs2_5_704 bs2_5_736))) (concat (concat (concat bs2_5_768 bs2_5_800) (concat bs2_5_832 bs2_5_864)) (concat (concat bs2_5_896 bs2_5_928) (concat bs2_5_960 bs2_5_992)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_32 : Interval s2Atlas 6 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 48 := (concat bs2_6_0 bs2_6_32)
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
theorem bs3_2_0 : Interval s3Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 4 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 13 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 17 := block_range (n:=17) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 17 := bs3_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 1 := bs3_5_0
theorem alls3 : ∀ k ≤ 5, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_0 : Interval s4Atlas 2 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_32 : Interval s4Atlas 2 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_64 : Interval s4Atlas 2 64 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 65 := (concat bs4_2_0 (concat bs4_2_32 bs4_2_64))
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
theorem bs4_3_224 : Interval s4Atlas 3 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_256 : Interval s4Atlas 3 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_288 : Interval s4Atlas 3 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_320 : Interval s4Atlas 3 320 23 := block_range (n:=23) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 343 := (concat (concat (concat bs4_3_0 bs4_3_32) (concat bs4_3_64 (concat bs4_3_96 bs4_3_128))) (concat (concat bs4_3_160 (concat bs4_3_192 bs4_3_224)) (concat bs4_3_256 (concat bs4_3_288 bs4_3_320))))
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
theorem bs4_4_1312 : Interval s4Atlas 4 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1344 : Interval s4Atlas 4 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1376 : Interval s4Atlas 4 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1408 : Interval s4Atlas 4 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1440 : Interval s4Atlas 4 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1472 : Interval s4Atlas 4 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1504 : Interval s4Atlas 4 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1536 : Interval s4Atlas 4 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1568 : Interval s4Atlas 4 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1600 : Interval s4Atlas 4 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1632 : Interval s4Atlas 4 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1664 : Interval s4Atlas 4 1664 7 := block_range (n:=7) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 1671 := (concat (concat (concat (concat (concat bs4_4_0 (concat bs4_4_32 bs4_4_64)) (concat bs4_4_96 (concat bs4_4_128 bs4_4_160))) (concat (concat bs4_4_192 (concat bs4_4_224 bs4_4_256)) (concat (concat bs4_4_288 bs4_4_320) (concat bs4_4_352 bs4_4_384)))) (concat (concat (concat bs4_4_416 (concat bs4_4_448 bs4_4_480)) (concat bs4_4_512 (concat bs4_4_544 bs4_4_576))) (concat (concat bs4_4_608 (concat bs4_4_640 bs4_4_672)) (concat (concat bs4_4_704 bs4_4_736) (concat bs4_4_768 bs4_4_800))))) (concat (concat (concat (concat bs4_4_832 (concat bs4_4_864 bs4_4_896)) (concat bs4_4_928 (concat bs4_4_960 bs4_4_992))) (concat (concat bs4_4_1024 (concat bs4_4_1056 bs4_4_1088)) (concat (concat bs4_4_1120 bs4_4_1152) (concat bs4_4_1184 bs4_4_1216)))) (concat (concat (concat bs4_4_1248 (concat bs4_4_1280 bs4_4_1312)) (concat (concat bs4_4_1344 bs4_4_1376) (concat bs4_4_1408 bs4_4_1440))) (concat (concat bs4_4_1472 (concat bs4_4_1504 bs4_4_1536)) (concat (concat bs4_4_1568 bs4_4_1600) (concat bs4_4_1632 bs4_4_1664))))))
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
theorem bs4_5_864 : Interval s4Atlas 5 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_896 : Interval s4Atlas 5 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_928 : Interval s4Atlas 5 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_960 : Interval s4Atlas 5 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_992 : Interval s4Atlas 5 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_1024 : Interval s4Atlas 5 1024 20 := block_range (n:=20) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 1044 := (concat (concat (concat (concat (concat bs4_5_0 bs4_5_32) (concat bs4_5_64 bs4_5_96)) (concat (concat bs4_5_128 bs4_5_160) (concat bs4_5_192 bs4_5_224))) (concat (concat (concat bs4_5_256 bs4_5_288) (concat bs4_5_320 bs4_5_352)) (concat (concat bs4_5_384 bs4_5_416) (concat bs4_5_448 bs4_5_480)))) (concat (concat (concat (concat bs4_5_512 bs4_5_544) (concat bs4_5_576 bs4_5_608)) (concat (concat bs4_5_640 bs4_5_672) (concat bs4_5_704 bs4_5_736))) (concat (concat (concat bs4_5_768 bs4_5_800) (concat bs4_5_832 bs4_5_864)) (concat (concat bs4_5_896 bs4_5_928) (concat bs4_5_960 (concat bs4_5_992 bs4_5_1024))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_32 : Interval s4Atlas 6 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 48 := (concat bs4_6_0 bs4_6_32)
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
theorem bs5_2_0 : Interval s5Atlas 2 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_32 : Interval s5Atlas 2 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_64 : Interval s5Atlas 2 64 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 65 := (concat bs5_2_0 (concat bs5_2_32 bs5_2_64))
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
theorem bs5_3_224 : Interval s5Atlas 3 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_256 : Interval s5Atlas 3 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_288 : Interval s5Atlas 3 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_320 : Interval s5Atlas 3 320 23 := block_range (n:=23) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 343 := (concat (concat (concat bs5_3_0 bs5_3_32) (concat bs5_3_64 (concat bs5_3_96 bs5_3_128))) (concat (concat bs5_3_160 (concat bs5_3_192 bs5_3_224)) (concat bs5_3_256 (concat bs5_3_288 bs5_3_320))))
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
theorem bs5_4_1312 : Interval s5Atlas 4 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1344 : Interval s5Atlas 4 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1376 : Interval s5Atlas 4 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1408 : Interval s5Atlas 4 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1440 : Interval s5Atlas 4 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1472 : Interval s5Atlas 4 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1504 : Interval s5Atlas 4 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1536 : Interval s5Atlas 4 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1568 : Interval s5Atlas 4 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1600 : Interval s5Atlas 4 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1632 : Interval s5Atlas 4 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1664 : Interval s5Atlas 4 1664 7 := block_range (n:=7) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 1671 := (concat (concat (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat bs5_4_96 (concat bs5_4_128 bs5_4_160))) (concat (concat bs5_4_192 (concat bs5_4_224 bs5_4_256)) (concat (concat bs5_4_288 bs5_4_320) (concat bs5_4_352 bs5_4_384)))) (concat (concat (concat bs5_4_416 (concat bs5_4_448 bs5_4_480)) (concat bs5_4_512 (concat bs5_4_544 bs5_4_576))) (concat (concat bs5_4_608 (concat bs5_4_640 bs5_4_672)) (concat (concat bs5_4_704 bs5_4_736) (concat bs5_4_768 bs5_4_800))))) (concat (concat (concat (concat bs5_4_832 (concat bs5_4_864 bs5_4_896)) (concat bs5_4_928 (concat bs5_4_960 bs5_4_992))) (concat (concat bs5_4_1024 (concat bs5_4_1056 bs5_4_1088)) (concat (concat bs5_4_1120 bs5_4_1152) (concat bs5_4_1184 bs5_4_1216)))) (concat (concat (concat bs5_4_1248 (concat bs5_4_1280 bs5_4_1312)) (concat (concat bs5_4_1344 bs5_4_1376) (concat bs5_4_1408 bs5_4_1440))) (concat (concat bs5_4_1472 (concat bs5_4_1504 bs5_4_1536)) (concat (concat bs5_4_1568 bs5_4_1600) (concat bs5_4_1632 bs5_4_1664))))))
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
theorem bs5_5_864 : Interval s5Atlas 5 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_896 : Interval s5Atlas 5 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_928 : Interval s5Atlas 5 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_960 : Interval s5Atlas 5 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_992 : Interval s5Atlas 5 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_1024 : Interval s5Atlas 5 1024 20 := block_range (n:=20) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 1044 := (concat (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 bs5_5_96)) (concat (concat bs5_5_128 bs5_5_160) (concat bs5_5_192 bs5_5_224))) (concat (concat (concat bs5_5_256 bs5_5_288) (concat bs5_5_320 bs5_5_352)) (concat (concat bs5_5_384 bs5_5_416) (concat bs5_5_448 bs5_5_480)))) (concat (concat (concat (concat bs5_5_512 bs5_5_544) (concat bs5_5_576 bs5_5_608)) (concat (concat bs5_5_640 bs5_5_672) (concat bs5_5_704 bs5_5_736))) (concat (concat (concat bs5_5_768 bs5_5_800) (concat bs5_5_832 bs5_5_864)) (concat (concat bs5_5_896 bs5_5_928) (concat bs5_5_960 (concat bs5_5_992 bs5_5_1024))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_32 : Interval s5Atlas 6 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 48 := (concat bs5_6_0 bs5_6_32)
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
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 46 := (concat bgb_4_0 bgb_4_32)
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
theorem bgb_5_576 : Interval gbAtlas 5 576 21 := block_range (n:=21) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 597 := (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)))) (concat (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 (concat bgb_5_384 bgb_5_416))) (concat (concat bgb_5_448 bgb_5_480) (concat bgb_5_512 (concat bgb_5_544 bgb_5_576)))))
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
theorem bgb_6_576 : Interval gbAtlas 6 576 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 596 := (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)))) (concat (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 (concat bgb_6_384 bgb_6_416))) (concat (concat bgb_6_448 bgb_6_480) (concat bgb_6_512 (concat bgb_6_544 bgb_6_576)))))
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
theorem bgb_7_288 : Interval gbAtlas 7 288 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 308 := (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 bgb_7_192) (concat bgb_7_224 (concat bgb_7_256 bgb_7_288))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 40 := (concat bgb_8_0 bgb_8_32)
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 4 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 8 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 8 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 33, 49),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 9, 25)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeafee8fee8fce8feeafee8fee8fce8feeafee8fee8fce8feeafee8fee8fce8feeafee8fee8fce8feeafee8fee8fce8feeafee8fee8fce8feeafee8fee8fce8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 49 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276813544 * 2 ^ 32 + 4276681960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37183.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,3]⟩,⟨.and,[1,2]⟩,⟨.or,[4,5]⟩,⟨.or,[6,7]⟩,⟨.and,[4,5]⟩,⟨.or,[1,2]⟩,⟨.and,[9,11]⟩,⟨.and,[3,8]⟩,⟨.or,[10,13]⟩,⟨.and,[0,14]⟩,⟨.or,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813544 * 2 ^ 32 + 4276681960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813544 * 2 ^ 32 + 4276681960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37183

open PEqualNP.Outside.L_meta_37183 in
theorem PEqualNP.Outside.L_meta_37183 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813544 * 2 ^ 32 + 4276681960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813544 * 2 ^ 32 + 4276681960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
