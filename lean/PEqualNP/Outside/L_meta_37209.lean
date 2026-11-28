import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37209.Model
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


end PEqualNP.Outside.L_meta_37209.Model

namespace PEqualNP.Outside.L_meta_37209
open PEqualNP.Outside.L_meta_37209.Model
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

def SBf (j : Nat) : Nat := [7, 6, 6, 7, 7, 8].getD j 0

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

def mirrorSteps : List Move := [swapRows 67]

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

end PEqualNP.Outside.L_meta_37209

namespace PEqualNP.Outside.L_meta_37209
open PEqualNP.Outside.L_meta_37209.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x1200f800c690174a00000101422a26053ab420131944606230008691140d49b2854e9238787875058010009058e001032001d200638a1520c1ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x12380000500c04005c9e14260060001800440a5a008a4e002200ae0090a0b4400016000200009c78009874009600003a00005210640082005600000062000000006a000608007a340000926c004800002c002a240000322800b6000000aa6e365e00000000b27094008e88540000000000000000a81a1c76000030002e20589a683c84ac72807e4aa68ca23e00000000000000a4b046007c00421e4c66860e00000102010002080206070000000200000800080103010101010000020c050eb7a92876c5250ebea6a15714d429faa2653c544cb9a64194f943419eaa4835f53506b8a6a0dbd4941b6292837b50506f0a0a0e7d4d41ce29a83af5250758a4a0edd4541dda82833c5050770a0a0ce141419f2a0836e52cc6daa598cf952319eaa4636e528c6daa518cf950319eaa0635e53c86baa790cf952219eaa4435e53886baa710cf950219eaa0435e53902baa7205b94a40b6a94819e539033aa7206b94a40d6a94813d519027ca1204f544409f28081ba501027ca9984f553309faa2613c544c2dea4985b14930bba8a6174514c2dca4185b548309f2a6413d54c827ea8904f15120afa9a415c53482eea2905d14520af298415d530827ca9884f55310dc206213f5484278a9084fd51109e2a2215f53442b8a6885bd4910b6292213e540427aa8085794c10aea98216e52042daa4086e10010
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0xe04002086ca70a3191320cb0c5314941c6d4c50507185314141cad4850507285214141c394e52902396510010
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 8
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
  | 6 => packedAt s0K6 (6+((h/1+packedAt s0K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s0K5 (788+((h/14+packedAt s0K5 (704+(h % 14)*6) 6) % 53)*7) 7
  | 4 => packedAt s0K4 (2724+((h/30+packedAt s0K4 (2484+(h % 30)*8) 8) % 161)*8) 8
  | 3 => packedAt s0K3 (312+((h/2+packedAt s0K3 (304+(h % 2)*4) 4) % 12)*4) 4
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xfffffff81fffffe07ffffffffe03fffe3ffe3f
  | 2 => 0x3f81ffffffffffff81f03e07ffffffffc88fff
  | 3 => 0x3ffe03ffe03f81fffe003ff83ffc1f01f0f3cc
  | 4 => 0xc00003ffffc001ffffffc0003fffe001ff03f0
  | 5 => 0xfffffc00000001ffffffffffc0000001fffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x84882808c489082016514a284a212954133615
  | 2 => 0x11245191091260c580a4148694c652a8c888ea
  | 3 => 0xa6149aa243a42b6aaa0927b227691c0d70d34c
  | 4 => 0x3459634492074db34d3d812439b38831bd03b0
  | 5 => 0x386183871c3871dc71ce39c701c210c1eeec00
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcccccc0f0c0c0c0fcccccc0f0c0c0c0fcccccc0f0c0c0c0fcccccc0f0c0c0c0fcccccc0f0c0c0c0fcccccc0f0c0c0c0fcccccc0f0c0c0c0fcccccc0f0c0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37209
namespace PEqualNP.Outside.L_meta_37209
open PEqualNP.Outside.L_meta_37209.Model
def s1K5 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x5800004006141007086aa80a00201299e380022b0002890002e3060000c2000482fe65f8cbe997c32fe63f8c7e98fc31fe43f887e90fc21fe61f8c3e987c30fe41f883e907c20fe21f843e887c10
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x118d0041080480039f004d28e0088f1c1400c06000c9110008a8f025028c346ce80325c00416010084c240002c0000050c418001b0c002d90732b541ccad90632b5418cb34c832ae42cc6b50b31ae428c6b50a31d5310c6790f219d43c86790e219d43887948421af424c2b10930b7414c2d10530ae420c2b50830b6410c2d504309f43482710d20b741482d105209e43082750c20b641082d504209f43442710d10af42442b109109e43042750c10ae42042b50810
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 24
  | 3 => 39
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*4) 4
  | 4 => packedAt s1K4 (i*15) 15
  | 3 => packedAt s1K3 (i*26) 26
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (5+((h/1+packedAt s1K5 (4+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s1K4 (408+((h/8+packedAt s1K4 (360+(h % 8)*6) 6) % 37)*6) 6
  | 3 => packedAt s1K3 (1092+((h/13+packedAt s1K3 (1014+(h % 13)*6) 6) % 51)*7) 7
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffbff7fffe3ffff1ff
  | 2 => 0xffffffffffffffffffffffd5f8e73fc71c7e93
  | 3 => 0xe6ff07cff81f8f1c
  | 4 => 0xf8fff80fffe00fe0
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff4010000009040025
  | 2 => 0x2a264a4642496692
  | 3 => 0x1942d41a90932b18
  | 4 => 0x78486ad24c24dc0
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 29 s1Pos s1Neg, 0xfaaaaaa0faaaaaa0faaaaaa0faaaaaa0faaaaaa0faaaaaa0faaaaaa0faaaaaa0faaaaaa0faaaaaa0faaaaaa0faaaaaa0faaaaaa0faaaaaa0faaaaaa0faaaaaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37209
namespace PEqualNP.Outside.L_meta_37209
open PEqualNP.Outside.L_meta_37209.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x511820381030100300df32ee32dd32ed32cd32be41bc41bf40bd40
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x4a602ce800000a6a9c658f544cb18a899634ca41c6990838d32d031a64a04d14540
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x86100a1987544ca0f654ca418319532503053214540
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 9
  | 3 => 8
  | 2 => 4
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (i*5) 5
  | 4 => packedAt s2K4 (i*16) 16
  | 3 => packedAt s2K3 (i*27) 27
  | 2 => packedAt s2K2 (i*38) 38
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (6+((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s2K4 (156+((h/3+packedAt s2K4 (144+(h % 3)*4) 4) % 12)*5) 5
  | 3 => packedAt s2K3 (224+((h/2+packedAt s2K3 (216+(h % 2)*4) 4) % 12)*4) 4
  | 2 => packedAt s2K2 (155+((h/1+packedAt s2K2 (152+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xe0ffffffffffff81fe0ff07ffffffffe463fff
  | 1 => 0xff07fe07e0fc1ffe1ff0ff87e0f0783fb9ce93
  | 3 => 0xfff83ff800ffe1ffe000fff8ff007fc1c1f31c
  | 4 => 0x3fffff0001ffffff0000ffff8001fe03e0
  | 5 => 0xffffc000000001ffffffffff00000001fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x28000241002000004401200901140a10021425
  | 1 => 0x425184324548a8960a50528268a150ac98ca92
  | 3 => 0x8432a890d6928baaa1489b50ba826585c16318
  | 4 => 0x16a53124941acdcd336a0a40dccb4109ec03c0
  | 5 => 0x18c621c718e31171dd8cec64100c063177bc00
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeeeee88aaaaaa88eeeeee88aaaaaa88eeeeee88aaaaaa88eeeeee88aaaaaa88eeeeee88aaaaaa88eeeeee88aaaaaa88eeeeee88aaaaaa88eeeeee88aaaaaa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37209
namespace PEqualNP.Outside.L_meta_37209
open PEqualNP.Outside.L_meta_37209.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x8c031300002b007c1004a18000002d2225884e9a08bc19700b4f001a986301454e20365872e0e50400520000920002800000000500138000000910000000006499200a878000080000b000410102244000c18000ff43fe43be43fd43fc43bc43ff42bf42fe42fd42bd42fc42ff32df32fe32fd32dd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x812e12c6a1636138b46f0994caa0000000003f001f0bc000722c0e000624492153e81846174718444922f86d44003d9c808390015098011b14942374a9b4005d23918c4023000048420a21c9008221343c000e000829f201dc5c9a0e92868053c0a44e650810c42a31d801180a2b848a02b3c9f840000c24d40660787d380000000000000211482a42a001698480e8002800000066b169c4002f00274001a34000000013000003c338240000001652e2c0018c009900000d2740023c003d0c9d4e60d4b13c8a00000c40000199fc005b2c1e87c7041990ac51001d93c6a002080000452340000001b8609b4a21822881c0c9122500818000000001808481070000028180000082859900800105001102098280008102018102800082120000808202018206118002000886cf94e439ea94873e5190e7aa121db94843b6a90873e5310f3ca621eb948439ea9087ad5210e5aa421cf944439ea80873e53d0a7ca3a14f543429eaa4855e5390abaa7214f14d42d7a92853c5150a7ea0a14f95042af298855d5310a7ea9994f15332cf21e659c43ccb3ea9996715332cfa16659d42cca7ca9194f55232aea9c65ad428ca7ea8994f15132cf21a659c434cb5a849967d5132ce2a265cf524cb3e84997390932cea1265cd424cb1a84994f950329eaa0655e530cabca720d754e419f29c839e539063ca720e754e419ea94839f329073a6520cf946419ea84833e531067aa420e7cc841ce990833e511076ca220cf540419f2a6633d54cc7388798db94b31b6a96633e548c67aa918cfd51319e2a2639c434c67ea818cf150319f2a6433d54c86bca790d754f219faa4433c548879a6510cfd51219e2a2433e540867aa810d794c21aea9843cd32086f4a010de540219f29e813d52d033e65a0674cb409f28e813d54902bea6a05714d40cfa9a813c5350338a6a04714d409fa92819f325033a64a04f14540dda82813e541027ea9984f153309f2a4613d548c33887184fd51309e2a2613e540c27aa8186710c30b7290616d520c2eca2185d544309f2a6413d54c82bca7905754f20e6996413e548827aa9104f951209eaa241cd324827ca8104f55020af298415d53082eca2105d544209faa6213c54c427ca9084f552109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0xcd39a00ec1802e70000280000000a1b92406d48b4a4180042c402d1ed00082c00c8018097910e980350054e8000009b6000053a00000803c1992a0801c8e307c038560160046b80051a900094400284000008303000820102381040000580c394d5210f0e63548438798e51d0a1c63543428d98754cca8d62d5332a598754cca8d62153328b195424ca8d6490932a3995424ca8c6550932a3185424ca8f60509329358a539062d6294e41a358a539070e6294e418758a539070d6294e418358a539061f65cca4187d95329070d524c8418718d501068d6210f31c310d52cc68d6210d318798f540c62d62150318e580540c61e63d5221c3d51328861e63d5121c355132087493254021c354932d021e639474093588535022d6214d40a3588535030e6214d4087588535030d6214d4083588535021c65cc94087195325022d6215330a3588438c21d6510c30a3588430c30c4354830c510d510c30d544cb208718d548821c63551208d185544830d544c9208798f54c421c6355210
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x290003990248c200101282b8cc6a9087219c6655093281ae431aa020c0d7298f5448606b94c728e81415c84354430818ecaa26490504715513248206b94c7aa621035c86355210
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (i*5) 5
  | 5 => packedAt s3K5 (i*16) 16
  | 4 => packedAt s3K4 (i*27) 27
  | 3 => packedAt s3K3 (i*38) 38
  | 2 => packedAt s3K2 (i*49) 49
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (6+((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s3K5 (912+((h/16+packedAt s3K5 (800+(h % 16)*7) 7) % 80)*7) 7
  | 4 => packedAt s3K4 (4895+((h/55+packedAt s3K4 (4455+(h % 55)*8) 8) % 218)*9) 9
  | 3 => packedAt s3K3 (2420+((h/20+packedAt s3K3 (2280+(h % 20)*7) 7) % 88)*7) 7
  | 2 => packedAt s3K2 (502+((h/3+packedAt s3K2 (490+(h % 3)*4) 4) % 15)*5) 5
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xf07ffc3ffffc3fc1fe1fc3fe1fffc1fe8cf3cf
  | 1 => 0xff87ffc1f0ffc3fe1fe1fc3fe1c1fe1f733d33
  | 2 => 0xfff87ffe00fffc7fe001ffc7fe01ffe183ce3c
  | 4 => 0x7fffff00007ffffe0007fffe0001fc0fc0
  | 5 => 0xffff80000000007ffffffff800000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x14000408402040004402404802504088045045
  | 1 => 0x212108848148040a0a20841220849414312512
  | 2 => 0x421251102a9220d4a1112a8554092941828a28
  | 4 => 0xb556225281aa96733542207992c0c45d80f80
  | 5 => 0x8c6643b9cce33279dd99f32110303199eff000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeeeee8e8eaeae8e8eeeee8e8eaeae8e8eeeee8e8eaeae8e8eeeee8e8eaeae8e8eeeee8e8eaeae8e8eeeee8e8eaeae8e8eeeee8e8eaeae8e8eeeee8e8eaeae8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37209
namespace PEqualNP.Outside.L_meta_37209
open PEqualNP.Outside.L_meta_37209.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x3e0000600000000000d023a0160406796ae1a311a62a65288383921b00003800001489281400b624000a009c0004000018024402f2ca098054491001e84bb0000002b0000001830a0400c10001810a00000ff43fe43be43fd43fc43bc43ff42bf42fe42fd42bd42fc42ff32df32fe32fd32dd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x138769d001780000000c800000000000000000000000019c000000058000000000f40000000964d390005800480003000000000026351b80000002912c782c9108000288000000418746a4f00044004712930e6000023c001b4fa2502001ba2826523b1acfa5a000012600219dd0e8e1c270d200070b4344200000cc7c4a0e47c1e0f8a542414d800c488110009400000011a003184800792d8c00000000000000008000000000080000000f0e22700218ac002f8700000001f800000c80000002e000002e4a94c0000000010a0000190008200001342a08000004619914002418a644000000d8000000000000002001460000000003f48800743424800aea242000d800378001200001fc00000000c0000038000000001200000000000070001d442000002800002c15418000001400980a800006100000468c1e83c002b00000000040180f6684b800e8280002ca0650005c100636a481a5d1795140004f22c28000000200008141c000100c0000008080200010080002000141400018000000008000001008040004018040001000001200008000200008000002000040600004f94e439ea94873e5190e7aa121db94843b6a90873e5310f3ca621eb948439ea9087ad5210e5aa421cf944439ea80873e53d0a7ca3a14f543429eaa4855e5390abaa7214f14d42d7a92853c5150a7ea0a14f95042af298855d5310a7ea9994f15332cf21e659c43ccb3ea9996715332cfa16659d42cca7ca9194f55232aea9c65ad428ca7ea8994f15132cf21a659c434cb5a849967d5132ce2a265cf524cb3e84997390932cea1265cd424cb1a84994f950329eaa0655e530cabca720d754e419f29c839e539063ca720e754e419ea94839f329073a6520cf946419ea84833e531067aa420e7cc841ce990833e511076ca220cf540419f2a6633d54cc7388798db94b31b6a96633e548c67aa918cfd51319e2a2639c434c67ea818cf150319f2a6433d54c86bca790d754f219faa4433c548879a6510cfd51219e2a2433e540867aa810d794c21aea9843cd32086f4a010de540219f29e813d52d033e65a0674cb409f28e813d54902bea6a05714d40cfa9a813c5350338a6a04714d409fa92819f325033a64a04f14540dda82813e541027ea9984f153309f2a4613d548c33887184fd51309e2a2613e540c27aa8186710c30b7290616d520c2eca2185d544309f2a6413d54c82bca7905754f20e6996413e548827aa9104f951209eaa241cd324827ca8104f55020af298415d53082eca2105d544209faa6213c54c427ca9084f552109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0xe0e1e00edd0b288daac20484af4c10002520121700ac6b26c5800000a8025321c01d420000f50c401a0a88a8000d00130c3840014dcda76680018604568300057390030f800024048270000302000028a00141810000600c394d5210f0e63548438798e51d0a1c63543428d98754cca8d62d5332a598754cca8d62153328b195424ca8d6490932a3995424ca8c6550932a3185424ca8f60509329358a539062d6294e41a358a539070e6294e418758a539070d6294e418358a539061f65cca4187d95329070d524c8418718d501068d6210f31c310d52cc68d6210d318798f540c62d62150318e580540c61e63d5221c3d51328861e63d5121c355132087493254021c354932d021e639474093588535022d6214d40a3588535030e6214d4087588535030d6214d4083588535021c65cc94087195325022d6215330a3588438c21d6510c30a3588430c30c4354830c510d510c30d544cb208718d548821c63551208d185544830d544c9208798f54c421c6355210
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x8a0404c70240419c4282b8cc6a9087219c6655093281ae431aa020c0d7298f5448606b94c728e81415c84354430818ecaa26490504715513248206b94c7aa621035c86355210
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
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
  | 5 => packedAt s4K5 (912+((h/16+packedAt s4K5 (800+(h % 16)*7) 7) % 80)*7) 7
  | 4 => packedAt s4K4 (4950+((h/55+packedAt s4K4 (4455+(h % 55)*9) 9) % 316)*9) 9
  | 3 => packedAt s4K3 (2420+((h/20+packedAt s4K3 (2280+(h % 20)*7) 7) % 80)*7) 7
  | 2 => packedAt s4K2 (502+((h/3+packedAt s4K2 (490+(h % 3)*4) 4) % 13)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xf07ffc3ffffc3fc1fe1fc3fe1fffc1fe8cf3cf
  | 1 => 0xff87ffc1f0ffc3fe1fe1fc3fe1c1fe1f733d33
  | 2 => 0xfff87ffe00fffc7fe001ffc7fe01ffe183ce3c
  | 3 => 0x7fffff00007ffffe0007fffe0001fc0fc0
  | 5 => 0xffff80000000007ffffffff800000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x14000408402040004402404802504088045045
  | 1 => 0x212108848148040a0a20841220849414312512
  | 2 => 0x421251102a9220d4a1112a8554092941828a28
  | 3 => 0xb556225281aa96733542207992c0c45d80f80
  | 5 => 0x8c6643b9cce33279dd99f32110303199eff000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeee8eee8eae8eae8eee8eee8eae8eae8eee8eee8eae8eae8eee8eee8eae8eae8eee8eee8eae8eae8eee8eee8eae8eae8eee8eee8eae8eae8eee8eee8eae8eae8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37209
namespace PEqualNP.Outside.L_meta_37209
open PEqualNP.Outside.L_meta_37209.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x4480a800ea0b80067808d365000f2284016342c1064e00829001092a4c00e931c251980a215800071200147cc8c4a04000e080007062000240ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31df31fe31fd31dd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xe61bd41cc3be6398774c730bfaa4617e548c2faa9185f15230bea9c61df438c3b887185f94a30bea9461de328c3b865185f94630bea8c61bf418c37a831877cc630ee98c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130ef21a61dd434c2fea4985f14930ef99261dd324c2fea2985f14530dfa0a61bd414c3be6298774c530fd98261de304c2fea8185f95030df2a0613e540c2faa8186f550309eaa0617c540c2fca61877d0c30ee218617e520c3dca4185b94830bea9061ed520c2daa418778c830ee190617e510c3eca2185d94430bea8861f5510c2eaa2186fd0430dea0861df310c3ba62185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c83dc65907b4cb20bf28e417d51c837e83906f50720ef98e41dd31c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3106fd0620dea0c41df31883ba63105f94220f790441fb20882fea8906fd51209faa2417e54482faa8905f15120de2a2413c54482fea69077d4d20afa9a417e53482faa6905f14d20ee29a415c53483dc84907b50920f719241ed32482fea2907dd4520bba8a417c51483e8a2905d14520dfa0a41bd41483be6290774c520f790a41ed21483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20bf290417e51083eca2105d94420bea8841f551082eaa2106fd0420dea0841df31083ba62105f94020f790041fa20083da40107e48020bfaa6217e54c437ca9884f95310beaa621bd54c427aa9885f15310bfa9e217e53c43bca7885794f10bea9e21dd53c42baa7885f14f10bfa96217e52c42faa5885f14b10dfa0e21f641c437a83887d50710daa0e21df31c43ec6388774c710fa98e21d531c43ec43887d48710bfaa4217e54842faa9085f15210bfa9c217e53842faa7085f14e10bfa94217e52842faa5085f14a10bea8c21bf418437a830877cc610ee98c21f721843e843085f94210fd10421f920843ee21087ec4210bfaa2217e54442faa8885f15110bfa9a217e53442faa6885f14d10bfa92217e52442faa4885f14910dfa0a21f6414437a82887d50510daa0a21df31443ec6288774c510fa98a21d531443ec42887d48510fd10221f920443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf28821bf410437a820877cc410ee98821f721043e842085f94010fb88021fa10043ea20087e44010
  | 1 => 0xf42cc7bc8598f750b31ee21663df41cc73e8398f790731eea0e639d41cc7b88398f7d4331ef28663dd50cc7b8a198dfd5231bf2a463be548c67ca918df55231deaa4633d548c6f8a918df54e31aea9c637e528c6faa518df94631dfa0c63f6418c77a8318fd50631daa0c63df318c7ee6318df94231bea84637f544c6fca898df55131be2a263df434c7bc8698f750d31ee21a637f524c6f8a498f7cc931ef19263dd324c7b86498efd0531fb20a63bd414c7ea8298ed50531fb98a63de314c6fea098df14131efaa263de544c7baa898f715131efa9263de524c7baa498f714931efa1263de424c7ba8498f710931efa8a63d7514c7be8298e7d0531ef20a63d6414c7ba8298e750531eaa0a6395414c7b88298f7d4131ef28263dd504c7b8a098dfd5031bf2a063be540c67ca818df55031deaa0633d540c6f8a818df94c31af298637e520c6faa418df94431dfa0863bd410c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21dfa0e43f641c877a8390fd50721daa0e43df31c87ec6390f74c721fa98e43d531c86fca190df54321bfaa4437e548877ca910cf95221beaa443bd548867aa910df15221bfa9c437e53887bca710d794e21bea9c43dd53886baa710df14e21bea94437e518877e8310ef50621ef98c43dd31887de4310fdc8621bf284437d50886fea890df95121beaa2437c54486fea690df94d21bea9a437c534877e8290ef50521ef98a43dd31487ee4290fb88521bfa82437c50486fea810df95021df2a0433e54086faa810ef550219eaa0437c54086fea610df94c21ef298435e53086faa610f754c21aea98437c53086fca410df94421dfa0843f6410877a8210fd50421daa0843df31087ec6210f74c421fa98843d531087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d037e87a06f50f40bf296817d52d037e85a06f50b40bf28e817d51d037e83a06f50740ef98e81dd31d02faa9205f94e40bea9c81be439037887205f94a40bea9481be429037885205f94640bea8c81bf419037a832077cc640ee98c817e509037e81207ed0240bfa9a81df53502bea6a05f14d40ee29a815c535037e86a06f50d40bfa92817c525037e84a06f50940bfa8a817c515037e82a06f50540ef98a81dd31503f680a06f90140bf2a0817e53103bca6205794c40bea9881dd53102baa6206f90c40de218817e52103dca4205b94840bea9081ed52102daa4206f90840de210817e51103eca2205d94440bea8881f551102eaa2206fd0440dea0881df31103ba62205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30ef99661dd32cc2fca3985f54730dfa0
  | 2 => 0xc0000780201e03c02000002048000020080080400402007401002018000008030040100001300e008018020000040380400600c0600000a0480580200a00c00008000002fca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43cea18877e5210efaa421df94443fb28887765110efaa221fd54443baa88877e5010efaa021df94f42ef29e855e53d0afaa7a17754f42aea9e85be43d0b7887a15f94742fb28e857651d0afaa3a17d54742baa8e857e50d0afaa1a15f55242bf29c85de5390abca7215f54e42eea9c855d5390b7e87216f50e42bf29485bf4290bde85215f94642bea8c857e5090afaa1215fd4d42be29a85be4350b7886a17bd0942df212857f5150af8a2a15fd4142be282857e5410afca6215f54c42dfa1885bd4310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0215fd5332bf2a665be54cca7ca9995f55332deaa6653d54ccaf8a99977d0f32ee21e657e51ccbeca3995d94732bea8e65f551ccaeaa3995f94332bea86657f548cafca9196f952329f2a4657d548cb7aa9194f55232be2a4657d538cbbc87197750e32bf29465df328cbde65195f94632bea8c657e508cafaa1195fd5132bf2a2657d544caf8a89977d0d32ee21a65ef324cbbc64995fd4532be28a657f504caf8a0995fd5032bf2a0657d540caf8a8195f94c32ef21865dd430cafca41977cc832f719065dd320cbda64195f94432bea88657e500cafaa0195f94f41bea9e83bf43d077c87a0ef50f41de21e837e52d06faa5a0efd0b41df21683bd42d077885a0df94341bea8683bf53d077ca7a0ef54f41de29e83bf52d077ca5a0ef54b41de29683bf32d077c65a0ef4cb41de19683bf50d077ca1a0ef54341de286837d549067aa920df94e41ef29c835e53906faa720f754e41aea9c837e52906faa520df94641dfa0c83f741906fca120df54241bfa9a837c535077e86a0ef90d41dea1a83bc43506fea4a0df14941dfa1283be425077a84a0ef10941fba0a83be41506fea0a0df14141dfa9a83be535077aa6a0ef14d41dfa9283be525077aa4a0ef14941df99283be325077a64a0ef0c941dfa8a83b7515077ea0a0ef94141dea8283bc50506fca820cf95041bf29883de53106bca620df54c41eea98835d53106fca420df54841bf28883bf41107ec8220ef50441faa08837e50106faa020dfd5331bf2a6637d54cc6f8a998f7d0f31ef21e63dd43cc7b88798df94b31bea9663df32cc7bc6598f74cb31ee19663bf41cc77a8398df94331bea8663df54cc7bca998f755331ee2a663df52cc7bca598f754b31ee29663d
  | 3 => 0xc00003b6f2540007c14c56c648ea8fd42c619a9000232708870af2dac44002475c43e48f000000b2ca9915000860fba5d2ec000b315b0000002d2b10a447cdb3330000000016c00073400223160000c822a29a8f04e0e71029c545aa10009fdab00000000000339000ca40011721600000331000210002e0000001468003ead68b3b5f120b04311ef0506b80001a19a10d6f8006ead4d5582c190a1c00000000044001f6026000000000007440baae6080012c83f0008b8928106341b57a00018c00194144000c8400000000000000d31c02999f8bb5861fc9ba7b3e80016a913386000380cc6e40017cae719e61d5f05e000295050005d8cbc00000438001648ea0dc97cab9c94b4000bf2430003b45602b1e851c00149042470002bb3a8b180000033e4d0c51e70aed640005568ebc4103085ac00088200014a00ba0002d45a0d9895000b5c00000370000e08cb340a20799cb548a28793152125801dacd2241446da600007ec000000007a10835e5d4358b285301621cc6309044c0c0c97925c5893692915cd344f81b0e4a24a41af3d8384821f167661116a0d22c4f8aa3176303bc228153fc0591a0180981186515650ac34c49da1c8908f929e35800000265000c140f2112808e0000330006c40034235a000003413484e11100003a5097b21b20622c00194000000001324de9cd40a9b418cf59a07b4028c048a28000000238992a2bc8000382448f9602dd670165331b96e22385506c5c2374003500ee740c581f6a2d74a3155638a883d2a635252ccb19c4ee0a90ea74452d941aa950460204982521a26c000000007900000066c00000000000000648000007fc958000002ad2da52064d24fc8643e0260001720000005e8005dc6450fb602a07809d1df58aa305b09d6249a5729ba47ac8d6c2f31462687f2a507ccf1743795b800156b4b4f07f08892626092d1200380001e0100100b00000c0280f0020000180000000005801012020008000040040000000005c0100700000801005002004018020000040000700200000004000068008000000000000e00a0500100c0000040200a0000100000700e00000001008000008030000000100c00000c018000040040001402600c0080900a01c0b00f00200c0180600000004001008000008090040000380100000c00801004020018000280000d00400800c010090020000000700203c08010024028008040000180a80500000c0200a0020440000100c0000300100a0140080001600c050060020000101100000400803002000050000000180080000e00c000090000200000500000800001002000018010020080400300800004000000000020040020180180000003c04802002000038000040000382202a01001000004000008010240000000700000c0080600800402803002000060020
  | 4 => 0xe20018eb37310911478000009280780000000c000890009451d11d3b60016524d0005fcbda6c18e839681331862a0000003980010c97553200072b24000b0800000188c595a34e09c3ac2508c0681cc00000498d900000000035c0035b000001851a70009894303629e0000024f00000025800000001078000000007700068a7f4000003d60010425352468c00370000000000000ea1f58c800000001958001100000035c0000013e80c000bd43c8000000017f000000cb4df0c0080000090502486c180b3a6d00e41ba56000000002ff404000828004626f40026b000000a1800550000000002721a84102638a000001c005266847a7240ac3c002033c4001a5000000a5d76a55504951030854d0c9cc7a9a4ae904000003d44a0000000001ac0036e0005dcb70f65a4978bc2462bc81033aa90003d4001a20002e80000940e00000322000000be2493329b80a0483f4db096377000a815c800000408c1000000000939f8458b38908e300030963800000000000e8300bec002b7000195b9b4c64067974b130005742fac42b465c4f2cc3baac109800600280001e60000015d0000000e8000d50000014700064cad4001c75e08e40e0000002500000065800130a2543cc080000017cb90168313e6bf0300a1000c7c003480000000029f0080009d880000000dd8001be000000001d20000000000000000800000869b109669e2a43a22b356a44918006c6348002f80829e4e710f0046fc761145548cc00000686000000f7000695718005f4bdc71264000001b380061c00000000000000000002b2000000001f4cb83b0f14e0000000000000011907c00040434b07000d5c000002c2108b580016eca856a174c60012e0d839e7b8f6800000cc000000000000730006d2d510a0c1000000001a80004bc4915c2a40000033230a0002c000170a0c000002b0af1b31c84162e51b89719c170ee08347e6dccc0b21bc3fc003584ecc788300000000157800000855599710000015c000520219880000000012011b54e0000016f48a001a02e61b29f03f2274902ccef2da162d55758b44425cc002750000f400000234000b1800000001b50dc00072800306364a8c002d104e0000018e000a754b00009235000378218dd82d80000084949800000b3dba13d00000053800214460001b5000000000000008bd6f0005a6000000001e0480000000786d00017a4f45f4b800005e000000002be655a300000075c9fb6d09e2f14c19d3421a0269e53d2000000000000006d3350004b45a96900022935000000000e980000a000ec0002828d564066306018000000602fc000003a4000001930000000018d1f6000000000de000468000006f16da5834c4f11330c29cc2c0733e18a0012800064a18c68a096880002b00001a5296c800048a70001d63020000007846
  | 5 => 0x5420ea518db6b28a710f0ab2088c50b22ef26a421421e3200765b099b1f84d8522fd49cafc2ead405c4c4e30611a0880d500000000000000476ab000000144af53f267
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xe41c431e5350710c754d41c43365450710d554d41c42b76550710cdd9541c43375350710e594d41c43355350710e554d41c43155350710cd94941c43345250710c795331c431d54cc710e550731c42b5648c710cd55231c431e544c710c755131c4397414c710e550531c4335544c710d594d31c42d7654c710d5d9531c4357544c710e595131c4355544c710e555131c4315544c710d594931c4354524c710ad59221c42d5638871097d8d548425c63552109798c548425d63152109b988548426d62152108fd91538423c6454e108f990538423d6414e109b988538426d6214e108fd91528423c6454a1097d8d528425c6354a108f990528423d6414a109798c528425d6314a10e550531842f16008610bc18520843e3214821097d8d544425c63551109bd89544426c62551109798c544425d63151108fd91534423c6454d109bd89534426c6254d108f990534423d6414d108fd91524423c645491097d8d524425c63549109dd85524423e64149108f590524425e63149109758c52442b56490510b558e41442746550510cdd9541443346550510cdd4d41443355350510cd94941443345250510ecd8141443b06050510e550731442b5648c510b558e3144397414c510e55053144274654c510d5d953144354654c510d5d513144355544c510d59493144354524c510f4d8131443d0604c5109d99621442b56488510b558e21442746548510ec50620443d131881109e19520443b14148110f44c520443e12148110ec50710443d131c41109798f540425d63d50109b98b540426d62d50108f596540423f61550108f585540423e64150109798c540425d63150109b988540426d62150109d984540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c1097d85530425d6154c108f990530423d6414c109798c530426e6214c109b58853042766114c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520436461548108f990520423d64148109798c520425d63148109b988520427661148109e980520423e64944108f592510425e63944109758e510423d65d0410c794f410431d53d0410cb94b410432d52d04108fd95410431e5350410c754d410432e5250410cb5494104336515041097597310431e54cc410c7553310434e52cc410d354b310425f654c410c7951310431d544c410d3949310434d524c410d59453104395414c4109d597210433554c8410d554f210436552c84109d59421043355408410d554c21043655208410bc580210433554c4010d554f100436552c40109e596100436952840109dd9510043355444010d554d100436552440109ed9510043695244010
  | 1 => 0x825c63552209798c548825d63152209d984548827561152208fd91538823c6454e208f990538823d6414e209d98453882756114e208f992518823d64946209798e518825d6394620cd94541883355150620d59453188355514c620e5505318823d61d51208f992544825e63951209758e544827661951209d586544825f63551209718d544827761551209d185544823e6515120cb588544823d6115120c7d53534831c54d4d2097587534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209dd8553482746154d2097994534831f5414d20c7150534834d6214d2097584534832c5490920b358e424826c6550920ab592324834c538c9209b195324833754d4520cd153514835753d4520d514f514833764d4520cd193514835763d4520d518f514823e64145208f590514825e63145209758c51483375414520cd15051483575314520d514c51483366414520cd59051483566314520d558c514837160145208f997414823c65d0520c7d4f414831c53d0520cdd47414833451d05208f995414823c6550520c7d4d414831c5350520cdd454148334515052097997314825c65cc520c7d53314831c54cc520d5d47314835451cc52097995314825c654c520c7d51314831c544c520d5d453148354514c520e5505314836451c8520e950721483c531c85209798f540825d63d50209d987540827561d50208f596540823d61950208fd85540823e64150209798c540825d63150209b988540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c2097586530831e5454c20c7551530825f6154c208f990530823d6414c209798c530826e6214c209d98453082756114c208f992510823d64944209798e510825d6394420cd95251083355494420d594e51083555394420cd99251083356494420d598e51083556394420cd95151083355454420d594d51083555354420cd99151083356454420d598d510835563544208fd97410823d65d0420c794f410831d53d0420cd947410833551d04208fd95410823d6550420c794d410831d5350420cd9454108335515042097d97310825d65cc420c7953310831d54cc420d5947310835551cc42097d95310825d654c420c7951310831d544c420d59453108355514c420e5505310832d54c8020d354f200836551c8020dc546200826f6548020cb551200834d5348020d9545200827b6548020dc545200825e63d53109758f54c433661953109798c54c425d63153108f99353c423d64d4f10c795253c431d5494f10d598653c431e5454f10c755153c423e6414f108f59053c423e64d4b108f59352c425e63d4b109758f52c423e6414b108f59052c425e6314b109758c52c431e53d0710c754f41c42d56390710d554
  | 2 => 0x5294440d954a51103566394440d558e51103565354440d554d51103665254440d954951103366454440d598d51103556354440cd90d51103344354440cd90951103344254440c794f411031d53d0440cb94b411032d52d0440cd547411031e5350440c754d411032e5250440cb5494110336515044097d97311025d65cc440d394b311034d52cc440d5947311035551cc44097d95311025d654c440d3949311034d524c440d59453110355514c440e5505311031d53d0040cb54b401033551d00408fd95401029c6350040c754d401032d5250040cd545401027b65500409d98454cc2756115330c715143cc23e6494b308f59252cc29d64ccb30b558732cc23e64947308f59251cc3365150730cd54541cc35551cc730e550531cc26e62152309b588548c27661152309d584548c31f5410e30b5584438c23f6454a308f191528c2776154a309d185528c29e648ca308f992518c23d6494630cd945418c3355150630d5945318c355514c630e5505318c23d61d51308f992544c25f63551309d984544c27561151308f994544c2b56115130c758c544c33661151308f584544c33561151308d584544c25e6590d30c7152434c25c6550d30c7151434c25e65cc930a7593324c31c54cc930b5587324c31c544c9308f990514c23d64145308f997414c23c65d05308f995414c23c6550530c7d53314c31c54cc530c7d51314c31c544c530d5d45314c395414c530c7152304c26e62d50309b58b540c27661d50309d587540c23d65950308f586540c31c63550308fd85540c23e64150309798c540c26e62150309b588540c27661150309d584540c25d65d0c30c7553430c25d6510c30c7550430c2d56110c30cb952520c32d5494830cb951520c32d5454830d3d0d520c34c435483097596320c29e648c830c7552320c34d528c830c7550320c34d520c8308f992510c23d6494430cd952510c3355494430d994a510c3655294430cd992510c3356494430cd951510c3355454430d9949510c3655254430cd991510c3356454430d598d510c3574354430d510d510c3563254430d50c9510c23f65d04308f597410c32e52d0430cb54b410c33651d0430cd547410c23f65504308f595410c32e5250430cb549410c3365150430cd545410c31e54cc430c7553310c34e52cc430d354b310c35551cc430c7951310c31d544c430d3949310c34d524c430d5945310c395414c430c7553300c34d52cc030d5547300c25f654c030a7191300c31d544c030d3549300c355514c0309ed95300c25e63d53209758f54c825e63953209758e54c827661953209d58654c823e64d4f208f59353c823e6494f208f59253c82766194f209d58653c82cd6390b20ab59232c823e64947208f59251c825e63947209758e51c8395414c720e950721c83c531c872097d8d548
  | 3 => 0xe21c794f418871d53d0621c794d418871d5350621c7953318871d54cc621c7951318871d544c621e5505318873554c8621d554f218865e63d51219758f544865e63951219758e544867561951218f993534863d64d4d218f992534863d6494d219d5865348795414c5218f990504863d64141219798c504865d63141219798f540865d63d50219e983540867960d50218f596540873661950218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21d5986530871e5454c21c7551530863e6414c218f590530865e6314c219e98053086796014c218f992510863d64944219798e510865d63944218f597410871e53d0421c754f41086756590421ad59241086d56390421d554e41086e562904218fd95410871e5350421c754d41087365450421d554d41086b76550421cdd9541087375350421e594d41087355350421e554d41087155350421cd949410865d65cc421c7953310871d54cc421e55073108675658c421ad5923108735548c421b558e31086e5628c42197d95310871e544c421c75513108797414c421e55053108735544c421d594d31086d7654c421d5d953108757544c421e59513108755544c421e55513108715544c421d594931087a541c8421f14c721086b56488421b558e210866f6548421e9d0521087c731484219dd95210873a5494021ce552500875a5394021d654e50087b14194021f44c6500873b4194021ce506500875b3194021d64c650087354154021d54c5500873a5454021ce551500875a5354021d654d50087b14154021f44c5500873b4154021dc90550087394154021dc50550087314154021d6cc550087723154021d64c550087713154021d44c5500876b2154021dc88550087692154021dc485500865e6394b409758e52d029d63d0b40ad58742d025e63947409758e51d033551d0740d594531d0355514c740e550531d02b56110e4097d8d529025c6354a409dd8552902746154a40a798e429025e63946409758e51903365150640cd5454190356514c640d55453190395414c6409758753502766114d409d58453502d56114d40d5984535025d6114d40d558453502556114d408f997435031c53d0d40c714d435023e65d0940a758f425031c53d0940ad587425031c53509409798c515025d6314540c7d4f415031c53d0540c7d4d415031c5350540cdd45415025e65cc54097197315025e654c540971953150395414c540c714e405025d6194c4097d85531023d6590c40c754e431031d5310c40ad584431034e5394840d354e521034e5354840d354d521032e4354840cb10d521023d6590840a798e421031d5390840cb54a421031d5310840cb548421025e63944409758e51103565394440d554e5110366
  | 4 => 0x558754cc71d5415331b558454cc69e64d4b31a759352cc6d561d4b31a799252cc69d6494b31d354852cc6d56114b319799742cc65d65d0b31b598742cc6d561d0b319799642cc65d6590b31e5d8541cc69f6454331a719150cc69e6414331a759050cc6ce6214331b358850cc7366195231cd951418c6b76550631cdd95418c7365250631c7953318c71d54cc631cd505508c66e62951319b58a544c65e65d0d31b5987434c65c6550d31c7151434c71d5410d31b5984434c63e64d49318f593524c69e64cc931a7593324c6d661cc931a7992324c69d648c931d3149324c6d4614c931ad592414c6d663905319d195414c7974350531e590d414c7954350531e510d414c7376550531cd195414c7976350531e518d414c7345250531e5cc9414c7963250531e54c9414c7943250531a7992314c69d648c531e5506314c73541d41318f990504c63d64141319b988504c66d6214131b398a544c6cd6295131b5586544c6d76155131c7550544c69e64d4931a7593524c69e6494931a7592524c6d56194931b5d85524c74d521493197997424c65d65d0931b5987424c6d561d093197996424c65d6590931b5d85424c6d46150931b5984424c6d56110931b5593514c6d662d4531b5583514c79751d053197996414c69d6490531b5996414c7566590531b5592414c6956490531b598a414c6d56090531e5d85414c7975150531b5995414c6d46550531e5d91414c7975450531e5151414c6d46250531e5d09414c7964250531e5509414c7944250531b5d81414c7976550531e5995414c7956550531e5195414c7976250531e5989414c7956250531e5189414c7975250531e5949414c7955250531e5149414c7976050531e5981414c7956050531e5181414c65e6510531a7990414c6d66110531e5504414c79541d4131e5506504c69f6454131a7191504c6cf6254131b3189504c7954154131a7990504c69d6414131b3988504c6cd6214131e5504504c65e63d50318f596540c63e64150319798c540c67661150318f992510c63d64944318f597410c71e53d04318fd95410c71e5350431cd945410c71e54cc431c7553310c735548c43197d95310c71e544c431c7551310c795414c4319dd95310c735544c431d594d310c65e63d53219758f54c865e63953219758e54c863e64d4f218f59353c863e6494f218f59253c86d56390721cdd9541c87346550721cdd4d41c87355350721e9d8941c87a46250721e550731c86b5648c721e5d0531c8795414c721d5d9531c8754654c721d5d5131c8755544c721f1d8931c87c4624c7218fd9150c863c645432197d8d50c865c6354321cd50550c875531543219798f548865d63d52219798c548865d63152218f993538863d64d4e21c7952538871d5494e21c7951538871d5454e218f990538863d6414
  | 5 => 0x5390b566194e42975865390b556194e42955865390a5f6154e42c794f4390b1e5350e42a758f4290b1e53d0a42ad5874290a5e63946429758e5190a3e6510d42ad5844350a9e63909429798c5150a5d63145429798c5050a5d63141429d9845050a7561141428fd954310a9d63d0842ad5874210a3f65508429bd954210a5e63944429758e5110a5f63540429718d5010a7661d53329d58754cca3d6195332c718d54cca3f61553329d98454cca756115332c755343ccb1d5410f32b558443cca3e64947328f59251ccb365494732cd55251ccb366494732cd59251ccb365454732cd55151ccb366454732cd59151ccb566354732d5d0d51ccb5443547329d986548ca756195232ad586548cb1d6395232cd986548ca3d6195232cd586548ca3561952328fd85548cb1e5490e32c7951438ca9d64cca32c7953328cad561cca328f992518ca3d64946329758e544ca7661951329d586544ca5e65d0d3297994434cb1d5410d32b5584434ca9e648c9328f990514ca3d64145328f990504ca3d64141329d984504ca7561141329798f540ca7661150329d584540ca7a60150329e580540ca3e6494c328f592530ca5d6590c3297d95430cb1c5450c328f992520ca3d6494832a7593320cad561cc83297d95320ca6f654c8328f992510ca3d64944328fd91500ca3c6454032c754c43d065e6394b419758e52d069e63d0b41a758f42d069e6390b41a758e42d072d5210b4197d8d50d065c6354341ab98b53d06ad62d4f41ad58753d071d5314f41ad58453d069e63d4b41a758f52d06b561d4b41a798e52d069d6394b41cb54852d06b56114b418f99732d063d65ccb41ad98732d06b561ccb418f99632d063d658cb41a7d8d50d069c6354341a798c50d069d6314341ab98850d06ad6214341d5986539071e53d0641c754f41906b66190d41c714d43506b66110d419798f525065d63d4941a798f425069d63d0941ad987425069e6390941a758e425072c5250941ad185425069e6390541a758e415065e63141419758c505066e62141419b58850506ae6294d41ab58a53506b56194d41add85535071d5314d41a798f525069d63d4941a798e525069d6394941ad58652506b76154941cb548525063e65cc9418f59732506b661cc941ad587325063e658c9418f59632506b7614c941ad18532506b6610c941ad58432506b563d4541ad98b51506b560d4541a7d8d505069c6354141abd8950506ac6254141a798c505069d6314141ab98850506ad6214141c794f411071d53d0441d554e411063f6550441c794d411071d53504419dd9541107365450441d554d411066e62d53319b58b54cc71c5450f31c755043cc63e6494b318f59252cc69e64ccb31a759332cc69e648cb31a759232cc74d520cb318fd9150cc63c6454331b398b54cc6cd62d5331b
  | 6 => 0x68002211088f898514492597d2249ca91b8000000de8191011dc8cd06508412a8798760a22371f823a9b021219e1529f30d027627a8c700009e00000025e21500000000000000020780004780010b00000005ca148002209669e68000001431faa880000001dd8c79e29818000001f990ea4b2938c60169f72491ab0609a902100021f9021c383712702e8dd00000026d00000028d15c00000000000019b21d82d81fa5f03d93494280008297c1d4a879491508b709ca271bea9c8a909300080000e0000000100c0400180d006004040020100080280000401006802006008058050020340180100600000005000008020020060000380b0020040200001a00000025000000020000140180080001600000000026004010010120340580200a000000040000080000204e00000002002000058000000280000100209c010000000440000100c0000200600200400000000014000020020040300000c00800807006008010060000040300700e0140000200000c018030080000080100201003003000000000000000080000600402801005006004000050020040181c0040080480001800801001000000010170040380800101201801800000000008040000140980700e0000000000c008018000080040f00d02e00401800002000028000000180900903604401011000000008000000040c00000400800001004014058030020000a002004000000030000000780100c01c0000300604c0080900000c0280702002c010000040000100300605400002012014008080120000080000e018020190000080000c004000010000000080380f00e00003806000014000000000380a00300c01401800008024008070000140180d0060080080001a00802007002004000000000440080200409c0b0080120000100f000020030020000000180000205801000004000010080000001680000e0180281200c00001805014004030050000000700000600800800000018008010000080000000000c018000900180200a0000080000600200000803004020020000000380000600400004800000000000000060240581200000001000012034020020000ec0000104a00401803000000020019d9875250e7561d49439b9885050e6d62141439d9845050e756114143a75924310e3f6550c4397d954310e9f6550c43c7d954310e9f6250c43a7d854310e9c6050c43c750e5210f954394443c750d5110f954354443cd9915110f566354443cdd0d5110f564354443cd50d5110f554354443c550d5110f1d43540439758653d0a5f6154f42c754e43d0b1d5310f42ad58443d0a5e63947429758e51d0b565394742d554e51d0b566394742d558e51d0b565354742d554d51d0b366454742d598d51d0b556354742cd90d51d0b3443547429d9865390a756194e42b5586
  | 7 => 0x1048420000000000001c2121a038a297303488007280000000000022605300000000012980000000014e88e29a8000578be1658000cc0f70000000bf80006285c1cd06a94d0bc2848000000000519171651bb1cca3b1c41a6807231a1f0a30052680388672400b81269908c999d1c98821e71fe8060ec1e50040100001940939308000000000000000001f500016411800018308813c00000000014680000000000028c0000320001a806800000f96c25182f1b200022d11092f16a8000001968ce13d2138001cc1ff00008b26f07c0000000000440001828770471840000000aa80014714f00000023695d28e86d2258000000000f318100024680000022280000017800000018a8f000022384e00000013680004c8000002538001628002660000000000000001520ed92a1eb20b8230000002050af08621619105f919a1c98d0208e78fda8507f12100497784380680027915a8e980020606ea8380006486f80a0000000000991040000021a7a280000cc8000001d800004311d0f2178a1b87b00102a88da420001ed99b8000810f9a570001cf0000002829560df00020a0001df80009400029602d09da96a52901a6f8c0a698b3865800a1e15180023fa0685e0000d79110b920f234a43927a6e256000000105a6c1e3a7692c0b22381971d29ad8278a12268a4924a470df88080000009f09614da6b8bd0000000258f580000002f8000000000000000000000e60000002240000001afa5222e8000001931698002131538a3a2525903a83fa430d61f78398871a4a8181893e9f48000c01b186211504d13f1dea3587106e029a2b9648788a19591b4a6da7f1459ed0cb8019e18cf0de2798b987e0e1a7a1892048d285b0610c918201e07a24808316d0ea0028d482188914508c9cb846a5b17a0e49660000c28850c49fc90519815f80000002e00005410a00017221e93d84f80026200012f8c226a0741118001ec167948800000000000277a5fa118001cf8001b717f1400250000eb94601480000015b19794c241a110959718b686a06b17ba5ca1880000023017f800263a6e9301ce80004c0000000ed27c12800007a8e38000001929ce1120078000000001880000c393f9758001340ef80000000022000000000000000009519224f00011e0000000d68ac00002000005383a232017a5800009029480020d00027180000021d0001d50000000001f298f00000014080000010b8d406600000000000000027484d986a0c83c0000b7909a7e205a75a678929ac27b18088a9af0639d58000c81a7015032a3925e8000001aa18b0ce80018ba0728f0000e916700011c29800002a0f680012e80004880010f9e613989109aa6580000000004580022c9de04b9e200000017720c21a80011400026500025d8400c19bc0db9190838ffa4280004a13109
  | 8 => 0x7ba7224a26b19381d1d79d60000aca7d9380001ee066a95000000118a931621e78e28000001a0227a7423519c8288001c08640000001081179ef1f40a6a172629eb8ae80010000e92520904e97b12b0001fb80900028a96085a9ca156937a8ba9c00d9a380817e88c1888000000d58b520880029585f0000000000a599e80001ea4c9e4a5525c1440748f4051022a3d89ea928319d21858cd8001d38001388110630000000d1a2f96c907a2a17d90d27385511ca1a1500f19e00ad8cb14b1ac9f58000001d10000000000e50001fb1c60c589a00008d19f9639b800009b8001038001ff8688000000bd9ad0000000001a20268000000000001558fd1241d007b8000000d827801323b94a19aa450918618fe285a100818002630ad0720001a41a08001b501600c186000297a6919982203006028700000b1e90bb26104503680882b9071919b09578000a0a3c16f2028001da89c25a08580003600023d00000003f0002291992860d08000c400021901d8ab1901958f800006c1b681b0000001c795700016b8000b316b00000010c8000570001ab8002600ee1289c5a7ea2f000000000050a618b603d00593b8001749a88000000000000878b111d84816a1481b10001988000002820002198000000f79260000001200000000000490000002708140d700322a80011324d8000001768588000001b89c107ea289e325d0001bf9a29ea8002441d30d120002909080026480018f80016e8be8000fa29705d99d8000001f68e018c80000029117296d80000001706ca8127d05a1dd13628e1231db8ab80021b1cda8922b0341b39220ee8000fe809a4780017a8581b9a221fd9d9a0e00000000011b0001e88350001bb80010624b9bd0001e41bda7c8001209ea1f10428000000aa0ea8d90ca8f48000001d89332578001128001ee80000d07693c80008e80000023280000018480000000000a8000000002908000000000001588ef0f514f8679790d88000001be0f2800183a44a008448f38039c809f80000000029b1e826a8e223300000001ca378000000109fc19f04f29d18ea80256a588700da86b9b588b94ba12a730000000000238fb19c00000000000000023080000001a1d409b06980000015300000007c8f095a0fc80000010280000023e26680018a1d198d80000000000000016e0000001960b18001f90001a180015b80003b1c19168000000358000000e800011600017980000006916308980026c8001db00017080003e25989882c00003e8001bc8000000d311f154a940b891ea91a1c13900007d07908a0000000000e0987a9d88485980024d29b90912e00013e03c97e0000558000000000000260000b08000000521f608f2808d38000001a52109872728119ae81b9e580009800000000000000000000000026704085b951289800000
  | 9 => 0x16f91492c9a10000271fa1760001df0002459359c005e9b783380f28301c01216899a16810f1f00528000000001438000000e100001a8000751b300014ca3401289d194a0e80000010c0778000da0dc0920000002608001f081f15e02480000000013503794a8c88ec8db00015811f95d9f18f91421ba00018e0000000000000001ef90a90087300000000006da4a9069228c300000010d85484601800e000241000000149a8c833240a0b27f849a900000bf24c28d9158cfa8fa182998af97113a82800003ba03284131a48a5b8000000000000dda040240000000000000000a60fb80000000000024e0000000d980c9a58002549e98001328002020001a99b927013a1fd0001cb0d51f38411601b600020f8000e58002010c11238b487da6415c815a498001aa80000000023f0002511690b400002b07f800132070a86a750000418000138b000013b13398017c8999b42019fe00004b2080002460590001c49b29d0a338001e10502168309c29550dc8781c898c1290311da0ca1c90a800000008680b9f22098000000fc2990002888ff0001ae0000001baa178000eb0000000000c68000000e6a4f8000000000000001bf24e97400014118994e11a0b58001a302c97004a80022180016121580000028a2360000000000001ec8000000000ba9d69c31f8897a920000a710312d0d200025011aa50a55a540ba2771a60889418001950a9a140a78000bba9a00000000022980000009700006f00022c00015f0000ae00000025a8001e09d700015e800000073a2e00028b0f11541c692da3c83808f8a88000c50000e3075800268856a712389618390000001750a50000a01c70fa8000562530000000b29dc1478001138719c500000020d90e0002310e88e722d93723a00020aa78800159a231101738f60198bc8000a40e41d905d23e894a3980029892b8002
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x98d1675d89414c68b3acc4a0a63455d66250531d0ac43128298c9676d49414c64b3b4a4a0a63255da5250531e0aa42928298d8772581414c6c2392c0a0a63459d46050531b0ce43028298d8572181414c743b1282a8263a1189415413192eeca08a098e8662504504c742b128228263455cf6550721a2ae9b2a6390e176350550c870bb2262a8643155c663d512186ae3326a690d3170d4d410868abaca6a08438559541cc421a2aeba0a6210d5170d51310868abaca898843c454d4194021e22a898ca010f11414c65008699baa82a8043c494d4154021e22a6a0aa010d53754c550087892a262a8043c45513154021aa2e720aa010d61729055008788a0e62a80434c5d23154021ac2e518aa010f13414c55008788a0a62a8043c85072154021e826390aa010d317488550086a8b9c42a8043c8d052154021e866290aa010c557198e52d024ab8cc721481455ce5150640c2ce8b08a6a061574584535028ab88a7a1a81455c45350d40a2ae229e84a061453587425028ab88a6a1281455c453d0540a2ae229a82a061665505315028ab88a7202818554d6110c40a4ae221aa4204957198e421030731aa521081459ce4254440a2ae329a822051573945411030bb2a8298881c1949414c440e0aa4a0a62204957118d401030631aa4a00818518d5150040a2ae22a287984357199252cc30baa2c221c61255c6648ca30a2ae928a631861563584544c30b39ac22a261855cd6115130a2ae22a4869851571151434c20ebb0a999261455c454cc930c28a8b0e649851571151324c28ab88a998a61455c4544c530a2ceaa0a629851571152304c28ab88c6aa061855516110c30a8ae221aa41849571992320c20fbb2a91906183991528c830a2ce9192a21851571951310c28aba4a29886145dd5414c430e0ca4a0a621870552505310c24ab88c898061071d9544c030c18c8a92601861464545300c22ab8cc7aa6410d5c664d4f208aae231aa91043571191538828ab9ca2a0c41455d2514c620c2ec9b1ea2906156458c5148318b22c028a419458d6014520a2ae229a829051573145414828ab88a898a41455d0514c520a2ceaa0a629051475505314830b32a8298a4185195414c520a48eaa0e4290544754c7214830ab22c728841855916354420a2ae329a821051573945410828ab8ca898841455d2514c420a2eeaa0a621051575505310830bb2a829884185595414c420a2ae629283885157414931c428ab98caa0a210d1d95350510a48e4a9a82885157314941442d0b90c0a0a21455d0654c5108a8ecaa2628854472551314428aba0a498a21705c8604c510c60caa0a4088650654c5204428ab9ca2a0821455c5544c410a2ae928a620851775505310430bb2a8298821c1949414c410e0aa4a0a6208631545802104328a9ac010821985496008410
  | 1 => 0x561f9ec5000040581600380011c646798134bc290b400001388928504080000004d80000005c30d622416034be68350017eae00000689900001726e5d000320000038f861002b10625060ecb89f08950d8ca100018800032c0fe802c000c45a000007c1346028082950b44d2671bb69a8312492c74ad000015ee0659e14a2f00270420066000000500220009e1ab39265911a2d767603a44844f252ac0087000006c550000000a93d2583617229211a4629b25ae0331b74fa0166800de3318225445d490600074288003c154e8e1840000208780047b1c00002f00000775b000eaa80d22872be00000ca7221801b0a45aa9c0079518009cb20007c28aa42930005b389997ac54aad04cc86b00000b300000002b6f8a83a1c00211a0c06c8485c00000407a0036b188000718012e006a9109a86359f9a4413983c12570111d82e2500c9c2db483716ed300378009800298000001408010f0181c02058280207010000002008000203008380006030080800018001a0f0300034050003c0401078000c040100c04070301804190502012040080010010800004020000800070100c120505008020192ae3b128621c8d721814310e4ab88c0a188743dc94394843a2ee2a1aa221d177550d5110e92b94c8a8887515ca6354443a2eeca1aa221d177250d5110e8a38286a88878554d6110f42c2ce8b0ca721615745865390a8ab8ca7a1c85455c65350e42a2ae329e8521616535874290a4ab8cc721285155c46354042a2ae231aa9996155458443ccb0ab1ac32a465859cd6195232c2ae6b0ca91951571952438ca8ab8ca8a1c65075da54cca32a2ae32a6651961654587328cb0aaa2c221a65255c6648c932a2ae22a2861951970151430ca1ab88c8a80658554d6114f4192ae331ca5a0c9573987425064ab98c2a1283255c663d494192ae7316a2a0c9773583515070aaa2c22a663255c66494b3192ae930e6498c9574185324c70a32a86a0a63499cb655053192ced9928298f04524c9414c64ab8cc9a9263255d262d453192ee8b06a298cc672995414c68b3ae84a0a63a11894250531b0ce5b2a8298d8572d95414c6c3394caa0a63615ca6550531c2aca32a82
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x190d18089500a001c0c584411cc090582dd94354443905821c14354443a05829d16194e42a05829cd61952328158795161cca32a05829d16114d40a058198d5290840a058118d5250040a05829cd61151308158715161cc930a0581991528c830815869d23254430a0581191524c03081587191514c030
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 890
  | 4 => 1340
  | 3 => 228
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
  | 6 => packedAt s5K6 (788+((h/14+packedAt s5K6 (704+(h % 14)*6) 6) % 53)*7) 7
  | 5 => packedAt s5K5 (27286+((h/296+packedAt s5K5 (24030+(h % 296)*11) 11) % 1292)*11) 11
  | 4 => packedAt s5K4 (55826+((h/446+packedAt s5K4 (50920+(h % 446)*11) 11) % 1945)*12) 12
  | 3 => packedAt s5K3 (11856+((h/76+packedAt s5K3 (11172+(h % 76)*9) 9) % 301)*9) 9
  | 2 => packedAt s5K2 (860+((h/4+packedAt s5K2 (840+(h % 4)*5) 5) % 18)*5) 5
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfe1ffff0ffff87f8387fc3ffe1fff83f0cf3cf
  | 1 => 0x3fe1e1ff0f0ff8ffc070fc787e3c3fc78b4d33
  | 2 => 0x3ffe01fff00fff0fff80ff807fc03ff8f38e3c
  | 3 => 0xc00001fffff0000fffff00007fffc000fc0fc0
  | 4 => 0xfffffe000000000fffffffff80000000fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x2000010000008000001008800440800001045
  | 1 => 0xa4485322249541894438645132289286894512
  | 2 => 0x8848444422a00129880890244812530328a28
  | 3 => 0xa1d55988aa8352aced5a204479338192dc0f80
  | 4 => 0x3119910ecccc64cf366cf26710220624efe000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfaeaeae8faeaeae8faeaeae8faeaeae8faeaeae8faeaeae8faeaeae8faeaeae8faeaeae8faeaeae8faeaeae8faeaeae8faeaeae8faeaeae8faeaeae8faeaeae8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37209
namespace PEqualNP.Outside.L_meta_37209
open PEqualNP.Outside.L_meta_37209.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x86823976000f000cbc2600104024ac21f003921159004af40040214eb440032a02805bb030b5d2801d005170731a400c6194e22d48cb2fad88988bc26cdb345c55500340004c0c0478200081001228787121c0010010605060007ff53017f94c07fd53017f14c05fe43007f50c05fc4301ffd48077f5201ff94807fd52005f54807fc52017fcc801fe32007f4c805fc3201ffd4407fe51005f94407fd5101ff144077c51017fcc401fe31007f4c405fc31007fc8401fe21007f48401fc2101ffd40077f5000ff94007fd50005f54003fc50017fcc003fe30007f4c003fc30007fc8003fe20007f48003fc20007fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x92400affcc92003ffc6490003ee3248001fe9924000fb4c92003ff86490003ff61480017fb0a4000ff98520007fac290003fc61480097e30a400bffd452005ffca2900037e5148017fea8a400bff1452005ef8a29002bff3148001ff18a4000ff4c520057f8629001fff2148001f790a4000ff88520007fa4290003ed214800ffe10a4001bfd812000ffea0900077f5048003ff2824001ff5412000efaa090007fc5048003ff9824001ff8c12000ffa6090007fc3048003ff9024007fec812000ffc4090007ee2048003fe1024001fb0812000ff04090007fe1048003fd0824001ff04120027fecb88012ff65c4009bfb2e20049fd9710027fccb8800efe65c4009feb2e2009bf59710027f8cb88012fc65c4009be32e20049f19710027fec788012ff63c4009ff31e2002bf98f10027fac788002fd63c4009fe31e2004bf18f1004ffea788023fe53c4013fea9e2008ff14f10047fc8788003fd43c4011fe21e2004ffd8b10025fec588013fe62c400f7f3162004ff58b10005fac588013fc62c40097e3162009ffd4b1004efea588027fe52c4013fea962000df54b1004ff8a588023ff32c4001ff1962000ff4cb10047f86588006fe61c4009ffa8e2004ff94710026fca388013fd51c4009fe28e2004df14710027fe6388013fe31c4009fb18e2004ff4c710007ea6388013fc31c4009ff90e2004ff88710027ec4388013fd21c4001fa90e2004ff0871000dfac188007ff50c4003bfa862001ff9431000ffaa1880077d50c4003fe2862001ffcc31000ffc6188007fd30c4003fe1862001ffc831000ffc4188007fd20c4003fe1062001ff8431000fec2188007fa10c4003fe0862001fd04310037feca8801aff6544001bfb2a20009fd9510037fcca8800efe654400dfeb2a2006bf59510037f8ca8800efc654400dbe32a20039f19510007fec688002ff634400bff31a2002bf98d10007fac688002fd634400bfe31a2002bf18d10037fea688017fe534400dfea9a2005ff14d1002ffc8688003fd434400bfe21a2000ffd8910005fec488003fe624400f7f3122000ff58910005fac488003fc624400f7e3122006ffd4910036fea48801bfe524400dfea922000df54910037f8a488017ff3244001ff1922000ff4c91002ff86488006ff614400dffa8a2004ff94510026fca28801bfd5144009fe28a2004df1451002ffe6288013fe3144001fb18a2000ff4c510007ea6288013fc3144001ff90a2004ff88510007ec4288003fd2144001fa90a2004ff0851000dfec088007ff5044003bfa822001ff9411000ffaa0880077d5044003fe2822001ffcc11000ffc6088007fd3044003fe1822001ffc811000ffc4088007fa2044003fe9022000fe4811000ff84088007ff1044009fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x77f3054003bf182a001df0c15000efc40a80077c2054003bf082a001df0415007ffeca9803eff654c01fff32a6003bf9953007ffaca9803efd654c01ffe32a6003bf19530007fec898002ff644c01dff3226010bf99130007fac898002fd644c01dfe3226010bf1913007ffea89803bfe544c01ffeaa2600eff1513000dfec69800bff534c005ff29a6002ff54d30017f8a69800bff434c005ff21a6002f790d30017fa8698003dd434c005fe21a6000ffd8930005fec498003fe624c001feb126000ff1893003df8c49803fff524c01fbfa92600fff9493007ffaa4980037d524c01ffe292600effd0930007fc8498003fd424c01dfe2126002ffcc930017be649800bfe324c005fe9926000f74c930017f86498003ff614c0017fb0a6000ff98530007fac298003fc614c0097e30a600fffd453007ffca2980037e514c01ffea8a600fff1453007ef8a29803bff414c001ff20a6000ff50530077f8829800bff314c005ef98a6002ff8c530017fa6298003dd314c005fe18a6000ffc8530007fc4298003fd214c001fe10a6001bfd813000ffea0980077f504c003ff2826001ff5413000efaa098007fc504c003ffa026001ff9013000ffa8098007fc404c003ff9826002fecc13000ffc6098007de304c003fe1826001f70c13000ff06098007fe204c003fe1026001ff8413000ff8209801fff65c800f7fb2e4007ff9972001dfccb9001f7e65c80073f32e4007ff5972006dfacb9001f7d65c80013eb2e4007ff1972003df8cb9001fff63c800f7fb1e4007ff98f20015fcc79001ffd63c80017eb1e4007ff18f2003df8c790037ff53c8019ff29e400dff54f20067f8a790033fe43c8001fea1e400cff10f2000dfcc59001fff52c800fbfa964007ff94b2003ffaa59001f7d52c800ffe2964007ffccb2003ffc659001fee32c800ffe9964000fb4cb2003ff8659001fff61c800fff30e4004bf9872003ffac390002fd61c800ffe30e400dffd472006ffca3900037e51c801bfea8e400dff1472006ef8a390033ff31c8001ff18e4000ff4c720067f8639001fff21c800ff790e4007ff8872003ffa4390003ed21c800ffe10e4001bf5832000ffea1900077f50c8003ff2864001ff5432000efaa190007fc50c8003ff9864001ff8c32000ffa6190007fc30c8003ff1064001fb8832000ff44190007fc20c8003f61064001ff8432000ff8219002fff65480177fb2a400bff9952001dfcca9002f7e65480073f32a400bff5952005dfaca900037d65480013eb2a400bff1952001df8ca90003ff63480017fb1a400aff98d20015fcc690003fd63480017eb1a400aff18d20015f8c69002fff5348015ff29a400bff54d20057f8a69002bfe4348001fea1a400aff10d2000dfec49002fff5248017bfa924007ff9492005ffaa4900037d524800ffe2
  | 2 => 0x2103ffc6510803fd328840ffe1944204bf98621027fea310813fe5188409bf28c4204ff54621027f8a3108137c5188409ff98c4204ff8c621027fa6310813fc3188409ff90c4204fbc862103fee4310813ff6088409ff3044201bf98221027fac110802fd6088409fe3044201bf182210d7fea11086b7f5088431ff284421aff542210c7f8a110867ff3088431ff1844218ff0c2210c7fc411081ffc2088409ff0844204ff042210bffeca9085eff6548401bfb2a42009fd95210bffcca9080efe654842ffeb2a4217bf595210bff8ca9080efc654842fbe32a42039f19521007fec690802ff634842dff31a4202bf98d21007fac690802fd634842dfe31a4202bf18d210bffea69085bfe534842ffea9a4216ff14d210b7fc8690803fd434842dfe21a4217ffd49210befea49081ffe524842ffea924200df5492103ff8a49085bff324840fff1924200ff4c92103ff8649085fff5148409ff28a4204df945210bffaa290813fc5148409be28a4216ffcc521027fc6290803fd3148409fe18a4207ffc852103fee4290813fe2148409f710a4200ffd8121005fec090857fe60484037f3024200ff581210aff8c090806fc604842fffa824217dfd41210affca09085ffd504842bfe2824216ffcc1210affc6090857fc304842bff1024207ff081210affc2090813fc1048409ffb284204bfd9421027fcca1080efe6508409bf32842039f99421027faca10852fd6508409beb2842009f59421027f8ca10812fc6508409ffb184204bfd8c21027fcc61080afe6308409ef3184202b798c21027fac610802fd6308409eeb184200b758c21027f8c610812fc6308429ffa984213ff94c210a7faa61084ffc5308427ff2184200ff50c2109ff8861081efe620840fffa904207dfd482103ffca41081ffd520840fbea904207ff1482103ffe641081ffe320840ffe9904207ff0c821025fcc210813ff5108409ff2884204df94421027faa210813fc5108409be2884204ffcc421027fc6210813fd3108409fe1884204ffc8421027de4210813fe2108409fb1084204ff48421027da421081ff52108409ffb004204ff9802100dfcc010813fa60084037d3004204ff58021005fac010813f960084017cb004204ff1802100df8c010853ff5008429bfa804212ff940210a7faa01084bfc5008427ff9804212ff8c021097f8601081ffe200840ffe1004204ff84021027f820108037f6354023bf31aa000df58d5008ef8c6a80477e4354001bea1aa011df10d50006fec4a80027f6254001bf312a000df58950006f8c4a80477f3254001bf192a000df4c95008ef864a80037f6154001bf30aa000df58550006f8c2a80127c6154023bf98aa000df8c550006fa62a80477c3154001bf90aa000df88550006fa42a80037c2154003bfb02a0019fd815001ef6c0a800
  | 3 => 0xf3046201bf98231027fac118802fd608c409fe3046201bf1823111ffea11888f7f508c443ff2846223ff5423110ff8a11888bff408c443ff2046221ff10231017fe611880bfe308c405fe1846221ff8823110ff84118813fe108c409fe0846220ffd9531105feca988037f654c4013fb2a6220ff9953101dfcca98883fd654c4417eb2a6220ff1953101df8ca988837c654c4073e32a6200ffd9131005fec89887ffe644c4217f3226200ff59131005fac89887ffc644c4217e3226220ffd51310fffca898883fd544c43ffe2a26204bfd8d31017fea698883df534c405ff29a6202ff54d31017f8a69880bdc534c405ffa1a6202ff90d31017bc869880bfd434c401eea1a6202ff10d31007fec498802ff624c401ff3126200ff58931007f8c49881efc624c441ffa926220dfd4931107fca498883fd524c401bea926220ff149310fffe8498803fe424c401fea12621fff10931017fe649880bdf324c405ff1926202ff4c931007ba649880bfc324c4057fb0a6220ffd4531027fca2988137e514c441fea8a6204ff14531026f8a29887fff414c409ff20a6200ff50531027f8829880bff314c405fb98a6204ff8c531027bc6298813fc314c409ee18a6202fd0c531007fec098802ff604c43dff3026201bf98131007fac09887bfc604c4037e3026220ffd4131106fea09887bfe504c441fea82621eff141310fffe809887bfe404c43dfe2026202ffcc131017be609880bfe304c405fe182621eff881310f7f8409887bfe104c409fe0826207ffd972103dfecb9081ffe65c84077f32e4207df9972101cfccb9081ffd65c843b7eb2e4207df59721004facb9081ffc65c840f7e32e4207ffd8f2103dfec79081ffe63c84057f31e4207ff58f21005fac79081ffc63c840f7e31e421dffd4f210e7fca790877fd53c8439fe29e421cff90f21007fa8790873fc43c840fffa964207dfd4b2103ffca59081ffd52c840fbea964207ff14b2103ffe659081ffe32c840ffe9964207ff0cb210effea390813fe51c8409bf28e421dff54721027f8a3908137c51c8439ff98e4204ff8c721007fa6390813fc31c840fffb064207ff9832100dfcc19081ffd60c84017eb064207ff1832100df8c190877ff50c843bbfa86421bff943210effaa19086ffc50c8439ff986421bff8c3210dff8619081ffe20c840ffe106421bff84321027f82190813ff65884097fb2c4204dfd9621024fecb10813fe65884077f32c4204ff596210d5facb10813fc65884097e32c4204df19621024f8cb10813ff63884097fb1c4204ff98e21015fcc710813fd63884017eb1c4204ff18e21025f8c71086bff5388433ff29c421aff54e210cff8a710867fe4388401fea1c4219ff10e210bdfac51086bff5288435bfa944207ff94a210d7faa5108037d528840ffe2944219ffcca
  | 4 => 0x2fd618c80ffe30c642bffd463215ffca3190affd518c857fe28c642bdf14632157fe83190abfc418c805ff98c6402ff0c63203ffec11901ffe608c8037f3046407ff58232005fac11901ffc608c8037e304642bffd423215efea1190a7fe508c857fea846429ff14232157fe81190a7fe408c853fe2046402ffcc232017fc611900bfc308c80fff1046407ff0823214ffc21190a7fc108c851ffb2a6428bfd9532147fcca9900efe654c851feb2a6428bf59532147f8ca9900efc654c801ffb226400bfd913213ffcc899042fe644c801feb226400bf5913213ff8c899042fc644c851ffaa26427ff95132147faa89909ffc544c80f7fb1a6402ffd4d32017fca69900bfd534c805fe29a6402ffd0d3213fbe869900bfe434c805fea1a6402ff10d32017b8869900aff624c851ffa926428dfd493203ffca4990a3fd524c801bea926407ff1493213ffe849901ffe424c801fea126407ff10932017fe649900bef324c80fff1926407f78c93203ff8649901fdc324c805f61926400ffd8532005fec299003fe614c801feb0a6400ff18532025f8c2990a3ff514c851ff28a6428ff54532147f8a2990a37c514c84fffa0a6427ff10532017fe629900bdf314c805fe18a6400ffd8132005fec09909bfe604c8037f3026400ff58132137f8c099006fc604c851ffa826428dfd4132137fca0990a3fd504c84dfe2826427ffd0132137fc809909bfc404c805ff9826402f7cc132017fc609900bfc304c84dff1026407ff08132137fc209909bfc104c809bfb1ca204df98e51026bcc7288137d6394409aeb1ca204df18e5112efc87288037d439444bbe21ca204dfd8a51026fcc5288137d62944013eb14a204df18a5112efe65288037e3294401be994a225df0ca51026fcc3288127e6194409bb30ca204dfcc651026f863288137f6094409bf304a204df58251004fac1288137c609444bbf984a224df8c251126f861288937e2094449be104a204df84251026f82128813ff658c4097fb2c6204ff9963101dfccb18813fd658c4477eb2c6204ff19631025f8cb18813ff648c4097fb246204ff99231085fcc918813fd648c4017eb246204ff19231025f8c91888fff548c445ff2a46223ff55231117f8a91880afd638c405ffa9c6202ff94e31017faa71880bfc538c405ffa1c6202ff90e31017fa871880bfc438c409ffb146204ff98a3103dfcc518813fd628c4017eb146204ff18a3111ffea51888f7f528c447ff2946223ff54a31006faa51888ffc528c445ffa146200ff90a31007fa851888bfc428c405ff9946202ff8ca31017fa651880bfc328c4097f30c6204ffd4631027fca3188137e518c409fea8c6204ff14631026f8a318813ff418c409ff20c6204ff10631027fe6318813df318c405fb98c6204ff0c631027e86318813ff608c409f
  | 5 => 0x3402800800001000400001001c00c00402800000002004802c01c00400001003003800400802403404000800002001800005c00000000400000802000800800800000400000000002c00c00c03000002803001c00800c00001800400801c00000401c00000000000003400000400400000400400000003c02400803c00c00400c00000c00000404400000000000008c04c00000401001000400401004000000800c00000800400400404400800002400800000400c00400c00800400001c00400400000000001400001800400401800c00c00400000000000800400000402c00000400800402801800002c00002000000802000c01000000c0000b800c05400002001400c03000c00c01801800c00804000801803004800000c0100000100045fffb2a862fbfd9543006fecaa18027f6550c5fff32a8603bf9954317ffacaa18befd6550c5ffe32a8603bf1954317ef8caa180e7c6550c057fb1a8602ffd4d43017fca6a180bfd5350c05fe29a8602ff90d430177c86a180bfc4350c05ee21a8602e710d43007fec4a1802ff6250c01ff3128600ff58943007f8c4a181efc6250c5fffa92862fdfd494317ffca4a18bffd5250c5ffe2928602ffcc943017f864a180bdc3250c01ffb0a8600bfd8543007fcc2a1803fd6150c01fe30a8604bf1854317ffea2a18bffe5150c5ffea8a862fff1454317ef8a2a180bff3150c05ef98a8602ff0c543007fec0a1802ff6050c5dff3028601bf98143007fac0a18bbfc6050c037e302862fffd414317efea0a18bbfe5050c5ffea82862eff14143017fe60a180bdf3050c05ff1828602ff0c143177fc40a18bbfc2050c5dff082862eff04143006fec6a90b77e6354801beb1aa42ddf18d5216efc86a90037d435485bbe21aa403dfd895201cfec4a900f6f625485bbf992a407df0c952006fec2a90037e6154801beb0aa400df18552024f8c2a90b77f315485bbe18aa400dfd8152004fec0a90b37e6054801beb02a42cdf1815216efe60a90b37e3054859be182a42cdf8815203ef840a90b37e1054859be082a407ffd963203dfecb1901ffe658c8077f32c6407df9963201cfccb1901ffd658c8577eb2c6407df59632004facb1901ffc658c80f7e32c6407ffd923203dfec91901ffe648c8217f3246407ef992320857cc91901ffd648c8017eb246407ef592320057ac91901ffc648c80f7e324642bffd5232157fca9190affd548c855fe2a46402bf58e32017fea71900bfe538c805fea9c6402ff14e32017fe871900bfe438c805ef21c6402ff50e32007ba871900bfc438c80f7f3146407ffd4a3203efea51901ffe528c80ffea946407df54a3203ff8a51901fff428c80fff2146407ff10a3203ffe651901fdf328c805f79946407ff0ca3203fd8651901fff618c80fff30c6404bf9863203ffac319
  | 6 => 0x318000c600708700017900007c1031eac00024067249c0000001e18f0000000000000000d49cf822a0289545e800157580075c000000040000000b852e4000000c703c06380000015b2648000a14e0a268001cf00000000016c4718dd40005c57b25002880000007c9ce00011685f13144201e9b40f695157d96aa571059b12308000238541d41d615c8000b69980001cdc0c06d6421620002079a60000a48e5800255175ddedcb1c627201602b9770d900016708c5cd8001a521e80000010f24d03300008c000106925a0126b83fc0016298d812966136000000060000096654d212088448e91604000cd1e400009880000000022784600000003d9b88000644001b3018800270c68a229555358000028340850000e28000000002055521380848000000000390000000000002478000640000000000000279f924280022d9bf9c7c0000000008320c088031de210b13c43486e409a190000708000b3000275151a200001ec8000000f6218908d3a9510000001c78000000000000000008000db0140f9167c0005d1d500008d49e8ce26290c8e250bc5c94bdaf0001509598001679ae8254cd839e03016507083c82a23a6d1dc877dc500023e83980016dd2c85b0e21c141725d970231183937a001bb8000ad0eb8fa1a10010002544cc8a811d23d99fa1787640b1df9c119313ca3a8c806541c9610000a5128056a2089683a5098911f51608000001b68c387d18c9bc009800400400403800002004c02001804001400002c09001403000c00c01800404008000001400c00000000401004805006000000002001c00c0080b000c00000801c00802401400403000800000002001000401c00400000802801000400001c00c00001803800800802c04400000800000c01000c03401000802000c01c00003000000c02404005000000c07800001007402800c00400c0100000140000b800000400001c00403402c00400400001400003c08800401804000000801c02c01803800000400801000400803800001c00402001801002400c01c01002402c00000401400400805c0080140e004c00000802400809800c00000000000000000000002800001404400001006400800800800000c01800000000002c00001400000400c02c00000800401c02800800800800000c02001401c00000000804400c01c04800c02400005801c03003c05006000401c00400000000400400000402000800c00001000000001002c01c00402400405c00800001000000400000402401800400000000004000003000000800003004400c00402000400003800c03000c01000401400001001c00000400003002401000000401401800002c00000c01003401000000400c0040380000000000b001000000000000000400c00c00001800000000c03802000400800800000000c0
  | 7 => 0x5787d94410b5118cf0a118b842933c0005fa600b613390c0781f70550001234179de1f616b2430000000000000f40ac00012304c00016cc001c5e5ba170a58940001e006d914821e58d75820d4f8980dd84ecd02504ee8060a996396d8000be12b8758339295a21ee00f400154d5d8698fdc0000000000024a8000001481341cd16310d89927780010a82c00011a977c0000000023f00000007003e11a1430fda0e04f5828e79a184040006c00005000024c96d13907e80017f0e5da01c39ecd191e680000000000480017c0d78e8041015109672ce11d5a685c019721da3b118a130ba82ca541ec59f4c79245e463e2349d387119f0350fba495caa211d900000022c1648b39f7a0f0f79ea9ea5ebc0023725f1c80000002120408a72738b34000d3954025e6a00016f99ecfa80009449b63380022800e8001b000001d181000000000131c002160468cf8dcde1910a399af80025a09215c000000240a599b80084225b6000170a650d28001299500ff82a25800000012ec0022480000018f9de4b5200976c798000a18001fc06c5e31368fb000198cd50a607352fdc18430158258ed0950030210898000bd00014b1988001d809fd40922d0f5c580000000000000026141480000018891e87e000245147a1a1789c482140009c044250c001324cbdd48ca8e1db0938993a5780000024e1b78be9c64e190e4bd98814d8260118e3260cb299600024986d0aa18a0e7453a379725104618cb483410cc092199c09b8000000001915c409b00008007600000026890d400131191248a2a000045895c000ba1fd87b97a98507400004dc000108a2a7253e0000001ab0dd21118b011532003a715e5d079c28000c59aa87f09a90c638965a6064d515176a0a26fce505b5220739491f0049cc56221761029858dc14b4219564570368731de9832480001641c88001e791d8000de11a41109288400000011202457314c0e2c0000024c1785da06dcb01dd8ff0559d700000000024f0728d60db93a22884c8ecdba93f9c98a21fb88d8206770afd27a2ba270000bb9728a0d0503712f15e0001e255fd720001ec000000215a7593322b0a052702d9ae2072460c314b9dd05c1420c20970bb64ea4cc0000012f44a9ad8001bd00000016d5e812419518e15800016500013340d8000051718000f18f48a78b180025540000000026d8000509d1030d9a0658001f3029000093c7a00010e88904a197800085a59c000130e142e04980010080000004fdce9200c114e16006f000000214a73000156a519fc8d800000e102ca3000259667840c8f1840001181039820001411690c91e1d77604a291a82718490868000001eb523d1381b0ed92f8b206120394f0f32639a78ca08ba71c0018085d8000000000001ed23306bc00000000047084655c001f4a6100012396e800
  | 8 => 0x12c1e3800000245874c000001f8a340810000d314e94c4000000000f296c01a89d1350f05f41128e3865278a1b941a06dc70000c19571b908cc201750771f193d838973800006c1f8b813d0b587b05100200000016b8002411d31d200017d0d200000000008c9be0324000002508000000c4000173c0013c016cf526981d8000002468000c69538d880002200022601f0588000001e4d68800000064cbc80017a0e652dc7504da6618184b03f8af09bd30946d9e0002658ed48aa670ac8e72300000fd42825ca6aa748000649878b3cda15b80793b8fd00003e822d370de94a000000000000196caa80004b42304e82a9e5a4b80000019415e84cc81a2e103c002608789dba3803b9060000000e695d14002b16841219000003ae760b9000000073d4c8002082058000000001742021ff0628180f100022a88e80024a1534000ad8f09681524000a91e500012e9991f29d8934a6c88a0000002150001f080003aa1f00002ea521b51455870efa7049dc9f800241800000026a2400000018680000000013983b5ef117815d72c000c492e1194fe40000900012d8d9827000184a1fa5e04b80006680000021d1c31e60000794001bc8000d19d003b0d084e5fa8000000138ef0b2c62128c6a083a140001c20000000001919438000b790e0000c352d1ee80000a0000000f71d28000000808a39ac05a19680004f89ec0f00000000004a49d800000000195a711d7955dbd9ab90400016a11986a95a175609000253c76c0017ea0600a9db144800007d7809a18605b800024c0000003f08890ae2d052909d0f800000258597400037877a7091313d5306700e894a8fccf8a10a0f924858194a569be8000000000948000001e9ceb5fa0001b183800000fe0e80000023180000000f88e00003d23462f01b92a20b80000011f17ba780000b4072157a6fa6c1d09cc0ae952932e29a5f8480a080000000021e0000000e486080021b0978a0233c7910b89e61c1498000c980000000000001046c952dad199927d161590000dfa588298000100cc0000001e10000000001ac8000519bb1544358661469318d40001d1800253a47171248cbfa4f886019a439260174ce83100019a9228e98cb2259d98fc2619d686f919c0013280011b8000002742304eb1898bc2510088c3c0016c88f8dc5ba0a40d100800018921a89f4f0c002530000001ca09e0001aa05305e13b094cda8ab1a99698001f20b711c0000068000001465020000488961ddcc88249c08e6d6f07f956e2fa54a6e9e99531e54002490000001dc10a0360000878001461fd2018eaa18011d5a84d4000a6867a67e3ca0d80004010115623f8075301a09f5a3923a1550a8a6e25590a46cc95800005a728b883c8f58fe1e906b2676250dc96186e2230775b9a1002363b85625b151df98000001a31ff8
  | 9 => 0x3a1a280001684d24405bd74859a3299e9250cb80002509c49d40000b95fa0d1a597c94719201c0000000000438000efc8bc414908ab80023212a800000000168c4e1ed8001091b72669588ee0000001b494d10880006ea5d18d03280000004c40020c8321f119d953c002590ec192a0b1034f80b466f00021395f07463d19d0190b99110754768002051da91b00007a85a8d58309081798000000000001df0e0063df80000f397e11fa6412094ae12a0aa6ee449745f68002768c52400ebc1a17f96e03bc0012691400014886900009998ea620f017640002d09f00000018ee359ea0bf0001285ef8001a3a1683153e80002fa5297366923c00000000008b10d12922c80000018c0c294500019b8fe9675171cb8000af8000000001a40000549a711ca6b00019b084c4180013f0c0130dc69c91fb1e095590fde71a689313cc001048000bb25e8000000000918000001a49cc954a5a92884adb58b086304f2069b381fcec49380c8e404bc0007848205200009c83010ec39423cea0b484518a91e0000001b2a21a3680005cc00110e6300020ad428900000df0002098f99a900010240009ccb10001e280024b0e60001e88ae10dda88002040000001bf0000ec80011012b21ca3526800008d0592361000d71fe9908b8c6ba1980d1e4945e5602f0749fe25c10ccf219c9eb1018d69b224d977a2e945974d158000001f38fc8019eb868020a11960c78d6684780
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x5738c510016f6638c510016f4638c510005f5728c5101af77528c51000775528c51000df6708c51000df4708c510026f7608c510027f3608c51010f77508c51010f75508c51010ff2208c510014ff764c51000cfe764c5100f4fd764c51000cfc764c5100057f754c5100357c754c5100067f654c5101067c654c510006df634c510016dc634c51002776514c51002774514c510027d4314c510005fb704c51000df8704c51000df4764c510016f4764c51000cf4764c51000777754c5101a774754c51000777654c5101a774654c510005f7744c510005f5744c510025f7734c510027d7734c510007d7634c510016f6634c510016f4634c51002fd4634c5101a7d7534c51002fd4534c51002fd6434c510007d5434c510005f7724c5101a777524c51000775524c51002fd7324c510007d5324c510007f3704c51000df6704c51000df4704c5100f7f0704c510026f7604c510027f3604c5100f777504c5100f775504c5100f7d7304c5100f7d5304c5100f7f2204c51000cfe76c851000cfc76c85100357e75c85100057d75c85100067f65c85100ee7c65c8510006ef62c851003eec62c851000dfa70c8510005f970c8510095f67688510026f6768851002777758851002774758851000777658851019f746588510025f77388510005f573885100adf5728851003ef6628851003ef4628851019f775288510007755288510027f3708851000df6708851000df47088510027f07088510026f76088510027f360885100c77750885100c77550885100c7f2208851003cff764851000cfe76485100acfd764851000cfc76485100057f75485100357c75485100067f65485100be7c6548510006ef624851003eec6248510027765148510027745148510027e42148510005fb704851000df87048510027f0104851000df4764851003ef4764851000cf47648510007777548510197747548510007776548510197746548510005f77348510005f57348510025f77248510027e77248510007e7624851003ef6624851003ef46248510007e46248510197775248510007755248510007f3704851000df6704851000df470485100aff07048510026f76048510027f360485100af7750485100af7550485100afe720485100aff220485100afe52048510025f8764811003ef87648110024f8764811018f7a75481100077975481100077b654811018f78654811000dfb724811000feb7248110007eb624811003efa624811003ef86248110007e8624811018f7b5248110007795248110007ea3248110007e93248110007f37148110025fa7148110025f87148110007f0714811000efb614811000ff361481101877a5148110187785148110007f23148110007f13148110007eb2148110007f22148110007e92148110007f12148110007e12148110
  | 1 => 0x8d10004bf7458d10084fe7458d10084fc7458d10006bc7458d10084bc7458d1010cff7358d10006df7358d1002ede4358d10004ff7258d10006ef7258d10004ef7258d1003cfc7258d10006ec7258d1003cec7258d100067f5258d1002edf3258d101e4ff7158d10006f77158d101de7e5158d101de7c5158d100f4ff7058d10006fb7058d100f67f5058d100f67d5058d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100057f7550d100357c7550d100067f6550d1017e7c6550d10016de6350d10006dd6350d1002f9c4350d1003cfe76d89100357c75d89100067f65d89100067c65d8910004ff75d89100067f75d891001cfe75d8910004fd75d891001cfc75d89100067c75d891001c7c75d8910014fe73d8910004fd73d8910014fc73d89100067f52d8910006ef32d8910006ec32d8910024fe71d8910024fc71d89101d67e51d89101d67c51d8910024ff70d891000cfe70d8910024fd70d891000cfc70d89100c67f50d89100c67d50d89100c6ef20d89100c6ed20d89100357e75989100057d75989100067f65989100067c6598910006ef62989100adf571989100057f75589100357c75589100067f65589100067c6558910005df735891002ddc73589100ddf77158910004ff75589100067f75589100047f755891001cfe7558910004fd755891001cfc75589100067c755891001c7c7558910004ff7358910006df7358910004df7358910014fe7358910014fc7358910006dc7358910014dc7358910006ef72589100067f52589100dcff7158910006f771589101867e51589101867c51589100acff7058910006fb70589100ae7f50589100ae7d50589100c4fe76189100357e75189100057d75189100067f65189100067c651891002dde7318910005dd731891003eee6218910006ed62189100067f76549100057e76549100067e76549100047e76549100067d76549100057c76549100067c76549100047c76549100067f635491016e7e63549100067d635491016e7c63549101cd7f72549100376f72549100067f625491003e7e62549100067d625491003e7c62549100257e71549100257c71549101667f61549101657f70549101657d70549101667f60549101677a20549101c77b105491016776105491016774105491016778105491003cff768c910004fe768c910004fd768c91003cfc768c9100357e758c9100057d758c9100067f658c91015e7c658c9101bdbe748c910005bd748c910006df638c910016dc638c910025f6718c910005f5718c91000dfa708c910005f9708c910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c9101467c654c910016de634c910006dd634c9101b5f6768c510026f6768c51000777658c5101af74658c510025f7748c510005f5748c5100f5f
  | 2 => 0x22e7c658cb10225be748cb10005bd748cb10025f6718cb10005f5718cb10004ff764cb10024fe764cb10004fd764cb10024fc764cb1021e7f654cb1021e7c654cb10016de634cb10006dd634cb10025f6714cb10025f7764c710216f7764c71000777754c71020f74754c71002777654c71002774654c710005f7744c710005f5744c710027d7734c710027d7634c710016f6634c710026f4634c710027d4634c71020fd7534c710047d4534c710047d6434c710007d5434c710005f7724c71020f77524c71000775524c710047d7324c710007d5324c71000df6704c71000df4704c7100f777504c7100f775504c7100f7d7304c7100f7d5304c710025f77648710006f77648710007777548710207747548710027776548710027746548710005f77348710005f57348710027e77248710027e7624871003ef66248710026f46248710027e4624871020777524871000775524871000df6704871000df470487100af7750487100af7550487100afe720487100afe520487101fd7e76d95100367e76d951001c7e76d95100067e63d95100067c63d95100057d72d95100257e71d95100257c71d95100257f70d95100257d70d95101277a20d95101f77b10d95101277610d95101277410d95101277810d95100067f73d95100067e73d95100067d73d95100067c73d95100067e43d95100067c43d95100067f72d95100067e72d95100067d72d95100047d72d95100067c72d95100067f32d95100067c32d95101267f71d95101f67e71d95100247e71d95101267d71d95101267c71d95100247c71d95100067f31d95101f67e31d95101f67c31d95101f67e21d95101f67c21d95101267f70d95100247f70d95101267e70d95101267d70d95100247d70d95101267c70d95101267f30d95101267e30d95101267d30d95101267c30d95101267f20d95101267e20d95101267d20d95101267c20d95101267f10d95101267e10d95101267d10d95101267c10d9510014fe76d8d100067f65d8d100067c65d8d1002ede63d8d10004ff75d8d1001cfe75d8d10004fd75d8d1001cfc75d8d10084fe74d8d10004fd74d8d10084fc74d8d10006df43d8d1002edc43d8d1003cfe72d8d10004fd72d8d100067f52d8d1002edc32d8d10024fe71d8d1000cfd71d8d10024fc71d8d101ee7e51d8d101ee7c51d8d1002edf31d8d10024ff70d8d1000cfe70d8d10024fd70d8d1000cfc70d8d1010e7f50d8d1010e7d50d8d1010edf30d8d1010edd30d8d100057f7558d100357c7558d100067f6558d100067c6558d10005bf7458d101bdbc7458d1002edc6358d10005ef7258d10005ec7258d101e5f77158d10004ff7558d100067f7558d100047f7558d1001cfe7558d10004fd7558d1001cfc7558d100067c7558d1001c7c7558d10004ff7458d10006bf745
  | 3 => 0xd65c852003def73c8520005ed73c8520026ee61c8520026ec61c85201876e51c85201876c51c852003feb70c852000dee70c852000dec70c852003fe870c852003eef60c852003feb60c85200df6f50c85200df6d50c85200dfea10c852000cfe76885201857f75885201857c75885200d67e65885200067d65885200aded7288520006f76188520026f4618852000dfa7088520005f9708852000cfc76485200057f754852005d7c75485200be7e65485200067d654852023f6f52485200076d5248520006f76148520026f4614852003fe42148520005fb704852000df8704852003fe8204852000dec7648520026ec764852000cec76485200076f754852023f6c754852023f6e65485200076d6548520005ef7348520005ed734852003def714852003fe77148520007e76148520026ee6148520026ec6148520007e461485201876e51485201876c5148520007eb704852000dee704852000dec70485200afe8704852003eef604852003feb60485200af6f50485200af6d50485200afea1048520004ff7558f100067f7558f100047f7558f1001cfe7558f10004fd7558f1001cfc7558f100067c7558f1001c7c7558f10004ff7458f10084fe7458f10084fc7458f10026df7358f10006df5358f10046dc5358f10046de4358f10004ff7258f1003cfc7258f100067f5258f10046df3258f10024ff7158f1000cfe7158f10024fd7158f1000cfc7158f100267e5158f100267c5158f10026de3158f10026dc3158f100f67f5058f100f67d5058f100f6df3058f100f6dd3058f10004ff7650f10024fe7650f10004fd7650f10024fc7650f100057f7550f1004d7c7550f102367f6550f102367c6550f10016de6350f10006dd6350f100479c4350f10025f67150f10004ff7558b100067f7558b100047f7558b1001cfe7558b10004fd7558b1001cfc7558b100067c7558b1001c7c7558b10004ff7358b10014fe7358b10014fc7358b10026ef7258b100067f5258b10024ff7158b1000cfe7158b10024fd7158b1000cfc7158b100267e5158b100267c5158b10026ee2158b10026ec2158b100ae7f5058b100ae7d5058b100aeef2058b100aeed2058b10026fa1058b10026f91058b100067f7654b100257e7654b101c67e7654b100247e7654b100067d7654b100257c7654b101c67c7654b100247c7654b101c67f6354b1016e7e6354b100067d6354b101c67c6354b101cd7f7254b1004f6f7254b101c67f6254b1003e7e6254b100067d6254b1003e7c6254b100257e7154b100257c7154b101667e6154b101c7763154b101c7762154b101657f7054b101657d7054b101667d6054b10167761054b101677a1054b10167741054b1003cff768cb10024fe768cb10004fd768cb10024fc768cb1004d7e758cb100057d758cb1022e7f658cb10
  | 4 => 0xc92003fae748c920005ed748c92003fad748c920005ad748c920135ed738c920016ee638c920016ec638c920057ce438c920007cd438c920005ed718c9202676c518c92000dee708c92000dec708c92003eef608c92003feb608c92014f6f508c92014f6d508c92014fea108c920014ff764c92000cfe764c920134fd764c92000cfc764c9201467e654c9200067d654c920006df634c920016dc634c9202576f524c9200076d524c92003fcc324c920005fb704c92000df8704c92000dec764c920016ec764c92000cec764c9202576e654c9200076d654c920005ef744c920005ed744c92003def734c92003fcf734c920007cf634c920016ee634c920016ec634c920057cc634c92025fcf434c920057cc434c920005ef714c9202576c514c920057cf314c920007eb704c92000dee704c92000dec704c920137e8704c92003eef604c92003feb604c9201376f504c9201376d504c920137cf304c920137cd304c920137ea104c920024fe76d852005d7e75d85200057d75d85200067e65d85200067d65d85200077451d8520004ff75d852001cfe75d85200067e75d852001c7e75d8520004fd75d85200067d75d85200047d75d852001cfc75d8520014fe73d8520004fd73d8520014fc73d85200067f52d85200067d52d8520006f751d85201867c51d8520006f451d85200067451d852000cfe70d852003cfd70d852000cfc70d85200de7f50d85200de7d50d85200def710d85201857c75985200067e65985200067d6598520006f761985200057f755852005d7c75585200067e65585200067d6558520005df7358520055dc735852005d7e75185200057d75185200067e65185200067d6518520055de7318520005dd7318520026f66118520006f561185201877451185201857f76945200267f76945201867e76945200057d76945201867d76945200047d76945200267c76945201875e73945201875d73945200067f639452012e7e63945200067d639452012e7c63945201876e72945200057d72945201876d72945200056d72945201267f62945200076e32945200076d32945201fd7e71945201877671945201867f61945200267e61945200267c61945201257f70945201277a70945201257d70945201877970945200057970945201267f609452024f7b20945201276e20945201276c20945201277820945201277a1094520004fe768c520004fd768c520024fc768c52011e7e658c5200067d658c520006df638c520016dc638c52003dee728c520005ed728c52000dfa708c520005f9708c520004ff764c520004fe764c520004fc764c5200057f754c52005d7c754c5201067e654c5200067d654c520016de634c520006dd634c520007cd324c520095ee76c852003eee76c852003f6e75c852003f6d75c85202476e65c85200076
  | 5 => 0x26ec614872003fe461487202876e51487202876c514872000dee704872000dec70487200af6f50487200af6d504872005e7f76595200075f73595200075c73595200067e63595200067c63595201cd7f72595200076f72595201cd6f72595200077771595201857c71595200077471595200057471595200077b705952027f7b20595201676e20595201676c20595201677820595201677a10595200067f73595200065f73595200067e73595200067d73595200067c73595200065c73595200067e43595200067c43595200067f72595201cc7f72595200066f72595200067f325952027e7e325952027e7c32595200067f71595200067771595200067e71595200067d71595200067c71595200247c71595200067471595200247471595200067f31595200067c315952027e7f215952027e7c21595201667f70595201647f70595200067b70595201667f30595201667e30595201667d30595201667c30595201667f20595201667e20595201667c20595201667e10595201667c1059520014fe76d8d2005d7e75d8d200057d75d8d200067e65d8d200067d65d8d20056de63d8d20004ff75d8d2001cfe75d8d200067e75d8d2001c7e75d8d20004fd75d8d200067d75d8d200047d75d8d2001cfc75d8d20084fe74d8d20004fd74d8d20084fc74d8d20006df53d8d20056dc53d8d20056de43d8d2003cfe72d8d2000cfd72d8d2003cfc72d8d200067f52d8d20056df32d8d20024fe71d8d20004fd71d8d200067c51d8d20056dc31d8d2003cff70d8d2003cfd70d8d2014e7f50d8d2014e7d50d8d2014edf30d8d2014edd30d8d200067e6558d200067d6558d20056dc6358d20275ef7258d20004ff7558d2001cfe7558d20004fd7558d2001cfc7558d20004ff7458d20084fe7458d20084fc7458d2014cff7358d20006df7358d20274ff7258d20006ef7258d200067f5258d20004ff7158d20024fc7158d200067c5158d20056df3158d20134ff7058d20006fb7058d201367f5058d201367d5058d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200057f7550d2005d7c7550d2017e7e6550d200067d6550d20006df6350d20016dc6350d200579c4350d201cd7f765492001e7f765492001c7f76549201667e76549201667d76549201647d765492001e7c76549200067f635492016e7e63549200067d635492016e7c635492003d7f725492005f6f725492003e7f625492003f6e32549201857c71549201c67c615492003f6f21549201657f70549200077b70549200057b70549201657d705492016778705492003e7f605492003f7b20549201676e205492003f6c205492003f78205492003f6820549201677a105492026dee768c92003eee768c92003f6e758c92003f6d758c9202676e658c9200076d658c92003def748
  | 6 => 0xc71597200067f31597200067c315972003e7f215972003e7e215972003e7d215972003e7c21597201667f70597201667e70597201667d70597201667c70597201667f30597201667e30597201667d30597201667c305972003e7f205972003e7e205972003e7d205972003e7c20597201667f10597201667e10597201667d10597201667c1059720004ff7558f2001cfe7558f20004fd7558f2001cfc7558f20004ff7458f20084fe7458f20084fc7458f2003edf7358f20006df4358f20066dc4358f2003cff7258f2000cfe7258f2003cfd7258f2000cfc7258f2003e7f5258f2003e7d5258f2003ede3258f2003edc3258f20004ff7158f20024fc7158f200067c5158f20066df3158f201367f5058f201367d5058f20136df3058f20136dd3058f20004ff7650f2003cfe7650f20004fd7650f2003cfc7650f200057f7550f2006d7c7550f2017e7e6550f200067d6550f202aedf6350f20016dc6350f200679c4350f2003dee7250f202afce3250f2003def764cb202a6ef764cb2003f6e654cb2003f6d654cb20005ef744cb20005ed744cb2003fcf734cb2003fcf634cb20016ee634cb2003eec634cb2003fcc634cb2029fcf434cb20067cc434cb20005ef714cb202976c514cb20067cf314cb2000dee704cb2000dec704cb201376f504cb201376d504cb20137cf304cb20137cd304cb20004ff75587200067f75587200047f755872001cfe7558720004fd755872001cfc75587200067c755872001c7c7558720004ff7358720014fe7358720014fc735872000cfc725872003e7f525872003e7d525872003ef771587202867c515872003ef7215872003ef421587200ae7f50587200ae7d505872003efa205872003ef920587200aef710587202857f76947200267f76947200247f76947202867e769472024d7d76947202867d76947200047d76947200267c76947202875e73947202875d739472024e7f639472012e7e63947200067d639472024e7c63947202857f72947202876e729472024d7d72947202876d72947200056d72947201267e629472024f6e32947200076d32947201fd7e71947202877671947202867f61947200267e61947202867d61947200267c61947202876f21947201257f70947201257d70947201267d60947201276e20947201277a20947201276c2094720024ff768c72003cfe768c720004fd768c72011e7e658c7200067d658c72003dee728c720005ed728c720004ff764c720004fd764c72003cfc764c7200057f754c72006d7c754c7201067e654c7200067d654c720016de634c720006dd634c72003dee724c720007cd324c72003def7648720006ef76487200076f754872028f6c754872003f6e654872003f6d6548720005ef7348720005ed734872003fe7714872003fe76148720026ee6148720
  | 7 => 0x85300067d75d85300047d75d853001cfc75d8530084fe74d8530004fd74d8530084fc74d853000cfd73d85302c6de43d8530006dd43d853003cfe72d8530004fd72d85300067f52d85300067d52d85302c6df32d8530006dd32d85301de7c51d85302c6f631d85302c6f531d8530014fd70d85301e67f50d85301e67d50d85301e6f710d8530006f7619853002df970985300057f755853007d7c7558530005bf7458530075bc7458530005ef7258530005ec7258530045fb7058530075be7418530005bd7418530026f66118530006f561185300267f76945301de7e76945301de7d76945300267c76945301df3e74945301df3d74945300067f64945302be7e64945300067d64945302be7c64945301df5e73945301df5d73945301267f639453012f5e43945300075d43945300057d72945300067f629453024e7c629453012f5f32945300075d32945301fd7e71945301df7671945301de7f61945300267e61945300267c61945301df5f31945301257f70945301257d70945301267f609453012f7b30945301275e30945301275c3094530127783094530004fe7690530004fd7690530024fc7690530006bf6490530086bc6490530015de7390530005dd7390530004ff7650530004fe7650530004fc76505300057f755053007d7c7550530086be6450530015de73505300079d435053000ddc764c530026dc764c53000cdc764c5300075f754c5302b75c754c530106de654c530106dc654c530005df744c530005dd744c530006df644c530006dd644c530005df724c530006df624c5302b75f524c5300075d524c530015df714c530017d7714c530007d7614c530026de614c530026dc614c530007d4614c5301df5e514c5301df5c514c530007db704c53000dde704c53000ddc704c5300f7d8704c530016df604c530017db604c5300f75f504c5300f75d504c530004fe76c8530004fd76c853003cfc76c853007d7e75c85300057d75c8530015de73c8530005dd73c8530004fe7688530004fd7688530024fc76885301dd7f75885301dd7c7588530015de7388530005dd7388530006ef628853003eec6288530004ff7648530004fe7648530004fc76485300057f754853007d7c7548530015de7348530005dd7348530004fe7608530004fd7608530024fc760853007d7e75085300057d7508530075be7408530005bd7408530015de7308530005dd7308530006ef620853003eec620853000dfa7008530005f970085300067f73597200067e73597200067d73597200067c73597200067e43597200067c435972003e7f725972003c7f725972003e7e725972003e7d725972003c7d725972003e7c725972003e7f325972003e7e325972003e7d325972003e7c32597200067f71597200067e71597200067d71597200067c71597200247
  | 8 => 0x76bf42d9130024fe71d9130004fd71d91300067c51d9130076bc41d9130316df31d9130014fd70d913030e7f50d913030e7d50d913030ebf40d9130084ff76591300057f755913007d7c7559130076bc64591302fddf7359130305fb7059130004ff75591300067f75591300047f755913001cfe7559130004fd755913001cfc75591300067c755913001c7c75591302fcff7359130006df7359130004ff725913003cfc72591300067f5259130004ff7159130024fc71591300067c51591302f6df3159130174ff7059130006fb70591301767f50591301767d505913000ddc7650d30086dc7650d3000cdc7650d300075f7550d302ef5c7550d30015df7450d300179f7450d300079f6450d30086de6450d30086dc6450d300779c6450d300869c6450d30005df7250d302aedc6250d302ef5f5250d300779c4250d30005df7150d302ef5c5150d300779f4150d30007db7050d3000dde7050d3000ddc7050d30177d87050d30016df6050d30017db6050d301775f5050d301775d5050d301779f4050d301779d4050d3003cfe76d8930004ff75d893001cfe75d8930004fd75d893001cfc75d8930084fe74d8930004fd74d8930084fc74d893000cfd73d89300067f52d89302e6ee32d89302e6ed32d8930024fe71d8930004fd71d89300067c51d89302e6df31d8930014fd70d89302767f50d89302767d50d8930276ef20d893007d7e75989300057d7598930075be7498930005bd7498930006ef6298930055f97098930065fb705893007d7e75189300057d751893003eee6218930006ed62189300067f76549300067e76549300067d76549300067c76549300067f64549302de7e64549300067d64549302de7c64549301667f635493016f5e43549300075d43549301cd7f725493007f6f72549300067f625493003e7e625493003e7c625493016f5f32549301dd7c71549301c67c615493016f5f31549301657f70549301667f605493016f7b30549301675e30549301675c3054930167783054930004fe7690930004fd769093003cfc769093007d7e75909300057d7590930015de7390930005dd73909300079d4390930004ff7650930004fe7650930004fc7650930006bf6450930086bc6450930015de73509302d79e435093000ddc764c93003edc764c93000cdc764c930005df744c930005dd744c93013ede644c93013edc644c930015df724c930017cf724c930007cf624c93003ede624c93003edc624c930007cc624c9302cf5f524c9300075d524c930005df714c9302cf5c514c930007db704c93000dde704c93000ddc704c930137d8704c930016df604c930017db604c9301375f504c9301375d504c930024fe76d853007d7e75d85300057d75d8530004ff75d853001cfe75d85300067e75d853001c7e75d8530004fd75d
  | 9 => 0x4318c55010d7f708c55000d7e708c55010d7d708c55000d7c708c55010e7f608c55011f7b608c55010f77108c5500057f764c5500067f764c5500047f764c5500057e764c5500057d764c5500057c764c5500067c764c5500047c764c5500057f744c5503257e744c5500057d744c5503257c744c55010d7f734c5500075f634c55008f5c634c55008f5e434c5500075d434c5500057f724c55027d7c724c5500067f624c55008f5f324c5500075d324c5501e57f714c5500267e614c5500267c614c55008f77314c55031f5e314c55031f5c314c55008f74314c5500f57f704c55000d7e704c55000d7c704c5500f67f604c5501077b604c5500f75f304c55027d7f76c85500057e76c855027e7e76c85500047e76c85500057d76c855027e7d76c85500047d76c855027d7c76c855027d7f73c855008d7e73c85500057d73c855027d7c73c855027e7f62c85500077761c85500267e61c85500267c61c85500077461c85500267461c85500dd7f70c855000d7e70c85500dd7d70c855000d7c70c85500de7f60c85500ef7b60c85500df6f20c855031d7f76885500267f76885500057e76885500057d768855031d7c76885500267c76885500247c768855031d7f738855008d7e73885500057d738855031d7c73885500ad7d72885500067f62885500957e71885500267e61885500267c618855031f6f218855027f7721885500c57f708855000d7e70885500c57d708855000d7c70885500c67f60885500d77b60885500c77710885500057f76485500067f76485500047f76485500057e76485500057d76485500057c76485500067c76485500047c76485500057f734855008d7e73485500057d734855008d7c73485500067f62485500267e61485500267c614855027f77214855031f6e21485500ad7f704855000d7e704855000d7c70485500ae7f60485500bf7b604855031d7f76085500057e760855031e7e76085500047e76085500057d760855031e7d76085500047d760855031d7c760855031d7f730855008d7e730855031f5e730855008d5e73085500057d730855031f5d73085500055d730855031d7c73085500dd7e720855027e7f62085500c57e71085500077761085500267e61085500267c610855031f74610855002674610855031f6f210855031f76210855031f6d210855027f7521085500957f700855000d7e70085500977a700855000d7a70085500957d700855031f79700855000579700855000d7c70085500967f60085500a77b6008550084fe76d9130076be64d9130004ff75d913001cfe75d9130004fd75d913001cfc75d9130174fd74d9130006bf54d9130076bc54d913000cff73d9130014fe73d913000cfd73d9130014fc73d9130316bf43d9130316bd43d913003cfe72d9130004fd72d91300067f52d9130
  | 10 => 0x895000d7e701895001d7d701895000d7c70189503567f601895035f7b60189503576f20189503576d201895027d7f768c9500057e768c95027e7e768c9500047e768c9500057d768c95027e7d768c9500047d768c95027d7c768c95027d7f748c9503257e748c95027f3e748c9503253e748c9500057d748c95027f3d748c9500053d748c95027d7c748c9501357d738c9500075f638c95008f5c638c95008f5e438c9500075d438c95026d7e728c95027e7f628c95027f5f328c95008f6f328c95027f6c328c95031d7e718c9500057d718c95022e7c618c95014d7f708c95000d7e708c95014d7d708c95000d7c708c95014e7f608c95015f7b608c95014f6f208c9500057f764c9500057e764c9500057d764c9500057c764c9500057f744c9503257e744c9500057d744c9503257c744c95014d7f734c95034f5f434c95008f5c434c9502757f724c9500067f624c95008f6f324c95027f5e324c95027f5c324c95008f6c324c9500057f714c95031d7c714c95021e7c614c95008f5f314c9501357f704c95000d7e704c95000d7c704c9501367f604c9501477b604c9501375f304c9500247e76d855008d7e73d85500057d73d855008d7c73d855027d7e72d85500057d72d85500067f62d85500067d62d855001d7f70d855001d7d70d85503367f60d85503477b60d85503377710d85503377510d855033d7d769855008d7e739855031f5e739855008d5e73985500057d739855031f5d73985500055d739855031d7c73985500067f63985500067e63985500067d63985500067c639855027d7e72985500057d72985500067f62985500067e62985500067d62985500067c62985501fd7e719855031e7f61985500077761985501257d709855031f7970985500357970985501267f609855004f7b60985500057f735855008d7e735855008d7c73585500057f725855027d7c72585500067f62585500067d625855000777615855031e7e615855033d7f70585500077b705855004d7b705855033e7f60585500377b60585503357e761855008d7e73185500057d731855031d7c73185500067f63185500067e63185500067d63185500067c631855027d7e72185500057d72185500067f62185500067e62185500067d62185500067c62185501257e711855031e7f61185500267e611855031f76611855002676611855031e7d611855000775611855001d7f701855000d7e701855001d7d701855000d7c70185501fe7f601855032f7b60185501ff7710185501ff75101855031d7f768c5500057e768c5500057d768c55031d7c768c55031d7f748c5503257e748c5500057d748c55031d7c748c5500f57d738c55027d7e728c5500057d728c5500067f628c5501b57e718c5500267e618c5500267c618c55031f5f318c55008f77318c55031f7
  | 11 => 0x26e9215802103ef12158021026f8215802139d7e76d8d503257e74d8d500057d74d8d503257c74d8d503757d73d8d5008e7e63d8d5008f5e63d8d5008e5e63d8d5008e7c63d8d500075f43d8d5008f5c43d8d5027d7e72d8d500057d72d8d5008f5c32d8d5031d7e71d8d500057d71d8d5008f5f31d8d5001d7f70d8d5000d7e70d8d5001d7d70d8d5000d7c70d8d503867f60d8d503977b60d8d503875f30d8d503875d30d8d5038d7f7658d500057f7458d500073f7458d500053f7458d503257e7458d503257c7458d500073c7458d503253c7458d503857f7358d500075f6358d5008e7e6358d5008e7c6358d5008f5c6358d500057f7258d5027d7c7258d500057f7158d5031d7c7158d503757f7058d500077b7058d5037d7b7058d503767f6058d5007f7b6058d500057f7650d500067f7650d500047f7650d500057e7650d500057d7650d500057c7650d500067c7650d500047c7650d502fd7f7350d5008f3e4350d5008f5c4350d5008f1c4350d500057f7250d5027d7c7250d5008f5c3250d500057f7150d5031d7c7150d502367c6150d5008f5f3150d501757f7050d5000d7e7050d5000d7c7050d501767f6050d5017f7b6050d501775f3050d5008d7e73d89500057d73d895008d7c73d89500067f63d89500067e63d89500067d63d89500067c63d895031d7e71d89500057d71d895001d7f70d895001d7d70d89501ce7f60d895036f7b60d89501cf6f20d89501cf6d20d89500067f73d89500067e73d89500067d73d89500067c73d89500067e43d89500067d43d89500067c43d89500067f32d895027e7c32d89500067f71d89500067e71d89500247e71d89500067d71d89500067c71d89500067f31d89500067c31d89501ce7f70d89501ce7d70d895001c7d70d89501ce7f30d89501ce7e30d89501ce7d30d89501ce7c30d89501ce7f20d89501ce6f20d89501ce7e20d89501ce7c20d89501ce7f10d89501ce7e10d89501ce7d10d89501ce7c10d89501657d769895008d7e73989500057d739895027d7c73989503557e729895027e7f62989500076f629895031d7e71989500057d71989503657d709895027f79709895005d7970989503667f609895006f7b60989500057f73589500075f73589500055f735895008d7e735895008d7c73589500075c735895008d5c73589500067f63589500067e63589500067d63589500067c63589500076f625895027e7e62589500057f715895000777715895000577715895031d7c71589500077471589500057471589501657f70589500077b705895006d7b70589501667f605895005f7b60589501cd7e761895008d7e73189500057d731895027d7c73189503657e721895027e7f621895027f6e621895027e7d62189500076d621895031d7e71189500057d711895001d7f701
  | 12 => 0xc7158c210267e5158c210267c5158c21026de3158c21026dc3158c21004ff7058c2100cfe7058c2100cfc7058c210067f5058c2109edf3058c21006de3058c2109edc3058c21006df7558c21006de7558c21006dd7558c21006dc7558c21006df7458c21006de7458c21006dd7458c21006dc7458c21006df5458c21006de5458c21006dd5458c21006dc5458c2103edf7258c2103ede7258c2103edd7258c2103edc7258c2103edf5258c2103e5f5258c2103ede5258c2103edd5258c2103e5d5258c2103edc5258c2103edf4258c2103ede4258c2103edd4258c2103edc4258c21026df7158c21026de7158c21026dd7158c21026dc7158c21026df5158c21026de5158c210265e5158c21026dd5158c21026dc5158c210265c5158c21026df4158c21026de4158c21026dd4158c21026dc4158c21026df2158c21026de2158c21026dd2158c21026dc2158c21006df7058c21006de7058c21006dd7058c21006dc7058c21006df5058c210065f5058c21006de5058c21006dd5058c21006dc5058c21006df4058c21006de4058c21006dc4058c2103edf2058c2103ede2058c2103edd2058c2103edc2058c21026df1058c21026de1058c21026dd1058c21026dc1058c21004ff7650c21024fe7650c21004fd7650c21024fc7650c210057f7550c210a57c7550c2117e7e6550c210067d6550c21016de6350c21006dd6350c2109f9c4350c21176fa6050c21004ff755802101cfe75580210067e755802101c7e7558021004fd75580210067d755802101cfc7558021004ff7358021014fe7358021014fc735802100cfd725802103e7f525802103e7d525802100cfd71580210267e51580210267c5158021026ef2158021026f62158021026ed215802103ef52158021024ff7058021026fb70580210967f5058021006fb50580210067b5058021096fa5058021006f95058021096f85058021006fb3058021096fa3058021096f8305802103efb205802103ef82058021026fb1058021026f81058021006fb7558021006fa75580210067a7558021006f97558021006797558021006f87558021006fb7358021006fa7358021006f97358021006f87358021006fb5358021006fa5358021006f95358021006f85358021006fa4358021006f94358021006f8435802103efb725802103efa725802103ef8725802103efb525802103e7b525802103efa525802103ef9525802103e79525802103ef8525802103efb325802103efa325802103ef9325802103ef83258021026fb7158021026fa7158021026f87158021026fb5158021026fa51580210267a5158021026f95158021026f85158021026785158021026fb3158021026fa3158021026f93158021026f83158021026fb2158021026eb2158021026fa2158021026f22158021026f92158021
  | 13 => 0x8d21006ef7258d210067f5258d210e4ff7158d21006f77158d2121e7e5158d2121e7c5158d21004ff7058d2100cfe7058d2100cfc7058d210067f5058d210b6df3058d21004ff7650d21004fe7650d21004fd7650d21004fc7650d210057f7550d210bd7c7550d210067f6550d2117e7c6550d21006df6350d21016dc6350d210b79c4350d2101e7f76549211c67e76549210be7d76549210257c765492101e7c76549210247c76549210067f635492116e7e63549210067d635492116e7c635492103d7f72549210bf6f725492103e7f625492103f6e32549210077771549210257e71549210257c715492100774715492102574715492103e7f615492103f7721549211c76e215492103f6c215492103f74215492103f6421549210057f70549211667e60549211667c605492103f6f2054921024fc764c9210067f654c9211467c654c921006df634c921016dc634c9210076d524c921005f7714c921025f4714c921014ff764c5210b4fd764c52103cfc764c5210057f754c5210bd7c754c5210067f654c5211067c654c521006df634c521016dc634c521005ef724c52103dec724c52100cfe76d81210bd7c75d81210067f65d81210067c65d81210aefa60d8121004ff75d81210067f75d812101cfe75d8121004fd75d812101cfc75d81210067c75d812101c7c75d8121014fe73d8121004fd73d8121014fc73d8121024fd72d812100cfc72d81210067f52d81210067d52d812103cfd71d812100cfc71d81212867e51d81212867c51d81210ae7f50d81210aefa20d81210aefa10d81210057f75581210bd7c75581210067f65581210067c6558121005df73581210b5dc73581210aef860581210067f73594210067e73594210067d73594210067c73594210067e43594210067c435942103e7f725942103e7e725942103e7d725942103e7c725942103e7f325942103e7e325942103e7d325942103e7c32594210267f71594210267e71594210247e71594210267d71594210267c71594210247c71594210267f31594210267e31594210267d31594210267c31594210267f21594210267e21594210267d21594210267c21594210067f70594210047f70594210067e70594210067d70594210067c70594210067f30594210067e30594210067c305942103e7f205942103e7e205942103e7d205942103e7c20594210267f10594210267e10594210267d10594210267c1059421004ff7558c2101cfe7558c21004fd7558c2101cfc7558c21004ff7458c21084fe7458c21084fc7458c21024ff7358c21026df7358c21006df5358c2109ede5358c21006dd5358c2109edc5358c21006df4358c2109ede4358c2109edc4358c2103cfe7258c2103cfc7258c2103e7f5258c2103e7d5258c2103ede3258c2103edc3258c21024fe7158c21024f
  | 14 => 0x26dc3158e21004ff7058e2100cfe7058e2100cfc7058e210067f5058e210cedf3058e21026f71058e21004ff7650e21024fe7650e21004fd7650e21024fc7650e210057f7550e210d57c7550e212367f6550e212367c6550e21016de6350e21006dd6350e210cf9c4350e2101e7f7654a210257c7654a2101e7c7654a210247c7654a211c67f6354a2116e7e6354a210067d6354a211c67c6354a2103d7f7254a210d76f7254a2103e7d6254a21007777154a210257e7154a210257c7154a211c7747154a21025747154a2103e7e6154a2103f6f2154a2103f772154a2103f742154a210057f7054a211667e6054a211667c6054a21014ff764ca21024fc764ca2121e7f654ca2121e7c654ca21016de634ca21006dd634ca2103fcc324ca21005f7714ca21025f4714ca21004ff75582210067f75582210047f755822101cfe7558221004fd755822101cfc75582210067c755822101c7c7558221004ff7358221014fe7358221014fc73582210067f52582210067d5258221024fc71582210267e51582210267c5158221026ef2158221026ed2158221026fb70582210c67f50582210c6fa2058221026fb1058221026f810582210bd7e76d95210be7e76d952101c7e76d95210067e63d95210067c63d95210257d72d95210257e71d95210257c71d952124f7721d95213a76e21d95213a76c21d952124f7421d95210057d70d95210067e60d95210067c60d95210067f73d95210067e73d95210067d73d95210067c73d95210067e43d95210067c43d95213a67f72d952124e7e72d95210be7d72d95210247d72d952124e7c72d95210067f32d952124e7e32d952124e7c32d952124e7f71d95213a67e71d95210be7d71d95213a67c71d95210067f31d95213a67e31d95213a67c31d952124e7f21d95213a67e21d95210be7d21d95213a67c21d95210067f70d95210067e70d95210067d70d95210047d70d95210067c70d95210067f30d95210067e30d95210067c30d952124e7f20d95210067e20d952124e7c20d95213a67f10d95210067e10d95213a67c10d9521014fe76d8d210067f65d8d210067c65d8d210b6de63d8d21004ff75d8d2101cfe75d8d21004fd75d8d2101cfc75d8d21084fe74d8d21004fd74d8d21084fc74d8d210b6de43d8d21024fd72d8d210067f52d8d210b6df32d8d2103cfd71d8d2122e7e51d8d2122e7c51d8d210b6df31d8d2100cfe70d8d21004fd70d8d2100cfc70d8d210067f50d8d21006de30d8d210b6dc30d8d210057f7558d210bd7c7558d210067f6558d210067c6558d210b6dc6358d21004ff7558d210067f7558d210047f7558d2101cfe7558d21004fd7558d2101cfc7558d210067c7558d2101c7c7558d21004ff7458d21084fe7458d21084fc7458d210b4ff7358d21006df7358d210ccff725
  | 15 => 0x4315053100cfe76d81311057c75d81310067f65d81310067c65d81310f6fa60d8131004ff75d81310067f75d813101cfe75d8131004fd75d813101cfc75d81310067c75d813101c7c75d8131084fe74d8131004fd74d8131084fc74d8131024fd73d813100cfc73d8131046de43d8131006dd43d813103cfe72d8131004fd72d81310067f52d81310067d52d8131046df32d8131006dd32d8131014fd71d81313ae7e51d81313ae7c51d81310f67f50d81310f6fa30d81310f6fa10d81310057f75581311057c75581310067f65581310067c6558131005bf74581310fdbc7458131005ef7258131005ec72581310f6f860581310067f73597210067e73597210067d73597210067c73597210067e43597210067c435972103e7f725972103e7e725972103e7d725972103e7c725972103e7f325972103e7e325972103e7d325972103e7c32597210ee7f71597211c67e71597210067d71597211c67c71597210067f31597211c67e31597211c67c315972103e7f215972103e7e215972103e7d215972103e7c21597210067f70597210047f70597210067e70597210067d70597210067c70597210067f30597210067e30597210067c305972103e7f205972103e7e205972103e7d205972103e7c20597211c67f10597210067e10597211c67c1059721004ff7558f2101cfe7558f21004fd7558f2101cfc7558f21004ff7458f21084fe7458f21084fc7458f2103edf7358f21006df4358f210e6dc4358f21024fc7258f2103e7f5258f2103e7d5258f2103ede3258f2103edc3258f2121e7e5158f2121e7c5158f210e6df3158f21004ff7058f2100cfe7058f2100cfc7058f210067f5058f210e6df3058f2103eef2058f21004ff7650f2103cfe7650f21004fd7650f2103cfc7650f210057f7550f210ed7c7550f2117e7e6550f210067d6550f212aedf6350f21016dc6350f210e79c4350f21014ff764c72103cfc764c7210057f754c7210ed7c754c7211067e654c7210067d654c721016de634c721006dd634c721005ef724c72103dec724c72102774514c721027d4314c721004ff755832101cfe75583210067e755832101c7e7558321004fd75583210067d755832101cfc7558321004ff7358321014fe7358321014fc7358321024fc725832103e7f525832103e7d52583211867e51583211867c515832103ef6215832103ef5215832103efb70583210de7f505832103efb205832103ef820583210defa1058321004ff7558e210067f7558e210047f7558e2101cfe7558e21004fd7558e2101cfc7558e210067c7558e2101c7c7558e21004ff7458e21084fe7458e21084fc7458e21026df7358e21006df5358e210cedc5358e210cede4358e210067f5258e210cedf3258e21024fc7158e210267e5158e210267c5158e21026de3158e21
  | 16 => 0xd313ef5c7550d311055c7550d310075f6550d313ef5c6550d31015df7450d310179f7450d310079f6450d31086de6450d31086dc6450d310ff9c6450d310869c6450d31005df7250d312aedc6250d313ef5f5250d310ff9c4250d31007d77150d31025de7150d31025dc7150d31007d47150d31016df6150d31017d76150d312375e5150d312375c5150d310ff9f4150d31005df7050d313ef5f5050d310ff9f4050d311057c75d89310067f65d89310067c65d8931004ff75d89310067f75d893101cfe75d8931004fd75d893101cfc75d89310067c75d893101c7c75d8931084fe74d8931004fd74d8931084fc74d8931024fd73d89310067f52d89310ceee32d89310ceed32d89313e67e51d89313e67c51d893100cfe70d8931004fd70d893100cfc70d89310067f50d89310cedf30d8931006ee20d8931006ec20d89311057e75989310057d75989310067f65989310067c65989310fdbe7498931005bd7498931006ef62989310b5f571989310057f75589311057c75589310067f65589310067c65589310e5f771589311057e75189310057d75189310067f65189310067c651893103eee6218931006ed62189310067f76549310057e76549310067e76549310047e76549310067d76549310057c76549310067c76549310047c76549310067f64549312de7e64549310067d64549312de7c64549310075f735493116f5c73549311c67f635493116f5e43549310075d43549313dd7f72549311076f72549310067f625493103e7e625493103e7c625493116f5f32549310077771549310257e71549310257c715493100774715493102574715493116e7f615493116f7731549311c75e31549311c75c315493116f7431549310057f70549311667e60549311667c605493116f5f3054931004fe7690931004fd769093103cfc76909311057e75909310057d75909310067f65909313d67c6590931015de7390931005dd73909310079d4390931006ef629093103eec6290931004ff7650931004fe7650931004fc76509310067f65509313ce7c6550931006bf6450931086bc6450931015de73509312d79e4350931006ef625093103eec6250931024dc764c931105de754c931105dc754c9310075f654c9313c75c654c931005df744c931005dd744c93113ede644c93113edc644c931015df724c931017cf724c931007cf624c93103ede624c93103edc624c931007cc624c93103ecc624c9313c75f524c9310075d524c931007d7714c931025de714c931025dc714c931007d4714c931025d4714c931016df614c931017d7614c93121f5e514c93121f5c514c931005df704c9313c75f504c931014fe76505313bcfd7650531014fc76505310067f65505313b67c6550531005df7350531015dc73505310079d4350531027745150531027d
  | 17 => 0x3cff7690a31024fe7690a31004fd7690a3111d7e7590a310057d7590a31015de7390a31005dd7390a31004ff7650a31004fd7650a31024fc7650a31086be6450a31006bd6450a31004ff755823101cfe7558231004fd755823101cfc7558231004ff7458231084fe7458231084fc7458231004ff725823103cfc72582310067f52582310067d5258231024fe7158231024fc71582310267e51582310267c5158231026df3158231026dd3158231026fb705823110e7f505823110efa305823110efa2058231026fb1058231026f810582314157e76d95311067e76d953101c7e76d95310067e64d95310067c64d953112f5e73d95311075d73d953112f5e43d95310057d72d953112f5f32d95310257e71d95310257c71d953112f7731d953140f5e31d953140f5c31d953112f7431d95310057d70d95310067e60d95310067c60d953112f5f30d95310067f74d95310067e74d95310067d74d95310067c74d953140e7f73d953112e7e73d953112e5e73d953112e7d73d95311065d73d953112e7c73d953112e7f43d953112e7e43d953112e7d43d953112e7c43d95310067f72d95310067e72d95310067d72d95310047d72d95310067c72d95310067f42d95310067c42d953112e7f32d953112e7e32d953112e7d32d953112e7c32d953112e7f71d953140e7e71d953112e7d71d953140e7c71d95310067f41d953140e7e41d953140e7c41d953112e7f31d953140e7e31d953112e7d31d953140e7c31d953140e7e21d953140e7c21d95310067f70d95310067e70d95310067d70d95310047d70d95310067c70d95310067f40d95310067e40d95310067c40d953112e7f30d953112e7e30d953112e7d30d953112e7c30d95310067e20d95310067c20d953140e7f10d95310067e10d953140e7c10d9531084fe76d91310067f65d91310067c65d91310febe64d9131004ff75d913101cfe75d9131004fd75d913101cfc75d9131024ff73d9131024fd73d91313febf43d91313febd43d913103cfe72d9131004fd72d91310067f52d91310febf42d9131014fd71d91314067e51d91314067c51d91310febf41d913100cfe70d9131004fd70d913100cfc70d91310067f50d9131006be40d91310febc40d91313fedf30d91310057f75591311057c75591310067f65591310067c65591310febc64591313f5f77159131004ff75591310067f75591310047f755913101cfe7559131004fd755913101cfc75591310067c755913101c7c75591313bcff7359131006df7359131004ff725913103cfc72591310067f52591313f4ff7159131006f771591312367e51591312367c5159131004ff705913100cfe705913100cfc70591310067f50591313bedf3059131025dc7650d31086dc7650d31024dc7650d310075f7550d31105de7550d31105dc755
  | 18 => 0xc748ca5122f3e648ca5122f3d648ca5121d7d738ca5122f5e638ca5122f5d638ca5112f5e438ca510075d438ca5142d7e728ca5122e7f628ca5124e7d628ca5124f5f328ca5112f6f328ca5124f6c328ca5122d7f718ca510257e718ca5122d7d718ca510257c718ca5122e7e618ca5122f76618ca511257e708ca510057d708ca511257c708ca5121d7f764ca510257e764ca5121d7d764ca510257c764ca510057f744ca512bd7e744ca510057d744ca512bd7c744ca5121f3e644ca5121f3d644ca5122d7f734ca5121f5e634ca5121f5d634ca514275f434ca5112f5c434ca513e57f724ca510067d624ca5112f6f324ca5124f5e324ca5124f5c324ca5112f6c324ca5121d7f714ca510257e714ca510257c714ca5121e7e614ca5121f76614ca5121f5f314ca510057f704ca511257e704ca511257c704ca5112f5f304ca510067f73582510067e73582510067d73582510067c73582510067e43582510067d43582510067c43582510067f72582510047f72582510067e72582510067d72582510067c72582510067f32582510067e32582510067d32582510067c32582510267e71582510247e71582510267c71582510247c71582510267f31582510267e31582510267d31582510267c31582510267f21582510267e21582510267d21582510267c21582510267f70582510267b70582511267f30582511267e30582511267c30582511267e20582511267a20582511267c20582510267f10582510267b10582510267e10582510267c1058251026781058251004ff755923101cfe7559231004fd755923101cfc7559231026bf7459231006bf5459231116bc54592313bebf43592313bebd4359231004ff725923103cfc72592310067f5259231116bf4259231024fe7159231024fc71592310267e51592310267c5159231026be4159231026bc4159231026df3159231026dd3159231004ff705923100cfe705923100cfc70592310067f5059231116bf4059231026f71059231004ff7558a3101cfe7558a31004fd7558a3101cfc7558a31004ff7458a31084fe7458a31084fc7458a31026ef7258a310067f5258a310b6ee3258a310b6ed3258a31024fc7158a310267e5158a310267c5158a31026df3158a31026dd3158a31026ee2158a31026ec2158a31004ff7058a3100cfe7058a3100cfc7058a310067f5058a31026f71058a310067f7654a311c67e7654a310067d7654a311c67c7654a311c67f6454a312de7e6454a310067d6454a311c67c6454a3116e7d6354a3141d7f7254a3111f6f7254a3103e7e6254a310067d6254a3103e7c6254a31007777154a310257e7154a310257c7154a311c7747154a31025747154a311c67e6154a311c75f3154a3116f773154a311c7743154a310057f7054a311667e6054a311667c6054a31
  | 19 => 0x91320067f50591322d6df305913201e7f765493216e7e765493216e7d765493201e7c76549320067f64549322de7e64549320067d64549322de7c64549320075f735493216f5c735493203e7f635493243f5f435493216f5c435493203d7f72549321476f725493203e7f625493243f6f425493203f6c425493216f6f325493203f5e325493203f5c325493203f6c325493203f4c325493221d7c71549321c67c615493216f5f315493203f6f21549320057f70549321667e60549321667c605493216f5f305493203f6f2054932014fe76509322d4fd7650932014fc7650932005df7350932015dc73509322d79c43509321457e75d85320057d75d8532004ff75d853201cfe75d85320067e75d853201c7e75d8532004fd75d85320067d75d85320047d75d853201cfc75d8532084fe74d8532004fd74d8532084fc74d853203cfd73d85320067f52d85320067d52d853221e7c51d85320e6f631d853200cfe70d8532004fd70d853200cfc70d85320067f50d85320e6df30d8532006f761985320057f75585321457c755853213dbe7418532005bd7418532026f66118532006f5611853200cfe76d8132136fa60d8132004ff75d813201cfe75d8132004fd75d813201cfc75d8132084fe74d8132004fd74d8132084fc74d813203cfd73d8132014fd72d81320067f52d81320067d52d8132024fe71d8132004fd71d81320067c51d8132066df31d81321367f50d8132136fa30d8132136fa20d8132136f860581322357f7650e510067f7650e510047f7650e510257e7650e512357d7650e510257c7650e512367c7650e510247c7650e514357f7350e512375e6350e512375d6350e5112f3e4350e5112f5c4350e5112f1c4350e510057f7250e5124d7c7250e5112f5c3250e512357f7150e510257e7150e510257c7150e512367e6150e51237766150e512375f3150e510057f7050e511257e7050e511257c7050e5112f5f3050e510067f7358a510067e7358a510067d7358a510067c7358a510067e4358a510067d4358a510067c4358a510267f7258a510266f7258a510067f3258a5124e7c3258a510267e7158a510267c7158a510247c7158a510267f3158a510267e3158a510267d3158a510267c3158a510267f2158a510267e2158a510266e2158a510267c2158a510266c2158a510067f7058a510047f7058a510067e7058a510067d7058a510067c7058a510067f3058a510067e3058a510067c3058a510067e2058a5124e7c2058a510267f1058a510267e1058a510267d1058a510267c1058a5122d7f768ca510257e768ca5122e7e768ca510247e768ca5122d7d768ca5124e7d768ca510047d768ca510257c768ca5124d7f748ca512bd7e748ca5124f3e748ca512bd3e748ca510057d748ca5124f3d748ca510053d748ca5124d7
  | 20 => 0x2d6bf31592322d6be31592322d6bd31592322d6bc315923203ebf215923203ebe215923203ebd215923203ebc2159232006bf7059232006be7059232006bd7059232006bc7059232006bf50592320063f5059232006be5059232006bd5059232006bc50592322d6bf30592322d6be30592322d6bd30592322d6bc305923203ebf205923203eaf205923203ebe205923203ebd205923203ebc2059232006be1059232006bc10592322addf7650e32086df7650e32084df7650e320075f7550e3245f5c7550e322af5e6550e322af5d6550e32015df7450e320179f7450e32086de6450e322af9e6450e320869e6450e322af9d6450e32086dc6450e322addf7250e32007cf7250e322afcc7250e32016de6250e32017ce6250e322af5f5250e322af5d5250e322af9e4250e322af9c4250e3245f5c5150e321579f4150e3245f5f5050e321579f4050e32004ff75586320067f75586320047f755863201cfe7558632004fd755863201cfc75586320067c755863201c7c7558632004ff7458632084fe7458632084fc74586320b6de4358632006dd435863203cfc725863203e7f525863203e7d525863203edf325863203edd325863203ef7715863222e7c51586320b6f6315863203ef7215863203ef42158632004ff705863200cfe705863200cfc70586320067f505863203eef2058632004ff755823201cfe75582320067e755823201c7e7558232004fd75582320067d755823201cfc7558232004ff7458232084fe7458232084fc7458232056de4358232006dd435823203cfe725823203cfc725823203e7f525823203e7d525823203edf325823203edd3258232004ff7158232024fc71582320067c515823203efb705823214e7f505823214efa305823203efb205823203ef8205823214efa1058232084fe76d913213ebe64d9132015de73d913203ddd73d913213f9f43d9132004ff75d913201cfe75d9132004fd75d913201cfc75d913203cff73d913203cfd73d913213edd73d913203cdd73d913244ebf43d913213edf43d913244ebd43d913244edc43d9132014fd72d91320067f52d913213ebf42d9132456de32d9132456dc32d9132024fe71d9132004fd71d91320067c51d913244edf31d913200cfe70d9132004fd70d913200cfc70d91320067f50d913244edf30d91320057f75591321457c755913213ebc64591322d79c4359132445ef7259132004ff75591320067f75591320047f755913201cfe7559132004fd755913201cfc75591320067c755913201c7c75591322d4ff7359132006df73591322d6be43591322d6dc43591322d69c4359132444ff7259132006ef72591320067f52591322aede32591322aedc3259132004ff7159132024fc71591320067c51591322d6df3159132004ff705913200cfe705913200cfc705
  | 21 => 0xe32d81524667c32d81520067f71d81520067e71d81520247e71d81520067d71d81520067c71d81520067f31d81520067c31d81524667f21d81524667c21d81521667f30d81521667e30d81521667c30d81521667f20d81521667e20d81521667a20d81521667c20d81521667e10d81521667c10d81520057f73581520075f73581520055f735815216d7e735815216d7c73581520075c735815216d5c73581520067f63581520067e63581520067d63581520067c635815236d7f72581520076f725815236d6f725815205e7f625815205f6f62581520057f71581520077771581520057771581521c57c71581520077471581520057471581520067f61581520067e61581520067d61581520067c61581521657f70581520077b60581521667e60581521667c60581521677860581520067f74596320067e74596320067d74596320067c745963216e7f735963216e7e735963216e7d735963216e7c735963216e7f435963216e7e435963216e7d435963216e7c435963203e7f725963203e7e725963203e7d725963203e7c725963203e7f425963203e7e425963203e7d425963203e7c425963203e7f325963203e7e325963203e7d325963203e7c32596320067f71596320067e71596320067d71596320067c71596320247c71596320067f41596320067c415963216e7f315963216e7e315963216e7d315963216e7c315963203e7f215963203e7e215963203e7d215963203e7c21596320067f70596320047f70596320067e70596320067d70596320067c70596320067f40596320067e40596320067c405963216e7f305963216e7e305963216e7d305963216e7c305963203e7f205963203e7e205963203e7d205963203e7c20596320067e10596320067c1059632004ff755923201cfe7559232004fd755923201cfc755923203ebf7459232006bf5459232156be5459232006bd5459232156bc54592322d6bf43592322d6bd435923203cfe725923203cfc725923203e7f525923203e7d525923203ebe425923203ebc4259232004ff7159232024fc71592320067c5159232156bf4159232156bc4159232004ff705923200cfe705923200cfc70592320067f5059232156bf4059232006be4059232156bc405923203eef2059232006bf7559232006be7559232006bd7559232006bc75592322d6be73592322d6bd73592322d6bc73592322d6bf53592322d6be53592322d6bd53592322d6bc535923203ebf725923203ebe725923203ebc725923203ebf525923203e3f525923203ebe525923203ebd525923203e3d525923203ebc525923203ebf325923203ebe325923203ebd325923203ebc3259232006bf7159232006be7159232006bd7159232006bc7159232006bf5159232006be5159232006bd5159232006bc51592320063c5159232
  | 22 => 0x8d522dd7e74d8d520057d74d8d522dd7c74d8d5216e7e63d8d5216f5e63d8d5216e5e63d8d5216e7c63d8d5216f5e43d8d5203d7e72d8d5201d7d72d8d5215e7f62d8d5215f6f62d8d5216f5f32d8d521c57e71d8d520057d71d8d5216f5f31d8d521657e70d8d520057d70d8d521657c70d8d520075e30d8d5216f5c30d8d520057f7458d522dd7e7458d522dd7c7458d5216d7f7358d520075f6358d5216e7e6358d5216e7c6358d5216f5c6358d5246d7f7258d520076f7258d5246d6f7258d521467f6258d521476f6258d520057f7158d521c57c7158d520057f7058d521657e7058d521657c7058d520057f7650d520067f7650d520047f7650d520057e7650d520057d7650d520057c7650d520067c7650d520047c7650d5216d7f7350d520075f6350d5216f5c6350d5216f3e4350d5216f5c4350d5216f1c4350d520057f7250d5203d7e7250d5203d7c7250d523de7f6250d5217f6f6250d522af5c3250d520057f7150d521c57c7150d522367c6150d5216f5f3150d520057f7050d521657e7050d521657c7050d5216f5f3050d5216d7e73d85520057d73d855216d7c73d85520ee7f62d85520ef6f62d85521657e70d85520057d70d85521657c70d85520077610d85520077410d855216d7e73985521c75e739855216d5e73985520057d73985521c75d73985520055d73985521c57c73985520067f63985520067e63985520067d63985520067c63985520bd7d72985521c76d72985520bd6d729855241e7f62985520d76f62985521c57e71985521c67f61985520077761985521657e70985520057d70985521657c70985520067e60985520067c60985520057f735855216d7e735855216d7c73585520d57f72585520076f72585520d56f72585520be7f62585520bf6f62585520077761585521c67e61585520057f70585521657e70585521657c70585520ed7e761855216d7e73185520057d73185521c57c73185520067f63185520067e63185520067d63185520067c631855241e7f62185520a76f62185521c67f61185520267e61185521c77661185520267661185521c67d61185520077561185521657e70185520057d70185521657c70185520067e60185520067c60185520077610185521c77410185521657e76d815216d7e73d81520057d73d815216d7c73d81520067f63d81520067e63d81520067d63d81520067c63d815203d7e72d815201d7d72d815206e7f62d815206f6f62d81521c57e71d81520057d71d81520067f61d81520067e61d81520067d61d81520067c61d81521667e60d81521677a60d81521667c60d81521677a20d81520067f73d81520067e73d81520067d73d81520067c73d81520067e43d81520067d43d81520067c43d815206e7f72d81521667d72d815201c7d72d81520067f32d81524667
  | 23 => 0x4957e76d954317e7e76d954301c7e76d954348f3e43d954348f5c43d954348f1c43d95430057d72d954348f5c32d95432357e71d954348f5f31d95430057d70d95430067e60d95430067c60d954348f5f30d954348e7f73d954348e7e73d954348e7d73d954348e7c73d954348e7e43d954348e7d43d954348e7c43d95430067f72d95430067e72d95430067d72d95430047d72d95430067c72d954348e7f32d954348e7e32d954348e7d32d954348e7c32d95430067f71d95430067e71d95430247e71d95430067d71d95430067c71d954348e7f31d954348e7e31d954348e7d31d954348e7c31d95430067f70d95430067e70d95430067d70d95430047d70d95430067c70d954348e7f30d954348e7e30d954348e7d30d954348e7c30d95430067e20d95430067c20d95430067e10d95430067c10d954303cfe76d894317d7c75d89430067f65d89430067c65d89434479c43d8943004ff75d89430067f75d894301cfe75d8943004fd75d894301cfc75d89430067c75d894301c7c75d8943084fd73d8943486dd73d8943446be43d8943446dc43d89434469c43d89430067f52d8943446ee32d89432aedc32d8943024fe71d8943004fd71d89430067c51d8943446df31d894300cfe70d8943004fd70d894300cfc70d89430067f50d8943446df30d894317d7e75989430057d75989430067f65989430067c659894344f9c4398943006ef62989430057f755894317d7c75589430067f65589430067c65589432d79c435894317d7e75189430057d75189430067f65189430067c651894347f9c431894303eee6218943006ed6218943024fe76d854317d7e75d85430057d75d85430067f65d85430067c65d85433f79c43d8543004ff75d854301cfe75d85430067e75d854301c7e75d8543004fd75d85430067d75d85430047d75d854301cfc75d8543084fd73d854303cfe72d8543004fd72d85430067f52d85432367c51d85433f6f631d854300cfe70d8543004fd70d854300cfc70d85430067f50d85433f6df30d854317d7e75985430057d75985430067f65985430067c65985433ff9c4398543006f761985430057f755854317d7c75585430067f65585430067c65585433bf9c43585432357c75185430067f65185430067c65185434779c4318543026f66118543006f5611854300cfe76d814317d7c75d81430067f65d81430067c65d81433079c43d8143176fa60d8143004ff75d81430067f75d814301cfe75d8143004fd75d814301cfc75d81430067c75d814301c7c75d8143084fd73d814303cfe72d8143004fd72d81430067f52d8143024fe71d8143004fd71d81430067c51d8143306df31d81431767f50d8143176fa30d81430057f755814317d7c75581430067f65581430067c65581432f79c4358143176f8605814316d7e76d
  | 24 => 0xc00400100100040000020070008002006009000c00c00000900380240030000000000016000000002e001000004000a001003800400000f0018004034000001000000800a000000401200b000000c00a00e00c8000004002000002002800a002800000000000a000c0000000018248010001000000000e005001000c008007000000c00c000000000c01c0260080008012011000805c000000004800001a00600b000003c008004802400400d0008000000000001802c00e002004000000c00b00600080000000010000006007000002801a00a008000801a01900200140260070008000002000000001802a015002000800a004003800000200500000000040060088004000000000004001a0060048050006004007800400000000000040000010000034004003001000c00000100300100340070000008002002007000c0100030070030028001001800000401c000001800a0050020030000003000002c042011004802000e007000001c0500030040014002005000000c01a014000800000600200000000040040010010004001000000804200c000000007a0000008010008018002001000000000000ac00600000000180000120048000000002002000401e001001800000001100780040000000010010008005000800401e00200700340080000020004022000000007400200000680040000020000010000002000806c01400500e800001a00100680080020040000024004002003800801800e00400000100050008004000000000801001600900800000000000038034004001001801800e000006800c03a0020018020008001000001c00800c0000008002000002803400000700000780000030020038000001000000c00001c002802402000100700000080070018010000002000001400c0170000008022006004002c010000006001800400000080000040140000058000011000801401800000a8030000005001003c032000000008400a00400981a401200000380040040210018014004000000803001c0000018020006000001001c002000002002c00c0030098010000018003002400200000080700140030060004002001000000c00200c000000000200400000080000010028014004012000800000800c000000803200200c000801c014001000400000000280280020040018060002001000001402000000280000540060020000024000010000400400000380080100000008004000000006800001600a00580280080010000038000000004807c00200f0000004030000001800000e004002005800e0050000020008002012804800a014000001800200d0000000008000001000800000c000803c002005002000000a022003000c002018002800802000000000080000000070078006007001800c0000020020000008002
  | 25 => 0x2001800000200000280000060010000020010002002801400e00300d0004018001006000000000000000240060000008000000000001800400c00e004800000600e0018014000001008800800600d00000f8000006000000400000000000080180000000004002000000800c01c0000058000002013003800000c005003000c00a003000000000000100a0000000001001800400a0070008008002007000801800003100580440000000000000000004000800001c004000800000000000d800800200400080000080000000000000001002801c00600200080140160030000004000003003003800a00d0060000008000000002800400700300480100010008068018009000000000000b0000010012002000800400000a0010000010000002000c000002003800003c00700680040060010028018002000000000800e004000800c01e00b003011400200500d801400000400100500060010060064006008000808800400400480000000000020058004037000000400000b0090000002000005800c00c001003805800800400480040100040028008006000003800c002001005803800400f001000400000200100140020120010000000002001003001800d0028008000002003001c00600000300080020030020028030000006001c002047004800c00400e002801400800b000000802a000003804400000000000000020010058004002004000005000400200000740040040008028002002001801400a00000380000240140038000000001000000001c02c00100000180000018024000003000802400602f003002800000200e800400400f00500040000010060000000000000000800a007000801000200a00580040020090020000028003002801400200d00000000100000088004020001020001400000b002803800600700180380020000000058002002004801000800e0008028002001001000c002001002000c00a0060020054000004000800000000a0010008052000000004401a0000008020000004003800002a00000f8000008000003801000800900000e002200000100080000010010058010004003800001400200000280020070008004000000000000000200100800040160000000000010000000007000e00c00180140060030058000006001007801000000e0000000004009000801c002002002801400c001000005800003400780280040000000018006001000802800600000100040340000008000004000009004400a0000008000020003004000402200000200000020000018004002000008801c02e0090068000004003000800000e0040020018010003001000400601b0000018038000000000004a02900080040200010030008000001009002800800b003000400001800700080000030000000008009000000
  | 26 => 0xefb510a800000000001bee90800391cf0700000002e124a00000000009e69a334f767dda2da50001ec435b236eccae600006433d8122d49cff666c0c991f87737ee00007c15877c80a09b4e000262242583663722109b8000122000361003a0007fe0521544a97000000138e44b475a1c10e4516bf8ac6c10c5ec6d985000000004d98001934d7167e31095b04aa08d861b58c2418000c59c98d906b71e48b6223409ba609b14565637ba6d866dfa7108000bda0003bc46f8ea62cd3408020a5ca76c127bfbfc00416bd91149dce64684000000000020718800000007b1800000083d13d13394a0ec7249800000076e800000050a0dd4cb10d40006980000001281d85000312d5eea5812d0000fc4f2b0000000b720003dfb6ac00000000000000008347d785dd592937f38003fa7e00039c256c0000000003282000000000000000090400032d400000000001e60000002f42f5554a18c7943d38000920715068de7449c36818b7bfc63e691b921abaad36a9d5f06469cd3a13b746120003639eedb7e1022af06f20905d14df320072673e28334991a068c0b8b2351bea2005b054ddcc611344af1cb0799f3e215d0956c5eb7fb3880001b70000584000c730000001f320004f2049672400000000000000000002b3000069e0000001f6a00000000012630000000000e26000108016aeda3b263c9f988c899c902000007a7df000802a0030000008000001001000402000000380000680000018030002004001003400400001880040020000028008006005000802001c0080000000000002000800000800b000000800000c00d8004000001000806c0000020030000002000002001c00000100380000000000038054000001003004c050002004801000a00100000040060070020030004009000800402e005002005400000000480600240000008008002011001004800c007002808c01a00d000000000a0010030020000001001001400200200180340160060008004000000008003c012003001002000c00a000800c000002000000400000200e802c00000900000040000030030010018003000000c02a000004000400002000a000400c005000000c016015000000006e000000801c01c00100d000402a004000800800e0010000050000006002000400c00300b80000280000010000016007007000000c016000002400a0030068010016005006000000200e00000080020030028064000006003801400a0000000008004000005002c00400100400200020010000020002000000004c018001001802801200900280080440170000000012001005800000003a001001000a008009000001a00300400b0004004004800c004004001000001a0010000020000000001000800c01400680000000030018038000000004800c000000004006400600
  | 27 => 0xe3207900000000372c0c0a489660004b2000039da04345ad27a8494104b8101d231831899035206000709129ce44cf46a998416e898443622a953c4df204255c6d7a121d5e66078a19203311b0d2e57ed29a32896abb04dba8150dea8085036b000071f25e5f30000ad10f29b3c0000003738d41dec7b4c008eee0500003208001c6874da3a8838d4470420a4e0559cde70003d6000000072d1d14228837480b60c6ad0000001e914427ad2502a65b5c64f3ffb53c9420007cf0001fdad59549395d75081a2e1ba8a82cf723873a768db0b947d8d75e5a1e20a8b9351480002a98001d27a940e83d7c72c1b10000000000bd0000069697af0c3c6300a0000fc315f1a0000b11000000164045b0000090000d4931d3b5d842e8d8003bf8c584b67e692fc00000037ff6ec0000006ea071d5bc00000000000000006d800005ca00037b8f8ff726eb33a80009966f820600006b4b331378001a2200024eb5d8000e2d729000000044c0000001a7a06a2af80004f60004e4b395dd453312588dcbe88da4689a9186ed2116a3bbe00000078da9646b00000002b7e5d48ba37102fc000000000064c0008f05c3204f27870603f0eb86daa6d57891ecc1caa10002b40000000721b184b3646b2bf15300005266aa09853369f000000000000007ae9be428800025840018244c142903585867fe7f871b80dc7a389d3f8cf8b0000000000be61c6136800000000000039f80000002a18331ce600022b87700002655198001f520002f20000000da131c000112a00033bf2d1ed4695600800199a82d1c622ac00000056133ed84c0000001c980006140003bc874200052b0498000000000351cf6e3b023f98c8000a087a337880007876421a01c308e61f61aac4e86763223699f7eb9c0dd2aad13e0c41151b084f2dd00a2bf96d362f654ce65c000b2a32b000000042d35e269a1b0d6384914d0dd49d9281400155d6e65ffb8880000d57160000000e2900006d04d48394b59204000a770000dec2ba0000a300000000000001288000000633e304ef83bf110be0d2420905ff2fe743837c51a01ad55c1794be3e94e19bf52e996206443b96be8480d1e79166a8b20722b8b17a01d9edeedc81d0001aa27e100023749801bb00026a0867a0e0e5b08ca52ec823c00000000000001cf5fd2c15181b441cf60001eaab0c0002070c9f5728fa7f6751f3b40002dc99f001025c4690001ea00000002bcbad791ef3b466a721e0ffc0680800142c0007473db1804c0371fb2aca968b67ff809c3d810d6994339c3c398038354800082b0002d24aee7d30000dfd87600048140013de0333729925658ff853e1b79ef61de14d086efca583598203d41800031194c9201d380000000000eeb0cd26180006550000001fc40006e9631555817050c2de15aefb4905800076ee563c
  | 28 => 0xb215654480b737a00009f219b00004d390e0000b632c82e8d1307f8bcd3dc0006290001e104f700000000003d719b9d793cc728329b6a0965000791ffe2000411234000104b907000000098ede900027384643c60001ddb8fe51c338000126dfc760b40003d04d1582a3b9356f5c7de4000000ee20003bf6000500184475036c0004c4b5dda945dfcfb25c8f6c1de80000000000003802b2ccb2000279000000055c1cf9750fc096379ab60bd12af56b28af4d8cae38cf40019700001178168a150005388000778f542788d312aa973366030c33a8e1f555ab80004277401f3c00033dbe24000000e0c209000065c0000be3cc400033a3e2b1410d00000003b30000c49513158d2f600062180000009b2e688000f9a0000fd0428000dad57e9e3e000796b92000177a3db2e7b540f5fb5a70825710980007b48464dbaef76f827c21080000001ac37d28127ef912971c9353048000c80c864fc21d8b4c6e68000000a84a830000c403ee65d5792f5d444000000000180a2196eadefea2000000012bd116423022ba35de0bf80110000d528db083156800012566408e927e0004ef39f4976ea5626000064e09a07a39c8bca8080001991a12f7e05bc001726cf900015fd79200048d00006aa64d25de99d93608d5f21a201ece1a00016ec5ce2737b318301ae18000019c80004a94b6142400000030aa9feef45ff44d883a0000007249d4831c00000034cd6d1e5928a35ccd0abac435000187c85e1fc0000acc1b245e8000a8e00000000016940002e50000000ec15fdc001d702c251c602db80aaac92162a7462701121635bc04414c4e2349f8467000301db3828455f9d59d66000000122000060a2a48000000bb11543f907dace70000000ef01496cb97800000002619bcc000eb000017c42767d201d9b92538a3e3143fca0000001b3a8b5af25ce8000000000aca76fd17513a2ab088309c6d238858a269db3ca5c4dc9bc9ceab3c1418000cb4591136263de8a54476c0001c00454180b291c5e00029e80002aa93d0000001aaa5ad203003c0000000000000000ea800035620009ff5eb318cf040004e03ff976a4ec00035c80009a3adebd7b10c2ee2e6a4b11f27660748000faa00000012d00000007c8a47ca261aec2e1835ee842ac6f38656b30003a63eb1d48cbd73f8e9d73c6fb6ecb1a4ac825447ab0e5ea40000934000000000154c000f4eaebaee13810205ae3eb0368012b1500030e97ee0000002dcc2daedc24683e124c0002311ac968304e1d420d708c0001ba00000000d00000000310739390a91c0002555f900016a60001069e5fba6bba000331800000024f4849ae80be6f90001b6a8ff42b4001e88c8100000000001c97b585cc0006b069a394ca0614e3dac00000000009e98610084d866d80016def2970db175d6798e09e00000
  | 29 => 0xa0a8610000000dafd827dd0de908a3be0003c690a2bbe2589de47cbf11000163800000012a720fe98b063cf80001820006803c585420000000000000be6000000000007c000000000079800013700000000001c5038892a6aec000154165129307454c00020e224cda70004702bc132052c00028d90feca53600c3007e77791e34ed54c0007db8f6000044c8a5304157c9a58cabf8b3c46298003b3d79e7fb3fa3c89f78300000028c00009e0000ae43668ef70a0a44000431577b9740006fd800000000000046c84791201fd30f1a488cc91ca7bf274e0aff02b4878d22e09554b25d1d141891e7a614d6642a07986e012fe8cbd174d8a4e7430001c2011e1320001755fe4d891759c36b322b40001875cd87e815184c4000fd37f980017080000000225cbe737bddc0000001bd80001cda0c2f16872440d4c9344212a9c0000004ef85da0000340eb808556e84bd95ab8d72a2643a3715175c42e0b7c181b6445060588a026788800003711b8c71d1cb8c400000000000013cf492000000109c0000003ab1d968b100005d3d4c6fd65bbc4200000066ec0000004cd000283c0004dd0000b4000000042d8000000000000384c0000002909041e32000733000000071735e84a9d44b213228c4421e960542b0218ae2022b098d512c0002e803ac0001f8078209edc85eb1b8e0cdcf21573f1885852800034f8dc0ae34073ab84040000007a51d760004d318e0001a3a0000828000fb69301993f2c93652d4ea38f033e821706864321019c973000144700076342f5cd00002ab0000000a8710a8001de200030e14289d63f48cef37a0000003da800039816a18398207364ba3dc3061e840000b1000088600037b7b280008f824880019ae578457208f08853155480011db7273fa896c000e1d00000000000004c0ae0dc08436000027000038979b0be50227033c84000000c14115a32e848333508b87d764bad27522b00000000003c1a0003c7c958001a4eb86e14b1d5dc8df73d01cec00099e59224b5d563f25b43b6e2be1d97c6073892cf9f01e3f4e95800032140012285bc000154501a76767619a8000f0596fcee0cc600052b800151000074822ec0008d54422e8079a9ac16b6c3400017200000009c8f565656620c5e76508d298499805b08fbd34ef6b7559e740d1ca54e72798a400059a6360dd4f28eae4116409dc38f7000000138b813735800002000020028950b42890000f80000bd82a01bf1a5d00000019798e5f186b000000000000001602809000029ab55ff90005638000174eaf258000000091d0002abf83ecc00003fb63d487d00c2e89d0c2696582c2548c0b3736a9e83e64c55a3b4b5e641990362a29536e426fe3f607edb5f32f9cb84adafb7c01650d1f99af673acaf10c73b2c17e848afce270dcd8834b084bfb63902b0006
  | 30 => 0x5bdad48256daf4fc9a51d8bb5780000012467ae8000c2a23a302100982cd06109343b1917325c08003341ba9c5c33a4000bacb5d0001a1000000022f2ae949a1a600000c8000000000000095a0006459cc506d0003e5a71801cc931670000000d658000fbc0000007ed981c0004d55f0a6a88647da66900000007995258b1000000000019d6b960000f4800043000055b000093f0002429b2800024e03c33140000003a31681e6000000000010dc00000005a01b2755000288d65e0004899b5200036250d87080006e300029a00005b551141f2ca42debfe98950b007a3b48000000a4800038e12d005d16e84856b2e5c58f0461d768c963f0a5de4b5af77044913eef5700034f17689456b420879d0987a520214000993b471f045c63c43259168850cb95b33e13d84994d0f8d205a20000d6015c9148e90f8306588ebc3384a2b5df079c58f9dd5dbdc926f5bafc000901a5d5ebdb7800028b0f7d2ee3a9a9c269f26e6928d124000008a902125c48560000000000000ae80002ad0000ab0d7af010000000068a98a000fcf61400000009dc0000000cc200034b2c617340000000001b900002cf00000000000000001994000000000000a62ee94000000084302c8000e9c47111b25f94d80003a48b0400000061b00007448c400016b055a0000000f05b52c6680002b99ecc4000000000001f5000000000000060b01ec0000000001bb5d341a800000008c27ae660f5056322cb12f000161900000000000000000000d516d679600029e4000bfb50d030a00053541914ac6e240a61a05815e580a25f00000c200032d8dd80009cb3c097d8e382422098001a48de11e8385c00074d0001015dddec60801d0493001a3e8b33051a69119eb399e494193da059a68874a698bac927678d47080d9ddb67b0f380519425e211331e87e8efc2ef0d5c00000004727b5f6602e00039e80000000001cbd0780e119b0c5d81753b2463e5400015e2b40000000aff2c09d5000052361700004184d25e0b7d95721081da3c020000004ed96fc0000001ea2ae1caa00003f80013220003021f3800055b2db2fb818aa64631021d2f036300009f16d8b727d1a4d9958000031331cee14e55cfba451c70007656120431fcc53f40009bc0001ed4000f3c000000282d076000000000000000000000000007f27b68000000866000000000000000015c173aee37d200000009418002b3c00000000000005fa0007b7000050ed62ae3c0016140005a23593166000032bff5920b5718a80013780003b0000000069a0000000000995a913023fb40001c7141c000bb853ac646f2a79a4e129cc000000059169dd2d6a04ca0001fa41c54f29ece354a860261f640008141216e8cebf24400027b0000716000256026cff6a6d6250e5a2cf7c10dee000e63414463560400026d3ba1
  | 31 => 0xe77632146921c5fdf0007a39b0400d6f99e623901e40000001c8c00038a4d10000aa80007d90000b90d4d616a8c9c1e56f51aa9f58d10637ce9ee8316e32474fdfda38ff90003b157a67150000f7e552bef1203e29f760000003f6b3ce0002d9ace5ff71820f684e12f4b2530c90bdcecd0478d4390b48bed2272c2298c0dd8003914436fb9e368001d74000000073c000000000000000083000000000005860188001e08cda0002eac0005e34eb22a00008b90ad80009ce915284296c2c8dc7098053d5dcdb15a401597e6def5bc80006fc49400000000bc00000032a574e8b079c80006f2d1433f205dc22a931cba6e000092236b37b1db6d7f1ff3c3ce14b377eba018f94ec33b532f0d8a0002ee8c689a566f7df666fc76a72653910070c8352ff345d458d254785bd65bc000058a126c7a00006d4000f5400021b503c000e3d7f73e157c6de0bad1b573a09114630000000f65b113c4710600000037d1ace9512d102581800002e2a84d4ea49e01c8f09d2c47301c38a00005b0000000122c0002fe319400047c08b18b40003680000e698c0ac80c3000000000000022895be0a616c357c8600003e1f605fa1db87439fb5fb33340000e416700000003e84551eb6001a1a400000021b8f95b1d3f6334a568000b165be3f6fb743fb7d3a585906774dcb16a414ed2c15b822655406f596820c000add00100015cc81280000008160000003af087000053bde0d2a02235c7a278b92b00612ba044602af00009e091e59754f83a736c51d29fb9396c401210a00011df4af9b0bd4504466b4398d6c000759247000000002c6b50001cbc5920000001e8277637b00002fe91c53f3601b681760558ec402e6bbad50f44ec45f80003e6079400041b10e59ab4760ffad35168efd26b04b581c1f2140ab9ca6c0066e7858c4b8ef4267dac5a903ea60f0000000739ffa00000006df5dc93c1914784d59d144bafbf6b74b75b7203736e9d3d528649f0003fc4e6ab613893c34c4812961ebc4ae4f00005a836c51e4378d2091c000b5b92608195ac0e86f8800000017d35a8000476000000325d9d235c0002388b82f7c0000000000d5e617b288dea3d9319bd885e4aaa51e19dc1f651f424b52c72a4010ce10f400065e8001e2935a41e0003a740000006440004000b016a32d446733e600000019dcbdc00006adfcce8f85769d1de6cae0001dc6000489671af8800009407f376c000000378ae48c6000070381d052a9f4048991d7cacaa78f00008b0f333e4be6c000ad4251b4680006cb09160bde38331c7b3dcc000ed92a81f000ea2511ce8d4d0f836e431aedd3e2a6f35f8000000d620003c1253041d0002452a1cc558000d256eccd4317d575f927e92f851e5eec04761012b8000c772d900000002a75d300000000000001ee40000002953711fb9000
  | 32 => 0x22161abc0005960ab31c8ff41e1b34000037871d9f5b8558ce5ce46b80000000000ef80a92acf16b672a2ddc06864a12abd80000004c0d2c0008cf4d02944eb82497808acc00069925e052dad8c7b52e97bc54a8cb5380288b0894c102bb790ca2135140228a0400015c4f1c100fc111a4001eb200027a1b544bee465a7b310ec60002f0af7c83e7610101fc0000c0a71c800021529b6a20000320dda22e23f5ff62674d9cbcbbc528e50c9dd00a2fc61560b312943ac7f580d2000d3a226c00000054600000012ba95f4e90000b460005c68001dde9380000001d6efa800000000000000000000000ab00000264000000174aaa0bd497609ca0080000000000ce4e8ee6522a800004c5fb10f1c79fea00000006fc4d69491ec51d011600044d3b551c1528487ae317042c919c00004fcf135c51299b3605b9298780000000286a4bc1eaf3f197a49c0009ca3167c49a5400000005e0c8b4492b6930866271150313b5c4e0005ad9dc00005890001eada5694f7049dc52dc0000001670f08eee10cc000000adb8001a2994600058e2a00a5e28653b13d9624ae074f7725ce2808884f2246481582eda6308ee3e20231e88d7145f0003f931980007a993280003c8025a01c3a2cdfddfa295d68f270a10cec1c000033c8001e20dff32fdaf895304d0a924d63c8bb65609340f86cf32bb1c9458aa29158bf14678f0020c0ee953085f75085ed73675e838961476ae8217e1085918c4a73e1cfd662000000264de546623032ea563ac0c00000000000000002d800002d5d7989400000006428000eee0000000001130bf4000004d7babaa7b20001114c4f3d307ad94000000031c1296e0200032c50966165b3ca7c05a8002a42fe53d00bb000220800000032e400000070d78383a22248a04e8bc8c19603e28590d60923cb5e28d788c6fb636d9e16d700007aa9b4cdb0005a7d27a494a00036a08e036a09f4e26dc1a5c00012ca1280007b2ad401107b8fa600000012900000760000b88a0333c000103c0000003139482d9d54a9708000f704150000000be00000f9c7dc0006e18000000000746293126200033b5cc8000000787c000000000185000090000000017653389d84756d709342358ea9629494ca80001e8cf4b9a60003634500fd180038cc00000074a53e0d38eec7bc2f2934a6fa4b317e579cb43440a5fe000a91011ae240380000862214df7bcb7f63de8890bc446640011f4d1666e769133a7301c00dbc000000000078400000045e00007910000001e3d8cc00000000000008b50000df3f080720003af5c4637200000000000004ee8b287c90000000000000000000000194c0006ee0fcc57800069bcd32fd666500036d974830557a0001e453657ea3c944060003e81388000cf18001b8029adfb45fb5b497da3807ea28451671a530100
  | 33 => 0x1d38e267e50001a300000003bd5e3e83a18c800052c0004eabac51a8f7557b10ec32e4ff3cb8a20000a8d2be62dc1de487abd337d766a2f22319f01503f91f43a4c7ac0cd7c40b659c0000212bee05ea000337000000000028a8000b3dafcb3334c161626305600000000000001ccc0007930000a8867e555000206d9a900057f00010ce43f43b8bedd5a51725fcf8c8cac56feb3a9daaeed60c8a1e587e8910698001dcaa6373000004381fe0fc51e897029d46cc001f680003b2074c0000000001276000f9a75aa7f800082074c02d3b98c7100038e9280dde0000f3f6b04720063ef403c27f64c213d3df0fbda801b4d6e3f5c6c2db4d5451141fb961f7fd156612f08580c460348504000d9424cb16400062acc032643f275158388e42dc1472c5800026ad2f8ec0000000bbb7ad8728b1824136413844c043a00000013c600043f35000008500000001534c70e0d0000000fdd0001ce800000028d80000000000000000cf4ae10001f746d65ca89fb8d2cae557718361cee528c69bb3bc58ca301ca2be49c63aa1703ae4118f2c0e42a8cafabfea820487c40175000234dba200000031f51461a13ec18f0c51d7a618a90c1dc36c7c3000192a0006e5153c000cf536b49c900d00000f99d1a1af5a4171cb0ac431f21f1e006acde302c2665e7800064fa5d41920006f500000000000003c900009c409f1e4609e0006c92c38e9600000015a9dd240f80000000000000bf000092a8c8755f105da000013100015c49e010f81287867ac00000010eae1c00029e112ea0d1590700000c6a0ca3708c62b5e00000011e40000001ab400090d531cb7060c530524b818d3f67300005ac00000054e3cddd1e0880000001702c5175a6fe92fa69009797c6b740001c7bb9c4f90fa7458c60c6c2df6ba8000e36bc04018c20c90b040000c3cc89e3766e8042000000000000109a00056dbe38dd88ebbf233c5fb254a3e3a090812bf17250000628cee8ed00010385c630180019b7de500027f19853dd4298e1c142b4b20189a03b6a69685000000063f2148001812ddf414c0000005d29de8000000000661800000087a0002017306c8e3fc29f70695be780c3a923c9f5781c3dc0a44e83253f0900f8a7176b80d9d349cc160821576ea915a8bb0660d6101b80549d21876e68d45404e54017b40969bed200012a2cd8cc90002910656bf05993c0a0000002a6b8d841e51a572b9a5a649b504083b5d2b0003ef00000004188000000a240250003828000cf80000140f200007f2bdf59b52e800020f800092e0000bcfda67682c78000a0dd693288aed2188747f43cf46cc9e16088000ac00004613eb8000afc172276878016f75186600000000003e490181dd65f3b12c54bbc21940000000007d58a799fcd0c3fe0ad876c000494368842ea8f42b0ff51da40
  | 34 => 0x93641339118e31d0e7c3f32415522b73d0c6c8b54169800135e518494b42ca0ad0f4028394fa8fd047a376172857b21a0e98fcef037fd16ac000b26385f2b4b9800000011a85de5c710e80000004a85a0b33cd72dd60f78b58a78bfd3c7135c00000012b3a64000ac47c75a85e040000002ca0194b46006800049ee245a01e849dea6a22215b110e87b49c8ca9e430001948d0cb3e4847603815b7cc9600000000000002a2a8e68574fe0ad000000038b1b86a045ae20a7bc800127c0000000cb0be03771a086940be2f86fc17494ca0001d6b135e1ce92a4100000000004d92098a02ad22fa9ca20f2b0f52f80011700004d88373fd4ec99cf185c6500f14618acf1af5823d99fb9ab42a02b90000d76000000366102abe70678000c9c4903c48000000a1e6d03358268ada0000679c6a00030d8000737e441f0d1f928ec5e287c27474a47000000000009c55423a500007bc3878b480000000f8b0c19f466076d0000964c555c008cc869f343f502095207c265fb9b89a8c0d436a9510327295c2bda1070000503895ca82c2a3b9f64c7e0150485ac409905956e7c000000daa5be8350000bea33f8f91f1a62e104a84000000011e9c740000000fd8bb7ab60000000000eb0b1a12c0001a6a6c42ce67e86805fd00026a474800064a35992a4adc0000998a6e88e000000098b00060980016e200075500016c600078b9a8c0000001b51885c80d967a786f40000431f16cd568ab1357c2174238000000000103ec659a380013d1417763f1e1844000000180e79d0af2f705b6ebe5e74656154246f48236a35ae880000000f16fae4b94321dd60000003d8417170e8d8800053119c00022b0001bccd8c3cf6684581dc6700839c00060f0000000000000000000000077f0001df869ab170002804dcbc385720a4c84c23152d2fac5740003b7c70c00070c5449481e3a0000000000db40000002cfc0000005fb39858acac000032bc000ac578a106c740000309b6197a2b3a0000001f2e2762b397a4e320000000ebc00000000004920007ef000372c000000292ada40005b457480003250f90000000000ce3c048349cf061a000270d46200065d118174aaed5752052b29cb353115c4bcf8782b9892917c0a46e282b5ddaa8e5d7ad5400046e7ce0399f2c8605f60ff1df200050493e6fd822d1c219b5cce5f5b5a136c9639065e68c780007106f9a692ce20670000000000a218000001a0eb4200028dd7b29fb4128894b3a841185b7d56cee504c3be4c5e0cce3c29f202b84b714c8001f028404f926eda5e0004b827a8000ab353a5051d08cc107fccb47f4c7c1520064b70edf3901e747fe24660c657869e9c135424152646f02f3748006aa140001bf2363701521375c39a35f05e1b4a4baaa016aa8ec0000004238000ccea3f6228000000e0b42ca3
  | 35 => 0x89da863e168faddc57c4bdf1f3ea800028a187265505223e754fef6b4a6b67e8a8759df0000d867ccc4e0007289b0c0000001706e85f1e00007cc759100bd40000afd99da1549c63cdf5a2b814836dd97600008abf211c638313ead91e92f89e8c8f68a74be80003738e90ca3e1218e4995a450003ce1a448280001011214de19bc2e5ca4877247f3654da296d4da11c26c01e649d015060810b71296dc1bc3452fbbf8f8eccf04890b8564659874fb279bc82db3c59815f7121af3515ac000abc1fb9e180000000001805ad69e9dbf9b659220001b7c154000d560000001e42ae6b66b0f000000030900018b0c321f489c432c0b6f7d9ef52d20001580000000d4e26cb2700000000003f55c1c00b0003b220000001a700000006fef850000000a0041880014c33f3d36e9ba000dfd0000000000033e2d80003e8d7c0bd0001cb6efa6f680000005c0474177c0004971cc91488783de3b580000009190000bfc844e950c79398000cff0b491bd37aedd8000000286f604b11cf00000000002f20eb600017f33a82b29e6f3a22999b80000000ab8e80cc0800390435accd8000001288d78000105420e3f10001ea414a65c0000000000c4400000016f4c60cac947999f6347fba518c8ccf0ed1b10ec875580000000000f5067080005c3db90001bf80005800d7bd9d9e457dce7bb10000988d9f1808000c3503ea8ac000c5f7171bb8000523f9784b1e4cd70243ae2035fbd21a10c26000d120003c180007070000000000afa0c5000020800000000001b700055882a40220005a70001e5c99267e800134894d058238ae6e12847600000563d9bbe8000a7238d6b789ddf16e167b8a059e0ad2900000014a4d1e00016400000002277a7f6ac1a07ca000000031b08180000001d238592273fa69300d80004580000000bb3124a550002a3168bc5a00000000000000000000000a7f0001ec737edee3210001f0e00007f5a9c000abd000262c00080e000000030a1f675f0b1dbaac744c50f49a360b445788b849a0000001ab104df8900000014d6b3b446187d0d6ea0000086945c7dc00025397b6ceb3413531a7c96f0631761c1000000000000009187d7dd74000ddd171000064af157ae65e55bd00054eb14d8560293d241ddcc4eb1bcd91c68a60003a800000005e60000000000b3feae0389dff1176b75cd166c6ba37bc0000000000d3705d3d6000665869ca1300069c9b2490c45942ac8a448691b76480003dcbfc0000000f644cf7e200011640000000000000c74800111c89e8e7186acd000015409396840000c800035f80004c900028a8c00e8800035614df68d79f0df41f569d31dbfbb55a4fb263eab74dc3c6b3ebf9c3823467af060556444d6e9358c226a404b2e5a9798cd0abaad0ae5622227eb9dd6cafb14b3ba151e285728c94307565
  | 36 => 0x1e160005278000f8c00000006a4000cb60000000ede0007b2a635f448ea00029ec5ee3a97e95941b0d6ef6a2a08d0c4df9368fa0c9bd1334e9aca4be44203f9a2653ae5c3f4bbd010956e80002595e1209b0003fbcf4a3523c96b64000000000289c0009c380000000000001d98f4c000ff18050611b22bde5bf28e8cbb7020d727304eaa5e4dd28f56e3c0636e09eff40acd505000002cc0f669ad316446d76f40001b7a6e17b0838c0000305ed227172200029f0296a1e0002914000e9e1fc5762bacfeed8f32631539eed8b6161db9f60b037df092066aab546b337800062610031760c8eff74f33658bf4830612a9079c3820001e8704e8ecd0b8b69b10b6e37d431c70aecd0b331219db7be4a9bb853607f940e9c601fb1675331db1504b0c1ce3f8486610e4aa3ddc46ac1c1102a0778c23f0003a3a624fc374924cdc561b91a50000ca8000725a668da4b271ac9be2000000000000165cc6b5b539bc0002dd8499a9535c5da17d04451122110000001b820007a5800121cd9a0001ca800000000018ad4630681e4bf78000b3d000223c3605d71fa8
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc5e7319462440014db04328c4880ff1d5c465189104ae3cb80ca3122000c5f655cc62440018b8cab98c4880023be1d62189100056641ac4312200087e869d952440014db053b2a4880021f60a765491000636c14eca92200487f809d952440090fb013b2a48800297e0d765491016d2e41aeca922000a6f825d952440014ef02bb2a4880121fa0476549100243e408eca92200487f801d952440090fb003b2a4880031e88076549100063b080eca922000c74101d952440010ff0eb1aa4880021f21d63549100051fc22c6a92205ba3c8458d52440014df04b1aa48801e9b209635491001c3e43ec4a92200087f8758952440070f90eb12a48800297e0d625491016d2e41ac4a92200387c859da32440010ff0abb4648800e1f215768c9100043e432eb192200087f87d9632440010fb0fb2c64880030f9d3658c9100061fb2ae91922000c3c655d2324400193ce9b1c64880063d219718c9100247c432e1192200387e85dd932440010fb0bbb264880021fe15764c91001c3e42aec99220008bf845d9324402117908bb2648800237e0d764c91000477c12ec99220108be841d9324400117b083b2648801e3721d634c91013d4e422c69922007acc8258d32440014e90ca9462880fe1fa1b754c5104143f43eca98a202487c87d95314404b8e8edbaa62880035c1c3754c5101263a3b6ca98a20018f4865d131440033e100ba262880d2d5215434c510006f1106e498a2000a748654931440598e8eca926288002b5219324c5101fc3e432eb90a202487f87d9721440010fb0fb2e42880029d21952885101fc3f436ea90a2074d7010dd521441290fd0fb2a42880921f21f65485101f73210eca90a20018fa86dc121440938e8edbaa42880035c1c375485101263a3b6ca90a20018f4865cd2144001cceca31242880029d219524851003e3a3b2a490a2007e646254921440614f10cbaa408813f1e1d975481101cdb5c12ea9022030b70815d5204407d8f0edb2a40880039ad946248110005e4c18c49022000a7886549204400f8f0eca92408801f9a1895248110005d4c24649022000be1818c92044001ae2ea38a4088002f460c7148110005f0c14629022000fc1324c520440099d0ed90a40880133c1da21481100adf0c144290220019e88748520440099d0ec90a4088013781c52148110187b128a429022030f605148520440035e10c90a40880133c1d9214811003f70312429022093f63524852044001ec2a490a4088006f821d2148110026f043a429022001be28648520440037c10c90a408801fb8219214811003f71bb2429022004de2764852044009bc0ec90a408801fb81d92148110007b1c2a429022093f60854852044127ec4ea90a4088003d85d52148110007b1b2a429022093f606548520440017c70690a4088002f860d2148110
  | 1 => 0xd0839eca880028f61073d95100062eb98e7b2a203ea76811cf65440494eb0239eca880121fa0572d95100243e40ae5b2a205087f805cb65440610fb00b96ca8800297a0c72d95100052ec18e5b2a203ea76811cb65440494eb02396ca880929ea0072d95101f53cc00e5b2a2000a3e84ccb654400147b09996ca880021fa1c32d95100043ec3865b2a202487e87cc765440010fb0f98eca880022fe1172d8d100845e422e5b1a200087e87d956344001878e9b2ac6880021fa1c6558d100061e3a0cab1a2000c3f65dd16344001878cbba2c6880031bd977258d100063632ee4b1a2000c6f651c963440018d8ca392c6880033318c7258d1001c3f43eeab1a200087d82dd563440010ff01baac6880021f6037558d100045fc22eab1a20108bc845d563440011df04baac68801e3b2097558d100043f438eab1a20108be87dd1634400187eebba2c6880030f1d77458d100061f28ee8b1a2000c3c51dd1634400187ea1ba2c6880030f5437458d100061fba8e8b1a2000c3c751d16344001938e9b9ac68801e3ba1f7258d1000637baee4b1a2000c6c75dc9634400195ee9b92c6880032b1d37258d1000637c2ee4b1a2000c6c85dc963440018dca3b92c6880031b1477258d1000637a86e4b1a2000c6d50dc963440018deea392c6880031b1d47258d1000657ba0e4b1a2000cac741c9634400199ee6392c6880021fa1f5258d1001c3e43ea4b1a2000c3f74d49634412f878e9a92c6880031bdcb5258d1003e36396a4b1a200387e85dd943440010fb0bbb2868800e1fa167650d100043ec2ceca1a2000c9c439d943440010ff0abb2868800e1f2157650d100046fc1aeca1a20008ef825d9434400f1d904bb2868800e1f2147650d100064e218eca1a200087e86dd543440092ed03baa86880021fa1f6550d100043e43ecaa1a2000e1c43d9543440211b90eb1a8688042a72116350d102ad66412c6a1a2000a6d82dd762440014db043aec4880021fe1573d891001c3e42ae7b1220008bf845cf624402117908b9ec488002aba1332d891001c3f436eab12202487c86dd562440010fd0fb2ac488003171cf65589100043f438cab122000c5c73195624412d8eee232ac48800317d9773589100062e32ee6b12200387e87dd562440090fd03baac4880121f20775589100043fc06eab12200087d80dd562440011bf06baac48800a3720d75589100047bc0aeab12200087e871d562440051bd0fb9ac48800317dd773589100062e3aee6b122000c9f74dcd62440018bca3b9ac4880031714773589100062fa86e6b122000c5d50dcd62440018beea39ac488003171d473589100064fba0e6b122000c9c741cd6244001998e7b92c48800317dcf52589103de2e39ea4b122000c7475dc5624400d0fb0fb28c488003179cf651891000536c16ca3122000
  | 2 => 0x265185200043fc3aca30a4000c5e7359461480094e902b28c2900031799573185200062eb2ae630a40008f78758461480014e90ab08c2900025be0976945201d43fc12ed28a4000c6f825da51480090f902bb4a2900031ee0176945200243f43ec728a400087d87d8e51480012f700b94a2901275a081729452002637c32e528a4004c6c865ca51480098dcc2b94a2900131b1857294520006b5c02e528a4000d68805ca51480a18dec0b94a2901275ad817294520186b5082e528a4030d69105ca51480012db0f194a290002cb6123294520125364326528a4004c7b865c251480098f10cb84a2900035ae097094520006b4412e128a4024c7b625c25148049ad6c4b84a2900035a8c97094520006b4992e128a4004c7a615c251480098f0c2b84a2900c35ac857094520186b490ae128a400387e859da31480010fb0b3b462900022fe11768c5200845e422ed18a4004a748159631480031d90cb94629000e1f217764c52001c3f42cec98a400087d859d931480070fd0a3b262900021f614764c5200043ec36ea98a400096d82dd531480010fd0eb2a62900021f21d654c5200253a40aca98a40048dc8758d31480095a902b1a6290003331d9324c520004b7c3acb90a4030b648159721481196d700b2e42900121f21d65885200253a40acb10a4030c7475d8621480612db05baa42901275a08375485200243e43aca90a4004a7481595214809fcc842b2a42900c25b21d5248520166363b2a490a4030b64815492148071cc8c2a9242900b35a1c152485200063a3aec290a4074c6c76dd52148001ad0e1baa42900c25b21d6548520166363b2ca90a4030b648159521480016d700b2a42900063b219734852000732b28c290a400387e87dd563c40018bd07baac7882071760f7558f100043ec16eab1e200487e81dd563c40090f903baac7882061fa1c7558f100246f43ea6b1e2000c5f75d4d63c40010fd0fa92c78800e1f21f5258f1001c3f42eeca1e200087d85dd943c40031ed03bb287880021fe157650f1001c3e42aeca1e200487e86dd543c40090f90dbaa87880125da077550f100246e43ac6a1e2000c5c7558d43c402153908b1a878800e1fa1f7558b100243f40eeab16200487c81dd562c40e90fd0e3aac5880121fa1f5258b100243e43ea4b162000a6f825d952c40010ff0eb1aa5880021f21d6354b100243e43ac4a96200087f855da32c40070f90abb465880121fa19758cb100243e432eb1962000c3f655d232c4001878caba4658800e1fa17764cb100043ec2eec99620018f681dd932c40010ff0abb2658800e1f215764cb100246e43ac69962007acc8258d32c40836a90aa1a63880129d219524c7100256a4326498e2000c7475dd921c40094e90ca92438801f9918952487100051f420c7b2a2000a3d8418f654400147
  | 3 => 0x2b2a4000a79800c56548001cb6e7b82ca90003961cf70595204de3db96e0b2a4000e6b72dc16548001ce6e3b82ca900039c1c770595201ccb7c12ebb1a400087d8799763480010ff0eb2ec6900029d20565d8d200043ec3cebb1a400387f875d763480018bf06baec6900031720d75d8d201cc3fc12ebb1a400487c815d763481190ff00baec69013e1f60175d8d200062ebaea7b1a400387f87d4b63480010fb0fa96c6900021fe1571d8d2001c3e42ae3b1a400487f8714763480010fb0e28ec6900029b60851d8d200053cc00a3b1a4000a7481595634800117f08baac6900422f2117558d200046fc1aeab1a40008f7815d563480091e902baac69000e1fa177158d200043ec2ee2b1a4000a6d8214563480018eee228ac6900131d1c45158d200053cc00a2b1a400387c85dd943480070fd0b3b286900021f6167650d200043fc2aeca1a400387c855d943480011ef02bb286900123d2057650d2001c3f428eca1a400087d851d943480010fb0dbaa86900025b60b7550d200043f43acaa1a400087c875954348001c3886b2a869011a9d2056550d200846f43ec6a1a4000c5c75d8d434802153d09b1a869026a1fa1f63549201643ec3ec6a924007a7a86dc1524800f6d505b82a4900b31ea1b70549201663cc36e0a92402cd6a82dc15248059ad305b82a4900b31ed8b7054920166b5b16e0a92400096f8759632480016c902b2c6490232dae01658c9200069732ae91924000d2d655d23248001a58a2ba4649001f2bd81748c92003ed5b02e91924000d2f505d23248001a5aa0ba464900036a841748c92027f26192ca9924043a748159532480598d8eca9264900b79318d524c920166b4382a4992402cc6c765953248001c98c6b2a6490002d9205654c920005b5c02ca99240079cd83dd132480031d90cba264902676310d744c92000cf4402e8992403996f825d761481192f700baec2900c29d20565d85200053ac30a3b0a4004c767614761480016cb0428ec290002dc60051d85200043ec3cebb0a40008df835d761480051b906baec29000e1fe1d75d85200062fc1aebb0a4000c5c835d761480730ff04baec2900031de0575d85204643fc02ebb0a404f87d805d761480070ff0fa96c2900021f61f52d85200a43fc3aa5b0a402c87d8754b61480614e902a96c2900c29da1751d85200063aba8a3b0a4000a758714761480618eb0e28ec2900029d60851d85201853bc00a3b0a4098a758014761480094ed0332cc2900129d20565985201863a3aec330a4000c5c7399561480614ed0332ac2900c21f21d65585200062e39acab0a4030a748159561480018bccbb9ac29000317597735852001c3fc32ea30a402c87d865d461480612e902ba8c2900021f61e65185200062f39cca30a4039c6d7299461480094e903328c2902331e5c
  | 4 => 0x3c813fb1886ba2659000e1fa1f755872024c3f438eab0e400487d825da51c80090fd02bb4a3900121f205769472024e3d102ed28e4049c79205da51c80932df0cb94a39027b1be1972947200263730ae528e4004c6c615ca51c80094e902b2c639000e1f217764c72000c77416ec98e400087f855d931c80070f90abb263900021f61b754c720004b6c16ea98e400087e8759531c80010f90eb2a63900129d205654c7200256a40ac698e4007ccc764c931c80011df0cb9a439000317ddb73595200062fbb0e6b2a4000d1c741cd654800147d0931aca900028f6126359520006a7b9ee4b2a4000d4c73dc965480018eeedb8aca9000359dcb71595200063bbb0e2b2a4000d57731c56548001aa8e638aca9000359dc871595200263bc30e2b2a4030c75861c565480018ecc638aca900031d18c7159520186b2c10e2b2a403ac77621c56548061ae50038aca900c35c60071595202863bb00e2b2a4000d73201c56548001acc4038aca90003590807159520006b8100e2b2a4000d5b73dc16548001ab0e7b82ca900035adcb7059520006b9b8ee0b2a4000d7071dc16548001c3ee9b9aca9000317dc373595200051f424e6b2a4000a3d849cd65480014bd0739aca9000317dce735952000536c14e6b2a4000a76819cd65480014eb0339aca900029e60273595200051fc22e6b2a4000a3c845cd65480014df04b9aca900029de0573595200053a40ae6b2a4000a7b805cd65480018bae639aca9000297a1c73595200062f438e6b2a4000e1f741cd65480018bce839aca90003171d073595200070e3a0e6b2a4000c1c741cd65480018bee039aca9013e9ba0a435952000536c1486b2a4080c747190d654813b8e8e221aca9000317dcf72595200062e39ee4b2a4039c6e87dc96548001c9ee7b92ca90003931cf72595204e637b86e4b2a4000a3e84cc9654800147b09992ca901f31d1c732595200243f43ee2b2a400487687dc56548001caee7b8aca90003951cf71595200063bb96e2b2a4000e6772dc565480018eee1b8aca9000297a0e71595200052ec1ce2b2a4000c5f739c565480018b8e738aca900029b60a71595200053b40ce2b2a4000c77719c565480014f30138aca9000297e0d71595200052e41ae2b2a4000a6f825c565480014f700b8aca9000317dcc71595200062e398e2b2a4004c76711c565480018eae238aca900029da1c71595200063b438e2b2a4000c77731c56548001caee638aca9000315dcc71595200063b398e2b2a4000c75731c565480018e8e638aca90003951cc71595200062a398e2b2a4000c77721c56548001ccee438aca900031ddc071595200043f43e62b2a400087d87cc565480098e8e398aca900028fa1031595200051ec2062b2a404fa6e820c565480014db0418aca900131d1c431595201653d4006
  | 5 => 0x80021fe1571d913001c3e42ae3b226000a7980147644c0070fd0fbaac8980021f60b75591300243f40eeab22600087f80dd5644c0010fb01baac89800237e0d75591300043f438eab226000c5c75dcd644c0010fd0fa92c89800e1f21f525913001c3f42ee2b22600087d85dc5644c0010fd0e28ac8980121f21c51591300053cc00a2b2260a3c5c76dd5434c147c38c9baa8698042a7a1b6450d304864e326e4a1a600087f855d3624c0070f90aba6c4980021fe1571d893001c3e42ae3b126000a7980147624c0011df0eb10c4980029b60a76549300051fc22eca92605ba3c845d9524c0014bf06bb2a4980029be0976549300053bc0aeca926038a74815d9524c0010ff0eb22a4980021f21d64549301652e43286a92605be1c6450d524c00f1b9073b48498006372197390930014cfc3a872126000c9e7650e424c0031b90cba2649809f27191744c93003e2e3b2a49926007e4c62549324c0010fb0f3aec2980022fe1175d85300845e422ebb0a60048dc835d7614c0070ff0ebaec2980030fe1175d85300061e422ebb0a6000c5f835d7614c0018b906baec2980021fe0975d85305143fc02ebb0a601187d805d7614c021938e8a1ec29800e1fe1f52d85300043ec3ea5b0a600087f8754b614c0010fb0ea96c2980ee9d20552d85300047bc3ac230a600087f87592514c0090f90eb24a29800257e1d43945301252e4328728a6057e1c6450e514c0494b90c994a2980063721973905300064fb22e720a600387e859d9414c0010fb0b3b28298003271d9435053040e2e3b6ea98a60018dc865d1314c0091b90eb22629808297215644c5301662e3b2a498a603bb5481549314c0031b90cb9e429800e1fa1676885300043ec2ced10a600087f855da214c0070f90abb442980022fe1176885300845e422ed10a60018dc865ce214c0070fd0b3b242980021f616764853000c6e432e690a60048dc839d8214c0031f1013b0429800637219730853000666b9ec410a60048f8865c0214c0019d6c4b80429801f3a18970085300051f424e6b2e4000a3d849cd65c80018bee739acb9001e9ba0a735972050d36c14e6b2e4000a76819cd65c80014eb0339acb9001e9ba0a435972000536c1486b2e400487e87dc565c80014bd0738acb900029760e715972003d37414e2b2e40a0a6d829c565c80090ff0eb8acb900131d9c471597200043f43e62b2e400087d87cc565c800147d0818acb900028f610315972003d3741062b2e4000a6d820c565c800f1bd0fa1ac79000e1fa177158f200043ec2ee2b1e4000a6d8214563c80070f90bbb287900423760f7650f200064e21eeca1e40018ee82dd943c80010ff0abb2879000e1f2157650f200064e21aeca1e400087d86dd543c80012db05baa87900021fa1d6550f200043e43acaa1e4000e1c435954
  | 6 => 0x62eb9ac530aa000a778158a61540094e902b14c2a80c71e5c1629855053eb8b86c330aa00087e87d8961540c70f90eb12c2a818e9d205625855000cbd43ee0b0aa0a6d7371dc161540230fb0fb18c2a8047179cf63185500253b40ec630aa000a3f8458c615400147908b18c2a8003175cc63185500253b408c630aa063d64215c8615409f0fb0fb10c2a80031b5cb62185500253b40ec430aa000a7581d8861540010fb0f310c2a80129d20662185500052fc1ac430aa000a5c8358861540014ef02b10c2a80129d20562185500253b408c430aa0009778758461540094ef0cb08c2a8296dce016118550004bdc02ed18aa00097980dd931540018bd07bb262a80031760f764c5500043ec16ec98aa000c7980dd931540010fd0d3b262a80024fe11764c5503249e422ec98aa00096f825d9315409f2d904bb262a80025ee01764c5500043ec10ec98aa00387f801d931540070fb003b262a800317cc0764c5500062e980ec98aa000c77101d931540018ea203b262a80021fe19744c5500043e432e898aa06395e87d8d31540018beedb1a62a818e5721d434c5500052e4328698aa064d1c7450d31540010fd0fb1262a80021f21f624c55000637b96c498aa04fc6c72d8931540c72b90e99262a813f531c9324c55031daa40a6498aa00387f809db21540070fb013b642a813f1bc8276c855000636904ed90aa00095f835db21540232b906bb642a80025ee0176c85500062fc1aed90aa000c5c835db21540018ef02bb642a80031ee0176c85500253b436c390aa000c757618721540012f700bb442a80021fe1973885500043e432e710aa004a7681d8a21540012f301bb242a80031e60376485500043f434ec90aa00095f835d921540232b906bb242a80025de057648550004bdc02ec90aa00487e811d921540090f9023b242a80031dc8476485500063a108ec90aa00387f801d921540070fb003b242a80031bc80764855000636900ec90aa000c77101d921540018ea203b242a80021fe1973485500043e432e690aa004a7681d8921540032f1013b042a80031ed8276085500243f40cec10aa00387f809d821540018f7013b042a800e1f602760855031e3c404ec10aa063974815d821540012f700bb042a80031ed81760855031e3a40aec10aa0a487f805d821540018f700bb042a813f17d89730855027e2eb12e610aa004c5e615cc21540098b8c2b9842a829317d817308550006adb02e610aa004a7686d8421540018eaedb0842a800e5ea1970085505263d432e010aa063c79865c021540072f10cb8042a813f1ed897008550006b9b0ae010aa004c7a615c021540098f0c2b8042a818f5c18570085500263830ae010aa063d6b215c021540c7ae442b8042a818f5a485700855027eb890ae010aa000c3d75d53644c0051b906b96c89
  | 7 => 0x3f845cf62540c927908b9ec4a813e1f61f63d895008e2f39ec7b12a000a3f8458f625400147908b1ec4a813e1f61c63d89500062eb98c7b12a04fa6e8218f62540014db05b9ec4a800317dce73d89500051fc22e7b12a000a3c845cf625400147d0839ec4a80028f61073d89500062eb98e7b12a000a6d821cf62540010ff0ea1ec4a80021f21d43d89500070ea1887b12a000a3e84ccb625400147b09996c4a800297a0e71d89500052ec1ce3b12a000c77719c762540734f50138ec4a82a29e60271d89500263b388e3b12a000c75711c762540010fd0f98ec4a80021f61f31d89500051f42063b12a000a3d840c762540734f50018ec4a80029e60031d8950566b4b86c5312a01195e87dcd6254001a3ee9b9ac4a800317d837358950006adb06e6b12a000d1f741cd6254001a38e839ac4a8047171cf63589500061e3a4c6b12a000c5f7398d625409f0f90eb1ac4a80028fe1163589500051e422c6b12a011c5c7358d6254001878e831ac4a800317dcc6358950006abb9ee2b12a000d5473dc562540018eec1b8ac4a80035cd837158950006abb98e2b12a000d54731c562540098ef0c38ac4a80031dd8c71589500063b318e2b12a000c75631c562540018e8c638ac4a80031d98871589500063a310e2b12a0a4c77601c56254001ae6c038ac4a800356dcf7058950006ac39ee0b12a09bd6b72dc16254001ae6e3b82c4a80035c1c77058950004b7c3ac4312a0abc6e7658862541556d700b10c4a80121fa06768c9500243e40ced192a00387f809da32540070fb013b464a813f1bc82768c95000636904ed192a00097b805da32540018bf06bb464a80031720d768c9500243e40aed192a000c7b805da325409f87ec4ba464a813f0f589748c9500061e30ae9192a08cc3f605d23254001a76c0ba464a813f4bc81748c9500062ebb6c7192a000d1e74d8e32540c92bf0ea1c64a800297219438c9503268f3a287192a00087f865c632540010f90cb8c64a80025e603764c9500049fc22ec992a06493c845d932540012bf06bb264a80025de05764c95031cba40aec992a00097b805d9325409f2bb07ba264a80021fe19744c9500043e432e8992a0a9d1c435d132540010fd0db8a64a80021f61b714c95021e3a30ee2992a06387d87d8b615409f8dce5b16c2a80031b5cb62d855031d3b40ec5b0aa063a748158b61540098bcc2b9cc2a80131718573985505262fb02e730aa000d5b605ce61540238bce7b1cc2a80030f9d263985500062eb9cc730aa004a768198e61540014eb0331cc2a80028fe1163985500051e422c730aa011c5e7358e61540094e902b1cc2a80030f9d063985500062eb98c730aa000c5e73d8a61540018bae7b14c2a82a31e5c362985500253b40cc530aa000a5f8358a61540014b906b14c2a8003179cd62985500
  | 8 => 0xaba2c610802972157458c210064eba0e8b184200e1f5495163084095ad032a2c610802b56065458c210052f42ce0b184200a5d859c1630840f59904b82c61080297a147058c210052ec28e0b184200a9e841c1630840153b08382c61081eb3a087058c2109d66c10e0b184204ad6811c163084275ab02382c610a3297e0b5058c214652ec16a0b184204a5e81d4163084094b903a82c61080297a164058c210052ec2c80b1842008de8710163084011bb0e202c61080297a144058c210052ec2880b184207ace82101630840159b04202c610812b5a044058c210056ac0880b18420387c85dd9430840193887bb286108021fe157650c2101c3e42aeca184200c9c435d943084010fb0dbaa8610a471798f7550c21024bb40eeaa184200c7a60dd543084010fd0eb2a86108021f21d6550c210070e21acaa1842048dc8758d43084018beeab1a8610803171d56350c210854e422c6a184263a79809d560084091e902baac0108129d20575580215253dc02eab00420387e85dcd60084010fb0bb9ac0108123ea1f50580215263d43ea0b004204a7a81d4160084094f103a82c010a939ac8750580215273910ea0b0042a4e6921d416008519ce243a82c0108123e21d50580210257840aa0b00428ca79829d560084094f5033aac0108129e20675580215273590ceab0042a4e72219d56008549cd2433aac010a339c486755802100579c0aeab004204af0815d560084018f70ebaac0108039ce0575580210253d40aeab004204a78815d560084c7ce102baac0108129c205755802131f3590aeab004263e72215d560084c7cd242baac01093f9c48575580210053d42ee6b004200a7985dcd600840f5d104b9ac0108029ea1473580210053cc28e6b004200aba841cd60084015730839ac01081ebaa08735802109574c10e6b004204af2811cd60084255e30239ac01080396d4e53580210257940ca6b004200af18194d600840f5d50521ac010802ba60a43580210053dc2a86b004200a788550d6008401d328621ac0108029761b43d8d500049fc22e5b1aa06493c845cb63540c927d0fba2c6a80030fd837458d500069db06e8b1aa000c3f761d163540238beedb1ac6a8003471d36358d500069dba6e0b1aa000d3874dc1635415dab6e7b82c6a80025e6037650d500070e21eeca1aa00087d82dd943540090fd03bb286a80031e6037650d500043f434eca1aa000d1c439d943540012bf06bb286a80025ee017650d500068e218eca1aa000e1c431d9435400187c863b286a80031710c7650d500060e218eca1aa00087d821d943540018b8643b286a80121fa047650d500243e408eca1aa000c5f311d943540070ff003b286a800e1f6007650d500062f980eca1aa000c5d301d9435415ba3887b9286a80021fa1b7150d500043ec36e2a1aa0009
  | 9 => 0x5358e210043f43ea4b1c420087e87d4163884070f90fa82c71080e1fa177650e210043ec2eeca1c420087f855d943884070f90abb287108121fa1b7550e210243e436eaa1c42048dc8758d43884018b8eab1a8710842a72116350e214d43e43ac6a944204c747158d52884092ed0fb8aa5108121fa1b7054a21024ba40ee0a944204cd47158d32884070fd0fbaac1108fa1fa1c75582210043f43ea4b04426b87c87549608840147d0931eca908028f61263d95210bc3ec38c1b2a4200a5e8318365484014bb06306ca908031e5c060d95210051f426e7b2a4200a3d84dcf65484018bae639eca908028fa1332d95210051ec2665b2a424987e87cc765484010fb0f98eca908121fa0570d95210243e40ae1b2a4200a5e831c365484014bb06386ca909269ba0870d95213a536c10e1b2a4274a76811c365484934eb02386ca908021fa1e30d95210043ec3c61b2a420087e870c365484010fb0e186ca908028fa1030d95210051ec2061b2a4249a6e820c365484014db04186ca909d29da0430d95210053ac0861b2a420087d8788365484010fb0f086ca908422fa1375d8d210045ec26ebb1a420087e87d9563484010fd0e32ac69080e1fa1f7558d210043ec06eab1a420087e871d563484010fd0fa92c69080e1f21f5258d210043f43ea0b1a420387c87d4163484070fd0bbb286908021f6177650d2101c3f42ceca1a420087d859d943484010ff0abb2869080e1f2157650d210047dc02eca1a42018f8805d943484070f90a3b286908021fa1b7550d210043f43ecaa1a420087c87d954348401c3887b2a869084237a1f6350d210854f426c6a1a4245c7471d8d52484010ff0eb1aa49080e1f21d635492121e3a38ac6a92420497687dc552484098ecec38aa49081ed920871549214f43f436e0a92428cd6421dc152484874d90ca9264908e31b1d9524c92116f2631aa49924238d647154932485290fd0dbaa6290a0a1fa1f654c52124c3e43eca98a4200a7980dd760484014f3003aec0908021fe1573d812101c3e42ae7b02425087c8754b60484070fd0dbaac0909d21f21b75581210043f43ecab024200c5c73d9560484010fd0e32ac090803171cc65581210062fb2ee6b024200c5c65dcd60484018bee739aca108129da0673594215853ac0ce6b284207a6e8290d65084014db0521aca1080e1f60b70594210243f40ee0b2842afa77815c165084094e902b82ca108021fa1e30594210043ec3c60b28420087e870c165084010fb0e182ca108028fa1030594210051ec2060b284207a6e820c165084014db04182ca108129da0430594210053ac0860b2842048de87d4d63084018beeba9ac6108123721d5358c210246f43e86b184200a5e858c163084014bb0b182c61080317dd67558c2103d67414e8b184200acd829d163084014bf
  | 10 => 0xa92620087c87591524c48d8e8e2b22a4988e297a1b73549310062f3b6e6a92620095c8750d524c4714b90ca1aa498803171d943549312df0e32286a926246d547150d524c4f98e8e3b12a4988125da1f715493116d3b436e2a926200c76761c5524c401aaee638aa498803551cc71549310043f436e0a92620387c859da424c4010ff0abb4849880e1f215769093103c76412ed212620087c865d6424c4092e902bac84988021fe1f65909310043ec3ecb2126225c5e73d96424c4018becab9c849880317195739093103e66312e721262049d4815ce424c40533f0ea1c8498803279d943909312af46312872126200ccd73d8a424c4070fd0bbb284988021f61776509310847743ec4a126281c5c76d95324c503aa8e3b2a6498a2b3318b744c9310246e432e8992622095c855d1324c44f938c8ba2649895733189744c931024ea40ae89926207ace86d89324c401c9eca312649880393194624c9310052e432a49926207c5c76549324c40fc98c4a92649890ed5205524c9311c6aa38aa499262049d687dc5324c5670fd0fb2a82988961f21f65505310254e43286a0a6202c9c7650d414c5656390aa1a8298812e520543505312378a28a86a0a6200a7980dd7604c4014f3003aec0988021fe1574d813101c3e42ae9b026210c9c7450f604c4010ff0ab96c09880e1f21572d81310043f43ea5b02620087c8754b604c4070fd0dbaac098a061f21b75581310043f43ecab026200c3c74d95604c4010fd0e32ac0988030f1d065581310061fb2ee8b026200c3c65dd1604c4018decbb92c0988031b197725813100637b28e4b026200c6c651c9604c40147d0939acb908028f61273597210062fb9ce6b2e4238a76819cd65c84014eb0339acb90ac69be0971597210043f43e62b2e420087d87cc565c85198f441b82cb9081e9ba0a705972124536c14e0b2e4200a5f835c165c84014b906b82cb908029de0570597211c53a40ae0b2e420087e878c165c84010fb0f182cb908021fa1c30597210043ec3860b2e4200a3e840c165c840147b08182cb9081e9ba08305972100536c1060b2e4238a76810c165c84014eb02182cb908021fa1e105972103c6f43e86b1e420387c85dd943c84211bb07bb287908032710f7650f210043fc2aeca1e420387c855d943c840193886bb287908021f61b7550f21024bb40eeaa1e420087e8759543c84010f90eb2a87908038710d6550f210043ec36ea98e422587e8759531c85050f90eb2a639081f331c9634c72127d3cc04eab0642008df835d560c84051b906baac1908c29d20575583214653dc02eab06420387e85dcd60c84010fb0bb9ac19080e1fa1f7558e210062f41eeab1c4281c5d83dd563884090fd03baac7108121f2077558e210043ec06eab1c428187e871d563884091bd0fa9ac71080317dd7
  | 11 => 0x8c4098e8e2b12a5188125da1f7154a31024ba40ee0a946204974815d6428c4070fd0bba2c1188021f617745823100537414c9b2a6200a6d82993654c4410fb0e306ca988028fa1060d95310051ec20c1b2a6200a6e82183654c4014db04306ca988031e5c060d953112d2f41ee9b2a6281a5d83dd3654c40187ae83a6ca9889697a0c74d953140d2ec18e9b2a6281a76811d3654c44b4eb023a6ca988028fa1372d95310051ec26e5b2a6225a5e83dcb654c5034bb07b96ca98803175cf72d953140d3b40ee5b2a6225a7581dcb654c4018bae6b96ca988021fe0172d953112d2f418e5b2a6281a5d831cb654c44b4bd07a16ca988029760f42d95310043f43885b2a620087d8710b654c44b0fd0fa0eca988021f61f41d953112d2f41ee1b2a6281a5d83dc3654c4018bae7b86ca98803175cd70d95310043fc12e1b2a6200a3e841c3654c40147b08386ca9889697a0c70d953140d2ec18e1b2a6200a6e821c3654c4014db04386ca98a069da0470d953112d3ac08e1b2a620087e87903654c4010fb0f206ca988021fa1c40d95310043ec3881b2a6225a5e83103654c4014bb06206ca988029ba0840d953100536c1081b2a6281a7681103654c4014eb02206ca988021fa1e20d95310043ec3c41b2a620087e87083654c4010fb0e106ca988028fa1020d95310051ec2041b2a6225a5e83083654c4014bb06106ca98a069da0420d95310053ac0841b2a622587e87843654c4010fb0f086ca988123760f75d91310043f43ecab22620087e87195644c4070fd0fbaac8988021f60b75591310043ec06eab22620087e871d5644c4010fd0fa92c89880e1f21f52591310043f43ea0b22620387c87d41644c5252bd0fbaa8698a8f171db7550d3151f0e326eaa1a62b595e87d95434c5038b8edb2a8698803871936550d310854f436c8a1a622095c85dc9434c521938c9b928698803551d77150d31104ae42ee0a1a62108be84dd7624c40117b09baec49880a3d60775d893100536c16ebb126200a6d821d7624c4010ff0aba6c49880e1f21574d89310043fc2ae1b12620387c855c3624c4010fd0fa86c4988029b60b50d893100556c2041b126200acd83083624c4015cb02106c4988030f9d365989310061f3a0cb3126200c3f655d2624c401878caba4c49881f2b189749893100656ba6c5312620087e87d95624c4010fd0e32ac4988821f61f651893100536c16ca31262b4c5d73194624c4014db04328c4988023be1d62189310043f434eca92625ba3e849d9524c40147b093b2a4988029b60a76549310061f424eca926200c3d849d9524c4018bd073b2a4988031760e765493100636c14eca926200c75819d9524c4010fb013b2a4988029be0976549310062f218eca926200c5f321d9524c4010fb003b2a498a031d1c764549310043fc3ac8
  | 12 => 0xe1f21d64549325c70e21ac8a926455e4c32591524c85b8bcedb9aa49901ed3a0b7354932466a6196e0a92640387f875d7614c8018bf06baec2990031720d75d85323dc3fc12ebb0a640087f805d7614c8070ff0fa96c2990021f61f52d85320a43fc3aa5b0a642d87d8754b614c8070ff0fa86c2990021f61f50d85320047bc3ac230a640087f855d3604c8070f90aba6c0990021fe1571d813201c3e42ae3b026400a6d82147604c8090fd0fbb287288038710f7650e510062fc1eeca1ca246c5c83dd9439440187c87bb287288031710f7650e510060e21eeca1ca20087d82dd943944018b865bb287288121fa077650e510243e40eeca1ca246c5f31dd9439448d8ba63bb287288021f6037650e510062f986eca1ca2b7d1c43dc9439440147d09b9ac5288028f6137358a510051f424e6b14a200a3d849cd62944018bee739ac52890e9b60a7358a513e537c12e6b14a200c5d731cd62944010ff0ea1ac5288021f21d4358a510070ea1886b14a200a3e84cc9629440147b09992c5288121fa077058a510243e40ee0b14a230a6d829c162944754df04b82c52880297a0c7058a510052ec18e0b14a204a76811c162944934eb02382c5288021fa1e3058a510043ec3c60b14a249a6e828c162944014db05182c5288021fa1c3058a510043ec3860b14a200a3e840c1629440147b08182c5289269ba083058a5100536c1060b14a204a76810c162944014eb02182c5288031edc22058a510061f422ed194a200c3d845da329448b8bd06bb465288031760d768ca510062f21aed194a249c5f325da32944938ba64bb465288121fa05768ca510243e40aed194a20087f805da32944938de40bb465288024fe19748ca510049ec32e9194a2b6d1e635d23294401a3ac6ba465289270fd89748ca5124e1eb12e9194a294c3e615d23294401a6cc2ba465289274bc81748ca512bcafc3a87194a200a5f8650e32944018baeca1c652895f479d1438ca5124caec1ee8994a20087f865d132944090f90cba26528adb4710d744ca510062fb9ce6b04a23ba79809cd60944eb4f700b9ac1288028fa1073582510051ec20e6b04a200c5d731cd60944094ed0239ac1288929d60473582510043fc3a86b04a20087c8750d6094401c3a8621ac1288121fa07725825100637906e4b04a230a79809c960944a14f700b92c12880297a0c72582510052ec18e4b04a204a76811c960944494eb02392c1288028fa1332582510051ec2664b04a20087e878c960944010fb0f192c1288028fa1232582510051ec2464b04a224a7a808c960944014f301192c1288021fa1c32582510043ec3864b04a224a7a800c960944014f300192c1288030fdd754592310247a40aeab14620387e85dd1628c4010fb0bba2c5188029be097654a311c53a40aeca946204c747159152
  | 13 => 0x43f43880b2c640087d87101658c85b4bd06202cb190029760c405963203d3741080b2c6400a6d82101658c8014ed02202cb190029d60440596320043f43c20b2c640087d87841658c8010fd0e082cb190021f61c10596320051f42020b2c6400a3d84041658c85b4bd06082cb190029760c105963203d3741020b2c6400a6d82041658c80187eebaa2c91901eaba0b545923203c5e43aa8b24640387e85dc5648c8010fb0bb8ac9190029b60851592320051f42c80b246400a3d85901648c80f55d05202c9190030fdd6755923203d57414eab246400aad829d5648c80147d0bb8ac9190028f61771592320051fc2ae2b246400a3c855c5648c80f55904b8ac91916aa7a0c71592320054ec18e2b246400cb5711c5648c80117d0f28ac9190022f61e51592322d54f41ca2b246400a9d83945648c80f55d0428ac919002ab60851592324a51fc10a2b246494e2e82145648c92947b0428ac9190038b608515923200516c10a2b246400a3d80145648c929c5e4028ac9190028fa1670592320051ec2ce0b246407aae829c1648c80155b05382c9190028fa1470592320051ec28e0b24645aa9e831c1648c80153b06382c91901eaba08705923215556c10e0b246400ab6811c1648c80156b02382c9192328fe0b50592324651ec16a0b246400a3e81d41648c919c5e41a82c91901eaba0a505923200556c14a0b246407aae82141648c80155b04282c9190028fa1610592320051ec2c20b246407aae82841648c80155b05082c9190022fa1c10592320045ec3820b246400a3e85041648c80147b0a082c91916aa7a0c10592320054ec1820b246407aae82041648c80155b04082c91928f17ddb7550e3251f0f326eaa1c6400d4f75dc9438c911b1ee9b9287190422fa1375586320045ec26eab0c640387e87dd5618c80187d09baac3190030f61375586320062f41eeab0c6400c5d83dd5618c8010fb01baac319043279d143586320043f43ea0b0c640387c87d41618c89f4f3013aac1192329ee01755823201c3f42ee8b04640087d85dd1608c82193ce8a1ac11900e1fa1771582320043ec2ee2b04640487f87145608c8010fb0e28ac1190029b60851582320053cc00a2b0464078dd83dd7644c80f8bae7a96c8990021fe1571d913201c3e42ae3b226400a6d82147644c8070fd0fbaac8990038710f75591320243f40eeab22640087d80dd5644c8010fd0e3aac8990038710c75591322d54f426e6b2264bde8c43dc9644c8010fd0fa92c89900e1f21f52591325e70e21ea4b22640387e85dc5644c8010fb0bb8ac8990021fa1c51591320243e438a2b2264bbe1c43145644c8014db0428ac8990021fa1f505913201c3e43ea0b2264bae1c43d41644c80f4bb07b22a4990b69b60b64549325cf17a16c8a92648ae4c32d91524c8010ff0eb22a499
  | 14 => 0xd7318c61548094ed02318c2a90029d6046318552004bbc3ac230aa4c0b67825846154871ae020b80c2a90129d20660185520253b408c030aa400a758684061548590fb0fb1ec0a90b7179cf63d81520051f424c7b02a400a3d8498f60549434db0531ec0a90029da0663d81520053ac0cc7b02a42c87d8718f60548018bae631ec0a90b29ea0063d81521643ec3ec3b02a438c7671d8760548594f501b0ec0a900297a0e61d81520052ec1cc3b02a4a0a6d8298760548010ff0eb0ec0a90b21f61c61d81520263b388c3b02a400c757118760548014f301b9ec0a90028fa1273d81520051ec24e7b02a400c5f739cf60548594dd0539ec0a92869b60a73d81520053b40ce7b02a400a75819cf60548018bae639ec0a90029e60073d81524653741487b02a400a6d8290f60548010ff0ea1ec0a90021f21d43d81520070ea1887b02a400a3e84ccb605480147b09996c0a90029e60371d81520052f41ce3b02a400a5d839c760548594dd0538ec0a92829b60a71d81520063bb8ce3b02a404c76711c760548018eae238ec0a90029e60071d81520043f43e63b02a40087d87cc7605480147d0818ec0a90028f61031d81524653741063b02a400a6d820c7605485b2bd0fb9ac0a900347dd373581520062ec36e6b02a400c5f62dcd6054801a9ec5b9ac0a900347dd073581520068e3a0e6b02a42dc5c73d8d605480147d0931ac0a90028f61263581520061e3a4c6b02a400c5f7398d605497f4db0531ac0a90029da0663581520053ac0cc6b02a42c87c8758d605485b8b8e6b1ac0a90030f1d063581520062fb98c6b02a400d4f73dc96054801a98e7b92c0a90e25da1f7158152006abb9ee2b02a400d5473dc56054801acee5b8ac0a90031d61b71581520063bb16e2b02a400d6762dc56054801aaee638ac0a9003551cc7158152006b3b90e2b02a404c77861c560548718eb0c38ac0a90031dd8c71581520063b318e2b02a400c75631c560548018e8c638ac0a920f1dd887158152006b3b10e2b02a400c76601c560548018e8c038ac0a90021fa1f61581521c63a38ec2b02a400a5e8398560548014bb0730ac0a900317dce61581520062e39cc2b02a4bea6d8298560548018eee330ac0a90131d1c661581521643e43ac2b02a438c747158560548018bee630ac0a9003171cc61581520063bb88c2b02a404c74711856054937ad6e5b02c0a90030fdd2745963216d2f41ce8b2c6400a5d839d1658c8014ed033a2cb190029d60674596320051f424e2b2c6400a3d849c5658c85b4bd0738acb190029760e71596320263b388e2b2c640087e87d05658c8010fb0fa0acb190b697a0c41596320052ec1882b2c640487e81dc1658c80f4dd05382cb191329b60a70596320052fc1ae0b2c642da5c835c1658c8010fd0f202cb190021f61e405963200
  | 15 => 0x43aec4a1957175cf52d89436970e21ea5b12860087f855c76250c070f90ab8ec4a18021fa1c51d89430243e438a3b1286b3c5d731476250da3c388628ec4a18131d9c451d89430063ab88a3b12860087f855c36250c070f90ab86c4a18021fa1f50d89436862eb9ea1b1286cfe1c43d436250c01a3886bacc4a1b3b175cf659894366e2eb98cb31286ccccd73d8a6250c01a3887baac4a18021fa1f655894365f0e21ecab12860087e871956250d95c388632ac4a18034710d751894317c3ec3eca3128600a6d82d946250c014db04328c4a18023be1d62189430068e21aebb0a864687d87d976150c8d4ed03b2ec2a191a1f61c65d854364f0e218cbb0a8646a76811976150c010fb0f3aec2a180e1fe1d75d85430062fc1aebb0a8600c5c835d76150c010ff04baec2a18021fe0175d854301c3fc3ea5b0a860087d87d4b6150c070ff0fa86c2a18021f61f50d85430068e21aeb30a86c8c5d731966150c01a3887baac2a18021fa1f65585430043f438cab0a86c7e1c431956150c094ed03b28c2a1a4b179cc65185436362eb98ca30a8604a76811946150c011ef0eb08c2a18029e60375d81430053cc00ebb02860087f855cb6050c070f90ab96c0a18021fa1f52d81430043fc2ae3b02860387c855c76050c010fd0e28ec0a18121f21c51d814301c3f436eab02869187c86dd56050c01a3887baac0a18021fa1f65581430043f438cab0286c5c5f731956050d892df04ba6c6a901e5b20974d8d520052ec3461b1aa4c3d4f73dc963548012db05bb286a90e25da077650d52004bac0eeca1aa400e1c43dd9435488d4ed03bb286a900317a0f7650d520062ec1eeca1aa400c6d82dd943548090fd03bb286a90031da077650d520243b40eeca1aa400c7581dd943548010fb01bb286a90021fa1a7650d52004b7c12eca1aa400e1c431d943548090fd023b286a90121f2047650d520062f988eca1aa40087d801d943548b72bd0fb1a86a900317ddb6350d522dd8f426c6a1aa45595d83dc94354985a3887b9286a9157538cb7250d520043f436e2a1aa40087d86dc543548098eced086c2a90029d61810d85520263b3b021b0aa400b558304361548016cb04086c2a90131d185739855241e2fb12e730aa400d4f625ce61548098bcc2b9cc2a90131718573985521c6aa30ae730aa404c54615ce615485b8bce7b1cc2a90028fa1263985520051ec24c730aa400c3e7498e61548018bae731cc2a90129da0663985520053ac0cc730aa42dc5e7358e61548094e902b1cc2a90030f9d063985520062eb98c730aa400d5573d866154983acae5b0cc2a90129da06609855258eb3b96c2b0aa42d87d87d8c615485b8bce7b18c2a90129da0763185520051f424c630aa400a3d8498c61548094ed03318c2a90029d60663185520253b40ac630aa400c5
  | 16 => 0x603600000e00600400000600200c00401400002000200000801000603200200005e00002c01201a00800000000603401000001200400200400000200201200001a02000400a01000e00000200c03e00001a01a06600400000200c00200000600200e00601600801c00800400e03001800203a00600800000400801a0d000202601600200000600c00c00201600601a00802001000000001200601800200601200200c00000000400e00000800c00000a00600400000a00000a01401800003c02802803400800a00a00005c00800002c00000a00a04802200000406400800602a02000200c00601604600c00200400000000600800200600a00000e01600001000002200200001400201400200e01c00002600000a00202200000e00000200000000202000400000400200400200400800000200000600401200800c00002001a00000000400000a00800200600000200c00400c00200402600001000601800c06800201400a00200400001201601200600001600200c00000201200200200000200200401400000000a00001400000600400600000800609000200200001601200200400400600602200400600000000001000a00400c00000000200000003200600a01000001400400a00a00600a00200200000201400000401000000400000000000000600800000402000400400200409002200000002803603200400200200000a01000200000000000e00400600a00000001000400000602000000000802400400400000200c02200201a00a00600200a00e01200201400c00800000000e00800000001001400600400401600004800002600200200d1c435cb6550c01a3886b86caa18be1f61c60d954300537410c1b2a8600a6d821836550c014ed02306caa18029d60460d95430063cb80c1b2a8691a5e83dcb6550d474bb07b96caa18029da0772d95430053ac0ee5b2a860487c815cb6550c010ff00b96caa18031b5c872d95430243fc3ae3b2a8691a5e831c76550d474bb0638ecaa18131d9c471d95430063ab88e3b2a860087f825c36550c090f902b86caa1a4697a0c70d954351d2ec18e1b2a8600a6e821c36550c014db04386caa18029da0470d95430053ac08e1b2a8600c79701c36550c010fd0f106caa18021f61e20d95430043f43841b2a860087d870836550d234bd06106caa18029760c20d95430053b40841b2a8600a75810836550c010fd0f086caa18021f61e10d95430043f43821b2a860087d870436550d234bd06086caa18029760c10d95430053741021b2a8600a6d820436550da9c3887b2ec4a1b1b175cc65d894369f0e218cbb1286108dd83dd76250c091ed03baec4a18023d60775d89430062eb9eebb128600e1c43dd76250c014db05baec4a18029da0775d89430062eb98ebb128600e1c431d76250c014db0
  | 17 => 0x15a800048316415e4c8400014412a0000422072a0ba3c8000171496c0000000001164abc4b844b841caf34891ab000072867100000000002a000000008e619a0eca1e8a125b70e20eb0ab87f228f93680005150000e285ac6d219c9cf00000000001c1cca00002b98e002360c40cf000059c0000001274000000000000000045700009fceee1b80001aba10000033019e904209e0000f350991540001d00e2c00046705cc4ea16e000000106668b24f828102e4b53c9875c3da2f036e99bc0005361ef00000008801700000d520003eb828200078a101211400066300000000e452b342017c89e54d000023262c5eb321892802c7ea455a34104c03d44297284de05b420079ca7200013c0fcd07661c28c80006667ab05b180c3023a833b000101a78e0000c4c53269f2ae9e9400000002306f40008e41fd866ee5e2b518f06d44a820e0001d0c28600027c0e3815a0000219c300000c000000008920001171dac0000004640000c00406234c54400000c00000800c00a00400a00200e00200c01000c00a05c00c01e00400200000400c00c00c02e00e00000a02403000601801a00a00000a00400800c00a00401a00000000002201800000c00c00000c00601800000000600800003c00000000003a01c00400c00800a00200001c01e00a03200200000000204800800800000002801401a00000200400000801000200400404a00600a00800e00c01402e00a00201c00000001e00000002a00e00200400000a00001400602c02402000200000000000201001200e05200001400200e01200000c01200e00001c00601a01800600e00000e02a00400401a00200200c01a00000a01801600800800400c0200100c600401800e01000600400002e00800000200000000c00200e04200e02001800008200601000001c00200208400c00a00200200c00201000002001000a00600e00400000400200200e00000400800603000001600000000c00801801800200800001400000a00400001600000000200001a00000800000000000000003e01601e01200200200000800a00a00000000000600201400a00401c00000200000200000202403800001000200200201a00a01801800600801000000600000600001600201600000c01800c00a00e00001600000200000201a00400e00200200600400600600001800600001000000000200001200001200600000800000400200001400000200602200000000c02000000001204007c00202000a00000a00600000a01001400603600e00001c0a000000000402803400000c00600401400800e00002e04400002a01a00004e00400203400600000400000a00200e00c04400200600000800201000601a00201c02401c00400400e01000200806e01a00000600000200600800a00602200200400001600200600400
  | 18 => 0x6061249000079800000000003a70001e880000007350000fc40000b800019d40001df23380000f600000003d91cc00006c80000001ef0d88000ffc27e000184059807b8000a74ddc15d00010f4cd80001d3000000000045c9c54e0c6572d807ad05e00005ccc180ee85d2ec9ac02d430a0498f2cb8a02334f1e5033d20c1210f500e037331611b08f412700010f01b471100013190ae0000001aec1a28b400000000007da3b88a780006691c7806000000015820f000000004c9ce43f44b7447800000000026892f849e65331c4000a107f945b000000000013ba0043e83fe98280000008a5130238866c77c3568000fc43c5000095815150d00000000000000fda3280000000000cd07be00021b8b9000041311c000000079709f80009c624f8dba35a1ac00004e8e74000000305a1220007a81ec0e1a5246cd3dc128ca1e0001ff800000000000000011ae6aa136039c59a8cf91c80003722d0a3a80000007c80000ff0000448000226c91c66e1dc0c0000000011800000005ea0000000000731198800038e000394165400048b46f4864642000305084017e0914160ef428828e0070aa4b5a5880570fb800009629911930b78b346180000000001458000fee245153060c0005fe2758f3c41d0aa21fd7b0bb000000010c00003c10d0913515059d20688b4b163512dc00000001d226f9060000000000000000000013680000000cc1a60000ba400023096680000000000d10492886000000026000000000000001100000dd000034b000000000000000000000005100868be00003462d183907a55b410d1f18afe6eab239f140002283d800010fa624000000000000000019510f802c0de194474a65221587c050431803a01c47380001509c3c50e3bc45ec180120000000000000000006e8000a9e7893b7885c5f212f00001b47990008000dc86221352c5cb7400000001280002f20000000000bb686e000219860e00030b0400b4a43e0f28174a782d117780884dc4292f95ba0cc22d211d8734e9476815c058c49c5bf21980003500033b2035c60459f0e50a90f9625311b86282e8783121e3569fa00011093a0e9a4db0b2057819c10c17300c519e09243521d4028000243a184b2246937308200007550341ee697a170233174470e78f3da8cba00000000012e469a12d257901cbdc000378975d1225754509a408c647b00009000000002e79490c928421c48000f843f8000105504a026135825c5640e217e4f990fd0000d7972c0003a33649a3116a0acbac815cfe70000e31d7814a34f12e4000a5a3a403c9bce3c2000000025000000000000008fc000037911c000555402847474263f02d192c3ac7700840a147de65f01392c50bc00a25306b813912c21c18640203b73e8d588da645b80000348424970b2a1949fe0001650000000000000
  | 19 => 0x600000005454378f8800000035310b00000000bb8a067e88a72f30d7c9a069a3a1617c28a774000080107000028b12440007343841c882f0094c44126107c7dd3e1d1d00005c411dc614cfc86900021340001ab176124c32800045b400009b2550d74adc70600000000003c16560000000d5f317032859c53686c000000015024d858045c0003ad0d900003660002a3987c0000003a88dac77c79133a00000006f30338880d32239b5b9cfc00000000016480000f3000000054e00022e80011350db1558000c0200020c8a0000068d3339e008d61c02b717dcf1655b40f899cf9e40225f9bf06940392a096149400bb187916cc720002ad0814de136a3ad8000486042800165cfbe1660000d0c00000003e80010488aa07d09a25fe88d3331c9420832814f9b280008a200003480005723179ef899a1dc43d9d4058e5e532218f421c37d0000982b064811749bb426c1960bf9df86583f993293f05ea59ab0486f840e2161a100f800000028111fc38569200014cc040000000000000070d3b90f2917e0003f780004660003dc400040800045e00000002928d800000000c900009700000000002064b3000044210991761953ef18e9056758118847c52e0002c50c34c420002411020c5238829083d038a0003eb174000035e3d218921fe25806c1778fa26270ac80003cb0000001c2800082200000000000002910e14000000000196c6e200000000007aa00000020c4d7c6dc3559758eca476184000041e385c38012800000028d01fc000264390145000076924d18d40003d326722b2a4a4413f70d1c00061838d0000c8a80c10c1470c1c1a426a1b90bc400000000000000c240a00000000980891f0c0006f402810b80004e000021e30c85be40182c827081d0768fa472a0000750e7cdc456936a969800057700009a60006ef12c83540000003060dd496c39e0a7800000000028880010727a02bb08d8f8069c0ea4b544cc3758450e445a65402528e9c58b4393068a0ad5c84a8928c40a8d4560001d98edc2740000b5c0002aa2c793607185e10ab8d9c2f663c19f80000003ed2db169d0c000000017040000003da0c101cc0003b1000049619f19d82208485bb0f2400010d08500016f400084fb73d9c80ea0fb041d40113f39634012cc6742da10e000106c8af000093a7ca0c800000000000000c91874e5a7d00000000a701390001b1c00023e84e000061c7e800000000005e30000b786ca64624e00000008410000000f240000000000ef654a2b58000aac54b1e9000000069131b8d5494439a14a1460fe57f6135106ecc4679174112c2ea6f2000000082c0560a904603381902d09bdc6ee8e10af93b873050a2979d580002d1aa95688a0626220f1ca448e02811380008800004051f809b87483dd40211718161d90f68b628c4123dafc1d
  | 20 => 0xb202b06812850600e82a11b509800762e405b06282d829e800001888c3c39750ada0003351b9d1808132ee000020a19b38c0f3ae004c40e1800042428946d0000c4c12922061685800000000000d4400000020b44263490001724dd86de11e8738000414000163000073a43bc00115c2cf0579a2110d47d0350e8895c8b80000eacdfa37b16c87fc00000030f1734e920000e48000dec23e3a780008355dd16207f0f925f30408000c9a71f1c0856c0000003f3905c550222212800058a03b3bfa1a0cb478d050903c00000039b0000000384000220412a31a000000000035300000000c40dc32f1a4ccc8000000110c090000085013c0008be3b00956b7f4c226500000030000c7800068041980011a803c00000000000000000e780000361560220000000000000000040287900018151960002b313e45194de3431f54b1c00000017f4f9f7d30000000a921f50000ec40002c900000009cc5ef2ba00001520cd000000000000000000000007c2a9d00004c231c3f184710403fa0000ab490a0001d7a0780002b400008a4b261f3af40f9cf6209b9bd02f00980000001cb023428f0cc9ae00000001e480000000003a255380008ba36313840006e30001188788776001237000028c2648b180001a98ed000000071d00014389906231da05c84416bd0000000000000291800000000000000bc0000001c9800000000000000002907190000000db27380370ed914d0001bf800032e7db2ccceb8868297a06000016820a44496640e6832048db840004d60000144c266ff0bf08504787fa0fba054b9c0a600003041be5a825e4314b643410f4862c25405205548447e40001920ff4a3a14626e92b033a7b208a234c8227010001154ea45bc1d500f04546d48d3a10c9e84ef000078c00025fb8f00000000001fb18508cb00000014d41430002e117d40006580208bb8bf2859000070e00089d000175ab5259b09983f804f03500000005230090001c4c23c8b20c480005e668700000002160003dbc0011bc13a000150c5d432f0000a8ce9c0001df9e7c0420003848f84000000000202488800040800040000003d4800000000000008ea4ae0003b19ff02e200046380000cc0003cd210ae06818428823850c71c05c8d200002bc00000d05c439b3fa03f108c0d40200d381660002629eb0e084f622519711384941da83a51c08060f616108bc4233f81be0b5453730792190a45e000017e00000003c800000546592ce1472f5e4cb02c8000b5e7bc0e0a1205202bf3dda2c422680204544ecaf854826b9038d6c65d21689c844a8a30000178fe62be44990ecb747a10001b3800080b00012e80007c4a8b8000596000178daca00a46e4368dc0b562f419a80000003ce42e5db41081b40ed90111b230100018c81560002738face6008f07c174c0523220e
  | 21 => 0x55c7990248b38a493c0cf062b1ad00002803f71f800008e476734a8ce05fa6823279e182643f89b114ecc2e26ac2c20b80003583d6929000007c000000065670b000001000088a000091000044600021acbda1aa40d08f62683573db8bf8fc175a36d8c949601221c115c0b807820a383b8ad05e40268bdc0fc53109ea21c4be2762970d8411f62038903bd04e093aff9b3002238b1860e0abf4376ad98d8c4585530d00dbcd4272313e13883fa02e4298b7c6f22982749b4e1d86854610b9c4128623829052fd26a03128000f448c500004f8ef00a31489abc0002790000000b8c4c700009740001ab99f000042a6c40000aec73200042a108a7db0001d81186d8014d3c21f2637e4353870170ef44f71ee022ca7e6d11788c2440c09b1381f9518b37c27f6138fa47e108b0d502c206780000000001244151ba4b2c3a93f32000c541c80c721700008bcb538c648f258d2699d8512a1a92c4801c0415e91e6de702224961e8c2f800022b3a38e800001090941a586da0000d60e4e51b0858000a540000003408ee82a0390218812c78c67d319934863e7461f20a883a24770e82358de32d0200a038f3a064393a3942d0082080957cc2232724420d0dae1604688432d8a6d01f1a1c879708d22d135458675c124432861d5053f89d303220003dd12d07f227a3010cdc31a4a90000af4158502914c834ac68503ec14804982eb0be1ec68d028112a570cb138742080b500b072b2369ad058152a03e5eccc3461227290002da5650b4981c95600037947d80000e02289e9c6c084725d8f0912c8c91f40c6cd0618006393b400074117d00000006c2000050467112000008fce843c02608f80eba1cb1cb80001e473700000000000004118000b480004549af00007ce8bb000049a0000000a110175290000750ace4273c280001128c6000000024223c80010d88981f8123086cc7003a37c9ba800025100017ec0008ac2f383c0af45573cd9ae50883fe33f80002a60000fc80000004420ad00003461982a8e36c5b80c319480704fa41d2550c740f425202106b45c62b109180003fc0f501c1e8c0340de00005f48c876c11795f4f828dd2750db083e69891d18200004cc0001cc8a027ca24813cc6600003e680540007e400000184b457e00000000000000000ecc00000000000000000000000a5a00084b30a930c00050c4148df906e4530a100011607b639e9eb8caa2ba1122128a0e47100009c40004053cc00dcfd814c0001f700000000001d500002ed44dc000d9e00000000c91200003a599040002b339303c40008990ce627cf2c0003658000be08831c1d08e1625062aa029e6543202d000d8ef289228047a909b000311087c2b01d31c90de00000b71ae95ec05a60435a800000072a9a800010e60454471e643741152b7946ca987884668d6c9
  | 22 => 0xf1800000019cc0006edc3b000000000000000002b853e0000b84a3c85500010249f442f3de800000000001f95408de7ce0002124a8829a0c380011a14b24500000be2244aed00000004ec347971c0008080000a9491a00044580009fc2320000000eea366374c0001480000930e1800041e800235000089e00005e820c18403181389c873309b8d142170003b98ecaa5070a8e363480000000959b5800048000019f03444fb3ca9a94baa21d03482880008a41058cb8000000146840cb722db14b18b400084c20e0bf11394520679a282f93d71398ae4b0c1d5402090456c0cb2fe19ad0e252712ed7d8ffe51213d8cda8b800042b00008064452b202560d64503909ff400010f3140d70ae23b934d96086460c646252f02941d827a86d804885b3d51fac8507814039f4ae5c89405a906caf02ac3fd9acc06029337016d51988b741d17303e40833a2a0a11302032c396b087e0e30001a5000000023e0f0d13400043b8cc8918000457c000d6400029a1c400161dd1318a28d5043a26792d64716c1069a38c0d83c73758d64c7645ea05804c1216c320e5f641344ad40da2b42047f509700007a0811000126482786739515ea02e63e1ee9564c5c73b13496b80aa62c82985ef18233d23c18d0efa54580000000000000001d10df45f23261bec00087e23000000005460001f220001a8b92078089c00024a93c4000689378177c03e00046a8abc3763c800000004d03ec1b48000c80283332a21ea161f132407083e62340000000000000318a0704bc8dda100c480d15302931580db455800022f45826a300020d40a856c000129c000882024800061661b0c621fca268a631b08d48344121bb1f5010e00007b80007d476a2051228d480003381d4c3471a61eda1e091e59403c0694d1c0ba007800085d83f3e211943d08df33d9b946a43260461c50f8e00039f139ef7e0c380c87888e07ed22c126d0cd6df1ec827c7ea0000001ab08b50000000bc85ca36e0001f06db055100e8000e2e64e3e60c549ff14b41e85bc3dc228a2f8218c0c49e3d840cc1fa0a709e1ee400075f3d30000000000000164055c0003180e340000000000bd91b00000001d5c0000004064eec000000381088cdea0000c4107e0001552a900000000000000cb46060001b40000be81de21905ace366b11eb213c7675810000000d2e0002b083845381c599e10a8b3c14e1240b08d2f69d0989210cee6c83fc1ae85f6000431861901e364279094246f66d0b119a04a000007c8000c9400010f1bf8232182009089817a5800239a6000079e29611503265043
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x105f985cc73d895000507251731cf625400141c9750c43d89500041de61711c7625400181c7321163589500050de51631c562540014349458c71589500050b648615d2325400181e74219438c9500060710c865d1325400181e732116398550006072127358a6154009854819cd6298550026152057358a6154009866815cb6218550007144c1101d9315400181c74219434c55000607210835db21540098658208476485500051c640211d92154001c612044076485500251ca5b615c0215400907897600515913000607210835d7614c00181c64e1d4394530026151c5839c565c80ab09d9810f7650f202ad23a4843dd943c800907691a1d6550f200040f25d8498d65480014369498c71595200050d652631c5654800116598080715952000519a58201c565480015459308071595200045c660201c5654800147296080715952000615dce819cd654800105f985cc735952000507251731cd6548001454915cc735952000507a52741cd6548001456919d07359520006191c58290d654800183471a1332595200040f25d84cc96548001834716133259520007051d073dc5654800985471a0e7159520026151c5839c5654800181e841ce71595200041de61711c56548001457935c471595200051524d711c56548001c1774dcc71595200050da52731c56548001435949cc715952000515a4e731c56548001437945cc71595200050d251731c56548001467925cc715952000515a5c731c56548001c17741cc7159520007051d0731c56548001c4473dc871595200260d1c6840c5654800103c9761031595200260d1c5840c56548009864716085158d200261c1c580145634800907691a1d6550d200060721c4359543481aba148110d6550d2027d4a642655d2324800152491595748c9204654ae41655d2324800142d96145748c9200054a640515d2324800186476205654c9200069118c8159532480098667660851d85200261c9d980147614800181c8420d75d8520006152047359561480014549159773585200261520673594614800945491595731852024d58644805ca514800154993209709452012558644825c25148001529948c970945200241d2448759531480094649759461485200241da478758d52c400142d92195748cb1000523650631c9634400109d9810c7650d1000525644431d9434400144d9219573189100051564c101d952440014659204076549100261c600101d9524400142d92195748c9100055864870dd53144009470965d47148110006545d5831c5204400166096549214811003e9821952485204400fc607654921481103a65821f854852044093a6086e152148110184d8261754852044059960875d521481101859825975485204409fc60765d521481101269821b65485204407dc6076d952148110
  | 1 => 0xb46e7308150e80018910de5b46000901455c64b8a331214443b628348c07002007e7e46a8800921fc3d325a0008108130029c46023c2e71e0034f1c167f5f2fcee66000013000000180000181c00000448016a0000000005d1c2ecc6c0341315000198f0dc93658746895a12ac174adcadc243d29a1d9400302c0f4005c2c8062854abc428a4fa18f2574d940005e4e1ac4801001a8960000128852c2092548a5048da74bd0d800189456a85403b803045a00000280004804001a0001c00020f008740a0003c08061180c300103808000e028341805098182a090009c020009800000f0e80c02040100008050101802070080022230005c20300000c14000580002150280010000050765c43dd76250c0160e9210f75d89430068310d82dd76250c0185573a0775d89430068510e81dd76250c0141d9710c75d894300583a48431d76250c01a0c4360875d89430241da4687d436250c0141e9610d75d854302607210835d76150c0141e9610f75585436ae85a0443dd9435480185583a077650d52026159d98304361548098667660810d85520260da067498e6154809856815ce639855200495e4d86840615480105f985cc73d81520241da478750f60548098547160e71d81520041de61711c760548098727160071d81520051524586dcd605480183474a06635815200615dce8198d60548010749760663581520050da52631c560548014359498c7158152026151c68398560548098547160e615815200607a107398560548098347161271596326bc8b64a85dc5648c80122f90608515923200607a1283dd5618c92984d7360851d913200507a5c43dd5644c80906c9760851591320068310d82145644c80141e9710f7650e516b507a5383dd9439440144e92e0f7650e516b507a4e43dd9439440141e9810f7650e516b50726043dd9439440141e9210f7650e516b507e4443dd943945ad41d9110f7650e510050764043dd9439440181c4360b7650e5100417a6032dd9439440141c940cb7650e510061360832dd9439440141c94cc37650e5100507a53739cd629440105f985cc7358a5100507e5d4310d629440181e83a11768ca510060798f865d2329440181e74e19438ca5100417a617650e329440181c43e19744ca5100417e61731cd6094409856815cf72d95310051364a431d9524c40141d94cc876549310050d652761c5524c40945696dcc71549312ac2766043dd943c840181e8710f6550d210241da4687595430840927298e0575580210249c24585dcd600840927291e15435802100507a4e431d9435400141e9210c7650d5000507644431d9435400141d9010c7650d500060710d821d9435400141c940c87650d5000613608321d9435400141c94cc47650d5000507253301d9435400141c944c07650d50005072517318f6254
  | 2 => 0x271f43ec436308000e0000154be9a80000b32c20cb27b3a9c85c82294a4005f3219469a6339a4647661954802b1f274f3c8a6a41748b218a89e1c040720847128792a164d2c42ebc5a0e5109620428238e000013c37a89f08a1a003206cb6292b122154b8002200001c502c90284a5e2663000002757000c2560c1
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x10e0000227a040c29400609a60058871202c0010001106d452421eebb12860090369e9210f75d894300502b4e21d03baec4a1802a06a210e81dd76250c01106d4524218ebb128600a8168443608515913200481d454c087bb2872880201ea8a4843dd9439440120ad0928196eca1ca200906680940cb7650e5100601928c1065bb28728802415a1250321d9435400120cd0128190eca1aa000c03251820c87650d500260c304c80423b242a80130518064c101d95244009830c0324080eca922004a142997560c7148110
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x310042000004805b7a8843a0775d8943005005b1251820cb7650e51005009b0251820cb7650e51005005b1251820c87650d50005009b0251820c87650d50
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x4
  | 3 => 0x6
  | 4 => 0x2
  | 5 => 0x94c
  | 6 => 0x94e
  | 7 => 0x3
  | 8 => 0x138c
  | 9 => 0x138e
  | 10 => 0x98c
  | 11 => 0x98e
  | 12 => 0x150c
  | 13 => 0x150e
  | 14 => 0x9cd
  | 15 => 0x9ce
  | 16 => 0x5
  | 17 => 0xa4c
  | 18 => 0x209
  | 19 => 0x20c
  | 20 => 0x20e
  | 21 => 0xb09
  | 22 => 0xb0c
  | 23 => 0xb0e
  | 24 => 0x1409
  | 25 => 0x140c
  | 26 => 0x140e
  | 27 => 0x1549
  | 28 => 0x154c
  | 29 => 0x154e
  | 30 => 0xb49
  | 31 => 0xb4d
  | 32 => 0xb4e
  | 33 => 0x1449
  | 34 => 0x144d
  | 35 => 0x144e
  | 36 => 0x14c9
  | 37 => 0x14cc
  | 38 => 0xcc9
  | 39 => 0xccd
  | 40 => 0xcce
  | 41 => 0x15c9
  | 42 => 0x15cd
  | 43 => 0x15ce
  | 44 => 0xd49
  | 45 => 0xd4c
  | 46 => 0xe89
  | 47 => 0xe8e
  | 48 => 0x98a
  | 49 => 0x98956
  | 50 => 0xb0956
  | 51 => 0x140956
  | 52 => 0xb4956
  | 53 => 0x144956
  | 54 => 0x249
  | 55 => 0x94d
  | 56 => 0xd4a
  | 57 => 0x1a09
  | 58 => 0x128a
  | 59 => 0x9ca
  | 60 => 0x16c9
  | 61 => 0x12ca
  | 62 => 0x134a
  | 63 => 0x2c9
  | 64 => 0xb1396
  | 65 => 0xb5396
  | 66 => 0x4c
  | 67 => 0xcca
  | 68 => 0x138d
  | 69 => 0x15ca
  | 70 => 0xe8a
  | 71 => 0xb0996
  | 72 => 0x154996
  | 73 => 0x14cb
  | 74 => 0xcc996
  | 75 => 0xcc995
  | 76 => 0x15c996
  | 77 => 0x3c9
  | 78 => 0x1709
  | 79 => 0xa4b
  | 80 => 0x150a
  | 81 => 0xb1516
  | 82 => 0xcd516
  | 83 => 0xcd515
  | 84 => 0x8c
  | 85 => 0xe8b
  | 86 => 0xb49d6
  | 87 => 0x14cd
  | 88 => 0x124c
  | 89 => 0xcc9d6
  | 90 => 0xd0c
  | 91 => 0xd4d
  | 92 => 0x128c
  | 93 => 0xe89d6
  | 94 => 0xa0c
  | 95 => 0x18c9
  | 96 => 0x180c
  | 97 => 0x1789
  | 98 => 0x130c
  | 99 => 0xa4a
  | 100 => 0xa4d
  | 101 => 0x4e
  | 102 => 0x19c9
  | 103 => 0xbc9
  | 104 => 0x124e
  | 105 => 0xcca55
  | 106 => 0x449
  | 107 => 0x8e
  | 108 => 0x1649
  | 109 => 0x128e
  | 110 => 0xec9
  | 111 => 0x168e
  | 112 => 0x1a49
  | 113 => 0x17c9
  | 114 => 0x12ce
  | 115 => 0x5c9
  | 116 => 0x164a
  | 117 => 0x168a
  | 118 => 0xb8e
  | 119 => 0xb8c
  | 120 => 0xccb56
  | 121 => 0xd0e
  | 122 => 0x160e
  | 123 => 0x1a0c
  | 124 => 0x170a
  | 125 => 0xe8b56
  | 126 => 0x184c
  | 127 => 0x148c
  | 128 => 0x178a
  | 129 => 0x17ca
  | 130 => 0x2cc
  | 131 => 0x1a0a
  | 132 => 0xcd4d5
  | 133 => 0x3ca
  | 134 => 0x18ca
  | 135 => 0xd4cd5
  | 136 => 0x188c
  | 137 => 0x160c
  | 138 => 0x178b
  | 139 => 0xe95d6
  | 140 => 0x198b
  | 141 => 0x170e
  | 142 => 0x28c
  | 143 => 0x40c
  | 144 => 0x170d
  | 145 => 0x194c
  | 146 => 0x74c
  | 147 => 0xb09895e
  | 148 => 0x2cb
  | 149 => 0x14a
  | 150 => 0x2d551
  | 151 => 0x1a0d
  | 152 => 0x1542d1
  | 153 => 0xd0994
  | 154 => 0x3ce
  | 155 => 0x151296
  | 156 => 0x1a0d51
  | 157 => 0x58a
  | 158 => 0x8a
  | 159 => 0xd1514
  | 160 => 0x150b16
  | 161 => 0x150cd6
  | 162 => 0x198c
  | 163 => 0x17cd
  | 164 => 0x198a
  | 165 => 0x5396
  | 166 => 0x139256
  | 167 => 0x124956
  | 168 => 0x128956
  | 169 => 0xd0a54
  | 170 => 0x9516
  | 171 => 0xd5a11
  | 172 => 0x128996
  | 173 => 0x188a54
  | 174 => 0x1692d6
  | 175 => 0x21256
  | 176 => 0x20b56
  | 177 => 0x155416
  | 178 => 0xb8b56
  | 179 => 0x2cd
  | 180 => 0x5ca
  | 181 => 0xb45d5
  | 182 => 0xd14d4
  | 183 => 0x1894d4
  | 184 => 0xd0d54
  | 185 => 0xccd55
  | 186 => 0x198d14
  | 187 => 0x2cd14
  | 188 => 0x1a0d14
  | 189 => 0x188d14
  | 190 => 0x98b16
  | 191 => 0x98cd6
  | 192 => 0x21416
  | 193 => 0x154b16
  | 194 => 0x188d54
  | 195 => 0x1715d6
  | 196 => 0x188e
  | 197 => 0x5d2d5
  | 198 => 0x5cd
  | 199 => 0x74b94
  | 200 => 0x5cb55
  | 201 => 0x75854
  | 202 => 0x74d14
  | 203 => 0x194d14
  | 204 => 0x170cd5
  | 205 => 0x5ccd5
  | 206 => 0x17ccd5
  | 207 => 0x199894
  | 208 => 0x198d
  | 209 => 0x2d894
  | 210 => 0x1a1894
  | 211 => 0x75894
  | 212 => 0x195894
  | 213 => 0x58e92
  | 214 => 0xe8592
  | 215 => 0x15cd55
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 49
  | 7 => 1266
  | 6 => 4096
  | 5 => 2279
  | 4 => 204
  | 3 => 18
  | 2 => 5
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
  | 8 => packedAt gbK8 (1428+((h/22+packedAt gbK8 (1274+(h % 22)*7) 7) % 80)*7) 7
  | 7 => packedAt gbK7 (53106+((h/522+packedAt gbK7 (46842+(h % 522)*12) 12) % 2069)*12) 12
  | 6 => packedAt gbK6 (217083+((h/1575+packedAt gbK6 (196608+(h % 1575)*13) 13) % 6239)*13) 13
  | 5 => packedAt gbK5 (144529+((h/839+packedAt gbK5 (134461+(h % 839)*12) 12) % 3325)*13) 13
  | 4 => packedAt gbK4 (14946+((h/74+packedAt gbK4 (14280+(h % 74)*9) 9) % 269)*9) 9
  | 3 => packedAt gbK3 (1488+((h/6+packedAt gbK3 (1458+(h % 6)*5) 5) % 22)*6) 6
  | 2 => packedAt gbK2 (463+((h/1+packedAt gbK2 (460+(h % 1)*3) 3) % 8)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xe0ff8380ffc1fffe0ffff80ffc1468cf0cf3cf
  | 1 => 0xff07fc00e0fe1e07f0f03ff07c6b97338b4d33
  | 2 => 0xfff8ffff00ffe007ff003fff838c183cf38e3c
  | 3 => 0xffffff000007ffffc00003f01fc0fc0fc0
  | 4 => 0xfffffffffff80000000003ffe000fff000
  | 5 => 0xffff0000000000000000000003ffffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x20090000010022800114080420002045001045
  | 1 => 0x410294086852141290a092a058218312894512
  | 2 => 0x9ad029b100a540252a01254b018c1828328a28
  | 3 => 0x840cedaba101047cccb80610af01d80dc0f80
  | 4 => 0x1080f36cdcf9997080820182137ec000efe000
  | 5 => 0xfce4007010210181080c060c63df7eff000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeeeee8faeaeae8feeeeee8faeaeae8feeeeee8faeaeae8feeeeee8faeaeae8feeeeee8faeaeae8feeeeee8faeaeae8feeeeee8faeaeae8feeeeee8faeaeae8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37209
namespace PEqualNP.Outside.L_meta_37209
open PEqualNP.Outside.L_meta_37209.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 8 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_32 : Interval s0Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_64 : Interval s0Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 92 := (concat bs0_4_0 (concat bs0_4_32 bs0_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 44 := (concat bs0_5_0 bs0_5_32)
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
theorem bs1_3_0 : Interval s1Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_32 : Interval s1Atlas 3 32 7 := block_range (n:=7) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 39 := (concat bs1_3_0 bs1_3_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 24 := bs1_4_0
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
theorem bs2_2_0 : Interval s2Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 4 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 8 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 9 := bs2_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 1 := bs2_5_0
theorem alls2 : ∀ k ≤ 5, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_2 i (by omega) hi
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 10 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_32 : Interval s3Atlas 3 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 60 := (concat bs3_3_0 bs3_3_32)
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
theorem bs3_4_128 : Interval s3Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_160 : Interval s3Atlas 4 160 5 := block_range (n:=5) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 165 := (concat (concat bs3_4_0 (concat bs3_4_32 bs3_4_64)) (concat bs3_4_96 (concat bs3_4_128 bs3_4_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 50 := (concat bs3_5_0 bs3_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 1 := bs3_6_0
theorem alls3 : ∀ k ≤ 6, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
  · exact alls3_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_0 : Interval s4Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 10 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_32 : Interval s4Atlas 3 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 60 := (concat bs4_3_0 bs4_3_32)
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
theorem bs4_4_160 : Interval s4Atlas 4 160 5 := block_range (n:=5) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 165 := (concat (concat bs4_4_0 (concat bs4_4_32 bs4_4_64)) (concat bs4_4_96 (concat bs4_4_128 bs4_4_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 50 := (concat bs4_5_0 bs4_5_32)
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
theorem bs5_3_224 : Interval s5Atlas 3 224 4 := block_range (n:=4) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 228 := (concat (concat (concat bs5_3_0 bs5_3_32) (concat bs5_3_64 bs5_3_96)) (concat (concat bs5_3_128 bs5_3_160) (concat bs5_3_192 bs5_3_224)))
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
theorem bgb_2_0 : Interval gbAtlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 5 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 18 := block_range (n:=18) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 18 := bgb_3_0
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
theorem bgb_4_192 : Interval gbAtlas 4 192 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 204 := (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat (concat bgb_4_96 bgb_4_128) (concat bgb_4_160 bgb_4_192)))
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
theorem bgb_5_2272 : Interval gbAtlas 5 2272 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2279 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)))) (concat (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 bgb_5_384)) (concat (concat bgb_5_416 bgb_5_448) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))))) (concat (concat (concat (concat bgb_5_576 bgb_5_608) (concat bgb_5_640 bgb_5_672)) (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)))) (concat (concat (concat bgb_5_864 bgb_5_896) (concat bgb_5_928 bgb_5_960)) (concat (concat bgb_5_992 bgb_5_1024) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)))))) (concat (concat (concat (concat (concat bgb_5_1152 bgb_5_1184) (concat bgb_5_1216 bgb_5_1248)) (concat (concat bgb_5_1280 bgb_5_1312) (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)))) (concat (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 bgb_5_1536)) (concat (concat bgb_5_1568 bgb_5_1600) (concat bgb_5_1632 (concat bgb_5_1664 bgb_5_1696))))) (concat (concat (concat (concat bgb_5_1728 bgb_5_1760) (concat bgb_5_1792 bgb_5_1824)) (concat (concat bgb_5_1856 bgb_5_1888) (concat bgb_5_1920 (concat bgb_5_1952 bgb_5_1984)))) (concat (concat (concat bgb_5_2016 bgb_5_2048) (concat bgb_5_2080 bgb_5_2112)) (concat (concat bgb_5_2144 bgb_5_2176) (concat bgb_5_2208 (concat bgb_5_2240 bgb_5_2272)))))))
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
theorem allgb_6 : Interval gbAtlas 6 0 4096 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 bgb_6_224))) (concat (concat (concat bgb_6_256 bgb_6_288) (concat bgb_6_320 bgb_6_352)) (concat (concat bgb_6_384 bgb_6_416) (concat bgb_6_448 bgb_6_480)))) (concat (concat (concat (concat bgb_6_512 bgb_6_544) (concat bgb_6_576 bgb_6_608)) (concat (concat bgb_6_640 bgb_6_672) (concat bgb_6_704 bgb_6_736))) (concat (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 bgb_6_864)) (concat (concat bgb_6_896 bgb_6_928) (concat bgb_6_960 bgb_6_992))))) (concat (concat (concat (concat (concat bgb_6_1024 bgb_6_1056) (concat bgb_6_1088 bgb_6_1120)) (concat (concat bgb_6_1152 bgb_6_1184) (concat bgb_6_1216 bgb_6_1248))) (concat (concat (concat bgb_6_1280 bgb_6_1312) (concat bgb_6_1344 bgb_6_1376)) (concat (concat bgb_6_1408 bgb_6_1440) (concat bgb_6_1472 bgb_6_1504)))) (concat (concat (concat (concat bgb_6_1536 bgb_6_1568) (concat bgb_6_1600 bgb_6_1632)) (concat (concat bgb_6_1664 bgb_6_1696) (concat bgb_6_1728 bgb_6_1760))) (concat (concat (concat bgb_6_1792 bgb_6_1824) (concat bgb_6_1856 bgb_6_1888)) (concat (concat bgb_6_1920 bgb_6_1952) (concat bgb_6_1984 bgb_6_2016)))))) (concat (concat (concat (concat (concat (concat bgb_6_2048 bgb_6_2080) (concat bgb_6_2112 bgb_6_2144)) (concat (concat bgb_6_2176 bgb_6_2208) (concat bgb_6_2240 bgb_6_2272))) (concat (concat (concat bgb_6_2304 bgb_6_2336) (concat bgb_6_2368 bgb_6_2400)) (concat (concat bgb_6_2432 bgb_6_2464) (concat bgb_6_2496 bgb_6_2528)))) (concat (concat (concat (concat bgb_6_2560 bgb_6_2592) (concat bgb_6_2624 bgb_6_2656)) (concat (concat bgb_6_2688 bgb_6_2720) (concat bgb_6_2752 bgb_6_2784))) (concat (concat (concat bgb_6_2816 bgb_6_2848) (concat bgb_6_2880 bgb_6_2912)) (concat (concat bgb_6_2944 bgb_6_2976) (concat bgb_6_3008 bgb_6_3040))))) (concat (concat (concat (concat (concat bgb_6_3072 bgb_6_3104) (concat bgb_6_3136 bgb_6_3168)) (concat (concat bgb_6_3200 bgb_6_3232) (concat bgb_6_3264 bgb_6_3296))) (concat (concat (concat bgb_6_3328 bgb_6_3360) (concat bgb_6_3392 bgb_6_3424)) (concat (concat bgb_6_3456 bgb_6_3488) (concat bgb_6_3520 bgb_6_3552)))) (concat (concat (concat (concat bgb_6_3584 bgb_6_3616) (concat bgb_6_3648 bgb_6_3680)) (concat (concat bgb_6_3712 bgb_6_3744) (concat bgb_6_3776 bgb_6_3808))) (concat (concat (concat bgb_6_3840 bgb_6_3872) (concat bgb_6_3904 bgb_6_3936)) (concat (concat bgb_6_3968 bgb_6_4000) (concat bgb_6_4032 bgb_6_4064)))))))
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
theorem bgb_7_1248 : Interval gbAtlas 7 1248 18 := block_range (n:=18) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1266 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 bgb_7_192) (concat bgb_7_224 (concat bgb_7_256 bgb_7_288)))) (concat (concat (concat bgb_7_320 bgb_7_352) (concat bgb_7_384 (concat bgb_7_416 bgb_7_448))) (concat (concat bgb_7_480 bgb_7_512) (concat bgb_7_544 (concat bgb_7_576 bgb_7_608))))) (concat (concat (concat (concat bgb_7_640 bgb_7_672) (concat bgb_7_704 (concat bgb_7_736 bgb_7_768))) (concat (concat bgb_7_800 bgb_7_832) (concat bgb_7_864 (concat bgb_7_896 bgb_7_928)))) (concat (concat (concat bgb_7_960 bgb_7_992) (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088))) (concat (concat bgb_7_1120 bgb_7_1152) (concat bgb_7_1184 (concat bgb_7_1216 bgb_7_1248))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 17 := block_range (n:=17) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 49 := (concat bgb_8_0 bgb_8_32)
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 7 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 18, 50)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeeeee8faeaeae8feeeeee8faeaeae8feeeeee8faeaeae8feeeeee8faeaeae8feeeeee8faeaeae8feeeeee8faeaeae8feeeeee8faeaeae8feeeeee8faeaeae8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 34 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277071592 * 2 ^ 32 + 4209699560) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37209.Model.Repr at out
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

def mono : List Gate := [⟨.or,[3,4]⟩,⟨.and,[3,4]⟩,⟨.or,[0,1]⟩,⟨.or,[1,6]⟩,⟨.or,[7,8]⟩,⟨.and,[2,10]⟩,⟨.and,[0,9]⟩,⟨.and,[5,8]⟩,⟨.or,[11,12]⟩,⟨.and,[6,13]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071592 * 2 ^ 32 + 4209699560) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071592 * 2 ^ 32 + 4209699560) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37209

open PEqualNP.Outside.L_meta_37209 in
theorem PEqualNP.Outside.L_meta_37209 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071592 * 2 ^ 32 + 4209699560) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071592 * 2 ^ 32 + 4209699560) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
